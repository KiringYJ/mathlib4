# frozen_string_literal: true

require "digest"
require "json"
require "pathname"
require "time"
require "yaml"

module AgentWorkbench
  class LockfileMigrationError < StandardError; end

  module LockfileMigration
    WORKFLOW_SCOPES = %w[portable_prompts portable_skills vendor_adapters].freeze
    WORKFLOW_KINDS = %w[portable_prompt portable_skill vendor_adapter].freeze
    SYNC_MODES = %w[full guide-only entrypoints-only portable-workflows repair].freeze
    STATIC_OUTPUT_SCOPES = {
      "AI_AGENT_GUIDE.md" => "guide",
      "CLAUDE.md" => "entrypoints",
      "AGENTS.md" => "entrypoints",
      "GEMINI.md" => "entrypoints",
      "opencode.json" => "entrypoints",
      ".codex/config.toml" => "entrypoints"
    }.freeze
    SHA256 = /\Asha256:[0-9a-f]{64}\z/
    COMMIT = /\A[0-9a-f]{40}(?:[0-9a-f]{24})?\z/

    module_function

    def migrate(lockfile, manifest, workbench_root:, consumer_root:, expected_repo:, expected_branch:,
                expected_requested_ref:, manifest_digest:, resolved_commit:, reconciled_at:)
      version = lockfile.fetch("schemaVersion")
      return deep_copy(lockfile) if version == 2
      raise LockfileMigrationError, "unsupported lockfile schema version: #{version}" unless version == 1

      expected_source = {
        "repo" => expected_repo,
        "branch" => expected_branch,
        "requestedRef" => expected_requested_ref
      }
      validate_expected_source!(expected_source)
      validate_v1_ledger!(lockfile, expected_source)
      validate_provenance!(manifest_digest, resolved_commit, reconciled_at)

      source_root = Pathname(workbench_root).expand_path
      output_root = Pathname(consumer_root).expand_path
      prompt_paths = registered_paths(manifest, "portable_prompts")
      skill_paths = registered_paths(manifest, "portable_skills")
      migrated = deep_copy(lockfile)
      migrated_scopes = []
      seen_outputs = {}

      migrated.fetch("installedArtifacts").each do |artifact|
        unless workflow_artifact?(artifact)
          normalize_preserved_artifact!(artifact)
          strip_legacy_metadata(artifact)
          next
        end

        registration = classify_artifact(artifact, prompt_paths, skill_paths)
        output_path = registration.fetch(:output_path)
        if seen_outputs.key?(output_path)
          raise LockfileMigrationError,
                "multiple legacy artifacts map to #{output_path}: #{seen_outputs.fetch(output_path)} and #{artifact_id(artifact)}"
        end

        seen_outputs[output_path] = artifact_id(artifact)
        reconcile_artifact!(artifact, registration, source_root, output_root)
        migrated_scopes << registration.fetch(:scope)
      end

      migrate_scopes!(migrated, migrated_scopes.uniq, manifest_digest, resolved_commit, reconciled_at)
      migrated["schemaVersion"] = 2
      migrated["generatedAt"] = reconciled_at
      migrated["manifestDigest"] = manifest_digest
      migrated["source"]["repo"] = expected_repo
      migrated["source"]["branch"] = expected_branch
      migrated["source"]["requestedRef"] = expected_requested_ref
      migrated["source"]["resolvedCommit"] = resolved_commit
      migrated
    end

    def read_json(path)
      JSON.parse(Pathname(path).read)
    end

    def write_json(path, value)
      output = Pathname(path)
      raise LockfileMigrationError, "refusing to overwrite migration output: #{output}" if output.exist?

      content = "#{JSON.pretty_generate(value)}\n"
      output.open(File::WRONLY | File::CREAT | File::EXCL, 0o600) { |file| file.write(content) }
    end

    def registered_paths(manifest, section)
      manifest.fetch(section, {}).to_h do |name, registration|
        [name, normalize_path(registration.fetch("path"))]
      end
    end

    def workflow_artifact?(artifact)
      artifact.is_a?(Hash) &&
        (WORKFLOW_SCOPES.include?(artifact["scope"]) || WORKFLOW_KINDS.include?(artifact["kind"]))
    end

    def validate_v1_ledger!(lockfile, expected_source)
      required_keys = %w[
        generatedAt
        source
        manifestDigest
        profile
        syncMode
        targets
        scopes
        installedArtifacts
        retainedRemovals
      ]
      missing = required_keys.reject { |key| lockfile.key?(key) }
      raise LockfileMigrationError, "v1 ledger missing required fields: #{missing.join(', ')}" unless missing.empty?

      validate_timestamp!(lockfile.fetch("generatedAt"), "generatedAt")
      validate_source!(lockfile.fetch("source"), expected_source)
      unless lockfile.fetch("manifestDigest").to_s.match?(SHA256)
        raise LockfileMigrationError, "invalid v1 manifest digest"
      end
      raise LockfileMigrationError, "v1 profile must be a non-empty string" unless non_empty_string?(lockfile.fetch("profile"))
      raise LockfileMigrationError, "invalid v1 sync mode" unless SYNC_MODES.include?(lockfile.fetch("syncMode"))
      validate_targets!(lockfile.fetch("targets"))
      validate_scopes!(lockfile.fetch("scopes"))
      validate_artifacts!(lockfile.fetch("installedArtifacts"))
      unless lockfile.fetch("retainedRemovals").is_a?(Array)
        raise LockfileMigrationError, "v1 retainedRemovals must be an array"
      end
    end

    def validate_expected_source!(expected_source)
      expected_source.each do |key, value|
        raise LockfileMigrationError, "expected source.#{key} is required" unless non_empty_string?(value)
      end
    end

    def validate_source!(source, expected_source)
      raise LockfileMigrationError, "v1 source must be an object" unless source.is_a?(Hash)

      %w[repo branch requestedRef resolvedCommit].each do |key|
        raise LockfileMigrationError, "v1 source.#{key} is required" unless non_empty_string?(source[key])
      end
      raise LockfileMigrationError, "invalid v1 source.resolvedCommit" unless source["resolvedCommit"].match?(COMMIT)

      expected_source.each do |key, expected_value|
        next if source[key] == expected_value

        raise LockfileMigrationError,
              "v1 source.#{key} mismatch: expected #{expected_value.inspect}, got #{source[key].inspect}"
      end
    end

    def validate_targets!(targets)
      raise LockfileMigrationError, "v1 targets must be an object" unless targets.is_a?(Hash) && !targets.empty?
      missing = %w[guide portable_prompts portable_skills].reject { |key| targets.key?(key) }
      raise LockfileMigrationError, "v1 targets missing required fields: #{missing.join(', ')}" unless missing.empty?
      unless targets.values.all? { |value| value == true || value == false }
        raise LockfileMigrationError, "v1 targets must contain booleans"
      end
    end

    def validate_scopes!(scopes)
      raise LockfileMigrationError, "v1 scopes must be an object" unless scopes.is_a?(Hash) && !scopes.empty?

      scopes.each do |name, scope|
        raise LockfileMigrationError, "v1 scope #{name} must be an object" unless scope.is_a?(Hash)
        %w[resolvedCommit manifestDigest lastReconciledAt].each do |key|
          raise LockfileMigrationError, "v1 scope #{name}.#{key} is required" unless scope.key?(key)
        end
        raise LockfileMigrationError, "invalid v1 scope #{name} commit" unless scope["resolvedCommit"].to_s.match?(COMMIT)
        raise LockfileMigrationError, "invalid v1 scope #{name} digest" unless scope["manifestDigest"].to_s.match?(SHA256)
        validate_timestamp!(scope["lastReconciledAt"], "scope #{name}.lastReconciledAt")
      end
    end

    def validate_artifacts!(artifacts)
      raise LockfileMigrationError, "v1 installedArtifacts must be an array" unless artifacts.is_a?(Array)

      seen_ids = {}
      seen_outputs = {}
      artifacts.each_with_index do |artifact, index|
        raise LockfileMigrationError, "v1 artifact #{index} must be an object" unless artifact.is_a?(Hash)
        %w[id kind scope sourcePath outputPath].each do |key|
          unless non_empty_string?(artifact[key])
            raise LockfileMigrationError, "v1 artifact #{index}.#{key} is required"
          end
        end
        %w[sourceChecksum lastAppliedOutputChecksum].each do |key|
          unless artifact[key].to_s.match?(SHA256)
            raise LockfileMigrationError, "v1 artifact #{index}.#{key} must be a SHA-256 digest"
          end
        end
        unless artifact["managed"] == true || artifact["managed"] == false
          raise LockfileMigrationError, "v1 artifact #{index}.managed must be boolean"
        end

        normalize_path(artifact.fetch("sourcePath"))
        output_path = normalize_path(artifact.fetch("outputPath"))
        id = artifact.fetch("id")
        if seen_ids.key?(id)
          raise LockfileMigrationError, "duplicate v1 artifact id #{id}: indexes #{seen_ids.fetch(id)} and #{index}"
        end
        if seen_outputs.key?(output_path)
          raise LockfileMigrationError,
                "duplicate v1 artifact output #{output_path}: indexes #{seen_outputs.fetch(output_path)} and #{index}"
        end
        seen_ids[id] = index
        seen_outputs[output_path] = index
        validate_artifact_output!(artifact, output_path, index)
        validate_resource_manifest!(artifact["resourceManifest"], index) if artifact.key?("resourceManifest")
      end
    end

    def validate_artifact_output!(artifact, output_path, index)
      return if workflow_artifact?(artifact)

      expected_scope = STATIC_OUTPUT_SCOPES[output_path]
      unless expected_scope
        raise LockfileMigrationError, "v1 artifact #{index} has a non-managed output path: #{output_path}"
      end
      return if artifact["scope"] == expected_scope

      raise LockfileMigrationError,
            "v1 artifact #{index} scope #{artifact['scope']} does not match output #{output_path}"
    end

    def validate_resource_manifest!(resources, artifact_index)
      unless resources.is_a?(Array)
        raise LockfileMigrationError, "v1 artifact #{artifact_index}.resourceManifest must be an array"
      end

      resources.each_with_index do |resource, resource_index|
        unless resource.is_a?(Hash)
          raise LockfileMigrationError,
                "v1 artifact #{artifact_index} resource #{resource_index} must be an object"
        end
        normalize_path(resource.fetch("path"))
        %w[sourceChecksum lastAppliedOutputChecksum].each do |key|
          unless resource[key].to_s.match?(SHA256)
            raise LockfileMigrationError,
                  "v1 artifact #{artifact_index} resource #{resource_index}.#{key} must be a SHA-256 digest"
          end
        end
      rescue KeyError => e
        raise LockfileMigrationError,
              "v1 artifact #{artifact_index} resource #{resource_index} missing field: #{e.key}"
      end
    end

    def classify_artifact(artifact, prompt_paths, skill_paths)
      source_path = normalize_path(artifact.fetch("sourcePath"))
      output_path = normalize_path(artifact.fetch("outputPath"))

      if (match = output_path.match(%r{\A\.agents/prompts/([^/]+)\.md\z}))
        name = match[1]
        expected_source = prompt_paths[name]
        raise_unregistered!(artifact, output_path) unless expected_source
        require_matching_name!(artifact, name)
        unless source_path == expected_source
          raise LockfileMigrationError, "legacy prompt source does not match #{name}: #{source_path}"
        end

        return {
          kind: "portable_prompt",
          scope: "portable_prompts",
          name: name,
          source_path: expected_source,
          output_path: output_path,
          mirror: nil
        }
      end

      match = output_path.match(%r{\A\.(agents|claude)/skills/([^/]+)/SKILL\.md\z})
      raise_unregistered!(artifact, output_path) unless match

      mirror, name = match.captures
      expected_source = skill_paths[name]
      raise_unregistered!(artifact, output_path) unless expected_source
      require_matching_name!(artifact, name)
      require_matching_capability!(artifact, name)
      unless valid_legacy_skill_source?(source_path, expected_source, name, artifact["vendor"])
        raise LockfileMigrationError, "legacy skill source does not map to #{name}: #{source_path}"
      end

      {
        kind: "portable_skill",
        scope: "portable_skills",
        name: name,
        source_path: expected_source,
        output_path: output_path,
        mirror: mirror
      }
    end

    def reconcile_artifact!(artifact, registration, source_root, output_root)
      source_file = safe_join(source_root, registration.fetch(:source_path))
      output_file = safe_join(output_root, registration.fetch(:output_path))
      verify_same_file!(source_file, output_file, artifact_id(artifact), source_root, output_root)

      name = registration.fetch(:name)
      mirror = registration.fetch(:mirror)
      artifact["id"] = artifact_identity(registration)
      artifact["kind"] = registration.fetch(:kind)
      artifact["scope"] = registration.fetch(:scope)
      artifact["name"] = name
      artifact["sourcePath"] = registration.fetch(:source_path)
      artifact["outputPath"] = registration.fetch(:output_path)
      artifact["sourceChecksum"] = checksum(source_file)
      artifact["lastAppliedOutputChecksum"] = checksum(output_file)
      artifact["resourceManifest"] = if registration.fetch(:kind) == "portable_skill"
                                       reconcile_resources(source_file, output_file, mirror == "claude")
                                     else
                                       []
                                     end
      strip_legacy_metadata(artifact)
    end

    def reconcile_resources(source_file, output_file, exact_destination)
      source_directory = source_file.dirname
      output_directory = output_file.dirname
      managed_files = real_relative_files(source_directory, source_directory) - ["SKILL.md"]

      resources = managed_files.map do |relative_path|
        source_resource = safe_join(source_directory, relative_path)
        output_resource = safe_join(output_directory, relative_path)
        verify_same_file!(source_resource, output_resource, relative_path, source_directory, output_directory)
        {
          "path" => relative_path,
          "sourceChecksum" => checksum(source_resource),
          "lastAppliedOutputChecksum" => checksum(output_resource)
        }
      end

      if exact_destination
        extras = relative_entries(output_directory) - real_relative_files(source_directory, source_directory)
        unless extras.empty?
          raise LockfileMigrationError, "Claude mirror contains unregistered files: #{extras.join(', ')}"
        end
      end

      resources
    end

    def migrate_scopes!(lockfile, migrated_scopes, manifest_digest, resolved_commit, reconciled_at)
      scopes = lockfile.fetch("scopes")
      legacy_scope = scopes.delete("vendor_adapters")
      scopes["portable_skills"] ||= legacy_scope if legacy_scope

      migrated_scopes.each do |scope|
        scopes[scope] ||= {}
        scopes[scope]["resolvedCommit"] = resolved_commit
        scopes[scope]["manifestDigest"] = manifest_digest
        scopes[scope]["lastReconciledAt"] = reconciled_at
      end
    end

    def valid_legacy_skill_source?(source_path, expected_source, name, vendor)
      return true if source_path == expected_source
      return true if source_path == "capabilities/#{name}/capability.yaml"

      adapter_match = source_path.match(%r{\Acapabilities/#{Regexp.escape(name)}/vendors/([^/]+)\.md\z})
      adapter_match && (!vendor || vendor == adapter_match[1])
    end

    def require_matching_name!(artifact, expected)
      return unless artifact["name"] && artifact["name"] != expected

      raise LockfileMigrationError, "artifact name #{artifact['name']} does not match output #{expected}"
    end

    def require_matching_capability!(artifact, expected)
      return unless artifact["capability"] && artifact["capability"] != expected

      raise LockfileMigrationError, "capability #{artifact['capability']} does not match skill #{expected}"
    end

    def raise_unregistered!(artifact, output_path)
      raise LockfileMigrationError, "legacy artifact has no registered destination: #{artifact_id(artifact)} (#{output_path})"
    end

    def verify_same_file!(expected, actual, label, expected_root, actual_root)
      raise LockfileMigrationError, "missing registered source: #{expected}" unless expected.file?
      raise LockfileMigrationError, "missing reconciled output for #{label}: #{actual}" unless actual.file?
      if symlink_component?(expected, expected_root)
        raise LockfileMigrationError, "registered source uses a symlink for #{label}: #{expected}"
      end
      if symlink_component?(actual, actual_root)
        raise LockfileMigrationError, "reconciled output uses a symlink for #{label}: #{actual}"
      end
      return if expected.binread == actual.binread

      raise LockfileMigrationError, "reconciled output differs from registered source for #{label}: #{actual}"
    end

    def artifact_identity(registration)
      prefix = registration.fetch(:kind)
      suffix = registration.fetch(:mirror) == "claude" ? ":claude" : ""
      "#{prefix}:#{registration.fetch(:name)}#{suffix}"
    end

    def artifact_id(artifact)
      artifact.fetch("id", artifact.inspect)
    end

    def strip_legacy_metadata(artifact)
      artifact.delete("capability")
      artifact.delete("vendor")
    end

    def normalize_preserved_artifact!(artifact)
      artifact["sourcePath"] = normalize_path(artifact.fetch("sourcePath"))
      artifact["outputPath"] = normalize_path(artifact.fetch("outputPath"))
      artifact.fetch("resourceManifest", []).each do |resource|
        resource["path"] = normalize_path(resource.fetch("path"))
      end
    end

    def relative_entries(directory)
      return [] unless directory.directory? || directory.symlink?

      directory.glob("**/*", File::FNM_DOTMATCH)
        .select { |path| path.file? || path.symlink? }
        .map { |path| path.relative_path_from(directory).to_s.tr("\\", "/") }
        .sort
    end

    def real_relative_files(directory, boundary)
      entries = directory.glob("**/*", File::FNM_DOTMATCH)
      symlink = entries.find { |path| path.symlink? || symlink_component?(path, boundary) }
      raise LockfileMigrationError, "registered source contains a symlink: #{symlink}" if symlink

      entries.select(&:file?)
        .map { |path| path.relative_path_from(directory).to_s.tr("\\", "/") }
        .sort
    end

    def symlink_component?(path, boundary)
      current = path
      loop do
        return true if current.symlink?
        return false if current == boundary || current == current.parent

        current = current.parent
      end
    end

    def checksum(path)
      "sha256:#{Digest::SHA256.file(path).hexdigest}"
    end

    def safe_join(root, relative_path)
      normalized = normalize_path(relative_path)
      candidate = (root / normalized).expand_path
      root_prefix = "#{root.to_s.sub(/[\\\/]\z/, '')}#{File::SEPARATOR}"
      return candidate if candidate == root || candidate.to_s.start_with?(root_prefix)

      raise LockfileMigrationError, "path escapes root: #{relative_path}"
    end

    def normalize_path(path)
      value = path.to_s.tr("\\", "/")
      pathname = Pathname(value)
      normalized = pathname.cleanpath.to_s.tr("\\", "/")
      if value.empty? || normalized == "." || value.start_with?("//") || pathname.absolute? ||
         value.match?(/\A[A-Za-z]:\//) || value.split("/").include?("..")
        raise LockfileMigrationError, "unsafe repository-relative path: #{path}"
      end

      normalized
    end

    def validate_provenance!(manifest_digest, resolved_commit, reconciled_at)
      raise LockfileMigrationError, "invalid manifest digest" unless manifest_digest.to_s.match?(SHA256)
      raise LockfileMigrationError, "invalid resolved commit" unless resolved_commit.to_s.match?(COMMIT)

      validate_timestamp!(reconciled_at, "reconciliation timestamp")
    end

    def validate_timestamp!(value, label)
      Time.iso8601(value)
    rescue ArgumentError, TypeError
      raise LockfileMigrationError, "invalid #{label}"
    end

    def non_empty_string?(value)
      value.is_a?(String) && !value.empty?
    end

    def deep_copy(value)
      JSON.parse(JSON.generate(value))
    end
  end
end

if $PROGRAM_NAME == __FILE__
  unless ARGV.length == 10
    warn "usage: ruby migrate_lockfile.rb <manifest.yaml> <consumer-root> <input.json> <output.json> <expected-repo> <expected-branch> <expected-requested-ref> <manifest-digest> <resolved-commit> <reconciled-at>"
    exit 2
  end

  manifest_path, consumer_root, input_path, output_path, expected_repo, expected_branch, expected_requested_ref,
    manifest_digest, resolved_commit, reconciled_at = ARGV

  begin
    manifest_file = Pathname(manifest_path).expand_path
    raise AgentWorkbench::LockfileMigrationError, "input and output paths must differ" if Pathname(input_path).expand_path == Pathname(output_path).expand_path

    manifest = YAML.safe_load_file(manifest_file)
    input = AgentWorkbench::LockfileMigration.read_json(input_path)
    migrated = AgentWorkbench::LockfileMigration.migrate(
      input,
      manifest,
      workbench_root: manifest_file.dirname,
      consumer_root: consumer_root,
      expected_repo: expected_repo,
      expected_branch: expected_branch,
      expected_requested_ref: expected_requested_ref,
      manifest_digest: manifest_digest,
      resolved_commit: resolved_commit,
      reconciled_at: reconciled_at
    )
    AgentWorkbench::LockfileMigration.write_json(output_path, migrated)
  rescue KeyError, JSON::ParserError, Psych::Exception, AgentWorkbench::LockfileMigrationError => e
    warn "lockfile migration failed: #{e.message}"
    exit 1
  end
end
