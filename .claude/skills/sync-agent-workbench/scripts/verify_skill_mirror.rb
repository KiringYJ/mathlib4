# frozen_string_literal: true

require "pathname"
require "yaml"

module AgentWorkbench
  class SkillMirrorVerificationError < StandardError; end

  module SkillMirror
    module_function

    def verify(workbench_root, consumer_root, claude: false)
      source_root = Pathname(workbench_root).expand_path
      output_root = Pathname(consumer_root).expand_path
      manifest = YAML.safe_load_file(source_root / "manifest.yaml")
      errors = []

      manifest.fetch("portable_skills").each do |name, registration|
        source_file = safe_join(source_root, registration.fetch("path"))
        source_directory = source_file.dirname
        unless source_file.file?
          raise SkillMirrorVerificationError, "missing registered source: #{source_file}"
        end
        if symlink_component?(source_file, source_root)
          raise SkillMirrorVerificationError, "registered source uses a symlink: #{source_file}"
        end
        managed_files = real_relative_files(source_directory, source_root)
        destinations = { ".agents" => safe_join(output_root, ".agents/skills/#{name}") }
        destinations[".claude"] = safe_join(output_root, ".claude/skills/#{name}") if claude

        destinations.each do |label, destination|
          if symlink_component?(destination, output_root)
            errors << "#{label}/skills/#{name}: skill directory is a symlink"
            next
          end

          managed_files.each do |relative_path|
            expected = safe_join(source_directory, relative_path)
            actual = safe_join(destination, relative_path)
            if symlink_component?(actual, output_root)
              errors << "#{label}/skills/#{name}/#{relative_path}: managed path is a symlink"
            elsif !actual.file?
              errors << "#{label}/skills/#{name}/#{relative_path}: missing managed file"
            elsif expected.binread != actual.binread
              errors << "#{label}/skills/#{name}/#{relative_path}: content differs from registered source"
            end
          end
        end

        next unless claude

        claude_destination = destinations.fetch(".claude")
        next if symlink_component?(claude_destination, output_root)

        extra_claude_files = relative_entries(claude_destination) - managed_files
        extra_claude_files.each do |relative_path|
          errors << ".claude/skills/#{name}/#{relative_path}: unregistered mirror file"
        end
      end

      errors
    end

    def real_relative_files(directory, boundary)
      unless directory.directory?
        raise SkillMirrorVerificationError, "missing registered source directory: #{directory}"
      end
      if symlink_component?(directory, boundary)
        raise SkillMirrorVerificationError, "registered source uses a symlink: #{directory}"
      end

      entries = directory.glob("**/*", File::FNM_DOTMATCH)
      symlink = entries.find { |path| path.symlink? || symlink_component?(path, boundary) }
      if symlink
        raise SkillMirrorVerificationError, "registered source contains a symlink: #{symlink}"
      end

      entries.select(&:file?)
        .map { |path| path.relative_path_from(directory).to_s.tr("\\", "/") }
        .sort
    end

    def relative_entries(directory)
      return [] unless directory.directory? || directory.symlink?

      directory.glob("**/*", File::FNM_DOTMATCH)
        .select { |path| path.file? || path.symlink? }
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

    def safe_join(root, relative_path)
      value = relative_path.to_s.tr("\\", "/")
      pathname = Pathname(value)
      normalized = pathname.cleanpath.to_s.tr("\\", "/")
      if value.empty? || normalized == "." || value.start_with?("//") || pathname.absolute? ||
         value.match?(/\A[A-Za-z]:\//) || value.split("/").include?("..")
        raise SkillMirrorVerificationError, "unsafe repository-relative path: #{relative_path}"
      end

      candidate = (root / normalized).expand_path
      root_prefix = "#{root.to_s.sub(/[\\\/]\z/, '')}#{File::SEPARATOR}"
      return candidate if candidate == root || candidate.to_s.start_with?(root_prefix)

      raise SkillMirrorVerificationError, "path escapes root: #{relative_path}"
    end
  end
end

if $PROGRAM_NAME == __FILE__
  unless ARGV.length.between?(2, 3) && (ARGV[2].nil? || ARGV[2] == "--claude")
    warn "usage: ruby verify_skill_mirror.rb <workbench-root> <consumer-root> [--claude]"
    exit 2
  end

  begin
    errors = AgentWorkbench::SkillMirror.verify(ARGV[0], ARGV[1], claude: ARGV[2] == "--claude")
    if errors.empty?
      puts "SKILL_MIRROR=PASS"
    else
      warn errors.join("\n")
      exit 1
    end
  rescue KeyError, Psych::Exception, AgentWorkbench::SkillMirrorVerificationError => e
    warn "skill mirror verification failed: #{e.message}"
    exit 1
  end
end
