---
name: math-pdf-reader
description: Read, transcribe, summarize, or verify mathematical PDFs with high fidelity by combining rendered-page inspection, cautious text extraction, version-matched source checks, and explicit uncertainty. Use for theorem, proof, formula, notation, attribution, or bibliographic work where ordinary PDF text extraction can silently corrupt mathematical content.
---

<!-- agent-workbench: managed portable-skill -->

# Math PDF Reader

## Dispatch

Use the exact model, effort, delivery boundary, and escalation rule for
`math-pdf-reader` in `AI_AGENT_GUIDE.md`'s **Skill Model and Reasoning Routing**
table. Literal navigation and metadata extraction are peripheral work;
mathematical verification or interpretation is research-mathematics work, and
main-theorem or adversarial proof audit is critical-proof work.

## Evidence Principles

- Treat the requested PDF version as the ground truth.
- Treat embedded PDF text and OCR as navigation aids, not authority for formulas, symbols, numbering, or punctuation.
- Treat TeX or other source files as authority only after checking version identity. If the source and PDF differ, prefer the rendered PDF for the requested version.
- Use mathematical reasoning to detect inconsistencies or impossible readings, not to fill unreadable symbols, repair formulas, or replace evidence.
- Treat search-result snippets, abstracts, reviews, and memory as non-evidence for the PDF text itself.
- Prefer an explicit uncertainty marker over a polished but unsupported reading.
- Fail closed: if the evidence does not support a faithful reading, identify what cannot be read instead of producing a plausible reconstruction.

## Workflow

1. Establish the evidence boundary.
   - Identify whether the PDF is user-supplied/private or public.
   - For private PDFs, do not upload the PDF, page images, cropped snippets, OCR text, titles, theorem statements, or other identifying content to external services without explicit permission.
   - Classify the task as exact transcription, theorem/proof extraction, summary/explanation, verification/critique, or bibliographic/attribution extraction.
2. Extract text only for navigation.
   - Use embedded text or local OCR to find pages, sections, theorem numbers, equation numbers, and search terms.
   - Do not trust extracted formulas, subscripts, superscripts, Greek letters, arrows, accents, primes, hats, bars, calligraphic letters, diagrams, or equation numbering without visual or version-matched source validation.
3. Render and inspect the relevant pages.
   - Render target pages at a resolution high enough for symbol-level inspection; use 300--600 dpi or equivalent zoom when practical.
   - For exact transcription or quotation, verify every mathematical symbol against the rendered page image.
   - Check line breaks, punctuation, accents, primes, bars, hats, subscripts, superscripts, arrows, relation symbols, brackets, and equation labels.
4. Search for source material only when appropriate.
   - Prefer arXiv source, author-hosted TeX, official repositories, publisher supplements, or official project pages.
   - Before using source text as evidence, verify title, authors, date/version, arXiv version or DOI when available, theorem/equation numbering, surrounding text, and page or section alignment.
   - If identity is uncertain, use the source only as a hint and mark source-resolved readings as uncertain.
5. Cross-check the evidence streams.
   - Compare extracted text or OCR, rendered pages, and version-matched source when available.
   - If they conflict, report the conflict and prefer the rendered page for the requested PDF.
   - Do not silently normalize notation, punctuation, or wording.
6. Apply mathematical consistency checks conservatively.
   - Check sources and targets of maps, variable binding, hypotheses, signs, indices, domains, codomains, dimensions, equation syntax, and notation consistency.
   - Use these checks to flag suspicious readings, not to rewrite the PDF.
   - Mark any editorial repair as inferred and separate it from the faithful reading.
7. Report uncertainty explicitly.
   - Use short markers such as `[uncertain: rendered symbol resembles \xi or x]`.
   - Distinguish PDF-verified, source-verified, OCR-derived, and inferred content.
   - If a symbol, word, or formula cannot be read reliably, leave it uncertain rather than guessing.
8. Cite concrete anchors.
   - Use page numbers and, when available, section, theorem/proposition/definition, proof paragraph, display, equation, figure, or line anchors.
   - Distinguish the PDF viewer's page index from a printed page number when they differ.
   - For external source validation, include the URL and version information such as arXiv version, repository path, tag, or commit when available.

## Strictness by Task

- Exact transcription or quotation: require rendered-page verification of every mathematical symbol and preserve wording, notation, punctuation, and displayed layout as closely as practical.
- Theorem/proof extraction: preserve hypotheses, quantifiers, notation, numbering, and dependency context; do not shorten unless asked.
- Summary or explanation: cite page, section, or theorem anchors and separate what the PDF states from interpretation.
- Verification or critique: state the claim being checked, anchors inspected, evidence used, and strongest justified conclusion.
- Bibliographic or attribution extraction: use only explicit PDF/source evidence or authoritative metadata; never infer missing publication facts from context or memory.

## Output Standard

- When accuracy matters, begin with a brief method note: pages inspected, whether page images were rendered, whether OCR or text extraction was used, and whether a version-matched source was found.
- For exact transcription, optimize fidelity over fluency and preserve uncertainty markers.
- Do not silently correct spelling, notation, numbering, grammar, hyphenation, or apparent typographical errors. Put proposed corrections in separate editorial notes.
- Give confidence only in evidence-backed terms: high for symbol-level PDF verification, medium for version-matched source plus partial visual checks, and low for OCR-derived or unresolved readings.
- For mathematical explanation, follow the target project's writing conventions when present; otherwise state the verdict first when appropriate, verify hypotheses before applying theorems, and give only the strongest justified conclusion.
- If rendered inspection, OCR, or source lookup cannot be performed, name the missing evidence stream and lower confidence accordingly.

## Safety and Privacy

- Treat user-provided PDFs as private unless the user gives a public URL or explicitly identifies the document as public.
- Do not upload private PDFs, page images, snippets, or OCR text to external OCR, AI, translation, search, or conversion services without explicit user permission.
- Do not infer publication metadata, attributions, dates, identifiers, or bibliographic facts from memory.
- Do not cite an online source as matching until version identity has been checked.
