# Project workflow

- Truthfulness is the core requirement. Never fabricate implementations, proofs,
  validation results, or progress. Report failures, incomplete work, unfavorable
  results, and uncertainty accurately. Distinguish proved results, conditional
  results, numerical evidence, and planned work.
- Keep project work inside this repository.
- Commit and push completed milestones to the configured GitHub remote after
  appropriate validation and review, without asking again for routine pushes.
  Work on the existing `main` branch; do not create additional branches.
- Maintain `.gitignore` as the project evolves. Never commit anything under
  `docs/`; keep those files local.
- Do not commit scratch files, intermediate outputs, generated test reports,
  logs, caches, or other disposable artifacts. Keep only useful project source,
  configuration, and public documentation in Git.
- Never commit secrets or personal information, including API keys, passwords,
  credentials, private names, addresses, or private course records. Public
  scholarly attribution is appropriate.
- Ignore rules only filter paths. Review the full staged diff and any new files
  for sensitive content before every commit and push, including example configs.
  Stage reviewed files explicitly and do not force-add ignored files.
- Use the repository's public GitHub alias and noreply email for commit identity;
  do not introduce a private name or personal email into commit metadata.
- Keep `README.md` and `README-zh.md` aligned, with their language links below
  the top-level titles. Describe planned work as planned, not completed.

# Local documentation

- Markdown files directly under `docs/` are concise, human-facing documents.
  Only the human user may create these files. Edit an existing file there only
  when the user instructs you to write or update its contents; never create a
  missing top-level document yourself.
- Subdirectories under `docs/` hold detailed working material for Codex,
  organized by project phase, component, or task. Proactively create and maintain
  these subdirectories and their Markdown notes when useful for implementation.
  Reference papers and supporting material may also be kept there.
- Preserve the distinction between concise human-facing outlines and detailed
  implementation notes. All contents of `docs/` remain local and uncommitted.
