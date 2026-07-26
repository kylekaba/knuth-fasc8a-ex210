# Project wiki maintenance

This directory is the persistent, LLM-maintained knowledge layer for the
Knuth Fascicle 8A Exercise 210 formalization. Repository sources, certificates,
and documents outside `wiki/` are the source of truth; do not modify them merely
to make a wiki claim true.

## Workflow

1. Read `index.md` before answering project-history or architecture questions.
2. Verify material claims against the linked repository source before editing a
   page. Prefer theorem names, file links, and reproducible commands to prose
   assertions.
3. Update every affected topic page, then update `index.md` if pages were added,
   renamed, or materially re-scoped.
4. Append one dated entry to `log.md`; never rewrite its earlier entries.
5. During lint passes, check stale progress counts, broken relative links,
   contradictory claims, orphan pages, and claims lacking a source link.

## Conventions

- Use lowercase kebab-case filenames.
- Begin topic pages with YAML frontmatter containing `title`, `updated`, and
  `tags`.
- Use Obsidian-compatible relative links such as `[Current status](current-status.md)`.
- Distinguish `proved in Lean`, `checked by an executable`, and `planned`.
- Treat generated `.olean` files and local build output as caches, not sources.
- Never ingest local secrets, credentials, `cli.txt`, or ignored build output.
- Keep pages compact enough to audit against the repository in one sitting.
