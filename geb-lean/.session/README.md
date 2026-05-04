# Session Context

This directory maintains continuity across Claude Code sessions. After a
conversation restart or compaction, read this directory to pick up context
from previous sessions.

## Structure

- `workstreams/` - One Markdown file per active workstream or project area

## Workstream Files

Each file in `workstreams/` represents an independent line of work. Use the
following template:

```markdown
# Workstream: [Name]

## Status
[Active | Paused ]

## Context
[Brief description of what this workstream is about]

## Tasks
- [ ] Task with enough context to resume
- [ ] Another task

## Notes
[Any other relevant context]
```

## Maintenance

- Archive or delete workstream files when work is complete
