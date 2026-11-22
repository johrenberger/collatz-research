# Project skills

These are the version-controlled canonical copies of the Collatz Research
OpenClaw skills. Runtime installations under `/data/.openclaw/skills/` and
`/data/.openclaw/workspace/skills/` should link to these directories so existing
skill names and runtime discovery paths remain unchanged.

Run `scripts/install-openclaw-skills.sh` from this checkout to install or check
those links. The installer refuses to replace an existing runtime skill whose
contents differ from the repository copy; reconcile the difference first.
After cloning on another machine, run the installer to expose these skills to
that environment's existing global and workspace skill directories.
