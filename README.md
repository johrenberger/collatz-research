# Collatz Research

Research infrastructure for mechanically checked intermediate statements about the accelerated Collatz map. This repository does **not** claim a proof of the Collatz conjecture.

## Scope

The project treats discovery and verification as separate concerns:

- Python enumerates, symbolically executes, and emits candidate certificates. It is untrusted.
- Lean checks definitions, certificate predicates, and proved lemmas. Only a successful Lean build is evidence of a formal result.
- JSON certificates are versioned, deterministic inputs to the verifier—not proofs by themselves.

The initial target is the accelerated map on positive odd integers:

\[
T(n) = (3n + 1) / 2^{v_2(3n+1)}.
\]

See [docs/mathematical-model.md](docs/mathematical-model.md), [docs/trust-model.md](docs/trust-model.md), and [docs/theorem-status.md](docs/theorem-status.md).

The gap between what the project has formalized and a global convergence claim — what is proven, what is assumed, and what is still open — is specified in [docs/convergence-frontier.md](docs/convergence-frontier.md).

## Quick start (workstation)

Prerequisites: Python 3.12+, [uv](https://docs.astral.sh/uv/), and the Lean version in `lean-toolchain`.

```sh
uv sync --group dev
uv run pytest
lake update
lake build
```

Use `make check` after dependencies are installed. Discovery experiments belong under `experiments/`; checked theorem development belongs under `Lean/`.

## Layout

```text
python/       untrusted discovery and certificate generation
Lean/         trusted formal definitions and proof development
schemas/      versioned JSON certificate contracts
docs/         architecture, protocol, status, and decisions
tests/        Python unit and schema tests
scripts/      reproducible local entry points
experiments/  parameterized, non-authoritative runs
paper/        manuscript sources and reproducibility appendix
```

## Research rules

1. Computational checks never establish universal claims.
2. Every theorem-status entry links to a Lean declaration and its build command.
3. Generated artifacts are reproducible from committed code and declared inputs.
4. No experiment output is presented as a mathematical result until independently reviewed and formalized.

## License and citation

License selection and contributor policy are intentionally pending maintainer direction. Cite the repository using `CITATION.cff` once maintainer metadata is completed.
