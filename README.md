# ZIVER OOPSLA 2026 Evaluation Reproduction

This checkout is organized around the paper's `Evaluation` section.

The paper has two main experiments:

1. `Table 1`: 7 representative SP1 component benchmarks.
2. `Table 2`: 25 audit-driven SP1 findings, with 16 reproduced and 9 unsupported under the current abstraction.

The repository now exposes those experiments directly through a small set of scripts instead of the earlier ad hoc runners.
Inside `benchmark/`, only the files needed by `exp1` and `exp2` are retained.

## Layout

- `evaluation/oopsla26/exp1_components.tsv`
  - manifest for `Table 1`
- `evaluation/oopsla26/exp2_audits.tsv`
  - manifest for `Table 2`, including the paper-facing `rich` / `unrolled` variant chosen for each supported case
- `scripts/oopsla26_setup.sh`
  - checks the local environment and builds `target/debug/ziver` if needed
- `scripts/oopsla26_exp1.sh`
  - reproduces `Table 1`
- `scripts/oopsla26_exp2.sh`
  - reproduces `Table 2`
- `scripts/oopsla26_reproduce_all.sh`
  - one-click entry point: environment -> experiment 1 -> experiment 2

All generated outputs go to `results/oopsla26/`.

## Paper Environment

The paper reports the following environment:

- Ubuntu `22.04.5` under WSL2, kernel `6.6.87.2`
- AMD Ryzen 9 `9950X3D`, `16` cores / `32` threads
- `30 GiB` RAM
- Rust `1.93.0-nightly`
- cvc5 `1.3.2` at commit `84c7e48`
- Z3 `4.15.3`

The setup script records the current local machine alongside that target environment so that version drift is explicit.

## Requirements

The reproduction scripts expect these commands to exist in `PATH`:

- `cargo`
- `rustc`
- `z3`
- `cvc5`

The current local checkout already builds with:

```bash
cargo build --quiet
```

## Quick Start

Run the full paper-facing workflow:

```bash
./scripts/oopsla26_reproduce_all.sh
```

This produces:

- `results/oopsla26/environment.txt`
- `results/oopsla26/exp1_components.tsv`
- `results/oopsla26/exp2_audits.tsv`

If you want averages instead of single-run wall time:

```bash
./scripts/oopsla26_reproduce_all.sh --iterations 3
```

If you want to force a rebuild before running:

```bash
OOPSLA26_REBUILD=1 ./scripts/oopsla26_reproduce_all.sh
```

## Experiment 1

`scripts/oopsla26_exp1.sh` reproduces the paper's `Table 1`.

Interpretation:

- paper `✓` means the component equivalence check should pass
- paper `✗` means the checker should find an inconsistency

The script prints:

- the paper result
- the local CLI observation
- the current average wall time
- the wall-time delta against the paper
- whether the local wall time matches the paper at `0.001s` precision
- whether the local run matches the paper verdict

## Experiment 2

`scripts/oopsla26_exp2.sh` reproduces the paper's `Table 2`.

Interpretation here is different from experiment 1:

- paper `✓` means the audit finding is reproduced under the current abstraction
- therefore the expected local CLI behavior is a failing equivalence check
- paper `✗` means the case is currently unsupported in this checkout and is listed as `SKIP (not modeled)`

The script prints:

- source audit and finding id
- category `L`, `X`, or `S`
- the paper-facing variant retained for that case
- whether the case is currently modeled
- the local CLI observation
- whether the bug was reproduced
- the local average wall time
- the wall-time delta against the paper
- whether the local wall time matches the paper at `0.001s` precision

At the end it also summarizes:

- reproduced count
- currently supported count
- unsupported count
- reproduced `L` and `X` cases

## Notes

- `Table 2` is intentionally data-driven through the manifest so the paper mapping stays explicit.
- The surviving `benchmark/Audit/SP1/*.cz` files are already the final paper-facing versions; for several cases they were taken from the earlier `rich` or `unrolled` variants to match the published timings.
- Wall times are local measurements and should be treated as reproduction numbers, not as exact copies of the paper's hardware-specific timings.
