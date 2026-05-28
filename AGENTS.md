# AGENTS.md

Main instructions for AI agents working in this repository.

## Agent Operating Rules

- Work autonomously on clear, safe, reversible tasks.
- Ask only when the next step is ambiguous, destructive, irreversible, or requires missing authority.
- Read the relevant Lean files before changing them.
- Keep diffs small, reviewable, and reversible.
- Prefer deletion, reuse, and local patterns over new abstractions.
- Do not add dependencies unless explicitly requested.
- Preserve user changes; never revert unrelated work.
- For simple repository lookups, prefer `rg`, `rg --files`, or `omx explore` when available.
- Use Codex native subagents only for independent bounded subtasks where parallelism improves quality or speed.

## Project Overview

This is a Lean 4 formalization of quadratic number fields `Q(√d)` and the
classification of their rings of integers, built on mathlib's
`QuadraticAlgebra`.

Core objects:

- `Qsqrtd (d : ℚ) := QuadraticAlgebra ℚ d 0`
- Parameters are usually explicit `Fact` instances:
  `[Fact (Squarefree d)] [Fact (d ≠ 1)]`
- Candidate integer rings:
  - `Zsqrtd d`
  - `ZOnePlusSqrtOverTwo k`

Main theorem files:

- `QuadraticNumberFields/RingOfIntegers/Classification.lean`
- `QuadraticNumberFields/RingOfIntegers/Discriminant.lean`
- `QuadraticNumberFields/RingOfIntegers/ZsqrtdMathlibInstances.lean`

Main declarations:

- `ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one`
- `ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one`
- `ringOfIntegers_classification`
- `discr_formula`
- `isDedekindDomain_iff_mod_four_ne_one`

## Repository Layout

- `QuadraticNumberFields.lean` re-exports the public library.
- `QuadraticNumberFields/Basic.lean` defines `Qsqrtd` and basic trace/norm API.
- `QuadraticNumberFields/Instances.lean` provides field and number field instances.
- `QuadraticNumberFields/Parameters.lean` handles squarefree normalization,
  rescaling, and parameter uniqueness.
- `QuadraticNumberFields/FieldClassification.lean` classifies quadratic fields by
  squarefree parameters.
- `QuadraticNumberFields/TotallyRealComplex.lean` proves real/complex/CM behavior.
- `QuadraticNumberFields/RingEquiv.lean` transfers Dedekind-domain structure
  across ring equivalences.
- `QuadraticNumberFields/RingOfIntegers/` contains the integer-ring
  classification, trace/norm preliminaries, mod-4 arithmetic, discriminants,
  and `Zsqrtd` ideal theory.
- `QuadraticNumberFields/Euclidean/Basic.lean` contains the norm-Euclidean
  classification framework.
- `QuadraticNumberFields/Examples/ZsqrtdNeg5/` contains verified examples for
  `ℤ[√(-5)]`.
- `blueprint/` contains leanblueprint sources.
- `home_page/` contains the GitHub Pages/docgen homepage content.

## Dependencies And Build

Current dependency versions are defined in `lakefile.toml` and `lean-toolchain`.
As of this file, the project uses Lean/mathlib/repl `v4.30.0-rc2`.

Useful commands:

```bash
lake exe cache get
lake build
```

Only run `lake build` when Lean files were modified or a full build is needed.
For targeted Lean changes, use Lean diagnostics first when available.

## Lean Workflow

- Use the `lean4` and `mathlib-style` skills when writing, editing, or reviewing
  Lean code.
- Follow mathlib style.
- Use existing project APIs and naming conventions before adding new helpers.
- Add module docstrings to new Lean files.
- Add docstrings to public definitions and theorems.
- Keep theorem statements stable unless the task requires changing them.
- Preserve `-- ANCHOR: name --` and `-- ANCHOR_END:` comments; they are used by
  documentation tooling.
- Prefer local checks on changed files before full builds.
- After Lean edits, verification should normally be:
  1. Lean diagnostics for each modified Lean file.
  2. `lake build` if the change affects imports, shared declarations, or public API.

## Ring-Of-Integers Architecture

The ring-of-integers proof is organized around:

- `ModFour.lean`: arithmetic modulo 4.
- `TraceNorm.lean`: trace/norm facts used by integrality proofs.
- `HalfInt.lean`: half-integer normal forms.
- `Zsqrtd.lean`: the `ℤ[√d]` model and embedding into `Qsqrtd`.
- `ZOnePlusSqrtOverTwo.lean`: the `ℤ[(1+√d)/2]` model.
- `Integrality.lean`: integral-closure constructions and normal-form arguments.
- `Classification.lean`: the final classification equivalences.
- `Norm.lean`: norm formulas and unit criteria.
- `Discriminant.lean`: field discriminant formula.
- `ZsqrtdIdeals.lean`: ideal membership, quotients, and primality.
- `ZsqrtdMathlibInstances.lean`: Dedekind-domain characterization for mathlib's
  `Zsqrtd`.

Keep new lemmas near the proof that needs them unless they clearly belong in one
of these shared files.

## mathlib Sync

Some basic quadratic-field material is intended to sync with mathlib PRs.

Likely mathlib-scope content:

- `Qsqrtd`
- basic trace/norm lemmas
- squarefree/rescaling facts
- parameter uniqueness
- general quadratic-field classification helpers

Project-only content for now:

- ring of integers classification
- discriminant formula
- Dedekind-domain characterization for `Zsqrtd`
- Euclidean-domain classification
- concrete ideal-theory examples

When syncing with mathlib, verify signatures, imports, docstrings, and style in
both repositories.

## OMX / Skills

- OMX is available, but runtime-only workflows such as `ralph`, `team`,
  `ultrawork`, `ultraqa`, and `ecomode` require an actual OMX CLI/tmux runtime.
- In Codex App or outside-tmux sessions, do not pretend those runtime workflows
  are active; use direct execution, planning, or native subagents instead.
- Use workflow skills when the user explicitly invokes them or the request
  clearly matches:
  - `analyze` / `investigate`: read-only deep analysis.
  - `plan this`: planning only.
  - `deep interview`: clarify requirements before implementation.
  - `code review`: review findings first, ordered by severity.
  - `cleanup` / `refactor` / `deslop`: write a cleanup plan first and protect
    behavior with tests where practical.

## Git And Commits

- Check `git status` before and after substantial work.
- Do not commit unless the user asks.
- Do not include Claude session URLs in commit messages.
- Commit messages should explain why the change was made.
- Prefer the repository's Lore protocol trailers when making commits:
  `Constraint:`, `Rejected:`, `Confidence:`, `Scope-risk:`, `Directive:`,
  `Tested:`, `Not-tested:`.
- Author identity should be:
  - Name: `Frankie Wang`
  - Email: `git@frankie.wang`
  - GitHub: `FrankieeW`

## Verification And Final Reports

Before claiming completion:

- Confirm the intended files changed.
- Run the relevant checks.
- Read the output of those checks.
- Report verification evidence and any known gaps.

Final reports should include:

- changed files
- verification performed
- remaining risks or skipped checks
