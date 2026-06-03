# mathlib Patch Rules

This repository keeps temporary upstream-style material under
`QuadraticNumberFields/Mathlib/`. These files are local patches for facts that
belong in mathlib but are not yet available in the pinned dependency.

## Placement

- Prefer patching a local mirror of an existing mathlib file.
  If a declaration belongs in `Mathlib/Foo/Bar.lean`, put the local patch in
  `QuadraticNumberFields/Mathlib/Foo/Bar.lean`.
- Do not create a new local mathlib file unless the corresponding new file
  would also be the right upstream mathlib file.
- Place declarations by mathematical ownership, not by the project file that
  first needs them. For example, a theorem about `Algebra.IsQuadraticExtension`
  belongs near field theory or algebra APIs, not in a prime-splitting file.
- Split patches when their dependencies belong to different layers. A pure
  field-theory lemma should not import ramification theory just because a later
  bridge lemma uses both.

## Generality

- State local mathlib patches as generally as the proof reasonably supports.
  Avoid project-specific types such as `Qsqrtd`, `Zsqrtd`, or concrete integer
  parameters unless the intended upstream target is itself about those objects.
- Minimize assumptions. Do not require `[NumberField K]`, `[CharZero R]`,
  Dedekind hypotheses, squarefreeness, or nonzero parameters when weaker
  assumptions such as finite dimensionality, separability, `ringChar F ≠ 2`, or
  domain/fraction-ring hypotheses suffice.
- Prefer typeclass assumptions that match the upstream API around the target
  declaration. Do not add convenience assumptions merely to make local instance
  search easier.
- If a theorem naturally decomposes into a general lemma plus a specialized
  application, upstream the general lemma and keep the specialized application
  in the project layer unless it is also mathlib-scope.

## Imports

- Keep imports as narrow as practical. A patch file should import the existing
  mathlib file it mirrors and only the additional files needed for the new
  declarations.
- Avoid introducing heavy downstream imports into an upstream-layer mirror when
  only one declaration needs them. Put that declaration in the lower layer that
  already owns those imports.
- Re-export local mathlib patches from `QuadraticNumberFields/Mathlib.lean`
  once they are intended for use outside their immediate file.

## Style

- Start every local mathlib patch file with a module docstring saying
  `Material destined for mathlib.`
- Follow mathlib naming, theorem shape, docstring, and import style.
- When a result lands upstream, replace local imports/usages with the upstream
  declaration and delete the local shim in the same change.
