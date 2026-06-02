# Designing the `QuadraticField` Abstraction

This document compares four ways of introducing a project-level
"quadratic field" concept on top of mathlib's
`Algebra.IsQuadraticExtension R S`, evaluated against three criteria:

- **Mathlib adaptation** — does the design respect mathlib's
  conventions, idioms, and instance architecture?
- **Elegance** — does the design express the right mathematical
  object with the minimum of bookkeeping?
- **Future extensibility** — can the design absorb new structure
  (chosen basis, primitive generator, distinguished involution,
  fundamental discriminant, …) without redesigning the core?

The comparison is deliberately independent of any pre-existing
project code; the four options are evaluated on their merits.

This document **does not pick a winner**. Sections 1–4 lay out the
options and their properties; section 5 scores each option on each
axis on a 1–5 scale so the reader can apply their own weighting.
The right choice depends on whether the project is primarily an
abstract layer or a computational one, and that judgement is left
to the reader.

## 1. The four options

The reference mathlib definition is

```lean
class Algebra.IsQuadraticExtension (R S : Type*) [CommSemiring R] [StrongRankCondition R]
    [Semiring S] [Algebra R S] extends Module.Free R S where
  finrank_eq_two' : Module.finrank R S = 2
```

`IsQuadraticExtension` extends `Module.Free`, which carries a
`Basis`; the class is therefore **data-bearing**, not a `Prop`.

The four candidate designs for a project-level `QuadraticField K`
(with the canonical specialization `R = ℚ` written explicitly):

### Option A — `class extends`

```lean
class QuadraticField (K : Type*) [Field K] [Algebra ℚ K]
    extends Algebra.IsQuadraticExtension ℚ K

-- Optional, to lift existing instances:
instance [Algebra.IsQuadraticExtension ℚ K] : QuadraticField K := ⟨⟨⟩⟩
```

The class inherits the parent fields verbatim: a `Module.Free`
basis, the `finrank_eq_two'` proof, and the `[Field K] [Algebra ℚ K]`
parent instances. `QuadraticField` is itself a data class.

### Option B — `class : Prop` wrapper

```lean
class QuadraticField (K : Type*) [Field K] [Algebra ℚ K] : Prop where
  isQuadratic : Algebra.IsQuadraticExtension ℚ K

instance (K) [Field K] [Algebra ℚ K] [QuadraticField K] :
    Algebra.IsQuadraticExtension ℚ K :=
  QuadraticField.isQuadratic
```

`QuadraticField` is a `Prop`. The mathlib class is referenced by a
named field, not inherited. A **one-way** out-instance promotes
`[QuadraticField K]` to `[Algebra.IsQuadraticExtension ℚ K]`.

### Option C — `abbrev` rename

```lean
abbrev QuadraticField (K : Type*) [Field K] [Algebra ℚ K] :=
  Algebra.IsQuadraticExtension ℚ K
```

`QuadraticField K` is **definitionally equal** to
`Algebra.IsQuadraticExtension ℚ K`. No new class is introduced.

### Option D — direct use

No project-level name. Statements refer to
`[Algebra.IsQuadraticExtension ℚ K]` directly, exactly as
`Mathlib/FieldTheory/Galois/Basic.lean` and
`Mathlib/NumberTheory/NumberField/CMField.lean` do.

## 2. Property matrix

| Property | A. extends | B. Prop wrapper | C. abbrev | D. direct |
|---|---|---|---|---|
| Carries data | yes (basis + finrank proof) | no (data held by `isQuadratic` field) | yes (transparent) | yes |
| Is `Prop` | no | yes | no | n/a |
| Instance resolution cost | comparable; instance term carries the `Free` structure | comparable; thin `Prop`, marginally lighter | comparable (same term as parent) | comparable (same term as parent) |
| Basis realized at resolution? | no — only when projected (`h.basis`) | no | no | no |
| Basis available in proof | via `h.basis` (dot notation) | via `(h.isQuadratic).chooseBasis` or `letI` | transparent | via parent class instance |
| Extensibility | full: any new field, data or `Prop` | `Prop` fields free; data fields force a data class | none | requires a separate class |
| Mathlib idiom match | partial (subclassing pattern) | close analog of `NumberField` (with a twist, see §3.2) | none | exact |
| Reusable as a parent class | yes | yes (with `Prop` constraint) | no | no |
| Diamond risk | real (basis non-canonical) | low (`Prop` is a one-way bridge) | same as parent | same as parent |
| Mathlib precedent | none | none — project convention | none | yes (`CMField`, `Galois.Basic`) |
| Lines of boilerplate | 1–3 | 7 | 1 | 0 |

## 3. Detailed analysis

### 3.1 Option A — `class extends`

**Mathlib adaptation.** Subclassing is a standard mathlib pattern
(`Field`, `Ring`, etc.); the `extends` keyword is the natural way
to say "this class is a refinement of that one." A subclass
inherits all parent projections, so `[QuadraticField K]` is a
strictly stronger assumption than `[IsQuadraticExtension ℚ K]`.
That said, no class in mathlib actually subclasses
`IsQuadraticExtension` itself — the precedent is the `extends`
mechanism in general, not its use on this specific parent.

**Elegance.** Maximum expressiveness per character: every relevant
piece of structure is one dot away. Proofs can write
`h.finrank_eq_two'`, `h.basis`, `h.normal`, `h.isGalois` without
ceremony.

**Future extensibility.** The strongest of the four. One can add
data fields (a chosen primitive generator, a distinguished
involution, a fundamental discriminant) or `Prop` fields
(separability, characteristic) directly to the class. The class
grows in place; consumers see all structure as one assumption.

**Cost.** The parent is data, so the child is data. The
`Module.Free` basis is **non-canonical** (its construction goes
through `Classical.choice`), so two `QuadraticField K` instances
constructed by different routes may carry different bases and
will not be definitionally equal. For abstract field statements
this is rarely observable, but it forces any user who needs a
specific basis to either `change` it explicitly or work
proof-locally. The cost is structurally the same as in mathlib
itself; the wrapper does not improve on it.

### 3.2 Option B — `class : Prop` wrapper

**Mathlib adaptation.** This is the pattern of `NumberField` in
mathlib (`Mathlib/NumberTheory/NumberField/Basic.lean:42`):

```lean
class NumberField (K : Type*) [Field K] : Prop where
  [to_charZero : CharZero K]
  [to_finiteDimensional : FiniteDimensional ℚ K]
```

`NumberField` does not extend `CharZero` or `FiniteDimensional`;
it carries them as named fields, because the natural reading of
"`K` is a number field" is a `Prop`, not a data record. A
`QuadraticField` wrapper follows the same shape, and pegs the new
class to the closest mathlib precedent for "K is a field with
extra property."

**A twist worth noting.** The analogy is close but not exact in
two respects. First, `NumberField` takes only `[Field K]`; it does
*not* take `[Algebra ℚ K]` as a parameter (the `ℚ`-algebra
structure comes from `CharZero K`). The `QuadraticField` sketch in
§1 carries `[Algebra ℚ K]` explicitly. Second, `NumberField`'s
fields are **instance-implicit** binders (`[to_charZero : …]`),
so they are re-exposed as instances automatically and `NumberField`
needs no hand-written out-instance. The Option B sketch uses an
*explicit* field (`isQuadratic : …`) plus a manually written
out-instance. An "instance-implicit field" variant of B would track
`NumberField` more faithfully and drop the explicit out-instance.

**Elegance.** `QuadraticField K` reads as a fact about `K` —
"K is a quadratic field" — rather than as a record of
data. Proofs in the abstract layer never need to mention a basis
or a chosen generator; those appear only when a specific lemma
asks for them, by `letI := h.isQuadratic` (or automatically, via
the out-instance).

**Future extensibility.** New `Prop` fields can be added freely.
New data fields can be added, but they convert the class from
`Prop` to data — a one-time cost. The bridge to mathlib is
**one-way** (`QuadraticField K → IsQuadraticExtension ℚ K`),
which deliberately cuts the `Algebra ℚ` diamond in the same
way that `IsQuadraticExtension`-based number-field instances do
in mathlib.

**Cost.** Slightly more boilerplate than A. One out-instance to
keep the mathlib API reachable (avoidable with the
instance-implicit-field variant). Indirect field access
(`h.isQuadratic.finrank_eq_two'`), partially compensated for by
Lean 4's coercion and instance search.

### 3.3 Option C — `abbrev` rename

**Mathlib adaptation.** None. Mathlib has no analogous
abbreviation for `IsQuadraticExtension`.

**Elegance.** Minimal, but deceptive: `abbrev` defines a name,
not a class. `[QuadraticField K]` in a signature works as a
typeclass parameter only because it unfolds to a real class;
the `abbrev` itself is not a class. Any later move to add a field
requires replacing the `abbrev` with a real class, breaking every
signature that referenced the old name.

**Future extensibility.** None. The moment the project needs to
add a primitive element witness, a `Conj` instance, or a
fundamental discriminant, the `abbrev` must be deleted and
replaced. There is no upgrade path.

**Cost.** Slightly cheaper than A in lines, but the upgrade cost
is real. `Conj` (or any later class that wants
`[QuadraticField K]` as a parent) cannot be written at all,
because there is no class to extend.

### 3.4 Option D — direct use

**Mathlib adaptation.** Exact. `CMField.lean:73` writes
`[is_quadratic : IsQuadraticExtension (maximalRealSubfield K) K]`;
`Galois/Basic.lean:678` writes
`variable ... [IsQuadraticExtension F K]`. No project-level
indirection; every proof reads as a mathlib proof.

**Elegance.** Zero abstraction. The only price is verbosity:
`[Algebra.IsQuadraticExtension ℚ K]` instead of `[QuadraticField K]`.

**Future extensibility.** New structure must live in a separate
class on top of the mathlib class. `QuadraticField` cannot be
the name of a *concept*; it can only be a phrase. If the project
later decides that "quadratic field" should package a primitive
generator, a `Conj`, or a fundamental discriminant, it has to
introduce one or more sibling classes — and the project layer
becomes a federation of small classes, not a single named
abstraction.

**Cost.** Loss of project-level terminology. Documentation that
says "let `K` be a quadratic field" is forced to mean
"`Algebra.IsQuadraticExtension ℚ K`" with no project name. The
project's own models (`Qsqrtd d`, and any future concrete
realization) must be linked to the mathlib class directly.

## 4. Cross-criterion summary

| Criterion | A. extends | B. Prop wrapper | C. abbrev | D. direct |
|---|---|---|---|---|
| Mathlib adaptation | partial | close to `NumberField` | misaligned | exact |
| Elegance (right math object) | overshoots (data) | right level (fact) | undercuts (rename) | right (no wrapper) |
| Future extensibility | strongest | strong (Prop fields) | none | requires sibling classes |
| Resolution cost | comparable | comparable (marginally lighter) | comparable | comparable |
| Diamond control | needs care | one-way bridge handles it | inherits parent | inherits parent |

## 5. Per-dimension scores

Scores are on a **1–5 scale** (5 = best on that axis). They are
per-axis assessments only; this document deliberately provides
**no aggregate and no recommendation**. Weight the axes according
to the project's priorities and total them yourself.

### 5.1 Score table

| Dimension | A. extends | B. Prop wrapper | C. abbrev | D. direct |
|---|:---:|:---:|:---:|:---:|
| Mathlib adaptation | 3 | 4 | 1 | 5 |
| Elegance (right math object) | 3 | 5 | 2 | 4 |
| Future extensibility | 5 | 4 | 1 | 2 |
| Resolution / inference cost | 4 | 5 | 4 | 4 |
| Diamond control | 2 | 5 | 3 | 3 |
| Boilerplate cost (5 = least) | 4 | 3 | 5 | 5 |

### 5.2 Score justifications

**Mathlib adaptation.** A (3): `extends` is idiomatic, but nothing
in mathlib subclasses `IsQuadraticExtension`. B (4): mirrors the
`NumberField` `Prop` pattern, docked one point for the
explicit-field / `[Algebra ℚ K]`-parameter twist (§3.2). C (1): no
mathlib analog. D (5): literally what `CMField` and `Galois.Basic`
do.

**Elegance.** A (3): expresses a *data record* where the intended
object is a *fact*. B (5): reads as "K is a quadratic field," the
right mathematical level. C (2): a rename that pretends to be a
class. D (4): no wrapper at all — correct, but verbose.

**Future extensibility.** A (5): any field, data or `Prop`, added
in place. B (4): `Prop` fields free; the first data field forces a
class migration. C (1): no upgrade path. D (2): every extension is
a new sibling class.

**Resolution / inference cost.** No option realizes a basis at
instance-resolution time, so the axis barely separates them. B (5):
a thin `Prop` is the cheapest to unify. A/C/D (4): the instance
term carries the `Free` structure but it is not forced.

**Diamond control.** A (2): the non-canonical basis is a real
diamond hazard when an instance is built by two routes. B (5): the
one-way `Prop` bridge cuts the `Algebra ℚ` diamond cleanly. C/D
(3): inherit whatever the mathlib parent does, with no project-level
control either way.

**Boilerplate cost** (5 = least code). D (5): zero lines. C (5):
one line. A (4): 1–3 lines. B (3): ~7 lines (one out-instance, one
named field, the class).

### 5.3 How to read the scores

- A project that is fundamentally a **computational** layer — where
  most abstract statements manipulate a specific basis, generator,
  or involution — should weight *extensibility* and *direct data
  access* heavily, which favors A.
- A project that is fundamentally an **abstract** layer — stating
  and proving theorems about "an arbitrary quadratic field" without
  committing to choices — should weight *elegance* and *diamond
  control* heavily, which favors B.
- A project that is a **thin glue layer** over mathlib, not owning
  its own terminology, should weight *mathlib adaptation* and
  *boilerplate* heavily, which favors D.
- C scores low on every axis except boilerplate and has no upgrade
  path; it is included for completeness.

The trade-off between owning project-level terminology (A/B/C give
you the name `QuadraticField`; D does not) and staying maximally
faithful to mathlib (D) is the single largest swing factor, and it
is a project-policy decision rather than a technical one.

## 6. Upgrade paths (extensibility detail)

How each option absorbs new structure — e.g. a primitive generator
that should be available without re-proving its existence.

**From A.** Add the field directly to the class (data or `Prop`).
No migration; every consumer sees it immediately.

**From B.** Three escalating moves, in increasing order of cost:

1. Add a `Prop`-valued *existence* field, keeping the class a
   `Prop`:

   ```lean
   hasPrimitive : ∃ β b c, β * β = algebraMap ℚ K b * β - algebraMap ℚ K c ∧
     IntermediateField.adjoin ℚ {β} = ⊤
   ```

   Extensibility is preserved; downstream proofs use
   `obtain ⟨β, b, c, h⟩ := h.hasPrimitive`.

2. If a **chosen** primitive generator is required (e.g. to define
   a section of a functor to `QuadraticFieldCat`), introduce a
   separate `structure` that bundles the field with the witness:

   ```lean
   structure QuadraticFieldWithGenerator (K : Type*) [Field K] [Algebra ℚ K] where
     quad : QuadraticField K
     β    : K
     b c  : ℚ
     spec : β * β = algebraMap ℚ K b * β - algebraMap ℚ K c ∧
            IntermediateField.adjoin ℚ {β} = ⊤
   ```

   A structure, not a class; it appears only where a chosen
   generator is genuinely needed, and the class is untouched.

3. If the full data-bearing class is eventually required, introduce
   a *new* class (`QuadraticFieldData`) and migrate data-bearing
   uses to it, linked to the `Prop` class by a one-directional
   instance.

**From C.** No upgrade path: the `abbrev` must be deleted and
replaced by a real class, and every signature using the name
rewritten.

**From D.** Each new piece of structure is a new sibling class on
top of `IsQuadraticExtension`; the project layer becomes a
federation of small classes.

## 7. References

- `Mathlib/LinearAlgebra/Dimension/StrongRankCondition.lean:679` —
  definition of `Algebra.IsQuadraticExtension`, its
  `extends Module.Free`, and the `finrank_eq_two'` projection
  (verified: line 679).
- `Mathlib/FieldTheory/Galois/Basic.lean:678` — uses
  `[IsQuadraticExtension F K]` directly to derive Galois
  properties (verified).
- `Mathlib/FieldTheory/Normal/Basic.lean:291` —
  `IsQuadraticExtension.normal`, illustrating how out-instances are
  layered on top (verified).
- `Mathlib/NumberTheory/NumberField/CMField.lean:73` — uses
  `IsQuadraticExtension` as a named structure field
  (`is_quadratic`) (verified).
- `Mathlib/NumberTheory/NumberField/Basic.lean:42` —
  `class NumberField`: the `Prop` pattern with two
  instance-implicit fields that the design of Option B mirrors
  (verified — note the fields are instance-implicit, see §3.2).
