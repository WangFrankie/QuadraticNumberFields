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

This document **does not pick a winner**. Sections 1–4 establish the
facts and lay out the options; section 5 scores each option on each
axis on a 1–5 scale so the reader can apply their own weighting.

## 0. The governing fact (verified)

Everything below turns on the nature of the parent class, so it is
stated first and was checked directly against the mathlib in this
project (`.lake/packages/mathlib`):

```lean
-- Mathlib/LinearAlgebra/FreeModule/Basic.lean:43
class Module.Free (R M) [Semiring R] [AddCommMonoid M] [Module R M] : Prop where
  exists_basis : Nonempty <| (I : Type v) × Basis I R M

-- Mathlib/LinearAlgebra/Dimension/StrongRankCondition.lean:679
class Algebra.IsQuadraticExtension (R S) [CommSemiring R] [StrongRankCondition R]
    [Semiring S] [Algebra R S] extends Module.Free R S where
  finrank_eq_two' : Module.finrank R S = 2
```

Consequences, each confirmed by elaboration (`example : Prop := …`
and `cases h1; cases h2; rfl`):

- **`Module.Free` is a `Prop`.** It asserts the *existence* of a
  basis (`Nonempty`), not a chosen basis. There is **no basis datum**
  to project.
- **`IsQuadraticExtension` is a `Prop`** (Lean infers `Prop` because
  every field is a proposition) and a **subsingleton**: any two
  instances are definitionally equal.
- A basis, when needed, is produced by `Module.Free.chooseBasis`
  (a `noncomputable def` through `Classical.choice`). This is
  available identically under every option below; **no option puts a
  basis "one dot away" as a field.**

This invalidates the common intuition that `IsQuadraticExtension`
"carries a non-canonical basis as data." It does not. The
practical fallout: the data-vs-`Prop` distinction between the
options **collapses** — all four operate at the level of a `Prop`
subsingleton — and the supposed "basis diamond" risk that would
separate the options **does not exist** until and unless someone
deliberately adds a *data* field (see §6).

(The separate `Algebra ℚ` diamond between `DivisionRing.toRatAlgebra`
and a model's own algebra instance is real, but it lives in the
concrete model `Qsqrtd d`, not in the `QuadraticField` wrapper, and
is present identically under all four options. It is out of scope
here.)

## 1. The four options

The canonical specialization is `R = ℚ`, written explicitly.

### Option A — `class extends`

```lean
class QuadraticField (K : Type*) [Field K] [Algebra ℚ K]
    extends Algebra.IsQuadraticExtension ℚ K

-- Optional reverse lift, to reuse existing mathlib instances:
instance [Algebra.IsQuadraticExtension ℚ K] : QuadraticField K := ⟨‹_›⟩
```

Because the parent is a `Prop` and no field is added, **`QuadraticField`
is itself a `Prop` subsingleton** (verified). `extends` gives the
forward projection `QuadraticField K → IsQuadraticExtension ℚ K`
for free.

### Option B — `class : Prop` wrapper

```lean
class QuadraticField (K : Type*) [Field K] [Algebra ℚ K] : Prop where
  isQuadratic : Algebra.IsQuadraticExtension ℚ K

instance (K) [Field K] [Algebra ℚ K] [QuadraticField K] :
    Algebra.IsQuadraticExtension ℚ K :=
  QuadraticField.isQuadratic
```

`QuadraticField` is a `Prop` subsingleton. The mathlib class is held
by a named field; a **one-way** out-instance (one line) provides the
forward bridge that A gets automatically.

### Option C — `abbrev` rename

```lean
abbrev QuadraticField (K : Type*) [Field K] [Algebra ℚ K] :=
  Algebra.IsQuadraticExtension ℚ K
```

`QuadraticField K` is **definitionally** the parent `Prop`. No new
class is introduced; it is an alias, not a class.

### Option D — direct use

No project-level name. Statements refer to
`[Algebra.IsQuadraticExtension ℚ K]` directly, exactly as
`Mathlib/FieldTheory/Galois/Basic.lean:678` and
`Mathlib/NumberTheory/NumberField/CMField.lean:73` do.

## 2. Property matrix

| Property | A. extends | B. Prop wrapper | C. abbrev | D. direct |
|---|---|---|---|---|
| Sort | `Prop` (subsingleton) | `Prop` (subsingleton) | `Prop` (= parent) | `Prop` (parent) |
| Carries real data | no | no | no | no |
| Basis access | `chooseBasis` (choice) | `chooseBasis` (choice) | `chooseBasis` (choice) | `chooseBasis` (choice) |
| Is a real class | yes | yes | no (alias) | no name |
| Forward → `IsQuadraticExtension` | free (projection) | 1-line out-instance | defeq (free) | identity |
| Reverse lift available | yes (creates two-way graph) | yes (kept separate) | defeq | n/a |
| Can be a parent / `extends`-ed later | yes | yes | no | no |
| Add `Prop` field later | in place | in place | no (replace) | sibling class |
| Add **data** field later | in place → becomes `Type`, real diamond | in place → same; or isolate in a `structure` | no (replace) | sibling structure |
| Instance-resolution cost | trivial (`Prop`) | trivial (`Prop`) | trivial | trivial |
| Mathlib precedent | `extends` on `Prop` classes | `NumberField` named-field `Prop` | none | `CMField`, `Galois.Basic` |
| Lines of boilerplate | 1 (+1 for reverse) | 3–7 | 1 | 0 |

## 3. Detailed analysis

### 3.1 Option A — `class extends`

**Mathlib adaptation.** `extends` is the standard way to say "this
class refines that one," and refining a `Prop` class with `extends`
is well-formed and used in mathlib. The forward projection
`QuadraticField K → IsQuadraticExtension ℚ K` comes for free, so
every mathlib lemma keyed on `IsQuadraticExtension` (`normal`,
`isGalois`, `finrank_eq_two`) is reachable with no extra wiring. The
one caveat: the *closest* precedent for "K is a field with an extra
property" — `NumberField` — uses named instance-implicit fields
rather than `extends`, so A matches the general `extends` idiom but
not that specific precedent.

**Elegance.** `QuadraticField K` is a `Prop` (verified), so it reads
as the fact "K is a quadratic field," not as a data record. The
earlier worry that A "overshoots by carrying data" is unfounded:
there is no data. Proofs reach the underlying predicate by the
automatic coercion/projection.

**Future extensibility.** Strong. New `Prop` fields can be added in
place. New **data** fields can also be added in place, but doing so
turns the class from `Prop` into `Type` and introduces a genuine,
non-defeq diamond (two instances with different chosen data are no
longer equal). That cost is intrinsic to wanting chosen data in the
core class and is **not** specific to A — B incurs exactly the same
cost if data is added the same way (see §6).

**Cost.** Almost none in the property-only regime. If a reverse lift
`IsQuadraticExtension → QuadraticField` is also declared, A and the
parent become inter-derivable (a two-way instance relationship);
because both are `Prop` subsingletons this is harmless for defeq, but
it is mild redundancy in the instance graph.

### 3.2 Option B — `class : Prop` wrapper

**Mathlib adaptation.** This mirrors the *shape* of `NumberField`
(`Mathlib/NumberTheory/NumberField/Basic.lean:42`):

```lean
class NumberField (K : Type*) [Field K] : Prop where
  [to_charZero : CharZero K]
  [to_finiteDimensional : FiniteDimensional ℚ K]
```

Two differences are worth noting. `NumberField` takes only
`[Field K]` (no `[Algebra ℚ K]` parameter — the algebra comes from
`CharZero`), and its fields are **instance-implicit** binders
(`[to_charZero : …]`), so they are re-exposed as instances
automatically and it needs **no** hand-written out-instance. The
Option B sketch uses an *explicit* field plus a manual out-instance.
A closer port of the `NumberField` pattern would make `isQuadratic`
an instance-implicit field and drop the explicit bridge:

```lean
class QuadraticField (K : Type*) [Field K] [Algebra ℚ K] : Prop where
  [isQuadratic : Algebra.IsQuadraticExtension ℚ K]
```

**Elegance.** Reads as a fact about `K`. Identical mathematical
content to A; the difference from A is purely how the underlying
predicate is exposed (named field + explicit bridge vs. inherited
projection).

**Future extensibility.** Same as A for `Prop` fields. For chosen
**data**, B has a documented discipline: rather than mutate the class
to `Type`, isolate the datum in a separate `structure` (§6), keeping
the class a clean `Prop`. This is a *convention* advantage, not a
structural capability A lacks — A could follow the same discipline.

**Cost.** More boilerplate than A (the explicit field and the
one-way out-instance), unless the instance-implicit-field variant is
used. The forward bridge that A gets for free is one explicit line
here — but that explicitness is also the point: the bridge direction
is visible and deliberately one-way.

### 3.3 Option C — `abbrev` rename

**Mathlib adaptation.** None. Mathlib has no analogous abbreviation
for `IsQuadraticExtension`.

**Elegance.** Minimal, but an `abbrev` is a name, not a class.
`[QuadraticField K]` works as a parameter only because it unfolds to
the real parent class; the alias itself cannot be extended or used
as a parent.

**Future extensibility.** None. The moment the project wants to add a
field (even a `Prop` one), or to make `QuadraticField` the parent of
another class, the `abbrev` must be deleted and replaced by a real
class, rewriting every signature that used the name. There is no
incremental upgrade path.

**Cost.** One line now; a disruptive rename later.

### 3.4 Option D — direct use

**Mathlib adaptation.** Exact. `CMField.lean:73` writes
`[is_quadratic : IsQuadraticExtension (maximalRealSubfield K) K]`;
`Galois/Basic.lean:678` writes `variable … [IsQuadraticExtension F K]`.
Every proof reads as a mathlib proof.

**Elegance.** Zero abstraction. The only price is verbosity:
`[Algebra.IsQuadraticExtension ℚ K]` instead of `[QuadraticField K]`.

**Future extensibility.** New structure must live in a separate class
on top of the mathlib class. `QuadraticField` cannot be the name of a
*concept*, only a phrase; packaging a generator, a `Conj`, or a
discriminant means introducing sibling classes, and the project layer
becomes a federation of small classes rather than one named
abstraction.

**Cost.** No project-level terminology. Documentation saying "let `K`
be a quadratic field" must mean `Algebra.IsQuadraticExtension ℚ K`
with no project name, and the project's own models must link to the
mathlib class directly.

## 4. Cross-criterion summary

With the governing fact in §0, the four options stop differing on
*sort* (all `Prop`) or *data/diamond* (none until data is added).
What remains:

| Criterion | A. extends | B. Prop wrapper | C. abbrev | D. direct |
|---|---|---|---|---|
| Mathlib adaptation | idiomatic `extends` | matches `NumberField` shape | misaligned | exact |
| Elegance | `Prop` fact, free projection | `Prop` fact, named field | alias, not a class | no wrapper, verbose |
| Extensibility | real class, in place | real class, in place | none | sibling classes |
| Bridge to mathlib | automatic (two-way if lifted) | explicit, one-way | defeq | identity |
| Boilerplate | least (1) | most (3–7) | least (1) | none (0) |
| Owns the name `QuadraticField` | yes | yes | yes | no |

A and B are now **near-equivalent**; the residual difference is one
of convention (inherited projection vs. named field + explicit
one-way bridge) and boilerplate.

## 5. Per-dimension scores

Scores are on a **1–5 scale** (5 = best on that axis). They are
per-axis assessments only; this document deliberately provides
**no aggregate and no recommendation**. Weight the axes according to
the project's priorities and total them yourself.

### 5.1 Score table

| Dimension | A. extends | B. Prop wrapper | C. abbrev | D. direct |
|---|:---:|:---:|:---:|:---:|
| Mathlib adaptation | 4 | 4 | 1 | 5 |
| Elegance (right math object) | 4 | 4 | 2 | 4 |
| Future extensibility | 4 | 4 | 1 | 2 |
| Bridge / instance-graph control | 4 | 5 | 4 | 5 |
| Boilerplate (5 = least) | 5 | 3 | 5 | 5 |

### 5.2 Score justifications

**Mathlib adaptation.** A (4): idiomatic `extends`, but not the exact
shape of the nearest precedent `NumberField`. B (4): matches the
`NumberField` named-field `Prop` shape, docked for the
explicit-field / `[Algebra ℚ K]`-parameter twist (§3.2). C (1): no
analog. D (5): literally `CMField` / `Galois.Basic`.

**Elegance.** A, B (4 each): both are `Prop` facts with identical
mathematical content; they tie. C (2): a rename masquerading as a
class. D (4): no wrapper — correct but verbose.

**Future extensibility.** A, B (4 each): both real classes; both add
`Prop` fields in place and can be parents; both face the same
`Type`-migration cost for chosen data. C (1): no upgrade path. D (2):
every extension is a new sibling class.

**Bridge / instance-graph control.** A (4): forward projection is
automatic; a reverse lift makes the relationship two-way (harmless
for `Prop` subsingletons, but redundant). B (5): one explicit,
deliberately one-way bridge. C (4): defeq to the parent, nothing to
manage. D (5): no project-level instance graph to manage.

**Boilerplate** (5 = least). A (5): one line. C (5): one line. D (5):
zero. B (3): class + field + out-instance (less with the
instance-implicit variant).

### 5.3 How to read the scores

- The data/`Prop` and diamond axes that dominated earlier framings
  are **gone** (§0): all options are `Prop` subsingletons. The live
  trade-offs are convention, boilerplate, naming, and extensibility.
- A and B score nearly identically. Prefer **A** for the least
  boilerplate and a free forward projection ("`QuadraticField` *is a*
  refined `IsQuadraticExtension`"); prefer **B** for a literal
  parallel to `NumberField` and an explicit one-way bridge direction.
- **C** scores low everywhere except boilerplate and has no upgrade
  path; it is included for completeness.
- **D** is strongest on mathlib fidelity and lightest of all, at the
  cost of the project owning the name `QuadraticField`. The choice
  between owning project terminology (A/B/C) and maximal mathlib
  fidelity (D) is a project-policy decision, not a technical one.

## 6. Upgrade paths (extensibility detail)

How each option absorbs new structure — e.g. a chosen primitive
generator. Note that adding *chosen data* to a `Prop` class turns it
into a `Type` and creates a real (non-defeq) diamond; this is true
for A and B alike, which is why isolating data in a separate
`structure` is the recommended discipline regardless of A vs. B.

**From A or B (identical options).**

1. Add a `Prop`-valued *existence* field, keeping the class a `Prop`
   subsingleton:

   ```lean
   hasPrimitive : ∃ β b c, β * β = algebraMap ℚ K b * β - algebraMap ℚ K c ∧
     IntermediateField.adjoin ℚ {β} = ⊤
   ```

   Downstream proofs use `obtain ⟨β, b, c, h⟩ := h.hasPrimitive`.

2. If a **chosen** generator is required (e.g. to define a section of
   a functor to `QuadraticFieldCat`), bundle it in a separate
   `structure` rather than mutating the class:

   ```lean
   structure QuadraticFieldWithGenerator (K : Type*) [Field K] [Algebra ℚ K] where
     quad : QuadraticField K
     β    : K
     b c  : ℚ
     spec : β * β = algebraMap ℚ K b * β - algebraMap ℚ K c ∧
            IntermediateField.adjoin ℚ {β} = ⊤
   ```

   This keeps the class a clean `Prop` and confines the chosen data
   (and its diamond) to where it is genuinely needed.

3. Only if a data-bearing *class* is unavoidable, introduce a new
   class (`QuadraticFieldData`) linked to the `Prop` class by a
   one-directional instance.

**From C.** No upgrade path: the `abbrev` must be deleted and
replaced by a real class, rewriting every signature using the name.

**From D.** Each new piece of structure is a new sibling class on top
of `IsQuadraticExtension`; the project layer becomes a federation of
small classes.

## 7. References

All file/line citations verified against `.lake/packages/mathlib`.

- `Mathlib/LinearAlgebra/FreeModule/Basic.lean:43` — `Module.Free`
  is a **`Prop`** (`exists_basis : Nonempty (Σ I, Basis I R M)`).
- `Mathlib/LinearAlgebra/Dimension/StrongRankCondition.lean:679` —
  definition of `Algebra.IsQuadraticExtension`, its
  `extends Module.Free`, and `finrank_eq_two'`. Confirmed to be a
  `Prop` subsingleton.
- `Mathlib/FieldTheory/Galois/Basic.lean:678` — uses
  `[IsQuadraticExtension F K]` directly to derive Galois properties.
- `Mathlib/FieldTheory/Normal/Basic.lean:291` —
  `IsQuadraticExtension.normal`, an out-instance layered on top.
- `Mathlib/NumberTheory/NumberField/CMField.lean:73` — uses
  `IsQuadraticExtension` as a named structure field (`is_quadratic`).
- `Mathlib/NumberTheory/NumberField/Basic.lean:42` —
  `class NumberField`, a `Prop` with two **instance-implicit** fields
  (the shape Option B mirrors; see §3.2).
