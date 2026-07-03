# Ray Class Group Prototype Archive

This note preserves a local prototype for a future ray class group API. It is
not part of the active genus-theory rebuild.

The archived patch is:

```text
docs/design/ray-classgroup-prototype.patch
```

The prototype split the future mathlib-facing API as:

- `QNFMathlib/NumberTheory/NumberField/RayClassGroup/Modulus.lean`
- `QNFMathlib/NumberTheory/NumberField/RayClassGroup/Basic.lean`
- `QNFMathlib/NumberTheory/NumberField/RayClassGroup/Narrow.lean`
- `QNFMathlib/NumberTheory/NumberField/RayClassGroup/ClassGroup.lean`

The main design point was to avoid defining a general ray class group as a
quotient of all fractional ideals. Instead, the quotient should have numerator
`I_K^m`, the group of fractional ideals coprime to the finite part of the
modulus.

The prototype used:

```lean
structure NumberField.RayModulus (K : Type*) [Field K] [NumberField K] where
  finitePart : Ideal (𝓞 K)
  finitePart_ne_bot : finitePart ≠ ⊥
  infinitePart : Set {w : NumberField.InfinitePlace K // w.IsReal}
```

For the narrow class group, the intended specialization is:

```lean
finitePart := ⊤
infinitePart := Set.univ
```

To restore the prototype on a clean branch:

```bash
git apply docs/design/ray-classgroup-prototype.patch
lake build QNFMathlib.NumberTheory.NumberField.RayClassGroup.Modulus \
  QNFMathlib.NumberTheory.NumberField.RayClassGroup.Basic \
  QNFMathlib.NumberTheory.NumberField.RayClassGroup.Narrow \
  QNFMathlib.NumberTheory.NumberField.RayClassGroup.ClassGroup \
  QNFMathlib
```
