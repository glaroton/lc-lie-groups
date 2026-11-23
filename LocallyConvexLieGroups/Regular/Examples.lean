/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Regular.Ck
public import LocallyConvexLieGroups.Regular.Banach
public import LocallyConvexLieGroups.Regular.Units
public import LocallyConvexLieGroups.CircleCover.Regular

/-!
# Examples of regular Lie groups

`C⁰`-regularity implies `C^k`-regularity for all `k` and regularity in the sense of Milnor
([GN26, Remark 6.1.2(c)]), so the `C⁰`-regular examples are regular: vector groups of sequentially
complete spaces ([GN26, Proposition 6.1.3]), Banach–Lie groups ([GN26, Theorem 6.3.4]), unit
groups of Banach algebras, and the universal cover of `Diff⁺(S¹)`.

## Main results

* `VectorGroup.isRegular`, `MBLieGroup.isRegular_of_completeSpace`, `UnitGroup.isRegular`,
  `CircleCover.isRegular`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open LocallyConvex.Analysis LocallyConvex.Manifolds

namespace LocallyConvex.LieGroups

universe u

/-- **`(E, +)` is regular** for `E` sequentially complete. -/
theorem VectorGroup.isRegular {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    [SeqComplete E] : MBLieGroup.IsRegular E (Multiplicative E) :=
  VectorGroup.isC0Regular.isRegular

/-- **Banach–Lie groups are regular** ([GN26, Theorem 6.3.4]). -/
theorem MBLieGroup.isRegular_of_completeSpace {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {G : Type*} [Group G] [TopologicalSpace G]
    [ChartedSpace E G] [MBLieGroup E G] : MBLieGroup.IsRegular E G :=
  MBLieGroup.isC0Regular_of_completeSpace.isRegular

/-- **Unit groups of real Banach algebras are regular.** -/
theorem UnitGroup.isRegular {A : Type u} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    [NormOneClass A] : MBLieGroup.IsRegular A (UnitGroup A) :=
  UnitGroup.isC0Regular.isRegular

/-- **The universal cover of `Diff⁺(S¹)` is regular.** -/
theorem CircleCover.isRegular : MBLieGroup.IsRegular CInfPer CircleCover.CoverGroup :=
  CircleCover.isC0Regular.isRegular

end LocallyConvex.LieGroups
