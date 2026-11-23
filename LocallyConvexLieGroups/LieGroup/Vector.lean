/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.LieAlgebra.Basic

/-!
# Vector groups

Each locally convex space `E` is an abelian Lie group with respect to addition
([GN26, Example 5.1.2]); its Lie algebra is `E` with the zero bracket ([GN26, Example 5.1.9(a)]).
Since `MBLieGroup` is stated for multiplicative groups, the vector group is `Multiplicative E`,
with the single global chart `Multiplicative.toAdd`.

## Main results

* `VectorGroup.instMBLieGroup`: **`(E, +)` is a Lie group** ([GN26, Example 5.1.2]).
* `VectorGroup.lie_eq_zero`: its Lie algebra is abelian ([GN26, Example 5.1.9(a)]).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups

universe u

namespace VectorGroup

variable (E : Type u) [TopologicalSpace E]

/-- `Multiplicative.toAdd` as a homeomorphism. -/
def homeomorph : Multiplicative E ≃ₜ E where
  toFun := Multiplicative.toAdd
  invFun := Multiplicative.ofAdd
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_toAdd
  continuous_invFun := continuous_ofAdd

/-- The global chart of the vector group. -/
def chart : OpenPartialHomeomorph (Multiplicative E) E := (homeomorph E).toOpenPartialHomeomorph

theorem chart_source : (chart E).source = univ := rfl

instance : ChartedSpace E (Multiplicative E) := (chart E).singletonChartedSpace (chart_source E)

theorem chartAt_eq (x : Multiplicative E) : chartAt E x = chart E := rfl

variable [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E]

instance : HasGroupoid (Multiplicative E) (mbGroupoid E) :=
  (chart E).singleton_hasGroupoid (chart_source E) _

/-- **Vector groups are Lie groups** ([GN26, Example 5.1.2]): in the global chart, the
multiplication is the addition of `E` and the inversion is the negation, both continuous linear. -/
instance instMBLieGroup : MBLieGroup E (Multiplicative E) where
  smoothMBM_mul k := by
    refine ⟨continuous_mul.continuousOn, fun x _ ↦ ?_⟩
    refine ContDiffMBOn.congr_of_isOpen
      (isOpen_chartDomain isOpen_univ continuous_mul.continuousOn _ _) (fun _ _ ↦ rfl)
      (((ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E).contDiffMBOn k
        univ).mono (subset_univ _))
  smoothMBM_inv k := by
    refine ⟨continuous_inv.continuousOn, fun x _ ↦ ?_⟩
    refine ContDiffMBOn.congr_of_isOpen
      (isOpen_chartDomain isOpen_univ continuous_inv.continuousOn _ _) (fun _ _ ↦ rfl)
      ((-ContinuousLinearMap.id ℝ E).contDiffMBOn k univ |>.mono (subset_univ _))

/-- **The Lie algebra of a vector group is abelian** ([GN26, Example 5.1.9(a)]). -/
theorem lie_eq_zero (x y : MBLieGroup.LieAlg E (Multiplicative E)) : ⁅x, y⁆ = 0 :=
  MBLieGroup.LieAlg.lie_eq_zero_of_comm (fun a b ↦ mul_comm a b) x y

end VectorGroup

end LocallyConvex.LieGroups
