/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Regular.Interval
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The primitive of curves in a normed space

`J η(t) = ∫₀ᵗ η̃` on `C([0, 1], E)`, a continuous linear operator of norm `≤ 1`, used to write
evolution equations in integral form.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function
open scoped Topology unitInterval

noncomputable section

namespace LocallyConvex.LieGroups

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The primitive -/

omit [NormedSpace ℝ E] in
theorem norm_extendCurve_le (η : C(I, E)) (s : ℝ) : ‖MBLieGroup.extendCurve η s‖ ≤ ‖η‖ :=
  η.norm_coe_le_norm _

/-- `J η(t) = ∫₀ᵗ η̃`. -/
def primitive (η : C(I, E)) : C(I, E) :=
  ⟨fun t ↦ ∫ s in (0 : ℝ)..t, MBLieGroup.extendCurve η s,
    (intervalIntegral.continuous_primitive (fun _ _ ↦
      (MBLieGroup.continuous_extendCurve η).intervalIntegrable _ _) 0).comp
      continuous_subtype_val⟩

theorem primitive_apply (η : C(I, E)) (t : I) :
    primitive η t = ∫ s in (0 : ℝ)..t, MBLieGroup.extendCurve η s := rfl

/-- **The primitive** `J`, a continuous linear operator of norm `≤ 1`. -/
def primitiveCLM : C(I, E) →L[ℝ] C(I, E) :=
  LinearMap.mkContinuous
    { toFun := primitive
      map_add' := fun η ζ ↦ by
        ext t
        simp only [primitive_apply, ContinuousMap.add_apply]
        exact intervalIntegral.integral_add
          ((MBLieGroup.continuous_extendCurve η).intervalIntegrable _ _)
          ((MBLieGroup.continuous_extendCurve ζ).intervalIntegrable _ _)
      map_smul' := fun c η ↦ by
        ext t
        simp only [primitive_apply, ContinuousMap.smul_apply, RingHom.id_apply]
        exact intervalIntegral.integral_smul c _ } 1 fun η ↦ by
    rw [one_mul]
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun t ↦ ?_
    change ‖∫ s in (0 : ℝ)..t, MBLieGroup.extendCurve η s‖ ≤ ‖η‖
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := t) (fun s _ ↦ norm_extendCurve_le η s)
    have ht : |(t : ℝ) - 0| ≤ 1 := by
      rw [sub_zero, abs_of_nonneg t.2.1]; exact t.2.2
    calc _ ≤ ‖η‖ * |(t : ℝ) - 0| := h
      _ ≤ ‖η‖ * 1 := mul_le_mul_of_nonneg_left ht (norm_nonneg _)
      _ = ‖η‖ := mul_one _

theorem primitiveCLM_apply (η : C(I, E)) (t : I) :
    primitiveCLM η t = ∫ s in (0 : ℝ)..t, MBLieGroup.extendCurve η s := rfl

theorem norm_primitiveCLM_apply_le (η : C(I, E)) : ‖primitiveCLM η‖ ≤ ‖η‖ := by
  refine (primitiveCLM.le_opNorm η).trans ?_
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

end LocallyConvex.LieGroups
