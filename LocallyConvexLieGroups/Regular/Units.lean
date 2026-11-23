/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Regular.Interval
public import LocallyConvexLieGroups.Exponential.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Unit groups of Banach algebras are `C⁰`-regular

Let `A` be a real Banach algebra. For `ξ ∈ C([0, 1], A)` the evolution equation `γ' = γ ξ`,
`γ(0) = 1` is linear: `γ = 1 + c` with `c = J((1 + c) ξ)`, where `J η(t) = ∫₀ᵗ η`. In the Banach
space `X = C([0, 1], A)`, this reads `(1 − T_ξ) c = J ξ` with `T_ξ c = J(c ξ)` and
`‖T_ξ‖ ≤ ‖ξ‖`. For `‖ξ‖ < 1`, `c = (1 − T_ξ)⁻¹ J ξ`, which is smooth in `ξ` since the inversion
of the Banach algebra `L(X)` is smooth. For `‖ξ‖ < 1/2` we get `‖c‖ < 1`, so `γ(t)` is a unit.
The local regularity criterion then shows that `A^×` is `C⁰`-regular
([GN26, Theorem 6.3.4]: Banach–Lie groups are `C⁰`-regular, here for unit groups).

## Main definitions

* `UnitGroup.primitiveCLM`: `J η(t) = ∫₀ᵗ η`, a continuous linear operator on `C([0, 1], A)`.
* `UnitGroup.solCLM ξ`: `T_ξ c = J(c ξ)`.
* `UnitGroup.sol ξ = (1 − T_ξ)⁻¹ J ξ`.

## Main results

* `UnitGroup.contDiffOn_sol`: `ξ ↦ c_ξ` is smooth on the unit ball.
* `UnitGroup.isEvolOn_sol`: for `‖ξ‖ < 1/2`, `1 + c_ξ` is the evolution of `ξ` on `[0, 1]`.
* `UnitGroup.isC0Regular`: **the unit group of a real Banach algebra is `C⁰`-regular.**

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace Metric
open scoped Topology unitInterval
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups.UnitGroup

universe u

variable {A : Type u} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]

/-! ### The primitive -/

omit [CompleteSpace A] [NormOneClass A] [NormedAlgebra ℝ A] in
theorem norm_extendCurve_le (η : C(I, A)) (s : ℝ) : ‖MBLieGroup.extendCurve η s‖ ≤ ‖η‖ :=
  η.norm_coe_le_norm _

/-- `J η(t) = ∫₀ᵗ η̃`. -/
def primitive (η : C(I, A)) : C(I, A) :=
  ⟨fun t ↦ ∫ s in (0 : ℝ)..t, MBLieGroup.extendCurve η s,
    (intervalIntegral.continuous_primitive (fun _ _ ↦
      (MBLieGroup.continuous_extendCurve η).intervalIntegrable _ _) 0).comp
      continuous_subtype_val⟩

omit [CompleteSpace A] [NormOneClass A] in
theorem primitive_apply (η : C(I, A)) (t : I) :
    primitive η t = ∫ s in (0 : ℝ)..t, MBLieGroup.extendCurve η s := rfl

/-- **The primitive** `J`, a continuous linear operator of norm `≤ 1`. -/
def primitiveCLM : C(I, A) →L[ℝ] C(I, A) :=
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

omit [CompleteSpace A] [NormOneClass A] in
theorem primitiveCLM_apply (η : C(I, A)) (t : I) :
    primitiveCLM η t = ∫ s in (0 : ℝ)..t, MBLieGroup.extendCurve η s := rfl

omit [CompleteSpace A] [NormOneClass A] in
theorem norm_primitiveCLM_apply_le (η : C(I, A)) : ‖primitiveCLM η‖ ≤ ‖η‖ := by
  refine (primitiveCLM.le_opNorm η).trans ?_
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

/-! ### The linear equation -/

/-- `T_ξ c = J(c ξ)`. -/
def solCLM : C(I, A) →L[ℝ] C(I, A) →L[ℝ] C(I, A) :=
  (ContinuousLinearMap.compL ℝ (C(I, A)) (C(I, A)) (C(I, A)) primitiveCLM).comp
    (ContinuousLinearMap.mul ℝ (C(I, A))).flip

omit [CompleteSpace A] [NormOneClass A] in
theorem solCLM_apply (ξ c : C(I, A)) : solCLM ξ c = primitiveCLM (c * ξ) := rfl

omit [CompleteSpace A] [NormOneClass A] in
theorem norm_solCLM_le (ξ : C(I, A)) : ‖solCLM ξ‖ ≤ ‖ξ‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun c ↦ by
    rw [solCLM_apply, mul_comm ‖ξ‖]
    exact (norm_primitiveCLM_apply_le _).trans (norm_mul_le _ _)

/-- `c_ξ = (1 − T_ξ)⁻¹ J ξ`. -/
def sol (ξ : C(I, A)) : C(I, A) := Ring.inverse (1 - solCLM ξ) (primitiveCLM ξ)

omit [NormOneClass A] in
theorem isUnit_one_sub {ξ : C(I, A)} (hξ : ‖ξ‖ < 1) : IsUnit (1 - solCLM ξ) := by
  have h : ‖solCLM ξ‖ < 1 := (norm_solCLM_le ξ).trans_lt hξ
  have hu := (Units.oneSub (solCLM ξ) h).isUnit
  rwa [Units.val_oneSub] at hu

omit [NormOneClass A] in
/-- **`c_ξ = J((1 + c_ξ) ξ)`.** -/
theorem sol_eq {ξ : C(I, A)} (hξ : ‖ξ‖ < 1) : sol ξ = primitiveCLM ((1 + sol ξ) * ξ) := by
  have h := congrArg (fun L : C(I, A) →L[ℝ] C(I, A) ↦ L (primitiveCLM ξ))
    (Ring.mul_inverse_cancel _ (isUnit_one_sub hξ))
  have h' : sol ξ - solCLM ξ (sol ξ) = primitiveCLM ξ := by
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      FunLike.coe_sub, Pi.sub_apply] at h
    exact h
  rw [add_mul, one_mul, map_add, ← solCLM_apply]
  exact eq_add_of_sub_eq h'

omit [NormOneClass A] in
/-- **`ξ ↦ c_ξ` is smooth on the unit ball**, by the smoothness of the inversion of `L(X)`. -/
theorem contDiffOn_sol (k : ℕ) : ContDiffOn ℝ k (sol (A := A)) (ball 0 1) := by
  intro ξ hξ
  rw [mem_ball_zero_iff] at hξ
  refine ContDiffAt.contDiffWithinAt ?_
  have h : ‖solCLM ξ‖ < 1 := (norm_solCLM_le ξ).trans_lt hξ
  have hinv : ContDiffAt ℝ k Ring.inverse (1 - solCLM ξ) := by
    have := contDiffAt_ringInverse ℝ (Units.oneSub (solCLM ξ) h) (n := k)
    rwa [Units.val_oneSub] at this
  have hS : ContDiff ℝ k ⇑(solCLM (A := A)) := ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := C(I, A))
    (F := C(I, A) →L[ℝ] C(I, A)) solCLM
  have hT : ContDiffAt ℝ k (fun ζ : C(I, A) ↦ 1 - solCLM ζ) ξ :=
    contDiffAt_const.sub hS.contDiffAt
  have hpair : ContDiffAt ℝ k
      (fun ζ : C(I, A) ↦ (Ring.inverse (1 - solCLM ζ), primitiveCLM ζ)) ξ :=
    (ContDiffAt.comp (g := Ring.inverse) (f := fun ζ : C(I, A) ↦ 1 - solCLM ζ) ξ hinv
      hT).prodMk (ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := C(I, A)) (F := C(I, A))
        primitiveCLM).contDiffAt
  exact (isBoundedBilinearMap_apply.contDiff.contDiffAt).comp ξ hpair

theorem norm_sol_lt_one {ξ : C(I, A)} (hξ : ‖ξ‖ < 1 / 2) : ‖sol ξ‖ < 1 := by
  have h1 : ‖ξ‖ < 1 := by linarith
  have h := sol_eq h1
  have hle : ‖sol ξ‖ ≤ (1 + ‖sol ξ‖) * ‖ξ‖ := by
    calc ‖sol ξ‖ = ‖primitiveCLM ((1 + sol ξ) * ξ)‖ := by rw [← h]
      _ ≤ ‖(1 + sol ξ) * ξ‖ := norm_primitiveCLM_apply_le _
      _ ≤ ‖1 + sol ξ‖ * ‖ξ‖ := norm_mul_le _ _
      _ ≤ (1 + ‖sol ξ‖) * ‖ξ‖ := by
        gcongr
        exact (norm_add_le _ _).trans (by rw [norm_one])
  nlinarith [norm_nonneg ξ, norm_nonneg (sol ξ)]

/-! ### The evolution -/

theorem isUnit_sol {ξ : C(I, A)} (hξ : ‖ξ‖ < 1 / 2) (s : ℝ) :
    IsUnit (1 + MBLieGroup.extendCurve (sol ξ) s) := by
  have h : ‖-MBLieGroup.extendCurve (sol ξ) s‖ < 1 := by
    rw [norm_neg]; exact (norm_extendCurve_le _ s).trans_lt (norm_sol_lt_one hξ)
  have hu := (Units.oneSub _ h).isUnit
  rwa [Units.val_oneSub, sub_neg_eq_add] at hu

/-- **The evolution of `ξ`**, `γ(s) = 1 + c_ξ(s)`, for `‖ξ‖ < 1/2`. -/
def solCurve {ξ : C(I, A)} (hξ : ‖ξ‖ < 1 / 2) (s : ℝ) : UnitGroup A :=
  (isUnit_sol hξ s).unit

theorem val_solCurve {ξ : C(I, A)} (hξ : ‖ξ‖ < 1 / 2) (s : ℝ) :
    val (solCurve hξ s) = 1 + MBLieGroup.extendCurve (sol ξ) s := rfl

/-- **`1 + c_ξ` is the evolution of `ξ` on `[0, 1]`**, for `‖ξ‖ < 1/2`. -/
theorem isEvolOn_solCurve {ξ : C(I, A)} (hξ : ‖ξ‖ < 1 / 2) :
    MBLieGroup.IsEvolOn A (MBLieGroup.extendCurve ξ) (solCurve hξ) := by
  set c := sol ξ
  set η := (1 + c) * ξ
  have hc : c = primitiveCLM η := sol_eq (by linarith)
  have hcr : ∀ r ∈ Icc (0 : ℝ) 1,
      MBLieGroup.extendCurve c r = ∫ s in (0 : ℝ)..r, MBLieGroup.extendCurve η s := by
    intro r hr
    rw [MBLieGroup.extendCurve_apply, projIcc_of_mem _ hr, hc]
    rfl
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (MBLieGroup.extendCurve c)
      (MBLieGroup.extendCurve η t) (Icc 0 1) t := fun t ht ↦
    ((MBLieGroup.continuous_extendCurve η).integral_hasStrictDerivAt 0 t).hasDerivAt
      |>.hasDerivWithinAt.congr (fun r hr ↦ hcr r hr) (hcr t ht)
  have hcont : Continuous fun s ↦ val (solCurve hξ s) :=
    continuous_const.add (MBLieGroup.continuous_extendCurve c)
  refine ⟨?_, fun t ht ↦ ⟨?_, ?_⟩⟩
  · apply Units.ext
    change 1 + MBLieGroup.extendCurve c 0 = 1
    rw [hcr 0 ⟨le_rfl, zero_le_one⟩, intervalIntegral.integral_same, add_zero]
  · exact (isOpenEmbedding_val A).isInducing.continuousWithinAt_iff.2
      hcont.continuousWithinAt
  · set a := val (solCurve hξ t)⁻¹
    have ha : a * (1 + MBLieGroup.extendCurve c t) = 1 := by
      rw [← val_solCurve hξ t, ← val_mul, inv_mul_cancel, val_one]
    have hlim := (hasDerivWithinAt_iff_tendsto_slope.1 (hderiv t ht)).const_mul a
    have hval : a * MBLieGroup.extendCurve η t = MBLieGroup.extendCurve ξ t := by
      change a * ((1 + MBLieGroup.extendCurve c t) * MBLieGroup.extendCurve ξ t) = _
      rw [← mul_assoc, ha, one_mul]
    rw [hval] at hlim
    refine hlim.congr fun r ↦ ?_
    change a * slope (MBLieGroup.extendCurve c) t r =
      (r - t)⁻¹ • ((val ((solCurve hξ t)⁻¹ * solCurve hξ r) - 1) -
        (val ((solCurve hξ t)⁻¹ * solCurve hξ t) - 1))
    rw [val_mul, val_mul, val_solCurve, val_solCurve, slope_def_module, mul_smul_comm]
    congr 1
    noncomm_ring

/-- **The unit group of a real Banach algebra is `C⁰`-regular** ([GN26, Theorem 6.3.4], for unit
groups), by the local regularity criterion. -/
theorem isC0Regular : MBLieGroup.IsC0Regular A (UnitGroup A) := by
  set W : Set A := ball 0 (1 / 2)
  have hnorm : ∀ ξ ∈ MBLieGroup.valIn W, ‖ξ‖ < 1 / 2 := fun ξ hξ ↦
    (ContinuousMap.norm_lt_iff _ (by norm_num)).2 fun t ↦ mem_ball_zero_iff.1 (hξ t)
  have hP := (isExp_exp (A := A)).exists_isEvol_const
  set one : I := ⟨1, ⟨zero_le_one, le_rfl⟩⟩
  have hchart : ∀ ξ (hξ : ξ ∈ MBLieGroup.valIn W),
      unitChart A (MBLieGroup.evol A (UnitGroup A) ξ) =
        ContinuousMap.evalCLM (R := ℝ) one (sol ξ) := by
    intro ξ hξ
    rw [MBLieGroup.evol_eq_of_isEvolOn hP (isEvolOn_solCurve (hnorm ξ hξ)), unitChart,
      val_solCurve, add_sub_cancel_left, MBLieGroup.extendCurve_apply,
      projIcc_of_mem _ ⟨zero_le_one, le_rfl⟩]
    rfl
  refine MBLieGroup.isC0Regular_of_local isOpen_ball (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2))
    (fun ξ hξ ↦ ?_) ?_
  · obtain ⟨Γ, hΓ, -⟩ := (isEvolOn_solCurve (hnorm ξ hξ)).exists_isEvol hP
    exact ⟨Γ, hΓ⟩
  intro k
  have hV : IsOpen (MBLieGroup.valIn W) := MBLieGroup.isOpen_valIn isOpen_ball
  have hVball : MBLieGroup.valIn W ⊆ ball 0 1 := fun ξ hξ ↦
    mem_ball_zero_iff.2 ((hnorm ξ hξ).trans (by norm_num))
  have hev : ContDiff ℝ k ⇑(ContinuousMap.evalCLM (R := ℝ) (M := A) one) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := C(I, A)) (F := A) _
  have hF : ContDiffMBOn k (fun ξ ↦ ContinuousMap.evalCLM (R := ℝ) one (sol ξ)) (ball 0 1) :=
    ContDiffOn.contDiffMBOn isOpen_ball (hev.comp_contDiffOn (contDiffOn_sol k))
  have hcont : ContinuousOn (MBLieGroup.evol A (UnitGroup A)) (MBLieGroup.valIn W) :=
    (isOpenEmbedding_unitChart A).isInducing.continuousOn_iff.2
      ((hF.continuousOn.mono hVball).congr fun ξ hξ ↦ hchart ξ hξ)
  refine ⟨hcont, fun ξ _ ↦ ?_⟩
  refine ContDiffMBOn.congr_of_isOpen (isOpen_chartDomain hV hcont _ _) (fun y hy ↦ ?_)
    (hF.mono fun y hy ↦ hVball hy.2.1)
  change _ = unitChart A (MBLieGroup.evol A (UnitGroup A) y)
  rw [hchart y hy.2.1]

end LocallyConvex.LieGroups.UnitGroup
