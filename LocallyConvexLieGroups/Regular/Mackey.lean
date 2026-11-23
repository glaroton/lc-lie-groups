/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Regular.Ck
public import LocallyConvexLieGroups.Regular.Vector
public import LocallyConvexAnalysis.Calculus.MackeyLipschitz

/-!
# Vector groups of Mackey complete spaces are regular

If `E` is Mackey complete, the vector group `(E, +)` is `C^k`-regular for every `k ≥ 1`, and
regular, with `evol(ξ) = ∫₀¹ ξ` ([GN26, Proposition 6.1.3], the implication from Mackey
completeness). A curve `ξ ∈ C^k([0, 1], E)` with `k ≥ 1` is Lipschitz: by the mean value inclusion on `[0, 1]`
(lc-analysis, `ContDiffLC.quotient_mem_closure_convexHull_of_convex`), its difference quotients lie
in the closed convex hull of `0` and its derivatives, a bounded set; the same holds for its
extension `ξ̃` by constants. Mackey complete spaces integrate Lipschitz curves (lc-analysis,
`MackeyComplete.exists_hasWeakIntegral_of_isLipschitzCurve`), and the fundamental theorem of
calculus gives the evolution `t ↦ ∫₀ᵗ ξ̃`.

## Main results

* `MBLieGroup.CkCurve.isLipschitzCurve`: `C^k` curves, `k ≥ 1`, are Lipschitz.
* `VectorGroup.isEvol_integral_ck`, `VectorGroup.integralCkCLM`.
* `VectorGroup.isCkRegular`, `VectorGroup.isRegular_of_mackeyComplete`: **`(E, +)` is
  `C^k`-regular (`k ≥ 1`) and regular for `E` Mackey complete.**

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology unitInterval
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

namespace MBLieGroup.CkCurve

variable {k : ℕ}

/-- The closed convex hull of `0` and the derivatives of `ξ ∈ C^k([0, 1], E)`, `k ≥ 1`. -/
def derivHull (ξ : CkCurve E k) : Set E :=
  closure (convexHull ℝ (insert 0
    ((fun τ ↦ dLC (⇑ξ) (Icc (0 : ℝ) 1) (τ, 1)) '' Icc (0 : ℝ) 1)))

theorem convex_derivHull (ξ : CkCurve E k) : Convex ℝ (derivHull ξ) :=
  (convex_convexHull ℝ _).closure

theorem zero_mem_derivHull (ξ : CkCurve E k) : (0 : E) ∈ derivHull ξ :=
  subset_closure (subset_convexHull ℝ _ (mem_insert _ _))

theorem isVonNBounded_derivHull (hk : 1 ≤ k) (ξ : CkCurve E k) :
    Bornology.IsVonNBounded ℝ (derivHull ξ) := by
  have hg : ContDiffLC 1 (⇑ξ) (Icc (0 : ℝ) 1) := ξ.contDiffLC.of_le hk
  have hc : IsCompact ((fun τ ↦ dLC (⇑ξ) (Icc (0 : ℝ) 1) (τ, 1)) '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn (hg.continuousOn_dLC_left 1)
  exact (isVonNBounded_convexHull ((hc.isVonNBounded (𝕜 := ℝ)).insert 0)).closure

/-- **Mean value inclusion**: the difference quotients of `ξ` on `[0, 1]` lie in `derivHull ξ`. -/
theorem quotient_mem_derivHull (hk : 1 ≤ k) (ξ : CkCurve E k) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≠ t) :
    (s - t)⁻¹ • (ξ s - ξ t) ∈ derivHull ξ := by
  have hg : ContDiffLC 1 (⇑ξ) (Icc (0 : ℝ) 1) := ξ.contDiffLC.of_le hk
  have hz : (1 / 2 : ℝ) ∈ interior (Icc (0 : ℝ) 1) := by
    rw [interior_Icc]; constructor <;> norm_num
  have hyt : t + (s - t) • (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simpa using hs
  have h := hg.quotient_mem_closure_convexHull_of_convex hasDenseInterior_Icc subset_rfl
    (convex_Icc 0 1) hz (sub_ne_zero.2 hst) ht hyt
  simp only [smul_eq_mul, mul_one, add_sub_cancel] at h
  refine closure_mono (convexHull_mono ?_) h
  rintro _ ⟨r, hr, rfl⟩
  refine mem_insert_of_mem _ ⟨t + r * (s - t), ?_, rfl⟩
  simpa using (convex_Icc (0 : ℝ) 1).add_smul_sub_mem ht hs hr

/-- **`C^1` curves are Lipschitz**: the difference quotients of the extension `ξ̃` of
`ξ ∈ C^k([0, 1], E)`, `k ≥ 1`, lie in `derivHull ξ`. -/
theorem diffQuot_subset (hk : 1 ≤ k) (ξ : CkCurve E k) (a b : ℝ) :
    diffQuot (extendCurve (toC0 ξ)) a b ⊆ derivHull ξ := by
  rintro _ ⟨s, -, t, -, hst, rfl⟩
  set s' := projIcc (0 : ℝ) 1 zero_le_one s
  set t' := projIcc (0 : ℝ) 1 zero_le_one t
  have he : ∀ r, extendCurve (toC0 ξ) r = ξ (projIcc (0 : ℝ) 1 zero_le_one r : ℝ) :=
    fun _ ↦ rfl
  rw [he, he]
  by_cases hst' : (s' : ℝ) = t'
  · rw [hst', sub_self, smul_zero]; exact zero_mem_derivHull ξ
  have hq := quotient_mem_derivHull hk ξ s'.2 t'.2 hst'
  have hlip : |(s' : ℝ) - t'| ≤ |s - t| := abs_projIcc_sub_projIcc zero_le_one
  set c := (s - t)⁻¹ * ((s' : ℝ) - t')
  have hc0 : 0 ≤ c := by
    rcases lt_or_gt_of_ne hst with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos (inv_nonpos.2 (sub_nonpos.2 h.le))
        (sub_nonpos.2 (monotone_projIcc zero_le_one h.le))
    · exact mul_nonneg (inv_nonneg.2 (sub_nonneg.2 h.le))
        (sub_nonneg.2 (monotone_projIcc zero_le_one h.le))
  have hc1 : c ≤ 1 := by
    have : |c| ≤ 1 := by
      rw [abs_mul, abs_inv]
      exact inv_mul_le_one_of_le₀ hlip (abs_nonneg _)
    exact (le_abs_self c).trans this
  have heq : (s - t)⁻¹ • (ξ s' - ξ t') = c • (((s' : ℝ) - t')⁻¹ • (ξ s' - ξ t')) := by
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ (sub_ne_zero.2 hst'), mul_one]
  rw [heq]
  exact (convex_derivHull ξ).smul_mem_of_zero_mem (zero_mem_derivHull ξ) hq ⟨hc0, hc1⟩

theorem isLipschitzCurve (hk : 1 ≤ k) (ξ : CkCurve E k) (a b : ℝ) :
    IsLipschitzCurve (extendCurve (toC0 ξ)) a b :=
  (isVonNBounded_derivHull hk ξ).subset (diffQuot_subset hk ξ a b)

end MBLieGroup.CkCurve

namespace VectorGroup

open MBLieGroup

variable [MackeyComplete E] {k : ℕ}

theorem exists_hasWeakIntegral_ck (hk : 1 ≤ k) (ξ : CkCurve E k) (s : ℝ) :
    ∃ y, HasWeakIntegral (extendCurve (CkCurve.toC0 ξ)) 0 s y := by
  rcases lt_trichotomy 0 s with h | rfl | h
  · exact MackeyComplete.exists_hasWeakIntegral_of_isLipschitzCurve h
      (CkCurve.isLipschitzCurve hk ξ 0 s)
  · exact ⟨0, hasWeakIntegral_same _ 0⟩
  · obtain ⟨y, hy⟩ := MackeyComplete.exists_hasWeakIntegral_of_isLipschitzCurve h
      (CkCurve.isLipschitzCurve hk ξ s 0)
    exact ⟨-y, hy.symm⟩

/-- **`t ↦ ∫₀ᵗ ξ̃` is the evolution of `ξ ∈ C^k([0, 1], E)`**, `k ≥ 1`, for `E` Mackey
complete. -/
theorem isEvol_integral_ck (hk : 1 ≤ k) (ξ : CkCurve E k) :
    IsEvol E (extendCurve (CkCurve.toC0 ξ))
      (fun t ↦ Multiplicative.ofAdd (weakIntegral (extendCurve (CkCurve.toC0 ξ)) 0 t)) := by
  set ξ' := extendCurve (CkCurve.toC0 ξ)
  have hc : Continuous ξ' := continuous_extendCurve _
  have hI : ∀ t, HasDirDerivAt (fun s ↦ weakIntegral ξ' 0 s) t 1 (ξ' t) := fun t ↦
    hasDirDerivAt_weakIntegral_right_of_exists isOpen_univ ordConnected_univ hc.continuousOn
      (mem_univ _) (fun s _ ↦ exists_hasWeakIntegral_ck hk ξ s) (mem_univ _)
  refine ⟨?_, fun t ↦ ⟨continuous_ofAdd.continuousAt.comp (continuousAt_of_hasDirDerivAt_one
    (hI t)), ?_⟩⟩
  · change Multiplicative.ofAdd (weakIntegral ξ' 0 0) = Multiplicative.ofAdd 0
    rw [(hasWeakIntegral_same ξ' 0).weakIntegral_eq]
  · have h := (hI t).sub (show HasDirDerivAt (fun _ : ℝ ↦ weakIntegral ξ' 0 t) t 1 0 by
      simp only [HasDirDerivAt, sub_self, smul_zero]; exact tendsto_const_nhds)
    rw [sub_zero] at h
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ ?_)
    change weakIntegral ξ' 0 s - weakIntegral ξ' 0 t =
      -weakIntegral ξ' 0 t + weakIntegral ξ' 0 s
    abel

theorem hasWeakIntegral_ck (hk : 1 ≤ k) (ξ : CkCurve E k) :
    HasWeakIntegral (extendCurve (CkCurve.toC0 ξ)) 0 1
      (weakIntegral (extendCurve (CkCurve.toC0 ξ)) 0 1) :=
  hasWeakIntegral_weakIntegral (exists_hasWeakIntegral_ck hk ξ 1)

/-- The integral `ξ ↦ ∫₀¹ ξ`, as a linear map on `C^k([0, 1], E)`. -/
def integralCkLM (hk : 1 ≤ k) : CkCurve E k →ₗ[ℝ] E where
  toFun ξ := weakIntegral (extendCurve (CkCurve.toC0 ξ)) 0 1
  map_add' ξ η := by
    have h := (hasWeakIntegral_ck hk ξ).add (continuous_extendCurve _).continuousOn
      (continuous_extendCurve _).continuousOn (hasWeakIntegral_ck hk η)
    rw [map_add]
    exact h.weakIntegral_eq
  map_smul' c ξ := by
    rw [map_smul]
    exact ((hasWeakIntegral_ck hk ξ).const_smul c).weakIntegral_eq

theorem continuous_integralCkLM (hk : 1 ≤ k) : Continuous (integralCkLM (E := E) hk) := by
  refine continuous_of_continuousAt_zero (integralCkLM (E := E) hk).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  intro N hN
  rw [Filter.mem_map]
  obtain ⟨W, hW, hWN⟩ := exists_nhds_weakIntegral_mem (zero_le_one' ℝ) hN
  obtain ⟨V, hVW, hVo, hV0⟩ := mem_nhds_iff.1 hW
  have hO : IsOpen {ξ : CkCurve E k | MapsTo (CkCurve.toC0 ξ) univ V} :=
    (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ hVo).preimage
      (CkCurve.toC0 (E := E) (k := k)).continuous
  have h0 : (0 : CkCurve E k) ∈ {ξ : CkCurve E k | MapsTo (CkCurve.toC0 ξ) univ V} := by
    intro t _; rw [map_zero]; exact hV0
  filter_upwards [hO.mem_nhds h0] with ξ hξ
  refine hWN _ _ (continuous_extendCurve _).continuousOn (hasWeakIntegral_ck hk ξ)
    fun t ht ↦ hVW ?_
  rw [extendCurve, IccExtend_of_mem _ _ ht]
  exact hξ (mem_univ _)

/-- **The integral `ξ ↦ ∫₀¹ ξ`**, a continuous linear map `C^k([0, 1], E) → E`. -/
def integralCkCLM (hk : 1 ≤ k) : CkCurve E k →L[ℝ] E :=
  ⟨integralCkLM hk, continuous_integralCkLM hk⟩

/-- **`(E, +)` is `C^k`-regular for `E` Mackey complete**, `k ≥ 1`
([GN26, Proposition 6.1.3], one direction). -/
theorem isCkRegular (hk : 1 ≤ k) : IsCkRegular E (Multiplicative E) k where
  semiregular ξ := ⟨_, isEvol_integral_ck hk ξ⟩
  smooth := by
    have h : (fun ξ : CkCurve E k ↦ evol E (Multiplicative E) (CkCurve.toC0 ξ)) =
        (fun x : E ↦ Multiplicative.ofAdd x) ∘ ⇑(integralCkCLM (E := E) hk) := by
      funext ξ
      rw [evol_eq (isEvol_integral_ck hk ξ)]
      rfl
    rw [h]
    exact (isExp E).smooth.comp fun k ↦
      (contMDiffMBOn_iff_contDiffMBOn isOpen_univ).2 ((integralCkCLM hk).contDiffMBOn k univ)

/-- **`(E, +)` is regular for `E` Mackey complete** ([GN26, Proposition 6.1.3]). -/
theorem isRegular_of_mackeyComplete : IsRegular E (Multiplicative E) :=
  (isCkRegular (E := E) le_rfl).isRegular

end VectorGroup

end LocallyConvex.LieGroups
