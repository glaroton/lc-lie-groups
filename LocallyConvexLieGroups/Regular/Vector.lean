/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Regular.Evol
public import LocallyConvexAnalysis.Calculus.Integral.FundamentalTheorem

/-!
# Vector groups are `C⁰`-regular

If `E` is sequentially complete, every continuous curve `ξ : [0, 1] → E` has an integral, and
the vector group `(E, +)` is `C⁰`-regular with `evol(ξ) = ∫₀¹ ξ` ([GN26, Proposition 6.1.3];
Glöckner–Neeb treat `k ≥ 1` with Mackey completeness, the proof for `k = 0` is the same with the
integrals of continuous curves).

## Main results

* `continuousAt_of_hasDirDerivAt_one`: differentiable curves are continuous.
* `VectorGroup.isEvol_integral`: `t ↦ ∫₀ᵗ ξ̃` is the evolution of `ξ`.
* `VectorGroup.integralCLM`: `ξ ↦ ∫₀¹ ξ̃`, a continuous linear map `C([0, 1], E) → E`.
* `VectorGroup.isC0Regular`: **`(E, +)` is `C⁰`-regular** for `E` sequentially complete.

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

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- **Differentiable curves are continuous.** -/
theorem continuousAt_of_hasDirDerivAt_one {c : ℝ → E} {t : ℝ} {y : E}
    (h : HasDirDerivAt c t 1 y) : ContinuousAt c t := by
  have h1 : Tendsto (fun s : ℝ ↦ s • (s⁻¹ • (c (t + s • (1 : ℝ)) - c t))) (𝓝[≠] 0)
      (𝓝 ((0 : ℝ) • y)) :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).smul h
  rw [zero_smul] at h1
  have h2 : Tendsto (fun s : ℝ ↦ c (t + s) - c t) (𝓝[≠] 0) (𝓝 0) := by
    refine h1.congr' (eventually_nhdsWithin_of_forall fun s hs ↦ ?_)
    have hs : s ≠ 0 := hs
    simp [smul_smul, mul_inv_cancel₀ hs]
  have h3 : Tendsto (fun s : ℝ ↦ c (t + s) - c t) (𝓝 0) (𝓝 0) := by
    rw [← nhdsNE_sup_pure (0 : ℝ)]
    refine h2.sup ?_
    simpa using tendsto_pure_nhds (fun s : ℝ ↦ c (t + s) - c t) (0 : ℝ)
  have h4 : Tendsto (fun s : ℝ ↦ s - t) (𝓝 t) (𝓝 0) := tendsto_sub_nhds_zero_iff.2 tendsto_id
  have h5 := h3.comp h4
  simp only [Function.comp_def, add_sub_cancel] at h5
  exact tendsto_sub_nhds_zero_iff.1 h5

namespace VectorGroup

variable [SeqComplete E]

/-- **`t ↦ ∫₀ᵗ ξ̃` is the evolution of `ξ`** in the vector group `(E, +)`. -/
theorem isEvol_integral (ξ : C(I, E)) :
    MBLieGroup.IsEvol E (MBLieGroup.extendCurve ξ)
      (fun t ↦ Multiplicative.ofAdd (weakIntegral (MBLieGroup.extendCurve ξ) 0 t)) := by
  set ξ' := MBLieGroup.extendCurve ξ
  have hc : Continuous ξ' := MBLieGroup.continuous_extendCurve ξ
  have hI : ∀ t, HasDirDerivAt (fun s ↦ weakIntegral ξ' 0 s) t 1 (ξ' t) := fun t ↦
    hasDirDerivAt_weakIntegral_right isOpen_univ ordConnected_univ hc.continuousOn (mem_univ _)
      (mem_univ _)
  refine ⟨?_, fun t ↦ ⟨continuous_ofAdd.continuousAt.comp (continuousAt_of_hasDirDerivAt_one
    (hI t)), ?_⟩⟩
  · change Multiplicative.ofAdd (weakIntegral ξ' 0 0) = Multiplicative.ofAdd 0
    rw [(hasWeakIntegral_same ξ' 0).weakIntegral_eq]
  · have h := (hI t).sub (hasDirDerivAt_const_curve (weakIntegral ξ' 0 t) t)
    rw [sub_zero] at h
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ ?_)
    change weakIntegral ξ' 0 s - weakIntegral ξ' 0 t =
      -weakIntegral ξ' 0 t + weakIntegral ξ' 0 s
    abel

theorem hasWeakIntegral_extendCurve (ξ : C(I, E)) :
    HasWeakIntegral (MBLieGroup.extendCurve ξ) 0 1
      (weakIntegral (MBLieGroup.extendCurve ξ) 0 1) :=
  hasWeakIntegral_weakIntegral
    (exists_hasWeakIntegral (MBLieGroup.continuous_extendCurve ξ).continuousOn)

/-- The integral `ξ ↦ ∫₀¹ ξ̃`, as a linear map. -/
def integralLM : C(I, E) →ₗ[ℝ] E where
  toFun ξ := weakIntegral (MBLieGroup.extendCurve ξ) 0 1
  map_add' ξ η := ((hasWeakIntegral_extendCurve ξ).add
    (MBLieGroup.continuous_extendCurve ξ).continuousOn
    (MBLieGroup.continuous_extendCurve η).continuousOn
    (hasWeakIntegral_extendCurve η)).weakIntegral_eq
  map_smul' c ξ := ((hasWeakIntegral_extendCurve ξ).const_smul c).weakIntegral_eq

theorem continuous_integralLM : Continuous (integralLM (E := E)) := by
  refine continuous_of_continuousAt_zero (integralLM (E := E)).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  intro N hN
  rw [Filter.mem_map]
  obtain ⟨W, hW, hWN⟩ := exists_nhds_weakIntegral_mem (zero_le_one' ℝ) hN
  obtain ⟨V, hVW, hVo, hV0⟩ := mem_nhds_iff.1 hW
  have hO : IsOpen {ξ : C(I, E) | MapsTo ξ univ V} :=
    ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ hVo
  have h0 : (0 : C(I, E)) ∈ {ξ : C(I, E) | MapsTo ξ univ V} := fun _ _ ↦ hV0
  filter_upwards [hO.mem_nhds h0] with ξ hξ
  refine hWN _ _ (MBLieGroup.continuous_extendCurve ξ).continuousOn
    (hasWeakIntegral_extendCurve ξ) fun t ht ↦ hVW ?_
  rw [MBLieGroup.extendCurve, IccExtend_of_mem _ _ ht]
  exact hξ (mem_univ _)

/-- **The integral `ξ ↦ ∫₀¹ ξ̃`**, a continuous linear map `C([0, 1], E) → E`. -/
def integralCLM : C(I, E) →L[ℝ] E := ⟨integralLM, continuous_integralLM⟩

/-- **`(E, +)` is `C⁰`-regular** for `E` sequentially complete, with `evol(ξ) = ∫₀¹ ξ`
([GN26, Proposition 6.1.3], case `k = 0`). -/
theorem isC0Regular : MBLieGroup.IsC0Regular E (Multiplicative E) where
  semiregular ξ := ⟨_, isEvol_integral ξ⟩
  smooth := by
    have h : MBLieGroup.evol E (Multiplicative E) =
        (fun x : E ↦ Multiplicative.ofAdd x) ∘ ⇑(integralCLM (E := E)) := by
      funext ξ
      rw [MBLieGroup.evol_eq (isEvol_integral ξ)]
      rfl
    rw [h]
    exact (isExp E).smooth.comp fun k ↦
      (contMDiffMBOn_iff_contDiffMBOn isOpen_univ).2 ((integralCLM (E := E)).contDiffMBOn k univ)

end VectorGroup

end LocallyConvex.LieGroups
