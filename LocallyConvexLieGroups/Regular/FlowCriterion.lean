/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Regular.Interval
public import LocallyConvexLieGroups.Regular.Vector

/-!
# Evolutions from flows

For groups of diffeomorphisms, the evolution `γ` of a curve `ξ` of vector fields is the inverse of
the flow `η` of `-ξ`: `γ(t) = η_t⁻¹`. This file isolates the group theoretic part of the argument
used for the universal cover of `Diff⁺(S¹)` (`CircleCover/Regular.lean`).

Let `W` be an open `0`-neighborhood of `𝔤` and `Ψ` a `C¹` map on `C([0, 1], W)` with
`Ψ(0) = 0` and `dΨ(0, -x) = x` for the constant curves (think of `Ψ(ζ)` as the time-one map of the
flow of `-ζ`, in the chart at the identity). Suppose that `η : ℝ → G` satisfies `η(0) = 1` and

  `φ(η_t η_r⁻¹) = Ψ(ζ_{r → t})`,  `ζ_{r → t}(w) = (t - r) ξ(r + w (t - r))`,

for `r, t ∈ [0, 1]` (the flow from `r` to `t` is the time-one map of the rescaled curve
`ζ_{r → t}`). Then `γ(t) = η_t⁻¹` is an evolution of `ξ` on `[0, 1]`
(`MBLieGroup.isEvolOn_of_flow`): `γ(t)⁻¹ γ(r) = η_t η_r⁻¹`, and
`ζ_{t + h → t} = h Z_h` with `Z_h → -ξ(t)` (constant), so `δ(γ)(t) = dΨ(0, -ξ(t)) = ξ(t)`.

## Main definitions

* `MBLieGroup.shiftField ξ s t`: the rescaled curve `ζ_{s → t}`.

## Main results

* `MBLieGroup.isEvolOn_of_flow`: **evolutions from flows.**
-/

@[expose] public section

open Set Filter Function
open scoped Topology unitInterval
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups.MBLieGroup

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

/-! ### Rescaled curves -/

/-- `ζ_{s → t}(w) = (t - s) ξ(s + w (t - s))`: the curve of the flow from `s` to `t`. -/
def shiftField (ξ : C(I, E)) (s t : ℝ) : C(I, E) :=
  ⟨fun w ↦ (t - s) • extendCurve ξ (s + w * (t - s)), by
    have h : Continuous fun w : I ↦ s + (w : ℝ) * (t - s) := by fun_prop
    exact ((continuous_extendCurve ξ).comp h).const_smul (t - s)⟩

omit [IsTopologicalAddGroup E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem shiftField_apply (ξ : C(I, E)) (s t : ℝ) (w : I) :
    shiftField ξ s t w = (t - s) • extendCurve ξ (s + w * (t - s)) := rfl

theorem abs_sub_le_one {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    |t - s| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]

theorem mem_Icc_of_mem {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    {w : ℝ} (hw : w ∈ Icc (0 : ℝ) 1) : s + w * (t - s) ∈ Icc (0 : ℝ) 1 := by
  constructor <;> nlinarith [hs.1, hs.2, ht.1, ht.2, hw.1, hw.2]

omit [IsTopologicalAddGroup E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem shiftField_mem {W : Set E} (hW : ∀ x ∈ W, ∀ c : ℝ, |c| ≤ 1 → c • x ∈ W) {ξ : C(I, E)}
    (hξ : ξ ∈ valIn W) {s t : ℝ} (hst : |t - s| ≤ 1) : shiftField ξ s t ∈ valIn W := fun w ↦ by
  rw [shiftField_apply, extendCurve_apply]
  exact hW _ (hξ _) _ hst

/-- `Z_h(w) = -ξ(t + h (1 - w))`. -/
def Zc (ξ : C(I, E)) (t h : ℝ) : C(I, E) :=
  ⟨fun w ↦ -extendCurve ξ (t + h * (1 - w)), by
    have hc : Continuous fun w : I ↦ t + h * (1 - (w : ℝ)) := by fun_prop
    exact ((continuous_extendCurve ξ).comp hc).neg⟩

omit [LocallyConvexSpace ℝ E] [T2Space E] in
theorem shiftField_eq (ξ : C(I, E)) (t h : ℝ) : shiftField ξ (t + h) t = h • Zc ξ t h := by
  ext w : 1
  rw [shiftField_apply, ContinuousMap.smul_apply]
  change _ = h • -extendCurve ξ (t + h * (1 - w))
  rw [show t + h + w * (t - (t + h)) = t + h * (1 - w) by ring, show t - (t + h) = -h by ring,
    neg_smul, smul_neg]

omit [Module ℝ E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem continuous_Zc (ξ : C(I, E)) (t : ℝ) : Continuous (Zc ξ t) :=
  ContinuousMap.continuous_of_continuous_uncurry _ <| by
    have hc : Continuous fun p : ℝ × I ↦ t + p.1 * (1 - (p.2 : ℝ)) := by fun_prop
    exact ((continuous_extendCurve ξ).comp hc).neg

omit [Module ℝ E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem Zc_zero (ξ : C(I, E)) (t : ℝ) : Zc ξ t 0 = -ContinuousMap.const I (extendCurve ξ t) := by
  ext w : 1
  change -extendCurve ξ (t + 0 * (1 - w)) = _
  simp

omit [LocallyConvexSpace ℝ E] [T2Space E] in
theorem shiftField_self (ξ : C(I, E)) (t : ℝ) : shiftField ξ (t + 0) t = 0 := by
  rw [shiftField_eq, zero_smul]

omit [LocallyConvexSpace ℝ E] [T2Space E] in
theorem shiftField_self' (ξ : C(I, E)) (t : ℝ) : shiftField ξ t t = 0 := by
  have h := shiftField_self ξ t
  rwa [add_zero] at h

omit [LocallyConvexSpace ℝ E] [T2Space E] in
theorem hasDirDerivAt_shift (ξ : C(I, E)) (t : ℝ) :
    HasDirDerivAt (fun h ↦ shiftField ξ (t + h) t) 0 1 (Zc ξ t 0) := by
  unfold HasDirDerivAt
  have hZ : Tendsto (Zc ξ t) (𝓝[≠] 0) (𝓝 (Zc ξ t 0)) :=
    (continuous_Zc ξ t).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine hZ.congr' (eventually_nhdsWithin_of_forall fun h (hh : h ≠ 0) ↦ ?_)
  change Zc ξ t h = h⁻¹ • (shiftField ξ (t + (0 + h • 1)) t - shiftField ξ (t + 0) t)
  rw [show (0 : ℝ) + h • (1 : ℝ) = h by simp, shiftField_eq, shiftField_self, sub_zero,
    smul_smul, inv_mul_cancel₀ hh, one_smul]

theorem tendsto_sub_nhdsNE (t : ℝ) :
    Tendsto (fun r ↦ r - t) (𝓝[Icc (0 : ℝ) 1 \ {t}] t) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun r hr ↦
    sub_ne_zero.2 (by simpa using hr.2)⟩
  have h : Tendsto (fun r : ℝ ↦ r - t) (𝓝 t) (𝓝 (t - t)) :=
    (continuous_id.sub continuous_const).tendsto t
  rw [sub_self] at h
  exact h.mono_left nhdsWithin_le_nhds

/-! ### Evolutions from flows -/

variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]

/-- **Evolutions from flows**: if `φ(η_t η_r⁻¹) = Ψ(ζ_{r → t})` for a `C¹` map `Ψ` with
`Ψ(0) = 0` and `dΨ(0, -x) = x`, then `t ↦ η_t⁻¹` is an evolution of `ξ` on `[0, 1]`. -/
theorem isEvolOn_of_flow {W : Set E} (hWo : IsOpen W) (h0W : (0 : E) ∈ W) {Ψ : C(I, E) → E}
    (hΨ : ContDiffMBOn 1 Ψ (valIn W)) (hΨ0 : Ψ 0 = 0)
    (hdΨ : ∀ x, dMB Ψ (0, -ContinuousMap.const I x) = x) {ξ : C(I, E)} {η : ℝ → G} (hη0 : η 0 = 1)
    (hsrc : ∀ t ∈ Icc (0 : ℝ) 1, ∀ r ∈ Icc (0 : ℝ) 1, η t * (η r)⁻¹ ∈ (chartAt E (1 : G)).source)
    (hchart : ∀ t ∈ Icc (0 : ℝ) 1, ∀ r ∈ Icc (0 : ℝ) 1,
      chartAt E (1 : G) (η t * (η r)⁻¹) = Ψ (shiftField ξ r t)) :
    IsEvolOn E (extendCurve ξ) fun t ↦ (η t)⁻¹ := by
  have := isTopologicalGroup E G
  have hzero : (0 : C(I, E)) ∈ valIn W := fun _ ↦ h0W
  refine ⟨by simp [hη0], fun t ht ↦ ?_⟩
  have hinv : ∀ r, ((η t)⁻¹)⁻¹ * (η r)⁻¹ = η t * (η r)⁻¹ := fun r ↦ by rw [inv_inv]
  have hd : HasDirDerivAt (fun h ↦ Ψ (shiftField ξ (t + h) t)) 0 1 (extendCurve ξ t) := by
    have h := hΨ.hasDirDerivAt_comp (isOpen_valIn hWo) (hasDirDerivAt_shift ξ t)
      (by rw [shiftField_self]; exact hzero)
    rw [shiftField_self, Zc_zero, hdΨ] at h
    exact h
  have hc : Tendsto (fun r ↦ Ψ (shiftField ξ (t + (r - t)) t)) (𝓝[Icc 0 1] t) (𝓝 0) := by
    have h1 := (continuousAt_of_hasDirDerivAt_one hd).tendsto
    rw [shiftField_self, hΨ0] at h1
    refine h1.comp ?_
    have h : Tendsto (fun r : ℝ ↦ r - t) (𝓝 t) (𝓝 (t - t)) :=
      (continuous_id.sub continuous_const).tendsto t
    rw [sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hφ : ∀ r ∈ Icc (0 : ℝ) 1,
      chartAt E (1 : G) (η t * (η r)⁻¹) = Ψ (shiftField ξ (t + (r - t)) t) := fun r hr ↦ by
    rw [add_sub_cancel]; exact hchart t ht r hr
  have hone : chartAt E (1 : G) 1 = 0 := by
    have h := hchart t ht t ht
    rwa [mul_inv_cancel, shiftField_self', hΨ0] at h
  refine ⟨?_, ?_⟩
  · -- continuity: `η_t η_r⁻¹ → 1`
    have h1 : Tendsto (fun r ↦ η t * (η r)⁻¹) (𝓝[Icc 0 1] t) (𝓝 1) := by
      have hs : ContinuousAt (chartAt E (1 : G)).symm 0 := by
        rw [← hone]
        exact (chartAt E (1 : G)).continuousAt_symm
          ((chartAt E (1 : G)).map_source (mem_chart_source E 1))
      have h2 := hs.tendsto.comp hc
      rw [← hone, (chartAt E (1 : G)).left_inv (mem_chart_source E 1)] at h2
      refine h2.congr' (eventually_nhdsWithin_of_forall fun r hr ↦ ?_)
      simp only [Function.comp_apply]
      rw [← hφ r hr, (chartAt E (1 : G)).left_inv (hsrc t ht r hr)]
    have h2 := h1.const_mul (η t)⁻¹
    rw [mul_one] at h2
    refine h2.congr fun r ↦ ?_
    rw [inv_mul_cancel_left]
  · have hlim := hd.comp (tendsto_sub_nhdsNE t)
    refine hlim.congr' (eventually_nhdsWithin_of_forall fun r hr ↦ ?_)
    simp only [Function.comp_apply]
    rw [hinv, hinv, hφ r hr.1, hφ t ht]
    simp only [zero_add, smul_eq_mul, mul_one, sub_self, add_zero]

end LocallyConvex.LieGroups.MBLieGroup
