/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Exponential.Unique

/-!
# Morphisms of connected Lie groups are determined by their Lie algebra morphisms

If `G` is connected and `φ₁, φ₂ : G → H` are morphisms of Lie groups with `L(φ₁) = L(φ₂)`, then
`φ₁ = φ₂` ([GN26, Proposition 5.5.7]).

## Main results

* `MBLieGroup.IsHom.eventuallyEq_of_lieHom_eq`: `φ₁ = φ₂` near the identity, for any `G`.
* `MBLieGroup.IsHom.eq_of_lieHom_eq`: **`φ₁ = φ₂` if `G` is connected** ([GN26,
  Proposition 5.5.7]).

## Proof

Glöckner and Neeb show that the logarithmic derivative of `ψ = φ₁ φ₂⁻¹` vanishes ([GN26,
Lemmas 5.5.4, 5.5.6]). We argue in the charts `χ`, `θ` at the identities, with the local group
laws `∗`. The local representative `P = θ ∘ ψ ∘ χ⁻¹` has `dP(χ(1)) = L(φ₁) − L(φ₂) = 0`, since the
multiplication has derivative `(a, b) ↦ a + b` and the inversion `−id` at the identity. From
`ψ(k k') = φ₁(k) ψ(k') φ₂(k)⁻¹`, `P(z ∗ w) = (P₁(z) ∗ P(w)) ∗ ι(P₂(z))`, whose derivative in `w` at
the identity vanishes; so `dP(z) ∘ d(z ∗ ·)(1) = 0`, and `d(z ∗ ·)(1)` is onto, being inverted by
`d(z⁻¹ ∗ ·)(z)`. Hence `dP = 0` near `χ(1)`, `P` is constant on a convex neighborhood, and
`φ₁ = φ₂` near `1`. The subgroup where they agree is then open, hence closed, and is all of `G`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups.MBLieGroup

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]
  {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {H : Type*} [Group H] [TopologicalSpace H] [ChartedSpace F H] [MBLieGroup F H]

theorem hasDirDerivAt_const_curve' {X Y : Type*} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y] (c : Y) (p v : X) :
    HasDirDerivAt (fun _ : X ↦ c) p v 0 := by
  simp only [HasDirDerivAt, sub_self, smul_zero]; exact tendsto_const_nhds

namespace IsHom

/-- `ψ = φ₁ φ₂⁻¹`. -/
def quot (φ₁ φ₂ : G →* H) (g : G) : H := φ₁ g * (φ₂ g)⁻¹

omit [TopologicalSpace G] [TopologicalSpace H] in
theorem quot_one (φ₁ φ₂ : G →* H) : quot φ₁ φ₂ 1 = 1 := by simp [quot]

omit [TopologicalSpace G] [TopologicalSpace H] in
theorem quot_mul (φ₁ φ₂ : G →* H) (k k' : G) :
    quot φ₁ φ₂ (k * k') = φ₁ k * quot φ₁ φ₂ k' * (φ₂ k)⁻¹ := by
  simp only [quot, map_mul, mul_inv_rev, mul_assoc]

variable {φ₁ φ₂ : G →* H} (hφ₁ : IsHom E F φ₁) (hφ₂ : IsHom E F φ₂)
include hφ₁ hφ₂

theorem smoothMBM_quot : SmoothMBM E F (quot φ₁ φ₂) := by
  have hi : SmoothMBM E F (fun g ↦ (φ₂ g)⁻¹) := (smoothMBM_inv (E := F) (G := H)).comp hφ₂
  exact (smoothMBM_mul (E := F) (G := H)).comp (fun k ↦ ContMDiffMBOn.prodMk
    (f := ⇑φ₁) (g := fun g ↦ (φ₂ g)⁻¹) isOpen_univ (hφ₁ k) (hi k))

/-- The local representative `P = θ ∘ ψ ∘ χ⁻¹` is `C¹` on its domain. -/
theorem contDiffMBOn_P :
    ContDiffMBOn 1 (fun z ↦ chartAt F (1 : H) (quot φ₁ φ₂ ((chartAt E (1 : G)).symm z)))
      (chartDomain (quot φ₁ φ₂) univ (chartAt E (1 : G)) (chartAt F (1 : H))) := by
  have h := (smoothMBM_quot hφ₁ hφ₂ 1).2 1 (mem_univ _)
  rw [quot_one] at h
  exact h


/-- `dP(χ(1)) = L(φ₁) − L(φ₂)`. -/
theorem hasDirDerivAt_P_one (v : E) :
    HasDirDerivAt (fun z ↦ chartAt F (1 : H) (quot φ₁ φ₂ ((chartAt E (1 : G)).symm z)))
      (chartAt E (1 : G) 1) v (hφ₁.lieHom v - hφ₂.lieHom v) := by
  set χ := chartAt E (1 : G)
  set θ := chartAt F (1 : H)
  set LH := localGroupLaw F H
  set ι := localInverse F H
  have h1 := mem_chart_source E (1 : G)
  have h1' := mem_chart_source F (1 : H)
  have hR₁ := (hφ₁.smoothMBOn_localRep 1).hasDirDerivAt (k := 0) one_mem_localRepDom v
  have hR₂ := (hφ₂.smoothMBOn_localRep 1).hasDirDerivAt (k := 0) one_mem_localRepDom v
  have hR₂χ : localRep (E := E) (F := F) φ₂ (chartAt E (1 : G) 1) = LH.one := localRep_one
  have hιR₂ := (ι.contDiffMBOn.of_le (by norm_num : 1 ≤ 2)).hasDirDerivAt_comp ι.isOpen_dom hR₂
    (by have := ι.one_mem; rwa [← hR₂χ] at this)
  rw [hR₂χ, ι.dMB_inv_one] at hιR₂
  have hpt : (localRep (E := E) (F := F) φ₁ (chartAt E (1 : G) 1),
      (ι.inv ∘ localRep (E := E) (F := F) φ₂) (chartAt E (1 : G) 1)) = (LH.one, LH.one) := by
    simp only [Function.comp_apply, hR₂χ]
    exact Prod.ext localRep_one ι.inv_one
  have hd := (LH.smooth 1).hasDirDerivAt_comp LH.isOpen_dom (hR₁.prodMk hιR₂)
    (by rw [hpt]; exact LH.one_one_mem)
  rw [hpt, LH.dMB_mul_one] at hd
  simp only at hd
  rw [← sub_eq_add_neg] at hd
  refine hd.congr_of_eventuallyEq ?_
  -- near `χ(1)`, `P(z) = P₁(z) ∗ ι(P₂(z))`
  set O : Set G := {k | φ₁ k ∈ θ.source ∧ φ₂ k ∈ θ.source ∧ (φ₂ k)⁻¹ ∈ θ.source}
  have := isTopologicalGroup F H
  have hc₁ : Continuous φ₁ := continuousOn_univ.1 (hφ₁ 0).continuousOn
  have hc₂ : Continuous φ₂ := continuousOn_univ.1 (hφ₂ 0).continuousOn
  have hO : IsOpen O := (θ.open_source.preimage hc₁).inter ((θ.open_source.preimage hc₂).inter
    (θ.open_source.preimage (hc₂.inv)))
  have hW : χ.target ∩ χ.symm ⁻¹' (χ.source ∩ O) ∈ 𝓝 (χ 1) :=
    (χ.isOpen_inter_preimage_symm (χ.open_source.inter hO)).mem_nhds
      ⟨χ.map_source h1, by
        rw [mem_preimage, χ.left_inv h1]
        exact ⟨h1, by rw [map_one]; exact h1', by rw [map_one]; exact h1',
          by rw [map_one, inv_one]; exact h1'⟩⟩
  filter_upwards [hW] with z hz
  obtain ⟨-, hk, hk₁, hk₂, hk₃⟩ := hz
  simp only [Function.comp_apply, localRep]
  change LH.mul (θ (φ₁ (χ.symm z)), θ ((θ.symm (θ (φ₂ (χ.symm z))))⁻¹)) =
    θ (quot φ₁ φ₂ (χ.symm z))
  rw [θ.left_inv hk₂, chart_mul_eq hk₁ hk₃]
  rfl

theorem dMB_P_one (hL : ∀ x, hφ₁.lieHom x = hφ₂.lieHom x) (v : E) :
    dMB (fun z ↦ chartAt F (1 : H) (quot φ₁ φ₂ ((chartAt E (1 : G)).symm z)))
      (chartAt E (1 : G) 1, v) = 0 := by
  rw [(hasDirDerivAt_P_one hφ₁ hφ₂ v).dMB_eq, hL v, sub_self]
  rfl

/-- The set where the argument works: `k = χ⁻¹(z)` with `k`, `k⁻¹` in the chart domain and
`φ₁(k)`, `φ₂(k)`, `φ₂(k)⁻¹`, `ψ(k)` in the chart domain of `H`. -/
def goodSet (φ₁ φ₂ : G →* H) : Set E :=
  (chartAt E (1 : G)).target ∩ (chartAt E (1 : G)).symm ⁻¹'
    {k | k ∈ (chartAt E (1 : G)).source ∧ k⁻¹ ∈ (chartAt E (1 : G)).source ∧
      φ₁ k ∈ (chartAt F (1 : H)).source ∧ φ₂ k ∈ (chartAt F (1 : H)).source ∧
      (φ₂ k)⁻¹ ∈ (chartAt F (1 : H)).source ∧ quot φ₁ φ₂ k ∈ (chartAt F (1 : H)).source}

theorem isOpen_goodSet : IsOpen (goodSet (E := E) (F := F) φ₁ φ₂) := by
  have := isTopologicalGroup F H
  have := isTopologicalGroup E G
  have hc₁ : Continuous φ₁ := continuousOn_univ.1 (hφ₁ 0).continuousOn
  have hc₂ : Continuous φ₂ := continuousOn_univ.1 (hφ₂ 0).continuousOn
  have hq : Continuous (quot φ₁ φ₂) := hc₁.mul hc₂.inv
  set χ := chartAt E (1 : G)
  set θ := chartAt F (1 : H)
  refine χ.isOpen_inter_preimage_symm ?_
  exact χ.open_source.inter ((χ.open_source.preimage continuous_inv).inter
    ((θ.open_source.preimage hc₁).inter ((θ.open_source.preimage hc₂).inter
      ((θ.open_source.preimage hc₂.inv).inter (θ.open_source.preimage hq)))))

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [MBLieGroup E G] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [MBLieGroup F H] hφ₁ hφ₂ in
theorem one_mem_goodSet : chartAt E (1 : G) 1 ∈ goodSet (E := E) (F := F) φ₁ φ₂ := by
  have h1 := mem_chart_source E (1 : G)
  have h1' := mem_chart_source F (1 : H)
  refine ⟨(chartAt E (1 : G)).map_source h1, ?_⟩
  rw [mem_preimage, (chartAt E (1 : G)).left_inv h1]
  exact ⟨h1, by rwa [inv_one], by rwa [map_one], by rwa [map_one],
    by rw [map_one, inv_one]; exact h1', by rwa [quot_one]⟩

/-- **`dP` vanishes on the good set.** -/
theorem dMB_P_eq_zero (hL : ∀ x, hφ₁.lieHom x = hφ₂.lieHom x) {z : E}
    (hz : z ∈ goodSet (E := E) (F := F) φ₁ φ₂) (u : E) :
    dMB (fun z ↦ chartAt F (1 : H) (quot φ₁ φ₂ ((chartAt E (1 : G)).symm z))) (z, u) = 0 := by
  set χ := chartAt E (1 : G)
  set θ := chartAt F (1 : H)
  set LG := localGroupLaw E G
  set LH := localGroupLaw F H
  set ι := localInverse F H
  set P : E → F := fun z ↦ θ (quot φ₁ φ₂ (χ.symm z))
  set k := χ.symm z
  obtain ⟨hzt, hk, hki, hk₁, hk₂, hk₃, hkq⟩ := hz
  have h1 := mem_chart_source E (1 : G)
  have h1' := mem_chart_source F (1 : H)
  have hP := contDiffMBOn_P hφ₁ hφ₂
  have hDopen : IsOpen (chartDomain (quot φ₁ φ₂) univ χ θ) :=
    isOpen_chartDomain isOpen_univ (smoothMBM_quot hφ₁ hφ₂ 0).continuousOn _ _
  have hzD : z ∈ chartDomain (quot φ₁ φ₂) univ χ θ := ⟨hzt, mem_univ _, hkq⟩
  have hχk : χ k = z := χ.right_inv hzt
  -- (a) `dP(z)(x̃_l(z)) = 0`
  have hz1 : (z, LG.one) ∈ LG.dom := by
    rw [← hχk]; exact chart_mem_dom hk h1 (by rw [mul_one]; exact hk)
  have hxl : ∀ v, dMB P (z, LG.xl v z) = 0 := by
    intro v
    -- first computation: chain rule through `w ↦ z ∗ w`
    have hA : HasDirDerivAt (P ∘ fun w ↦ LG.mul (z, w)) LG.one v (dMB P (z, LG.xl v z)) := by
      have hin := (LG.contDiffMBOn_mul_left 1 z).hasDirDerivAt (k := 0) hz1 v
      have h := hP.hasDirDerivAt_comp hDopen hin (by rw [LG.mul_one z hz1]; exact hzD)
      rwa [LG.mul_one z hz1, ← LocalGroupLaw.xl_eq] at h
    -- second computation: `P(z ∗ w) = (P₁(z) ∗ P(w)) ∗ ι(P₂(z))`
    set a := θ (φ₁ k)
    set c := ι.inv (θ (φ₂ k))
    have hc : c = θ ((φ₂ k)⁻¹) := by
      change θ ((θ.symm (θ (φ₂ k)))⁻¹) = _
      rw [θ.left_inv hk₂]
    have hP1 : P LG.one = θ 1 := by
      change θ (quot φ₁ φ₂ (χ.symm (χ 1))) = θ 1
      rw [χ.left_inv h1, quot_one]
    have ha1 : (a, P LG.one) ∈ LH.dom := by
      rw [hP1]; exact chart_mem_dom hk₁ h1' (by rw [mul_one]; exact hk₁)
    have hmid : LH.mul (a, P LG.one) = θ (φ₁ k) := by
      rw [hP1, chart_mul_eq hk₁ h1', mul_one]
    have hac : (LH.mul (a, P LG.one), c) ∈ LH.dom := by
      rw [hmid, hc]; exact chart_mem_dom hk₁ hk₃ hkq
    have hPin : HasDirDerivAt P LG.one v 0 := by
      have h := hP.hasDirDerivAt (k := 0) (by
        exact ⟨χ.map_source h1, mem_univ _, by
          rw [mem_preimage, χ.left_inv h1, quot_one]; exact h1'⟩) v
      rwa [dMB_P_one hφ₁ hφ₂ hL v] at h
    have hB1 : HasDirDerivAt (fun w ↦ LH.mul (a, P w)) LG.one v 0 := by
      have h := (LH.contDiffMBOn_mul_left 1 a).hasDirDerivAt_comp (LH.isOpen_domL a) hPin ha1
      have hz : dMB (fun b ↦ LH.mul (a, b)) (P LG.one, 0) = 0 := by
        have := (LH.contDiffMBOn_mul_left 1 a).dMB_smul ha1 0 0
        simpa using this
      rwa [hz] at h
    have hB : HasDirDerivAt (fun w ↦ LH.mul (LH.mul (a, P w), c)) LG.one v 0 := by
      have h := (LH.smooth 1).hasDirDerivAt_comp LH.isOpen_dom
        (hB1.prodMk (hasDirDerivAt_const_curve' c LG.one v)) hac
      have hz : dMB LH.mul ((LH.mul (a, P LG.one), c), ((0 : F), (0 : F))) = 0 := by
        have := (LH.smooth 1).dMB_smul hac 0 ((0 : F), (0 : F))
        rw [Prod.mk_zero_zero]
        simpa using this
      rwa [hz] at h
    -- the two functions agree near the identity
    have hev : (fun w ↦ LH.mul (LH.mul (a, P w), c)) =ᶠ[𝓝 LG.one]
        P ∘ fun w ↦ LG.mul (z, w) := by
      have := isTopologicalGroup F H
      have := isTopologicalGroup E G
      have hc₁ : Continuous φ₁ := continuousOn_univ.1 (hφ₁ 0).continuousOn
      have hc₂ : Continuous φ₂ := continuousOn_univ.1 (hφ₂ 0).continuousOn
      have hq : Continuous (quot φ₁ φ₂) := hc₁.mul hc₂.inv
      set O : Set G := {k' | k' ∈ χ.source ∧ k * k' ∈ χ.source ∧ quot φ₁ φ₂ k' ∈ θ.source ∧
        φ₁ k * quot φ₁ φ₂ k' ∈ θ.source ∧ quot φ₁ φ₂ (k * k') ∈ θ.source}
      have hO : IsOpen O := χ.open_source.inter
        ((χ.open_source.preimage (continuous_const.mul continuous_id)).inter
          ((θ.open_source.preimage hq).inter ((θ.open_source.preimage
            (continuous_const.mul hq)).inter
              (θ.open_source.preimage (hq.comp (continuous_const.mul continuous_id))))))
      have hmem : χ.target ∩ χ.symm ⁻¹' O ∈ 𝓝 LG.one :=
        (χ.isOpen_inter_preimage_symm hO).mem_nhds ⟨χ.map_source h1, by
          change χ.symm (χ 1) ∈ O
          rw [χ.left_inv h1]
          exact ⟨h1, by rwa [mul_one], by rw [quot_one]; exact h1',
            by rw [quot_one, mul_one]; exact hk₁, by rwa [mul_one]⟩⟩
      filter_upwards [hmem] with w hw'
      obtain ⟨-, hw, hkw, hqw, hq1w, hqkw⟩ := hw'
      change LH.mul (LH.mul (θ (φ₁ k), θ (quot φ₁ φ₂ (χ.symm w))), c) =
        θ (quot φ₁ φ₂ (χ.symm (χ (χ.symm z * χ.symm w))))
      rw [chart_mul_eq hk₁ hqw, hc, chart_mul_eq hq1w hk₃, χ.left_inv hkw, quot_mul]
    have hA' := hB.congr_of_eventuallyEq hev
    exact tendsto_nhds_unique hA hA'
  -- (b) `v ↦ x̃_l(v)(z)` is onto
  set z' := χ k⁻¹
  have hz'z : (z', z) ∈ LG.dom := by
    rw [← hχk]; exact chart_mem_dom hki hk (by rw [inv_mul_cancel]; exact h1)
  have hz'z1 : LG.mul (z', z) = LG.one := by
    rw [← hχk, chart_mul_eq hki hk, inv_mul_cancel]; rfl
  set v := dMB (fun y ↦ LG.mul (z', y)) (z, u)
  have hsurj : LG.xl v z = u := by
    rw [LocalGroupLaw.xl_eq]
    have hin := (LG.contDiffMBOn_mul_left 1 z').hasDirDerivAt (k := 0) hz'z u
    have h := (LG.contDiffMBOn_mul_left 1 z).hasDirDerivAt_comp (LG.isOpen_domL z) hin
      (by rw [hz'z1]; exact hz1)
    rw [hz'z1] at h
    have hid : (fun y ↦ LG.mul (z, y)) ∘ (fun y ↦ LG.mul (z', y)) =ᶠ[𝓝 z] fun y ↦ y := by
      have := isTopologicalGroup E G
      set O : Set G := {g | g ∈ χ.source ∧ k⁻¹ * g ∈ χ.source}
      have hO : IsOpen O := χ.open_source.inter
        (χ.open_source.preimage (continuous_const.mul continuous_id))
      have hmem : χ.target ∩ χ.symm ⁻¹' O ∈ 𝓝 z :=
        (χ.isOpen_inter_preimage_symm hO).mem_nhds ⟨hzt, hk, by
          rw [inv_mul_cancel]; exact h1⟩
      filter_upwards [hmem] with y hy'
      obtain ⟨hy, hy1, hy2⟩ := hy'
      change χ (χ.symm z * χ.symm (χ (χ.symm (χ k⁻¹) * χ.symm y))) = y
      rw [χ.left_inv hki, χ.left_inv hy2, mul_inv_cancel_left, χ.right_inv hy]
    have hid' : HasDirDerivAt (fun y : E ↦ y) z u u :=
      (ContinuousLinearMap.id ℝ E).hasDirDerivAt z u
    exact tendsto_nhds_unique (h.congr_of_eventuallyEq hid) hid'
  rw [← hsurj]
  exact hxl v

/-- **`φ₁ = φ₂` near the identity** if `L(φ₁) = L(φ₂)`. -/
theorem eventuallyEq_of_lieHom_eq (hL : ∀ x, hφ₁.lieHom x = hφ₂.lieHom x) :
    ⇑φ₁ =ᶠ[𝓝 1] ⇑φ₂ := by
  set χ := chartAt E (1 : G)
  set θ := chartAt F (1 : H)
  set P : E → F := fun z ↦ θ (quot φ₁ φ₂ (χ.symm z))
  have h1 := mem_chart_source E (1 : G)
  have h1' := mem_chart_source F (1 : H)
  have hP := contDiffMBOn_P hφ₁ hφ₂
  -- a convex open neighborhood of `χ(1)` inside the good set
  obtain ⟨S, ⟨hSn, hSc⟩, hSW⟩ := (LocallyConvexSpace.convex_basis (𝕜 := ℝ) (χ 1)).mem_iff.1
    ((isOpen_goodSet hφ₁ hφ₂).mem_nhds one_mem_goodSet)
  set V := interior S
  have hV : IsOpen V := isOpen_interior
  have hVc : Convex ℝ V := hSc.interior
  have h1V : χ 1 ∈ V := mem_interior_iff_mem_nhds.2 hSn
  have hVW : V ⊆ goodSet (E := E) (F := F) φ₁ φ₂ := interior_subset.trans hSW
  have hDopen : IsOpen (chartDomain (quot φ₁ φ₂) univ χ θ) :=
    isOpen_chartDomain isOpen_univ (smoothMBM_quot hφ₁ hφ₂ 0).continuousOn _ _
  have hgD : goodSet (E := E) (F := F) φ₁ φ₂ ⊆ chartDomain (quot φ₁ φ₂) univ χ θ :=
    fun z hz ↦ ⟨hz.1, mem_univ _, hz.2.2.2.2.2.2⟩
  have hconst : ∀ z ∈ V, P z = θ 1 := by
    intro z hz
    set ℓ : ℝ → E := fun t ↦ t • (z - χ 1) + χ 1
    have hℓ : ℓ = ⇑(AffineMap.lineMap (χ 1) z : ℝ →ᵃ[ℝ] E) := by
      funext t; rw [AffineMap.lineMap_apply]; rfl
    set J := ℓ ⁻¹' V
    have hJ : IsOpen J := hV.preimage (by fun_prop)
    have hJc : IsPreconnected J := by
      rw [show J = (AffineMap.lineMap (χ 1) z : ℝ →ᵃ[ℝ] E) ⁻¹' V by rw [← hℓ]]
      exact (hVc.affine_preimage _).isPreconnected
    have hd : ∀ t ∈ J, HasDirDerivAt (P ∘ ℓ) t 1 0 := by
      intro t ht
      have hin : HasDirDerivAt ℓ t 1 (z - χ 1) := by
        unfold HasDirDerivAt
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with r (hr : r ≠ 0)
        simp only [ℓ, smul_eq_mul, mul_one, add_smul, add_sub_add_right_eq_sub,
          add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr, one_smul]
      have h := hP.hasDirDerivAt_comp hDopen hin (hgD (hVW ht))
      rwa [dMB_P_eq_zero hφ₁ hφ₂ hL (hVW ht)] at h
    have h0J : (0 : ℝ) ∈ J := by simpa [J, ℓ] using h1V
    have h1J : (1 : ℝ) ∈ J := by simpa [J, ℓ] using hz
    have he := eq_of_hasDirDerivAt_zero hJ hJc hd h1J h0J
    simp only [Function.comp_apply, ℓ, one_smul, sub_add_cancel, zero_smul, zero_add] at he
    rw [he]
    change θ (quot φ₁ φ₂ (χ.symm (χ 1))) = θ 1
    rw [χ.left_inv h1, quot_one]
  have hN : χ.source ∩ χ ⁻¹' V ∈ 𝓝 (1 : G) :=
    inter_mem (χ.open_source.mem_nhds h1) ((χ.continuousAt h1).preimage_mem_nhds
      (hV.mem_nhds h1V))
  filter_upwards [hN] with g hg'
  obtain ⟨hg, hgV⟩ := hg'
  have hPg := hconst (χ g) hgV
  have hgq : quot φ₁ φ₂ g ∈ θ.source := by
    have := (hVW hgV).2.2.2.2.2.2
    rwa [χ.left_inv hg] at this
  change θ (quot φ₁ φ₂ (χ.symm (χ g))) = θ 1 at hPg
  rw [χ.left_inv hg] at hPg
  exact mul_inv_eq_one.mp (θ.injOn hgq h1' hPg)

/-- **Morphisms of connected Lie groups are determined by their Lie algebra morphisms**
([GN26, Proposition 5.5.7]): if `G` is connected and `L(φ₁) = L(φ₂)`, then `φ₁ = φ₂`. -/
theorem eq_of_lieHom_eq [PreconnectedSpace G] (hL : ∀ x, hφ₁.lieHom x = hφ₂.lieHom x) :
    φ₁ = φ₂ := by
  have := isTopologicalGroup E G
  set S := MonoidHom.eqLocus φ₁ φ₂
  have hS : (S : Set G) ∈ 𝓝 (1 : G) := eventuallyEq_of_lieHom_eq hφ₁ hφ₂ hL
  have hO := Subgroup.isOpen_of_mem_nhds S hS
  have hC := Subgroup.isClosed_of_isOpen S hO
  have hU := IsClopen.eq_univ ⟨hC, hO⟩ ⟨1, S.one_mem⟩
  ext g
  have hg : g ∈ (S : Set G) := hU ▸ mem_univ g
  exact hg

end IsHom

end LocallyConvex.LieGroups.MBLieGroup
