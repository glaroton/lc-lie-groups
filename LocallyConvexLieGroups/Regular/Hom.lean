/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Regular.Vector

/-!
# Regularity and morphisms

For a morphism of Lie groups `φ : G → H`, `δ(φ ∘ γ) = L(φ) δ(γ)`. Hence, if `G` is
`C⁰`-regular and `L(φ)` has a continuous linear right inverse `sec`, then `H` is `C⁰`-regular,
with `evol_H(ξ) = φ(evol_G(sec ∘ ξ))`. This covers covering morphisms, for which `L(φ)` is an
isomorphism ([GN26, Proposition 6.1.5], one direction).

## Main results

* `MBLieGroup.HasLogDerivAt.map`: `δ(φ ∘ γ) = L(φ) δ(γ)`.
* `MBLieGroup.IsC0Regular.of_hom`: regularity passes to `H`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology unitInterval
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups.MBLieGroup

universe u

variable {E F : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]
  {H : Type*} [Group H] [TopologicalSpace H] [ChartedSpace F H] [MBLieGroup F H]
  {φ : G →* H}

omit [MBLieGroup F H] in
/-- **`δ(φ ∘ γ) = L(φ) δ(γ)`** for a morphism of Lie groups `φ`. -/
theorem HasLogDerivAt.map (hφ : IsHom E F φ) {γ : ℝ → G} {x : E} {t : ℝ}
    (h : HasLogDerivAt E γ x t) :
    HasLogDerivAt F (fun s ↦ φ (γ s))
      (dMB (IsHom.localRep (E := E) (F := F) φ) (chartAt E (1 : G) 1, x)) t := by
  set ψ := chartAt E (1 : G)
  have hc : Continuous φ := continuousOn_univ.1 (hφ 0).1
  refine ⟨hc.continuousAt.comp h.1, ?_⟩
  have h1 := mem_chart_source E (1 : G)
  have hw : ∀ᶠ s in 𝓝 t, (γ t)⁻¹ * γ s ∈ ψ.source := by
    have := isTopologicalGroup E G
    have hc' : ContinuousAt (fun s ↦ (γ t)⁻¹ * γ s) t := continuousAt_const.mul h.1
    have h0 : (γ t)⁻¹ * γ t ∈ ψ.source := by rw [inv_mul_cancel]; exact h1
    exact hc'.preimage_mem_nhds (ψ.open_source.mem_nhds h0)
  have hcd := continuousAt_of_hasDirDerivAt_one h.2
  have hmem : ψ ((γ t)⁻¹ * γ t) ∈ IsHom.localRepDom (E := E) (F := F) φ := by
    rw [inv_mul_cancel]; exact IsHom.one_mem_localRepDom
  have hdom : ∀ᶠ s in 𝓝 t, ψ ((γ t)⁻¹ * γ s) ∈ IsHom.localRepDom (E := E) (F := F) φ :=
    hcd.preimage_mem_nhds (hφ.isOpen_localRepDom.mem_nhds hmem)
  have hd := ((hφ.smoothMBOn_localRep) 1).hasDirDerivAt_comp hφ.isOpen_localRepDom h.2 hmem
  rw [inv_mul_cancel] at hd
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hw] with s hs
  change chartAt F (1 : H) (φ (ψ.symm (ψ ((γ t)⁻¹ * γ s)))) =
    chartAt F (1 : H) ((φ (γ t))⁻¹ * φ (γ s))
  rw [ψ.left_inv hs, map_mul, map_inv]

/-- Postcomposition with a continuous linear map, on `C([0, 1], ·)`. -/
def compLeftCLM (sec : F →L[ℝ] E) : C(I, F) →L[ℝ] C(I, E) where
  toFun ξ := (⟨sec, sec.continuous⟩ : C(F, E)).comp ξ
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  cont := ContinuousMap.continuous_postcomp _

/-- **Regularity passes along morphisms with a split Lie algebra map** ([GN26, Proposition 6.1.5],
for covering morphisms): if `G` is `C⁰`-regular and `L(φ) ∘ sec = id` for a continuous linear `sec`,
then `H` is `C⁰`-regular, with `evol_H(ξ) = φ(evol_G(sec ∘ ξ))`. -/
theorem IsC0Regular.of_hom (hG : IsC0Regular E G) (hφ : IsHom E F φ) (sec : F →L[ℝ] E)
    (hsec : ∀ y, dMB (IsHom.localRep (E := E) (F := F) φ) (chartAt E (1 : G) 1, sec y) = y) :
    IsC0Regular F H := by
  have hevol : ∀ ξ : C(I, F), ∃ γ : ℝ → G, IsEvol E (extendCurve (compLeftCLM sec ξ)) γ ∧
      IsEvol F (extendCurve ξ) (fun s ↦ φ (γ s)) := by
    intro ξ
    obtain ⟨γ, hγ⟩ := hG.semiregular (compLeftCLM sec ξ)
    refine ⟨γ, hγ, by change φ (γ 0) = 1; rw [hγ.1, map_one], fun t ↦ ?_⟩
    have h := (hγ.2 t).map hφ
    change HasLogDerivAt F _ (dMB _ (_, sec (extendCurve ξ t))) t at h
    rwa [hsec] at h
  have hsemi : IsC0Semiregular F H := fun ξ ↦ by
    obtain ⟨γ, -, h⟩ := hevol ξ
    exact ⟨_, h⟩
  refine ⟨hsemi, ?_⟩
  have heq : evol F H = φ ∘ evol E G ∘ compLeftCLM sec := by
    funext ξ
    obtain ⟨γ, hγ, h⟩ := hevol ξ
    simp only [Function.comp_apply, evol_eq h, evol_eq hγ]
  rw [heq]
  exact SmoothMBM.comp (hφ : SmoothMBM E F φ) (hG.smooth.comp fun k ↦
    (contMDiffMBOn_iff_contDiffMBOn isOpen_univ).2 ((compLeftCLM sec).contDiffMBOn k univ))

end LocallyConvex.LieGroups.MBLieGroup
