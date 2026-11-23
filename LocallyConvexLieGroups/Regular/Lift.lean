/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Regular.Hom
public import LocallyConvexLieGroups.Regular.Interval
public import Mathlib.Analysis.LocallyConvex.BalancedCoreHull

/-!
# Regularity lifts along local diffeomorphisms

Let `φ : G → H` be a morphism of Lie groups which is a local diffeomorphism at `1`: there are open
identity neighborhoods `U ⊆ G`, `V ⊆ H` and a smooth `ρ : V → U` inverse to `φ`. If `H` is
`C⁰`-regular, so is `G` ([GN26, Proposition 6.1.5], the other direction). For `ξ` near `0`, the
evolution `Γ` of `L(φ) ∘ ξ` in `H` stays in `V`, and `ρ ∘ Γ` is the evolution of `ξ`: near `t`,
`ρ(Γ t)⁻¹ ρ(Γ r) = ρ(Γ(t)⁻¹ Γ(r))` since `φ` is injective on `U`, and `d(ρ)(1) L(φ) = id`.

## Main results

* `MBLieGroup.IsC0Regular.of_localDiffeo`: **`C⁰`-regularity lifts along local diffeomorphisms.**

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology unitInterval Pointwise
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

/-! ### Rescaled curves -/

/-- `t ↦ s t` on `[0, 1]`, for `s ∈ [0, 1]`. -/
def scaleMap (s : I) : C(I, I) :=
  ⟨fun t ↦ ⟨s * t, unitInterval.mul_mem s.2 t.2⟩, by fun_prop⟩

omit [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- `S(η, s)(t) = s η(s t)`. -/
def scaleCurve (η : C(I, F)) (s : I) : C(I, F) := (s : ℝ) • η.comp (scaleMap s)

omit [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem extendCurve_scaleCurve (η : C(I, F)) (s : I) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    extendCurve (scaleCurve η s) r = (s : ℝ) • extendCurve η (s * r) := by
  have hsr : (s : ℝ) * r ∈ Icc (0 : ℝ) 1 := unitInterval.mul_mem s.2 hr
  rw [extendCurve_apply, extendCurve_apply, projIcc_of_mem _ hr, projIcc_of_mem _ hsr]
  rfl

omit [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [MBLieGroup F H] in
/-- **`r ↦ Γ(s r)` is the evolution of `S(η, s)` on `[0, 1]`.** -/
theorem IsEvol.isEvolOn_scale {η : C(I, F)} {Γ : ℝ → H} (h : IsEvol F (extendCurve η) Γ)
    (s : I) : IsEvolOn F (extendCurve (scaleCurve η s)) fun r ↦ Γ (s * r) := by
  refine ⟨by simp [h.1], fun r hr ↦ ?_⟩
  rw [extendCurve_scaleCurve η s hr]
  exact ((h.2 ((s : ℝ) * r)).comp_mul (c := (s : ℝ)) (r := r)).hasLogDerivWithinAt _

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [MBLieGroup F H] in
theorem isEvol_zero : IsEvol F (fun _ ↦ (0 : F)) (fun _ ↦ (1 : H)) :=
  ⟨rfl, fun t ↦ ⟨continuousAt_const, hasDirDerivAt_const_curve _ t⟩⟩

theorem evol_zero : evol F H (0 : C(I, F)) = 1 :=
  evol_eq (γ := fun _ ↦ (1 : H)) isEvol_zero

/-! ### Lifting evolutions -/

variable {φ : G →* H}

/-- **`C⁰`-regularity lifts along local diffeomorphisms** ([GN26, Proposition 6.1.5]): if
`φ : G → H` is a morphism of Lie groups with a smooth local inverse `ρ : V → U` near `1` and `H` is
`C⁰`-regular, then `G` is `C⁰`-regular. -/
theorem IsC0Regular.of_localDiffeo (hH : IsC0Regular F H) (hφ : IsHom E F φ) {U : Set G}
    {V : Set H} (hU : IsOpen U) (hV : IsOpen V) (h1U : (1 : G) ∈ U) (h1V : (1 : H) ∈ V)
    {ρ : H → G} (hρ : SmoothMBMOn F E ρ V) (hρU : MapsTo ρ V U)
    (hφρ : ∀ h ∈ V, φ (ρ h) = h) (hρφ : ∀ g ∈ U, ρ (φ g) = g) : IsC0Regular E G := by
  have := isTopologicalGroup E G
  have := isTopologicalGroup F H
  set ψG := chartAt E (1 : G)
  set ψH := chartAt F (1 : H)
  have hρ1 : ρ 1 = 1 := by have := hρφ 1 h1U; rwa [map_one] at this
  have hρc : ContinuousOn ρ V := (hρ 0).1
  have hφc : Continuous φ := continuousOn_univ.1 (hφ 0).1
  have hinj : ∀ g₁ ∈ U, ∀ g₂ ∈ U, φ g₁ = φ g₂ → g₁ = g₂ := fun g₁ h₁ g₂ h₂ he ↦ by
    rw [← hρφ g₁ h₁, he, hρφ g₂ h₂]
  -- `L(φ)` as a continuous linear map
  set Lφ : E →L[ℝ] F :=
    ⟨hφ.lieHom.toLinearMap, hφ.continuous_lieHom⟩
  have hLφ : ∀ x, Lφ x = dMB (IsHom.localRep (E := E) (F := F) φ) (ψG 1, x) := fun _ ↦ rfl
  -- `ρ` in the charts at the identity, and `dρ(1) L(φ) = id`
  set R : F → E := ψG ∘ ρ ∘ ψH.symm
  set DR := chartDomain ρ V ψH ψG
  have hDR : IsOpen DR := isOpen_chartDomain hV hρc ψH ψG
  have hRs : SmoothMBOn R DR := fun k ↦ by
    have h := (hρ k).2 1 h1V
    rw [hρ1] at h
    exact h
  have h1G := mem_chart_source E (1 : G)
  have h1H := mem_chart_source F (1 : H)
  have hψH1 : ψH 1 ∈ DR := ⟨ψH.map_source h1H,
    ⟨by rw [ψH.left_inv h1H]; exact h1V,
    by change ρ (ψH.symm (ψH 1)) ∈ ψG.source; rw [ψH.left_inv h1H, hρ1]; exact h1G⟩⟩
  have hR1 : R (ψH 1) = ψG 1 := by
    change ψG (ρ (ψH.symm (ψH 1))) = ψG 1; rw [ψH.left_inv h1H, hρ1]
  have hR : ∀ x, dMB R (ψH 1, Lφ x) = x := by
    intro x
    have hloc1 : IsHom.localRep (E := E) (F := F) φ (ψG 1) = ψH 1 := IsHom.localRep_one
    have hd := (hRs 1).hasDirDerivAt_comp hDR
      ((hφ.smoothMBOn_localRep 1).hasDirDerivAt IsHom.one_mem_localRepDom x)
      (by rw [hloc1]; exact hψH1)
    rw [hloc1, ← hLφ] at hd
    have hev : (R ∘ IsHom.localRep (E := E) (F := F) φ) =ᶠ[𝓝 (ψG 1)] id := by
      have hO : IsOpen (ψG.target ∩ ψG.symm ⁻¹' U) := ψG.isOpen_inter_preimage_symm hU
      have hmem : ψG 1 ∈ ψG.target ∩ ψG.symm ⁻¹' U :=
        ⟨ψG.map_source h1G, by rw [mem_preimage, ψG.left_inv h1G]; exact h1U⟩
      filter_upwards [hO.mem_nhds hmem,
        hφ.isOpen_localRepDom.mem_nhds IsHom.one_mem_localRepDom] with b hb hbd
      change ψG (ρ (ψH.symm (ψH (φ (ψG.symm b))))) = b
      rw [ψH.left_inv hbd.2.2, hρφ _ hb.2, ψG.right_inv hb.1]
    have hid : HasDirDerivAt (R ∘ IsHom.localRep (E := E) (F := F) φ) (ψG 1) x x :=
      ((ContinuousLinearMap.id ℝ E).hasDirDerivAt _ _).congr_of_eventuallyEq hev.symm
    exact (hd.dMB_eq).symm.trans hid.dMB_eq
  -- a neighborhood of `0` in `C([0, 1], F)` whose evolutions stay in `V`
  have hPH := hH.isExp.exists_isEvol_const
  have hevc : Continuous (evol F H) := continuousOn_univ.1 (hH.smooth 0).1
  have hN : evol F H ⁻¹' V ∈ 𝓝 (0 : C(I, F)) :=
    hevc.continuousAt.preimage_mem_nhds (hV.mem_nhds (by rw [evol_zero]; exact h1V))
  obtain ⟨⟨K, W₀⟩, ⟨-, hW₀⟩, hsub⟩ :=
    ((𝓝 (0 : F)).basis_sets.nhds_continuousMapConst (X := I)).mem_iff.1 hN
  obtain ⟨B, ⟨hB, hBbal⟩, hBW⟩ := (nhds_basis_balanced ℝ F).mem_iff.1 hW₀
  set WG : Set E := interior (Lφ ⁻¹' B)
  have hWGo : IsOpen WG := isOpen_interior
  have hWG0 : (0 : E) ∈ WG :=
    mem_interior_iff_mem_nhds.2 (Lφ.continuous.continuousAt.preimage_mem_nhds (by simpa using hB))
  -- for `ξ` with values in `W_G`, the evolution of `L(φ) ∘ ξ` stays in `V` on `[0, 1]`
  have hstay : ∀ ξ ∈ valIn WG, ∀ Γ : ℝ → H, IsEvol F (extendCurve (compLeftCLM Lφ ξ)) Γ →
      ∀ s ∈ Icc (0 : ℝ) 1, Γ s ∈ V := by
    intro ξ hξ Γ hΓ s hs
    have hS : scaleCurve (compLeftCLM Lφ ξ) ⟨s, hs⟩ ∈ evol F H ⁻¹' V := by
      refine hsub fun t _ ↦ hBW ?_
      change s • Lφ (ξ (scaleMap ⟨s, hs⟩ t)) ∈ B
      refine hBbal.smul_mem ?_ (interior_subset (hξ (scaleMap ⟨s, hs⟩ t)) : _)
      rw [Real.norm_of_nonneg hs.1]; exact hs.2
    have he := evol_eq_of_isEvolOn hPH (hΓ.isEvolOn_scale ⟨s, hs⟩)
    simp only [mul_one] at he
    rw [mem_preimage, he] at hS
    exact hS
  -- the lift `ρ ∘ Γ` is the evolution of `ξ` on `[0, 1]`
  have hlift : ∀ ξ ∈ valIn WG, ∀ Γ : ℝ → H, IsEvol F (extendCurve (compLeftCLM Lφ ξ)) Γ →
      IsEvolOn E (extendCurve ξ) fun r ↦ ρ (Γ r) := by
    intro ξ hξ Γ hΓ
    have hΓV := hstay ξ hξ Γ hΓ
    have hΓc : Continuous Γ := continuous_iff_continuousAt.2 fun t ↦ (hΓ.2 t).1
    refine ⟨by change ρ (Γ 0) = 1; rw [hΓ.1, hρ1], fun t ht ↦ ⟨?_, ?_⟩⟩
    · exact (hρc (Γ t) (hΓV t ht)).comp hΓc.continuousWithinAt fun r hr ↦ hΓV r hr
    -- the derivative of `R(φ_H(Γ(t)⁻¹ Γ(r)))`
    have hmem : ψH ((Γ t)⁻¹ * Γ t) ∈ DR := by rw [inv_mul_cancel]; exact hψH1
    have hd := (hRs 1).hasDirDerivAt_comp hDR (hΓ.2 t).2 hmem
    rw [inv_mul_cancel] at hd
    change HasDirDerivAt _ t 1 (dMB R (ψH 1, Lφ (extendCurve ξ t))) at hd
    rw [hR] at hd
    have hsl := (hasDirDerivAt_one_iff_slope.1 hd).mono_left
      (nhdsWithin_mono t fun r (hr : r ∈ Icc (0 : ℝ) 1 \ {t}) ↦ hr.2)
    refine hsl.congr' ?_
    -- near `t`, `ρ(Γ t)⁻¹ ρ(Γ r) = ρ(Γ(t)⁻¹ Γ(r))`
    have hw : ∀ᶠ r in 𝓝 t, (Γ t)⁻¹ * Γ r ∈ V ∩ ψH.source := by
      have hc : ContinuousAt (fun r ↦ (Γ t)⁻¹ * Γ r) t := continuousAt_const.mul hΓc.continuousAt
      have h0 : (Γ t)⁻¹ * Γ t ∈ V ∩ ψH.source := by rw [inv_mul_cancel]; exact ⟨h1V, h1H⟩
      exact hc.preimage_mem_nhds ((hV.inter ψH.open_source).mem_nhds h0)
    have hu : ∀ᶠ r in 𝓝[Icc (0 : ℝ) 1] t, (ρ (Γ t))⁻¹ * ρ (Γ r) ∈ U := by
      have hc : ContinuousWithinAt (fun r ↦ (ρ (Γ t))⁻¹ * ρ (Γ r)) (Icc 0 1) t :=
        continuousWithinAt_const.mul
          ((hρc (Γ t) (hΓV t ht)).comp hΓc.continuousWithinAt fun r hr ↦ hΓV r hr)
      have h0 : (ρ (Γ t))⁻¹ * ρ (Γ t) ∈ U := by rw [inv_mul_cancel]; exact h1U
      exact hc.preimage_mem_nhdsWithin (hU.mem_nhds h0)
    have hu' := nhdsWithin_mono t (fun r (hr : r ∈ Icc (0 : ℝ) 1 \ {t}) ↦ hr.1) hu
    have hw' := nhdsWithin_le_nhds (s := Icc (0 : ℝ) 1 \ {t}) hw
    have hI : ∀ᶠ r in 𝓝[Icc (0 : ℝ) 1 \ {t}] t, r ∈ Icc (0 : ℝ) 1 :=
      eventually_nhdsWithin_of_forall fun r hr ↦ hr.1
    filter_upwards [hu', hw', hI] with r hru hrw hrI
    have heq : (ρ (Γ t))⁻¹ * ρ (Γ r) = ρ ((Γ t)⁻¹ * Γ r) := by
      refine hinj _ hru _ (hρU hrw.1) ?_
      rw [map_mul, map_inv, hφρ _ (hΓV t ht), hφρ _ (hΓV r hrI), hφρ _ hrw.1]
    have hRt : R (ψH ((Γ t)⁻¹ * Γ t)) = ψG ((ρ (Γ t))⁻¹ * ρ (Γ t)) := by
      rw [inv_mul_cancel, inv_mul_cancel, hR1]
    change (r - t)⁻¹ • (R (ψH ((Γ t)⁻¹ * Γ r)) - R (ψH ((Γ t)⁻¹ * Γ t))) =
      (r - t)⁻¹ • (ψG ((ρ (Γ t))⁻¹ * ρ (Γ r)) - ψG ((ρ (Γ t))⁻¹ * ρ (Γ t)))
    rw [hRt, heq]
    change (r - t)⁻¹ • (ψG (ρ (ψH.symm (ψH ((Γ t)⁻¹ * Γ r)))) - _) = _
    rw [ψH.left_inv hrw.2]
  -- one-parameter groups of `G`
  have hPG : ∀ x : E, ∃ P : ℝ → G, IsEvol E (fun _ ↦ x) P := by
    intro x
    have ht : Tendsto (fun n : ℕ ↦ (1 / ((n : ℝ) + 1)) • x) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const x
      rwa [zero_smul] at this
    obtain ⟨n, hn⟩ := (ht.eventually (hWGo.mem_nhds hWG0)).exists
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    set y := (1 / ((n : ℝ) + 1)) • x
    have hy : ContinuousMap.const I y ∈ valIn WG := fun _ ↦ hn
    obtain ⟨Γ, hΓ⟩ := hH.semiregular (compLeftCLM Lφ (ContinuousMap.const I y))
    have hl := hlift _ hy Γ hΓ
    rw [extendCurve_const] at hl
    have hc := hl.oneParam.comp_mul ((n : ℝ) + 1)
    rw [smul_smul, mul_one_div_cancel hn1, one_smul] at hc
    exact ⟨_, hc⟩
  have hsemi : IsC0Semiregular E G := isC0Semiregular_of_local (hWGo.mem_nhds hWG0)
    fun ξ hξ ↦ by
      obtain ⟨Γ, hΓ⟩ := hH.semiregular (compLeftCLM Lφ ξ)
      obtain ⟨Γ', hΓ', -⟩ := (hlift ξ hξ Γ hΓ).exists_isEvol hPG
      exact ⟨Γ', hΓ'⟩
  -- smoothness: `evol_G = ρ ∘ evol_H ∘ L(φ)_*` near `0`
  have hVo : IsOpen (valIn WG) := isOpen_valIn hWGo
  have heq : ∀ ξ ∈ valIn WG, evol E G ξ = ρ (evol F H (compLeftCLM Lφ ξ)) := by
    intro ξ hξ
    obtain ⟨Γ, hΓ⟩ := hH.semiregular (compLeftCLM Lφ ξ)
    rw [evol_eq_of_isEvolOn hPG (hlift ξ hξ Γ hΓ), evol_eq hΓ]
  have hmaps : MapsTo (fun ξ ↦ evol F H (compLeftCLM Lφ ξ)) (valIn WG) V := by
    intro ξ hξ
    obtain ⟨Γ, hΓ⟩ := hH.semiregular (compLeftCLM Lφ ξ)
    change evol F H (compLeftCLM Lφ ξ) ∈ V
    rw [evol_eq hΓ]
    exact hstay ξ hξ Γ hΓ 1 ⟨zero_le_one, le_rfl⟩
  refine isC0Regular_of_local' hsemi fun k ↦ ⟨WG, hWGo, hWG0, ?_⟩
  have hA : ContMDiffMBOn (E := C(I, E)) (F := F) k
      (fun ξ ↦ evol F H (compLeftCLM Lφ ξ)) (valIn WG) :=
    ContMDiffMBOn.mono' ((hH.smooth.comp fun k ↦ (contMDiffMBOn_iff_contDiffMBOn isOpen_univ).2
      ((compLeftCLM Lφ).contDiffMBOn k univ)) k) (subset_univ _)
  exact ContMDiffMBOn.congr' hVo ((hρ k).comp hVo hV hA hmaps) heq

end LocallyConvex.LieGroups.MBLieGroup

