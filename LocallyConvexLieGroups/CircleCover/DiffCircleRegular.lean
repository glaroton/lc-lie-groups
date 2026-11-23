/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.CircleCover.Covering
public import LocallyConvexLieGroups.CircleCover.Regular
public import LocallyConvexLieGroups.Regular.Ck
public import LocallyConvexLieGroups.Regular.Hom
public import LocallyConvexLieGroups.Regular.OpenSubgroup

/-!
# `Diff(S¹)` and `Diff⁺(S¹)` are regular

The covering morphism `q : \widetilde{Diff}⁺(S¹) → Diff(S¹)` has a smooth local right inverse in
the chart `φ` of `Diff(S¹)` at the identity: for `γ = φ⁻¹(σ)`, `⟪p, γ(p)⟫ > 0` for every
`p ∈ S¹`, so the angle from `p` to `γ(p)` is the principal one, and
`ρ(σ)(t) = arg(γ(e^{2πit}) e^{-2πit})/2π` is a periodic function with `q(ρ(σ)) = γ`, smooth
in `σ`. Then `L(q)` splits, and `C⁰`-regularity passes from the universal cover
(`CircleCover.isC0Regular`) to `Diff(S¹)` (`MBLieGroup.IsC0Regular.of_hom_of_rightInverse`) and
to its identity component `Diff⁺(S¹)`. Both are then regular.

## Main definitions

* `CircleCover.rho`: the local right inverse `ρ` of the covering morphism.

## Main results

* `CircleCover.coverHom_rho`: **`q(ρ(σ)) = φ⁻¹(σ)`**.
* `CircleCover.smoothMBOn_rho`: `ρ` is smooth on the chart range.
* `CircleCover.isC0Regular_diffCircle`, `CircleCover.isC0Regular_diffPlusCircle`:
  **`Diff(S¹)` and `Diff⁺(S¹)` are `C⁰`-regular.**
* `CircleCover.isRegular_diffCircle`, `CircleCover.isRegular_diffPlusCircle`: they are regular.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology ContDiff Real
open LocallyConvex.Analysis LocallyConvex.Manifolds CInfPer DiffCircle

noncomputable section

namespace LocallyConvex.LieGroups.CircleCover

/-- In the chart at the identity, `⟪p, γ(p)⟫ > 0`. -/
theorem inner_gT_pos (s : TO) (p : UnitCircle) : 0 < inner ℝ (p.1 : R2) ((gT s p).1 : R2) := by
  have h := φ1.map_target s.2
  rw [VaryingAtlas.restrict_chart_source] at h
  exact h p

theorem mem_relDom_gT (s : TO) (p : UnitCircle) : (((gT s p).1 : R2), (p.1 : R2)) ∈ relDom := by
  refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
  rw [re_J_mul_conj, real_inner_comm]
  exact inner_gT_pos s p

open scoped Classical in
/-- `F(σ, θ) = relAng(γ_σ(e^{2πiθ}), e^{2πiθ})`, for `σ` in the chart at the identity. -/
def Frho (p : Mod × ℝ) : ℝ :=
  if h : p.1 ∈ φ1.target then relAng (gT ⟨p.1, h⟩ (circ p.2)).1 (circ p.2).1 else 0

theorem smoothMBOn_Frho : SmoothMBOn Frho (φ1.target ×ˢ univ) := by
  refine smoothMBOn_of_opens_prod TO fun k ↦ ?_
  have hemb := isEmbeddedSubmanifold_sphere norm_circleBase
  let := hemb.chartedSpace
  have := hemb.mbManifold
  have hΨ3 : ContMDiffMB (ModelProd Mod ℝ) (ModelProd Mod CircleModel) k
      (fun x : TO × ℝ ↦ (x.1, circ x.2)) :=
    ContMDiffMBOn.prodMk isOpen_univ (smoothMBM_fst k) ((smoothMBM_circ.comp smoothMBM_snd) k)
  have hev : ContMDiffMB (ModelProd Mod ℝ) CircleModel k
      (fun x : TO × ℝ ↦ gT x.1 (circ x.2)) :=
    ContMDiffMBOn.comp (g := fun x : TO × UnitCircle ↦ gT x.1 x.2)
      (f := fun x : TO × ℝ ↦ (x.1, circ x.2)) isOpen_univ isOpen_univ
      (smoothMBM_evalChart k) hΨ3 (mapsTo_univ _ _)
  have hv1 : ContMDiffMB (ModelProd Mod ℝ) R2 k
      (fun x : TO × ℝ ↦ ((gT x.1 (circ x.2)).1 : R2)) :=
    ContMDiffMBOn.comp (g := fun z : UnitCircle ↦ (z.1 : R2))
      (f := fun x : TO × ℝ ↦ gT x.1 (circ x.2)) isOpen_univ isOpen_univ
      (hemb.smoothMBM_val k) hev (mapsTo_univ _ _)
  have hc2 : ContMDiffMB (ModelProd Mod ℝ) CircleModel k (fun x : TO × ℝ ↦ circ x.2) :=
    (smoothMBM_circ.comp smoothMBM_snd) k
  have hv2 : ContMDiffMB (ModelProd Mod ℝ) R2 k (fun x : TO × ℝ ↦ ((circ x.2).1 : R2)) :=
    ContMDiffMBOn.comp (g := fun z : UnitCircle ↦ (z.1 : R2))
      (f := fun x : TO × ℝ ↦ circ x.2) isOpen_univ isOpen_univ
      (hemb.smoothMBM_val k) hc2 (mapsTo_univ _ _)
  have hΨ4 : ContMDiffMB (ModelProd Mod ℝ) (ModelProd R2 R2) k
      (fun x : TO × ℝ ↦ (((gT x.1 (circ x.2)).1 : R2), ((circ x.2).1 : R2))) :=
    ContMDiffMBOn.prodMk isOpen_univ hv1 hv2
  have h := ContMDiffMBOn.comp (g := fun p : R2 × R2 ↦ relAng p.1 p.2)
    (f := fun x : TO × ℝ ↦ (((gT x.1 (circ x.2)).1 : R2), ((circ x.2).1 : R2))) isOpen_univ
    isOpen_relDom (contMDiffMBOn_relAng k) hΨ4 fun x _ ↦ mem_relDom_gT x.1 (circ x.2)
  refine ContMDiffMBOn.congr' isOpen_univ h fun x _ ↦ ?_
  change Frho ((x.1 : Mod), x.2) = relAng (gT x.1 (circ x.2)).1 (circ x.2).1
  simp only [Frho, show (x.1 : Mod) ∈ φ1.target from x.1.2, ↓reduceDIte]

theorem contDiff_Frho {σ : Mod} (hσ : σ ∈ φ1.target) : ContDiff ℝ ∞ fun t ↦ Frho (σ, t) := by
  have h : SmoothMBOn (fun t : ℝ ↦ Frho (σ, t)) univ := fun k ↦
    ContDiffMBOn.comp (g := Frho) (f := fun t : ℝ ↦ (σ, t)) isOpen_univ
      (φ1.open_target.prod isOpen_univ) (smoothMBOn_Frho k)
      ((contDiffMBOn_const k σ _).prodMk isOpen_univ (smoothMBOn_id _ k))
      fun t _ ↦ ⟨hσ, mem_univ _⟩
  exact contDiffOn_univ.1 ((smoothMBOn_iff_contDiffOn isOpen_univ).1 h)

open scoped Classical in
/-- **The local right inverse** `ρ(σ)(θ) = relAng(γ_σ(e^{2πiθ}), e^{2πiθ})`. -/
def rho (σ : Mod) : CInfPer :=
  if hσ : σ ∈ φ1.target then
    CInfPer.mk (fun t ↦ Frho (σ, t)) (contDiff_Frho hσ) fun t ↦ by
      simp only [Frho, hσ, ↓reduceDIte, circ_add_one]
  else 0

theorem rho_apply {σ : Mod} (hσ : σ ∈ φ1.target) (t : ℝ) : rho σ t = Frho (σ, t) := by
  simp only [rho, hσ, ↓reduceDIte]
  rfl

theorem smoothMBOn_rho : SmoothMBOn rho φ1.target :=
  smoothMBOn_of_uncurry φ1.open_target smoothMBOn_Frho fun _ hσ t ↦ rho_apply hσ t

/-- **`act(ρ(σ), ·) = γ_σ`.** -/
theorem coverHom_rho {σ : Mod} (hσ : σ ∈ φ1.target) (hd : rho σ ∈ domain) :
    (show diffeos CircleModel UnitCircle from coverHom ⟨rho σ, hd⟩) = φ1.symm σ := by
  refine Subtype.ext (SmoothMap.ext fun p ↦ Subtype.ext ?_)
  change rotU (rho σ, p.1) = ((gT ⟨σ, hσ⟩ p).1 : R2)
  have hu : uz (rho σ) p.1 = relAng (gT ⟨σ, hσ⟩ p).1 p.1 := by
    rw [uz, rho_apply hσ]
    simp only [Frho, hσ, ↓reduceDIte, circ_ang]
  rw [rotU, hu]
  exact rotU_relAng (norm_circle _) (norm_circle p)

theorem relAng_self {z : R2} (hz : ‖z‖ = 1) : relAng z z = 0 := by
  rw [relAng, Complex.mul_conj, Complex.normSq_eq_norm_sq, LinearIsometryEquiv.norm_map, hz]
  simp [ang]

theorem one_mem_target : φ1 1 ∈ φ1.target := φ1.map_source (DA.mem_chartAt_source 1)

theorem rho_one : rho (φ1 1) = 0 := by
  ext t
  rw [rho_apply one_mem_target]
  simp only [Frho, one_mem_target, ↓reduceDIte]
  have h : gT ⟨φ1 1, one_mem_target⟩ = (1 : diffeos CircleModel UnitCircle).1 := by
    change (φ1.symm (φ1 1)).1 = _
    rw [φ1.left_inv (DA.mem_chartAt_source 1)]
  rw [h]
  exact relAng_self (norm_circle _)

theorem chartAt_diffCircle_apply (g : DiffCircle) :
    chartAt (DiffeoModel UnitCircle.localAddition) (1 : DiffCircle) g = φ1 g := by
  change φ1 ((1 : DiffCircle)⁻¹ * g) = φ1 g
  rw [inv_one, one_mul]

theorem chartAt_coverGroup_symm {v : CInfPer} (hv : v ∈ domain) :
    (chartAt CInfPer (1 : CoverGroup)).symm v = ⟨v, hv⟩ := by
  have hs : (⟨v, hv⟩ : CoverGroup) ∈ (chartAt CInfPer (1 : CoverGroup)).source :=
    mem_chart_source CInfPer (⟨v, hv⟩ : CoverGroup)
  exact (chartAt CInfPer (1 : CoverGroup)).left_inv hs

/-- **`Diff(S¹)` is `C⁰`-regular**: the covering morphism `\widetilde{Diff}⁺(S¹) → Diff(S¹)` has
the smooth local right inverse `rho` in the chart at the identity. -/
theorem isC0Regular_diffCircle :
    MBLieGroup.IsC0Regular (DiffeoModel UnitCircle.localAddition) DiffCircle := by
  have hc : ContinuousOn rho φ1.target := (smoothMBOn_rho 0).continuousOn
  set W := φ1.target ∩ rho ⁻¹' domain with hWdef
  have hW : IsOpen W := hc.isOpen_inter_preimage φ1.open_target isOpen_domain
  have hcov : ∀ y ∈ W, (coverHom ((chartAt CInfPer (1 : CoverGroup)).symm (rho y)) :
      diffeos CircleModel UnitCircle) = φ1.symm y := fun y hy ↦ by
    rw [chartAt_coverGroup_symm hy.2]
    exact coverHom_rho hy.1 hy.2
  have h1W : chartAt (DiffeoModel UnitCircle.localAddition) (1 : DiffCircle) 1 ∈ W := by
    rw [chartAt_diffCircle_apply]
    refine ⟨one_mem_target, ?_⟩
    change rho (φ1 1) ∈ domain
    rw [rho_one]
    exact zero_mem
  refine isC0Regular.of_hom_of_rightInverse isHom_coverHom hW h1W
    ((smoothMBOn_rho 1).mono inter_subset_left) ?_ ?_ ?_
  · rw [chartAt_diffCircle_apply]
    exact rho_one
  · intro y hy
    refine ⟨mem_chart_target CInfPer (⟨rho y, hy.2⟩ : CoverGroup), mem_univ _, ?_⟩
    change coverHom ((chartAt CInfPer (1 : CoverGroup)).symm (rho y)) ∈
      (chartAt (DiffeoModel UnitCircle.localAddition) (1 : DiffCircle)).source
    refine ⟨mem_univ _, ?_⟩
    change (1 : DiffCircle)⁻¹ * coverHom ((chartAt CInfPer (1 : CoverGroup)).symm (rho y)) ∈
      φ1.source
    rw [inv_one, one_mul]
    rw [hcov y hy]
    exact φ1.map_target hy.1
  · intro y hy
    change chartAt (DiffeoModel UnitCircle.localAddition) (1 : DiffCircle)
      (coverHom ((chartAt CInfPer (1 : CoverGroup)).symm (rho y))) = y
    rw [chartAt_diffCircle_apply]
    change φ1 (coverHom ((chartAt CInfPer (1 : CoverGroup)).symm (rho y)) :
      diffeos CircleModel UnitCircle) = y
    rw [hcov y hy]
    exact φ1.right_inv hy.1

/-- **`Diff⁺(S¹)` is `C⁰`-regular.** -/
theorem isC0Regular_diffPlusCircle :
    MBLieGroup.IsC0Regular (DiffeoModel UnitCircle.localAddition) DiffPlusCircle :=
  (MBLieGroup.isC0Regular_identityComponent_iff _ _).2 isC0Regular_diffCircle

/-- **`Diff(S¹)` is regular.** -/
theorem isRegular_diffCircle :
    MBLieGroup.IsRegular (DiffeoModel UnitCircle.localAddition) DiffCircle :=
  isC0Regular_diffCircle.isRegular

/-- **`Diff⁺(S¹)` is regular.** -/
theorem isRegular_diffPlusCircle :
    MBLieGroup.IsRegular (DiffeoModel UnitCircle.localAddition) DiffPlusCircle :=
  isC0Regular_diffPlusCircle.isRegular

end LocallyConvex.LieGroups.CircleCover
