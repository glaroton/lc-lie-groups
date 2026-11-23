/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.LieAlgebra.Adjoint

/-!
# The adjoint action is smooth

The adjoint action `σ_Ad : G × L(G) → L(G)`, `(g, y) ↦ Ad(g) y`, is smooth ([GN26, after
Definition 5.2.4]).

## Main results

* `MBLieGroup.smoothMBM_conjMap`: the conjugation `(g, k) ↦ g k g⁻¹` is smooth.
* `MBLieGroup.Ad_eq_dMB_conjRep`: in the chart `φ` at the identity, `Ad(φ⁻¹(z)) y = ∂_w K(z, w) y`
  at `w = φ(1)`, where `K` is the local representative of the conjugation.
* `MBLieGroup.smoothMBM_AdAction`: **the adjoint action is smooth**.

## Proof

Near the identity, `(z, y) ↦ ∂_w K(z, φ(1)) y` is smooth because `K` is. At an arbitrary point
`g₀`, `Ad(g) y = Ad(g₀) (Ad(g₀⁻¹ g) y)`, where `Ad(g₀)` is continuous linear and `g ↦ φ(g₀⁻¹ g)` is
the local representative of a left translation.

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

/-- The conjugation `(g, k) ↦ g k g⁻¹`. -/
def conjMap (p : G × G) : G := p.1 * p.2 * p.1⁻¹

theorem smoothMBM_conjMap : SmoothMBM (ModelProd E E) E (conjMap (G := G)) := by
  have h1 : SmoothMBM (ModelProd E E) E (fun p : G × G ↦ p.1 * p.2) := smoothMBM_mul
  have h2 : SmoothMBM (ModelProd E E) E (fun p : G × G ↦ p.1⁻¹) :=
    (smoothMBM_inv (E := E) (G := G)).comp smoothMBM_fst
  exact (smoothMBM_mul (E := E) (G := G)).comp (fun k ↦ ContMDiffMBOn.prodMk
    (f := fun p : G × G ↦ p.1 * p.2) (g := fun p : G × G ↦ p.1⁻¹) isOpen_univ (h1 k) (h2 k))

variable (E G) in
/-- The local representative `K(z, w) = φ(φ⁻¹(z) φ⁻¹(w) φ⁻¹(z)⁻¹)` of the conjugation. -/
def conjRep (q : E × E) : E :=
  chartAt E (1 : G) (conjMap ((chartAt E (1 : G)).symm q.1, (chartAt E (1 : G)).symm q.2))

variable (E G) in
/-- The domain of `conjRep`. -/
def conjRepDom : Set (E × E) :=
  chartDomain (conjMap (G := G)) univ (chartAt (ModelProd E E) ((1 : G), (1 : G)))
    (chartAt E (1 : G))

omit [TopologicalSpace G] in
theorem conjMap_one : conjMap ((1 : G), (1 : G)) = 1 := by simp [conjMap]

theorem smoothMBOn_conjRep : SmoothMBOn (conjRep E G) (conjRepDom E G) := by
  intro k
  have h := (smoothMBM_conjMap (E := E) (G := G) k).2 ((1 : G), (1 : G)) (mem_univ _)
  rw [conjMap_one] at h
  exact h

theorem isOpen_conjRepDom : IsOpen (conjRepDom E G) :=
  isOpen_chartDomain isOpen_univ (smoothMBM_conjMap (E := E) (G := G) 0).continuousOn _ _

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [MBLieGroup E G] in
theorem one_mem_conjRepDom :
    (chartAt E (1 : G) 1, chartAt E (1 : G) 1) ∈ conjRepDom E G := by
  have h1 := mem_chart_source E (1 : G)
  refine ⟨⟨(chartAt E (1 : G)).map_source h1, (chartAt E (1 : G)).map_source h1⟩, mem_univ _, ?_⟩
  change conjMap ((chartAt E (1 : G)).symm (chartAt E (1 : G) 1),
    (chartAt E (1 : G)).symm (chartAt E (1 : G) 1)) ∈ (chartAt E (1 : G)).source
  rw [(chartAt E (1 : G)).left_inv h1, conjMap_one]
  exact h1

/-- **`Ad` in the chart at the identity**: `Ad(φ⁻¹(z)) y = ∂_w K(z, φ(1)) y`. -/
theorem Ad_eq_dMB_conjRep (z y : E) :
    LieAlg.toModel (Ad E ((chartAt E (1 : G)).symm z) (LieAlg.toModel.symm y)) =
      dMB (conjRep E G) ((z, chartAt E (1 : G) 1), ((0 : E), y)) := by
  rw [dMB_slice₂]
  rfl

/-- `F(z, y) = ∂_w K(z, φ(1)) y`, which is `Ad(φ⁻¹(z)) y`. -/
def AdRep (q : E × E) : E := dMB (conjRep E G) ((q.1, chartAt E (1 : G) 1), ((0 : E), q.2))

variable (E G) in
/-- The domain of smoothness of `AdRep`. -/
def AdRepDom : Set (E × E) := {q | (q.1, chartAt E (1 : G) 1) ∈ conjRepDom E G}

theorem isOpen_AdRepDom : IsOpen (AdRepDom E G) :=
  (isOpen_conjRepDom (E := E) (G := G)).preimage (by fun_prop)

theorem contDiffMBOn_AdRep (k : ℕ) : ContDiffMBOn k (AdRep (E := E) (G := G)) (AdRepDom E G) := by
  have hA : ContDiffMBOn k (fun q : E × E ↦ ((q.1, chartAt E (1 : G) 1), ((0 : E), q.2)))
      (AdRepDom E G) :=
    (((ContinuousLinearMap.fst ℝ E E).contDiffMBOn k _).prodMk isOpen_AdRepDom
      (contDiffMBOn_const k _ _)).prodMk isOpen_AdRepDom
      ((contDiffMBOn_const k (0 : E) _).prodMk isOpen_AdRepDom
        ((ContinuousLinearMap.snd ℝ E E).contDiffMBOn k _))
  exact ContDiffMBOn.comp (g := dMB (conjRep E G))
    (f := fun q : E × E ↦ ((q.1, chartAt E (1 : G) 1), ((0 : E), q.2))) isOpen_AdRepDom
    (isOpen_conjRepDom.prod isOpen_univ) (smoothMBOn_conjRep (k + 1)).2.2 hA
    fun _ hq ↦ ⟨hq, mem_univ _⟩

/-- The adjoint action, on the model space. -/
def AdAction (p : G × E) : E := LieAlg.toModel (Ad E p.1 (LieAlg.toModel.symm p.2))

/-- `Ad(g) y = Ad(g₀) F(φ(g₀⁻¹ g), y)`. -/
theorem AdAction_eq (g₀ g : G) (hg : g₀⁻¹ * g ∈ (chartAt E (1 : G)).source) (y : E) :
    AdAction (g, y) = AdCLM g₀ (AdRep (G := G) (chartAt E (1 : G) (g₀⁻¹ * g), y)) := by
  have h := Ad_eq_dMB_conjRep (E := E) (G := G) (chartAt E (1 : G) (g₀⁻¹ * g)) y
  rw [(chartAt E (1 : G)).left_inv hg] at h
  have h' : Ad E (g₀⁻¹ * g) (LieAlg.toModel.symm y) =
      LieAlg.toModel.symm (AdRep (G := G) (chartAt E (1 : G) (g₀⁻¹ * g), y)) := h
  change LieAlg.toModel (Ad E g (LieAlg.toModel.symm y)) =
    LieAlg.toModel (Ad E g₀
      (LieAlg.toModel.symm (AdRep (G := G) (chartAt E (1 : G) (g₀⁻¹ * g), y))))
  rw [← h', ← LieHom.comp_apply, ← Ad_mul, mul_inv_cancel_left]

theorem continuous_AdAction : Continuous (AdAction (E := E) (G := G)) := by
  have := isTopologicalGroup E G
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  obtain ⟨g₀, y₀⟩ := x
  have h1 := mem_chart_source E (1 : G)
  have hev : AdAction (E := E) (G := G) =ᶠ[𝓝 (g₀, y₀)]
      fun p : G × E ↦ AdCLM g₀ (AdRep (G := G) (chartAt E (1 : G) (g₀⁻¹ * p.1), p.2)) := by
    have hO : IsOpen {p : G × E | g₀⁻¹ * p.1 ∈ (chartAt E (1 : G)).source} :=
      (chartAt E (1 : G)).open_source.preimage (continuous_const.mul continuous_fst)
    filter_upwards [hO.mem_nhds (by simp)] with p hp
    exact AdAction_eq g₀ p.1 hp p.2
  refine ContinuousAt.congr ?_ hev.symm
  refine (AdCLM g₀).continuous.continuousAt.comp ?_
  have hmem : (chartAt E (1 : G) (g₀⁻¹ * g₀), y₀) ∈ AdRepDom E G := by
    change (chartAt E (1 : G) (g₀⁻¹ * g₀), chartAt E (1 : G) 1) ∈ conjRepDom E G
    rw [inv_mul_cancel]; exact one_mem_conjRepDom
  have hAd : ContinuousAt (AdRep (G := G))
      ((fun p : G × E ↦ (chartAt E (1 : G) (g₀⁻¹ * p.1), p.2)) (g₀, y₀)) :=
    (contDiffMBOn_AdRep 0).continuousOn.continuousAt (isOpen_AdRepDom.mem_nhds hmem)
  refine ContinuousAt.comp (g := AdRep (G := G))
    (f := fun p : G × E ↦ (chartAt E (1 : G) (g₀⁻¹ * p.1), p.2)) hAd ?_
  refine ContinuousAt.prodMk ?_ continuousAt_snd
  refine ContinuousAt.comp (f := fun p : G × E ↦ g₀⁻¹ * p.1) ?_ (by fun_prop)
  exact (chartAt E (1 : G)).continuousAt (by simp)

/-- **The adjoint action `(g, y) ↦ Ad(g) y` is smooth** ([GN26, after Definition 5.2.4]). -/
theorem smoothMBM_AdAction : SmoothMBM (ModelProd E E) E (AdAction (E := E) (G := G)) := by
  intro k
  have := isTopologicalGroup E G
  refine contMDiffMB_of_chartAt continuous_AdAction fun x ↦ ?_
  obtain ⟨g₀, y₀⟩ := x
  set ψ := chartAt E g₀
  set χ := chartAt E (1 : G)
  have h1 := mem_chart_source E (1 : G)
  -- the local representative of `g ↦ g₀⁻¹ g`
  have hT := (smoothMBM_mul_left (E := E) g₀⁻¹ k).2 g₀ (mem_univ _)
  simp only [inv_mul_cancel] at hT
  set T : E → E := χ ∘ (fun x : G ↦ g₀⁻¹ * x) ∘ ψ.symm
  set DT := chartDomain (fun x : G ↦ g₀⁻¹ * x) univ ψ χ
  have hDT : IsOpen DT :=
    isOpen_chartDomain isOpen_univ (smoothMBM_mul_left (E := E) g₀⁻¹ 0).continuousOn _ _
  set O : Set (E × E) := {q | q.1 ∈ DT ∧ (T q.1, q.2) ∈ AdRepDom E G}
  have hO : IsOpen O := by
    have hc : ContinuousOn (fun q : E × E ↦ (T q.1, q.2)) (Prod.fst ⁻¹' DT) :=
      (hT.continuousOn.comp continuousOn_fst fun _ h ↦ h).prodMk continuousOn_snd
    exact hc.isOpen_inter_preimage (hDT.preimage continuous_fst) isOpen_AdRepDom
  have hg₀ : ψ g₀ ∈ DT := ⟨ψ.map_source (mem_chart_source E g₀), mem_univ _, by
    change g₀⁻¹ * ψ.symm (ψ g₀) ∈ χ.source
    rw [ψ.left_inv (mem_chart_source E g₀), inv_mul_cancel]; exact h1⟩
  have hTg₀ : T (ψ g₀) = χ 1 := by
    change χ (g₀⁻¹ * ψ.symm (ψ g₀)) = χ 1
    rw [ψ.left_inv (mem_chart_source E g₀), inv_mul_cancel]
  refine ⟨O, hO, ⟨hg₀, ?_⟩, fun q hq ↦ ⟨⟨hq.1.1, mem_univ _⟩, mem_univ _, mem_univ _⟩, ?_⟩
  · change (T (ψ g₀), y₀) ∈ AdRepDom E G
    rw [hTg₀]; exact one_mem_conjRepDom
  -- on `O`, the representative is `Ad(g₀) ∘ F ∘ (T × id)`
  have hTq : ContDiffMBOn k (fun q : E × E ↦ (T q.1, q.2)) O :=
    ((ContDiffMBOn.comp (g := T) (f := Prod.fst) (hDT.preimage continuous_fst) hDT hT
      ((ContinuousLinearMap.fst ℝ E E).contDiffMBOn k _) fun _ h ↦ h).mono
      fun q (h : q ∈ O) ↦ h.1).prodMk hO ((ContinuousLinearMap.snd ℝ E E).contDiffMBOn k _)
  have hF : ContDiffMBOn k (AdRep (G := G) ∘ fun q : E × E ↦ (T q.1, q.2)) O :=
    ContDiffMBOn.comp hO isOpen_AdRepDom (contDiffMBOn_AdRep k) hTq fun _ h ↦ h.2
  have hS : ContDiffMBOn k (⇑(AdCLM g₀) ∘ (AdRep (G := G) ∘ fun q : E × E ↦ (T q.1, q.2))) O :=
    ContDiffMBOn.comp hO isOpen_univ ((AdCLM g₀).contDiffMBOn k univ) hF (mapsTo_univ _ _)
  refine ContDiffMBOn.congr_of_isOpen hO (fun q hq ↦ ?_) hS
  have hq1 : g₀⁻¹ * ψ.symm q.1 ∈ χ.source := hq.1.2.2
  change AdCLM g₀ (AdRep (χ (g₀⁻¹ * ψ.symm q.1), q.2)) = AdAction (ψ.symm q.1, q.2)
  exact (AdAction_eq g₀ (ψ.symm q.1) hq1 q.2).symm

end LocallyConvex.LieGroups.MBLieGroup
