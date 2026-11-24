/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Diffeomorphism.Flow
public import LocallyConvexLieGroups.LieGroup.Quotient
public import LocallyConvexManifolds.MappingSpace.ExponentialLaw

/-!
# Smoothness of the time-one map of a flow

For `ξ` with values in the common `0`-neighborhood `N₀` of `Γ_id`, the time-one map
`η_ξ(y) = c_y(1)` of the flow of `-ξ` is smooth on `K` (`Diffeo.smoothMBM_flowOne`): near a point,
it is `φ⁻¹ ∘ S ∘ φ` for the solution map `S` of the equation in the chart `φ` of some local data.
As a function of `(ξ, y)` it is `C^{k,ℓ}` for all `k, ℓ` (`Diffeo.contMDiffMB₂_flowOne`), since the
solution is smooth in `(ξ, z)`. By the exponential law for `C^∞(K, K)` ([GN26, Theorem 4.2.2(a)],
lc-manifolds), `ξ ↦ η_ξ` is smooth into `C^∞(K, K)` (`Diffeo.smooth_flowMap`).

The parameter space is an open subset `U` of `C([0, 1], Γ_id)`, as a manifold
(`TopologicalSpace.Opens`), which the exponential law requires.
-/

@[expose] public section

open Set Filter Function Metric TopologicalSpace
open scoped Topology NNReal unitInterval
open LocallyConvex.Analysis LocallyConvex.Manifolds
open LocallyConvex.LieGroups.MBLieGroup (extendCurve valIn shiftField)

noncomputable section

namespace LocallyConvex.LieGroups

/-! ### Charts of open subsets of a vector space -/

section OpensCharts

variable {E : Type*} [TopologicalSpace E] (U : Opens E)

theorem opens_chartAt_apply (ζ a : U) : chartAt E ζ a = a.1 := rfl

theorem opens_chartAt_source (ζ : U) : (chartAt E ζ).source = univ := by
  rw [Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
  rfl

theorem opens_mem_chartAt_target (ζ : U) {a : E} : a ∈ (chartAt E ζ).target ↔ a ∈ U := by
  constructor
  · intro ha
    have h := (chartAt E ζ.1).subtypeRestr_symm_apply (U := U) ⟨ζ⟩ ha
    have h2 : ((chartAt E ζ).symm a).1 = a := by
      rw [← (show (chartAt E ζ.1).symm a = a by simp [chartAt_self_eq])]; exact h
    rw [← h2]
    exact ((chartAt E ζ).symm a).2
  · intro ha
    have hs : (⟨a, ha⟩ : U) ∈ (chartAt E ζ).source := by rw [opens_chartAt_source]; trivial
    exact (chartAt E ζ).map_source hs

theorem opens_chartAt_symm_apply (ζ : U) {a : E} (ha : a ∈ U) : ((chartAt E ζ).symm a).1 = a := by
  have h := (chartAt E ζ.1).subtypeRestr_symm_apply (U := U) ⟨ζ⟩
    ((opens_mem_chartAt_target U ζ).2 ha)
  rw [← (show (chartAt E ζ.1).symm a = a by simp [chartAt_self_eq])]; exact h

end OpensCharts

namespace Diffeo

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {K : Type} [TopologicalSpace K] [ChartedSpace H K] [MBManifold H K] [CompactSpace K] [T2Space K]
  (A : LocalAddition H K)

/-! ### The time-one map in charts -/

theorem flowCurve_one_eq_local {x : K} (D : LocalData A x) {ξ : C(I, DiffeoModel A)}
    (hξ₀ : ξ ∈ valIn (N₀ A)) (hξ : ξ ∈ valIn D.N) {y : K} (hy : y ∈ (chartAt H x).source)
    (hyr : chartAt H x y ∈ ball (chartAt H x x) D.r) :
    flowCurve A ξ y 1 = (chartAt H x).symm (ParamODE.sol D.data (ξ, chartAt H x y) 1) := by
  rw [flowCurve_eq_local A D hξ₀ hξ hy hyr ⟨zero_le_one, le_rfl⟩, MBLieGroup.extendCurve_apply,
    projIcc_right]
  rfl

/-- The solution at time one is smooth in `(ξ, z)`. -/
theorem smoothMBOn_solOne {x : K} (D : LocalData A x) :
    SmoothMBOn (fun q : C(I, DiffeoModel A) × H ↦ ParamODE.sol D.data q 1)
      (ParamODE.par D.N (chartAt H x x) D.r) := fun k ↦
  ContDiffMBOn.comp (ParamODE.isOpen_par D.isOpen) isOpen_univ
    ((ContinuousMap.evalCLM ℝ (1 : I) : C(I, H) →L[ℝ] H).contDiffMBOn k univ)
    (ParamODE.smoothMBOn_sol D.data k) (mapsTo_univ _ _)

theorem solOne_mem_target {x : K} (D : LocalData A x) {q : C(I, DiffeoModel A) × H}
    (hq : q ∈ ParamODE.par D.N (chartAt H x x) D.r) :
    ParamODE.sol D.data q 1 ∈ (chartAt H x).target :=
  D.ball_sub (ParamODE.sol_mem_ball D.data hq 1)

/-- **The time-one map is smooth on `K`.** -/
theorem smoothMBM_flowOne {ξ : C(I, DiffeoModel A)} (hξ : ξ ∈ valIn (N₀ A)) :
    SmoothMBM H H fun y ↦ flowCurve A ξ y 1 := by
  intro k
  refine ContMDiffMBOn.of_local isOpen_univ fun y₀ _ ↦ ?_
  set x := ctr A y₀
  set D := ld A x
  set φ := chartAt H x
  have hξD : ξ ∈ valIn D.N := valIn_ld A hξ (ctr_mem A y₀)
  refine ⟨startSet A x, isOpen_startSet A x, mem_startSet_ctr A y₀, ?_⟩
  have hS : ContMDiffMBOn (E := H) (F := H) k (fun z ↦ ParamODE.sol D.data (ξ, z) 1)
      (ball (φ x) D.r) := by
    refine (contMDiffMBOn_iff_contDiffMBOn isOpen_ball).2 ?_
    exact ContDiffMBOn.comp (g := fun q ↦ ParamODE.sol D.data q 1)
      (f := fun z : H ↦ (ξ, z)) isOpen_ball (ParamODE.isOpen_par D.isOpen)
      (smoothMBOn_solOne A D k) ((contDiffMBOn_const k ξ _).prodMk isOpen_ball
        (smoothMBOn_id _ k)) fun z hz ↦ ⟨hξD, hz⟩
  have hφ : ContMDiffMBOn (E := H) (F := H) k φ (startSet A x) :=
    contMDiffMBOn_mono (contMDiffMBOn_chart (chart_mem_atlas H x)) inter_subset_left
  have h1 := ContMDiffMBOn.comp (isOpen_startSet A x) isOpen_ball hS hφ fun y hy ↦ hy.2
  have h2 := ContMDiffMBOn.comp (isOpen_startSet A x) φ.open_target
    (contMDiffMBOn_chart_symm (k := k) (chart_mem_atlas H x)) h1
    fun y hy ↦ solOne_mem_target A D ⟨hξD, hy.2⟩
  exact ContMDiffMBOn.congr' (isOpen_startSet A x) h2 fun y hy ↦
    flowCurve_one_eq_local A D hξ hξD hy.1 hy.2

/-- **The time-one map, as a smooth map.** -/
def flowOne {ξ : C(I, DiffeoModel A)} (hξ : ξ ∈ valIn (N₀ A)) : SmoothMap H H K K :=
  ⟨fun y ↦ flowCurve A ξ y 1, smoothMBM_flowOne A hξ⟩

/-! ### Smoothness in `(ξ, y)` -/

set_option maxHeartbeats 1000000 in
-- the goal is an unfolded `ContMDiffMB₂`, with large local representatives
/-- **The time-one map is `C^{k,ℓ}` in `(ξ, y)`**, on an open set of curves with values in
`N₀`. -/
theorem contMDiffMB₂_flowOne (U : Opens C(I, DiffeoModel A)) (hU : (U : Set _) ⊆ valIn (N₀ A))
    (k ℓ : ℕ) :
    ContMDiffMB₂ H H (VaryingAtlas.ofChartedSpace C(I, DiffeoModel A) U) k ℓ
      (fun p : U × K ↦ flowCurve A p.1.1 p.2 1) := by
  intro ζ y₀
  set x := ctr A y₀
  set D := ld A x
  set φ := chartAt H x
  set P := ParamODE.par D.N (φ x) D.r
  set G : C(I, DiffeoModel A) × H → K := fun q ↦ φ.symm (ParamODE.sol D.data q 1)
  have hζD : ζ.1 ∈ valIn D.N := valIn_ld A (hU ζ.2) (ctr_mem A y₀)
  have hy₀ := mem_startSet_ctr A y₀
  have hP : (ζ.1, φ y₀) ∈ P := ⟨hζD, hy₀.2⟩
  have hPo : IsOpen P := ParamODE.isOpen_par D.isOpen
  have hGc : ContinuousOn G P :=
    φ.continuousOn_symm.comp (smoothMBOn_solOne A D 0).continuousOn
      fun q hq ↦ solOne_mem_target A D hq
  set q₀ := flowCurve A ζ.1 y₀ 1
  have hGq : G (ζ.1, φ y₀) = q₀ :=
    (flowCurve_one_eq_local A D (hU ζ.2) hζD hy₀.1 hy₀.2).symm
  set c := chartAt H q₀
  have hmem : G ⁻¹' c.source ∩ P ∈ 𝓝 (ζ.1, φ y₀) :=
    inter_mem ((hGc.continuousAt (hPo.mem_nhds hP)).preimage_mem_nhds
      (c.open_source.mem_nhds (by rw [hGq]; exact mem_chart_source H q₀))) (hPo.mem_nhds hP)
  obtain ⟨U₁, V₁, hU₁, hζU₁, hV₁, hyV₁, hUV⟩ := mem_nhds_prod_iff'.1 hmem
  set U₂ := U₁ ∩ (U : Set C(I, DiffeoModel A))
  set V₂ := V₁ ∩ ball (φ x) D.r
  have hU₂ : IsOpen U₂ := hU₁.inter U.isOpen
  have hV₂ : IsOpen V₂ := hV₁.inter isOpen_ball
  have hbox : ∀ a ∈ U₂, ∀ b ∈ V₂, G (a, b) ∈ c.source ∧ (a, b) ∈ P := fun a ha b hb ↦
    hUV ⟨ha.1, hb.1⟩
  have hrep : ∀ a ∈ U₂, ∀ b ∈ V₂,
      flowCurve A a (φ.symm b) 1 = G (a, b) := fun a ha b hb ↦ by
    have hbt : b ∈ φ.target := D.ball_sub (ball_subset_ball (by linarith [D.data.pos]) hb.2)
    have h := flowCurve_one_eq_local A D (hU ha.2) (hbox a ha b hb).2.1 (φ.map_target hbt)
      (by rw [φ.right_inv hbt]; exact hb.2)
    rwa [φ.right_inv hbt] at h
  set B := VaryingAtlas.ofChartedSpace C(I, DiffeoModel A) U
  set i : B.ι := ⟨chartAt C(I, DiffeoModel A) ζ, chart_mem_atlas _ ζ⟩
  have hBi : B.chart i = chartAt C(I, DiffeoModel A) ζ := rfl
  have hsymm : ∀ a ∈ U₂, ((B.chart i).symm a).1 = a := fun a ha ↦ by
    rw [hBi]; exact opens_chartAt_symm_apply U ζ ha.2
  have hf : ∀ a ∈ U₂, ∀ b ∈ V₂, flowCurve A ((B.chart i).symm a).1 (φ.symm b) 1 = G (a, b) :=
    fun a ha b hb ↦ by rw [hsymm a ha]; exact hrep a ha b hb
  -- the local representative `(a, b) ↦ c(G(a, b))` is smooth
  have hT : ContDiffMBOn (k + ℓ) (c ∘ φ.symm) (φ.target ∩ φ.symm ⁻¹' c.source) :=
    smoothMBOn_transition (chart_mem_atlas H x) (chart_mem_atlas H q₀) _
  have hcG : ContDiffMBOn (k + ℓ) (fun q ↦ c (G q)) (U₂ ×ˢ V₂) :=
    ContDiffMBOn.comp (g := c ∘ φ.symm) (f := fun q ↦ ParamODE.sol D.data q 1)
      (hU₂.prod hV₂) (φ.isOpen_inter_preimage_symm c.open_source) hT
      ((smoothMBOn_solOne A D (k + ℓ)).mono fun q hq ↦ (hbox q.1 hq.1 q.2 hq.2).2)
      fun q hq ↦ ⟨solOne_mem_target A D (hbox q.1 hq.1 q.2 hq.2).2,
        (hbox q.1 hq.1 q.2 hq.2).1⟩
  refine ⟨i, φ, chart_mem_atlas H x, c, chart_mem_atlas H q₀, U₂, V₂, ?_, hy₀.1, ?_,
    ⟨hyV₁, hy₀.2⟩, ⟨hU₂, hV₂, ?_, ?_, ?_⟩, ?_⟩
  · rw [hBi, opens_chartAt_source]; trivial
  · change ζ.1 ∈ U₂; exact ⟨hζU₁, ζ.2⟩
  · intro a ha; rw [hBi]; exact (opens_mem_chartAt_target U ζ).2 ha.2
  · intro b hb; exact D.ball_sub (ball_subset_ball (by linarith [D.data.pos]) hb.2)
  · intro a ha b hb
    change flowCurve A ((B.chart i).symm a).1 (φ.symm b) 1 ∈ c.source
    rw [hf a ha b hb]; exact (hbox a ha b hb).1
  · refine (hcG.contDiffMBOn₂ hU₂ hV₂).congr hU₂ hV₂ fun q hq ↦ ?_
    change c (G q) = c (flowCurve A ((B.chart i).symm q.1).1 (φ.symm q.2) 1)
    rw [hf q.1 hq.1 q.2 hq.2]
    rfl

/-- **The time-one map is smooth into `C^∞(K, K)`**, by the exponential law
([GN26, Theorem 4.2.2(a)]). -/
theorem smooth_flowOne (U : Opens C(I, DiffeoModel A)) (hU : (U : Set _) ⊆ valIn (N₀ A)) :
    (VaryingAtlas.ofChartedSpace C(I, DiffeoModel A) U).Smooth (A.mappingAtlasSm (H := H) (M := K))
      (fun ζ : U ↦ flowOne A (hU ζ.2)) := fun k ↦
  A.contMDiffOn_mappingAtlasSm_iff.2 fun ℓ ↦ contMDiffMB₂_flowOne A U hU k ℓ

end Diffeo

end LocallyConvex.LieGroups
