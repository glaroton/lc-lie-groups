/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.LieGroup.Basic
public import LocallyConvexManifolds.Manifold.LocalDiffeo
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Quotients of Lie groups by discrete normal subgroups

Let `π : M → Q` be a continuous, open and surjective map from a manifold `M` onto a topological
space `Q`, injective near each point, such that any two points of a fiber are related by a smooth
map `τ : M → M` with `π ∘ τ = π` (a *deck transformation*). Then `Q` carries a manifold structure
for which `π` is a local diffeomorphism: the charts are `c_x ∘ (π|_U)⁻¹`, where `U` is
a neighbourhood of `x` on which `π` is injective and `c_x` is the chart of `M` at `x`. Near each
point, `(π|_U)⁻¹ ∘ π` is a deck transformation, so the transition maps are local
representatives of deck transformations in charts of `M` (`IsSmoothQuotientMap.chartedSpace`).
A map into `Q` that lifts to a smooth map into `M` is smooth
(`IsSmoothQuotientMap.contMDiffMBOn_of_lift`), and a map out of `Q` is smooth if its composition
with `π` is (`IsSmoothQuotientMap.contMDiffMB_of_comp`).

For a Lie group `G` and a discrete subgroup `Γ`, the quotient map `G → G/Γ` satisfies these
hypotheses, with the right translations by elements of `Γ` as deck transformations. If `Γ` is
normal, the group operations of `G/Γ` lift locally to those of `G`, and `G/Γ` is a Lie group
modeled on the same space as `G`, for which `G → G/Γ` is a morphism of Lie groups and a local
diffeomorphism ([GN26, Corollary 5.3.4], for the covering `G → G/Γ`).

## Main definitions

* `IsSmoothQuotientMap E π`: the hypotheses above.
* `IsSmoothQuotientMap.chartedSpace`: the charted space structure on `Q`.
* `MBLieGroup.instChartedSpaceQuotient`, `MBLieGroup.instMBLieGroupQuotient`: **`G/Γ` is a Lie
  group**, for `Γ` discrete (`DiscreteTopology Γ`) and normal.

## Main results

* `IsSmoothQuotientMap.mbManifold`: `Q` is a manifold.
* `IsSmoothQuotientMap.contMDiffMBOn_of_lift`: maps into `Q` that lift to smooth maps are smooth.
* `IsSmoothQuotientMap.contMDiffMBOn_sect_symm`: the local inverses of `π` are smooth.
* `IsSmoothQuotientMap.contMDiffMB_of_comp`, `MBLieGroup.smoothMBM_of_comp_mk`: a map out of `Q`
  is smooth if its composition with `π` is.
* `MBLieGroup.isSmoothQuotientMap_mk`: `G → G/Γ` satisfies the hypotheses, for `Γ` discrete.
* `MBLieGroup.isHom_mk`, `MBLieGroup.exists_smooth_local_inverse`: `G → G/Γ` is a morphism of Lie
  groups and a local diffeomorphism.
* `MBLieGroup.smoothMBM_symm_of_local`: a bijective morphism of Lie groups with a smooth local
  inverse near the identity is an isomorphism of Lie groups.

## Implementation notes

[GN26, Corollary 5.3.4] goes through the construction of Lie groups from local data
([GN26, Theorem 5.3.1]). Here the charts of `G/Γ` are written down directly, at every point,
and their compatibility comes from the deck transformations; the group structure is only used
at the end, to lift the multiplication and the inversion locally.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function
open scoped Topology
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups

universe u

section Quotient

variable (E : Type u) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  {Q : Type*} [TopologicalSpace Q]

/-- `π : M → Q` is a quotient map by smooth deck transformations: continuous, open, surjective,
locally injective, and any two points of a fiber are related by a smooth `τ` with `π ∘ τ = π`. -/
structure IsSmoothQuotientMap (π : M → Q) : Prop where
  continuous : Continuous π
  isOpenMap : IsOpenMap π
  surjective : Surjective π
  locInj : ∀ x, ∃ U, IsOpen U ∧ x ∈ U ∧ InjOn π U
  deck : ∀ x y, π x = π y → ∃ τ : M → M, SmoothMBM E E τ ∧ τ x = y ∧ ∀ z, π (τ z) = π z

variable {E}

section Helpers

variable {H F' : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H]
  [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  [AddCommGroup F'] [Module ℝ F'] [TopologicalSpace F']
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] {N : Type*} [TopologicalSpace N]
  [ChartedSpace F' N] {k : ℕ}

theorem contMDiffMBOn_mono {f : X → N} {U V : Set X}
    (hf : ContMDiffMBOn (E := H) (F := F') k f U) (hVU : V ⊆ U) :
    ContMDiffMBOn (E := H) (F := F') k f V :=
  ⟨hf.1.mono hVU, fun x hx ↦ (hf.2 x (hVU hx)).mono fun _ hy ↦ ⟨hy.1, hVU hy.2.1, hy.2.2⟩⟩

theorem contMDiffMBOn_congr [T2Space F'] {f g : X → N} {U : Set X} (hU : IsOpen U)
    (hf : ContMDiffMBOn (E := H) (F := F') k f U) (h : EqOn g f U) :
    ContMDiffMBOn (E := H) (F := F') k g U := by
  refine ⟨hf.1.congr h, fun x hx ↦ ?_⟩
  have hD : chartDomain g U (chartAt H x) (chartAt F' (g x)) =
      chartDomain f U (chartAt H x) (chartAt F' (f x)) := by
    rw [h hx]
    ext y
    simp only [chartDomain, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rwa [← h h2]⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rwa [h h2]⟩
  rw [hD, h hx]
  exact ContDiffMBOn.congr_of_isOpen (isOpen_chartDomain hU hf.1 _ _)
    (fun y hy ↦ by simp only [Function.comp_apply, h hy.2.1]) (hf.2 x hx)

end Helpers

/-- The inverses of the charts of a manifold are smooth. -/
theorem contMDiffMBOn_chart_symm {k : ℕ} {e : OpenPartialHomeomorph M E} (he : e ∈ atlas E M) :
    ContMDiffMBOn (E := E) (F := E) k e.symm e.target := by
  refine ⟨e.continuousOn_symm, fun y hy ↦ ?_⟩
  have h := smoothMBOn_transition he (chart_mem_atlas E (e.symm y)) k
  exact h.mono fun z hz ↦ ⟨hz.2.1, hz.2.2⟩

/-- Charts of a manifold are smooth on their sources. -/
theorem contMDiffMBOn_chart {k : ℕ} {e : OpenPartialHomeomorph M E} (he : e ∈ atlas E M) :
    ContMDiffMBOn (E := E) (F := E) k e e.source := by
  refine ⟨e.continuousOn, fun x hx ↦ ?_⟩
  have h := smoothMBOn_transition (chart_mem_atlas E x) he k
  exact h.mono fun z hz ↦ ⟨hz.1, hz.2.1⟩

namespace IsSmoothQuotientMap

variable {π : M → Q} (hπ : IsSmoothQuotientMap E π)
include hπ

/-- A chosen point of the fiber. -/
def pre (q : Q) : M := surjInv hπ.surjective q

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem pi_pre (q : Q) : π (hπ.pre q) = q := surjInv_eq hπ.surjective q

/-- A neighbourhood of `pre q`, inside the chart at `pre q`, on which `π` is injective. -/
def dom (q : Q) : Set M :=
  Classical.choose (hπ.locInj (hπ.pre q)) ∩ (chartAt E (hπ.pre q)).source

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem isOpen_dom (q : Q) : IsOpen (hπ.dom q) :=
  (Classical.choose_spec (hπ.locInj (hπ.pre q))).1.inter (chartAt E (hπ.pre q)).open_source

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem pre_mem_dom (q : Q) : hπ.pre q ∈ hπ.dom q :=
  ⟨(Classical.choose_spec (hπ.locInj (hπ.pre q))).2.1, mem_chart_source E _⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem injOn_dom (q : Q) : InjOn π (hπ.dom q) :=
  (Classical.choose_spec (hπ.locInj (hπ.pre q))).2.2.mono inter_subset_left

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem dom_subset (q : Q) : hπ.dom q ⊆ (chartAt E (hπ.pre q)).source := inter_subset_right

/-- `π` restricted to `dom q`, a local homeomorphism. -/
def sect (q : Q) : OpenPartialHomeomorph M Q :=
  haveI : Nonempty M := ⟨hπ.pre q⟩
  OpenPartialHomeomorph.ofContinuousOpen (Set.InjOn.toPartialEquiv π (hπ.dom q) (hπ.injOn_dom q))
    hπ.continuous.continuousOn hπ.isOpenMap (hπ.isOpen_dom q)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem sect_source (q : Q) : (hπ.sect q).source = hπ.dom q := rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem sect_target (q : Q) : (hπ.sect q).target = π '' hπ.dom q := rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem sect_apply (q : Q) (x : M) : hπ.sect q x = π x := rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem sect_symm_pi (q : Q) {x : M} (hx : x ∈ hπ.dom q) : (hπ.sect q).symm (π x) = x :=
  (hπ.sect q).left_inv hx

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem pi_sect_symm (q : Q) {y : Q} (hy : y ∈ (hπ.sect q).target) :
    π ((hπ.sect q).symm y) = y :=
  (hπ.sect q).right_inv hy

/-- **The chart of `Q` at `q`**: `c ∘ (π|_U)⁻¹`, for the chart `c` of `M` at `pre q`. -/
def chartQ (q : Q) : OpenPartialHomeomorph Q E :=
  (hπ.sect q).symm.trans (chartAt E (hπ.pre q))

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem chartQ_apply (q y : Q) : hπ.chartQ q y = chartAt E (hπ.pre q) ((hπ.sect q).symm y) := rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem chartQ_symm_apply (q : Q) (v : E) :
    (hπ.chartQ q).symm v = π ((chartAt E (hπ.pre q)).symm v) := rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem chartQ_source (q : Q) : (hπ.chartQ q).source = (hπ.sect q).target := by
  rw [chartQ, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
  refine inter_eq_left.2 fun y hy ↦ hπ.dom_subset q ((hπ.sect q).map_target hy)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem chartQ_target_subset (q : Q) :
    (hπ.chartQ q).target ⊆ (chartAt E (hπ.pre q)).target := by
  rw [chartQ, OpenPartialHomeomorph.trans_target]
  exact inter_subset_left

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
/-- **Near `z`, `(π|_U)⁻¹ ∘ π` is a deck transformation.** -/
theorem exists_deck (q : Q) {z : M} (hz : π z ∈ (hπ.sect q).target) :
    ∃ τ : M → M, SmoothMBM E E τ ∧ ∃ O, IsOpen O ∧ z ∈ O ∧ ∀ z' ∈ O,
      π z' ∈ (hπ.sect q).target ∧ (hπ.sect q).symm (π z') = τ z' ∧ τ z' ∈ hπ.dom q := by
  set w := (hπ.sect q).symm (π z)
  have hw : w ∈ hπ.dom q := (hπ.sect q).map_target hz
  have hπw : π w = π z := hπ.pi_sect_symm q hz
  obtain ⟨τ, hτ, hτz, hτπ⟩ := hπ.deck z w hπw.symm
  have hτc : Continuous τ := continuousOn_univ.1 (hτ 0).1
  refine ⟨τ, hτ, τ ⁻¹' hπ.dom q, (hπ.isOpen_dom q).preimage hτc, by
    change τ z ∈ hπ.dom q; rw [hτz]; exact hw, fun z' hz' ↦ ?_⟩
  have h1 : π z' = π (τ z') := (hτπ z').symm
  refine ⟨h1 ▸ mem_image_of_mem π hz', ?_, hz'⟩
  rw [h1]
  exact hπ.sect_symm_pi q hz'

/-- **Maps that lift to smooth maps into `M` have smooth local representatives** in the charts
`chartQ q`. -/
theorem contDiffMBOn_chartQ_of_lift {H : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H]
    [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [MBManifold H X]
    {k : ℕ} {F : X → Q} {F' : X → M} {V : Set X} (hV : IsOpen V)
    (hF' : ContMDiffMBOn (E := H) (F := E) k F' V) (hFF : ∀ p ∈ V, F p = π (F' p))
    {e : OpenPartialHomeomorph X H} (he : e ∈ atlas H X) (q : Q) :
    ContDiffMBOn k (hπ.chartQ q ∘ F ∘ e.symm) (chartDomain F V e (hπ.chartQ q)) := by
  have hFc : ContinuousOn F V :=
    (hπ.continuous.comp_continuousOn hF'.1).congr fun p hp ↦ hFF p hp
  have hD := isOpen_chartDomain hV hFc e (hπ.chartQ q)
  refine ContDiffMBOn.of_local hD fun y hy ↦ ?_
  obtain ⟨hye, hyV, hyF⟩ := hy
  have hz : π (F' (e.symm y)) ∈ (hπ.sect q).target := by
    rw [← hFF _ hyV, ← hπ.chartQ_source]; exact hyF
  obtain ⟨τ, hτ, O, hO, hzO, hOp⟩ := hπ.exists_deck q hz
  set c := chartAt E (hπ.pre q)
  have hG : ContMDiffMBOn (E := H) (F := E) k (τ ∘ F') V :=
    ContMDiffMBOn.comp (g := τ) (f := F') hV isOpen_univ (hτ k) hF' (mapsTo_univ _ _)
  have hrep := hG.contDiffMBOn_chart hV he (chart_mem_atlas E (hπ.pre q))
  set W := e.target ∩ e.symm ⁻¹' (V ∩ F' ⁻¹' O)
  have hW : IsOpen W := e.isOpen_inter_preimage_symm (hF'.1.isOpen_inter_preimage hV hO)
  have hWsub : W ⊆ chartDomain (τ ∘ F') V e c := fun y' hy' ↦
    ⟨hy'.1, hy'.2.1, hπ.dom_subset q (hOp _ hy'.2.2).2.2⟩
  refine ⟨W, hW, ⟨hye, hyV, hzO⟩, ?_⟩
  refine (ContDiffMBOn.congr_of_isOpen hW (fun y' hy' ↦ ?_) (hrep.mono hWsub)).mono
    inter_subset_right
  change c (τ (F' (e.symm y'))) = c ((hπ.sect q).symm (F (e.symm y')))
  rw [hFF _ hy'.2.1, (hOp _ hy'.2.2).2.1]

/-- **The charted space structure on `Q`.** -/
@[instance_reducible]
def chartedSpace : ChartedSpace E Q where
  atlas := range hπ.chartQ
  chartAt := hπ.chartQ
  mem_chart_source q := by
    rw [hπ.chartQ_source]
    exact ⟨hπ.pre q, hπ.pre_mem_dom q, hπ.pi_pre q⟩
  chart_mem_atlas q := mem_range_self q

theorem smoothMBOn_transQ (a b : Q) :
    SmoothMBOn ((hπ.chartQ a).symm.trans (hπ.chartQ b))
      ((hπ.chartQ a).symm.trans (hπ.chartQ b)).source := by
  intro k
  have hF' : ContMDiffMBOn (E := E) (F := E) k (chartAt E (hπ.pre a)).symm (hπ.chartQ a).target :=
    contMDiffMBOn_mono (contMDiffMBOn_chart_symm (chart_mem_atlas E (hπ.pre a)))
      (hπ.chartQ_target_subset a)
  have h := hπ.contDiffMBOn_chartQ_of_lift (H := E) (X := E) (hπ.chartQ a).open_target hF'
    (fun v _ ↦ hπ.chartQ_symm_apply a v) (chart_mem_atlas E (0 : E)) b
  exact h.mono fun z hz ↦ ⟨mem_univ _, hz.1, hz.2⟩

/-- **`Q` is a manifold.** -/
theorem mbManifold : @MBManifold E _ _ _ _ _ _ _ Q _ hπ.chartedSpace := by
  let := hπ.chartedSpace
  refine ⟨?_⟩
  rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
  refine ⟨hπ.smoothMBOn_transQ a b, ?_⟩
  rw [← OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm]
  exact hπ.smoothMBOn_transQ b a


/-- **Maps into `Q` that lift to smooth maps into `M` are smooth.** -/
theorem contMDiffMBOn_of_lift {H : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H]
    [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [MBManifold H X]
    {k : ℕ} {F : X → Q} {F' : X → M} {V : Set X} (hV : IsOpen V)
    (hF' : ContMDiffMBOn (E := H) (F := E) k F' V) (hFF : ∀ p ∈ V, F p = π (F' p)) :
    letI := hπ.chartedSpace
    ContMDiffMBOn (E := H) (F := E) k F V := by
  let := hπ.chartedSpace
  refine ⟨(hπ.continuous.comp_continuousOn hF'.1).congr fun p hp ↦ hFF p hp, fun x _ ↦ ?_⟩
  exact hπ.contDiffMBOn_chartQ_of_lift hV hF' hFF (chart_mem_atlas H x) (F x)

/-- **`π` is smooth.** -/
theorem smoothMBM : letI := hπ.chartedSpace; SmoothMBM E E π := by
  intro k
  exact hπ.contMDiffMBOn_of_lift isOpen_univ (smoothMBMOn_id isOpen_univ k) fun _ _ ↦ rfl

/-- **The local inverses of `π` are smooth.** -/
theorem contMDiffMBOn_sect_symm (q : Q) {k : ℕ} :
    letI := hπ.chartedSpace
    ContMDiffMBOn (E := E) (F := E) k (hπ.sect q).symm (hπ.sect q).target := by
  let := hπ.chartedSpace
  have := hπ.mbManifold
  set c := chartAt E (hπ.pre q)
  have h1 : ContMDiffMBOn (E := E) (F := E) k (hπ.chartQ q) (hπ.chartQ q).source :=
    contMDiffMBOn_chart (M := Q) (mem_range_self q)
  have h2 : ContMDiffMBOn (E := E) (F := E) k c.symm c.target :=
    contMDiffMBOn_chart_symm (chart_mem_atlas E (hπ.pre q))
  have h := ContMDiffMBOn.comp (g := c.symm) (f := hπ.chartQ q) (hπ.chartQ q).open_source
    c.open_target h2 h1 fun y hy ↦ hπ.chartQ_target_subset q ((hπ.chartQ q).map_source hy)
  rw [hπ.chartQ_source] at h
  refine contMDiffMBOn_congr (hπ.sect q).open_target h fun y hy ↦ ?_
  change (hπ.sect q).symm y = c.symm (c ((hπ.sect q).symm y))
  rw [c.left_inv (hπ.dom_subset q ((hπ.sect q).map_target hy))]

/-- **A map out of `Q` is smooth if its composition with `π` is.** -/
theorem contMDiffMB_of_comp {F' : Type u} [AddCommGroup F'] [Module ℝ F'] [TopologicalSpace F']
    [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] [LocallyConvexSpace ℝ F'] [T2Space F']
    {N : Type*} [TopologicalSpace N] [ChartedSpace F' N] [MBManifold F' N] {k : ℕ} {f : Q → N}
    (hf : ContMDiffMB E F' k (f ∘ π)) :
    letI := hπ.chartedSpace
    ContMDiffMB E F' k f := by
  let := hπ.chartedSpace
  have hq : Topology.IsQuotientMap π :=
    hπ.isOpenMap.isQuotientMap hπ.continuous hπ.surjective
  refine ⟨(hq.continuous_iff.2 (continuousOn_univ.1 hf.1)).continuousOn, fun x _ ↦ ?_⟩
  set c := chartAt E (hπ.pre x)
  have h := hf.contDiffMBOn_chart isOpen_univ (chart_mem_atlas E (hπ.pre x))
    (chart_mem_atlas F' (f x))
  exact h.mono fun v hv ↦ ⟨hπ.chartQ_target_subset x hv.1, mem_univ _, hv.2.2⟩

end IsSmoothQuotientMap

end Quotient

section Group

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]
  (Γ : Subgroup G) [DiscreteTopology Γ]

namespace MBLieGroup

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [ChartedSpace E G] [MBLieGroup E G] in
/-- A discrete subgroup meets some identity neighbourhood only in `1`. -/
theorem exists_isOpen_inter_eq_one :
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧ ∀ γ ∈ Γ, γ ∈ V → γ = 1 := by
  obtain ⟨V, hV, hpre⟩ := isOpen_induced_iff.1 (isOpen_discrete ({1} : Set Γ))
  have h1 : (1 : Γ) ∈ (Subtype.val ⁻¹' V : Set Γ) := by rw [hpre]; rfl
  refine ⟨V, hV, h1, fun γ hγ hγV ↦ ?_⟩
  have : (⟨γ, hγ⟩ : Γ) ∈ (Subtype.val ⁻¹' V : Set Γ) := hγV
  rw [hpre] at this
  exact congrArg Subtype.val this

include E in
/-- **The quotient map `G → G/Γ` by a discrete subgroup is a quotient by smooth deck
transformations**, the right translations by elements of `Γ`. -/
theorem isSmoothQuotientMap_mk : IsSmoothQuotientMap E (QuotientGroup.mk : G → G ⧸ Γ) := by
  have := isTopologicalGroup E G
  refine ⟨QuotientGroup.continuous_mk, QuotientGroup.isOpenMap_coe, QuotientGroup.mk_surjective,
    fun x ↦ ?_, fun x y h ↦ ?_⟩
  · obtain ⟨V, hV, h1V, hΓV⟩ := exists_isOpen_inter_eq_one Γ
    have hc : Continuous fun p : G × G ↦ p.1⁻¹ * p.2 :=
      (continuous_fst.inv).mul continuous_snd
    have hmem : (fun p : G × G ↦ p.1⁻¹ * p.2) ⁻¹' V ∈ 𝓝 ((1 : G), (1 : G)) :=
      hc.continuousAt.preimage_mem_nhds (by simpa using hV.mem_nhds h1V)
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 hmem
    obtain ⟨W, hWuv, hW, h1W⟩ := mem_nhds_iff.1 (inter_mem hu hv)
    refine ⟨(fun y ↦ x⁻¹ * y) ⁻¹' W, hW.preimage (continuous_const.mul continuous_id),
      by simpa using h1W, fun a ha b hb hab ↦ ?_⟩
    have hΓ : a⁻¹ * b ∈ Γ := QuotientGroup.eq.1 hab
    have hV' : a⁻¹ * b ∈ V := by
      have := huv (show (x⁻¹ * a, x⁻¹ * b) ∈ u ×ˢ v from ⟨(hWuv ha).1, (hWuv hb).2⟩)
      simpa [mul_assoc] using this
    have := hΓV _ hΓ hV'
    rw [inv_mul_eq_one] at this
    exact this
  · have hγ : x⁻¹ * y ∈ Γ := QuotientGroup.eq.1 h
    refine ⟨fun z ↦ z * (x⁻¹ * y), smoothMBM_mul_right _, by simp, fun z ↦ ?_⟩
    refine QuotientGroup.eq.2 ?_
    rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    exact Γ.inv_mem hγ

/-- The charted space structure of `G/Γ`, for `Γ` discrete. -/
@[instance_reducible]
instance instChartedSpaceQuotient : ChartedSpace E (G ⧸ Γ) :=
  (isSmoothQuotientMap_mk (E := E) Γ).chartedSpace

instance instMBManifoldQuotient : MBManifold E (G ⧸ Γ) :=
  (isSmoothQuotientMap_mk (E := E) Γ).mbManifold

/-- **The quotient map `G → G/Γ` is smooth.** -/
theorem smoothMBM_mk : SmoothMBM E E (QuotientGroup.mk : G → G ⧸ Γ) :=
  (isSmoothQuotientMap_mk (E := E) Γ).smoothMBM

/-- **`G/Γ` is a Lie group** for a discrete normal subgroup `Γ` ([GN26, Corollary 5.3.4]). -/
instance instMBLieGroupQuotient [Γ.Normal] : MBLieGroup E (G ⧸ Γ) := by
  set hπ := isSmoothQuotientMap_mk (E := E) Γ
  refine { smoothMBM_mul := fun k ↦ ?_, smoothMBM_inv := fun k ↦ ?_ }
  · refine ContMDiffMBOn.of_local isOpen_univ fun p _ ↦ ?_
    set s1 := hπ.sect p.1
    set s2 := hπ.sect p.2
    set W : Set ((G ⧸ Γ) × (G ⧸ Γ)) := s1.target ×ˢ s2.target
    have hW : IsOpen W := s1.open_target.prod s2.open_target
    have hp : p ∈ W := ⟨(hπ.chartQ_source p.1) ▸ mem_chart_source E p.1,
      (hπ.chartQ_source p.2) ▸ mem_chart_source E p.2⟩
    have hf1 : ContMDiffMBOn (E := ModelProd E E) (F := E) k (fun r : (G ⧸ Γ) × (G ⧸ Γ) ↦
        s1.symm r.1) W :=
      ContMDiffMBOn.comp (g := s1.symm) (f := Prod.fst) hW s1.open_target
        (hπ.contMDiffMBOn_sect_symm p.1) (contMDiffMBOn_mono (smoothMBM_fst k) (subset_univ _))
        fun r hr ↦ hr.1
    have hf2 : ContMDiffMBOn (E := ModelProd E E) (F := E) k (fun r : (G ⧸ Γ) × (G ⧸ Γ) ↦
        s2.symm r.2) W :=
      ContMDiffMBOn.comp (g := s2.symm) (f := Prod.snd) hW s2.open_target
        (hπ.contMDiffMBOn_sect_symm p.2) (contMDiffMBOn_mono (smoothMBM_snd k) (subset_univ _))
        fun r hr ↦ hr.2
    have hF' : ContMDiffMBOn (E := ModelProd E E) (F := E) k
        (fun r : (G ⧸ Γ) × (G ⧸ Γ) ↦ s1.symm r.1 * s2.symm r.2) W :=
      ContMDiffMBOn.comp (g := fun q : G × G ↦ q.1 * q.2)
        (f := fun r : (G ⧸ Γ) × (G ⧸ Γ) ↦ (s1.symm r.1, s2.symm r.2)) hW isOpen_univ
        (smoothMBM_mul (E := E) k) (ContMDiffMBOn.prodMk hW hf1 hf2) (mapsTo_univ _ _)
    refine ⟨W, hW, hp, hπ.contMDiffMBOn_of_lift hW hF' fun r hr ↦ ?_⟩
    rw [QuotientGroup.mk_mul, hπ.pi_sect_symm _ hr.1, hπ.pi_sect_symm _ hr.2]
  · refine ContMDiffMBOn.of_local isOpen_univ fun q _ ↦ ?_
    set s := hπ.sect q
    have hq : q ∈ s.target := (hπ.chartQ_source q) ▸ mem_chart_source E q
    have hF' : ContMDiffMBOn (E := E) (F := E) k (fun y : G ⧸ Γ ↦ (s.symm y)⁻¹) s.target :=
      ContMDiffMBOn.comp (g := fun g : G ↦ g⁻¹) (f := s.symm) s.open_target isOpen_univ
        (smoothMBM_inv (E := E) k) (hπ.contMDiffMBOn_sect_symm q) (mapsTo_univ _ _)
    refine ⟨s.target, s.open_target, hq, hπ.contMDiffMBOn_of_lift s.open_target hF'
      fun y hy ↦ ?_⟩
    rw [QuotientGroup.mk_inv, hπ.pi_sect_symm _ hy]

/-- **The quotient map `G → G/Γ` is a morphism of Lie groups.** -/
theorem isHom_mk [Γ.Normal] : IsHom E E (QuotientGroup.mk' Γ) := smoothMBM_mk Γ

/-- **`G → G/Γ` is a local diffeomorphism**: it is injective on a neighbourhood `U` of each point,
with a smooth inverse on the open set `π(U)`. -/
theorem exists_smooth_local_inverse (x : G) :
    ∃ U : Set G, IsOpen U ∧ x ∈ U ∧ InjOn (QuotientGroup.mk : G → G ⧸ Γ) U ∧
      IsOpen ((QuotientGroup.mk : G → G ⧸ Γ) '' U) ∧ ∃ σ : G ⧸ Γ → G,
        SmoothMBMOn E E σ ((QuotientGroup.mk : G → G ⧸ Γ) '' U) ∧ ∀ y ∈ U, σ (y : G ⧸ Γ) = y := by
  have := isTopologicalGroup E G
  set hπ := isSmoothQuotientMap_mk (E := E) Γ
  set q : G ⧸ Γ := QuotientGroup.mk x
  set γ := (hπ.pre q)⁻¹ * x
  have hγ : γ ∈ Γ := QuotientGroup.eq.1 (hπ.pi_pre q)
  have hmk : ∀ a : G, ((a * γ⁻¹ : G) : G ⧸ Γ) = a := fun a ↦
    QuotientGroup.eq.2 (by rw [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]; exact hγ)
  set U := (fun a : G ↦ a * γ⁻¹) ⁻¹' hπ.dom q
  have hU : IsOpen U := (hπ.isOpen_dom q).preimage (continuous_id.mul continuous_const)
  have hxU : x ∈ U := by
    change x * γ⁻¹ ∈ hπ.dom q
    rw [show x * γ⁻¹ = hπ.pre q by simp [γ]]
    exact hπ.pre_mem_dom q
  have himg : (QuotientGroup.mk : G → G ⧸ Γ) '' U ⊆ (hπ.sect q).target := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← hmk a]
    exact mem_image_of_mem _ ha
  refine ⟨U, hU, hxU, fun a ha b hb hab ↦ ?_, QuotientGroup.isOpenMap_coe U hU,
    fun y ↦ (hπ.sect q).symm y * γ, fun k ↦ ?_, fun y hy ↦ ?_⟩
  · have := hπ.injOn_dom q ha hb (by
      change ((a * γ⁻¹ : G) : G ⧸ Γ) = ((b * γ⁻¹ : G) : G ⧸ Γ)
      rw [hmk, hmk]; exact hab)
    simpa using this
  · have h := ContMDiffMBOn.comp (g := fun g : G ↦ g * γ) (f := (hπ.sect q).symm)
      (hπ.sect q).open_target isOpen_univ (smoothMBM_mul_right (E := E) γ k)
      (hπ.contMDiffMBOn_sect_symm q) (mapsTo_univ _ _)
    exact contMDiffMBOn_mono h himg
  · change (hπ.sect q).symm ((y : G ⧸ Γ)) * γ = y
    rw [← hmk y, hπ.sect_symm_pi q hy, inv_mul_cancel_right]

/-- **A map out of `G/Γ` is smooth if its composition with `G → G/Γ` is.** -/
theorem smoothMBM_of_comp_mk {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
    {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [MBManifold F N] {f : G ⧸ Γ → N}
    (hf : SmoothMBM E F (f ∘ (QuotientGroup.mk : G → G ⧸ Γ))) : SmoothMBM E F f := fun k ↦
  (isSmoothQuotientMap_mk (E := E) Γ).contMDiffMB_of_comp (hf k)

/-- **A bijective morphism with a smooth local inverse near the identity has a smooth inverse**:
near `g₀`, `φ⁻¹(g) = φ⁻¹(g₀) σ(g₀⁻¹ g)`. -/
theorem smoothMBM_symm_of_local {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
    {K : Type*} [Group K] [TopologicalSpace K] [ChartedSpace F K] [MBLieGroup F K]
    (φ : G ≃* K) {N : Set K} (hN : IsOpen N) (h1 : (1 : K) ∈ N) {σ : K → G}
    (hσ : SmoothMBMOn F E σ N) (hσφ : ∀ g ∈ N, σ g = φ.symm g) : SmoothMBM F E φ.symm := by
  have := isTopologicalGroup F K
  intro k
  refine ContMDiffMBOn.of_local isOpen_univ fun g₀ _ ↦ ?_
  set O := (fun g ↦ g₀⁻¹ * g) ⁻¹' N
  have hO : IsOpen O := hN.preimage (continuous_const.mul continuous_id)
  have hg₀ : g₀ ∈ O := by
    change g₀⁻¹ * g₀ ∈ N
    rw [inv_mul_cancel]; exact h1
  have h1' : ContMDiffMBOn (E := F) (F := F) k (fun g ↦ g₀⁻¹ * g) O :=
    contMDiffMBOn_mono (smoothMBM_mul_left (E := F) g₀⁻¹ k) (subset_univ _)
  have h2 := ContMDiffMBOn.comp (g := σ) (f := fun g ↦ g₀⁻¹ * g) hO hN (hσ k) h1' fun g hg ↦ hg
  have h3 := ContMDiffMBOn.comp (g := fun h ↦ φ.symm g₀ * h) (f := σ ∘ fun g ↦ g₀⁻¹ * g) hO
    isOpen_univ (smoothMBM_mul_left (E := E) (φ.symm g₀) k) h2 (mapsTo_univ _ _)
  refine ⟨O, hO, hg₀, contMDiffMBOn_congr hO h3 fun g hg ↦ ?_⟩
  change φ.symm g = φ.symm g₀ * σ (g₀⁻¹ * g)
  rw [hσφ _ hg, ← map_mul, mul_inv_cancel_left]

end MBLieGroup

end Group

end LocallyConvex.LieGroups
