/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Diffeomorphism.IntCurve
public import LocallyConvexLieGroups.Regular.FlowCriterion

/-!
# Flows of time dependent vector fields on a compact manifold

Let `K` be a compact manifold modeled on a finite-dimensional normed space, with a local addition
`A`. Around each point `x` of `K`, in the preferred chart, the equation `ż = -ξ̃(t)(z)` satisfies
the hypotheses of `ParamODE` for `ξ` in an open `0`-neighborhood `N_x` of `Γ_id` and initial values
in a ball (`Diffeo.LocalData`): the representatives near `0` are small with small derivatives,
uniformly on a compact ball (`exists_isOpen_bound`). Finitely many of these balls cover `K`; for `ξ`
with values in the intersection `N₀` of the corresponding `N_x`, the integral curve of `-ξ` through
every point exists on `[0, 1]` (`Diffeo.flowCurve`), and it is given by the solution in the chart
of any local data (`Diffeo.flowCurve_eq_local`), by uniqueness of integral curves.

Reparametrizing integral curves (`Diffeo.IsIntCurve.shift`) gives the **flow property**: the flow
from `r` to `t` is the time-one map of the rescaled curve `ζ_{r → t}`
(`Diffeo.flowCurve_shiftField`).

## Main definitions

* `Diffeo.LocalData A x`: data for the equation in the preferred chart at `x`.
* `Diffeo.N₀ A`: the common open `0`-neighborhood of `Γ_id`.
* `Diffeo.flowCurve A ξ y`: the integral curve of `-ξ` starting at `y`.

## Main results

* `Diffeo.isIntCurve_flowCurve`, `Diffeo.flowCurve_zero`: the integral curves.
* `Diffeo.flowCurve_eq_local`: they are the solutions in charts.
* `Diffeo.flowCurve_shiftField`: the flow property.
-/

@[expose] public section

open Set Filter Function Metric
open scoped Topology NNReal unitInterval
open LocallyConvex.Analysis LocallyConvex.Manifolds
open LocallyConvex.LieGroups.MBLieGroup (extendCurve valIn shiftField)

noncomputable section

namespace LocallyConvex.LieGroups.Diffeo

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {K : Type} [TopologicalSpace K] [ChartedSpace H K] [MBManifold H K] [CompactSpace K] [T2Space K]
  (A : LocalAddition H K)

/-! ### Local data -/

/-- **Data for the equation `ż = -ξ̃(t)(z)` in the preferred chart at `x`**: a radius `r` and an
open `0`-neighborhood `N` of `Γ_id` satisfying the hypotheses of `ParamODE` on `B(x̃, 3r)`. -/
structure LocalData (x : K) where
  /-- The radius. -/
  r : ℝ
  /-- The fields. -/
  N : Set (DiffeoModel A)
  isOpen : IsOpen N
  zero_mem : (0 : DiffeoModel A) ∈ N
  ball_sub : ball (chartAt H x x) (3 * r) ⊆ (chartAt H x).target
  data : ParamODE.IsData (vf A (cIdx (H := H) x)) N (chartAt H x x) r

theorem nonempty_localData (x : K) : Nonempty (LocalData A x) := by
  set j := cIdx (H := H) x
  set z₀ := chartAt H x x
  have hz₀ : z₀ ∈ (chartAt H x).target := (chartAt H x).map_source (mem_chart_source H x)
  obtain ⟨ε, hε, hεt⟩ := Metric.isOpen_iff.1 (chartAt H x).open_target z₀ hz₀
  set r := ε / 4
  have hr : 0 < r := by positivity
  have hcl : closedBall z₀ (3 * r) ⊆ (chartAt H x).target :=
    (closedBall_subset_ball (by simp only [r]; linarith)).trans hεt
  set ε' := min r (1 / 2)
  have hε' : 0 < ε' := lt_min hr (by norm_num)
  have hvf := smoothMBOn_vf A j
  obtain ⟨N, hNo, hN0, hN⟩ := exists_isOpen_bound (W := DiffeoModel A) (f := vf A j)
    (chartAt H x).open_target (hvf 1) (fun z hz ↦ by simp [vf, rep_zero A j hz])
    (isCompact_closedBall z₀ (3 * r)) hcl hε'
  have hsub : ball z₀ (3 * r) ⊆ (chartAt H x).target := ball_subset_closedBall.trans hcl
  refine ⟨⟨r, N, hNo, hN0, hsub, hNo, hr,
    fun k ↦ (hvf k).mono (prod_mono (subset_univ _) hsub), ?_, ?_⟩⟩
  · intro w hw z hz
    exact (hN w hw z (ball_subset_closedBall hz)).1.le.trans (min_le_left _ _)
  · intro w hw z hz z' hz'
    have hg := contDiffMBOn_slice A (chartAt H x).open_target (hvf 1) w
    refine norm_sub_le_of_dMB_le (chartAt H x).open_target hg (convex_ball z₀ (3 * r)) hsub
      (by norm_num) (fun z'' hz'' h ↦ ?_) hz hz'
    rw [dMB_slice_right]
    exact ((hN w hw z'' (ball_subset_closedBall hz'')).2 h).trans
      (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _))

/-- A choice of local data at every point. -/
def ld (x : K) : LocalData A x := Classical.choice (nonempty_localData A x)

/-- The open set where the solutions of the local data at `x` start. -/
def startSet (x : K) : Set K :=
  (chartAt H x).source ∩ chartAt H x ⁻¹' ball (chartAt H x x) (ld A x).r

theorem isOpen_startSet (x : K) : IsOpen (startSet A x) :=
  (chartAt H x).isOpen_inter_preimage isOpen_ball

theorem mem_startSet (x : K) : x ∈ startSet A x :=
  ⟨mem_chart_source H x, mem_ball_self (ld A x).data.pos⟩

theorem exists_cover : ∃ T : Finset K, ∀ y, ∃ x ∈ T, y ∈ startSet A x := by
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (startSet A) (isOpen_startSet A)
    fun y _ ↦ mem_iUnion.2 ⟨y, mem_startSet A y⟩
  refine ⟨T, fun y ↦ ?_⟩
  obtain ⟨x, hx, hy⟩ := mem_iUnion₂.1 (hT (mem_univ y))
  exact ⟨x, hx, hy⟩

/-- A finite set of centers of local data whose start sets cover `K`. -/
def cover : Finset K := (exists_cover A).choose

/-- **The common `0`-neighborhood** of `Γ_id`: fields for which all the local data apply. -/
def N₀ : Set (DiffeoModel A) := ⋂ x ∈ cover A, (ld A x).N

theorem isOpen_N₀ : IsOpen (N₀ A) := isOpen_biInter_finset fun x _ ↦ (ld A x).isOpen

theorem zero_mem_N₀ : (0 : DiffeoModel A) ∈ N₀ A := mem_iInter₂.2 fun x _ ↦ (ld A x).zero_mem

/-- The center of a start set containing `y`. -/
def ctr (y : K) : K := ((exists_cover A).choose_spec y).choose

theorem ctr_mem (y : K) : ctr A y ∈ cover A := ((exists_cover A).choose_spec y).choose_spec.1

theorem mem_startSet_ctr (y : K) : y ∈ startSet A (ctr A y) :=
  ((exists_cover A).choose_spec y).choose_spec.2

theorem valIn_ld {ξ : C(I, DiffeoModel A)} (hξ : ξ ∈ valIn (N₀ A)) {x : K} (hx : x ∈ cover A) :
    ξ ∈ valIn (ld A x).N := fun s ↦ mem_iInter₂.1 (hξ s) x hx

/-! ### Integral curves through every point -/

/-- **The integral curve of `-ξ` starting at `y`**, from the local data at a center for `y`. -/
def flowCurve (ξ : C(I, DiffeoModel A)) (y : K) (s : ℝ) : K :=
  (chartAt H (ctr A y)).symm
    (extendCurve (ParamODE.sol (ld A (ctr A y)).data (ξ, chartAt H (ctr A y) y)) s)

theorem isIntCurve_flowCurve {ξ : C(I, DiffeoModel A)} (hξ : ξ ∈ valIn (N₀ A)) (y : K) :
    IsIntCurve A ξ (flowCurve A ξ y) :=
  isIntCurve_sol A (cIdx (H := H) (ctr A y)) (ld A (ctr A y)).data (ld A (ctr A y)).ball_sub
    (valIn_ld A hξ (ctr_mem A y)) (mem_startSet_ctr A y).2

/-- The solution in the chart of local data starts at the initial point. -/
theorem sol_start {x : K} (D : LocalData A x) {ξ : C(I, DiffeoModel A)} (hξ : ξ ∈ valIn D.N)
    {y : K} (hy : y ∈ (chartAt H x).source) (hyr : chartAt H x y ∈ ball (chartAt H x x) D.r) :
    (chartAt H x).symm (extendCurve (ParamODE.sol D.data (ξ, chartAt H x y)) 0) = y := by
  rw [MBLieGroup.extendCurve_apply, projIcc_left]
  change (chartAt H x).symm (ParamODE.sol D.data (ξ, chartAt H x y) 0) = y
  rw [ParamODE.sol_zero D.data ⟨hξ, hyr⟩, (chartAt H x).left_inv hy]

theorem flowCurve_zero {ξ : C(I, DiffeoModel A)} (hξ : ξ ∈ valIn (N₀ A)) (y : K) :
    flowCurve A ξ y 0 = y :=
  sol_start A _ (valIn_ld A hξ (ctr_mem A y)) (mem_startSet_ctr A y).1 (mem_startSet_ctr A y).2

/-- **The integral curves are the solutions in the chart of any local data.** -/
theorem flowCurve_eq_local {x : K} (D : LocalData A x) {ξ : C(I, DiffeoModel A)}
    (hξ₀ : ξ ∈ valIn (N₀ A)) (hξ : ξ ∈ valIn D.N) {y : K} (hy : y ∈ (chartAt H x).source)
    (hyr : chartAt H x y ∈ ball (chartAt H x x) D.r) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    flowCurve A ξ y s =
      (chartAt H x).symm (extendCurve (ParamODE.sol D.data (ξ, chartAt H x y)) s) :=
  (isIntCurve_flowCurve A hξ₀ y).eqOn A
    (isIntCurve_sol A (cIdx (H := H) x) D.data D.ball_sub hξ hyr)
    (by rw [flowCurve_zero A hξ₀, sol_start A D hξ hy hyr]) hs

/-! ### The flow property -/

omit [FiniteDimensional ℝ H] in
/-- **Reparametrized integral curves**: `w ↦ c(r + w (t - r))` is an integral curve of
`-ζ_{r → t}`. -/
theorem IsIntCurve.shift {ξ : C(I, DiffeoModel A)} {c : ℝ → K} (hc : IsIntCurve A ξ c) {r t : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    IsIntCurve A (shiftField ξ r t) fun w ↦ c (r + w * (t - r)) := by
  set φ : ℝ → ℝ := fun w ↦ r + w * (t - r)
  have hmaps : MapsTo φ (Icc 0 1) (Icc 0 1) := fun w hw ↦ MBLieGroup.mem_Icc_of_mem hr ht hw
  have hφc : Continuous φ := by fun_prop
  refine ⟨hc.1.comp hφc.continuousOn hmaps, fun w hw j hj ↦ ?_⟩
  have hd := hc.2 (φ w) (hmaps hw) j hj
  have hφ : HasDerivWithinAt φ (t - r) (Icc 0 1) w := by
    have := ((hasDerivAt_id w).mul_const (t - r)).const_add r
    simpa [φ] using this.hasDerivWithinAt
  have hcomp := hd.scomp w hφ hmaps
  have hz : j.1 (c (φ w)) ∈ j.1.target := j.1.map_source hj
  have hval : extendCurve (shiftField ξ r t) w = (t - r) • extendCurve ξ (φ w) := by
    rw [MBLieGroup.extendCurve_apply, projIcc_of_mem _ hw]
    rfl
  have hlin := rep_add_smul A j (extendCurve ξ (φ w)) 0 (t - r) 0 hz
  simp only [zero_smul, add_zero] at hlin
  rw [hval, hlin, ← smul_neg]
  exact hcomp

/-- **The flow property**: the integral curve of `-ζ_{r → t}` through `c_y(r)` is
`w ↦ c_y(r + w (t - r))`. -/
theorem flowCurve_shiftField {ξ : C(I, DiffeoModel A)} (hξ : ξ ∈ valIn (N₀ A)) {r t : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hζ : shiftField ξ r t ∈ valIn (N₀ A))
    (y : K) {w : ℝ} (hw : w ∈ Icc (0 : ℝ) 1) :
    flowCurve A (shiftField ξ r t) (flowCurve A ξ y r) w = flowCurve A ξ y (r + w * (t - r)) :=
  (isIntCurve_flowCurve A hζ _).eqOn A ((isIntCurve_flowCurve A hξ y).shift A hr ht)
    (by rw [flowCurve_zero A hζ]; simp) hw

end LocallyConvex.LieGroups.Diffeo
