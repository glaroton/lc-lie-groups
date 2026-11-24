/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Diffeomorphism.FlowSmooth
public import LocallyConvexLieGroups.LieGroup.OpenSubgroup
public import Mathlib.Analysis.LocallyConvex.BalancedCoreHull

/-!
# `Diff(K)` is a regular Lie group

Let `K` be a nonempty compact manifold modeled on a normed space, with a normalized local addition
`A`. Then the Lie group `Diff(K)` is `C⁰`-regular (`Diffeo.isC0Regular`): for a curve `ξ` of vector
fields near `0`, the evolution is `γ(t) = η_t⁻¹`, where `η_t` is the flow of `-ξ` from `0` to `t`.

## Proof

* The flow of `-ξ` exists for `ξ` with values in an open `0`-neighborhood `N₀` of `Γ_id`
  (`Diffeomorphism/Flow.lean`), and `ξ ↦ η_ξ = η_1` is smooth into `C^∞(K, K)` by the exponential
  law (`Diffeomorphism/FlowSmooth.lean`). Since `η_0 = id` and the diffeomorphisms in the domain of
  the chart at the identity form an open set, there is a balanced open `0`-neighborhood `W ⊆ N₀`
  of `Γ_id` such that `η_ζ` is such a diffeomorphism for `ζ ∈ C([0, 1], W)` (`Diffeo.W`).
* For `ξ ∈ C([0, 1], W)`, the flow from `r` to `t` is `η_{ζ_{r → t}}`
  (`Diffeo.flowCurve_shiftField`), so `η_t η_r⁻¹ = η_{ζ_{r → t}}`, and with `Ψ(ζ) = φ(η_ζ)`
  (`φ` the chart at the identity) the criterion `MBLieGroup.isEvolOn_of_flow` applies once
  `dΨ(0, -x) = x` is known.
* `dΨ(0, -x) = x` is checked pointwise, through the evaluations `u ↦ u(p)`, which are continuous
  linear and separate the points of `Γ_id`: in the preferred chart at `p`,
  `Ψ(-h x)(p) = Θ_p(S(h))` with `S(h) = z_h(1)` the time-one value of the solution of
  `ż = h x̃(z)`, `z(0) = p̃`, and `Θ_p` the inverse of `Σ(p, ·)`. The difference quotient
  `h⁻¹ (S(h) - p̃) = ∫₀¹ x̃(z_h(s)) ds` tends to `x̃(p̃) = x(p)`, and `dΘ_p(p̃) = id` for a
  normalized local addition.
* The local regularity criterion with solutions on `[0, 1]`
  (`MBLieGroup.isC0Regular_of_nhds_isEvolOn`) concludes.

[GN26, §13.1] leaves the regularity of `Diff(K)` to be written. It is classical: [KM97, Theorem
43.1] proves it in the convenient setting, and [Nee06, Theorem III.3.1] through the ILH structure of
`Diff(K)`; the argument here is the direct one, through the flows of time dependent vector fields.

## Main results

* `Diffeo.isEvolOn_flow`: the inverse flow is an evolution.
* `Diffeo.isC0Regular`: **`Diff(K)` is `C⁰`-regular.**

## Implementation notes

* The model space of `K` is a normed space in `Type` (the superposition operators on
  `C([0, 1], E)` are in a single universe), finite-dimensional since `K` is compact and nonempty.
* The local addition is normalized, as in `Diffeomorphism/LieAlgebra.lean`; every local addition
  can be normalized (lc-manifolds, `LocalAddition.normalize`).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
* [A. Kriegl, P. W. Michor, *The Convenient Setting of Global Analysis*][KM97]
* [K.-H. Neeb, *Towards a Lie theory of locally convex groups*][Nee06]
-/

@[expose] public section

open Set Filter Function Metric TopologicalSpace
open scoped Topology NNReal unitInterval
open LocallyConvex.Analysis LocallyConvex.Manifolds
open LocallyConvex.LieGroups.MBLieGroup (extendCurve valIn shiftField)

noncomputable section

namespace LocallyConvex.LieGroups

/-! ### Smoothness on open subsets of a vector space -/

section Opens

universe u

variable {E F : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- **Maps smooth on an open subset**, as a manifold, are smooth on it. -/
theorem smoothMBMOn_of_opens (s : Opens E) {f : E → N} (hf : SmoothMBM E F fun x : s ↦ f x) :
    SmoothMBMOn E F f s := by
  intro k
  refine ⟨continuousOn_iff_continuous_domRestrict.2 (continuousOn_univ.1 (hf k).1), fun x hx ↦ ?_⟩
  have h := (hf k).2 ⟨x, hx⟩ (mem_univ _)
  have hD : chartDomain (fun y : s ↦ f y) univ (chartAt E (⟨x, hx⟩ : s)) (chartAt F (f x)) =
      chartDomain f s (chartAt E x) (chartAt F (f x)) := by
    ext a
    simp only [chartDomain, mem_inter_iff, mem_preimage, mem_univ, true_and, chartAt_self_eq,
      OpenPartialHomeomorph.refl_target, OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply, id_eq]
    constructor
    · rintro ⟨ha, hfa⟩
      have hs := (opens_mem_chartAt_target s ⟨x, hx⟩).1 ha
      refine ⟨hs, ?_⟩
      rwa [opens_chartAt_symm_apply s ⟨x, hx⟩ hs] at hfa
    · rintro ⟨hs, hfa⟩
      refine ⟨(opens_mem_chartAt_target s ⟨x, hx⟩).2 hs, ?_⟩
      rwa [opens_chartAt_symm_apply s ⟨x, hx⟩ hs]
  rw [hD] at h
  refine h.congr_of_isOpen (isOpen_chartDomain s.isOpen (continuousOn_iff_continuous_domRestrict.2
    (continuousOn_univ.1 (hf k).1)) _ _) fun a ha ↦ ?_
  have hs : a ∈ s := ha.2.1
  simp only [Function.comp_apply, chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
    OpenPartialHomeomorph.refl_apply, id_eq]
  rw [opens_chartAt_symm_apply s ⟨x, hx⟩ hs]

end Opens

namespace Diffeo

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {K : Type} [TopologicalSpace K] [ChartedSpace H K] [MBManifold H K] [CompactSpace K] [T2Space K]
  (A : LocalAddition H K)

/-- An element of `Diff(K)` as a smooth map. -/
def toMap (d : Diffeo A) : SmoothMap H H K K := (show diffeos H K from d).1

/-! ### The flow of the zero field -/

theorem zero_mem_valIn_N₀ : (0 : C(I, DiffeoModel A)) ∈ valIn (N₀ A) := fun _ ↦ zero_mem_N₀ A

theorem flowCurve_zero_field (y : K) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    flowCurve A 0 y s = y := by
  have h0 := zero_mem_valIn_N₀ A
  have hc : IsIntCurve A 0 fun _ ↦ y := by
    refine ⟨continuousOn_const, fun t _ j hj ↦ ?_⟩
    have he : extendCurve (0 : C(I, DiffeoModel A)) t = 0 := by
      rw [MBLieGroup.extendCurve_apply]; rfl
    rw [he, rep_zero A j (j.1.map_source hj), neg_zero]
    exact hasDerivWithinAt_const _ _ _
  exact (isIntCurve_flowCurve A h0 y).eqOn A hc (flowCurve_zero A h0 y) hs

theorem flowOne_zero : flowOne A (zero_mem_valIn_N₀ A) = toMap A 1 :=
  SmoothMap.ext fun y ↦ flowCurve_zero_field A y ⟨zero_le_one, le_rfl⟩

omit [FiniteDimensional ℝ H] in
theorem shiftField_zero_one (ξ : C(I, DiffeoModel A)) : shiftField ξ 0 1 = ξ := by
  ext w : 1
  rw [MBLieGroup.shiftField_apply, sub_zero, one_smul, zero_add, mul_one,
    MBLieGroup.extendCurve_apply, projIcc_of_mem _ w.2]

/-! ### Fields whose flows lie in the chart at the identity -/

/-- The curves `ζ` with values in `N₀` whose time-one map is a diffeomorphism in the domain of
the chart of `Diff(K)` at the identity. -/
def goodSet : Set C(I, DiffeoModel A) :=
  {ζ | ∃ hζ : ζ ∈ valIn (N₀ A),
    ∃ d ∈ (chartAt (DiffeoModel A) (1 : Diffeo A)).source, toMap A d = flowOne A hζ}

theorem isOpen_goodSet : IsOpen (goodSet A) := by
  set U₀ : Opens C(I, DiffeoModel A) := ⟨valIn (N₀ A), MBLieGroup.isOpen_valIn (isOpen_N₀ A)⟩
  have hg : Continuous fun ζ : U₀ ↦ flowOne A ζ.2 :=
    continuousOn_univ.1 (smooth_flowOne A U₀ subset_rfl 0).1
  set S : Set (SmoothMap H H K K) := toMap A '' (chartAt (DiffeoModel A) (1 : Diffeo A)).source
  have hS : IsOpen S := SmoothMap.isOpen_setOf_isDiffeo.isOpenMap_subtype_val _
    (chartAt (DiffeoModel A) (1 : Diffeo A)).open_source
  have hO : IsOpen ((fun ζ : U₀ ↦ flowOne A ζ.2) ⁻¹' S) := hS.preimage hg
  have heq : goodSet A = Subtype.val '' ((fun ζ : U₀ ↦ flowOne A ζ.2) ⁻¹' S) := by
    ext ζ
    constructor
    · rintro ⟨hζ, d, hd, hde⟩
      exact ⟨⟨ζ, hζ⟩, ⟨d, hd, hde⟩, rfl⟩
    · rintro ⟨ζ', ⟨d, hd, hde⟩, rfl⟩
      exact ⟨ζ'.2, d, hd, hde⟩
  rw [heq]
  exact U₀.isOpen.isOpenMap_subtype_val _ hO

theorem zero_mem_goodSet : (0 : C(I, DiffeoModel A)) ∈ goodSet A :=
  ⟨zero_mem_valIn_N₀ A, 1, mem_chart_source _ _, (flowOne_zero A).symm⟩

theorem goodSet_subset : goodSet A ⊆ valIn (N₀ A) := fun _ hζ ↦ hζ.1

open Classical in
/-- The time-one map of `ζ ∈ goodSet`, as an element of `Diff(K)`. -/
def diffeoOf (ζ : C(I, DiffeoModel A)) : Diffeo A :=
  if hζ : ζ ∈ goodSet A then hζ.2.choose else 1

theorem diffeoOf_spec {ζ : C(I, DiffeoModel A)} (hζ : ζ ∈ goodSet A) :
    diffeoOf A ζ ∈ (chartAt (DiffeoModel A) (1 : Diffeo A)).source ∧
      toMap A (diffeoOf A ζ) = flowOne A hζ.1 := by
  rw [diffeoOf, dite_eq_left_of_eq_true (eq_true hζ)]
  exact hζ.2.choose_spec

theorem diffeoOf_apply {ζ : C(I, DiffeoModel A)} (hζ : ζ ∈ goodSet A) (y : K) :
    toMap A (diffeoOf A ζ) y = flowCurve A ζ y 1 := by
  rw [(diffeoOf_spec A hζ).2]; rfl

theorem diffeoOf_zero : diffeoOf A 0 = 1 :=
  Subtype.ext ((diffeoOf_spec A (zero_mem_goodSet A)).2.trans (flowOne_zero A))

/-- **`ζ ↦ η_ζ` is smooth into `Diff(K)`** on `goodSet`. -/
theorem smoothMBMOn_diffeoOf :
    SmoothMBMOn C(I, DiffeoModel A) (DiffeoModel A) (diffeoOf A) (goodSet A) := by
  set O : Opens C(I, DiffeoModel A) := ⟨goodSet A, isOpen_goodSet A⟩
  have hsm := smooth_flowOne A O (goodSet_subset A)
  set g : O → diffeos H K := fun ζ ↦ diffeoOf A ζ.1
  have hg : (VaryingAtlas.ofChartedSpace C(I, DiffeoModel A) O).Smooth (diffeoAtlas A) g := by
    intro k
    refine ((A.mappingAtlasSm (H := H) (M := K)).contMDiffOn_restrict_iff
      SmoothMap.isOpen_setOf_isDiffeo).2 ?_
    refine VaryingAtlas.ContMDiffOn.congr (hsm k) isOpen_univ fun ζ _ ↦ ?_
    exact (diffeoOf_spec A ζ.2).2.symm
  exact smoothMBMOn_of_opens O ((isVaryingLieGroup_diffeos A).smoothMBM_of_smooth hg)

/-! ### The time-one map in the chart at the identity -/

/-- `Ψ(ζ) = φ(η_ζ)`, the time-one map of the flow of `-ζ` in the chart `φ` of `Diff(K)` at the
identity. -/
def Ψ (ζ : C(I, DiffeoModel A)) : DiffeoModel A :=
  chartAt (DiffeoModel A) (1 : Diffeo A) (diffeoOf A ζ)

theorem smoothMBOn_Ψ : SmoothMBOn (Ψ A) (goodSet A) := fun k ↦ by
  have h := ContMDiffMBOn.comp (isOpen_goodSet A)
    (chartAt (DiffeoModel A) (1 : Diffeo A)).open_source
    (contMDiffMBOn_chart (k := k) (chart_mem_atlas (DiffeoModel A) (1 : Diffeo A)))
    (smoothMBMOn_diffeoOf A k) fun ζ hζ ↦ (diffeoOf_spec A hζ).1
  exact (contMDiffMBOn_iff_contDiffMBOn (isOpen_goodSet A)).1 h

theorem Ψ_zero : Ψ A 0 = 0 := by
  rw [Ψ, diffeoOf_zero]
  exact law_one A

/-- **`Ψ(ζ)` evaluated at `p`**: the fiber coordinate `θ⁻¹(p, η_ζ(p))`. -/
theorem evalAt_Ψ {ζ : C(I, DiffeoModel A)} (hζ : ζ ∈ goodSet A) (p : K) :
    (p, flowCurve A ζ p 1) ∈ A.toOpenPartialHomeomorph.target ∧
      evalAt A p (Ψ A ζ) = (A.toOpenPartialHomeomorph.symm (p, flowCurve A ζ p 1)).vec := by
  have hV := isVaryingLieGroup_diffeos A
  set d : diffeos H K := diffeoOf A ζ
  have hd : d ∈ (hV.transChart 1).source := (diffeoOf_spec A hζ).1
  have hs' : d ∈ (chartOne A).source := by
    have h := (hV.mem_transChart_source).1 hd
    rwa [inv_one, one_mul] at h
  have hsrc : (show diffeos H K from d).1 ∈ A.chartSourceSm (1 : diffeos H K).1 := by
    have h := hs'
    rw [chartOne, VaryingAtlas.restrict_chart_source] at h
    exact h
  have hval : (show diffeos H K from d).1 p = flowCurve A ζ p 1 := diffeoOf_apply A hζ p
  refine ⟨hval ▸ hsrc p, ?_⟩
  change (A.chartFunSm (1 : diffeos H K).1 ((1 : diffeos H K)⁻¹ * d).1) p = _
  rw [inv_one, one_mul, LocalAdditionAux.chartFunSm_apply A _ _ hsrc p, hval]
  rfl

/-! ### The derivative of `Ψ` at `0` -/

omit [FiniteDimensional ℝ H] in
theorem rep_smul (i : atlas H K) (u : DiffeoModel A) (c : ℝ) {z : H} (hz : z ∈ i.1.target) :
    rep A i (c • u) z = c • rep A i u z := by
  have h := rep_add_smul A i u 0 c 0 hz
  simpa using h

/-- The solution for the zero field is constant. -/
theorem sol_zero_field {x : K} (D : LocalData A x) {z : H} (hz : z ∈ ball (chartAt H x x) D.r) :
    ParamODE.sol D.data (0, z) = ContinuousMap.const I z := by
  have hp : ((0 : C(I, DiffeoModel A)), z) ∈ ParamODE.par D.N (chartAt H x x) D.r :=
    ⟨fun _ ↦ D.zero_mem, hz⟩
  have hc : ContinuousMap.const I z ∈ valuedIn I (closedBall (chartAt H x x) (2 * D.r)) :=
    fun _ ↦ closedBall_subset_closedBall (by linarith [D.data.pos]) (ball_subset_closedBall hz)
  refine (ParamODE.eq_sol D.data hp hc ?_).symm
  have hcb : ContinuousMap.const I z ∈ valuedIn I (ball (chartAt H x x) (3 * D.r)) :=
    fun s ↦ ParamODE.closedBall_subset_ball' D.data (hc s)
  have hf : ParamODE.field (vf A (cIdx (H := H) x)) D.N (chartAt H x x) D.r 0
      (ContinuousMap.const I z) = 0 := by
    have hzt : z ∈ (chartAt H x).target := D.ball_sub (hcb 0)
    ext s
    rw [ParamODE.field_apply D.data (fun _ ↦ D.zero_mem) hcb]
    simp [vf, rep_zero A (cIdx (H := H) x) hzt]
  ext t
  simp [ParamODE.Pic, hf]

/-- **The time-one value of the solution of `ż = h x̃(z)`** has derivative `x̃(z)` at `h = 0`. -/
theorem hasDirDerivAt_solOne_smul {x : K} (D : LocalData A x) (u : DiffeoModel A) :
    HasDirDerivAt (fun h : ℝ ↦ ParamODE.sol D.data (h • -ContinuousMap.const I u,
      chartAt H x x) 1) 0 1 (rep A (cIdx (H := H) x) u (chartAt H x x)) := by
  set j := cIdx (H := H) x
  set z := chartAt H x x
  set v : C(I, DiffeoModel A) := -ContinuousMap.const I u
  have hz : z ∈ ball z D.r := mem_ball_self D.data.pos
  have hp0 : ((0 : C(I, DiffeoModel A)), z) ∈ ParamODE.par D.N z D.r := ⟨fun _ ↦ D.zero_mem, hz⟩
  set sl : ℝ → C(I, H) := fun h ↦ ParamODE.sol D.data (h • v, z)
  have hpar : ∀ᶠ h in 𝓝 (0 : ℝ), (h • v, z) ∈ ParamODE.par D.N z D.r := by
    have hc : Continuous fun h : ℝ ↦ (h • v, z) := by fun_prop
    exact hc.continuousAt.preimage_mem_nhds ((ParamODE.isOpen_par D.isOpen).mem_nhds
      (by rw [zero_smul]; exact hp0))
  have hT : ∀ q ∈ ParamODE.par D.N z D.r, ParamODE.sol D.data q ∈ valuedIn I j.1.target :=
    fun q hq s ↦ D.ball_sub (ParamODE.sol_mem_ball D.data hq s)
  -- the rescaled integrand
  have hrepc : ContinuousOn (fun z' ↦ rep A j u z') j.1.target :=
    (contDiffMBOn_slice A j.1.open_target (smoothMBOn_rep A j 0) u).continuousOn
  set R : C(I, H) → C(I, H) := pushforward I (fun z' ↦ rep A j u z') j.1.target
  set Q : ℝ → H := fun h ↦ primitiveCLM (R (sl h)) 1
  have hQ : ContinuousAt Q 0 := by
    have hsl : ContinuousAt sl 0 := by
      have hc : Continuous fun h : ℝ ↦ (h • v, z) := by fun_prop
      refine ((ParamODE.smoothMBOn_sol D.data 0).continuousOn.continuousAt
        ((ParamODE.isOpen_par D.isOpen).mem_nhds ?_)).comp hc.continuousAt
      rw [zero_smul]; exact hp0
    have hR : ContinuousAt R (sl 0) :=
      (continuousOn_pushforward hrepc).continuousAt ((isOpen_valuedIn j.1.open_target).mem_nhds
        (hT _ (hpar.self_of_nhds)))
    exact ((continuous_eval_const (1 : I)).comp
      (primitiveCLM (E := H)).continuous).continuousAt.comp (hR.comp hsl)
  have hQ0 : Q 0 = rep A j u z := by
    have h0 : sl 0 = ContinuousMap.const I z := by
      simp only [sl, zero_smul]; exact sol_zero_field A D hz
    simp only [Q, primitiveCLM_apply, h0]
    have hRc : R (ContinuousMap.const I z) = ContinuousMap.const I (rep A j u z) := by
      ext s
      exact pushforward_apply hrepc (fun _ ↦ (D.ball_sub (ball_subset_ball
        (by linarith [D.data.pos]) hz))) s
    rw [hRc]
    simp [MBLieGroup.extendCurve_apply]
  -- the difference quotient
  have hdq : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
      h⁻¹ • (ParamODE.sol D.data ((0 + h • (1 : ℝ)) • v, z) 1 -
        ParamODE.sol D.data ((0 : ℝ) • v, z) 1) = Q h := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hpar] with h hh hp
    have hh' : h ≠ 0 := hh
    simp only [zero_add, smul_eq_mul, mul_one, zero_smul]
    rw [sol_zero_field A D hz, ContinuousMap.const_apply, ParamODE.sol_apply D.data hp,
      add_sub_cancel_left]
    have hint : ∀ s, extendCurve (ParamODE.field (vf A j) D.N z D.r (h • v) (sl h)) s =
        h • extendCurve (R (sl h)) s := fun s ↦ by
      rw [MBLieGroup.extendCurve_apply, MBLieGroup.extendCurve_apply,
        ParamODE.field_apply D.data hp.1 (ParamODE.sol_mem_ball D.data hp),
        pushforward_apply hrepc (hT _ hp)]
      have hzt := hT _ hp (projIcc 0 1 zero_le_one s)
      have hvs : (h • v) (projIcc 0 1 zero_le_one s) = (-h) • u := by
        simp [v, smul_neg, neg_smul]
      simp only [vf]
      rw [hvs, rep_smul A j u (-h) hzt, neg_smul, neg_neg]
    rw [intervalIntegral.integral_congr (g := fun s ↦ h • extendCurve (R (sl h)) s)
      (fun s _ ↦ hint s), intervalIntegral.integral_smul, smul_smul, inv_mul_cancel₀ hh', one_smul]
    rfl
  unfold HasDirDerivAt
  rw [← hQ0]
  exact (hQ.tendsto.mono_left nhdsWithin_le_nhds).congr' (hdq.mono fun h hh ↦ hh.symm)

/-- **`dΨ(0, -u) = u`**, for a normalized local addition: evaluated at `p`, through the inverse
`Θ_p` of `Σ(p, ·)` and the solutions in the preferred chart at `p`. -/
theorem dMB_Ψ (hA : A.IsNormalized) (u : DiffeoModel A) :
    dMB (Ψ A) (0, -ContinuousMap.const I u) = u := by
  refine SecSm.ext fun p ↦ ?_
  change evalAt A p (dMB (Ψ A) (0, -ContinuousMap.const I u)) = evalAt A p u
  set v : C(I, DiffeoModel A) := -ContinuousMap.const I u
  set D := ld A p
  set φ := chartAt H p
  set z := φ p
  set j := cIdx (H := H) p
  set S : ℝ → H := fun h ↦ ParamODE.sol D.data (h • v, z) 1
  have hz : z ∈ ball z D.r := mem_ball_self D.data.pos
  -- the derivative of `p ↦ Ψ(·)(p)` along `v`, from the smoothness of `Ψ`
  have hd : HasDirDerivAt (Ψ A) 0 v (dMB (Ψ A) (0, v)) :=
    (smoothMBOn_Ψ A 1).2.1 0 (zero_mem_goodSet A) v
  have hL : HasDirDerivAt (fun ζ ↦ evalAt A p (Ψ A ζ)) 0 v (evalAt A p (dMB (Ψ A) (0, v))) := by
    have h := ContDiffMBOn.hasDirDerivAt_comp isOpen_univ ((evalAt A p).contDiffMBOn 1 univ) hd
      (mem_univ _)
    rwa [((evalAt A p).hasDirDerivAt _ _).dMB_eq] at h
  -- the same derivative, computed in the chart at `p`
  have hS0 : S 0 = z := by
    simp only [S, zero_smul]
    rw [sol_zero_field A D hz]; rfl
  have hΘ : HasDirDerivAt (A.fibreInv p ∘ S) 0 1 (dMB (A.fibreInv p) (S 0, rep A j u z)) :=
    ContDiffMBOn.hasDirDerivAt_comp (A.isOpen_fibreInvDom p) (A.smoothMBOn_fibreInv p 1)
      (hasDirDerivAt_solOne_smul A D u) (by rw [hS0]; exact (A.fibreInv_self p).1)
  rw [hS0, LocalAdditionAux.dMB_fibreInv_self A hA p] at hΘ
  have hrep : rep A j u z = evalAt A p u := by
    rw [rep_apply]
    change coordAt j ⟨φ.symm (φ p), evalAt A (φ.symm (φ p)) u⟩ = _
    rw [φ.left_inv (mem_chart_source H p)]
    exact coordAt_chartAt p _
  rw [hrep] at hΘ
  have hev : ∀ᶠ h in 𝓝 (0 : ℝ), evalAt A p (Ψ A (h • v)) = A.fibreInv p (S h) := by
    have hc : Continuous fun h : ℝ ↦ h • v := by fun_prop
    have hmem : goodSet A ∩ valIn D.N ∈ 𝓝 (0 : C(I, DiffeoModel A)) :=
      inter_mem ((isOpen_goodSet A).mem_nhds (zero_mem_goodSet A))
        ((MBLieGroup.isOpen_valIn D.isOpen).mem_nhds fun _ ↦ D.zero_mem)
    filter_upwards [hc.continuousAt.preimage_mem_nhds (by rw [zero_smul]; exact hmem)]
      with h hh
    obtain ⟨hg, hN⟩ := hh
    obtain ⟨hθ, he⟩ := evalAt_Ψ A hg p
    have hflow := flowCurve_one_eq_local A D (goodSet_subset A hg) hN (mem_chart_source H p) hz
    rw [hflow] at hθ he
    rw [he]
    exact ((A.fibreInv_spec (solOne_mem_target A D ⟨hN, hz⟩) hθ).2).symm
  have hdir : HasDirDerivAt (fun ζ ↦ evalAt A p (Ψ A ζ)) 0 v (evalAt A p u) := by
    unfold HasDirDerivAt at hΘ ⊢
    refine hΘ.congr' ?_
    filter_upwards [nhdsWithin_le_nhds hev] with h hh
    simp only [Function.comp_apply, zero_add, smul_eq_mul, mul_one]
    rw [hh, Ψ_zero, map_zero, hS0, (A.fibreInv_self p).2]
  exact tendsto_nhds_unique hL hdir

/-! ### Evolutions -/

theorem exists_W : ∃ W : Set (DiffeoModel A), IsOpen W ∧ (0 : DiffeoModel A) ∈ W ∧
    (∀ x ∈ W, ∀ c : ℝ, |c| ≤ 1 → c • x ∈ W) ∧ valIn W ⊆ goodSet A := by
  have hN : goodSet A ∈ 𝓝 (0 : C(I, DiffeoModel A)) :=
    (isOpen_goodSet A).mem_nhds (zero_mem_goodSet A)
  obtain ⟨⟨K', W₀⟩, ⟨-, hW₀⟩, hsub⟩ :=
    ((𝓝 (0 : DiffeoModel A)).basis_sets.nhds_continuousMapConst (X := I)).mem_iff.1 hN
  obtain ⟨B, ⟨hB, hBbal⟩, hBW⟩ := (nhds_basis_balanced ℝ (DiffeoModel A)).mem_iff.1 hW₀
  have hB0 : (0 : DiffeoModel A) ∈ interior B := mem_interior_iff_mem_nhds.2 hB
  refine ⟨interior B, isOpen_interior, hB0, fun x hx c hc ↦ ?_,
    fun ξ hξ ↦ hsub fun t _ ↦ hBW (interior_subset (hξ t))⟩
  exact (hBbal.interior hB0).smul_mem (by rwa [Real.norm_eq_abs]) hx

/-- **A balanced open `0`-neighborhood `W` of `Γ_id`** such that the time-one maps of the curves
with values in `W` are diffeomorphisms in the domain of the chart at the identity. -/
def W : Set (DiffeoModel A) := (exists_W A).choose

theorem isOpen_W : IsOpen (W A) := (exists_W A).choose_spec.1

theorem zero_mem_W : (0 : DiffeoModel A) ∈ W A := (exists_W A).choose_spec.2.1

theorem smul_mem_W {x : DiffeoModel A} (hx : x ∈ W A) {c : ℝ} (hc : |c| ≤ 1) : c • x ∈ W A :=
  (exists_W A).choose_spec.2.2.1 x hx c hc

theorem valIn_W_subset : valIn (W A) ⊆ goodSet A := (exists_W A).choose_spec.2.2.2

/-- **The flow** `η_t` of `-ξ` from `0` to `t`, as an element of `Diff(K)`. -/
def η (ξ : C(I, DiffeoModel A)) (t : ℝ) : Diffeo A := diffeoOf A (shiftField ξ 0 t)

theorem shiftField_mem_goodSet {ξ : C(I, DiffeoModel A)} (hξ : ξ ∈ valIn (W A)) {r t : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) : shiftField ξ r t ∈ goodSet A :=
  valIn_W_subset A (MBLieGroup.shiftField_mem (fun _ hx _ hc ↦ smul_mem_W A hx hc) hξ
    (MBLieGroup.abs_sub_le_one hr ht))

theorem toMap_η {ξ : C(I, DiffeoModel A)} (hξ : ξ ∈ valIn (W A)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (y : K) : toMap A (η A ξ t) y = flowCurve A ξ y t := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hξ₀ := goodSet_subset A (valIn_W_subset A hξ)
  have hζ := shiftField_mem_goodSet A hξ h0 ht
  rw [η, diffeoOf_apply A hζ]
  have h := flowCurve_shiftField A hξ₀ h0 ht (goodSet_subset A hζ) y ⟨zero_le_one, le_rfl⟩
  rw [flowCurve_zero A hξ₀] at h
  rw [h, zero_add, one_mul, sub_zero]

/-- **The flow property in `Diff(K)`**: `η_t η_r⁻¹ = η_{ζ_{r → t}}`. -/
theorem η_mul_inv {ξ : C(I, DiffeoModel A)} (hξ : ξ ∈ valIn (W A)) {r t : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    η A ξ t * (η A ξ r)⁻¹ = diffeoOf A (shiftField ξ r t) := by
  have hξ₀ := goodSet_subset A (valIn_W_subset A hξ)
  have hζ := shiftField_mem_goodSet A hξ hr ht
  suffices h : η A ξ t = diffeoOf A (shiftField ξ r t) * η A ξ r by
    rw [h, mul_inv_cancel_right]
  refine Subtype.ext (SmoothMap.ext fun y ↦ ?_)
  change toMap A (η A ξ t) y = toMap A (diffeoOf A (shiftField ξ r t)) (toMap A (η A ξ r) y)
  rw [toMap_η A hξ ht, toMap_η A hξ hr, diffeoOf_apply A hζ,
    flowCurve_shiftField A hξ₀ hr ht (goodSet_subset A hζ) y ⟨zero_le_one, le_rfl⟩, one_mul,
    add_sub_cancel]

/-- **The evolution of `ξ` is `t ↦ η_t⁻¹`.** -/
theorem isEvolOn_flow (hA : A.IsNormalized) {ξ : C(I, DiffeoModel A)} (hξ : ξ ∈ valIn (W A)) :
    MBLieGroup.IsEvolOn (DiffeoModel A) (extendCurve ξ) fun t ↦ (η A ξ t)⁻¹ := by
  refine MBLieGroup.isEvolOn_of_flow (isOpen_W A) (zero_mem_W A)
    ((smoothMBOn_Ψ A 1).mono (valIn_W_subset A)) (Ψ_zero A) (dMB_Ψ A hA) ?_ ?_ ?_
  · rw [η, MBLieGroup.shiftField_self', diffeoOf_zero]
  · intro t ht r hr
    rw [η_mul_inv A hξ hr ht]
    exact (diffeoOf_spec A (shiftField_mem_goodSet A hξ hr ht)).1
  · intro t ht r hr
    rw [η_mul_inv A hξ hr ht]
    rfl

/-! ### Regularity -/

/-- **`Diff(K)` is `C⁰`-regular** ([GN26, §13.1]), for a compact manifold `K` modeled on a
finite-dimensional normed space, with a normalized local addition. -/
theorem isC0Regular_of_finiteDimensional (hA : A.IsNormalized) :
    MBLieGroup.IsC0Regular (DiffeoModel A) (Diffeo A) := by
  have hU : IsOpen (valIn (W A)) := MBLieGroup.isOpen_valIn (isOpen_W A)
  have hsol : ∀ ξ ∈ valIn (W A), ∃ γ : ℝ → Diffeo A,
      MBLieGroup.IsEvolOn (DiffeoModel A) (extendCurve ξ) γ := fun ξ hξ ↦
    ⟨_, isEvolOn_flow A hA hξ⟩
  have hP := MBLieGroup.exists_isEvol_const_of_isEvolOn
    ((isOpen_W A).mem_nhds (zero_mem_W A)) hsol
  refine MBLieGroup.isC0Regular_of_nhds_isEvolOn hU (fun _ ↦ zero_mem_W A) hsol ?_
  have hdi : SmoothMBMOn C(I, DiffeoModel A) (DiffeoModel A) (diffeoOf A) (valIn (W A)) :=
    fun k ↦ ContMDiffMBOn.mono' (smoothMBMOn_diffeoOf A k) (valIn_W_subset A)
  have hinv := SmoothMBMOn.comp hU isOpen_univ
    (fun k ↦ (MBLieGroup.smoothMBM_inv (E := DiffeoModel A) (G := Diffeo A)) k) hdi
    (mapsTo_univ _ _)
  refine fun k ↦ ContMDiffMBOn.congr' hU (hinv k) fun ξ hξ ↦ ?_
  rw [MBLieGroup.evol_eq_of_isEvolOn hP (isEvolOn_flow A hA hξ)]
  change (diffeoOf A (shiftField ξ 0 1))⁻¹ = (diffeoOf A ξ)⁻¹
  rw [shiftField_zero_one]

end Diffeo

/-- **`Diff(K)` is `C⁰`-regular** ([GN26, §13.1]), for a nonempty compact manifold `K` modeled on
a normed space (finite-dimensional, since `K` is compact), with a normalized local addition. -/
theorem Diffeo.isC0Regular {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : Type} [TopologicalSpace K] [ChartedSpace H K] [MBManifold H K] [CompactSpace K]
    [T2Space K] [Nonempty K] (A : LocalAddition H K) (hA : A.IsNormalized) :
    MBLieGroup.IsC0Regular (DiffeoModel A) (Diffeo A) :=
  have := finiteDimensional_of_compactSpace (H := H) K
  Diffeo.isC0Regular_of_finiteDimensional A hA

end LocallyConvex.LieGroups
