/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.CircleCover.LieGroup
public import LocallyConvexLieGroups.CircleCover.Inverse
public import LocallyConvexLieGroups.Exponential.Basic
public import LocallyConvexAnalysis.ODE.MaximalFlow
public import Mathlib.Analysis.ODE.ExistUnique

/-!
# The exponential function of the universal cover of `Diff⁺(S¹)`

A periodic function `x ∈ C^∞_per` is the vector field `x ∂_y` on `ℝ`, invariant under the
translation by `1`. Since `x` is bounded and Lipschitz, its flow `Fl^x` is global, and
`Fl^x_t = id + (Fl^x_t − id)` with `Fl^x_t − id` periodic. We show that
`exp(x) = Fl^x_1 − id` is an exponential function of `\widetilde{Diff}⁺(S¹)` in the sense of
[GN26, Definition 5.6.1] (`MBLieGroup.IsExp`).

## Main definitions

* `CircleCover.vf`: the equation `y' = x(y)`, with the parameter `x ∈ C^∞_per`.
* `CircleCover.Fl t y x`: its flow, `Fl^x_t(y)`.
* `CircleCover.expMap x = Fl^x_1 − id ∈ C^∞_per` and `CircleCover.exp x ∈ \widetilde{Diff}⁺(S¹)`.

## Main results

* `CircleCover.mem_dom`: **the flow is global**, by the Picard–Lindelöf theorem on `[-T, T]`
  (Mathlib), with the bounds `|x| ≤ p₀(x)` and `Lip(x) ≤ p₁(x)`.
* `CircleCover.smoothMBOn_flow`: **the flow is smooth in time, initial value and the parameter
  `x ∈ C^∞_per`**, by lc-analysis's maximal flows with locally convex parameters
  ([GN26, Theorem 2.4.29]).
* `CircleCover.Fl_add`, `CircleCover.Fl_smul`, `CircleCover.Fl_add_one`: the flow property
  `Fl^x_{s+t} = Fl^x_s ∘ Fl^x_t`, the rescaling `Fl^{c x}_t = Fl^x_{c t}`, and the periodicity
  `Fl^x_t(y + 1) = Fl^x_t(y) + 1`, all by uniqueness of solutions.
* `CircleCover.smoothMBOn_expMap`: `exp` is smooth into `C^∞_per`
  (`CircleCover.smoothMBOn_of_uncurry`).
* `CircleCover.isExp_exp`: **`\widetilde{Diff}⁺(S¹)` has an exponential function**
  ([GN26, §13.3]: `exp(x) = Fl^x_1`).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function
open scoped Topology NNReal ContDiff
open LocallyConvex.Analysis LocallyConvex.Manifolds CInfPer DiffCircle

noncomputable section

namespace LocallyConvex.LieGroups.CircleCover

/-! ### The flow of a periodic vector field -/

/-- The equation `y' = x(y)`, as `f(t, y, x) = x(y)`. -/
def vf (q : ℝ × ℝ × CInfPer) : ℝ := q.2.2 q.2.1

theorem smoothMBOn_vf : SmoothMBOn vf univ := fun k ↦ by
  set A : ℝ × ℝ × CInfPer →L[ℝ] CInfPer × ℝ :=
    ((ContinuousLinearMap.snd ℝ ℝ CInfPer).comp (ContinuousLinearMap.snd ℝ ℝ _)).prod
      ((ContinuousLinearMap.fst ℝ ℝ CInfPer).comp (ContinuousLinearMap.snd ℝ ℝ _))
  have h := ContDiffMBOn.comp_clm A isOpen_univ (smoothMBOn_ev k)
  rw [preimage_univ] at h
  exact h

theorem locallyLipschitzY_vf : MaximalFlow.LocallyLipschitzY vf univ :=
  MaximalFlow.locallyLipschitzY_of_contDiffMBOn isOpen_univ (smoothMBOn_vf 1)

/-- **The flow is global**: solutions of `y' = x(y)` exist on all of `ℝ`. -/
theorem mem_dom (t t₀ y : ℝ) (x : CInfPer) : (t, t₀, y, x) ∈ MaximalFlow.dom vf univ := by
  set T : ℝ := |t| + |t₀| + 1
  have hT : 0 < T := by positivity
  set L : ℝ≥0 := ⟨seminorm 0 x, apply_nonneg _ _⟩
  set K : ℝ≥0 := ⟨seminorm 1 x, apply_nonneg _ _⟩
  set a : ℝ≥0 := L * ⟨2 * T, by positivity⟩
  have ht₀ : t₀ ∈ Icc (-T) T :=
    ⟨by linarith [neg_abs_le t₀, abs_nonneg t], by linarith [le_abs_self t₀, abs_nonneg t]⟩
  have hb : ∀ z ∈ Metric.closedBall y a, ‖(x : ℝ → ℝ) z‖ ≤ L := fun z _ ↦ by
    rw [Real.norm_eq_abs]; exact abs_apply_le x z
  have hl : LipschitzOnWith K (x : ℝ → ℝ) (Metric.closedBall y a) := by
    refine (LipschitzWith.of_dist_le_mul fun z w ↦ ?_).lipschitzOnWith
    rw [Real.dist_eq, Real.dist_eq]
    exact abs_sub_le x w z
  have hm : (L : ℝ) * max (T - t₀) (t₀ - -T) ≤ (a : ℝ) - ((0 : ℝ≥0) : ℝ) := by
    have hmax : max (T - t₀) (t₀ - -T) ≤ 2 * T :=
      max_le (by linarith [ht₀.1]) (by linarith [ht₀.2])
    simp only [a, NNReal.coe_zero, sub_zero]
    exact mul_le_mul_of_nonneg_left hmax L.2
  have hPL : IsPicardLindelof (fun _ ↦ (x : ℝ → ℝ)) (⟨t₀, ht₀⟩ : Icc (-T) T) y a 0 L K :=
    IsPicardLindelof.of_time_independent hb hl hm
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hsol : MaximalFlow.IsSol vf univ x (Ioo (-T) T) α := fun s hs ↦
    ⟨mem_univ _, (hα s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)⟩
  have ht₀' : t₀ ∈ Ioo (-T) T :=
    ⟨by linarith [neg_abs_le t₀, abs_nonneg t], by linarith [le_abs_self t₀, abs_nonneg t]⟩
  have ht' : t ∈ Ioo (-T) T :=
    ⟨by linarith [neg_abs_le t, abs_nonneg t₀], by linarith [le_abs_self t, abs_nonneg t₀]⟩
  have h := MaximalFlow.mem_dom isOpen_Ioo isPreconnected_Ioo ht₀' ht' hsol
  change (t, t₀, α (⟨t₀, ht₀⟩ : Icc (-T) T), x) ∈ _ at h
  rwa [hα0] at h

theorem dom_eq_univ : MaximalFlow.dom vf univ = univ :=
  eq_univ_of_forall fun q ↦ mem_dom q.1 q.2.1 q.2.2.1 q.2.2.2

/-- **The flow is smooth in time, initial time, initial value and the parameter.** -/
theorem smoothMBOn_flow : SmoothMBOn (MaximalFlow.flow vf univ) univ := by
  have h := (MaximalFlow.isOpen_dom_and_smoothMBOn_flow isOpen_univ smoothMBOn_vf).2
  rwa [dom_eq_univ] at h

/-- The flow `Fl^x_t(y)` of the vector field `x ∂_y`. -/
def Fl (t y : ℝ) (x : CInfPer) : ℝ := MaximalFlow.flow vf univ (t, 0, y, x)

/-- **Uniqueness**: a global solution of `γ' = x(γ)` is the flow. -/
theorem flow_eq_of_hasDerivAt {x : CInfPer} {γ : ℝ → ℝ} (hγ : ∀ s, HasDerivAt γ (x (γ s)) s)
    (t t₀ : ℝ) : MaximalFlow.flow vf univ (t, t₀, γ t₀, x) = γ t :=
  MaximalFlow.flow_eq locallyLipschitzY_vf isOpen_univ isPreconnected_univ (mem_univ _)
    (mem_univ _) fun s _ ↦ ⟨mem_univ _, hγ s⟩

/-- The flow solves the equation. -/
theorem hasDerivAt_flow (t₀ y : ℝ) (x : CInfPer) (s : ℝ) :
    HasDerivAt (fun r ↦ MaximalFlow.flow vf univ (r, t₀, y, x))
      (x (MaximalFlow.flow vf univ (s, t₀, y, x))) s :=
  (MaximalFlow.isSol_flow locallyLipschitzY_vf (t₀ := t₀) (y₀ := y) (p := x) s
    (mem_dom s t₀ y x)).2

theorem flow_self (t₀ y : ℝ) (x : CInfPer) : MaximalFlow.flow vf univ (t₀, t₀, y, x) = y := by
  obtain ⟨I, γ, hI, hIc, ht₀, -, hγ, hsol⟩ := mem_dom t₀ t₀ y x
  simp only at ht₀ hγ hsol
  rw [← hγ]
  exact MaximalFlow.flow_eq locallyLipschitzY_vf hI hIc ht₀ ht₀ hsol

theorem Fl_zero (y : ℝ) (x : CInfPer) : Fl 0 y x = y := flow_self 0 y x

theorem hasDerivAt_Fl (y : ℝ) (x : CInfPer) (s : ℝ) :
    HasDerivAt (fun r ↦ Fl r y x) (x (Fl s y x)) s :=
  hasDerivAt_flow 0 y x s

/-- **The flow property** `Fl^x_{s + t} = Fl^x_s ∘ Fl^x_t`. -/
theorem Fl_add (s t y : ℝ) (x : CInfPer) : Fl (s + t) y x = Fl s (Fl t y x) x := by
  have hγ : ∀ r, HasDerivAt (fun r ↦ Fl (r + t) y x) (x (Fl (r + t) y x)) r := fun r ↦
    (hasDerivAt_Fl y x (r + t)).comp_add_const r t
  have h := flow_eq_of_hasDerivAt hγ s 0
  simp only [zero_add] at h
  exact h.symm

/-- **Rescaling**: `Fl^{c x}_t = Fl^x_{c t}`. -/
theorem Fl_smul (c t y : ℝ) (x : CInfPer) : Fl t y (c • x) = Fl (c * t) y x := by
  have hγ : ∀ r, HasDerivAt (fun r ↦ Fl (c * r) y x) ((c • x) (Fl (c * r) y x)) r := fun r ↦ by
    have h := (hasDerivAt_Fl y x (c * r)).comp r ((hasDerivAt_id r).const_mul c)
    simp only [mul_one] at h
    exact h.congr_deriv (by change x (Fl (c * r) y x) * c = c * x (Fl (c * r) y x); ring)
  have h := flow_eq_of_hasDerivAt hγ t 0
  simp only [mul_zero, Fl_zero] at h
  exact h

/-- **Periodicity** `Fl^x_t(y + 1) = Fl^x_t(y) + 1`. -/
theorem Fl_add_one (t y : ℝ) (x : CInfPer) : Fl t (y + 1) x = Fl t y x + 1 := by
  have hγ : ∀ r, HasDerivAt (fun r ↦ Fl r y x + 1) (x (Fl r y x + 1)) r := fun r ↦ by
    rw [x.periodic]
    exact (hasDerivAt_Fl y x r).add_const 1
  have h := flow_eq_of_hasDerivAt hγ t 0
  simp only [Fl_zero] at h
  exact h

/-! ### The exponential function -/

theorem smoothMBOn_Fl_line (t : ℝ) (x : CInfPer) : SmoothMBOn (fun y ↦ Fl t y x) univ := fun k ↦ by
  have hin : ContDiffMBOn k (fun y : ℝ ↦ (t, (0 : ℝ), y, x)) univ :=
    (contDiffMBOn_const k t _).prodMk isOpen_univ ((contDiffMBOn_const k (0 : ℝ) _).prodMk
      isOpen_univ ((smoothMBOn_id _ k).prodMk isOpen_univ (contDiffMBOn_const k x _)))
  exact ContDiffMBOn.comp isOpen_univ isOpen_univ (smoothMBOn_flow k) hin (mapsTo_univ _ _)

theorem contDiff_Fl (t : ℝ) (x : CInfPer) : ContDiff ℝ ∞ (fun y ↦ Fl t y x) :=
  contDiffOn_univ.1 ((smoothMBOn_iff_contDiffOn isOpen_univ).1 (smoothMBOn_Fl_line t x))

/-- `exp(x) = Fl^x_1 − id`, a periodic function. -/
def expMap (x : CInfPer) : CInfPer :=
  CInfPer.mk (fun y ↦ Fl 1 y x - y) ((contDiff_Fl 1 x).sub contDiff_id) fun y ↦ by
    change Fl 1 (y + 1) x - (y + 1) = Fl 1 y x - y
    rw [Fl_add_one]; ring

theorem expMap_apply (x : CInfPer) (y : ℝ) : expMap x y = Fl 1 y x - y := rfl

theorem lift_expMap (x : CInfPer) : lift (expMap x) = fun y ↦ Fl 1 y x := by
  funext y
  simp only [lift, expMap_apply]
  ring

/-- `Fl^x_1` is a diffeomorphism of `ℝ`, with inverse `Fl^x_{-1}`. -/
theorem expMap_mem (x : CInfPer) : expMap x ∈ domain := by
  rw [mem_domain_iff]
  refine ⟨fun z ↦ Fl (-1) z x, (contDiff_Fl (-1) x).differentiable (by simp), fun z ↦ ?_⟩
  rw [lift_expMap]
  change Fl (-1) (Fl 1 z x) x = z
  rw [← Fl_add, neg_add_cancel, Fl_zero]

/-- **`exp` is smooth** into `C^∞_per`. -/
theorem smoothMBOn_expMap : SmoothMBOn expMap univ := by
  have hF : SmoothMBOn (fun p : CInfPer × ℝ ↦ MaximalFlow.flow vf univ (1, 0, p.2, p.1) - p.2)
      (univ ×ˢ univ) := fun k ↦ by
    have hin : ContDiffMBOn k (fun p : CInfPer × ℝ ↦ ((1 : ℝ), (0 : ℝ), p.2, p.1))
        (univ ×ˢ univ) :=
      (contDiffMBOn_const k (1 : ℝ) _).prodMk (isOpen_univ.prod isOpen_univ)
        ((contDiffMBOn_const k (0 : ℝ) _).prodMk (isOpen_univ.prod isOpen_univ)
          ((((ContinuousLinearMap.snd ℝ CInfPer ℝ).contDiffMBOn k univ).mono (subset_univ _)).prodMk
            (isOpen_univ.prod isOpen_univ)
            (((ContinuousLinearMap.fst ℝ CInfPer ℝ).contDiffMBOn k univ).mono (subset_univ _))))
    exact (ContDiffMBOn.comp (isOpen_univ.prod isOpen_univ) isOpen_univ (smoothMBOn_flow k) hin
      (mapsTo_univ _ _)).sub (isOpen_univ.prod isOpen_univ)
        (((ContinuousLinearMap.snd ℝ CInfPer ℝ).contDiffMBOn k univ).mono (subset_univ _))
  exact smoothMBOn_of_uncurry isOpen_univ hF fun _ _ _ ↦ rfl

/-- **The exponential function of `\widetilde{Diff}⁺(S¹)`**, `exp(x) = Fl^x_1`. -/
def exp (x : CInfPer) : CoverGroup := ⟨expMap x, expMap_mem x⟩

/-- Evaluation at `y`, as a continuous linear functional on `C^∞_per`. -/
def evalCLM (y : ℝ) : CInfPer →L[ℝ] ℝ :=
  (BoundedContinuousFunction.evalCLM ℝ y).comp (derivCLM 0)

@[simp] theorem evalCLM_apply (y : ℝ) (u : CInfPer) : evalCLM y u = u y := rfl

/-- **`\widetilde{Diff}⁺(S¹)` has an exponential function** ([GN26, §13.3]):
`exp(x) = Fl^x_1`, the time-one flow of the periodic vector field `x ∂_y`. -/
theorem isExp_exp : MBLieGroup.IsExp CInfPer exp where
  smooth := smoothMBM_of_val_comp DiffCircle.Ω (g := exp) fun k ↦
    (contMDiffMBOn_iff_contDiffMBOn isOpen_univ).2 (smoothMBOn_expMap k)
  map_add_smul x s t := by
    apply Subtype.ext
    rw [CoverGroup.coe_mul]
    apply lift_injective
    rw [lift_comp]
    change lift (expMap ((s + t) • x)) = lift (expMap (s • x)) ∘ lift (expMap (t • x))
    rw [lift_expMap, lift_expMap, lift_expMap]
    funext y
    simp only [Function.comp_apply, Fl_smul, mul_one]
    exact Fl_add s t y x
  dMB_chart x := by
    have hc : (fun y ↦ chartAt CInfPer (1 : CoverGroup) (exp y)) = expMap := rfl
    rw [hc]
    ext y
    have hd := (smoothMBOn_expMap 1).hasDirDerivAt (mem_univ 0) x
    have hcomp := ((evalCLM y).contDiffMBOn 1 univ).hasDirDerivAt_comp isOpen_univ hd
      (mem_univ _)
    have h0 : Fl 1 y (0 : CInfPer) = y := by
      rw [← zero_smul ℝ x, Fl_smul, zero_mul, Fl_zero]
    have h2 : HasDirDerivAt (fun u ↦ evalCLM y (expMap u)) 0 x (x y) := by
      have h1 := hasDirDerivAt_one (hasDerivAt_Fl y x 0)
      rw [Fl_zero] at h1
      unfold HasDirDerivAt at h1 ⊢
      refine h1.congr fun t ↦ ?_
      simp only [evalCLM_apply, expMap_apply, zero_add, smul_eq_mul, mul_one, h0, Fl_smul,
        Fl_zero]
      ring
    calc (dMB expMap (0, x)) y = evalCLM y (dMB expMap (0, x)) := rfl
      _ = dMB (fun u ↦ evalCLM y (expMap u)) (0, x) := by
        rw [show (fun u ↦ evalCLM y (expMap u)) = ⇑(evalCLM y) ∘ expMap from rfl, hcomp.dMB_eq,
          ((evalCLM y).hasDirDerivAt _ _).dMB_eq]
      _ = x y := h2.dMB_eq

end LocallyConvex.LieGroups.CircleCover
