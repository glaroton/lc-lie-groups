/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Regular.Primitive
public import LocallyConvexLieGroups.Regular.Local
public import LocallyConvexAnalysis.ODE.FixedPointParam
public import LocallyConvexAnalysis.MappingSpace.Pushforward

/-!
# Differential equations driven by continuous curves of fields

Let `W` be a locally convex space (of "fields"), `F` a Banach space and `f : W × F → F`, smooth on
`N × B(z₀, 3r)` for an open set `N ⊆ W`, bounded by `r` and `1/2`-Lipschitz in the second variable
there. For a curve `ξ ∈ C([0, 1], N)` and `y ∈ B(z₀, r)`, the equation

  `z'(t) = f(ξ(t), z(t))`, `z(0) = y`,

has a unique solution `z ∈ C([0, 1], B̄(z₀, 2r))`, the fixed point of the Picard operator
`Pic((ξ, y), z)(t) = y + ∫₀ᵗ f(ξ(s), z(s)) ds` on `C([0, 1], F)`. The operator is a superposition
operator followed by the primitive, hence smooth in `((ξ, y), z)`, and a uniform family of
`1/2`-contractions; by the fixed points with locally convex parameters of lc-analysis
([GN26, Proposition 2.3.27(a)]) the solution is smooth in `(ξ, y)`. The time dependence of the
equation is only continuous, which is why this is not a case of the flows with parameters of
[GN26, Theorem 2.4.34].

The spaces live in `Type`, as do the superposition operators on `C([0, 1], E)` of lc-analysis.

This generalizes the Picard argument for the circle (`CircleCover/Regular.lean`), and is used for
the flows of time dependent vector fields on compact manifolds.

## Main definitions

* `ParamODE.IsData f N z₀ r`: the hypotheses on `f`.
* `ParamODE.Pic`: the Picard operator; `ParamODE.sol`: its fixed point.

## Main results

* `ParamODE.smoothMBOn_sol`: the solution is smooth in `(ξ, y)`.
* `ParamODE.sol_apply`, `ParamODE.hasDerivWithinAt_sol`: it solves the equation.
* `ParamODE.eq_sol`: uniqueness among curves with values in `B̄(z₀, 2r)` solving the integral
  equation.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function Metric
open scoped Topology NNReal unitInterval
open LocallyConvex.Analysis
open LocallyConvex.LieGroups.MBLieGroup (extendCurve valIn)

noncomputable section

namespace LocallyConvex.LieGroups.ParamODE

variable {W : Type} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] [T2Space W]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-! ### Curves of pairs and constant curves -/

variable (W F) in
/-- The pairing `C(I, W) × C(I, F) → C(I, W × F)`. -/
def pairCLM : C(I, W) × C(I, F) →L[ℝ] C(I, W × F) where
  toFun p := p.1.prodMk p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := ContinuousMap.continuous_of_continuous_uncurry _ <| by
    have h1 : Continuous fun q : (C(I, W) × C(I, F)) × I ↦ q.1.1 q.2 :=
      continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd)
    have h2 : Continuous fun q : (C(I, W) × C(I, F)) × I ↦ q.1.2 q.2 :=
      continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd)
    exact h1.prodMk h2

omit [LocallyConvexSpace ℝ W] [T2Space W] [CompleteSpace F] in
@[simp] theorem pairCLM_apply (p : C(I, W) × C(I, F)) (s : I) :
    pairCLM W F p s = (p.1 s, p.2 s) := rfl

variable (F) in
/-- Constant curves, `y ↦ (t ↦ y)`. -/
def constCLM : F →L[ℝ] C(I, F) where
  toFun := ContinuousMap.const I
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := ContinuousMap.continuous_const'

omit [CompleteSpace F] in
@[simp] theorem constCLM_apply (y : F) (s : I) : constCLM F y s = y := rfl

/-! ### The hypotheses -/

/-- **The data of the equation `z' = f(ξ(t), z)`**: `f` is smooth on `N × B(z₀, 3r)`, bounded by
`r` and `1/2`-Lipschitz in `z` there. -/
structure IsData (f : W × F → F) (N : Set W) (z₀ : F) (r : ℝ) : Prop where
  isOpen : IsOpen N
  pos : 0 < r
  smooth : SmoothMBOn f (N ×ˢ ball z₀ (3 * r))
  bound : ∀ w ∈ N, ∀ z ∈ ball z₀ (3 * r), ‖f (w, z)‖ ≤ r
  lip : ∀ w ∈ N, ∀ z ∈ ball z₀ (3 * r), ∀ z' ∈ ball z₀ (3 * r),
    ‖f (w, z) - f (w, z')‖ ≤ 1 / 2 * ‖z - z'‖

variable {f : W × F → F} {N : Set W} {z₀ : F} {r : ℝ}

/-- The domain `N × B(z₀, 3r)` of `f`. -/
abbrev dom (N : Set W) (z₀ : F) (r : ℝ) : Set (W × F) := N ×ˢ ball z₀ (3 * r)

/-- The parameters: `ξ ∈ C(I, N)` and `y ∈ B(z₀, r)`. -/
abbrev par (N : Set W) (z₀ : F) (r : ℝ) : Set (C(I, W) × F) := valIn N ×ˢ ball z₀ r

omit [AddCommGroup W] [Module ℝ W] [IsTopologicalAddGroup W] [ContinuousSMul ℝ W]
  [LocallyConvexSpace ℝ W] [T2Space W] [NormedSpace ℝ F] [CompleteSpace F] in
theorem isOpen_par (hN : IsOpen N) : IsOpen (par N z₀ r) :=
  (MBLieGroup.isOpen_valIn hN).prod isOpen_ball

omit [NormedSpace ℝ F] [CompleteSpace F] in
theorem isClosed_valuedIn_closedBall (z₀ : F) (ρ : ℝ) :
    IsClosed (valuedIn I (closedBall z₀ ρ)) := by
  have : valuedIn I (closedBall z₀ ρ) = ⋂ s : I, (fun z : C(I, F) ↦ z s) ⁻¹' closedBall z₀ ρ := by
    ext z; simp [valuedIn]
  rw [this]
  exact isClosed_iInter fun s ↦ isClosed_closedBall.preimage (continuous_eval_const s)

/-! ### The Picard operator -/

/-- `s ↦ f(ξ(s), z(s))`. -/
def field (f : W × F → F) (N : Set W) (z₀ : F) (r : ℝ) (ξ : C(I, W)) (z : C(I, F)) : C(I, F) :=
  pushforward I f (dom N z₀ r) (pairCLM W F (ξ, z))

omit [LocallyConvexSpace ℝ W] [T2Space W] [CompleteSpace F] in
theorem field_apply (hf : IsData f N z₀ r) {ξ : C(I, W)} (hξ : ξ ∈ valIn N) {z : C(I, F)}
    (hz : z ∈ valuedIn I (ball z₀ (3 * r))) (s : I) :
    field f N z₀ r ξ z s = f (ξ s, z s) :=
  pushforward_apply (hf.smooth 0).continuousOn (fun s ↦ ⟨hξ s, hz s⟩) s

/-- **The Picard operator** `Pic((ξ, y), z)(t) = y + ∫₀ᵗ f(ξ(s), z(s)) ds`. -/
def Pic (f : W × F → F) (N : Set W) (z₀ : F) (r : ℝ) (q : (C(I, W) × F) × C(I, F)) : C(I, F) :=
  constCLM F q.1.2 + primitiveCLM (field f N z₀ r q.1.1 q.2)

omit [LocallyConvexSpace ℝ W] [T2Space W] [CompleteSpace F] in
theorem Pic_apply (q : (C(I, W) × F) × C(I, F)) (t : I) :
    Pic f N z₀ r q t = q.1.2 + ∫ s in (0 : ℝ)..t, extendCurve (field f N z₀ r q.1.1 q.2) s := by
  simp [Pic, primitiveCLM_apply]

omit [CompleteSpace F] in
theorem smoothMBOn_Pic (hf : IsData f N z₀ r) :
    SmoothMBOn (Pic f N z₀ r) (par N z₀ r ×ˢ valuedIn I (ball z₀ (3 * r))) := fun k ↦ by
  set L : (C(I, W) × F) × C(I, F) →L[ℝ] C(I, W × F) :=
    (pairCLM W F).comp (((ContinuousLinearMap.fst ℝ C(I, W) F).comp
      (ContinuousLinearMap.fst ℝ (C(I, W) × F) C(I, F))).prod
      (ContinuousLinearMap.snd ℝ (C(I, W) × F) C(I, F)))
  set A : (C(I, W) × F) × C(I, F) →L[ℝ] C(I, F) :=
    (constCLM F).comp ((ContinuousLinearMap.snd ℝ C(I, W) F).comp
      (ContinuousLinearMap.fst ℝ (C(I, W) × F) C(I, F)))
  have hD : IsOpen (dom N z₀ r) := hf.isOpen.prod isOpen_ball
  have hS : IsOpen (par N z₀ r ×ˢ valuedIn I (ball z₀ (3 * r))) :=
    (isOpen_par hf.isOpen).prod (isOpen_valuedIn isOpen_ball)
  have hpf : ContDiffMBOn k (fun q ↦ pushforward I f (dom N z₀ r) (L q))
      (par N z₀ r ×ˢ valuedIn I (ball z₀ (3 * r))) := by
    have h := ContDiffMBOn.comp_clm L (isOpen_valuedIn hD)
      (contDiffMBOn_pushforward k hD (hf.smooth k))
    exact h.mono fun q hq s ↦ ⟨hq.1.1 s, hq.2 s⟩
  have hJ := ContDiffMBOn.comp hS isOpen_univ
    ((primitiveCLM (E := F)).contDiffMBOn k univ) hpf (mapsTo_univ _ _)
  refine ContDiffMBOn.congr_of_isOpen hS (fun q _ ↦ ?_)
    (((A.contDiffMBOn k _)).add hS hJ)
  rfl

/-! ### The contraction -/

omit [LocallyConvexSpace ℝ W] [T2Space W] [CompleteSpace F] in
theorem norm_field_sub_le (hf : IsData f N z₀ r) {ξ : C(I, W)} (hξ : ξ ∈ valIn N)
    {z z' : C(I, F)} (hz : z ∈ valuedIn I (ball z₀ (3 * r)))
    (hz' : z' ∈ valuedIn I (ball z₀ (3 * r))) :
    ‖field f N z₀ r ξ z - field f N z₀ r ξ z'‖ ≤ 1 / 2 * ‖z - z'‖ := by
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun s ↦ ?_
  rw [ContinuousMap.sub_apply, field_apply hf hξ hz, field_apply hf hξ hz']
  refine (hf.lip _ (hξ s) _ (hz s) _ (hz' s)).trans ?_
  gcongr
  exact (z - z').norm_coe_le_norm s

omit [LocallyConvexSpace ℝ W] [T2Space W] [CompleteSpace F] in
theorem norm_field_le (hf : IsData f N z₀ r) {ξ : C(I, W)} (hξ : ξ ∈ valIn N)
    {z : C(I, F)} (hz : z ∈ valuedIn I (ball z₀ (3 * r))) : ‖field f N z₀ r ξ z‖ ≤ r :=
  (ContinuousMap.norm_le _ hf.pos.le).2 fun s ↦ by
    rw [field_apply hf hξ hz]; exact hf.bound _ (hξ s) _ (hz s)

omit [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] [T2Space W]
  [CompleteSpace F] in
theorem closedBall_subset_ball' (hf : IsData f N z₀ r) :
    closedBall z₀ (2 * r) ⊆ ball z₀ (3 * r) :=
  closedBall_subset_ball (by linarith [hf.pos])

omit [LocallyConvexSpace ℝ W] [T2Space W] [CompleteSpace F] in
/-- **The Picard operators form a uniform family of `1/2`-contractions.** -/
theorem uniformContraction (hf : IsData f N z₀ r) :
    UniformContraction (Pic f N z₀ r) (par N z₀ r) (valuedIn I (ball z₀ (3 * r)))
      (valuedIn I (closedBall z₀ (2 * r))) (1 / 2 : ℝ≥0) where
  isOpen_param := isOpen_par hf.isOpen
  isOpen := isOpen_valuedIn isOpen_ball
  isClosed := isClosed_valuedIn_closedBall z₀ _
  nonempty := ⟨ContinuousMap.const I z₀, fun _ ↦ mem_closedBall_self (by linarith [hf.pos])⟩
  subset z hz s := closedBall_subset_ball' hf (hz s)
  lt_one := by rw [← NNReal.coe_lt_coe]; norm_num
  mapsTo p hp z hz t := by
    have hz' : z ∈ valuedIn I (ball z₀ (3 * r)) := fun s ↦ closedBall_subset_ball' hf (hz s)
    rw [mem_closedBall, dist_eq_norm]
    change ‖Pic f N z₀ r (p, z) t - z₀‖ ≤ 2 * r
    have h1 : ‖p.2 - z₀‖ < r := by rw [← dist_eq_norm]; exact hp.2
    have h2 : ‖primitiveCLM (field f N z₀ r p.1 z) t‖ ≤ r :=
      ((primitiveCLM (field f N z₀ r p.1 z)).norm_coe_le_norm t).trans
        ((norm_primitiveCLM_apply_le _).trans (norm_field_le hf hp.1 hz'))
    have he : Pic f N z₀ r (p, z) t - z₀ = (p.2 - z₀) + primitiveCLM (field f N z₀ r p.1 z) t := by
      simp only [Pic, ContinuousMap.add_apply, constCLM_apply]; abel
    rw [he]
    linarith [norm_add_le (p.2 - z₀) (primitiveCLM (field f N z₀ r p.1 z) t)]
  lipschitz p hp z hz z' hz' := by
    have h : Pic f N z₀ r (p, z) - Pic f N z₀ r (p, z') =
        primitiveCLM (field f N z₀ r p.1 z - field f N z₀ r p.1 z') := by
      simp only [Pic, map_sub]; abel
    rw [h]
    refine (norm_primitiveCLM_apply_le _).trans ?_
    simpa using norm_field_sub_le hf hp.1 hz hz'

/-! ### The solutions -/

/-- **The solution** of `z' = f(ξ(t), z)`, `z(0) = y`, on `[0, 1]`. -/
def sol (hf : IsData f N z₀ r) (p : C(I, W) × F) : C(I, F) := (uniformContraction hf).fixedPoint p

variable (hf : IsData f N z₀ r) {p : C(I, W) × F}

omit [LocallyConvexSpace ℝ W] [T2Space W] in
theorem sol_mem (hp : p ∈ par N z₀ r) : sol hf p ∈ valuedIn I (closedBall z₀ (2 * r)) :=
  (uniformContraction hf).fixedPoint_mem hp

omit [LocallyConvexSpace ℝ W] [T2Space W] in
theorem sol_mem_ball (hp : p ∈ par N z₀ r) : sol hf p ∈ valuedIn I (ball z₀ (3 * r)) :=
  fun s ↦ closedBall_subset_ball' hf (sol_mem hf hp s)

omit [LocallyConvexSpace ℝ W] [T2Space W] in
theorem Pic_sol (hp : p ∈ par N z₀ r) : Pic f N z₀ r (p, sol hf p) = sol hf p :=
  (uniformContraction hf).apply_fixedPoint hp

omit [LocallyConvexSpace ℝ W] [T2Space W] in
/-- **Uniqueness**: a curve in `B̄(z₀, 2r)` solving the integral equation is the solution. -/
theorem eq_sol (hp : p ∈ par N z₀ r) {z : C(I, F)} (hz : z ∈ valuedIn I (closedBall z₀ (2 * r)))
    (hPz : Pic f N z₀ r (p, z) = z) : z = sol hf p :=
  (uniformContraction hf).eq_fixedPoint hp hz hPz

/-- **The solution is smooth in `(ξ, y)`.** -/
theorem smoothMBOn_sol : SmoothMBOn (sol hf) (par N z₀ r) := fun k ↦
  UniformContraction.contDiffMBOn_fixedPoint_of_contDiffMBOn k (uniformContraction hf)
    (smoothMBOn_Pic hf k)

omit [LocallyConvexSpace ℝ W] [T2Space W] in
theorem sol_apply (hp : p ∈ par N z₀ r) (t : I) :
    sol hf p t = p.2 + ∫ s in (0 : ℝ)..t, extendCurve (field f N z₀ r p.1 (sol hf p)) s := by
  conv_lhs => rw [← Pic_sol hf hp]
  exact Pic_apply _ t

omit [LocallyConvexSpace ℝ W] [T2Space W] in
theorem sol_zero (hp : p ∈ par N z₀ r) : sol hf p 0 = p.2 := by
  rw [sol_apply hf hp]; simp

omit [LocallyConvexSpace ℝ W] [T2Space W] in
/-- **The solution solves the equation** on `[0, 1]`. -/
theorem hasDerivWithinAt_sol (hp : p ∈ par N z₀ r) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (extendCurve (sol hf p))
      (f (extendCurve p.1 t, extendCurve (sol hf p) t)) (Icc 0 1) t := by
  set g := extendCurve (field f N z₀ r p.1 (sol hf p))
  have hg : Continuous g := MBLieGroup.continuous_extendCurve _
  have hd : HasDerivAt (fun s ↦ p.2 + ∫ s' in (0 : ℝ)..s, g s') (g t) t :=
    (intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
      (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt).const_add _
  have hgt : g t = f (extendCurve p.1 t, extendCurve (sol hf p) t) := by
    simp only [g, MBLieGroup.extendCurve, IccExtend_of_mem _ _ ht]
    exact field_apply hf hp.1 (sol_mem_ball hf hp) _
  rw [← hgt]
  refine hd.hasDerivWithinAt.congr (fun s hs ↦ ?_) ?_
  · simp only [MBLieGroup.extendCurve, IccExtend_of_mem _ _ hs]
    exact sol_apply hf hp _
  · simp only [MBLieGroup.extendCurve, IccExtend_of_mem _ _ ht]
    exact sol_apply hf hp _

end LocallyConvex.LieGroups.ParamODE
