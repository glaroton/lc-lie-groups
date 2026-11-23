/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.CircleCover.Exponential
public import LocallyConvexLieGroups.Regular.Local
public import LocallyConvexLieGroups.Regular.Vector
public import LocallyConvexLieGroups.Regular.Primitive
public import LocallyConvexLieGroups.Regular.Interval
public import LocallyConvexAnalysis.ODE.FixedPointParam
public import LocallyConvexAnalysis.MappingSpace.Pushforward

/-!
# The universal cover of `Diff⁺(S¹)` is `C⁰`-regular

For `ξ ∈ C([0, 1], C^∞_per)` with `|ξ(t)'| < 1/4`, the equation `u' = -ξ(t)(u)`, `u(0) = y`, is
the fixed point of the Picard operator `Pic((ξ, y), u)(t) = y - ∫₀ᵗ ξ(r)(u(r)) dr` on
`C([0, 1], ℝ)`, a uniform family of contractions (constant `1/4`) which is smooth in
`((ξ, y), u)`: a superposition operator followed by the primitive. By lc-analysis's fixed points
with locally convex parameters ([GN26, Proposition 2.3.27(a)]), the solution `u_y` is smooth in
`(ξ, y)`, so `u_·(t) - id` is a smooth periodic function, smooth in `ξ`
(`smoothMBOn_of_uncurry`), and `u_·(t) ∈ Ω` since
`∂_y u_y(t) ≥ 2/3`. The evolution is `γ(t) = u_·(t)⁻¹`: with the flow property
`u_t = u_{s → t} ∘ u_s`, `γ(t)⁻¹ γ(r) = u_{r → t}` is the time-one map `Ψ` of the rescaled field
`ζ_{r → t}(w) = (t - r) ξ(r + w (t - r))`, and `ζ_{t + h → t} = h Z_h` with `Z_h → -ξ(t)`
(constant); so `δ(γ)(t) = dΨ(0, -ξ(t)) = ξ(t)`, the last step by comparison with the exponential
function. The local regularity criterion ([GN26, Lemma 6.1.4]) concludes. [GN26, §13.1] leaves
the regularity of diffeomorphism groups to be written; this is a direct proof for the circle.

## Main definitions

* `CircleCover.Pic`, `CircleCover.sol`: the Picard operator and its fixed point `u_y`.
* `CircleCover.flowPt ξ t = u_·(t) - id` and `CircleCover.cg ξ t ∈ \widetilde{Diff}⁺(S¹)`.
* `CircleCover.shiftField ξ s t`: the field of the flow from `s` to `t`.
* `CircleCover.evolCurve ξ t = (cg ξ t)⁻¹`: the evolution of `ξ`.

## Main results

* `CircleCover.smoothMBOn_sol`: the solution is smooth in `(ξ, y)`.
* `CircleCover.cg_eq_mul`: **the flow property** `u_t = u_{s → t} ∘ u_s`.
* `CircleCover.isEvolOn_evolCurve`: `δ(γ) = ξ` on `[0, 1]`.
* `CircleCover.isC0Regular`: **`\widetilde{Diff}⁺(S¹)` is `C⁰`-regular.**

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function
open scoped Topology NNReal unitInterval ContDiff
open LocallyConvex.Analysis LocallyConvex.Manifolds CInfPer DiffCircle
open LocallyConvex.LieGroups.MBLieGroup (extendCurve valIn)

noncomputable section

namespace LocallyConvex.LieGroups.CircleCover

/-! ### The Picard operator -/

/-- The pairing `C(I, C^∞_per) × C(I, ℝ) → C(I, C^∞_per × ℝ)`. -/
def pairCLM : C(I, CInfPer) × C(I, ℝ) →L[ℝ] C(I, CInfPer × ℝ) where
  toFun p := p.1.prodMk p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := ContinuousMap.continuous_of_continuous_uncurry _ <| by
    have h1 : Continuous fun q : (C(I, CInfPer) × C(I, ℝ)) × I ↦ q.1.1 q.2 :=
      continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd)
    have h2 : Continuous fun q : (C(I, CInfPer) × C(I, ℝ)) × I ↦ q.1.2 q.2 :=
      continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd)
    exact h1.prodMk h2

@[simp] theorem pairCLM_apply (p : C(I, CInfPer) × C(I, ℝ)) (s : I) :
    pairCLM p s = (p.1 s, p.2 s) := rfl

/-- The parameters `(ξ, y)`: a time-dependent field and an initial value. -/
abbrev Par : Type := C(I, CInfPer) × ℝ

/-- `r ↦ ξ(r)(u(r))`. -/
def field (ξ : C(I, CInfPer)) (u : C(I, ℝ)) : C(I, ℝ) :=
  pushforward I ev univ (pairCLM (ξ, u))

theorem field_apply (ξ : C(I, CInfPer)) (u : C(I, ℝ)) (r : I) : field ξ u r = ξ r (u r) := by
  rw [field, pushforward_apply (smoothMBOn_ev 0).continuousOn (fun _ ↦ mem_univ _)]
  rfl

/-- **The Picard operator** of `u' = -ξ(t)(u)`, `u(0) = y`:
`Pic((ξ, y), u)(t) = y - ∫₀ᵗ ξ(r)(u(r)) dr`. -/
def Pic (q : Par × C(I, ℝ)) : C(I, ℝ) :=
  q.1.2 • (1 : C(I, ℝ)) - LieGroups.primitiveCLM (field q.1.1 q.2)

theorem Pic_apply (q : Par × C(I, ℝ)) (t : I) :
    Pic q t = q.1.2 - ∫ r in (0 : ℝ)..t, extendCurve (field q.1.1 q.2) r := by
  simp [Pic, LieGroups.primitiveCLM_apply]

theorem smoothMBOn_Pic : SmoothMBOn Pic univ := fun k ↦ by
  set L : Par × C(I, ℝ) →L[ℝ] C(I, CInfPer × ℝ) :=
    pairCLM.comp (((ContinuousLinearMap.fst ℝ C(I, CInfPer) ℝ).comp
      (ContinuousLinearMap.fst ℝ Par C(I, ℝ))).prod (ContinuousLinearMap.snd ℝ Par C(I, ℝ)))
  set A : Par × C(I, ℝ) →L[ℝ] C(I, ℝ) :=
    ((ContinuousLinearMap.snd ℝ C(I, CInfPer) ℝ).comp
      (ContinuousLinearMap.fst ℝ Par C(I, ℝ))).smulRight (1 : C(I, ℝ))
  have hpf : ContDiffMBOn k (fun q ↦ pushforward I ev univ (L q)) univ := by
    have h := ContDiffMBOn.comp_clm L (isOpen_valuedIn isOpen_univ)
      (contDiffMBOn_pushforward k isOpen_univ (smoothMBOn_ev k))
    have hU : L ⁻¹' valuedIn I (univ : Set (CInfPer × ℝ)) = univ :=
      eq_univ_of_forall fun _ _ ↦ mem_univ _
    rwa [hU] at h
  have hJ := ContDiffMBOn.comp isOpen_univ isOpen_univ
    ((LieGroups.primitiveCLM (E := ℝ)).contDiffMBOn k univ) hpf (mapsTo_univ _ _)
  refine ContDiffMBOn.congr_of_isOpen isOpen_univ (fun q _ ↦ ?_)
    (((A.contDiffMBOn k univ)).sub isOpen_univ hJ)
  rfl

/-! ### The contraction -/

/-- Fields with `|ξ'| < 1/4`. -/
def W : Set CInfPer := {x | seminorm 1 x < 1 / 4}

theorem isOpen_W : IsOpen W :=
  isOpen_lt ((continuous_norm).comp (continuous_derivBCF 1)) continuous_const

/-- The parameter domain `{(ξ, y) : |ξ(t)'| < 1/4}`. -/
def parDom : Set Par := valIn W ×ˢ univ

theorem isOpen_parDom : IsOpen parDom := (MBLieGroup.isOpen_valIn isOpen_W).prod isOpen_univ

theorem norm_field_sub_le {ξ : C(I, CInfPer)} (hξ : ξ ∈ valIn W) (u v : C(I, ℝ)) :
    ‖field ξ u - field ξ v‖ ≤ 1 / 4 * ‖u - v‖ := by
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun r ↦ ?_
  rw [ContinuousMap.sub_apply, field_apply, field_apply, Real.norm_eq_abs]
  calc |ξ r (u r) - ξ r (v r)| ≤ seminorm 1 (ξ r) * |u r - v r| := by
        exact CInfPer.abs_sub_le (ξ r) (v r) (u r)
    _ ≤ 1 / 4 * ‖u - v‖ := by
        refine mul_le_mul (hξ r).le ?_ (abs_nonneg _) (by norm_num)
        rw [← Real.norm_eq_abs, ← ContinuousMap.sub_apply]
        exact (u - v).norm_coe_le_norm r

theorem uniformContraction :
    UniformContraction Pic parDom univ univ (1 / 4 : ℝ≥0) where
  isOpen_param := isOpen_parDom
  isOpen := isOpen_univ
  isClosed := isClosed_univ
  nonempty := univ_nonempty
  subset := subset_rfl
  lt_one := by
    rw [← NNReal.coe_lt_coe]; norm_num
  mapsTo _ _ := mapsTo_univ _ _
  lipschitz p hp u _ v _ := by
    have h : Pic (p, u) - Pic (p, v) = LieGroups.primitiveCLM (field p.1 v - field p.1 u) := by
      simp only [Pic, map_sub]; abel
    rw [h]
    refine (LieGroups.norm_primitiveCLM_apply_le _).trans ?_
    rw [norm_sub_rev]
    simpa using norm_field_sub_le hp.1 u v

/-! ### The solutions -/

/-- **The solution** of `u' = -ξ(t)(u)`, `u(0) = y`, on `[0, 1]`, for `|ξ'| < 1/4`. -/
def sol (p : Par) : C(I, ℝ) := uniformContraction.fixedPoint p

theorem Pic_sol {p : Par} (hp : p ∈ parDom) : Pic (p, sol p) = sol p :=
  uniformContraction.apply_fixedPoint hp

theorem eq_sol {p : Par} (hp : p ∈ parDom) {u : C(I, ℝ)} (hu : Pic (p, u) = u) : u = sol p :=
  uniformContraction.eq_fixedPoint hp (mem_univ _) hu

theorem smoothMBOn_sol : SmoothMBOn sol parDom := fun k ↦
  UniformContraction.contDiffMBOn_fixedPoint_of_contDiffMBOn k uniformContraction
    ((smoothMBOn_Pic k).mono (subset_univ _))

theorem mem_parDom {ξ : C(I, CInfPer)} (hξ : ξ ∈ valIn W) (y : ℝ) : (ξ, y) ∈ parDom :=
  ⟨hξ, mem_univ _⟩

theorem sol_add_one {ξ : C(I, CInfPer)} (hξ : ξ ∈ valIn W) (y : ℝ) :
    sol (ξ, y + 1) = sol (ξ, y) + 1 := by
  refine (eq_sol (mem_parDom hξ _) ?_).symm
  have hf : field ξ (sol (ξ, y) + 1) = field ξ (sol (ξ, y)) := by
    ext r
    simp only [field_apply, ContinuousMap.add_apply, ContinuousMap.one_apply]
    exact (ξ r).periodic _
  conv_rhs => rw [← Pic_sol (mem_parDom hξ y)]
  simp only [Pic, hf, add_smul, one_smul]
  abel

theorem sol_zero {p : Par} (hp : p ∈ parDom) : sol p 0 = p.2 := by
  rw [← Pic_sol hp, Pic_apply]
  simp

/-- `‖u_{y'} - u_y‖ ≤ 4/3 |y' - y|`. -/
theorem norm_sol_sub_le {ξ : C(I, CInfPer)} (hξ : ξ ∈ valIn W) (y y' : ℝ) :
    ‖sol (ξ, y') - sol (ξ, y)‖ ≤ 4 / 3 * |y' - y| := by
  set d := sol (ξ, y') - sol (ξ, y)
  have hd : d = (y' - y) • (1 : C(I, ℝ)) -
      LieGroups.primitiveCLM (field ξ (sol (ξ, y')) - field ξ (sol (ξ, y))) := by
    simp only [d]
    conv_lhs => rw [← Pic_sol (mem_parDom hξ y'), ← Pic_sol (mem_parDom hξ y)]
    simp only [Pic, map_sub, sub_smul]
    abel
  have hJ : ‖LieGroups.primitiveCLM (field ξ (sol (ξ, y')) - field ξ (sol (ξ, y)))‖ ≤
      1 / 4 * ‖d‖ :=
    (LieGroups.norm_primitiveCLM_apply_le _).trans (norm_field_sub_le hξ _ _)
  have h1 : ‖(y' - y) • (1 : C(I, ℝ))‖ ≤ |y' - y| := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (by simp)
  have : ‖d‖ ≤ |y' - y| + 1 / 4 * ‖d‖ := by
    calc ‖d‖ ≤ _ := by rw [hd]; exact norm_sub_le _ _
      _ ≤ _ := add_le_add h1 hJ
  linarith

/-- `u_{y'}(t) - u_y(t) ≥ 2/3 (y' - y)` for `y ≤ y'`. -/
theorem sol_sub_ge {ξ : C(I, CInfPer)} (hξ : ξ ∈ valIn W) {y y' : ℝ} (hy : y ≤ y') (t : I) :
    2 / 3 * (y' - y) ≤ sol (ξ, y') t - sol (ξ, y) t := by
  have h := norm_sol_sub_le hξ y y'
  have hJ : ‖LieGroups.primitiveCLM (field ξ (sol (ξ, y')) - field ξ (sol (ξ, y)))‖ ≤
      1 / 4 * ‖sol (ξ, y') - sol (ξ, y)‖ :=
    (LieGroups.norm_primitiveCLM_apply_le _).trans (norm_field_sub_le hξ _ _)
  have he : sol (ξ, y') t - sol (ξ, y) t = (y' - y) -
      LieGroups.primitiveCLM (field ξ (sol (ξ, y')) - field ξ (sol (ξ, y))) t := by
    conv_lhs => rw [← Pic_sol (mem_parDom hξ y'), ← Pic_sol (mem_parDom hξ y)]
    simp only [Pic, map_sub, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, smul_eq_mul, mul_one]
    ring
  have hle := (LieGroups.primitiveCLM (field ξ (sol (ξ, y')) -
    field ξ (sol (ξ, y)))).norm_coe_le_norm t
  rw [Real.norm_eq_abs] at hle
  rw [abs_of_nonneg (sub_nonneg.2 hy)] at h
  rw [he]
  have := le_abs_self (LieGroups.primitiveCLM (field ξ (sol (ξ, y')) - field ξ (sol (ξ, y))) t)
  linarith

/-- `y ↦ u_y(t)` is smooth. -/
theorem contDiff_sol {ξ : C(I, CInfPer)} (hξ : ξ ∈ valIn W) (t : I) :
    ContDiff ℝ ∞ fun y ↦ sol (ξ, y) t := by
  have hin : SmoothMBOn (fun y : ℝ ↦ ((ξ, y) : Par)) univ := fun k ↦
    (contDiffMBOn_const k ξ _).prodMk isOpen_univ (smoothMBOn_id _ k)
  have h : SmoothMBOn (fun y : ℝ ↦ sol (ξ, y) t) univ := fun k ↦
    ContDiffMBOn.comp isOpen_univ isOpen_univ
      ((ContinuousMap.evalCLM ℝ t : C(I, ℝ) →L[ℝ] ℝ).contDiffMBOn k univ)
      (ContDiffMBOn.comp isOpen_univ isOpen_parDom (smoothMBOn_sol k) (hin k)
        fun y _ ↦ mem_parDom hξ y) (mapsTo_univ _ _)
  exact contDiffOn_univ.1 ((smoothMBOn_iff_contDiffOn isOpen_univ).1 h)

open scoped Classical in
/-- `u_·(t) - id`, a periodic function. -/
def flowPt (ξ : C(I, CInfPer)) (t : I) : CInfPer :=
  if hξ : ξ ∈ valIn W then
    CInfPer.mk (fun y ↦ sol (ξ, y) t - y) ((contDiff_sol hξ t).sub contDiff_id) fun y ↦ by
      change sol (ξ, y + 1) t - (y + 1) = sol (ξ, y) t - y
      rw [sol_add_one hξ]
      simp only [ContinuousMap.add_apply, ContinuousMap.one_apply]
      ring
  else 0

theorem flowPt_apply {ξ : C(I, CInfPer)} (hξ : ξ ∈ valIn W) (t : I) (y : ℝ) :
    flowPt ξ t y = sol (ξ, y) t - y := by
  simp only [flowPt, hξ, ↓reduceDIte]; rfl

theorem lift_flowPt {ξ : C(I, CInfPer)} (hξ : ξ ∈ valIn W) (t : I) :
    lift (flowPt ξ t) = fun y ↦ sol (ξ, y) t := by
  funext y
  simp only [lift, flowPt_apply hξ]
  ring

theorem flowPt_mem {ξ : C(I, CInfPer)} (hξ : ξ ∈ valIn W) (t : I) : flowPt ξ t ∈ domain := by
  intro y
  set f := fun y ↦ sol (ξ, y) t
  have hf : HasDerivAt f (deriv f y) y :=
    ((contDiff_sol hξ t).differentiable (by simp)).differentiableAt.hasDerivAt
  have hd : deriv (flowPt ξ t) y = deriv f y - 1 := by
    have : (flowPt ξ t : ℝ → ℝ) = fun y ↦ f y - y := funext (flowPt_apply hξ t)
    rw [this]
    exact (hf.sub (hasDerivAt_id y)).deriv
  rw [hd]
  have hge : 2 / 3 ≤ deriv f y := by
    have ht := (hasDerivAt_iff_tendsto_slope.1 hf).mono_left
      (nhdsWithin_mono y (s := Ioi y) fun z hz ↦ mem_compl_singleton_iff.2 (ne_of_gt hz))
    refine ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun z (hz : y < z) ↦ ?_)
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 hz)]
    exact sol_sub_ge hξ hz.le t
  linarith

/-! ### The flow from `s` to `t` -/

theorem smul_mem_W {x : CInfPer} (hx : x ∈ W) {c : ℝ} (hc : |c| ≤ 1) : c • x ∈ W := by
  change seminorm 1 (c • x) < 1 / 4
  rw [map_smul_eq_mul, Real.norm_eq_abs]
  have h0 := apply_nonneg (seminorm 1) x
  calc |c| * seminorm 1 x ≤ 1 * seminorm 1 x := mul_le_mul_of_nonneg_right hc h0
    _ < 1 / 4 := by rw [one_mul]; exact hx

theorem abs_sub_le_one {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    |t - s| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]

theorem mem_Icc_of_mem {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    {w : ℝ} (hw : w ∈ Icc (0 : ℝ) 1) : s + w * (t - s) ∈ Icc (0 : ℝ) 1 := by
  constructor <;> nlinarith [hs.1, hs.2, ht.1, ht.2, hw.1, hw.2]

/-- `ζ(w) = (t - s) ξ(s + w (t - s))`: the field of the flow from `s` to `t`. -/
def shiftField (ξ : C(I, CInfPer)) (s t : ℝ) : C(I, CInfPer) :=
  ⟨fun w ↦ (t - s) • extendCurve ξ (s + w * (t - s)), by
    have h : Continuous fun w : I ↦ s + (w : ℝ) * (t - s) := by fun_prop
    exact ((MBLieGroup.continuous_extendCurve ξ).comp h).const_smul (t - s)⟩

theorem shiftField_apply (ξ : C(I, CInfPer)) (s t : ℝ) (w : I) :
    shiftField ξ s t w = (t - s) • extendCurve ξ (s + w * (t - s)) := rfl

theorem shiftField_mem {ξ : C(I, CInfPer)} (hξ : ξ ∈ valIn W) {s t : ℝ} (hst : |t - s| ≤ 1) :
    shiftField ξ s t ∈ valIn W := fun w ↦ by
  rw [shiftField_apply]
  exact smul_mem_W (hξ _) hst

theorem extendCurve_field (ξ : C(I, CInfPer)) (u : C(I, ℝ)) (τ : ℝ) :
    extendCurve (field ξ u) τ = extendCurve ξ τ (extendCurve u τ) := by
  rw [MBLieGroup.extendCurve_apply, field_apply]; rfl

theorem extendCurve_sol {ξ : C(I, CInfPer)} (hξ : ξ ∈ valIn W) (y : ℝ) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) 1) :
    extendCurve (sol (ξ, y)) τ = y - ∫ r in (0 : ℝ)..τ, extendCurve (field ξ (sol (ξ, y))) r := by
  rw [MBLieGroup.extendCurve_apply, projIcc_of_mem _ hτ, ← Pic_sol (mem_parDom hξ y), Pic_apply]
  rw [Pic_sol (mem_parDom hξ y)]

/-- **The flow property**: `w ↦ u_y(s + w (t - s))` solves the equation of `shiftField ξ s t`. -/
theorem sol_shiftField {ξ : C(I, CInfPer)} (hξ : ξ ∈ valIn W) (y : ℝ) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (w : I) :
    sol (shiftField ξ s t, extendCurve (sol (ξ, y)) s) w =
      extendCurve (sol (ξ, y)) (s + w * (t - s)) := by
  set U := extendCurve (sol (ξ, y))
  set F := extendCurve (field ξ (sol (ξ, y)))
  have hF : Continuous F := MBLieGroup.continuous_extendCurve _
  set v : C(I, ℝ) := ⟨fun w ↦ U (s + w * (t - s)), (MBLieGroup.continuous_extendCurve _).comp
    (continuous_const.add (continuous_subtype_val.mul continuous_const))⟩
  have hv : v = sol (shiftField ξ s t, U s) := by
    refine eq_sol (mem_parDom (shiftField_mem hξ (abs_sub_le_one hs ht)) _) ?_
    ext w
    rw [Pic_apply]
    change U s - _ = U (s + w * (t - s))
    have hw := w.2
    have hcongr : ∀ ρ ∈ uIcc (0 : ℝ) w,
        extendCurve (field (shiftField ξ s t) v) ρ = (t - s) * F ((t - s) * ρ + s) := by
      intro ρ hρ
      rw [uIcc_of_le hw.1] at hρ
      have hρ1 : ρ ∈ Icc (0 : ℝ) 1 := ⟨hρ.1, hρ.2.trans hw.2⟩
      rw [MBLieGroup.extendCurve_apply, projIcc_of_mem _ hρ1, field_apply, shiftField_apply]
      simp only [v, ContinuousMap.coe_mk, CInfPer.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [show (t - s) * ρ + s = s + ρ * (t - s) by ring]
      simp only [F, extendCurve_field]
      rfl
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul,
      ← smul_eq_mul, intervalIntegral.smul_integral_comp_mul_add, mul_zero, zero_add,
      show (t - s) * w + s = s + w * (t - s) by ring]
    have hτ := mem_Icc_of_mem hs ht hw
    rw [show U s = _ from extendCurve_sol hξ y hs, show U (s + w * (t - s)) = _ from
      extendCurve_sol hξ y hτ, sub_sub,
      intervalIntegral.integral_add_adjacent_intervals (hF.intervalIntegrable _ _)
        (hF.intervalIntegrable _ _)]
  rw [← hv]
  rfl

open scoped Classical in
/-- The solution at time `t`, as an element of `\widetilde{Diff}⁺(S¹)`. -/
def cg (ξ : C(I, CInfPer)) (t : I) : CoverGroup :=
  if hξ : ξ ∈ valIn W then ⟨flowPt ξ t, flowPt_mem hξ t⟩ else 1

theorem coe_cg {ξ : C(I, CInfPer)} (hξ : ξ ∈ valIn W) (t : I) :
    (cg ξ t : CInfPer) = flowPt ξ t := by
  simp [cg, hξ]

theorem cg_zero {ξ : C(I, CInfPer)} (hξ : ξ ∈ valIn W) : cg ξ 0 = 1 := by
  refine Subtype.ext ?_
  rw [coe_cg hξ, CoverGroup.coe_one]
  ext y
  rw [flowPt_apply hξ, sol_zero (mem_parDom hξ y)]
  simp

/-- **`u_t = u_{s → t} ∘ u_s`** in `\widetilde{Diff}⁺(S¹)`. -/
theorem cg_eq_mul {ξ : C(I, CInfPer)} (hξ : ξ ∈ valIn W) (s t : I) :
    cg ξ t = cg (shiftField ξ s t) 1 * cg ξ s := by
  have hζ := shiftField_mem hξ (abs_sub_le_one s.2 t.2)
  refine Subtype.ext (lift_injective ?_)
  rw [CoverGroup.coe_mul, lift_comp, coe_cg hξ, coe_cg hζ, coe_cg hξ, lift_flowPt hξ,
    lift_flowPt hζ, lift_flowPt hξ]
  funext y
  simp only [Function.comp_apply]
  have h := sol_shiftField hξ y s.2 t.2 1
  rw [MBLieGroup.extendCurve_apply, projIcc_val] at h
  rw [h]
  simp only [Set.Icc.coe_one, one_mul, add_sub_cancel, MBLieGroup.extendCurve_apply, projIcc_val]

/-! ### The time-one map -/

/-- The time-one map `Ψ(ζ) = u_·(1) - id`. -/
def Ψ (ζ : C(I, CInfPer)) : CInfPer := flowPt ζ 1

theorem smoothMBOn_Ψ : SmoothMBOn Ψ (valIn W) := by
  have hF : SmoothMBOn (fun p : C(I, CInfPer) × ℝ ↦ sol p 1 - p.2) (valIn W ×ˢ univ) :=
    fun k ↦ (ContDiffMBOn.comp isOpen_parDom isOpen_univ
      ((ContinuousMap.evalCLM ℝ (1 : I) : C(I, ℝ) →L[ℝ] ℝ).contDiffMBOn k univ)
      (smoothMBOn_sol k) (mapsTo_univ _ _)).sub isOpen_parDom
      (((ContinuousLinearMap.snd ℝ C(I, CInfPer) ℝ).contDiffMBOn k univ).mono (subset_univ _))
  exact smoothMBOn_of_uncurry (MBLieGroup.isOpen_valIn isOpen_W) hF fun ζ hζ y ↦
    flowPt_apply hζ 1 y

theorem zero_mem_valIn : (0 : C(I, CInfPer)) ∈ valIn W := fun _ ↦ by
  change seminorm 1 0 < 1 / 4
  rw [map_zero]; norm_num

/-- For a constant field `-h x`, the solution is the flow of `h x`. -/
theorem sol_smul_const (x : CInfPer) {h : ℝ} (hh : |h| * seminorm 1 x < 1 / 4) (y : ℝ) :
    sol (h • -ContinuousMap.const I x, y) = ⟨fun w ↦ Fl w y (h • x),
      (continuous_iff_continuousAt.2 fun s ↦ (hasDerivAt_Fl y (h • x) s).continuousAt).comp
        continuous_subtype_val⟩ := by
  have hmem : h • -ContinuousMap.const I x ∈ valIn W := fun w ↦ by
    change seminorm 1 (h • -x) < 1 / 4
    rw [map_smul_eq_mul, map_neg_eq_map, Real.norm_eq_abs]; exact hh
  refine (eq_sol (mem_parDom hmem y) ?_).symm
  ext w
  rw [Pic_apply]
  change y - _ = Fl w y (h • x)
  have hcongr : ∀ r ∈ uIcc (0 : ℝ) w, extendCurve (field (h • -ContinuousMap.const I x)
      ⟨fun w ↦ Fl w y (h • x), (continuous_iff_continuousAt.2 fun s ↦
        (hasDerivAt_Fl y (h • x) s).continuousAt).comp continuous_subtype_val⟩) r =
      -((h • x) (Fl r y (h • x))) := by
    intro r hr
    rw [uIcc_of_le w.2.1] at hr
    have hr1 : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1, hr.2.trans w.2.2⟩
    rw [MBLieGroup.extendCurve_apply, projIcc_of_mem _ hr1, field_apply]
    simp
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_neg,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hasDerivAt_Fl y (h • x) s)
      (((h • x).contDiff.continuous.comp (continuous_iff_continuousAt.2 fun s ↦
        (hasDerivAt_Fl y (h • x) s).continuousAt)).intervalIntegrable _ _), Fl_zero]
  ring

theorem Ψ_smul_const (x : CInfPer) {h : ℝ} (hh : |h| * seminorm 1 x < 1 / 4) :
    Ψ (h • -ContinuousMap.const I x) = expMap (h • x) := by
  have hmem : h • -ContinuousMap.const I x ∈ valIn W := fun w ↦ by
    change seminorm 1 (h • -x) < 1 / 4
    rw [map_smul_eq_mul, map_neg_eq_map, Real.norm_eq_abs]; exact hh
  ext y
  rw [Ψ, flowPt_apply hmem, expMap_apply, sol_smul_const x hh]
  rfl

theorem Ψ_zero : Ψ 0 = 0 := by
  have h := Ψ_smul_const 0 (h := 0) (by simp)
  rw [zero_smul, zero_smul] at h
  rw [h]
  ext y
  rw [expMap_apply, ← zero_smul ℝ (0 : CInfPer), Fl_smul, zero_mul, Fl_zero]
  simp

/-- **`dΨ(0, -x) = x`** for constant fields. -/
theorem hasDirDerivAt_Ψ (x : CInfPer) : HasDirDerivAt Ψ 0 (-ContinuousMap.const I x) x := by
  have hE : HasDirDerivAt expMap 0 x x := by
    have h := (smoothMBOn_expMap 1).hasDirDerivAt (mem_univ 0) x
    have hd : dMB expMap (0, x) = x := isExp_exp.dMB_chart x
    rwa [hd] at h
  have hev : ∀ᶠ h in 𝓝 (0 : ℝ), |h| * seminorm 1 x < 1 / 4 := by
    have hc : Continuous fun h : ℝ ↦ |h| * seminorm 1 x := by fun_prop
    exact hc.continuousAt.eventually_lt continuousAt_const (by simp)
  have h0 : expMap 0 = 0 := by
    have := Ψ_smul_const x (h := 0) (by simp)
    rw [zero_smul, zero_smul, Ψ_zero] at this
    exact this.symm
  unfold HasDirDerivAt at hE ⊢
  refine hE.congr' ?_
  filter_upwards [nhdsWithin_le_nhds hev] with h hh
  rw [zero_add, zero_add, Ψ_smul_const x hh, Ψ_zero, h0]

/-! ### The logarithmic derivative -/

/-- `Z_h(w) = -ξ(t + h (1 - w))`. -/
def Zc (ξ : C(I, CInfPer)) (t h : ℝ) : C(I, CInfPer) :=
  ⟨fun w ↦ -extendCurve ξ (t + h * (1 - w)), by
    have hc : Continuous fun w : I ↦ t + h * (1 - (w : ℝ)) := by fun_prop
    exact ((MBLieGroup.continuous_extendCurve ξ).comp hc).neg⟩

theorem shiftField_eq (ξ : C(I, CInfPer)) (t h : ℝ) :
    shiftField ξ (t + h) t = h • Zc ξ t h := by
  ext w : 1
  rw [shiftField_apply, ContinuousMap.smul_apply]
  change _ = h • -extendCurve ξ (t + h * (1 - w))
  rw [show t + h + w * (t - (t + h)) = t + h * (1 - w) by ring, show t - (t + h) = -h by ring,
    neg_smul, smul_neg]

theorem continuous_Zc (ξ : C(I, CInfPer)) (t : ℝ) : Continuous (Zc ξ t) :=
  ContinuousMap.continuous_of_continuous_uncurry _ <| by
    have hc : Continuous fun p : ℝ × I ↦ t + p.1 * (1 - (p.2 : ℝ)) := by fun_prop
    exact ((MBLieGroup.continuous_extendCurve ξ).comp hc).neg

theorem Zc_zero (ξ : C(I, CInfPer)) (t : ℝ) :
    Zc ξ t 0 = -ContinuousMap.const I (extendCurve ξ t) := by
  ext w : 1
  change -extendCurve ξ (t + 0 * (1 - w)) = _
  simp

theorem shiftField_self (ξ : C(I, CInfPer)) (t : ℝ) : shiftField ξ (t + 0) t = 0 := by
  rw [shiftField_eq, zero_smul]

theorem hasDirDerivAt_shift (ξ : C(I, CInfPer)) (t : ℝ) :
    HasDirDerivAt (fun h ↦ shiftField ξ (t + h) t) 0 1 (Zc ξ t 0) := by
  unfold HasDirDerivAt
  have hZ : Tendsto (Zc ξ t) (𝓝[≠] 0) (𝓝 (Zc ξ t 0)) :=
    (continuous_Zc ξ t).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine hZ.congr' (eventually_nhdsWithin_of_forall fun h (hh : h ≠ 0) ↦ ?_)
  change Zc ξ t h = h⁻¹ • (shiftField ξ (t + (0 + h • 1)) t - shiftField ξ (t + 0) t)
  rw [show (0 : ℝ) + h • (1 : ℝ) = h by simp, shiftField_eq, shiftField_self, sub_zero,
    smul_smul, inv_mul_cancel₀ hh, one_smul]

/-- **`d/dh Ψ(ζ_{t+h → t}) = ξ(t)` at `h = 0`.** -/
theorem hasDirDerivAt_Ψ_shift (ξ : C(I, CInfPer)) (t : ℝ) :
    HasDirDerivAt (fun h ↦ Ψ (shiftField ξ (t + h) t)) 0 1 (extendCurve ξ t) := by
  have hd := (smoothMBOn_Ψ 1).hasDirDerivAt_comp (MBLieGroup.isOpen_valIn isOpen_W)
    (hasDirDerivAt_shift ξ t) (by rw [shiftField_self]; exact zero_mem_valIn)
  rw [shiftField_self, Zc_zero, (hasDirDerivAt_Ψ _).dMB_eq] at hd
  exact hd

/-- The evolution `γ(t) = u_t⁻¹`. -/
def evolCurve (ξ : C(I, CInfPer)) (t : ℝ) : CoverGroup := (cg ξ (projIcc 0 1 zero_le_one t))⁻¹

theorem inv_evolCurve_mul {ξ : C(I, CInfPer)} (hξ : ξ ∈ valIn W) {t r : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hr : r ∈ Icc (0 : ℝ) 1) :
    (evolCurve ξ t)⁻¹ * evolCurve ξ r = cg (shiftField ξ r t) 1 := by
  simp only [evolCurve, inv_inv]
  rw [projIcc_of_mem _ ht, projIcc_of_mem _ hr, cg_eq_mul hξ ⟨r, hr⟩ ⟨t, ht⟩,
    mul_inv_cancel_right]

theorem chart_inv_evolCurve_mul {ξ : C(I, CInfPer)} (hξ : ξ ∈ valIn W) {t r : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hr : r ∈ Icc (0 : ℝ) 1) :
    chartAt CInfPer (1 : CoverGroup) ((evolCurve ξ t)⁻¹ * evolCurve ξ r) =
      Ψ (shiftField ξ (t + (r - t)) t) := by
  rw [inv_evolCurve_mul hξ ht hr, add_sub_cancel]
  exact coe_cg (shiftField_mem hξ (abs_sub_le_one hr ht)) 1

theorem tendsto_sub_nhdsNE (t : ℝ) :
    Tendsto (fun r ↦ r - t) (𝓝[Icc (0 : ℝ) 1 \ {t}] t) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun r hr ↦
    sub_ne_zero.2 (by simpa using hr.2)⟩
  have h : Tendsto (fun r : ℝ ↦ r - t) (𝓝 t) (𝓝 (t - t)) :=
    (continuous_id.sub continuous_const).tendsto t
  rw [sub_self] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- **The logarithmic derivative of `γ` is `ξ`.** -/
theorem hasLogDerivWithinAt_evolCurve {ξ : C(I, CInfPer)} (hξ : ξ ∈ valIn W) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    MBLieGroup.HasLogDerivWithinAt CInfPer (evolCurve ξ) (extendCurve ξ t) (Icc 0 1) t := by
  have := MBLieGroup.isTopologicalGroup CInfPer CoverGroup
  have hd := hasDirDerivAt_Ψ_shift ξ t
  have hc : Tendsto (fun r ↦ Ψ (shiftField ξ (t + (r - t)) t)) (𝓝[Icc 0 1] t) (𝓝 0) := by
    have h1 := (continuousAt_of_hasDirDerivAt_one hd).tendsto
    rw [shiftField_self, Ψ_zero] at h1
    refine h1.comp ?_
    have h : Tendsto (fun r : ℝ ↦ r - t) (𝓝 t) (𝓝 (t - t)) :=
      (continuous_id.sub continuous_const).tendsto t
    rw [sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine ⟨?_, ?_⟩
  · have h1 : Tendsto (fun r ↦ (evolCurve ξ t)⁻¹ * evolCurve ξ r) (𝓝[Icc 0 1] t) (𝓝 1) := by
      rw [tendsto_subtype_rng]
      refine hc.congr' (eventually_nhdsWithin_of_forall fun r hr ↦ ?_)
      exact (chart_inv_evolCurve_mul hξ ht hr).symm
    have h2 := (tendsto_const_nhds (x := evolCurve ξ t)).mul h1
    rw [mul_one] at h2
    refine h2.congr fun r ↦ ?_
    exact mul_inv_cancel_left _ _
  · have hlim := hd.comp (tendsto_sub_nhdsNE t)
    refine hlim.congr' (eventually_nhdsWithin_of_forall fun r hr ↦ ?_)
    simp only [Function.comp_apply]
    rw [chart_inv_evolCurve_mul hξ ht hr.1, chart_inv_evolCurve_mul hξ ht ht]
    simp only [zero_add, smul_eq_mul, mul_one, sub_self, add_zero]

theorem isEvolOn_evolCurve {ξ : C(I, CInfPer)} (hξ : ξ ∈ valIn W) :
    MBLieGroup.IsEvolOn CInfPer (extendCurve ξ) (evolCurve ξ) := by
  refine ⟨?_, fun t ht ↦ hasLogDerivWithinAt_evolCurve hξ ht⟩
  change (cg ξ (projIcc 0 1 zero_le_one 0))⁻¹ = 1
  rw [projIcc_left]
  exact inv_eq_one.2 (cg_zero hξ)

/-! ### Regularity -/

theorem exists_isEvol_const (x : CInfPer) :
    ∃ P : ℝ → CoverGroup, MBLieGroup.IsEvol CInfPer (fun _ ↦ x) P :=
  isExp_exp.exists_isEvol_const x

theorem evol_eq {ξ : C(I, CInfPer)} (hξ : ξ ∈ valIn W) :
    MBLieGroup.evol CInfPer CoverGroup ξ = (cg ξ 1)⁻¹ := by
  rw [MBLieGroup.evol_eq_of_isEvolOn exists_isEvol_const (isEvolOn_evolCurve hξ)]
  change (cg ξ (projIcc 0 1 zero_le_one 1))⁻¹ = _
  rw [projIcc_right]
  rfl

/-- A map into `Ω` is smooth on an open set if its composite with the inclusion is. -/
theorem smoothMBMOn_of_val_comp {g : C(I, CInfPer) → CoverGroup} {U : Set C(I, CInfPer)}
    (hg : SmoothMBMOn C(I, CInfPer) CInfPer (Subtype.val ∘ g) U) :
    SmoothMBMOn C(I, CInfPer) CInfPer g U := by
  intro k
  refine ⟨Topology.IsInducing.subtypeVal.continuousOn_iff.2 (hg k).1, fun x hx ↦ ?_⟩
  have hD : chartDomain g U (chartAt C(I, CInfPer) x) (chartAt CInfPer (g x)) =
      chartDomain (Subtype.val ∘ g) U (chartAt C(I, CInfPer) x)
        (chartAt CInfPer ((Subtype.val ∘ g) x)) := by
    ext y
    simp [chartDomain, TopologicalSpace.Opens.chartAt_eq,
      OpenPartialHomeomorph.subtypeRestr_source]
  rw [hD]
  exact (hg k).2 x hx

/-- **The universal cover of `Diff⁺(S¹)` is `C⁰`-regular.** -/
theorem isC0Regular : MBLieGroup.IsC0Regular CInfPer CoverGroup := by
  have hU := MBLieGroup.isOpen_valIn isOpen_W
  refine MBLieGroup.isC0Regular_of_nhds hU zero_mem_valIn (fun ξ hξ ↦ ?_) ?_
  · obtain ⟨Γ, hΓ, -⟩ := (isEvolOn_evolCurve hξ).exists_isEvol exists_isEvol_const
    exact ⟨Γ, hΓ⟩
  · have hcg : SmoothMBMOn C(I, CInfPer) CInfPer (fun ξ ↦ cg ξ 1) (valIn W) := by
      refine smoothMBMOn_of_val_comp fun k ↦ ?_
      refine ContMDiffMBOn.congr' hU ((contMDiffMBOn_iff_contDiffMBOn hU).2 (smoothMBOn_Ψ k))
        fun ξ hξ ↦ ?_
      exact coe_cg hξ 1
    have hinv := SmoothMBMOn.comp hU isOpen_univ
      (fun k ↦ (MBLieGroup.smoothMBM_inv (E := CInfPer) (G := CoverGroup)) k) hcg
      (mapsTo_univ _ _)
    exact fun k ↦ ContMDiffMBOn.congr' hU (hinv k) fun ξ hξ ↦ evol_eq hξ

end LocallyConvex.LieGroups.CircleCover
