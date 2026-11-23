/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Examples.DiffCircle
public import LocallyConvexAnalysis.Calculus.Rules
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Calculus on the space of smooth periodic functions

`C^∞_per` (lc-manifolds, `CInfPer`) is the Fréchet space of smooth `1`-periodic functions on `ℝ`,
with the seminorms `p_k(u) = sup |u^{(k)}|`. We show that it is a Fréchet algebra on which the
derivative is a continuous linear operator, and that the **precomposition**
`(u, w) ↦ u ∘ (id + w)` is smooth in the sense of Michal–Bastiani, with
`d(u ∘ (id + w))(h, v) = h ∘ (id + w) + (u' ∘ (id + w)) v`. This is what makes the composition of
the group `\widetilde{Diff}⁺(S¹)` smooth in its global chart ([GN26, §13.3]).

## Main definitions

* `CInfPer.D`: the derivative `u ↦ u'`, a continuous linear operator.
* `CInfPer.mul`, `CInfPer.const`: products and constants.
* `CInfPer.precomp u w = u ∘ (id + w)`.

## Main results

* `CInfPer.continuous_iff`: a map into `C^∞_per` is continuous iff all its derivatives are, as maps
  into `BC(ℝ)`.
* `CInfPer.continuous_mul`, `CInfPer.smoothMBOn_mul`: the multiplication is continuous, hence
  smooth.
* `CInfPer.hasDirDerivAt_precompBCF`: the derivative of `(u, w) ↦ u ∘ (id + w) ∈ BC(ℝ)`, with an
  `O(t)` error from Taylor's formula.
* `CInfPer.smoothMBOn_precomp`: **the precomposition is smooth** `C^∞_per × C^∞_per → C^∞_per`,
  and `CInfPer.hasDirDerivAt_precomp` gives its derivative.

## Implementation notes

The smoothness of `P(u, w) = u ∘ (id + w)` as a map into `BC(ℝ)` follows by induction on the
order from `dP((u, w), (h, v)) = P(h, w) + P(u', w) v`, which is again built from `P`. For the
derivatives of order `m`, we treat `Q_m(u, w, a) = (P(u, w) a)^{(m)}` for all `a ∈ C^∞_per` at
once: `Q_{m+1}(u, w, a) = Q_m(u', w, (1 + w') a) + Q_m(u, w, a')`. The space `C^∞_per` embeds in
`∏_m BC(ℝ)` with closed range, so `P` is smooth into `C^∞_per`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function
open scoped Topology ContDiff BoundedContinuousFunction
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.Manifolds.CInfPer

/-! ### Continuity into `C^∞_per` -/

/-- **A map into `C^∞_per` is continuous iff all its derivatives are continuous into `BC(ℝ)`.** -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → CInfPer} :
    Continuous f ↔ ∀ k, Continuous fun x ↦ derivBCF k (f x) := by
  rw [isUniformInducing_J.isInducing.continuous_iff, continuous_pi_iff]
  rfl

/-- `J` as a continuous linear map. -/
def JCLM : CInfPer →L[ℝ] (ℕ → ℝ →ᵇ ℝ) := ⟨J, isUniformInducing_J.isInducing.continuous⟩

/-- `u ↦ u^{(k)}` as a continuous linear map `C^∞_per → BC(ℝ)`. -/
def derivCLM (k : ℕ) : CInfPer →L[ℝ] (ℝ →ᵇ ℝ) := ⟨derivL k, continuous_derivBCF k⟩

@[simp] theorem derivCLM_apply (k : ℕ) (u : CInfPer) : derivCLM k u = derivBCF k u := rfl

/-- **`C^k` maps into `C^∞_per`** are the maps all of whose derivatives are `C^k` into `BC(ℝ)`. -/
theorem contDiffMBOn_of_derivBCF {E : Type} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] {k : ℕ}
    {f : E → CInfPer} {W : Set E} (hW : IsOpen W)
    (h : ∀ m, ContDiffMBOn k (fun x ↦ derivBCF m (f x)) W) : ContDiffMBOn k f W :=
  contDiffMBOn_of_isClosedEmbedding JCLM isEmbedding_J isClosed_range_J hW (contDiffMBOn_pi hW h)

/-! ### Basic estimates -/

theorem abs_le_seminorm (k : ℕ) (u : CInfPer) (x : ℝ) : |iteratedDeriv k u x| ≤ seminorm k u :=
  norm_iteratedDeriv_le_seminorm k u x

theorem seminorm_nonneg' (k : ℕ) (u : CInfPer) : 0 ≤ seminorm k u :=
  apply_nonneg _ _

theorem abs_apply_le (u : CInfPer) (x : ℝ) : |u x| ≤ seminorm 0 u := by
  simpa using abs_le_seminorm 0 u x

theorem abs_deriv_le (u : CInfPer) (x : ℝ) : |deriv u x| ≤ seminorm 1 u := by
  simpa using abs_le_seminorm 1 u x

theorem hasDerivAt (u : CInfPer) (x : ℝ) : HasDerivAt u (deriv u x) x :=
  (DiffCircle.differentiable u x).hasDerivAt

/-- **Mean value inequality**: `|u(b) − u(a)| ≤ p₁(u) |b − a|`. -/
theorem abs_sub_le (u : CInfPer) (a b : ℝ) : |u b - u a| ≤ seminorm 1 u * |b - a| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := ⇑u) (C := seminorm 1 u)
    (s := univ) (fun x _ ↦ DiffCircle.differentiable u x) (fun x _ ↦ abs_deriv_le u x)
    convex_univ (mem_univ a) (mem_univ b)
  simpa [Real.norm_eq_abs] using h

/-! ### The derivative -/

/-- **The derivative** `u ↦ u'` on `C^∞_per`. -/
def deriv' (u : CInfPer) : CInfPer :=
  mk (deriv u) (contDiff_infty_iff_deriv.mp u.contDiff).2 (DiffCircle.periodic_deriv u)

@[simp] theorem coe_deriv' (u : CInfPer) : ⇑(deriv' u) = deriv u := rfl

theorem iteratedDeriv_deriv' (k : ℕ) (u : CInfPer) :
    iteratedDeriv k (deriv' u) = iteratedDeriv (k + 1) u := by
  rw [iteratedDeriv_succ', coe_deriv']

theorem derivBCF_deriv' (k : ℕ) (u : CInfPer) : derivBCF k (deriv' u) = derivBCF (k + 1) u := by
  ext x
  simp only [coe_derivBCF]
  rw [iteratedDeriv_deriv']

theorem seminorm_deriv' (k : ℕ) (u : CInfPer) : seminorm k (deriv' u) = seminorm (k + 1) u := by
  simp [seminorm_apply, derivBCF_deriv']

/-- **The derivative is a continuous linear operator** on `C^∞_per`. -/
def D : CInfPer →L[ℝ] CInfPer where
  toFun := deriv'
  map_add' u v := by
    ext x
    exact deriv_add (DiffCircle.differentiable u x) (DiffCircle.differentiable v x)
  map_smul' c u := by
    ext x
    exact deriv_const_smul c (DiffCircle.differentiable u x)
  cont := continuous_iff.2 fun k ↦ by
    simp only [derivBCF_deriv']
    exact continuous_derivBCF (k + 1)

@[simp] theorem D_apply (u : CInfPer) : D u = deriv' u := rfl

theorem derivBCF_succ (k : ℕ) (u : CInfPer) : derivBCF (k + 1) u = derivBCF k (D u) :=
  (derivBCF_deriv' k u).symm

/-- `|u(a + s) − u(a) − u'(a) s| ≤ p₂(u) s²`. -/
theorem abs_taylor_le (u : CInfPer) (a s : ℝ) :
    |u (a + s) - u a - deriv u a * s| ≤ seminorm 2 u * s ^ 2 := by
  set g : ℝ → ℝ := fun y ↦ u y - deriv u a * y
  have hg : ∀ y, HasDerivAt g (deriv u y - deriv u a) y := fun y ↦
    (hasDerivAt u y).sub ((hasDerivAt_id y).const_mul (deriv u a)) |>.congr_deriv (by simp)
  have hb : ∀ y ∈ uIcc a (a + s), ‖deriv g y‖ ≤ seminorm 2 u * |s| := by
    intro y hy
    rw [(hg y).deriv, Real.norm_eq_abs]
    have h1 := abs_sub_le (deriv' u) a y
    rw [seminorm_deriv'] at h1
    simp only [coe_deriv'] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (seminorm_nonneg' 2 u))
    have := Set.abs_sub_left_of_mem_uIcc hy
    simpa using this
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := g)
    (fun y _ ↦ (hg y).differentiableAt) hb (convex_uIcc a (a + s)) left_mem_uIcc right_mem_uIcc
  have hga : g (a + s) - g a = u (a + s) - u a - deriv u a * s := by simp only [g]; ring
  rw [hga, Real.norm_eq_abs] at h
  calc |u (a + s) - u a - deriv u a * s| ≤ seminorm 2 u * |s| * ‖a + s - a‖ := h
    _ = seminorm 2 u * s ^ 2 := by
      rw [add_sub_cancel_left, Real.norm_eq_abs, mul_assoc, ← sq, sq_abs]

/-! ### Products and constants -/

/-- The product of two smooth periodic functions. -/
def mul (u v : CInfPer) : CInfPer :=
  mk (fun x ↦ u x * v x) (u.contDiff.mul v.contDiff) fun x ↦ by
    simp only [u.periodic x, v.periodic x]

@[simp] theorem coe_mul (u v : CInfPer) : ⇑(mul u v) = fun x ↦ u x * v x := rfl

/-- A constant function. -/
def const (c : ℝ) : CInfPer := mk (fun _ ↦ c) contDiff_const fun _ ↦ rfl

@[simp] theorem coe_const (c : ℝ) : ⇑(const c) = fun _ ↦ c := rfl

theorem mul_const_one (u : CInfPer) : mul u (const 1) = u := by ext x; simp

theorem D_mul (u v : CInfPer) : D (mul u v) = mul (D u) v + mul u (D v) := by
  ext x
  simp only [D_apply, coe_deriv', coe_mul, coe_add]
  exact deriv_mul (DiffCircle.differentiable u x) (DiffCircle.differentiable v x)

theorem mul_add_right (u v w : CInfPer) : mul u (v + w) = mul u v + mul u w := by
  ext x; simp [mul_add]

theorem mul_add_left (u v w : CInfPer) : mul (u + v) w = mul u w + mul v w := by
  ext x; simp [add_mul]

theorem mul_smul_left (c : ℝ) (u v : CInfPer) : mul (c • u) v = c • mul u v := by
  ext x; simp [mul_assoc]

theorem mul_smul_right (c : ℝ) (u v : CInfPer) : mul u (c • v) = c • mul u v := by
  ext x; simp [mul_left_comm]

theorem mul_assoc' (u v w : CInfPer) : mul (mul u v) w = mul u (mul v w) := by
  ext x; simp [mul_assoc]

theorem derivBCF_zero_mul (u v : CInfPer) :
    derivBCF 0 (mul u v) = derivBCF 0 u * derivBCF 0 v := by
  ext x; simp

/-- **The multiplication of `C^∞_per` is continuous.** -/
theorem continuous_mul : Continuous fun p : CInfPer × CInfPer ↦ mul p.1 p.2 := by
  refine continuous_iff.2 fun k ↦ ?_
  induction k with
  | zero =>
    simp only [derivBCF_zero_mul]
    exact ((continuous_derivBCF 0).comp continuous_fst).mul
      ((continuous_derivBCF 0).comp continuous_snd)
  | succ k ih =>
    simp only [derivBCF_succ, D_mul]
    have h1 : Continuous fun p : CInfPer × CInfPer ↦ derivBCF k (mul (D p.1) p.2) :=
      ih.comp ((D.continuous.comp continuous_fst).prodMk continuous_snd)
    have h2 : Continuous fun p : CInfPer × CInfPer ↦ derivBCF k (mul p.1 (D p.2)) :=
      ih.comp (continuous_fst.prodMk (D.continuous.comp continuous_snd))
    exact (h1.add h2).congr fun p ↦ (map_add (derivL k) _ _).symm

/-- The multiplication as a bilinear map. -/
def mulBilin : CInfPer →ₗ[ℝ] CInfPer →ₗ[ℝ] CInfPer :=
  LinearMap.mk₂ ℝ mul mul_add_left mul_smul_left mul_add_right mul_smul_right

/-- **The multiplication of `C^∞_per` is smooth.** -/
theorem smoothMBOn_mul : SmoothMBOn (fun p : CInfPer × CInfPer ↦ mul p.1 p.2) univ :=
  contDiffMBOn_bilin mulBilin continuous_mul

/-! ### Precomposition -/

/-- **The precomposition** `u ∘ (id + w)`. -/
def precomp (u w : CInfPer) : CInfPer :=
  mk (fun x ↦ u (x + w x)) (u.contDiff.comp (contDiff_id.add w.contDiff)) fun x ↦ by
    change u (x + 1 + w (x + 1)) = u (x + w x)
    rw [w.periodic x, add_right_comm, u.periodic]

@[simp] theorem coe_precomp (u w : CInfPer) : ⇑(precomp u w) = fun x ↦ u (x + w x) := rfl

/-- The chain rule: `(u ∘ (id + w))' = (u' ∘ (id + w)) (1 + w')`. -/
theorem D_precomp (u w : CInfPer) :
    D (precomp u w) = mul (precomp (D u) w) (const 1 + D w) := by
  ext x
  simp only [D_apply, coe_deriv', coe_precomp, coe_mul, coe_add, coe_const, Pi.add_apply]
  have h := (hasDerivAt u (x + w x)).comp x ((hasDerivAt_id x).add (hasDerivAt w x))
  exact h.deriv

/-- `P(u, w) = u ∘ (id + w)` as a bounded continuous function. -/
def precompBCF (p : CInfPer × CInfPer) : ℝ →ᵇ ℝ := derivBCF 0 (precomp p.1 p.2)

theorem precompBCF_apply (p : CInfPer × CInfPer) (x : ℝ) :
    precompBCF p x = p.1 (x + p.2 x) := by
  simp [precompBCF]

/-- **`P` is continuous**: `|u(x + w x) − u₀(x + w₀ x)| ≤ p₀(u − u₀) + p₁(u₀) p₀(w − w₀)`. -/
theorem continuous_precompBCF : Continuous precompBCF := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  set B : CInfPer × CInfPer → ℝ := fun p ↦
    seminorm 0 (p.1 - p₀.1) + seminorm 1 p₀.1 * seminorm 0 (p.2 - p₀.2)
  have hB : Continuous B := by
    have h0 : Continuous (seminorm 0) := (continuous_derivBCF 0).norm
    exact (h0.comp (continuous_fst.sub continuous_const)).add
      (continuous_const.mul (h0.comp (continuous_snd.sub continuous_const)))
  have hB0 : B p₀ = 0 := by simp [B]
  refine squeeze_zero (fun _ ↦ dist_nonneg) (fun p ↦ ?_) (hB0 ▸ hB.tendsto p₀)
  rw [BoundedContinuousFunction.dist_eq]
  refine csInf_le ⟨0, fun _ h ↦ h.1⟩ ⟨add_nonneg (seminorm_nonneg' _ _)
    (mul_nonneg (seminorm_nonneg' _ _) (seminorm_nonneg' _ _)), fun x ↦ ?_⟩
  rw [precompBCF_apply, precompBCF_apply, Real.dist_eq]
  have e1 := abs_apply_le (p.1 - p₀.1) (x + p.2 x)
  have e2 := abs_sub_le p₀.1 (x + p₀.2 x) (x + p.2 x)
  have e3 := abs_apply_le (p.2 - p₀.2) x
  simp only [coe_sub, Pi.sub_apply] at e1 e3
  calc |p.1 (x + p.2 x) - p₀.1 (x + p₀.2 x)|
      ≤ |p.1 (x + p.2 x) - p₀.1 (x + p.2 x)| + |p₀.1 (x + p.2 x) - p₀.1 (x + p₀.2 x)| :=
        _root_.abs_sub_le _ _ _
    _ ≤ seminorm 0 (p.1 - p₀.1) + seminorm 1 p₀.1 * seminorm 0 (p.2 - p₀.2) := by
        refine add_le_add e1 (e2.trans (mul_le_mul_of_nonneg_left ?_ (seminorm_nonneg' _ _)))
        rw [add_sub_add_left_eq_sub]
        exact e3

/-- The derivative of `P`: `dP((u, w), (h, v)) = P(h, w) + P(u', w) v`. -/
def precompBCFDeriv (r : (CInfPer × CInfPer) × (CInfPer × CInfPer)) : ℝ →ᵇ ℝ :=
  precompBCF (r.2.1, r.1.2) + precompBCF (D r.1.1, r.1.2) * derivBCF 0 r.2.2

/-- **The derivative of `P`**, with an `O(t)` error. -/
theorem hasDirDerivAt_precompBCF (p q : CInfPer × CInfPer) :
    HasDirDerivAt precompBCF p q (precompBCFDeriv (p, q)) := by
  obtain ⟨u, w⟩ := p
  obtain ⟨h, v⟩ := q
  set C : ℝ := seminorm 2 u * seminorm 0 v ^ 2 + seminorm 1 h * seminorm 0 v
  have hC : 0 ≤ C := add_nonneg (mul_nonneg (seminorm_nonneg' _ _) (sq_nonneg _))
    (mul_nonneg (seminorm_nonneg' _ _) (seminorm_nonneg' _ _))
  have key : ∀ t : ℝ, t ≠ 0 → ‖t⁻¹ • (precompBCF ((u, w) + t • (h, v)) - precompBCF (u, w)) -
      precompBCFDeriv ((u, w), (h, v))‖ ≤ C * |t| := by
    intro t ht
    refine (BoundedContinuousFunction.norm_le (mul_nonneg hC (abs_nonneg t))).2 fun x ↦ ?_
    set a := x + w x
    have hval : (t⁻¹ • (precompBCF ((u, w) + t • (h, v)) - precompBCF (u, w)) -
        precompBCFDeriv ((u, w), (h, v))) x =
        t⁻¹ * (u (a + t * v x) - u a - deriv u a * (t * v x)) + (h (a + t * v x) - h a) := by
      simp only [_root_.sub_apply, _root_.smul_apply, smul_eq_mul, precompBCFDeriv,
        _root_.add_apply, _root_.mul_apply, precompBCF_apply, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, coe_add, coe_smul, D_apply, coe_deriv', coe_derivBCF,
        iteratedDeriv_zero, Pi.add_apply, Pi.smul_apply]
      have ha : x + (w x + t * v x) = a + t * v x := by simp only [a]; ring
      rw [ha]
      field_simp
      ring
    rw [hval, Real.norm_eq_abs]
    have e1 := abs_taylor_le u a (t * v x)
    have e2 := abs_sub_le h a (a + t * v x)
    have ev := abs_apply_le v x
    have hv2 : v x ^ 2 ≤ seminorm 0 v ^ 2 := sq_le_sq' (abs_le.1 ev).1 (abs_le.1 ev).2
    calc |t⁻¹ * (u (a + t * v x) - u a - deriv u a * (t * v x)) + (h (a + t * v x) - h a)|
        ≤ |t⁻¹ * (u (a + t * v x) - u a - deriv u a * (t * v x))| + |h (a + t * v x) - h a| :=
          abs_add_le _ _
      _ ≤ |t|⁻¹ * (seminorm 2 u * (t * v x) ^ 2) + seminorm 1 h * (|t| * seminorm 0 v) := by
          rw [abs_mul, abs_inv]
          refine add_le_add (mul_le_mul_of_nonneg_left e1 (inv_nonneg.2 (abs_nonneg t)))
            (e2.trans (mul_le_mul_of_nonneg_left ?_ (seminorm_nonneg' _ _)))
          rw [add_sub_cancel_left, abs_mul]
          exact mul_le_mul_of_nonneg_left ev (abs_nonneg t)
      _ ≤ C * |t| := by
          have ht' : 0 < |t| := abs_pos.2 ht
          have : |t|⁻¹ * (seminorm 2 u * (t * v x) ^ 2) = seminorm 2 u * v x ^ 2 * |t| := by
            rw [mul_pow, ← sq_abs t]
            field_simp
          rw [this]
          simp only [C, add_mul]
          refine add_le_add ?_ (le_of_eq (by ring))
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hv2 (abs_nonneg t)) (seminorm_nonneg' _ _)
  unfold HasDirDerivAt
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun t : ℝ ↦ C * |t|) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ ↦ C * |t|) (𝓝 0) (𝓝 (C * |0|)) :=
      (continuous_const.mul continuous_abs).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
  exact key t ht

theorem dMB_precompBCF : dMB precompBCF = precompBCFDeriv :=
  funext fun r ↦ (hasDirDerivAt_precompBCF r.1 r.2).dMB_eq

/-- **`P(u, w) = u ∘ (id + w)` is smooth** as a map into `BC(ℝ)`. -/
theorem contDiffMBOn_precompBCF (k : ℕ) : ContDiffMBOn k precompBCF univ := by
  induction k with
  | zero => exact continuous_precompBCF.continuousOn
  | succ k ih =>
    refine ⟨continuous_precompBCF.continuousOn, fun p _ q ↦ ?_, ?_⟩
    · rw [dMB_precompBCF]; exact hasDirDerivAt_precompBCF p q
    · rw [dMB_precompBCF, univ_prod_univ]
      set L₁ : (CInfPer × CInfPer) × (CInfPer × CInfPer) →L[ℝ] CInfPer × CInfPer :=
        ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)).prod
          ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _))
      set L₂ : (CInfPer × CInfPer) × (CInfPer × CInfPer) →L[ℝ] CInfPer × CInfPer :=
        (D.comp ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _))).prod
          ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _))
      set L₃ : (CInfPer × CInfPer) × (CInfPer × CInfPer) →L[ℝ] (ℝ →ᵇ ℝ) :=
        (derivCLM 0).comp ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))
      have h₁ : ContDiffMBOn k (fun r ↦ precompBCF (L₁ r)) univ := by
        have := ContDiffMBOn.comp_clm L₁ isOpen_univ ih
        rwa [preimage_univ] at this
      have h₂ : ContDiffMBOn k (fun r ↦ precompBCF (L₂ r)) univ := by
        have := ContDiffMBOn.comp_clm L₂ isOpen_univ ih
        rwa [preimage_univ] at this
      have hmul : Continuous fun p : (ℝ →ᵇ ℝ) × (ℝ →ᵇ ℝ) ↦
          LinearMap.mul ℝ (ℝ →ᵇ ℝ) p.1 p.2 := by
        simp only [LinearMap.mul_apply']; exact continuous_fst.mul continuous_snd
      have h₃ := ContDiffMBOn.bilin (LinearMap.mul ℝ (ℝ →ᵇ ℝ)) hmul isOpen_univ h₂
        (L₃.contDiffMBOn k univ)
      exact ContDiffMBOn.congr_of_isOpen isOpen_univ
        (f₁ := fun r ↦ precompBCF (L₁ r) + LinearMap.mul ℝ (ℝ →ᵇ ℝ) (precompBCF (L₂ r)) (L₃ r))
        (fun _ _ ↦ rfl) (h₁.add isOpen_univ h₃)

/-! ### Higher derivatives of the precomposition -/

/-- Triples `(u, w, a)`. -/
abbrev T3 : Type := CInfPer × CInfPer × CInfPer

/-- `(u, w, a) ↦ u`. -/
def π₁ : T3 →L[ℝ] CInfPer := ContinuousLinearMap.fst ℝ CInfPer (CInfPer × CInfPer)

/-- `(u, w, a) ↦ w`. -/
def π₂ : T3 →L[ℝ] CInfPer :=
  (ContinuousLinearMap.fst ℝ CInfPer CInfPer).comp
    (ContinuousLinearMap.snd ℝ CInfPer (CInfPer × CInfPer))

/-- `(u, w, a) ↦ a`. -/
def π₃ : T3 →L[ℝ] CInfPer :=
  (ContinuousLinearMap.snd ℝ CInfPer CInfPer).comp
    (ContinuousLinearMap.snd ℝ CInfPer (CInfPer × CInfPer))

theorem contDiffMBOn_clm {X Y : Type} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X]
    [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y] [T2Space Y] (k : ℕ) (A : X →L[ℝ] Y)
    {f : X → Y} (hf : ∀ x, A x = f x) : ContDiffMBOn k f univ :=
  ContDiffMBOn.congr_of_isOpen isOpen_univ (fun x _ ↦ hf x) (A.contDiffMBOn k univ)

theorem continuous_mul_BCF : Continuous fun p : (ℝ →ᵇ ℝ) × (ℝ →ᵇ ℝ) ↦
    LinearMap.mul ℝ (ℝ →ᵇ ℝ) p.1 p.2 := by
  simp only [LinearMap.mul_apply']; exact continuous_fst.mul continuous_snd

/-- `Q_m(u, w, a) = (P(u, w) a)^{(m)}`. -/
def precompQ (m : ℕ) (p : T3) : ℝ →ᵇ ℝ :=
  derivBCF m (mul (precomp p.1 p.2.1) p.2.2)

theorem precompQ_succ (m : ℕ) (p : T3) :
    precompQ (m + 1) p = precompQ m (D p.1, p.2.1, mul (const 1 + D p.2.1) p.2.2) +
      precompQ m (p.1, p.2.1, D p.2.2) := by
  simp only [precompQ, derivBCF_succ, D_mul, D_precomp, mul_assoc']
  exact map_add (derivL m) _ _

theorem contDiffMBOn_precompQ (k m : ℕ) : ContDiffMBOn k (precompQ m) univ := by
  have hu : ContDiffMBOn k (fun p : T3 ↦ p.1) univ := contDiffMBOn_clm k π₁ fun _ ↦ rfl
  have hw : ContDiffMBOn k (fun p : T3 ↦ p.2.1) univ := contDiffMBOn_clm k π₂ fun _ ↦ rfl
  have ha : ContDiffMBOn k (fun p : T3 ↦ p.2.2) univ := contDiffMBOn_clm k π₃ fun _ ↦ rfl
  induction m with
  | zero =>
    have h0 : ∀ p : T3, precompQ 0 p = precompBCF (p.1, p.2.1) * derivBCF 0 p.2.2 := fun p ↦ by
      simp [precompQ, derivBCF_zero_mul, precompBCF]
    have hP : ContDiffMBOn k (fun p : T3 ↦ precompBCF (p.1, p.2.1)) univ := by
      have := ContDiffMBOn.comp_clm (π₁.prod π₂) isOpen_univ (contDiffMBOn_precompBCF k)
      rwa [preimage_univ] at this
    have ha0 : ContDiffMBOn k (fun p : T3 ↦ derivBCF 0 p.2.2) univ :=
      contDiffMBOn_clm k ((derivCLM 0).comp π₃) fun _ ↦ rfl
    exact ContDiffMBOn.congr_of_isOpen isOpen_univ (fun p _ ↦ (h0 p).symm)
      (ContDiffMBOn.bilin (LinearMap.mul ℝ (ℝ →ᵇ ℝ)) continuous_mul_BCF isOpen_univ hP ha0)
  | succ m ih =>
    have hD1 : ContDiffMBOn k (fun p : T3 ↦ D p.1) univ :=
      contDiffMBOn_clm k (D.comp π₁) fun _ ↦ rfl
    have hDa : ContDiffMBOn k (fun p : T3 ↦ D p.2.2) univ :=
      contDiffMBOn_clm k (D.comp π₃) fun _ ↦ rfl
    have h1w : ContDiffMBOn k (fun p : T3 ↦ const 1 + D p.2.1) univ :=
      (contDiffMBOn_const k (const 1) univ).add isOpen_univ
        (contDiffMBOn_clm k (D.comp π₂) fun _ ↦ rfl)
    have hm : ContDiffMBOn k (fun p : T3 ↦ mul (const 1 + D p.2.1) p.2.2) univ :=
      ContDiffMBOn.bilin mulBilin continuous_mul isOpen_univ h1w ha
    have hA : ContDiffMBOn k (fun p : T3 ↦
        precompQ m (D p.1, p.2.1, mul (const 1 + D p.2.1) p.2.2)) univ :=
      ContDiffMBOn.comp (g := precompQ m)
        (f := fun p : T3 ↦ (D p.1, p.2.1, mul (const 1 + D p.2.1) p.2.2)) isOpen_univ isOpen_univ ih
        (hD1.prodMk isOpen_univ (hw.prodMk isOpen_univ hm)) (mapsTo_univ _ _)
    have hB : ContDiffMBOn k (fun p : T3 ↦ precompQ m (p.1, p.2.1, D p.2.2)) univ :=
      ContDiffMBOn.comp (g := precompQ m) (f := fun p : T3 ↦ (p.1, p.2.1, D p.2.2))
        isOpen_univ isOpen_univ ih
        (hu.prodMk isOpen_univ (hw.prodMk isOpen_univ hDa)) (mapsTo_univ _ _)
    exact ContDiffMBOn.congr_of_isOpen isOpen_univ (fun p _ ↦ (precompQ_succ m p).symm)
      (hA.add isOpen_univ hB)

/-- **The precomposition `(u, w) ↦ u ∘ (id + w)` is smooth** on `C^∞_per × C^∞_per`. -/
theorem smoothMBOn_precomp :
    SmoothMBOn (fun p : CInfPer × CInfPer ↦ precomp p.1 p.2) univ := fun k ↦ by
  refine contDiffMBOn_of_derivBCF isOpen_univ fun m ↦ ?_
  have h1 : ContDiffMBOn k (fun p : CInfPer × CInfPer ↦ p.1) univ :=
    contDiffMBOn_clm k (ContinuousLinearMap.fst ℝ CInfPer CInfPer) fun _ ↦ rfl
  have h2 : ContDiffMBOn k (fun p : CInfPer × CInfPer ↦ p.2) univ :=
    contDiffMBOn_clm k (ContinuousLinearMap.snd ℝ CInfPer CInfPer) fun _ ↦ rfl
  have h := ContDiffMBOn.comp isOpen_univ isOpen_univ (contDiffMBOn_precompQ k m)
    (h1.prodMk isOpen_univ (h2.prodMk isOpen_univ (contDiffMBOn_const k (const 1) univ)))
    (mapsTo_univ _ _)
  refine ContDiffMBOn.congr_of_isOpen isOpen_univ (fun p _ ↦ ?_) h
  simp [precompQ, mul_const_one]


theorem derivBCF_zero_injective : Injective (derivBCF 0) := by
  intro u v h
  ext x
  simpa using DFunLike.congr_fun h x

/-- **The derivative of the precomposition**:
`d(u ∘ (id + w))(h, v) = h ∘ (id + w) + (u' ∘ (id + w)) v`. -/
theorem hasDirDerivAt_precomp (p q : CInfPer × CInfPer) :
    HasDirDerivAt (fun p : CInfPer × CInfPer ↦ precomp p.1 p.2) p q
      (precomp q.1 p.2 + mul (precomp (D p.1) p.2) q.2) := by
  have hd := (smoothMBOn_precomp 1).hasDirDerivAt (k := 0) (mem_univ p) q
  convert hd using 1
  refine derivBCF_zero_injective (tendsto_nhds_unique ?_ (hd.clm_comp_real (derivCLM 0)))
  have h := hasDirDerivAt_precompBCF p q
  rw [show derivBCF 0 (precomp q.1 p.2 + mul (precomp (D p.1) p.2) q.2) =
      precompBCFDeriv (p, q) by
    change derivL 0 (precomp q.1 p.2 + mul (precomp (D p.1) p.2) q.2) = _
    rw [map_add (derivL 0)]
    change _ + derivBCF 0 (mul _ _) = _
    rw [derivBCF_zero_mul]; rfl]
  exact h

end LocallyConvex.Manifolds.CInfPer
