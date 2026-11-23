/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Regular.Mackey
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Regular vector groups are Mackey complete

If the vector group `(E, +)` is regular, then `E` is Mackey complete; with `Regular/Mackey.lean`,
this gives [GN26, Proposition 6.1.3]: for `k ≥ 1`, `(E, +)` is `C^k`-regular if and only if `E` is
Mackey complete, and likewise for regularity.

Regularity integrates smooth curves on `[0, 1]`. That smooth curves suffice for Mackey
completeness is [GN26, Remark 1.1.18(c)], which refers to [KM97, Theorem 2.14]; we prove it by
adapting lc-analysis's proof for Lipschitz curves (`MackeyComplete.of_integratesLipschitzCurves`),
replacing its tents by smooth bumps. Given a Mackey–Cauchy sequence `u` with `u_l − u_k ∈ r_k B`,
a fast subsequence `u_{n_j}` gives increments `d_j ∈ w_j c_j K`, `K` the absolutely convex hull of
`B`, and the curve `γ(t) = ∑_j β((t − a_j)/w_j) d_j/w_j`, with a smooth bump `β` of integral `1`
on `[1/4, 3/4]`, `a_j = 1 − 2^{-j}` and `w_j = 2^{-j-1}`, has the partial integrals
`u_{n_N} − u_{n_0}`. For each `t` the sum is finite, and choosing `c_j` small compared with
`sup |β^{(n)}| w_j^{-n-1}` for all `n ≤ j` makes all derivatives of `γ` tend to `0` at `t = 1`,
so `γ` is smooth (`smoothMBOn_of_derivSeq`). The integral of `γ` is the limit of the subsequence.

## Main results

* `MackeyConverse.smoothMBOn_of_derivSeq`: a curve with a sequence of derivatives is smooth.
* `MackeyConverse.mackeyComplete_of_integratesSmooth`: **if smooth curves have weak integrals on
  `[0, 1]`, then `E` is Mackey complete**.
* `VectorGroup.mackeyComplete_of_isRegular`, `VectorGroup.isCkRegular_iff`,
  `VectorGroup.isRegular_iff`: **[GN26, Proposition 6.1.3]**.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
* [A. Kriegl, P. W. Michor, *The Convenient Setting of Global Analysis*][KM97]
-/

@[expose] public section

open Set Filter Function TopologicalSpace MeasureTheory
open scoped Topology unitInterval ContDiff Pointwise
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups.MackeyConverse

universe u

/-! ### A smooth bump on `[1/4, 3/4]` -/

/-- A smooth bump function on `ℝ` around `1/2`. -/
def bumpR : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- The normalized bump: smooth, nonnegative, supported in `[1/4, 3/4]`, with integral `1`. -/
def bumpFn (t : ℝ) : ℝ := bumpR.normed volume t

theorem contDiff_bumpFn : ContDiff ℝ ∞ bumpFn := bumpR.contDiff_normed

theorem bumpFn_nonneg (t : ℝ) : 0 ≤ bumpFn t := bumpR.nonneg_normed t

theorem iteratedDeriv_bumpFn_eq_zero (n : ℕ) {t : ℝ} (ht : t ∉ Icc (1 / 4 : ℝ) (3 / 4)) :
    iteratedDeriv n bumpFn t = 0 := by
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have hts : t ∉ tsupport bumpFn := by
    change t ∉ tsupport (bumpR.normed volume)
    rw [bumpR.tsupport_normed_eq, Real.closedBall_eq_Icc]
    convert ht using 2; norm_num [bumpR]
  have : t ∉ support (iteratedFDeriv ℝ n bumpFn) := fun h ↦
    hts (support_iteratedFDeriv_subset n h)
  rw [notMem_support] at this
  rw [this]; rfl

theorem continuous_iteratedDeriv_bumpFn (n : ℕ) : Continuous (iteratedDeriv n bumpFn) :=
  contDiff_bumpFn.continuous_iteratedDeriv n (mod_cast le_top)

theorem hasDerivAt_iteratedDeriv_bumpFn (n : ℕ) (t : ℝ) :
    HasDerivAt (iteratedDeriv n bumpFn) (iteratedDeriv (n + 1) bumpFn t) t := by
  rw [iteratedDeriv_succ]
  exact ((contDiff_bumpFn.differentiable_iteratedDeriv n (mod_cast WithTop.coe_lt_top _))
    t).hasDerivAt

theorem exists_bound_bumpFn (n : ℕ) : ∃ C, 0 ≤ C ∧ ∀ t, |iteratedDeriv n bumpFn t| ≤ C := by
  have hc : HasCompactSupport (iteratedDeriv n bumpFn) := by
    refine HasCompactSupport.of_support_subset_isCompact (K := Icc (1 / 4 : ℝ) (3 / 4))
      isCompact_Icc fun t ht ↦ ?_
    by_contra h
    exact ht (iteratedDeriv_bumpFn_eq_zero n h)
  obtain ⟨C, hC⟩ := (continuous_iteratedDeriv_bumpFn n).bounded_above_of_compact_support hc
  exact ⟨max C 0, le_max_right _ _, fun t ↦ (hC t).trans (le_max_left _ _)⟩

/-- A bound for the `n`-th derivative of the bump. -/
def bumpBound (n : ℕ) : ℝ := (exists_bound_bumpFn n).choose

theorem bumpBound_nonneg (n : ℕ) : 0 ≤ bumpBound n := (exists_bound_bumpFn n).choose_spec.1

theorem abs_iteratedDeriv_le (n : ℕ) (t : ℝ) : |iteratedDeriv n bumpFn t| ≤ bumpBound n :=
  (exists_bound_bumpFn n).choose_spec.2 t

/-! ### The rescaled bumps -/

/-- `g_{n,j}(t) = w_j^{-n} β^{(n)}((t − a_j)/w_j)`, the `n`-th derivative of the bump
`β((t − a_j)/w_j)` on `[a_j, a_{j+1}]`, with `a_j = 1 − 2^{-j}` and `w_j = 2^{-j-1}`. -/
def g (n j : ℕ) (t : ℝ) : ℝ :=
  (tentWidth j)⁻¹ ^ n * iteratedDeriv n bumpFn ((t - tentLeft j) / tentWidth j)

theorem hasDerivAt_g (n j : ℕ) (t : ℝ) : HasDerivAt (g n j) (g (n + 1) j t) t := by
  have hw := (tentWidth_pos j).ne'
  have ha : HasDerivAt (fun t ↦ (t - tentLeft j) / tentWidth j) (1 / tentWidth j) t :=
    ((hasDerivAt_id t).sub_const _).div_const _
  have h := ((hasDerivAt_iteratedDeriv_bumpFn n _).comp t ha).const_mul ((tentWidth j)⁻¹ ^ n)
  convert h using 1
  · funext s; rfl
  · simp only [g]
    ring

theorem g_eq_zero (n j : ℕ) {t : ℝ}
    (ht : t ∉ Icc (tentLeft j + tentWidth j / 4) (tentLeft j + 3 * tentWidth j / 4)) :
    g n j t = 0 := by
  have hw := tentWidth_pos j
  rw [g, iteratedDeriv_bumpFn_eq_zero n, mul_zero]
  intro hmem
  apply ht
  rw [mem_Icc, le_div_iff₀ hw, div_le_iff₀ hw] at hmem
  constructor <;> linarith [hmem.1, hmem.2]

theorem abs_g_le (n j : ℕ) (t : ℝ) : |g n j t| ≤ (tentWidth j)⁻¹ ^ n * bumpBound n := by
  rw [g, abs_mul, abs_of_pos (by have := tentWidth_pos j; positivity)]
  exact mul_le_mul_of_nonneg_left (abs_iteratedDeriv_le n _)
    (by have := tentWidth_pos j; positivity)

theorem g_eq_zero_of_le {n j : ℕ} {t : ℝ} (ht : t ≤ tentLeft j) : g n j t = 0 :=
  g_eq_zero n j fun h ↦ by linarith [h.1, tentWidth_pos j]

theorem g_eq_zero_of_one_le {n j : ℕ} {t : ℝ} (ht : 1 ≤ t) : g n j t = 0 :=
  g_eq_zero n j fun h ↦ by
    linarith [h.2, tentWidth_pos j, tentLeft_lt_one (j + 1), tentLeft_succ j]

theorem tentLeft_add_two_mul (j : ℕ) : tentLeft j + 2 * tentWidth j = 1 := by
  simp only [tentLeft, tentWidth, pow_succ]; ring

theorem integral_g (j : ℕ) : ∫ t in (0 : ℝ)..1, g 0 j t = tentWidth j := by
  have hw := (tentWidth_pos j)
  simp only [g, pow_zero, one_mul, iteratedDeriv_zero, sub_div]
  rw [intervalIntegral.integral_comp_div_sub (f := bumpFn) hw.ne', smul_eq_mul]
  rw [intervalIntegral.integral_eq_integral_of_support_subset]
  · change tentWidth j * ∫ x, bumpR.normed volume x = tentWidth j
    rw [bumpR.integral_normed, mul_one]
  · change support (bumpR.normed volume) ⊆ _
    rw [bumpR.support_normed_eq, Real.ball_eq_Ioo]
    intro x hx
    simp only [bumpR, mem_Ioo] at hx
    have h1 := tentLeft_nonneg j
    have h2 : tentLeft j + 2 * tentWidth j = 1 := by
      simp only [tentLeft, tentWidth, pow_succ]; ring
    constructor
    · rw [zero_div]; linarith [div_nonneg h1 hw.le]
    · rw [div_sub_div_same, le_div_iff₀ hw]; nlinarith

/-! ### The curves -/

section Curves

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

/-- The partial sums `∑_{j < N} g_{n,j}(t) e_j`. -/
def S (n : ℕ) (e : ℕ → E) (N : ℕ) (t : ℝ) : E := ∑ j ∈ Finset.range N, g n j t • e j

/-- The curve `∑_j g_{n,j}(t) e_j`, a finite sum for each `t`. -/
def D (n : ℕ) (e : ℕ → E) (t : ℝ) : E :=
  open Classical in
  if h : ∃ N, t ≤ tentLeft N then S n e (Nat.find h) t else 0

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [T2Space E] in
theorem S_stable (n : ℕ) (e : ℕ → E) {M N : ℕ} (hMN : M ≤ N) {t : ℝ} (ht : t ≤ tentLeft M) :
    S n e N t = S n e M t := by
  rw [S, S, ← Finset.sum_range_add_sum_Ico _ hMN, add_eq_left]
  refine Finset.sum_eq_zero fun j hj ↦ ?_
  rw [g_eq_zero_of_le (ht.trans (tentLeft_mono (Finset.mem_Ico.1 hj).1)), zero_smul]

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [T2Space E] in
theorem S_eq_zero_of_one_le (n : ℕ) (e : ℕ → E) (N : ℕ) {t : ℝ} (ht : 1 ≤ t) : S n e N t = 0 :=
  Finset.sum_eq_zero fun j _ ↦ by rw [g_eq_zero_of_one_le ht, zero_smul]

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [T2Space E] in
theorem D_eq_of_le (n : ℕ) (e : ℕ → E) {N : ℕ} {t : ℝ} (ht : t ≤ tentLeft N) :
    D n e t = S n e N t := by
  have h : ∃ N, t ≤ tentLeft N := ⟨N, ht⟩
  rw [D, dite_eq_left_of_eq_true (eq_true h)]
  exact (S_stable n e (Nat.find_min' h ht) (Nat.find_spec h)).symm

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [T2Space E] in
theorem D_eq_zero_of_one_le (n : ℕ) (e : ℕ → E) {t : ℝ} (ht : 1 ≤ t) : D n e t = 0 := by
  rw [D]
  split_ifs with h
  · exact S_eq_zero_of_one_le n e _ ht
  · rfl

theorem exists_lt_tentLeft {t : ℝ} (ht : t < 1) : ∃ N, t < tentLeft N := by
  obtain ⟨N, hN⟩ : ∃ N, (1 / 2 : ℝ) ^ N < 1 - t :=
    exists_pow_lt_of_lt_one (by linarith) (by norm_num)
  exact ⟨N, by unfold tentLeft; linarith⟩

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [T2Space E] in
theorem eventually_D_eq (n : ℕ) (e : ℕ → E) (t : ℝ) : ∀ᶠ N in atTop, D n e t = S n e N t := by
  rcases lt_or_ge t 1 with ht | ht
  · obtain ⟨N₀, hN₀⟩ := exists_lt_tentLeft ht
    filter_upwards [eventually_ge_atTop N₀] with N hN
    exact D_eq_of_le n e (hN₀.le.trans (tentLeft_mono hN))
  · exact Eventually.of_forall fun N ↦ by
      rw [D_eq_zero_of_one_le n e ht, S_eq_zero_of_one_le n e N ht]

omit [IsTopologicalAddGroup E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem hasDirDerivAt_smul_const {f : ℝ → ℝ} {f' t : ℝ} (hf : HasDerivAt f f' t) (v : E) :
    HasDirDerivAt (fun s ↦ f s • v) t 1 (f' • v) := by
  unfold HasDirDerivAt
  have h := (hasDerivAt_iff_tendsto_slope_zero.1 hf).smul_const v
  refine h.congr fun s ↦ ?_
  simp only [smul_eq_mul, mul_one]
  rw [← sub_smul, smul_smul]

omit [LocallyConvexSpace ℝ E] [T2Space E] in
theorem hasDirDerivAt_S (n : ℕ) (e : ℕ → E) (N : ℕ) (t : ℝ) :
    HasDirDerivAt (S n e N) t 1 (S (n + 1) e N t) := by
  induction N with
  | zero =>
    have h0 : S n e 0 = fun _ ↦ 0 := by funext s; simp [S]
    rw [h0, show S (n + 1) e 0 t = 0 by simp [S]]
    unfold HasDirDerivAt
    simp only [sub_self, smul_zero]
    exact tendsto_const_nhds
  | succ N ih =>
    have h := ih.add (hasDirDerivAt_smul_const (hasDerivAt_g n N t) (e N))
    have hf : S n e (N + 1) = fun s ↦ S n e N s + g n N s • e N := by
      funext s; simp only [S, Finset.sum_range_succ]
    rw [hf, show S (n + 1) e (N + 1) t = S (n + 1) e N t + g (n + 1) N t • e N by
      simp only [S, Finset.sum_range_succ]]
    exact h

end Curves

/-! ### Derivatives of the curves -/

section Deriv

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

omit [LocallyConvexSpace ℝ E] [T2Space E] in
theorem hasDirDerivAt_D_of_lt (n : ℕ) (e : ℕ → E) {t : ℝ} (ht : t < 1) :
    HasDirDerivAt (D n e) t 1 (D (n + 1) e t) := by
  obtain ⟨N, hN⟩ := exists_lt_tentLeft ht
  have hev : S n e N =ᶠ[𝓝 t] D n e := by
    filter_upwards [Iio_mem_nhds hN] with s hs
    exact (D_eq_of_le n e (le_of_lt hs)).symm
  rw [D_eq_of_le (n + 1) e hN.le]
  exact (hasDirDerivAt_S n e N t).congr_of_eventuallyEq hev

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem hasDirDerivAt_D_of_gt (n : ℕ) (e : ℕ → E) {t : ℝ} (ht : 1 < t) :
    HasDirDerivAt (D n e) t 1 (D (n + 1) e t) := by
  rw [D_eq_zero_of_one_le (n + 1) e ht.le]
  have hev : (fun _ : ℝ ↦ (0 : E)) =ᶠ[𝓝 t] D n e := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact (D_eq_zero_of_one_le n e (le_of_lt hs)).symm
  refine HasDirDerivAt.congr_of_eventuallyEq ?_ hev
  unfold HasDirDerivAt
  simp only [sub_self, smul_zero]
  exact tendsto_const_nhds

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [T2Space E] in
/-- Near `1`, the difference quotients of `D n e` at `1` are small multiples of `K`. -/
theorem quotient_mem_smul {K : Set E} (hKc : Convex ℝ K) (h0 : (0 : E) ∈ K)
    (hneg : ∀ x ∈ K, -x ∈ K) {e : ℕ → E} {c : ℕ → ℝ} (hc0 : ∀ j, 0 ≤ c j)
    (he : ∀ j, e j ∈ c j • K)
    (hbound : ∀ n j, n ≤ j → (tentWidth j)⁻¹ ^ (n + 1) * bumpBound n * c j ≤ (1 / 2) ^ (j + 1))
    {n J : ℕ} (hnJ : n ≤ J) {s : ℝ} (hs : |s| < 5 / 8 * (1 / 2) ^ J) :
    s⁻¹ • D n e (1 + s) ∈ ((1 / 2 : ℝ) ^ J) • K := by
  rcases le_or_gt 0 s with hs0 | hs0
  · rw [D_eq_zero_of_one_le n e (by linarith), smul_zero]
    exact zero_mem_smul_set h0
  set t := 1 + s
  obtain ⟨N, hN⟩ := exists_lt_tentLeft (show t < 1 by simp only [t]; linarith)
  rw [D_eq_of_le n e hN.le, S, Finset.smul_sum]
  set coef : ℕ → ℝ := fun j ↦ if J ≤ j then (1 / 2 : ℝ) ^ (j + 1) else 0
  have hcoef : ∀ j, 0 ≤ coef j := fun j ↦ by
    simp only [coef]; split_ifs <;> positivity
  have hterm : ∀ j ∈ Finset.range N, s⁻¹ • g n j t • e j ∈ coef j • K := by
    intro j _
    by_cases hg : g n j t = 0
    · rw [hg, zero_smul, smul_zero]; exact zero_mem_smul_set h0
    have hmem : t ∈ Icc (tentLeft j + tentWidth j / 4) (tentLeft j + 3 * tentWidth j / 4) := by
      by_contra h; exact hg (g_eq_zero n j h)
    have hw := tentWidth_pos j
    have h2 := tentLeft_add_two_mul j
    have hsw : tentWidth j ≤ |s| := by
      rw [abs_of_neg hs0]; simp only [t] at hmem; linarith [hmem.2]
    have hJj : J ≤ j := by
      by_contra hj
      have hj := not_le.1 hj
      have : (1 / 2 : ℝ) ^ J ≤ tentWidth j := by
        unfold tentWidth
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      linarith
    obtain ⟨k, hk, hke⟩ := he j
    simp only at hke
    rw [← hke, smul_smul, smul_smul]
    simp only [coef, hJj, ↓reduceIte]
    refine smul_mem_smul_of_abs_le hKc h0 hneg hk ?_
    calc |s⁻¹ * g n j t * c j| = |s|⁻¹ * |g n j t| * c j := by
          rw [abs_mul, abs_mul, abs_inv, abs_of_nonneg (hc0 j)]
      _ ≤ (tentWidth j)⁻¹ * ((tentWidth j)⁻¹ ^ n * bumpBound n) * c j := by
          have h1 : |s|⁻¹ ≤ (tentWidth j)⁻¹ := inv_anti₀ hw hsw
          have h2 := abs_g_le n j t
          have h3 := hc0 j
          have h4 : 0 ≤ |s|⁻¹ := inv_nonneg.2 (abs_nonneg _)
          have h5 : 0 ≤ (tentWidth j)⁻¹ ^ n * bumpBound n :=
            mul_nonneg (by positivity) (bumpBound_nonneg n)
          gcongr
      _ = (tentWidth j)⁻¹ ^ (n + 1) * bumpBound n * c j := by ring
      _ ≤ (1 / 2) ^ (j + 1) := hbound n j (hnJ.trans hJj)
  have hsum := sum_mem_smul hKc h0 (Finset.range N) (fun j _ ↦ hcoef j) hterm
  refine mem_smul_of_le hKc h0 hsum (Finset.sum_nonneg fun j _ ↦ hcoef j) ?_
  calc ∑ j ∈ Finset.range N, coef j ≤ ∑ j ∈ Finset.Ico J (max J N), (1 / 2 : ℝ) ^ (j + 1) := by
        rw [Finset.range_eq_Ico]
        calc ∑ j ∈ Finset.Ico 0 N, coef j ≤ ∑ j ∈ Finset.Ico 0 (max J N), coef j :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.Ico_subset_Ico le_rfl (le_max_right _ _)) fun j _ _ ↦ hcoef j
          _ = ∑ j ∈ Finset.Ico J (max J N), coef j := by
              rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le J) (le_max_left J N),
                Finset.sum_eq_zero fun j hj ↦ ?_, zero_add]
              have hj' : ¬ J ≤ j := by have := (Finset.mem_Ico.1 hj).2; omega
              simp only [coef, hj', ↓reduceIte]
          _ = _ := Finset.sum_congr rfl fun j hj ↦ by
              simp only [coef, (Finset.mem_Ico.1 hj).1, ↓reduceIte]
    _ = (1 / 2) ^ J - (1 / 2) ^ (max J N) := sum_Ico_half_pow (le_max_left _ _)
    _ ≤ (1 / 2) ^ J := by linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (max J N)]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem hasDirDerivAt_D_one {K : Set E} (hKb : Bornology.IsVonNBounded ℝ K)
    (hKc : Convex ℝ K) (h0 : (0 : E) ∈ K) (hneg : ∀ x ∈ K, -x ∈ K) {e : ℕ → E} {c : ℕ → ℝ}
    (hc0 : ∀ j, 0 ≤ c j) (he : ∀ j, e j ∈ c j • K)
    (hbound : ∀ n j, n ≤ j → (tentWidth j)⁻¹ ^ (n + 1) * bumpBound n * c j ≤ (1 / 2) ^ (j + 1))
    (n : ℕ) : HasDirDerivAt (D n e) 1 1 (D (n + 1) e 1) := by
  rw [D_eq_zero_of_one_le (n + 1) e le_rfl]
  unfold HasDirDerivAt
  rw [D_eq_zero_of_one_le n e le_rfl]
  intro W hW
  rw [Filter.mem_map]
  obtain ⟨W', hW', hW'W⟩ : ∃ W' ∈ 𝓝 (0 : E), W' ⊆ W := ⟨W, hW, subset_rfl⟩
  have hev : ∀ᶠ J in atTop, MapsTo (((1 / 2 : ℝ) ^ J) • ·) K W' :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).eventually
      ((hKb hW').eventually_nhds_zero (mem_of_mem_nhds hW'))
  obtain ⟨J, hJ⟩ := (hev.and (eventually_ge_atTop n)).exists
  have hball : Metric.ball (0 : ℝ) (5 / 8 * (1 / 2) ^ J) ∈ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds _ (by positivity))
  filter_upwards [hball] with s hs
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
  have h := quotient_mem_smul hKc h0 hneg hc0 he hbound hJ.2 hs
  obtain ⟨k, hk, hke⟩ := h
  refine hW'W ?_
  simp only [smul_eq_mul, mul_one, sub_zero]
  rw [← hke]
  exact hJ.1 hk

end Deriv

/-! ### Smoothness -/

section Smooth

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

/-- A curve with a sequence of continuous derivatives is smooth. -/
theorem smoothMBOn_of_derivSeq {Dn : ℕ → ℝ → E}
    (hd : ∀ n t, HasDirDerivAt (Dn n) t 1 (Dn (n + 1) t)) : SmoothMBOn (Dn 0) univ := by
  suffices h : ∀ k n, ContDiffMBOn k (Dn n) univ from fun k ↦ h k 0
  intro k
  induction k with
  | zero =>
    intro n
    exact (continuous_iff_continuousAt.2 fun t ↦
      continuousAt_of_hasDirDerivAt_one (hd n t)).continuousOn
  | succ k ih =>
    intro n
    have hdir : ∀ t h, HasDirDerivAt (Dn n) t h (h • Dn (n + 1) t) := fun t h ↦ by
      simpa using (hd n t).smul_dir h
    have hdMB : dMB (Dn n) = fun p : ℝ × ℝ ↦ p.2 • Dn (n + 1) p.1 :=
      funext fun p ↦ (hdir p.1 p.2).dMB_eq
    refine ⟨(ih n).continuousOn, fun t _ h ↦ ?_, ?_⟩
    · rw [(hdir t h).dMB_eq]; exact hdir t h
    · rw [hdMB]
      have hU : IsOpen ((univ : Set ℝ) ×ˢ (univ : Set ℝ)) := isOpen_univ.prod isOpen_univ
      exact ContDiffMBOn.smul_fun hU
        (((ContinuousLinearMap.snd ℝ ℝ ℝ).contDiffMBOn k univ).mono (subset_univ _))
        (ContDiffMBOn.comp (g := Dn (n + 1)) (f := fun p : ℝ × ℝ ↦ p.1) hU isOpen_univ
          (ih (n + 1)) (((ContinuousLinearMap.fst ℝ ℝ ℝ).contDiffMBOn k univ).mono
            (subset_univ _)) (mapsTo_univ _ _))

end Smooth

/-! ### Mackey completeness -/

section Mackey

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

/-- **If smooth curves have weak integrals on `[0, 1]`, then `E` is Mackey complete**
(compare [GN26, Remark 1.1.18(c)]). As in lc-analysis's
`MackeyComplete.of_integratesLipschitzCurves`, a fast subsequence of a Mackey–Cauchy sequence is
integrated along a curve made of bumps; here the bumps are smooth, and the coefficients decay
fast enough for the curve to be smooth at `t = 1`. -/
theorem mackeyComplete_of_integratesSmooth
    (h : ∀ γ : ℝ → E, SmoothMBOn γ univ → ∃ y, HasWeakIntegral γ 0 1 y) : MackeyComplete E where
  exists_tendsto u B r hB hr hu := by
    -- the absolutely convex hull `K` of `B`
    set K := convexHull ℝ (insert 0 (B ∪ -B))
    have hKc : Convex ℝ K := convex_convexHull ℝ _
    have h0 : (0 : E) ∈ K := subset_convexHull ℝ _ (mem_insert _ _)
    have hBK : B ⊆ K := fun x hx ↦ subset_convexHull ℝ _ (mem_insert_of_mem _ (Or.inl hx))
    have hneg : ∀ x ∈ K, -x ∈ K := fun x hx ↦ by
      have hs : -(insert (0 : E) (B ∪ -B)) = insert 0 (B ∪ -B) := by
        ext y; simp [or_comm]
      have : -x ∈ -K := Set.neg_mem_neg.mpr hx
      rwa [← convexHull_neg, hs] at this
    have hKb : Bornology.IsVonNBounded ℝ K :=
      isVonNBounded_convexHull ((hB.union hB.neg).insert 0)
    -- the coefficients
    set M : ℕ → ℝ := fun j ↦
      1 + ∑ n ∈ Finset.range (j + 1), (tentWidth j)⁻¹ ^ (n + 1) * bumpBound n
    have hM : ∀ j, 1 ≤ M j := fun j ↦ by
      have : 0 ≤ ∑ n ∈ Finset.range (j + 1), (tentWidth j)⁻¹ ^ (n + 1) * bumpBound n :=
        Finset.sum_nonneg fun n _ ↦ mul_nonneg (by have := tentWidth_pos j; positivity)
          (bumpBound_nonneg n)
      simp only [M]; linarith
    set c : ℕ → ℝ := fun j ↦ (1 / 2) ^ (j + 1) / M j
    have hc : ∀ j, 0 < c j := fun j ↦ div_pos (by positivity) (by linarith [hM j])
    have hbound : ∀ n j, n ≤ j →
        (tentWidth j)⁻¹ ^ (n + 1) * bumpBound n * c j ≤ (1 / 2) ^ (j + 1) := by
      intro n j hnj
      have hle : (tentWidth j)⁻¹ ^ (n + 1) * bumpBound n ≤ M j := by
        have := Finset.single_le_sum (f := fun n ↦ (tentWidth j)⁻¹ ^ (n + 1) * bumpBound n)
          (fun n _ ↦ mul_nonneg (by have := tentWidth_pos j; positivity) (bumpBound_nonneg n))
          (Finset.mem_range.2 (Nat.lt_succ_of_le hnj))
        simp only [M]; linarith
      have hMpos : 0 < M j := by linarith [hM j]
      calc (tentWidth j)⁻¹ ^ (n + 1) * bumpBound n * c j
          ≤ M j * c j := mul_le_mul_of_nonneg_right hle (hc j).le
        _ = (1 / 2) ^ (j + 1) := by simp only [c]; field_simp
    have hc0 : ∀ j, bumpBound 0 * c j ≤ (1 / 2) ^ (j + 1) := fun j ↦ by
      have := hbound 0 j (Nat.zero_le j)
      have hw : 1 ≤ (tentWidth j)⁻¹ := by
        rw [one_le_inv₀ (tentWidth_pos j)]
        exact (tentWidth_le j).trans (by norm_num)
      calc bumpBound 0 * c j ≤ (tentWidth j)⁻¹ ^ (0 + 1) * bumpBound 0 * c j := by
            rw [zero_add, pow_one, mul_assoc]
            exact le_mul_of_one_le_left (mul_nonneg (bumpBound_nonneg 0) (hc j).le) hw
        _ ≤ _ := this
    -- a fast subsequence
    set ε : ℕ → ℝ := fun j ↦ c j * tentWidth j
    have hε : ∀ j, 0 < ε j := fun j ↦ mul_pos (hc j) (tentWidth_pos j)
    obtain ⟨n, hn, hnε⟩ := extraction_forall_of_eventually (P := fun j k ↦ |r k| ≤ ε j)
      fun j ↦ by
        obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hr (ε j) (hε j)
        exact eventually_atTop.mpr ⟨N, fun k hk ↦ by
          have := hN k hk; rw [Real.dist_eq, sub_zero] at this; exact this.le⟩
    -- the increments, rescaled
    set d : ℕ → E := fun j ↦ u (n (j + 1)) - u (n j)
    set e : ℕ → E := fun j ↦ (tentWidth j)⁻¹ • d j
    have he : ∀ j, e j ∈ c j • K := fun j ↦ by
      obtain ⟨b, hb, hbe⟩ := hu (n j) (n (j + 1)) (hn (Nat.lt_succ_self j)).le
      have hw := tentWidth_pos j
      have hμ : |(tentWidth j)⁻¹ * r (n j)| ≤ c j := by
        rw [abs_mul, abs_of_pos (inv_pos.2 hw)]
        calc (tentWidth j)⁻¹ * |r (n j)| ≤ (tentWidth j)⁻¹ * ε j := by
              gcongr; exact hnε j
          _ = c j := by simp only [ε]; field_simp
      have := smul_mem_smul_of_abs_le hKc h0 hneg (hBK hb) hμ
      simp only [e, d, ← hbe, smul_smul]
      exact this
    -- the smooth curve
    set γ := D 0 e
    have hγd : ∀ k t, HasDirDerivAt (D k e) t 1 (D (k + 1) e t) := fun k t ↦ by
      rcases lt_trichotomy t 1 with ht | rfl | ht
      · exact hasDirDerivAt_D_of_lt k e ht
      · exact hasDirDerivAt_D_one hKb hKc h0 hneg (fun j ↦ (hc j).le) he hbound k
      · exact hasDirDerivAt_D_of_gt k e ht
    have hγs : SmoothMBOn γ univ := smoothMBOn_of_derivSeq (Dn := fun k ↦ D k e) hγd
    obtain ⟨y, hy⟩ := h γ hγs
    have hγc : ContinuousOn γ (Icc 0 1) := (hγs 0).continuousOn.mono (subset_univ _)
    have hcont : ∀ N, Continuous (S 0 e N) := fun N ↦
      continuous_iff_continuousAt.2 fun t ↦
        continuousAt_of_hasDirDerivAt_one (hasDirDerivAt_S 0 e N t)
    -- the weak integral of the partial sums is `u (n N) - u (n 0)`
    have hGint : ∀ N, HasWeakIntegral (S 0 e N) 0 1 (u (n N) - u (n 0)) := by
      intro N
      induction N with
      | zero =>
        have : S 0 e 0 = fun _ ↦ 0 := by funext t; simp [S]
        rw [this, sub_self]
        simpa using hasWeakIntegral_const (0 : E) 0 1
      | succ N ih =>
        have hfun : S 0 e (N + 1) = fun t ↦ S 0 e N t + g 0 N t • e N := by
          funext t; simp only [S, Finset.sum_range_succ]
        have hgc : Continuous (g 0 N) :=
          continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_g 0 N t).continuousAt
        have hterm : HasWeakIntegral (fun t ↦ g 0 N t • e N) 0 1 (d N) := by
          intro φ
          simp only [map_smul, smul_eq_mul]
          rw [intervalIntegral.integral_mul_const, integral_g]
          have hw := tentWidth_pos N
          simp only [e, map_smul, smul_eq_mul]
          field_simp
        have := ih.add (hcont N).continuousOn (hgc.smul continuous_const).continuousOn hterm
        rw [hfun]
        convert this using 1
        simp only [d]; abel
    -- the subsequence converges to `u (n 0) + y`
    have hconv : Tendsto (fun N ↦ u (n N)) atTop (𝓝 (u (n 0) + y)) := by
      have hsmall : Tendsto (fun N ↦ y - (u (n N) - u (n 0))) atTop (𝓝 0) := by
        intro W hW
        rw [Filter.mem_map]
        obtain ⟨W', hW', hW'c, hW'conv, hW'W⟩ := exists_closed_convex_two_smul_subset hW
        have hev : ∀ᶠ N in atTop, MapsTo (((1 / 2 : ℝ) ^ N) • ·) K W' :=
          (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).eventually
            ((hKb hW').eventually_nhds_zero (mem_of_mem_nhds hW'))
        filter_upwards [hev] with N hN
        have hdiff := hy.sub zero_le_one hγc (hcont N).continuousOn (hGint N)
        have hmem := hdiff.mem_smul zero_le_one (hγc.sub (hcont N).continuousOn) hW'conv hW'c
          (mem_of_mem_nhds hW') fun t _ ↦ by
            obtain ⟨M', hM', hNM⟩ := ((eventually_D_eq 0 e t).and
              (eventually_ge_atTop N)).exists
            have hIco : γ t - S 0 e N t = ∑ j ∈ Finset.Ico N M', g 0 j t • e j := by
              simp only [γ, hM', S]
              rw [← Finset.sum_range_add_sum_Ico _ hNM, add_sub_cancel_left]
            rw [Pi.sub_apply, hIco]
            have hmem := sum_mem_smul hKc h0 (Finset.Ico N M')
              (c := fun j ↦ (1 / 2 : ℝ) ^ (j + 1)) (fun j _ ↦ by positivity)
              (x := fun j ↦ g 0 j t • e j) fun j _ ↦ by
                obtain ⟨k, hk, hke⟩ := he j
                simp only at hke
                rw [← hke, smul_smul]
                refine smul_mem_smul_of_abs_le hKc h0 hneg hk ?_
                rw [abs_mul, abs_of_pos (hc j)]
                refine le_trans ?_ (hc0 j)
                have := abs_g_le 0 j t
                rw [pow_zero, one_mul] at this
                exact mul_le_mul_of_nonneg_right this (hc j).le
            have hle : ∑ j ∈ Finset.Ico N M', (1 / 2 : ℝ) ^ (j + 1) ≤ (1 / 2) ^ N := by
              rw [sum_Ico_half_pow hNM]
              linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) M']
            obtain ⟨k, hk, hke⟩ := mem_smul_of_le hKc h0 hmem
              (Finset.sum_nonneg fun j _ ↦ by positivity) hle
            rw [← hke]
            exact hN hk
        exact hW'W (by norm_num at hmem ⊢; exact hmem)
      have := (tendsto_const_nhds (x := u (n 0) + y)).sub hsmall
      simp only [sub_zero] at this
      convert this using 2 with N
      abel
    exact ⟨u (n 0) + y, tendsto_of_mackeyCauchy_of_subseq hB hr hu hn hconv⟩

end Mackey

end LocallyConvex.LieGroups.MackeyConverse

namespace LocallyConvex.LieGroups.VectorGroup

open MBLieGroup MackeyConverse

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

/-- **Regular vector groups are Mackey complete** ([GN26, Proposition 6.1.3], the other
direction): a smooth curve `γ` restricts to `ξ ∈ C^∞([0, 1], E)`, whose evolution `Γ` has
derivative `ξ̃`, so `∫₀¹ γ = Γ(1) − Γ(0)`. -/
theorem mackeyComplete_of_isRegular (h : IsRegular E (Multiplicative E)) : MackeyComplete E := by
  refine mackeyComplete_of_integratesSmooth fun γ hγ ↦ ?_
  classical
  set f : ℝ → E := fun t ↦ if t ∈ Icc (0 : ℝ) 1 then γ t else 0
  have hf : SmoothLC f (Icc (0 : ℝ) 1) := fun k ↦
    ((hγ k).contDiffLC isOpen_univ (subset_univ _) hasDenseInterior_Icc).congr fun t ht ↦ by
      simp only [f, ht, ↓reduceIte]
  set ξ : SmoothCurve E := SmoothLCMap.mk f hf fun t ht ↦ by simp only [f, ht, ↓reduceIte]
  obtain ⟨Γ, hΓ⟩ := h.semiregular ξ
  set ξ' := extendCurve (SmoothCurve.toC0 ξ)
  have hξ' : ∀ t ∈ Icc (0 : ℝ) 1, ξ' t = γ t := fun t ht ↦ by
    change f (projIcc (0 : ℝ) 1 zero_le_one t : ℝ) = γ t
    rw [projIcc_of_mem _ ht]
    simp only [f, ht, ↓reduceIte]
  have hd : ∀ t, HasDirDerivAt (fun s ↦ Multiplicative.toAdd (Γ s)) t 1 (ξ' t) := fun t ↦ by
    have h2 := (hΓ.2 t).2.add (show HasDirDerivAt (fun _ : ℝ ↦ Multiplicative.toAdd (Γ t)) t 1 0
      by simp only [HasDirDerivAt, sub_self, smul_zero]; exact tendsto_const_nhds)
    rw [add_zero] at h2
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ ?_)
    change -Multiplicative.toAdd (Γ t) + Multiplicative.toAdd (Γ s) + Multiplicative.toAdd (Γ t) =
      Multiplicative.toAdd (Γ s)
    abel
  have hint := hasWeakIntegral_sub_of_hasDirDerivAt (fun t _ ↦ hd t)
    (continuous_extendCurve _).continuousOn (a := 0) (b := 1)
  refine ⟨Multiplicative.toAdd (Γ 1) - Multiplicative.toAdd (Γ 0), fun φ ↦ ?_⟩
  rw [hint φ]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le zero_le_one] at ht
  simp only [hξ' t ht]

/-- **[GN26, Proposition 6.1.3]**: for `k ≥ 1`, `(E, +)` is `C^k`-regular if and only if `E` is
Mackey complete. -/
theorem isCkRegular_iff {k : ℕ} (hk : 1 ≤ k) :
    IsCkRegular E (Multiplicative E) k ↔ MackeyComplete E :=
  ⟨fun h ↦ mackeyComplete_of_isRegular h.isRegular, fun _ ↦ isCkRegular hk⟩

/-- **[GN26, Proposition 6.1.3]**, `k = ∞`: `(E, +)` is regular if and only if `E` is Mackey
complete. -/
theorem isRegular_iff : IsRegular E (Multiplicative E) ↔ MackeyComplete E :=
  ⟨mackeyComplete_of_isRegular, fun _ ↦ isRegular_of_mackeyComplete⟩

end LocallyConvex.LieGroups.VectorGroup
