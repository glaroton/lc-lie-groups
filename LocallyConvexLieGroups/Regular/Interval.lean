/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Regular.Local

/-!
# Evolutions on `[0, 1]`

[GN26, Definition 6.1.1] solves `γ(0) = 1`, `δ(γ) = ξ` on `[0, 1]`, with one-sided derivatives at
the endpoints; `LocallyConvexLieGroups.Regular.Evol` solves it on `ℝ` for the extension `ξ̃` of `ξ`
by constants. We show that the two notions of `C⁰`-semiregularity and `C⁰`-regularity agree.

## Main definitions

* `MBLieGroup.HasLogDerivWithinAt γ x s t`: `δ(γ)(t) = x` within `s`.
* `MBLieGroup.IsEvolOn ξ γ`: `γ(0) = 1` and `δ(γ)(t) = ξ(t)` within `[0, 1]` for `t ∈ [0, 1]`.
* `MBLieGroup.IsC0SemiregularGN`, `MBLieGroup.evolGN`, `MBLieGroup.IsC0RegularGN`: the notions of
  [GN26, Definition 6.1.1] (`k = 0`).

## Main results

* `MBLieGroup.HasLogDerivWithinAt.hasLogDerivAt_of_Iic_Ici`: one-sided logarithmic derivatives
  that agree give a logarithmic derivative.
* `MBLieGroup.IsEvolOn.oneParam`: a solution on `[0, 1]` for a constant curve `x` extends to the
  one-parameter group `P(t) = γ(1)^⌊t⌋ γ(t − ⌊t⌋)`.
* `MBLieGroup.IsEvolOn.exists_isEvol`: under `C⁰`-semiregularity on `[0, 1]`, every solution on
  `[0, 1]` extends to a solution on `ℝ`, continued by one-parameter groups beyond `[0, 1]`.
* `MBLieGroup.isC0Semiregular_iff`, `MBLieGroup.isC0Regular_iff`: **the two notions agree.**

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology unitInterval
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups.MBLieGroup

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]

/-! ### Slopes -/

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
/-- Derivatives of curves as limits of slopes. -/
theorem hasDirDerivAt_one_iff_slope {f : ℝ → E} {t : ℝ} {x : E} :
    HasDirDerivAt f t 1 x ↔ Tendsto (fun r ↦ (r - t)⁻¹ • (f r - f t)) (𝓝[≠] t) (𝓝 x) := by
  have h₁ : Tendsto (fun h : ℝ ↦ t + h) (𝓝[≠] 0) (𝓝[≠] t) :=
    tendsto_nhdsWithin_iff.2 ⟨(Continuous.tendsto' (by fun_prop) 0 t (by simp)).mono_left
      nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun h (hh : h ≠ 0) ↦ by simpa using hh⟩
  have h₂ : Tendsto (fun r : ℝ ↦ r - t) (𝓝[≠] t) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨(Continuous.tendsto' (by fun_prop) t 0 (by simp)).mono_left
      nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun r (hr : r ≠ t) ↦
        sub_ne_zero.2 hr⟩
  unfold HasDirDerivAt
  constructor
  · intro h
    refine (h.comp h₂).congr fun r ↦ ?_
    simp
  · intro h
    refine (h.comp h₁).congr fun r ↦ ?_
    simp

/-! ### One-sided logarithmic derivatives -/

variable (E) in
/-- **The logarithmic derivative within `s`**: `δ(γ)(t) = x` within `s`. -/
def HasLogDerivWithinAt (γ : ℝ → G) (x : E) (s : Set ℝ) (t : ℝ) : Prop :=
  ContinuousWithinAt γ s t ∧
    Tendsto (fun r ↦ (r - t)⁻¹ • (chartAt E (1 : G) ((γ t)⁻¹ * γ r) -
      chartAt E (1 : G) ((γ t)⁻¹ * γ t))) (𝓝[s \ {t}] t) (𝓝 x)

variable {γ γ' : ℝ → G} {x : E} {s s' : Set ℝ} {t : ℝ}

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] in
theorem HasLogDerivAt.hasLogDerivWithinAt (h : HasLogDerivAt E γ x t) (s : Set ℝ) :
    HasLogDerivWithinAt E γ x s t :=
  ⟨h.1.continuousWithinAt, (hasDirDerivAt_one_iff_slope.1 h.2).mono_left
    (nhdsWithin_mono _ fun _ hr ↦ hr.2)⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] in
/-- **Localization**: if `s' ⊆ s` near `t`. -/
theorem HasLogDerivWithinAt.mono_of_nhds (h : HasLogDerivWithinAt E γ x s t) {U : Set ℝ}
    (hU : U ∈ 𝓝 t) (hsub : s' ∩ U ⊆ s) : HasLogDerivWithinAt E γ x s' t := by
  refine ⟨h.1.mono_of_mem_nhdsWithin (mem_nhdsWithin_iff_exists_mem_nhds_inter.2
    ⟨U, hU, fun r hr ↦ hsub ⟨hr.2, hr.1⟩⟩), h.2.mono_left (nhdsWithin_le_of_mem ?_)⟩
  exact mem_nhdsWithin_iff_exists_mem_nhds_inter.2
    ⟨U, hU, fun r hr ↦ ⟨hsub ⟨hr.2.1, hr.1⟩, hr.2.2⟩⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] in
theorem HasLogDerivWithinAt.congr (h : HasLogDerivWithinAt E γ x s t)
    (heq : γ' =ᶠ[𝓝[s] t] γ) (ht : γ' t = γ t) : HasLogDerivWithinAt E γ' x s t := by
  refine ⟨h.1.congr_of_eventuallyEq heq ht, h.2.congr' ?_⟩
  filter_upwards [nhdsWithin_mono t sdiff_subset heq] with r hr
  simp only [hr, ht]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] in
theorem HasLogDerivWithinAt.mul_left [IsTopologicalGroup G] (h : HasLogDerivWithinAt E γ x s t)
    (g : G) : HasLogDerivWithinAt E (fun r ↦ g * γ r) x s t := by
  refine ⟨continuousWithinAt_const.mul h.1, h.2.congr fun r ↦ ?_⟩
  simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] in
theorem HasLogDerivWithinAt.comp_add_const (c : ℝ) (h : HasLogDerivWithinAt E γ x s (t + c)) :
    HasLogDerivWithinAt E (fun r ↦ γ (r + c)) x ((· + c) ⁻¹' s) t := by
  have hT : Tendsto (fun r : ℝ ↦ r + c) (𝓝[(· + c) ⁻¹' s \ {t}] t) (𝓝[s \ {t + c}] (t + c)) :=
    tendsto_nhdsWithin_iff.2 ⟨(Continuous.tendsto (by fun_prop) t).mono_left
      nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun r hr ↦
        ⟨hr.1, fun h' ↦ hr.2 (add_right_cancel h')⟩⟩
  refine ⟨ContinuousWithinAt.comp (g := γ) (f := fun r : ℝ ↦ r + c) h.1
    (by fun_prop : Continuous fun r : ℝ ↦ r + c).continuousWithinAt (mapsTo_preimage _ _),
    (h.2.comp hT).congr fun r ↦ ?_⟩
  simp

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] in
/-- A logarithmic derivative within a neighborhood is a logarithmic derivative. -/
theorem HasLogDerivWithinAt.hasLogDerivAt (h : HasLogDerivWithinAt E γ x s t) (hs : s ∈ 𝓝 t) :
    HasLogDerivAt E γ x t := by
  refine ⟨h.1.continuousAt hs, hasDirDerivAt_one_iff_slope.2 (h.2.mono_left ?_)⟩
  rw [sdiff_eq, nhdsWithin_inter, nhdsWithin_eq_nhds.2 hs]
  exact le_inf nhdsWithin_le_nhds le_rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] in
/-- **Gluing one-sided logarithmic derivatives.** -/
theorem HasLogDerivWithinAt.hasLogDerivAt_of_Iic_Ici (h₁ : HasLogDerivWithinAt E γ x (Iic t) t)
    (h₂ : HasLogDerivWithinAt E γ x (Ici t) t) : HasLogDerivAt E γ x t := by
  refine ⟨continuousAt_iff_continuous_left_right.2 ⟨h₁.1, h₂.1⟩,
    hasDirDerivAt_one_iff_slope.2 ?_⟩
  rw [← nhdsLT_sup_nhdsGT]
  refine Tendsto.sup ?_ ?_
  · have := h₁.2; rwa [Iic_sdiff_right] at this
  · have := h₂.2; rwa [Ici_sdiff_left] at this

/-! ### Evolutions on `[0, 1]` -/

variable (E) in
/-- **`γ` is an evolution of `ξ` on `[0, 1]`** ([GN26, Definition 6.1.1]). -/
def IsEvolOn (ξ : ℝ → E) (γ : ℝ → G) : Prop :=
  γ 0 = 1 ∧ ∀ t ∈ Icc (0 : ℝ) 1, HasLogDerivWithinAt E γ (ξ t) (Icc 0 1) t

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] in
theorem IsEvol.isEvolOn {ξ : ℝ → E} (h : IsEvol E ξ γ) : IsEvolOn E ξ γ :=
  ⟨h.1, fun t _ ↦ (h.2 t).hasLogDerivWithinAt _⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] in
theorem IsEvolOn.hasLogDerivAt {ξ : ℝ → E} (h : IsEvolOn E ξ γ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasLogDerivAt E γ (ξ t) t :=
  (h.2 t (Ioo_subset_Icc_self ht)).hasLogDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- **One-parameter groups from solutions on `[0, 1]`**: `P(t) = γ(1)^⌊t⌋ γ(t − ⌊t⌋)`. -/
theorem IsEvolOn.oneParam (h : IsEvolOn E (fun _ ↦ x) γ) :
    IsEvol E (fun _ ↦ x) (fun t ↦ γ 1 ^ ⌊t⌋ * γ (Int.fract t)) := by
  have := isTopologicalGroup E G
  set P : ℝ → G := fun t ↦ γ 1 ^ ⌊t⌋ * γ (Int.fract t)
  refine ⟨by simp [P, h.1], fun t ↦ ?_⟩
  -- the pieces `P = γ(1)ⁿ γ(· − n)` on `[n, n + 1)`
  have hpiece : ∀ n : ℤ, ∀ r ∈ Ico (n : ℝ) (n + 1), P r = γ 1 ^ n * γ (r + -n) := by
    intro n r hr
    have hf : ⌊r⌋ = n := Int.floor_eq_iff.2 hr
    simp only [P, hf, Int.fract, ← sub_eq_add_neg]
  have hwithin : ∀ n : ℤ, ∀ r ∈ Icc (0 : ℝ) 1,
      HasLogDerivWithinAt E (fun r' ↦ γ 1 ^ n * γ (r' + -n)) x (Icc (n : ℝ) (n + 1)) (r + n) := by
    intro n r hr
    have h1 := (h.2 r hr)
    have h2 := HasLogDerivWithinAt.comp_add_const (-(n : ℝ)) (t := r + n)
      (by simpa using h1)
    have hset : (· + -(n : ℝ)) ⁻¹' Icc (0 : ℝ) 1 = Icc (n : ℝ) (n + 1) := by
      ext r'; simp only [mem_preimage, mem_Icc]; constructor <;> intro h <;> constructor <;>
        linarith [h.1, h.2]
    rw [hset] at h2
    exact h2.mul_left _
  rcases eq_or_ne (Int.fract t) 0 with ht | ht
  · -- `t = n` is an integer: glue `γ(1)^{n-1} γ(· − n + 1)` and `γ(1)ⁿ γ(· − n)`
    obtain ⟨n, rfl⟩ : ∃ n : ℤ, t = n := ⟨⌊t⌋, by
      have := Int.floor_add_fract t; rw [ht, add_zero] at this; exact this.symm⟩
    refine HasLogDerivWithinAt.hasLogDerivAt_of_Iic_Ici ?_ ?_
    · have hw := hwithin (n - 1) 1 ⟨zero_le_one, le_rfl⟩
      have hn : (1 : ℝ) + ((n - 1 : ℤ) : ℝ) = n := by push_cast; ring
      rw [hn] at hw
      have hloc := hw.mono_of_nhds (s' := Iic (n : ℝ)) (Ioi_mem_nhds (show ((n - 1 : ℤ) : ℝ) < n by
        push_cast; linarith)) fun r hr ↦ by
          obtain ⟨hr1, hr2⟩ := hr
          have hr1' : r ≤ n := hr1
          have hr2' : ((n - 1 : ℤ) : ℝ) < r := hr2
          push_cast at hr2' ⊢
          exact ⟨hr2'.le, by linarith⟩
      refine hloc.congr ?_ ?_
      · filter_upwards [Ioc_mem_nhdsLE (show ((n - 1 : ℤ) : ℝ) < n by push_cast; linarith)]
          with r hr
        rcases eq_or_lt_of_le hr.2 with rfl | hlt
        · simp only [P, Int.floor_intCast, Int.fract_intCast, h.1, mul_one]
          push_cast
          rw [show ((n : ℝ) + -((n : ℝ) - 1)) = 1 by ring, ← zpow_add_one, sub_add_cancel]
        · exact hpiece (n - 1) r ⟨hr.1.le, by push_cast; linarith⟩
      · simp only [P, Int.floor_intCast, Int.fract_intCast, h.1, mul_one]
        push_cast
        rw [show ((n : ℝ) + -((n : ℝ) - 1)) = 1 by ring, ← zpow_add_one, sub_add_cancel]
    · have hw := hwithin n 0 ⟨le_rfl, zero_le_one⟩
      rw [zero_add] at hw
      have hloc := hw.mono_of_nhds (s' := Ici (n : ℝ))
        (Iio_mem_nhds (show (n : ℝ) < n + 1 by linarith))
        fun r hr ↦ by
          obtain ⟨hr1, hr2⟩ := hr
          exact ⟨(hr1 : (n : ℝ) ≤ r), le_of_lt (hr2 : r < (n : ℝ) + 1)⟩
      refine hloc.congr ?_ (hpiece n n ⟨le_rfl, by linarith⟩)
      filter_upwards [Ico_mem_nhdsGE (show (n : ℝ) < n + 1 by linarith)] with r hr
      exact hpiece n r hr
  · -- `t` is not an integer
    set n := ⌊t⌋
    have hlt : (n : ℝ) < t := lt_of_le_of_ne (Int.floor_le t) fun h' ↦ ht (by
      rw [Int.fract, ← h', Int.floor_intCast, sub_self])
    have hlt' : t < n + 1 := Int.lt_floor_add_one t
    have hint : Int.fract t ∈ Ioo (0 : ℝ) 1 := ⟨by
      rw [Int.fract]; linarith, Int.fract_lt_one t⟩
    have h0 := h.hasLogDerivAt hint
    rw [show Int.fract t = t + -(n : ℝ) by rw [Int.fract, ← sub_eq_add_neg]] at h0
    have hd := (h0.comp_add_const (-(n : ℝ))).mul_left (γ 1 ^ n)
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hlt hlt'] with r hr
    exact hpiece n r ⟨hr.1.le, hr.2⟩

/-! ### Extension to `ℝ` -/

variable (E G) in
/-- **`C⁰`-semiregularity in the sense of [GN26, Definition 6.1.1]**: every `ξ ∈ C([0, 1], 𝔤)` has
an evolution on `[0, 1]` (curves `ℝ → G`, of which only the values on `[0, 1]` matter). -/
def IsC0SemiregularGN : Prop := ∀ ξ : C(I, E), ∃ γ : ℝ → G, IsEvolOn E (extendCurve ξ) γ

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] in
theorem extendCurve_of_nonpos (ξ : C(I, E)) {t : ℝ} (ht : t ≤ 0) :
    extendCurve ξ t = extendCurve ξ 0 := by
  rw [extendCurve_apply, extendCurve_apply, projIcc_of_le_left _ ht,
    projIcc_of_le_left _ le_rfl]

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] in
theorem extendCurve_of_one_le (ξ : C(I, E)) {t : ℝ} (ht : 1 ≤ t) :
    extendCurve ξ t = extendCurve ξ 1 := by
  rw [extendCurve_apply, extendCurve_apply, projIcc_of_right_le _ ht,
    projIcc_of_right_le _ le_rfl]

/-- `C⁰`-semiregularity on `[0, 1]` gives one-parameter groups. -/
theorem IsC0SemiregularGN.exists_isEvol_const (hGN : IsC0SemiregularGN E G) (x : E) :
    ∃ P : ℝ → G, IsEvol E (fun _ ↦ x) P := by
  obtain ⟨c, hc⟩ := hGN (ContinuousMap.const I x)
  rw [extendCurve_const] at hc
  exact ⟨_, hc.oneParam⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] in
/-- One-parameter groups are evolutions of constant curves. -/
theorem IsOneParam.isEvol {P : ℝ → G} (h : IsOneParam E P x) : IsEvol E (fun _ ↦ x) P := by
  refine ⟨h.map_zero, fun t ↦ ⟨h.continuous.continuousAt, hasDirDerivAt_shift ?_⟩⟩
  have hf : (fun r ↦ chartAt E (1 : G) ((P t)⁻¹ * P (t + r))) =
      fun r ↦ chartAt E (1 : G) (P r) := by
    funext r
    rw [← h.map_neg, ← h.map_add, neg_add_cancel_left]
  rw [hf]
  exact h.hasDirDerivAt

omit [MBLieGroup E G] in
/-- A Lie group with an exponential function has one-parameter groups. -/
theorem IsExp.exists_isEvol_const {exp : E → G} (h : IsExp E exp) (x : E) :
    ∃ P : ℝ → G, IsEvol E (fun _ ↦ x) P :=
  ⟨_, (h.isOneParam x).isEvol⟩

/-- **Solutions on `[0, 1]` extend to `ℝ`**, continued by the one-parameter groups of `ξ(0)` and
`ξ(1)` beyond `[0, 1]`. -/
theorem IsEvolOn.exists_isEvol (hP : ∀ x : E, ∃ P : ℝ → G, IsEvol E (fun _ ↦ x) P)
    {ξ : C(I, E)} {γ : ℝ → G} (h : IsEvolOn E (extendCurve ξ) γ) :
    ∃ Γ : ℝ → G, IsEvol E (extendCurve ξ) Γ ∧ EqOn Γ γ (Icc 0 1) := by
  have := isTopologicalGroup E G
  set x₀ := extendCurve ξ 0
  set x₁ := extendCurve ξ 1
  obtain ⟨P₀, hP₀⟩ := hP x₀
  obtain ⟨P₁, hP₁⟩ := hP x₁
  set Γ : ℝ → G := fun t ↦ if t ≤ 0 then P₀ t else if t ≤ 1 then γ t else γ 1 * P₁ (t + -1)
  have hΓL : ∀ t ≤ 0, Γ t = P₀ t := fun t ht ↦ by simp [Γ, ht]
  have hΓ : EqOn Γ γ (Icc 0 1) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | hlt
    · simp only [Γ, le_rfl, ↓reduceIte]; rw [hP₀.1, h.1]
    · simp [Γ, not_le.2 hlt, ht.2]
  have hΓR : ∀ t, 1 ≤ t → Γ t = γ 1 * P₁ (t + -1) := by
    intro t ht
    rcases eq_or_lt_of_le ht with rfl | hlt
    · rw [hΓ ⟨zero_le_one, le_rfl⟩, add_neg_cancel, hP₁.1, mul_one]
    · simp [Γ, not_le.2 (zero_lt_one.trans hlt), not_le.2 hlt]
  have hQ : ∀ t, HasLogDerivAt E (fun s ↦ γ 1 * P₁ (s + -1)) x₁ t := fun t ↦
    ((hP₁.2 (t + -1)).comp_add_const (-1)).mul_left (γ 1)
  refine ⟨Γ, ⟨by rw [hΓL 0 le_rfl]; exact hP₀.1, fun t ↦ ?_⟩, hΓ⟩
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [extendCurve_of_nonpos ξ ht.le]
    refine (hP₀.2 t).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds ht] with s hs using hΓL s (le_of_lt hs)
  · refine HasLogDerivWithinAt.hasLogDerivAt_of_Iic_Ici ?_ ?_
    · refine ((hP₀.2 0).hasLogDerivWithinAt _).congr ?_ (hΓL 0 le_rfl)
      filter_upwards [self_mem_nhdsWithin] with s hs using hΓL s hs
    · refine ((h.2 0 ⟨le_rfl, zero_le_one⟩).mono_of_nhds (s' := Ici 0)
        (Iio_mem_nhds zero_lt_one) fun r hr ↦ ⟨hr.1, le_of_lt hr.2⟩).congr ?_
        (hΓ ⟨le_rfl, zero_le_one⟩)
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)]
        with s hs0 hs1 using hΓ ⟨hs0, le_of_lt hs1⟩
  · rcases lt_trichotomy t 1 with ht1 | rfl | ht1
    · refine (h.hasLogDerivAt ⟨ht, ht1⟩).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds ht ht1] with s hs using hΓ ⟨hs.1.le, hs.2.le⟩
    · refine HasLogDerivWithinAt.hasLogDerivAt_of_Iic_Ici ?_ ?_
      · refine ((h.2 1 ⟨zero_le_one, le_rfl⟩).mono_of_nhds (s' := Iic 1)
          (Ioi_mem_nhds zero_lt_one) fun r hr ↦ ⟨le_of_lt hr.2, hr.1⟩).congr ?_
          (hΓ ⟨zero_le_one, le_rfl⟩)
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds zero_lt_one)]
          with s hs1 hs0 using hΓ ⟨le_of_lt hs0, hs1⟩
      · refine ((hQ 1).hasLogDerivWithinAt _).congr ?_ (hΓR 1 le_rfl)
        filter_upwards [self_mem_nhdsWithin] with s hs using hΓR s hs
    · rw [extendCurve_of_one_le ξ ht1.le]
      refine (hQ t).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds ht1] with s hs using hΓR s (le_of_lt hs)

/-- **The two notions of `C⁰`-semiregularity agree.** -/
theorem isC0Semiregular_iff : IsC0SemiregularGN E G ↔ IsC0Semiregular E G := by
  constructor
  · intro h ξ
    obtain ⟨γ, hγ⟩ := h ξ
    obtain ⟨Γ, hΓ, -⟩ := hγ.exists_isEvol h.exists_isEvol_const
    exact ⟨Γ, hΓ⟩
  · intro h ξ
    obtain ⟨γ, hγ⟩ := h ξ
    exact ⟨γ, hγ.isEvolOn⟩

/-- If `G` has one-parameter groups (e.g. an exponential function, or under
`C⁰`-semiregularity), every solution on `[0, 1]` ends at `evol(ξ)`. -/
theorem evol_eq_of_isEvolOn (hP : ∀ x : E, ∃ P : ℝ → G, IsEvol E (fun _ ↦ x) P)
    {ξ : C(I, E)} {γ : ℝ → G} (hγ : IsEvolOn E (extendCurve ξ) γ) : evol E G ξ = γ 1 := by
  obtain ⟨Γ, hΓ, heq⟩ := hγ.exists_isEvol hP
  rw [evol_eq hΓ, heq ⟨zero_le_one, le_rfl⟩]

open Classical in
variable (E G) in
/-- The evolution map of [GN26, Definition 6.1.1], from solutions on `[0, 1]`. -/
def evolGN (ξ : C(I, E)) : G :=
  if h : ∃ γ : ℝ → G, IsEvolOn E (extendCurve ξ) γ then h.choose 1 else 1

theorem evolGN_eq (h : IsC0SemiregularGN E G) : evolGN E G = evol E G := by
  funext ξ
  have hex := h ξ
  simp only [evolGN, hex, ↓reduceDIte]
  exact (evol_eq_of_isEvolOn h.exists_isEvol_const hex.choose_spec).symm

variable (E G) in
/-- **`C⁰`-regularity in the sense of [GN26, Definition 6.1.1].** -/
structure IsC0RegularGN : Prop where
  semiregular : IsC0SemiregularGN E G
  smooth : SmoothMBM C(I, E) E (evolGN E G)

/-- **The two notions of `C⁰`-regularity agree.** -/
theorem isC0Regular_iff : IsC0RegularGN E G ↔ IsC0Regular E G := by
  constructor
  · intro h
    refine ⟨isC0Semiregular_iff.1 h.1, ?_⟩
    rw [← evolGN_eq h.1]
    exact h.2
  · intro h
    have hs := isC0Semiregular_iff.2 h.1
    refine ⟨hs, ?_⟩
    rw [evolGN_eq hs]
    exact h.2

end LocallyConvex.LieGroups.MBLieGroup
