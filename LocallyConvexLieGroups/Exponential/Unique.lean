/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Exponential.Basic

/-!
# Uniqueness of one-parameter groups and of exponential functions

A one-parameter group `γ : ℝ → G` is determined by its derivative `x = γ'(0)` ([GN26,
Remark 5.6.4]: it solves `γ' = γ x`, whose solutions are unique by [GN26, Lemma 5.5.4]). Hence a
Lie group has at most one exponential function ([GN26, Proposition 5.6.3]), and exponential
functions are natural: `φ ∘ exp_G = exp_H ∘ L(φ)` for morphisms `φ` ([GN26,
Proposition 5.6.12]).

## Main definitions

* `MBLieGroup.IsOneParam γ x`: `γ` is a continuous one-parameter group with derivative `x` at `0`
  in the chart at the identity.

## Main results

* `MBLieGroup.IsOneParam.eq`: **two one-parameter groups with the same derivative at `0` are
  equal**.
* `MBLieGroup.IsExp.unique`: **a Lie group has at most one exponential function**
  ([GN26, Proposition 5.6.3]).
* `MBLieGroup.IsExp.map_hom`: **`φ ∘ exp_G = exp_H ∘ L(φ)`** ([GN26, Proposition 5.6.12]).

## Proof

Instead of the logarithmic derivative ([GN26, Lemma 5.5.4]) we argue in the chart `φ` at the
identity, where the multiplication is a local group law `∗`. For a one-parameter group `γ`, the
curve `c(t) = φ(γ(t))` satisfies `c(s + r) = c(s) ∗ c(r) = c(r) ∗ c(s)`, so
`c'(s) = x̃_l(c(s)) = x̃_r(c(s))`, where `x̃_l(z) = d(b ↦ z ∗ b)(1) x` and
`x̃_r(z) = d(a ↦ a ∗ z)(1) x`. For two one-parameter groups `γ₁`, `γ₂` with derivative `x`, the
curve `e(s) = φ(γ₁(−s) γ₂(s)) = c₁(−s) ∗ c₂(s)` has derivative
`−dm(a, b)(x̃_l(a), 0) + dm(a, b)(0, x̃_r(b)) = 0` (`a = c₁(−s)`, `b = c₂(s)`): both terms are the
derivative of `t ↦ (a ∗ (1 + t x)) ∗ b = a ∗ ((1 + t x) ∗ b)` at `0`. So `e` is constant near `0`,
`γ₁ = γ₂` near `0`, and everywhere since `γ(t) = γ(t/n)ⁿ`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups

universe u

/-! ### Curves -/

section Curves

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem hasDirDerivAt_const_curve (a : E) (s : ℝ) :
    HasDirDerivAt (fun _ : ℝ ↦ a) s 1 0 := by
  simp only [HasDirDerivAt, sub_self, smul_zero]; exact tendsto_const_nhds

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem hasDirDerivAt_shift {c : ℝ → E} {s : ℝ} {y : E}
    (h : HasDirDerivAt (fun r ↦ c (s + r)) 0 1 y) : HasDirDerivAt c s 1 y := by
  unfold HasDirDerivAt at h ⊢; simpa using h

omit [IsTopologicalAddGroup E] [LocallyConvexSpace ℝ E] in
theorem hasDirDerivAt_comp_neg {c : ℝ → E} {s : ℝ} {y : E}
    (h : HasDirDerivAt c (-s) 1 y) : HasDirDerivAt (fun r ↦ c (-r)) s 1 (-y) := by
  have h' := h.smul_dir (-1)
  rw [neg_one_smul ℝ y] at h'
  unfold HasDirDerivAt at h' ⊢
  refine h'.congr fun t ↦ ?_
  simp only [smul_eq_mul, mul_one, mul_neg, neg_add]

/-- A curve with vanishing derivative on an open interval is constant there. -/
theorem eq_of_hasDirDerivAt_zero {e : ℝ → E} {J : Set ℝ} (hJ : IsOpen J) (hJ' : IsPreconnected J)
    (h : ∀ s ∈ J, HasDirDerivAt e s 1 0) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) : e s = e t := by
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)]
  intro ψ
  have hd : ∀ r ∈ J, HasDerivAt (fun r ↦ ψ (e r)) 0 r := fun r hr ↦ by
    have h1 := (h r hr).clm_comp_real ψ
    rw [map_zero] at h1
    rw [hasDerivAt_iff_tendsto_slope_zero]
    unfold HasDirDerivAt at h1
    simpa [smul_eq_mul] using h1
  exact hJ.is_const_of_deriv_eq_zero hJ'
    (fun r hr ↦ (hd r hr).differentiableAt.differentiableWithinAt) (fun r hr ↦ (hd r hr).deriv)
    hs ht

end Curves

/-! ### Right invariant fields of a local group law -/

namespace LocalGroupLaw

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] (L : LocalGroupLaw E)

/-- The local right invariant vector field `x̃_r(z) = d(a ↦ a ∗ z)(1) x`. -/
def xr (x z : E) : E := dMB L.mul ((L.one, z), (x, 0))

theorem xr_eq (x z : E) : L.xr x z = dMB (fun a ↦ L.mul (a, z)) (L.one, x) :=
  dMB_slice L.mul L.one x z

/-- The right multiplications `a ↦ a ∗ z` are smooth. -/
theorem contDiffMBOn_mul_right (k : ℕ) (z : E) :
    ContDiffMBOn k (fun a ↦ L.mul (a, z)) {a | (a, z) ∈ L.dom} :=
  ContDiffMBOn.comp (g := L.mul) (f := fun a ↦ (a, z)) (L.isOpen_dom.preimage (by fun_prop))
    L.isOpen_dom (L.smooth k) ((smoothMBOn_id _ k).prodMk (L.isOpen_dom.preimage (by fun_prop))
      (contDiffMBOn_const k z _)) fun _ h ↦ h

theorem hasDirDerivAt_mul_one_add (a x : E) (ha : (a, L.one) ∈ L.dom) :
    HasDirDerivAt (fun t : ℝ ↦ L.mul (a, L.one + t • x)) 0 1 (L.xl x a) := by
  have h := (L.smooth 1).hasDirDerivAt (k := 0) ha ((0 : E), x)
  rw [show L.xl x a = dMB L.mul ((a, L.one), ((0 : E), x)) from rfl]
  unfold HasDirDerivAt at h ⊢
  simpa using h

theorem hasDirDerivAt_one_add_mul (b x : E) (hb : (L.one, b) ∈ L.dom) :
    HasDirDerivAt (fun t : ℝ ↦ L.mul (L.one + t • x, b)) 0 1 (L.xr x b) := by
  have h := (L.smooth 1).hasDirDerivAt (k := 0) hb (x, (0 : E))
  rw [show L.xr x b = dMB L.mul ((L.one, b), (x, (0 : E))) from rfl]
  unfold HasDirDerivAt at h ⊢
  simpa using h

/-- Derivatives of products of curves. -/
theorem hasDirDerivAt_mul_curve {a b : ℝ → E} {s : ℝ} {a' b' : E} (ha : HasDirDerivAt a s 1 a')
    (hb : HasDirDerivAt b s 1 b') (hab : (a s, b s) ∈ L.dom) :
    HasDirDerivAt (fun r ↦ L.mul (a r, b r)) s 1 (dMB L.mul ((a s, b s), (a', b'))) :=
  (L.smooth 1).hasDirDerivAt_comp L.isOpen_dom (ha.prodMk hb) hab

/-- **`dm(a, b)(x̃_l(a), 0) = dm(a, b)(0, x̃_r(b))`**: both are the derivative at `0` of
`t ↦ (a ∗ (1 + t x)) ∗ b = a ∗ ((1 + t x) ∗ b)`. -/
theorem dMB_xl_eq_xr {a b : E} (x : E) (hab : (a, b) ∈ L.dom) (ha : (a, L.one) ∈ L.dom)
    (hb : (L.one, b) ∈ L.dom) :
    dMB L.mul ((a, b), (L.xl x a, 0)) = dMB L.mul ((a, b), (0, L.xr x b)) := by
  have hf : HasDirDerivAt (fun t : ℝ ↦ L.mul (L.mul (a, L.one + t • x), b)) 0 1
      (dMB L.mul ((a, b), (L.xl x a, 0))) := by
    have h := L.hasDirDerivAt_mul_curve (L.hasDirDerivAt_mul_one_add a x ha)
      (hasDirDerivAt_const_curve b 0) (by simpa [L.mul_one a ha] using hab)
    simpa [L.mul_one a ha] using h
  have hg : HasDirDerivAt (fun t : ℝ ↦ L.mul (a, L.mul (L.one + t • x, b))) 0 1
      (dMB L.mul ((a, b), (0, L.xr x b))) := by
    have h := L.hasDirDerivAt_mul_curve (hasDirDerivAt_const_curve a 0)
      (L.hasDirDerivAt_one_add_mul b x hb) (by simpa [L.one_mul b hb] using hab)
    simpa [L.one_mul b hb] using h
  -- the two curves agree near `0`
  have hc1 : ContinuousAt (fun t : ℝ ↦ (a, L.one + t • x)) 0 := by fun_prop
  have hc2 : ContinuousAt (fun t : ℝ ↦ (L.one + t • x, b)) 0 := by fun_prop
  have e1 : (fun t : ℝ ↦ (a, L.one + t • x)) 0 ∈ L.dom := by simpa using ha
  have e2 : (fun t : ℝ ↦ (L.one + t • x, b)) 0 ∈ L.dom := by simpa using hb
  have hL1 : ContinuousAt L.mul ((fun t : ℝ ↦ (a, L.one + t • x)) 0) :=
    (L.smooth 0).continuousOn.continuousAt (L.isOpen_dom.mem_nhds e1)
  have hL2 : ContinuousAt L.mul ((fun t : ℝ ↦ (L.one + t • x, b)) 0) :=
    (L.smooth 0).continuousOn.continuousAt (L.isOpen_dom.mem_nhds e2)
  have hm1 : ContinuousAt (fun t : ℝ ↦ (L.mul (a, L.one + t • x), b)) 0 :=
    (ContinuousAt.comp (f := fun t : ℝ ↦ (a, L.one + t • x)) hL1 hc1).prodMk continuousAt_const
  have hm2 : ContinuousAt (fun t : ℝ ↦ (a, L.mul (L.one + t • x, b))) 0 :=
    continuousAt_const.prodMk (ContinuousAt.comp (f := fun t : ℝ ↦ (L.one + t • x, b)) hL2 hc2)
  have e3 : (fun t : ℝ ↦ (L.mul (a, L.one + t • x), b)) 0 ∈ L.dom := by
    simpa [L.mul_one a ha] using hab
  have e4 : (fun t : ℝ ↦ (a, L.mul (L.one + t • x, b))) 0 ∈ L.dom := by
    simpa [L.one_mul b hb] using hab
  have hev : (fun t : ℝ ↦ L.mul (a, L.mul (L.one + t • x, b))) =ᶠ[𝓝 0]
      fun t : ℝ ↦ L.mul (L.mul (a, L.one + t • x), b) := by
    filter_upwards [hc1.preimage_mem_nhds (L.isOpen_dom.mem_nhds e1),
      hc2.preimage_mem_nhds (L.isOpen_dom.mem_nhds e2),
      hm1.preimage_mem_nhds (L.isOpen_dom.mem_nhds e3),
      hm2.preimage_mem_nhds (L.isOpen_dom.mem_nhds e4)] with t h1 h2 h3 h4
    exact (L.mul_assoc a _ b h1 h2 h3 h4).symm
  exact tendsto_nhds_unique hf (hg.congr_of_eventuallyEq hev)

end LocalGroupLaw

/-! ### One-parameter groups -/

namespace MBLieGroup

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]

variable (E) in
/-- **A one-parameter group** `γ : ℝ → G` with derivative `x` at `0`, in the chart at the
identity. -/
structure IsOneParam (γ : ℝ → G) (x : E) : Prop where
  map_add : ∀ s t, γ (s + t) = γ s * γ t
  continuous : Continuous γ
  hasDirDerivAt : HasDirDerivAt (fun t ↦ chartAt E (1 : G) (γ t)) 0 1 x

theorem chart_mem_dom {g k : G} (hg : g ∈ (chartAt E (1 : G)).source)
    (hk : k ∈ (chartAt E (1 : G)).source) (hgk : g * k ∈ (chartAt E (1 : G)).source) :
    (chartAt E (1 : G) g, chartAt E (1 : G) k) ∈ (localGroupLaw E G).dom := by
  refine ⟨⟨(chartAt E (1 : G)).map_source hg, (chartAt E (1 : G)).map_source hk⟩, ?_⟩
  change (chartAt E (1 : G)).symm (chartAt E (1 : G) g) *
    (chartAt E (1 : G)).symm (chartAt E (1 : G) k) ∈ (chartAt E (1 : G)).source
  rw [(chartAt E (1 : G)).left_inv hg, (chartAt E (1 : G)).left_inv hk]
  exact hgk

theorem chart_mul_eq {g k : G} (hg : g ∈ (chartAt E (1 : G)).source)
    (hk : k ∈ (chartAt E (1 : G)).source) :
    (localGroupLaw E G).mul (chartAt E (1 : G) g, chartAt E (1 : G) k) =
      chartAt E (1 : G) (g * k) := by
  change chartAt E (1 : G) ((chartAt E (1 : G)).symm (chartAt E (1 : G) g) *
    (chartAt E (1 : G)).symm (chartAt E (1 : G) k)) = _
  rw [(chartAt E (1 : G)).left_inv hg, (chartAt E (1 : G)).left_inv hk]

theorem localGroupLaw_one_eq : (localGroupLaw E G).one = chartAt E (1 : G) 1 := rfl

namespace IsOneParam

variable {γ : ℝ → G} {x : E} (h : IsOneParam E γ x)
include h

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] in
theorem map_zero : γ 0 = 1 := by
  have h1 := h.map_add 0 0
  rw [add_zero] at h1
  exact mul_eq_left.mp h1.symm

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] in
theorem map_neg (s : ℝ) : γ (-s) = (γ s)⁻¹ := by
  have h1 := h.map_add s (-s)
  rw [add_neg_cancel, h.map_zero] at h1
  exact (inv_eq_of_mul_eq_one_right h1.symm).symm

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] in
theorem map_nat_mul (n : ℕ) (s : ℝ) : γ (n * s) = γ s ^ n := by
  induction n with
  | zero => simp [h.map_zero]
  | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, h.map_add, ih, pow_succ]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] in
theorem map_add_comm (s t : ℝ) : γ s * γ t = γ t * γ s := by
  rw [← h.map_add, ← h.map_add, add_comm]

/-- In the chart at the identity, `c(t) = φ(γ(t))` satisfies `c'(s) = x̃_l(c(s))`. -/
theorem hasDirDerivAt_xl {s : ℝ} (hs : γ s ∈ (chartAt E (1 : G)).source) :
    HasDirDerivAt (fun t ↦ chartAt E (1 : G) (γ t)) s 1
      ((localGroupLaw E G).xl x (chartAt E (1 : G) (γ s))) := by
  set φ := chartAt E (1 : G)
  set L := localGroupLaw E G
  have h1 := mem_chart_source E (1 : G)
  have h0 : γ 0 ∈ φ.source := by rw [h.map_zero]; exact h1
  have hmem : φ (γ 0) ∈ L.domL (φ (γ s)) :=
    chart_mem_dom hs h0 (by rw [h.map_zero, mul_one]; exact hs)
  have hd := (L.contDiffMBOn_mul_left 1 (φ (γ s))).hasDirDerivAt_comp (L.isOpen_domL _)
    h.hasDirDerivAt hmem
  have hval : dMB (fun b ↦ L.mul (φ (γ s), b)) (φ (γ 0), x) = L.xl x (φ (γ s)) := by
    rw [h.map_zero, LocalGroupLaw.xl_eq]; rfl
  rw [hval] at hd
  refine hasDirDerivAt_shift (hd.congr_of_eventuallyEq ?_)
  have hU : ∀ᶠ r in 𝓝 (0 : ℝ), γ r ∈ φ.source :=
    (h.continuous.continuousAt (x := 0)).preimage_mem_nhds (φ.open_source.mem_nhds h0)
  filter_upwards [hU] with r hr
  change L.mul (φ (γ s), φ (γ r)) = φ (γ (s + r))
  rw [chart_mul_eq hs hr, h.map_add]

/-- In the chart at the identity, `c(t) = φ(γ(t))` satisfies `c'(s) = x̃_r(c(s))`. -/
theorem hasDirDerivAt_xr {s : ℝ} (hs : γ s ∈ (chartAt E (1 : G)).source) :
    HasDirDerivAt (fun t ↦ chartAt E (1 : G) (γ t)) s 1
      ((localGroupLaw E G).xr x (chartAt E (1 : G) (γ s))) := by
  set φ := chartAt E (1 : G)
  set L := localGroupLaw E G
  have h1 := mem_chart_source E (1 : G)
  have h0 : γ 0 ∈ φ.source := by rw [h.map_zero]; exact h1
  have hmem : φ (γ 0) ∈ {a | (a, φ (γ s)) ∈ L.dom} :=
    chart_mem_dom h0 hs (by rw [h.map_zero, one_mul]; exact hs)
  have hd := (L.contDiffMBOn_mul_right 1 (φ (γ s))).hasDirDerivAt_comp
    (L.isOpen_dom.preimage (by fun_prop)) h.hasDirDerivAt hmem
  have hval : dMB (fun a ↦ L.mul (a, φ (γ s))) (φ (γ 0), x) = L.xr x (φ (γ s)) := by
    rw [h.map_zero, LocalGroupLaw.xr_eq]; rfl
  rw [hval] at hd
  refine hasDirDerivAt_shift (hd.congr_of_eventuallyEq ?_)
  have hU : ∀ᶠ r in 𝓝 (0 : ℝ), γ r ∈ φ.source :=
    (h.continuous.continuousAt (x := 0)).preimage_mem_nhds (φ.open_source.mem_nhds h0)
  filter_upwards [hU] with r hr
  change L.mul (φ (γ r), φ (γ s)) = φ (γ (s + r))
  rw [chart_mul_eq hr hs, h.map_add_comm, h.map_add]

end IsOneParam

/-- **Two one-parameter groups with the same derivative at `0` are equal** ([GN26,
Remark 5.6.4, Lemma 5.5.4]). -/
theorem IsOneParam.eq {γ₁ γ₂ : ℝ → G} {x : E} (h₁ : IsOneParam E γ₁ x)
    (h₂ : IsOneParam E γ₂ x) : γ₁ = γ₂ := by
  set φ := chartAt E (1 : G)
  set L := localGroupLaw E G
  have h1 := mem_chart_source E (1 : G)
  set S : Set ℝ := {s | γ₁ (-s) ∈ φ.source ∧ γ₂ s ∈ φ.source ∧ γ₁ (-s) * γ₂ s ∈ φ.source}
  have := isTopologicalGroup E G
  have hS : IsOpen S := by
    have c1 : Continuous fun s : ℝ ↦ γ₁ (-s) := h₁.continuous.comp continuous_neg
    exact (φ.open_source.preimage c1).inter ((φ.open_source.preimage h₂.continuous).inter
      (φ.open_source.preimage (c1.mul h₂.continuous)))
  have h0S : (0 : ℝ) ∈ S := by
    refine ⟨?_, ?_, ?_⟩
    · rw [neg_zero, h₁.map_zero]; exact h1
    · rw [h₂.map_zero]; exact h1
    · rw [neg_zero, h₁.map_zero, h₂.map_zero, mul_one]; exact h1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hS 0 h0S
  rw [Real.ball_eq_Ioo, zero_sub, zero_add] at hball
  -- the curve `e(s) = φ(γ₁(-s)) ∗ φ(γ₂(s))`
  set e : ℝ → E := fun s ↦ L.mul (φ (γ₁ (-s)), φ (γ₂ s))
  have he : ∀ s ∈ S, HasDirDerivAt e s 1 0 := by
    intro s hs
    have ha := hasDirDerivAt_comp_neg (h₁.hasDirDerivAt_xl hs.1)
    have hb := h₂.hasDirDerivAt_xr hs.2.1
    have hab : (φ (γ₁ (-s)), φ (γ₂ s)) ∈ L.dom := chart_mem_dom hs.1 hs.2.1 hs.2.2
    have ha1 : (φ (γ₁ (-s)), L.one) ∈ L.dom :=
      chart_mem_dom hs.1 h1 (by rw [mul_one]; exact hs.1)
    have h1b : (L.one, φ (γ₂ s)) ∈ L.dom :=
      chart_mem_dom h1 hs.2.1 (by rw [one_mul]; exact hs.2.1)
    have hd := L.hasDirDerivAt_mul_curve ha hb hab
    have hsplit : ((-L.xl x (φ (γ₁ (-s))), L.xr x (φ (γ₂ s))) : E × E) =
        (-1 : ℝ) • (L.xl x (φ (γ₁ (-s))), (0 : E)) + ((0 : E), L.xr x (φ (γ₂ s))) := by
      simp
    rw [hsplit, (L.smooth 1).dMB_add L.isOpen_dom hab, (L.smooth 1).dMB_smul hab,
      L.dMB_xl_eq_xr x hab ha1 h1b, neg_one_smul, neg_add_cancel] at hd
    exact hd
  -- `e` is constant near `0`
  have hconst : ∀ s ∈ Ioo (-ε) ε, γ₂ s = γ₁ s := by
    intro s hs
    have hsS := hball hs
    have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.2 hε, hε⟩
    have heq := eq_of_hasDirDerivAt_zero isOpen_Ioo isPreconnected_Ioo
      (fun r hr ↦ he r (hball hr)) hs h0
    have he0 : e 0 = φ 1 := by
      change L.mul (φ (γ₁ (-0)), φ (γ₂ 0)) = φ 1
      rw [neg_zero, h₁.map_zero, h₂.map_zero, chart_mul_eq h1 h1, mul_one]
    have hes : e s = φ (γ₁ (-s) * γ₂ s) := chart_mul_eq hsS.1 hsS.2.1
    rw [he0, hes] at heq
    have h11 := φ.injOn hsS.2.2 h1 heq
    rw [h₁.map_neg] at h11
    exact (inv_mul_eq_one.mp h11).symm
  -- and everywhere
  funext t
  obtain ⟨n, hn⟩ := exists_nat_gt (|t| / ε)
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg (abs_nonneg t) hε.le) hn
  have hts : t = n * (t / n) := by field_simp
  have hmem : t / n ∈ Ioo (-ε) ε := by
    rw [mem_Ioo, ← abs_lt, abs_div, abs_of_pos hn0, div_lt_iff₀ hn0]
    rwa [div_lt_iff₀ hε, mul_comm] at hn
  rw [hts, h₁.map_nat_mul, h₂.map_nat_mul, hconst _ hmem]

/-! ### Exponential functions -/

omit [MBLieGroup E G] in
theorem IsExp.isOneParam {exp : E → G} (h : IsExp E exp) (x : E) :
    IsOneParam E (fun t : ℝ ↦ exp (t • x)) x where
  map_add s t := h.map_add_smul x s t
  continuous := h.continuous.comp (by fun_prop)
  hasDirDerivAt := by
    have h1 : exp 0 ∈ (chartAt E (1 : G)).source := by
      rw [h.exp_zero]; exact mem_chart_source E 1
    have hd := (h.contDiffMBOn_chart 1).hasDirDerivAt (k := 0) h1 x
    rw [h.dMB_chart x] at hd
    unfold HasDirDerivAt at hd ⊢
    simpa using hd

/-- **A Lie group has at most one exponential function** ([GN26, Proposition 5.6.3]). -/
theorem IsExp.unique {exp₁ exp₂ : E → G} (h₁ : IsExp E exp₁) (h₂ : IsExp E exp₂) :
    exp₁ = exp₂ := by
  funext x
  have h := congrFun ((h₁.isOneParam x).eq (h₂.isOneParam x)) 1
  simpa using h

variable {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {H : Type*} [Group H] [TopologicalSpace H] [ChartedSpace F H] [MBLieGroup F H]

/-- **Exponential functions are natural** ([GN26, Proposition 5.6.12]): for a morphism of Lie
groups `φ`, `φ ∘ exp_G = exp_H ∘ L(φ)`. -/
theorem IsExp.map_hom {expG : E → G} {expH : F → H} (hG : IsExp E expG) (hH : IsExp F expH)
    {φ : G →* H} (hφ : IsHom E F φ) (x : E) : φ (expG x) = expH (hφ.lieHom x) := by
  set χ := chartAt E (1 : G)
  have hφc : Continuous φ := continuousOn_univ.1 (hφ 0).continuousOn
  have h₁ : IsOneParam F (fun t : ℝ ↦ φ (expG (t • x))) (hφ.lieHom x) := by
    refine ⟨fun s t ↦ by simp only [hG.map_add_smul, map_mul],
      hφc.comp (hG.isOneParam x).continuous, ?_⟩
    have hc := (hG.isOneParam x).hasDirDerivAt
    have hmem : (fun t : ℝ ↦ χ (expG (t • x))) 0 ∈ IsHom.localRepDom (E := E) (F := F) φ := by
      simp only [zero_smul, hG.exp_zero]
      exact IsHom.one_mem_localRepDom
    have hd := (hφ.smoothMBOn_localRep 1).hasDirDerivAt_comp hφ.isOpen_localRepDom hc hmem
    simp only [zero_smul, hG.exp_zero] at hd
    refine hd.congr_of_eventuallyEq ?_
    have h0 : (fun t : ℝ ↦ expG (t • x)) 0 ∈ χ.source := by
      simp only [zero_smul, hG.exp_zero]
      exact mem_chart_source E 1
    have hU : ∀ᶠ t in 𝓝 (0 : ℝ), expG (t • x) ∈ χ.source :=
      ((hG.isOneParam x).continuous.continuousAt (x := 0)).preimage_mem_nhds
        (χ.open_source.mem_nhds h0)
    filter_upwards [hU] with t ht
    simp only [Function.comp_apply, IsHom.localRep]
    rw [(chartAt E (1 : G)).left_inv ht]
  have h := congrFun (h₁.eq (hH.isOneParam (hφ.lieHom x))) 1
  simp only [one_smul] at h
  exact h.trans (congrArg expH (one_smul ℝ (hφ.lieHom x : F)))

end MBLieGroup

end LocallyConvex.LieGroups
