/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Exponential.Unique
public import LocallyConvexLieGroups.LieAlgebra.AdjointAction

/-!
# Logarithmic derivatives and their uniqueness

For a curve `γ : ℝ → G` in a Lie group, the (left) logarithmic derivative
`δ(γ)(t) = γ(t)⁻¹ γ̇(t) ∈ 𝔤` ([GN26, §5.5, §6.1]) is read in the chart `φ` at the identity, without
tangent bundles: `δ(γ)(t) = x` means that `s ↦ φ(γ(t)⁻¹ γ(s))` has derivative `x` at `s = t`.

## Main definitions

* `MBLieGroup.HasLogDerivAt γ x t`: `γ` is continuous at `t` and `δ(γ)(t) = x`.

## Main results

* `MBLieGroup.HasLogDerivAt.mul_inv`: if `δ(γ₁)(t) = δ(γ₂)(t)`, then `γ₂ γ₁⁻¹` has vanishing
  logarithmic derivative at `t`.
* `MBLieGroup.eq_of_hasLogDerivAt_zero`: a curve with vanishing logarithmic derivative is constant.
* `MBLieGroup.eq_of_hasLogDerivAt`: **the Uniqueness Lemma** ([GN26, Lemma 5.5.4]): two curves with
  the same logarithmic derivative and the same initial value are equal.

## Implementation notes

`δ(γ₂ γ₁⁻¹) = 0` is shown without the product rule: near `t`,
`(γ₂ γ₁⁻¹)(t)⁻¹ (γ₂ γ₁⁻¹)(s) = g w₂(s) w₁(s)⁻¹ g⁻¹` with `g = γ₁(t)` and `wᵢ(s) = γᵢ(t)⁻¹ γᵢ(s)`, a
smooth function `K(w₂, w₁)` with `K(w, w) = 1`; so its derivative is `dK((1, 1), (x, x)) = 0`, the
derivative of `w ↦ K(w, w)` along the diagonal.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups.MBLieGroup

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]

variable (E) in
/-- **The logarithmic derivative** `δ(γ)(t) = γ(t)⁻¹ γ̇(t)` is `x`, read in the chart `φ` at the
identity: `s ↦ φ(γ(t)⁻¹ γ(s))` has derivative `x` at `t` ([GN26, §5.5]). -/
def HasLogDerivAt (γ : ℝ → G) (x : E) (t : ℝ) : Prop :=
  ContinuousAt γ t ∧ HasDirDerivAt (fun s ↦ chartAt E (1 : G) ((γ t)⁻¹ * γ s)) t 1 x

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] in
/-- `δ(g γ) = δ(γ)`. -/
theorem HasLogDerivAt.mul_left [IsTopologicalGroup G] {γ : ℝ → G} {x : E} {t : ℝ}
    (h : HasLogDerivAt E γ x t) (g : G) : HasLogDerivAt E (fun s ↦ g * γ s) x t := by
  refine ⟨continuousAt_const.mul h.1, ?_⟩
  have heq : (fun s ↦ chartAt E (1 : G) ((g * γ t)⁻¹ * (g * γ s))) =
      fun s ↦ chartAt E (1 : G) ((γ t)⁻¹ * γ s) := by
    funext s; congr 1; group
  rw [heq]
  exact h.2

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] in
/-- `δ(γ(· + c))(t) = δ(γ)(t + c)`. -/
theorem HasLogDerivAt.comp_add_const {γ : ℝ → G} {x : E} {t : ℝ} (c : ℝ)
    (h : HasLogDerivAt E γ x (t + c)) : HasLogDerivAt E (fun s ↦ γ (s + c)) x t := by
  refine ⟨ContinuousAt.comp (g := γ) (f := fun s ↦ s + c) h.1 (by fun_prop), ?_⟩
  have h2 := h.2
  unfold HasDirDerivAt at h2 ⊢
  refine h2.congr fun r ↦ ?_
  simp only [smul_eq_mul, mul_one, add_right_comm]

/-! ### The conjugated quotient `(a, b) ↦ g a b⁻¹ g⁻¹` in the chart -/

/-- `K_g(a, b) = g a b⁻¹ g⁻¹`. -/
def quotMap (g : G) (p : G × G) : G := g * (p.1 * p.2⁻¹) * g⁻¹

omit [TopologicalSpace G] in
theorem quotMap_one (g : G) : quotMap g ((1 : G), (1 : G)) = 1 := by simp [quotMap]

theorem smoothMBM_quotMap (g : G) : SmoothMBM (ModelProd E E) E (quotMap (G := G) g) := by
  have h2 : SmoothMBM (ModelProd E E) E (fun p : G × G ↦ p.2⁻¹) :=
    (smoothMBM_inv (E := E) (G := G)).comp smoothMBM_snd
  have h3 : SmoothMBM (ModelProd E E) E (fun p : G × G ↦ p.1 * p.2⁻¹) :=
    (smoothMBM_mul (E := E) (G := G)).comp fun k ↦ ContMDiffMBOn.prodMk isOpen_univ
      (smoothMBM_fst k) (h2 k)
  have h4 := (smoothMBM_mul_left (E := E) g).comp h3
  exact (smoothMBM_mul_right (E := E) g⁻¹).comp h4

variable (E) in
/-- `K_g` in the charts at the identity. -/
def quotRep (g : G) (q : E × E) : E :=
  chartAt E (1 : G) (quotMap g ((chartAt E (1 : G)).symm q.1, (chartAt E (1 : G)).symm q.2))

variable (E) in
/-- The domain of `quotRep`. -/
def quotRepDom (g : G) : Set (E × E) :=
  chartDomain (quotMap g) univ (chartAt (ModelProd E E) ((1 : G), (1 : G))) (chartAt E (1 : G))

theorem smoothMBOn_quotRep (g : G) : SmoothMBOn (quotRep E g) (quotRepDom E g) := by
  intro k
  have h := (smoothMBM_quotMap (E := E) g k).2 ((1 : G), (1 : G)) (mem_univ _)
  rw [quotMap_one] at h
  exact h

theorem isOpen_quotRepDom (g : G) : IsOpen (quotRepDom E g) :=
  isOpen_chartDomain isOpen_univ (smoothMBM_quotMap (E := E) g 0).continuousOn _ _

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [MBLieGroup E G] in
theorem one_mem_quotRepDom (g : G) :
    (chartAt E (1 : G) 1, chartAt E (1 : G) 1) ∈ quotRepDom E g := by
  have h1 := mem_chart_source E (1 : G)
  refine ⟨⟨(chartAt E (1 : G)).map_source h1, (chartAt E (1 : G)).map_source h1⟩, mem_univ _, ?_⟩
  change quotMap g ((chartAt E (1 : G)).symm (chartAt E (1 : G) 1),
    (chartAt E (1 : G)).symm (chartAt E (1 : G) 1)) ∈ (chartAt E (1 : G)).source
  rw [(chartAt E (1 : G)).left_inv h1, quotMap_one]
  exact h1

/-- **`dK_g((1, 1), (x, x)) = 0`**, since `K_g(w, w) = 1`. -/
theorem dMB_quotRep_diag (g : G) (x : E) :
    dMB (quotRep E g) ((chartAt E (1 : G) 1, chartAt E (1 : G) 1), (x, x)) = 0 := by
  set φ := chartAt E (1 : G)
  set Δ : E →L[ℝ] E × E := (ContinuousLinearMap.id ℝ E).prod (ContinuousLinearMap.id ℝ E)
  have hΔ : HasDirDerivAt (fun p : E ↦ (p, p)) (φ 1) x (x, x) := Δ.hasDirDerivAt _ _
  have hd := ((smoothMBOn_quotRep (E := E) g) 1).hasDirDerivAt_comp (isOpen_quotRepDom g) hΔ
    (one_mem_quotRepDom g)
  -- `K_g(w, w) = φ(1)` near `φ(1)`
  have hV : IsOpen (φ.target ∩ (fun p : E ↦ (p, p)) ⁻¹' quotRepDom E g) :=
    φ.open_target.inter ((isOpen_quotRepDom g).preimage (by fun_prop))
  have h1V : φ 1 ∈ φ.target ∩ (fun p : E ↦ (p, p)) ⁻¹' quotRepDom E g :=
    ⟨φ.map_source (mem_chart_source E (1 : G)), one_mem_quotRepDom g⟩
  have hconst : EqOn (quotRep E g ∘ fun p : E ↦ (p, p)) (fun _ ↦ φ 1)
      (φ.target ∩ (fun p : E ↦ (p, p)) ⁻¹' quotRepDom E g) := by
    intro p _
    change φ (quotMap g (φ.symm p, φ.symm p)) = φ 1
    simp [quotMap]
  rw [← hd.dMB_eq]
  exact dMB_eq_zero_of_eqOn_const hV h1V hconst x

/-! ### Uniqueness -/

/-- **`δ(γ₂ γ₁⁻¹) = 0` where `δ(γ₁) = δ(γ₂)`.** -/
theorem HasLogDerivAt.mul_inv {γ₁ γ₂ : ℝ → G} {x : E} {t : ℝ} (h₁ : HasLogDerivAt E γ₁ x t)
    (h₂ : HasLogDerivAt E γ₂ x t) : HasLogDerivAt E (fun s ↦ γ₂ s * (γ₁ s)⁻¹) 0 t := by
  have := isTopologicalGroup E G
  set φ := chartAt E (1 : G)
  set g := γ₁ t
  have h1 := mem_chart_source E (1 : G)
  refine ⟨h₂.1.mul h₁.1.inv, ?_⟩
  -- `wᵢ(s) = γᵢ(t)⁻¹ γᵢ(s)` stays in the chart domain near `t`
  have hw : ∀ γ : ℝ → G, ContinuousAt γ t → ∀ᶠ s in 𝓝 t, (γ t)⁻¹ * γ s ∈ φ.source := by
    intro γ hγ
    have hc : ContinuousAt (fun s ↦ (γ t)⁻¹ * γ s) t := continuousAt_const.mul hγ
    have h0 : (γ t)⁻¹ * γ t ∈ φ.source := by rw [inv_mul_cancel]; exact h1
    exact hc.preimage_mem_nhds (φ.open_source.mem_nhds h0)
  have hin := h₂.2.prodMk h₁.2
  have hmem : ((fun s ↦ (φ ((γ₂ t)⁻¹ * γ₂ s), φ ((γ₁ t)⁻¹ * γ₁ s))) t) ∈ quotRepDom E g := by
    simp only [inv_mul_cancel]
    exact one_mem_quotRepDom g
  have hd := ((smoothMBOn_quotRep (E := E) g) 1).hasDirDerivAt_comp (isOpen_quotRepDom g) hin hmem
  have hval : dMB (quotRep E g) ((fun s ↦ (φ ((γ₂ t)⁻¹ * γ₂ s), φ ((γ₁ t)⁻¹ * γ₁ s))) t,
      (x, x)) = 0 := by
    simp only [inv_mul_cancel]
    exact dMB_quotRep_diag g x
  rw [hval] at hd
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hw γ₁ h₁.1, hw γ₂ h₂.1] with s hs₁ hs₂
  change φ (quotMap g (φ.symm (φ ((γ₂ t)⁻¹ * γ₂ s)), φ.symm (φ ((γ₁ t)⁻¹ * γ₁ s)))) =
    φ ((γ₂ t * (γ₁ t)⁻¹)⁻¹ * (γ₂ s * (γ₁ s)⁻¹))
  rw [φ.left_inv hs₁, φ.left_inv hs₂]
  congr 1
  simp only [quotMap, g]
  group

/-- **A curve with vanishing logarithmic derivative is constant.** -/
theorem eq_of_hasLogDerivAt_zero {P : ℝ → G} (hP : ∀ t, HasLogDerivAt E P 0 t) (s t : ℝ) :
    P s = P t := by
  set φ := chartAt E (1 : G)
  set L := localGroupLaw E G
  have h1 := mem_chart_source E (1 : G)
  have hc : Continuous P := continuous_iff_continuousAt.2 fun t ↦ (hP t).1
  have := isTopologicalGroup E G
  suffices hloc : IsLocallyConstant P from hloc.apply_eq_of_preconnectedSpace s t
  refine (IsLocallyConstant.iff_eventually_eq P).2 fun s₀ ↦ ?_
  set S : Set ℝ := {s | (P s₀)⁻¹ * P s ∈ φ.source}
  have hS : IsOpen S := φ.open_source.preimage (continuous_const.mul hc)
  have hs₀ : s₀ ∈ S := by
    change (P s₀)⁻¹ * P s₀ ∈ φ.source
    rw [inv_mul_cancel]; exact h1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hS s₀ hs₀
  set e : ℝ → E := fun s ↦ φ ((P s₀)⁻¹ * P s)
  have he : ∀ s₁ ∈ Metric.ball s₀ ε, HasDirDerivAt e s₁ 1 0 := by
    intro s₁ hs₁
    have ha : (P s₀)⁻¹ * P s₁ ∈ φ.source := hball hs₁
    have hmem : φ ((P s₁)⁻¹ * P s₁) ∈ L.domL (φ ((P s₀)⁻¹ * P s₁)) := by
      rw [inv_mul_cancel]
      exact chart_mem_dom ha h1 (by rw [mul_one]; exact ha)
    have hd := (L.contDiffMBOn_mul_left 1 (φ ((P s₀)⁻¹ * P s₁))).hasDirDerivAt_comp
      (L.isOpen_domL _) (hP s₁).2 hmem
    have h0 : dMB (fun b ↦ L.mul (φ ((P s₀)⁻¹ * P s₁), b)) (φ ((P s₁)⁻¹ * P s₁), (0 : E)) = 0 := by
      have := (L.contDiffMBOn_mul_left 1 (φ ((P s₀)⁻¹ * P s₁))).dMB_smul hmem (0 : ℝ) (0 : E)
      simpa using this
    rw [h0] at hd
    refine hd.congr_of_eventuallyEq ?_
    have hw : ∀ᶠ s in 𝓝 s₁, (P s₁)⁻¹ * P s ∈ φ.source := by
      have hc' : ContinuousAt (fun s ↦ (P s₁)⁻¹ * P s) s₁ :=
        continuousAt_const.mul hc.continuousAt
      have h0' : (P s₁)⁻¹ * P s₁ ∈ φ.source := by rw [inv_mul_cancel]; exact h1
      exact hc'.preimage_mem_nhds (φ.open_source.mem_nhds h0')
    filter_upwards [hw] with s hs
    change L.mul (φ ((P s₀)⁻¹ * P s₁), φ ((P s₁)⁻¹ * P s)) = φ ((P s₀)⁻¹ * P s)
    rw [chart_mul_eq ha hs]
    congr 1
    group
  filter_upwards [Metric.ball_mem_nhds s₀ hε] with s hs
  have heq := eq_of_hasDirDerivAt_zero Metric.isOpen_ball (convex_ball s₀ ε).isPreconnected he hs
    (Metric.mem_ball_self hε)
  have hsrc : (P s₀)⁻¹ * P s ∈ φ.source := hball hs
  have hsrc₀ : (P s₀)⁻¹ * P s₀ ∈ φ.source := hball (Metric.mem_ball_self hε)
  have h := φ.injOn hsrc hsrc₀ heq
  rw [inv_mul_cancel] at h
  exact (inv_mul_eq_one.1 h).symm

/-- **The Uniqueness Lemma** ([GN26, Lemma 5.5.4]): two curves with the same logarithmic
derivative that agree at one point are equal. -/
theorem eq_of_hasLogDerivAt {γ₁ γ₂ : ℝ → G} {ξ : ℝ → E} (h₁ : ∀ t, HasLogDerivAt E γ₁ (ξ t) t)
    (h₂ : ∀ t, HasLogDerivAt E γ₂ (ξ t) t) {t₀ : ℝ} (h₀ : γ₁ t₀ = γ₂ t₀) : γ₁ = γ₂ := by
  funext s
  have h := eq_of_hasLogDerivAt_zero (fun t ↦ (h₁ t).mul_inv (h₂ t)) s t₀
  simp only [h₀, mul_inv_cancel] at h
  exact (mul_inv_eq_one.1 h).symm

end LocallyConvex.LieGroups.MBLieGroup
