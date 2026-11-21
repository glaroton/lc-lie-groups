/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Diffeomorphism.Basic
public import LocallyConvexLieGroups.LieAlgebra.Basic
public import LocallyConvexManifolds.LocalAddition.Normalize

/-!
# The Lie algebra of `Diff(K)`

For a compact manifold `K` with a normalized local addition `Σ`, the Lie algebra of the Lie group
`Diff(K)` is the Lie algebra `V(K)` of vector fields on `K` with the **opposite** bracket
([GN26, Example 5.4.3]): the model space of `Diff(K)` is the space `Γ_id` of smooth sections of
`TK` along the identity, that is, vector fields written in fiber coordinates, and its bracket is
`[x, y] = [y, x]_{V(K)}`.

## Main definitions

* `SecSm.evalCLM`: evaluation of smooth sections at a point, as a continuous linear map.
* `Diffeo.law A`: the multiplication of `Diff(K)` in the chart at the identity.
* `Diffeo.toField A u`: the vector field with fiber coordinates `u ∈ Γ_id`.

## Main results

* `Diffeo.law_mul_apply`: in the chart at the identity,
  `(a ∗ b)(p) = θ⁻¹(p, Σ(a(q)))` with `q = Σ(b(p))` (`θ = (π, Σ)`).
* `Diffeo.evalAt_dMB_xl`: `(dỹ_l(0) x)(p) = d²Θ_p(φ_p p)(x(p), y(p)) + dx̃(φ_p p) y(p)`, where
  `Θ_p` inverts `Σ(p, ·)` and `x̃` is the local representative of `x` in the chart `φ_p` at `p`.
* `Diffeo.evalAt_lie`, **`Diffeo.toField_lie`**: `[x, y] = [Y, X]` for the vector fields `X`, `Y`
  with fiber coordinates `x`, `y` ([GN26, Example 5.4.3]).

## Implementation notes

Glöckner and Neeb deduce the formula from the derived action of `Diff(K)` on `K`, using the
exponential map of a Riemannian metric as local addition. Here we compute the bracket
`[x, y] = dỹ_l(0) x − dx̃_l(0) y` of `L(Diff(K))` directly. Evaluation at `p` is continuous linear
on `Γ_id`, so it commutes with the derivatives, and `(dỹ_l(0) x)(p)` is the mixed second
derivative at `0` of `G(s, t) = (s x ∗ t y)(p)` (`LocalGroupLaw.clm_dMB_xl`). In the chart `φ_p`
of `K`, `G(s, t) = Θ_p(Σ̃(Q(t), s x̃(Q(t))))` with `Q(t) = φ_p Σ(p, t y(p))`
(`Diffeo.law_mul_smul_apply`). For a normalized local addition, `Σ̃(z, 0) = z` and
`∂_v Σ̃(z, 0) = id` at every point of the chart, and `dΘ_p(φ_p p) = id`; the chain rule gives
`d²Θ_p(x(p), y(p)) + dx̃ · y(p)`. The first term is symmetric, so it cancels in the bracket.

For a local addition that is not normalized, the identification of `Γ_id` with vector fields
through the chart differs from the one in the statement by the fiber derivative of `Σ` along the
zero section. Every local addition can be normalized (lc-manifolds, `LocalAddition.normalize`,
[GN26, Remark 3.8.16]).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter
open scoped Topology
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

universe u

variable {H : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
  [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  {K : Type u} [TopologicalSpace K] [ChartedSpace H K] [MBManifold H K]

namespace LocallyConvex.Manifolds

/-! ### Evaluation of sections -/

namespace SecSm

variable {f : C(K, K)}

theorem continuous_eval (p : K) : Continuous fun u : SecSm H H f ↦ u p := by
  set a : atlas H K × atlas H K := (⟨chartAt H p, chart_mem_atlas H p⟩,
    ⟨chartAt H (f p), chart_mem_atlas H (f p)⟩)
  have hx := chartAt_mem_chartDomOpens (H := H) (E := H) f p
  have hev : Continuous fun γ : ContDiffMBMap H 0 (chartDomOpens f a.1 a.2) ↦ γ (chartAt H p p) :=
    (continuous_eval_const ((⟨chartAt H p p, hx⟩, Fin.elim0) :
      chartDomOpens f a.1 a.2 × (Fin 0 → H))).comp
      (ContDiffMBMap.continuous_iteratedD 0 (Nat.zero_le 0))
  refine (hev.comp ((SecCk.coordCLM a).continuous.comp (toCkCLM 0).continuous)).congr fun u ↦ ?_
  exact SecCk.coordFun_chartAt (toCkCLM 0 u) p

/-- Evaluation at `p`, as a continuous linear map. -/
def evalCLM (p : K) : SecSm H H f →L[ℝ] H where
  toFun u := u p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_eval p

theorem evalCLM_apply (p : K) (u : SecSm H H f) : evalCLM p u = u p :=
  rfl

end SecSm

end LocallyConvex.Manifolds

namespace LocallyConvex.LieGroups

variable [CompactSpace K] [T2Space K] (A : LocalAddition H K)

namespace LocalAdditionAux

omit [CompactSpace K] [T2Space K] in
theorem chartFunSm_apply (f g : SmoothMap H H K K) (hg : g ∈ A.chartSourceSm f) (x : K) :
    A.chartFunSm f g x = (A.toOpenPartialHomeomorph.symm (f x, g x)).vec := by
  rw [LocalAddition.chartFunSm, dite_eq_left_of_eq_true (eq_true hg)]
  rfl

omit [CompactSpace K] in
theorem chartInvFunSm_apply (f : SmoothMap H H K K) {τ : SecSm H H (SmoothMap.toC f)}
    (hτ : τ ∈ A.chartTargetSm f) (x : K) : A.chartInvFunSm f τ x = A.toFun ⟨f x, τ x⟩ := by
  rw [LocalAddition.chartInvFunSm, dite_eq_left_of_eq_true (eq_true hτ)]
  rfl

omit [CompactSpace K] [T2Space K] in
/-- `Σ(z, 0) = z` in a tangent chart. -/
theorem invLocal_zero (i : atlas H K) {z : H} (hz : z ∈ i.1.target) :
    A.invLocal i i (z, 0) = z := by
  have hq : i.1.symm z ∈ i.1.source := i.1.map_target hz
  have h := tangentChart_symm_coordAt i (v := (⟨i.1.symm z, 0⟩ : TangentBundle H K)) hq
  change (tangentChart i i.1).symm (i.1 (i.1.symm z), coordAt i ⟨i.1.symm z, 0⟩) = _ at h
  erw [coordAt_zero i hq] at h
  rw [i.1.right_inv hz] at h
  simp only [LocalAddition.invLocal]
  rw [h, A.toFun_zero, i.1.right_inv hz]

omit [CompactSpace K] [T2Space K] in
/-- **A normalized local addition in a tangent chart**: `∂_v Σ(z, 0) = id` at every point `z`
of the chart. -/
theorem dMB_invLocal_zero (hA : A.IsNormalized) (i : atlas H K) {z : H} (hz : z ∈ i.1.target)
    (w : H) : dMB (A.invLocal i i) ((z, 0), (0, w)) = w := by
  set y := i.1.symm z
  have hy : y ∈ i.1.source := i.1.map_target hz
  set c := LocalAddition.chartIdx (E := H) y
  have hyc : y ∈ c.1.source := mem_chart_source H y
  have halpha : ∀ v, A.alpha y v = v := fun v ↦ hA y v
  have h := A.coordAt_alpha i hy (tangentCoordChange i c y w)
  rw [halpha, (tangentCoordChange_comp i c i ⟨⟨hy, hyc⟩, hy⟩ w).trans
    (tangentCoordChange_self i hy w), i.1.right_inv hz] at h
  exact h.symm

omit [CompactSpace K] [T2Space K] in
/-- For a normalized local addition, `dΘ_p(φ_p p) = id`, `Θ_p` the inverse of `Σ(p, ·)`. -/
theorem dMB_fibreInv_self (hA : A.IsNormalized) (p : K) (w : H) :
    dMB (A.fibreInv p) (chartAt H p p, w) = w := by
  have h := A.alpha_beta p w
  rwa [show A.alpha p (A.beta p w) = A.beta p w from hA p _] at h

omit [CompactSpace K] [T2Space K] in
/-- For a normalized local addition, `d(v ↦ φ_p Σ(p, v))(0) = id`. -/
theorem dMB_fibreMap_zero (hA : A.IsNormalized) (p : K) (w : H) :
    dMB (A.fibreMap p) (0, w) = w :=
  hA p w

omit [CompactSpace K] [T2Space K] in
theorem zero_mem_invLocalDom (i : atlas H K) {z : H} (hz : z ∈ i.1.target) :
    (z, 0) ∈ A.invLocalDom i i := by
  have hq : i.1.symm z ∈ i.1.source := i.1.map_target hz
  have h := (A.invLocal_spec i i (v := (⟨i.1.symm z, 0⟩ : TangentBundle H K)) hq (A.zero_mem _)
    (by rw [A.toFun_zero]; exact hq)).1
  change (i.1 (i.1.symm z), coordAt i ⟨i.1.symm z, 0⟩) ∈ A.invLocalDom i i at h
  erw [coordAt_zero i hq] at h
  rwa [i.1.right_inv hz] at h

end LocalAdditionAux

namespace Diffeo

/-- Evaluation at `p` on the model space of `Diff(K)`. -/
def evalAt (p : K) : DiffeoModel A →L[ℝ] H := SecSm.evalCLM p

/-- The local group law of `Diff(K)` in the chart at the identity. -/
abbrev law : LocalGroupLaw (DiffeoModel A) := MBLieGroup.localGroupLaw (DiffeoModel A) (Diffeo A)

theorem law_one : (law A).one = 0 := by
  refine SecSm.ext fun p ↦ ?_
  change (A.chartFunSm _ ((1 : diffeos H K)⁻¹ * 1).1) p = 0
  rw [inv_one, one_mul]
  refine (LocalAdditionAux.chartFunSm_apply A (1 : diffeos H K).1 (1 : diffeos H K).1
    (fun x ↦ A.self_mem_target x) p).trans ?_
  change (A.toOpenPartialHomeomorph.symm (p, p)).vec = 0
  rw [A.symm_self]
  rfl

/-- The chart of `Diff(K)` at the identity. -/
abbrev chartOne : OpenPartialHomeomorph (diffeos H K) (DiffeoModel A) :=
  (diffeoAtlas A).chart ((diffeoAtlas A).chartAt 1)

/-- **The multiplication of `Diff(K)` in the chart at the identity**:
`(a ∗ b)(p) = θ⁻¹(p, Σ(a(q)))`, `q = Σ(b(p))`. -/
theorem law_mul_apply {a b : DiffeoModel A} (hab : (a, b) ∈ (law A).dom) :
    (∀ q, (⟨q, evalAt A q a⟩ : TangentBundle H K) ∈ A.source) ∧
    (∀ q, (⟨q, evalAt A q b⟩ : TangentBundle H K) ∈ A.source) ∧
    ∀ p, (p, A.toFun ⟨A.toFun ⟨p, evalAt A p b⟩, evalAt A (A.toFun ⟨p, evalAt A p b⟩) a⟩) ∈
        A.toOpenPartialHomeomorph.target ∧
      evalAt A p ((law A).mul (a, b)) = (A.toOpenPartialHomeomorph.symm
        (p, A.toFun ⟨A.toFun ⟨p, evalAt A p b⟩,
          evalAt A (A.toFun ⟨p, evalAt A p b⟩) a⟩)).vec := by
  have hV := isVaryingLieGroup_diffeos A
  obtain ⟨⟨ha, hb⟩, hs⟩ := hab
  have ha1 : a ∈ (chartOne A).target := hV.transChart_target_subset 1 ha
  have hb1 : b ∈ (chartOne A).target := hV.transChart_target_subset 1 hb
  have ha2 : a ∈ A.chartTargetSm (1 : diffeos H K).1 :=
    VaryingAtlas.restrict_chart_target_subset _ _ _ ha1
  have hb2 : b ∈ A.chartTargetSm (1 : diffeos H K).1 :=
    VaryingAtlas.restrict_chart_target_subset _ _ _ hb1
  set γa := (chartOne A).symm a
  set γb := (chartOne A).symm b
  have hγa : ∀ q, γa.1 q = A.toFun ⟨q, evalAt A q a⟩ := fun q ↦ by
    rw [show (γa : SmoothMap H H K K) = A.chartInvFunSm _ a from
      VaryingAtlas.restrict_chart_symm_apply _ _ _ ha1]
    exact LocalAdditionAux.chartInvFunSm_apply A _ ha2 q
  have hγb : ∀ q, γb.1 q = A.toFun ⟨q, evalAt A q b⟩ := fun q ↦ by
    rw [show (γb : SmoothMap H H K K) = A.chartInvFunSm _ b from
      VaryingAtlas.restrict_chart_symm_apply _ _ _ hb1]
    exact LocalAdditionAux.chartInvFunSm_apply A _ hb2 q
  have hsym : ∀ c, (chartAt (DiffeoModel A) (1 : Diffeo A)).symm c = (chartOne A).symm c :=
    fun c ↦ (hV.transChart_symm_apply 1 c).trans (one_mul _)
  have hs' : γa * γb ∈ (chartOne A).source := by
    have h := (hV.mem_transChart_source).1 hs
    have h' : (1 : diffeos H K)⁻¹ * ((1 * γa) * (1 * γb)) ∈ (chartOne A).source := h
    simpa only [inv_one, one_mul] using h'
  have hsrc : (γa * γb).1 ∈ A.chartSourceSm (1 : diffeos H K).1 := by
    have h := hs'
    rw [chartOne, VaryingAtlas.restrict_chart_source] at h
    exact h
  have hval : ∀ q, (γa * γb).1 q = A.toFun ⟨A.toFun ⟨q, evalAt A q b⟩,
      evalAt A (A.toFun ⟨q, evalAt A q b⟩) a⟩ := fun q ↦ by
    change γa.1 (γb.1 q) = _
    rw [hγb, hγa]
  have hm : (law A).mul (a, b) = chartOne A (γa * γb) := by
    change chartOne A ((1 : diffeos H K)⁻¹ * ((1 * γa) * (1 * γb))) = _
    simp only [inv_one, one_mul]
  refine ⟨fun q ↦ ha2 q, fun q ↦ hb2 q, fun p ↦ ⟨?_, ?_⟩⟩
  · rw [← hval]
    exact hsrc p
  · rw [hm, ← hval]
    exact LocalAdditionAux.chartFunSm_apply A _ _ hsrc p

/-! ### The multiplication near the identity, in charts of `K` -/

/-- The identity of `K`, as a continuous map. -/
abbrev fid : C(K, K) := SmoothMap.toC (1 : diffeos H K).1

/-- The preferred chart at `p`, as an element of the atlas. -/
abbrev cIdx (p : K) : atlas H K := LocalAddition.chartIdx (E := H) p

/-- The local representative of `u ∈ Γ_id` in the preferred chart at `p`. -/
def locRep (p : K) (u : DiffeoModel A) : H → H :=
  localCoord (H := H) (E := H) (fid (H := H)) (cIdx (H := H) p) (cIdx (H := H) p)
    (fun q ↦ evalAt A q u)

/-- The curve `t ↦ φ_p(Σ(t y(p)))`. -/
def curveQ (p : K) (y : DiffeoModel A) (t : ℝ) : H := A.fibreMap p (t • evalAt A p y)

theorem contDiffMBOn_locRep (p : K) (u : DiffeoModel A) (k : ℕ) :
    ContDiffMBOn k (locRep A p u)
      (chartDomOpens (H := H) (E := H) (fid (H := H)) (cIdx (H := H) p) (cIdx (H := H) p)) :=
  SecCk.contDiffMBOn_localCoord (SecSm.toCkCLM k u) (cIdx (H := H) p) (cIdx (H := H) p)

theorem locRep_apply (p : K) (u : DiffeoModel A) {q : K} (hq : q ∈ (chartAt H p).source) :
    locRep A p u (chartAt H p q) = coordAt (cIdx (H := H) p) ⟨q, evalAt A q u⟩ := by
  simp only [locRep]
  change coordAt _ ⟨(chartAt H p).symm (chartAt H p q), _⟩ = _
  rw [(chartAt H p).left_inv hq]

theorem locRep_self (p : K) (u : DiffeoModel A) : locRep A p u (chartAt H p p) = evalAt A p u := by
  rw [locRep_apply A p u (mem_chart_source H p)]
  exact coordAt_chartAt p _

/-- **The multiplication near the identity, in charts of `K`**:
`(s x ∗ t y)(p) = Θ_p(Σ̃(Q(t), s x̃(Q(t))))`, `Q(t) = φ_p Σ(p, t y(p))`. -/
theorem law_mul_smul_apply (p : K) (x y : DiffeoModel A) {s t : ℝ}
    (hdom : (s • x, t • y) ∈ (law A).dom) (hQ : t • evalAt A p y ∈ A.fibreMapDom p)
    (hI : (curveQ A p y t, s • locRep A p x (curveQ A p y t)) ∈
      A.invLocalDom (cIdx (H := H) p) (cIdx (H := H) p)) :
    evalAt A p ((law A).mul (s • x, t • y)) =
      A.fibreInv p (A.invLocal (cIdx (H := H) p) (cIdx (H := H) p)
        (curveQ A p y t, s • locRep A p x (curveQ A p y t))) := by
  obtain ⟨hxA, -, hm⟩ := law_mul_apply A hdom
  obtain ⟨hθ, hval⟩ := hm p
  rw [map_smul] at hθ hval
  set i := cIdx (H := H) p
  set q : K := A.toFun ⟨p, t • evalAt A p y⟩
  have hq : q ∈ i.1.source := (A.mem_fibreMapDom hQ).2
  have hQq : curveQ A p y t = i.1 q := rfl
  have hv : coordAt i ⟨q, evalAt A q (s • x)⟩ = s • locRep A p x (curveQ A p y t) := by
    rw [hQq, locRep_apply A p x hq, map_smul]
    exact coordAt_smul i hq s _
  set v : TangentBundle H K := ⟨q, evalAt A q (s • x)⟩
  have hvA : v ∈ A.source := hxA q
  have hsymm : (tangentChart i i.1).symm (i.1 q, coordAt i v) = v :=
    tangentChart_symm_coordAt i (v := v) hq
  have hS : A.toFun v ∈ i.1.source := by
    have h := hI.2
    rw [← hv, hQq] at h
    change A.toFun ((tangentChart i i.1).symm (i.1 q, coordAt i v)) ∈ i.1.source at h
    rwa [hsymm] at h
  have hinv := (A.invLocal_spec i i (v := v) hq hvA hS).2
  change A.invLocal i i (i.1 q, coordAt i v) = i.1 (A.toFun v) at hinv
  rw [← hv, hQq, hinv]
  have hθ' : (p, (chartAt H p).symm (i.1 (A.toFun v))) ∈ A.toOpenPartialHomeomorph.target := by
    rw [(chartAt H p).left_inv hS]
    exact hθ
  rw [(A.fibreInv_spec (i.1.map_source hS) hθ').2, (chartAt H p).left_inv hS]
  exact hval

/-- **The derivatives of the left invariant fields of `Diff(K)`, evaluated at `p`**: for a
normalized local addition,
`(dỹ_l(0) x)(p) = d²Θ_p(φ_p p)(x(p), y(p)) + dx̃(φ_p p) y(p)`, where `Θ_p` is the inverse of
`Σ(p, ·)` and `x̃` is the local representative of `x` in the preferred chart `φ_p` at `p`. -/
theorem evalAt_dMB_xl (hA : A.IsNormalized) (p : K) (x y : DiffeoModel A) :
    evalAt A p (dMB ((law A).xl y) ((law A).one, x)) =
      dMB (dMB (A.fibreInv p)) ((chartAt H p p, evalAt A p x), (evalAt A p y, 0)) +
        dMB (locRep A p x) (chartAt H p p, evalAt A p y) := by
  rw [(law A).clm_dMB_xl (evalAt A p) x y, law_one]
  simp only [zero_add]
  set i := cIdx (H := H) p
  set Θ := A.fibreInv p
  set At := A.invLocal i i
  set X := locRep A p x
  set Q := curveQ A p y
  set y₀ := evalAt A p y
  set z₀ := chartAt H p p
  set D : Set H := (chartDomOpens (H := H) (E := H) (fid (H := H)) i i : Set H)
  have hD : IsOpen D := (chartDomOpens (H := H) (E := H) (fid (H := H)) i i).isOpen
  have hΘ := A.smoothMBOn_fibreInv p
  have hΘD := A.isOpen_fibreInvDom p
  have hX := contDiffMBOn_locRep A p x
  -- the curve `Q`
  set T : Set ℝ := (fun t : ℝ ↦ t • y₀) ⁻¹' A.fibreMapDom p
  have hT : IsOpen T := (A.isOpen_fibreMapDom p).preimage (by fun_prop)
  have hQ : ∀ k, ContDiffMBOn k Q T := fun k ↦
    ContDiffMBOn.comp (g := A.fibreMap p) (f := fun t : ℝ ↦ t • y₀) hT (A.isOpen_fibreMapDom p)
      (A.smoothMBOn_fibreMap p k)
      (((ContinuousLinearMap.id ℝ ℝ).smulRight y₀).contDiffMBOn k T) fun _ ht ↦ ht
  have hQ0 : Q 0 = z₀ := by
    change A.fibreMap p ((0 : ℝ) • y₀) = z₀
    rw [zero_smul]
    exact congrArg (chartAt H p) (A.toFun_zero p)
  have h0T : (0 : ℝ) ∈ T := by
    change (0 : ℝ) • y₀ ∈ A.fibreMapDom p
    rw [zero_smul]
    exact A.zero_mem_fibreMapDom p
  have hz₀D : z₀ ∈ D := chartAt_mem_chartDomOpens (H := H) (E := H) (fid (H := H)) p
  set V : Set H := D ∩ A.fibreInvDom p
  have hV : IsOpen V := hD.inter hΘD
  have hz₀V : z₀ ∈ V := ⟨hz₀D, (A.fibreInv_self p).1⟩
  set T' : Set ℝ := T ∩ Q ⁻¹' V
  have hT' : IsOpen T' := (hQ 0).continuousOn.isOpen_inter_preimage hT hV
  have h0T' : (0 : ℝ) ∈ T' := ⟨h0T, by rw [mem_preimage, hQ0]; exact hz₀V⟩
  -- the neighborhood `W` of `(0, 0)` where the chart formula holds
  set W₁ : Set (ℝ × ℝ) := (fun q : ℝ × ℝ ↦ (q.1 • x, q.2 • y)) ⁻¹' (law A).dom
  have hW₁ : IsOpen W₁ := (law A).isOpen_dom.preimage (by fun_prop)
  set W₂ : Set (ℝ × ℝ) := Prod.snd ⁻¹' T'
  have hW₂ : IsOpen W₂ := hT'.preimage continuous_snd
  have hc : ContinuousOn (fun q : ℝ × ℝ ↦ (Q q.2, q.1 • X (Q q.2))) W₂ := by
    have hQs : ContinuousOn (fun q : ℝ × ℝ ↦ Q q.2) W₂ :=
      (hQ 0).continuousOn.comp continuousOn_snd fun _ hq ↦ hq.1
    have hXQ : ContinuousOn (fun q : ℝ × ℝ ↦ X (Q q.2)) W₂ :=
      (hX 0).continuousOn.comp hQs fun _ hq ↦ hq.2.1
    exact hQs.prodMk (continuousOn_fst.smul hXQ)
  set W₃ : Set (ℝ × ℝ) := W₂ ∩ (fun q : ℝ × ℝ ↦ (Q q.2, q.1 • X (Q q.2))) ⁻¹' A.invLocalDom i i
  have hW₃ : IsOpen W₃ := hc.isOpen_inter_preimage hW₂ (A.isOpen_invLocalDom i i)
  set W := W₁ ∩ W₃
  have hW : IsOpen W := hW₁.inter hW₃
  have hQtarget : ∀ t ∈ T', Q t ∈ i.1.target := fun t ht ↦ (mem_chartDomOpens.1 ht.2.1).1
  have hW0 : ∀ t ∈ T', ((0 : ℝ), t) ∈ W₃ := fun t ht ↦ ⟨ht, by
    change (Q t, (0 : ℝ) • X (Q t)) ∈ A.invLocalDom i i
    rw [zero_smul]
    exact LocalAdditionAux.zero_mem_invLocalDom A i (hQtarget t ht)⟩
  -- the derivative in `s`
  have hE1 : ∀ t ∈ T', ((0 : ℝ), t) ∈ W₁ →
      dMB (fun s : ℝ ↦ evalAt A p ((law A).mul (s • x, t • y))) (0, 1) = dMB Θ (Q t, X (Q t)) := by
    intro t ht ht1
    have h0W : ((0 : ℝ), t) ∈ W := ⟨ht1, hW0 t ht⟩
    set w := X (Q t)
    set c : H × H := (Q t, 0)
    set L : ℝ →L[ℝ] H × H :=
      (ContinuousLinearMap.inr ℝ H H).comp ((ContinuousLinearMap.id ℝ ℝ).smulRight w)
    have hL : ∀ s : ℝ, L s + c = (Q t, s • w) := fun s ↦ by simp [L, c]
    set g₀ : ℝ → H := fun s ↦ At (L s + c)
    set U₁ : Set ℝ := (fun s ↦ L s + c) ⁻¹' A.invLocalDom i i
    have hU₁ : IsOpen U₁ := (A.isOpen_invLocalDom i i).preimage (by fun_prop)
    have hg₀ : ContDiffMBOn 1 g₀ U₁ :=
      ContDiffMBOn.comp (g := At) (f := fun s ↦ L s + c) hU₁ (A.isOpen_invLocalDom i i)
        (A.smoothMBOn_invLocal i i 1) ((L.contDiffMBOn 1 U₁).add hU₁ (contDiffMBOn_const 1 c U₁))
        fun _ h ↦ h
    have hzt := hQtarget t ht
    have hg₀0 : g₀ 0 = Q t := by
      simp only [g₀, map_zero, zero_add, c]
      exact LocalAdditionAux.invLocal_zero A i hzt
    have h0U₁ : (0 : ℝ) ∈ U₁ := by
      change L 0 + c ∈ A.invLocalDom i i
      rw [map_zero, zero_add]
      exact LocalAdditionAux.zero_mem_invLocalDom A i hzt
    set U₀ := U₁ ∩ g₀ ⁻¹' A.fibreInvDom p
    have h0U₀ : (0 : ℝ) ∈ U₀ := ⟨h0U₁, by rw [mem_preimage, hg₀0]; exact ht.2.2⟩
    have hev : (fun s : ℝ ↦ evalAt A p ((law A).mul (s • x, t • y))) =ᶠ[𝓝 0] Θ ∘ g₀ := by
      have hmem : {s : ℝ | (s, t) ∈ W} ∈ 𝓝 (0 : ℝ) :=
        (hW.preimage (by fun_prop : Continuous fun s : ℝ ↦ (s, t))).mem_nhds h0W
      filter_upwards [hmem] with s hs
      rw [law_mul_smul_apply A p x y hs.1 hs.2.1.1 hs.2.2]
      simp only [Function.comp_apply, g₀, hL]
      rfl
    rw [dMB_eq_comp_of_eventuallyEq hΘD (hΘ 1) (hg₀.mono inter_subset_left) (fun _ h ↦ h.2) h0U₀
      hev 1, hg₀0]
    have h := dMB_comp_affine At L.toLinearMap c (0 : ℝ) 1
    simp only [ContinuousLinearMap.coe_coe, map_zero, zero_add] at h
    change dMB Θ (Q t, dMB g₀ (0, 1)) = _
    rw [show dMB g₀ (0, 1) = dMB At (c, L 1) from h,
      show L 1 = (0, w) by simp [L], LocalAdditionAux.dMB_invLocal_zero A hA i hzt]
  -- the derivative in `t`
  have h00 : ((0 : ℝ), (0 : ℝ)) ∈ W₁ := by
    change ((0 : ℝ) • x, (0 : ℝ) • y) ∈ (law A).dom
    rw [zero_smul, zero_smul, ← law_one]
    exact (law A).one_one_mem
  have hev2 : (fun t : ℝ ↦ dMB (fun s : ℝ ↦ evalAt A p ((law A).mul (s • x, t • y))) (0, 1)) =ᶠ[𝓝 0]
      (fun z ↦ dMB Θ (z, X z)) ∘ Q := by
    have hmem : {t : ℝ | ((0 : ℝ), t) ∈ W₁} ∈ 𝓝 (0 : ℝ) :=
      (hW₁.preimage (by fun_prop : Continuous fun t : ℝ ↦ ((0 : ℝ), t))).mem_nhds h00
    filter_upwards [hT'.mem_nhds h0T', hmem] with t ht ht1
    exact hE1 t ht ht1
  have hg₁ : ContDiffMBOn 1 (fun z ↦ dMB Θ (z, X z)) V :=
    ContDiffMBOn.comp (g := dMB Θ) (f := fun z ↦ (z, X z)) hV (hΘD.prod isOpen_univ) (hΘ 2).2.2
      ((smoothMBOn_id V 1).prodMk hV ((hX 1).mono inter_subset_left)) fun _ hz ↦
        ⟨hz.2, mem_univ _⟩
  rw [dMB_eq_comp_of_eventuallyEq hV hg₁ ((hQ 1).mono inter_subset_left) (fun _ ht ↦ ht.2) h0T'
    hev2 1, hQ0]
  have hdQ : dMB Q (0, 1) = y₀ := by
    have h := dMB_comp_linearMap (A.fibreMap p) (LinearMap.toSpanSingleton ℝ H y₀) 0 1
    simp only [map_zero, LinearMap.toSpanSingleton_apply, one_smul] at h
    rw [← LocalAdditionAux.dMB_fibreMap_zero A hA p y₀, ← h]
    rfl
  rw [hdQ, dMB_dMB_comp_apply hΘD hV inter_subset_right (hΘ 2) ((hX 1).mono inter_subset_left)
    hz₀V y₀, locRep_self, LocalAdditionAux.dMB_fibreInv_self A hA]

theorem evalAt_bracket (hA : A.IsNormalized) (x y : DiffeoModel A) (p : K) :
    evalAt A p ((law A).bracket x y) =
      localBracket (locRep A p y) (locRep A p x) (chartAt H p p) := by
  rw [LocalGroupLaw.bracket_eq, map_sub, evalAt_dMB_xl A hA p x y,
    evalAt_dMB_xl A hA p y x, (A.smoothMBOn_fibreInv p 2).dMB_dMB_symm (A.isOpen_fibreInvDom p)
      (A.fibreInv_self p).1 (evalAt A p x) (evalAt A p y), localBracket, locRep_self, locRep_self]
  abel

/-- **The bracket of `L(Diff(K))` in charts of `K`** ([GN26, Example 5.4.3]): for a normalized
local addition, `[x, y](p) = [ỹ, x̃](φ_p p)`, the local bracket of the local representatives in
the preferred chart at `p`, with the arguments swapped. -/
theorem evalAt_lie (hA : A.IsNormalized) (x y : MBLieGroup.LieAlg (DiffeoModel A) (Diffeo A))
    (p : K) :
    evalAt A p (⁅x, y⁆ : MBLieGroup.LieAlg (DiffeoModel A) (Diffeo A)) =
      localBracket (locRep A p y) (locRep A p x) (chartAt H p p) :=
  evalAt_bracket A hA x y p

/-- The vector field on `K` with fiber coordinates `u ∈ Γ_id`. -/
def toField (u : DiffeoModel A) (q : K) : TangentBundle H K := ⟨q, evalAt A q u⟩

/-- **The Lie algebra of `Diff(K)` is the Lie algebra of vector fields with the opposite
bracket** ([GN26, Example 5.4.3]): for a normalized local addition `A` (every local addition can
be normalized, lc-manifolds `LocalAddition.normalize`), the identification of the model space of
`Diff(K)` with vector fields turns the bracket of `L(Diff(K))` into the opposite of the Lie
bracket of vector fields: `[x, y] = [Y, X]`. -/
theorem toField_lie (hA : A.IsNormalized) (x y : MBLieGroup.LieAlg (DiffeoModel A) (Diffeo A)) :
    toField A (⁅x, y⁆ : MBLieGroup.LieAlg (DiffeoModel A) (Diffeo A)) =
      lieBracket (toField A y) (toField A x) := by
  funext p
  change (⟨p, evalAt A p (⁅x, y⁆ : MBLieGroup.LieAlg (DiffeoModel A) (Diffeo A))⟩ :
    TangentBundle H K) = _
  rw [evalAt_lie A hA x y p]
  rfl

end Diffeo

end LocallyConvex.LieGroups
