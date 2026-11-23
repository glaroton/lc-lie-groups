/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.LieAlgebra.Basic
public import LocallyConvexAnalysis.Calculus.Rules

/-!
# Taylor expansions of a local group law

Let `x ∗ y = m(x, y)` be a local group law with identity `1` (in [GN26, Remark 5.1.8], the
multiplication of a Lie group in a chart `φ` with `φ(e) = 0`, so that `1 = 0`). Writing the
Taylor expansion of `m` at `(1, 1)` as `m(1 + x, 1 + y) = 1 + b₁(x, y) + b₂(x, y) + ⋯` with
`b_k = (1/k!) δ^k m`, [GN26, Remark 5.1.8] shows:

* (a) `b₁(x, y) = x + y`, `b₂` is bilinear, `b₂(x, y) = ∂_s ∂_t (s x ∗ t y)`, and the Lie bracket
  is the skew-symmetric part of `b₂`: `[x, y] = b₂(x, y) − b₂(y, x)`;
* (b) for the inversion `η(x) = x⁻¹ = s₁(x) + s₂(x) + ⋯`: `s₁(x) = −x` and `s₂(x) = b₂(x, x)`
  ([GN26, (5.6)]);
* (c) the conjugation `(x ∗ y) ∗ x⁻¹` and the commutator `x ∗ y ∗ x⁻¹ ∗ y⁻¹` have second order
  terms `y + [x, y]` and `[x, y]` ([GN26, (5.7), (5.8)]).

We state these in terms of first and second derivatives at the identity, with `δ²f(v) = d²f(v, v)`:
the second order term of `f` at `p` is `(1/2) d²f(p)(v, v)`.

## Main definitions

* `LocalGroupLaw.b2`: the second order term `b₂(x, y) = dỹ_l(1) x` of the multiplication.
* `LocalGroupLaw.LocalInverse`: a `C²` inversion `ι` of a local group law near the identity,
  `x ∗ ι(x) = 1`.
* `LocalGroupLaw.conj`, `LocalGroupLaw.commutator`: `(x ∗ y) ∗ ι(x)` and
  `((x ∗ y) ∗ ι(x)) ∗ ι(y)`.

## Main results

* `LocalGroupLaw.dMB_mul_one`: `dm(1, 1)(x, y) = x + y`, i.e. `b₁(x, y) = x + y`.
* `LocalGroupLaw.dMB_dMB_mul_one`: `d²m(1, 1)((x, y), (x, y)) = 2 b₂(x, y)`.
* `LocalGroupLaw.b2_eq_mixed`: `b₂(x, y) = ∂_t ∂_s ((1 + s x) ∗ (1 + t y))`.
* `LocalGroupLaw.bracket_eq_b2_sub_b2`: `[x, y] = b₂(x, y) − b₂(y, x)`.
* `LocalGroupLaw.LocalInverse.dMB_inv_one`, `LocalGroupLaw.LocalInverse.dMB_dMB_inv_one`:
  `dι(1) x = −x` and `d²ι(1)(x, x) = 2 b₂(x, x)` ([GN26, (5.6)]).
* `LocalGroupLaw.LocalInverse.dMB_conj_one`, `LocalGroupLaw.LocalInverse.dMB_dMB_conj_one`:
  the conjugation has first derivative `(x, y) ↦ y` and second derivative
  `d²(1, 1)((x, y), (x, y)) = 2 [x, y]` ([GN26, (5.7)]).
* `LocalGroupLaw.LocalInverse.dMB_commutator_one`,
  `LocalGroupLaw.LocalInverse.dMB_dMB_commutator_one`: the commutator has vanishing first
  derivative and second derivative `2 [x, y]` ([GN26, (5.8)]).

## Implementation notes

Everything follows from the second-order chain rule of lc-analysis (`dMB_dMB_comp`) applied to
`m ∘ τ` for maps `τ` with `τ(p) = (1, 1)`: by `dm(1, 1)(u, w) = u + w` and
`d²m(1, 1)(v, v) = 2 b₂(v₁, v₂)`,
`d²(m ∘ τ)(p)(v, v) = 2 b₂(dτ₁ v, dτ₂ v) + d²τ₁(v, v) + d²τ₂(v, v)`
(`LocalGroupLaw.dMB_dMB_mul_comp`). For `d²m(1, 1)(v, v)` itself, the pure second derivatives in
the two factors vanish because `m(·, 1)` and `m(1, ·)` are the identity near `1`
([GN26, Lemma 5.1.7]).

The inversion is not part of `LocalGroupLaw`; a `LocalInverse` is an extra datum. Note that
`dι(1) x = −x` does not need a hypothesis `ι(1) = 1`, which follows from `1 ∗ ι(1) = 1`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter
open scoped Topology
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups

universe u

section Aux

variable {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X]
  {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {G : Type u} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]

omit [LocallyConvexSpace ℝ X] [T2Space X] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] in
/-- The differential of a map that is constant near the point vanishes. -/
theorem dMB_eq_zero_of_eqOn_const {g : X → F} {U : Set X} (hU : IsOpen U) {y : X} (hy : y ∈ U)
    {c : F} (hg : EqOn g (fun _ ↦ c) U) (u : X) : dMB g (y, u) = 0 := by
  have h0 : HasDirDerivAt (fun _ : X ↦ c) y u 0 := by
    simp only [HasDirDerivAt, sub_self, smul_zero]; exact tendsto_const_nhds
  exact (h0.congr_of_eventuallyEq
    (eventuallyEq_of_mem (hU.mem_nhds hy) fun _ hz ↦ (hg hz).symm)).dMB_eq

omit [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- Continuous linear maps have vanishing second derivative. -/
theorem dMB_dMB_clm (A : X →L[ℝ] F) (p v w : X) : dMB (dMB ⇑A) ((p, v), (w, 0)) = 0 := by
  have h : dMB ⇑A = fun q : X × X ↦ A q.2 := funext fun q ↦ (A.hasDirDerivAt q.1 q.2).dMB_eq
  rw [h]
  have h' := (A.comp (ContinuousLinearMap.snd ℝ X X)).hasDirDerivAt (p, v) (w, 0)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd', map_zero] at h'
  exact h'.dMB_eq

omit [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] in
/-- First derivatives of pairs. -/
theorem dMB_prodMk {f : X → F} {g : X → G} {U : Set X} (hf : ContDiffMBOn 1 f U)
    (hg : ContDiffMBOn 1 g U) {p : X} (hp : p ∈ U) (v : X) :
    dMB (fun z ↦ (f z, g z)) (p, v) = (dMB f (p, v), dMB g (p, v)) :=
  ((hf.hasDirDerivAt hp v).prodMk (hg.hasDirDerivAt hp v)).dMB_eq

omit [LocallyConvexSpace ℝ X] [T2Space X] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] [IsTopologicalAddGroup G] [ContinuousSMul ℝ G]
  [LocallyConvexSpace ℝ G] in
/-- Second derivatives of pairs. -/
theorem dMB_dMB_prodMk {f : X → F} {g : X → G} {U : Set X} (hU : IsOpen U)
    (hf : ContDiffMBOn 2 f U) (hg : ContDiffMBOn 2 g U) {p : X} (hp : p ∈ U) (v w : X) :
    dMB (dMB (fun z ↦ (f z, g z))) ((p, v), (w, 0)) =
      (dMB (dMB f) ((p, v), (w, 0)), dMB (dMB g) ((p, v), (w, 0))) := by
  have hf1 : ContDiffMBOn 1 f U := hf.of_le (by norm_num)
  have hg1 : ContDiffMBOn 1 g U := hg.of_le (by norm_num)
  have hpv : (p, v) ∈ U ×ˢ (univ : Set X) := ⟨hp, mem_univ _⟩
  have hev : dMB (fun z ↦ (f z, g z)) =ᶠ[𝓝 (p, v)] fun q ↦ (dMB f q, dMB g q) :=
    eventuallyEq_of_mem ((hU.prod isOpen_univ).mem_nhds hpv) fun q hq ↦
      dMB_prodMk hf1 hg1 hq.1 q.2
  rw [dMB_congr_of_eventuallyEq hev]
  exact ((hf.2.2.hasDirDerivAt hpv _).prodMk (hg.2.2.hasDirDerivAt hpv _)).dMB_eq

omit [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G] in
/-- Derivatives of `g ∘ A` for a continuous linear map `A`. -/
theorem dMB_comp_clm (g : F → G) (A : X →L[ℝ] F) (p v : X) :
    dMB (g ∘ ⇑A) (p, v) = dMB g (A p, A v) :=
  dMB_comp_linearMap g A.toLinearMap p v

omit [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G] in
/-- Second derivatives of `g ∘ A` for a continuous linear map `A`. -/
theorem dMB_dMB_comp_clm (g : F → G) (A : X →L[ℝ] F) (p v w : X) :
    dMB (dMB (g ∘ ⇑A)) ((p, v), (w, 0)) = dMB (dMB g) ((A p, A v), (A w, 0)) := by
  have h : dMB (g ∘ ⇑A) = dMB g ∘ ⇑(A.prodMap A) :=
    funext fun q ↦ dMB_comp_clm g A q.1 q.2
  rw [h, dMB_comp_clm]
  simp

end Aux

namespace LocalGroupLaw

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] (L : LocalGroupLaw E)

/-! ### The second order term of the multiplication -/

/-- **The second order term** of the multiplication at `(1, 1)`, `b₂(x, y) = dỹ_l(1) x`
([GN26, Remark 5.1.8(a)]; see `dMB_dMB_mul_one` and `b2_eq_mixed` for the identification with
the Taylor expansion). -/
def b2 (x y : E) : E := dMB (L.xl y) (L.one, x)

/-- **The Lie bracket is the skew-symmetric part of `b₂`** ([GN26, Remark 5.1.8(a)]). -/
theorem bracket_eq_b2_sub_b2 (x y : E) : L.bracket x y = L.b2 x y - L.b2 y x :=
  L.bracket_eq x y

theorem b2_add_left (x x' y : E) : L.b2 (x + x') y = L.b2 x y + L.b2 x' y :=
  (L.contDiffMBOn_xl 1 y).dMB_add L.isOpen_domR L.one_mem_domR x x'

theorem b2_smul_left (c : ℝ) (x y : E) : L.b2 (c • x) y = c • L.b2 x y :=
  (L.contDiffMBOn_xl 1 y).dMB_smul L.one_mem_domR c x

theorem b2_add_right (x y y' : E) : L.b2 x (y + y') = L.b2 x y + L.b2 x y' :=
  L.dMB_xl_add y y' x

theorem b2_smul_right (c : ℝ) (x y : E) : L.b2 x (c • y) = c • L.b2 x y :=
  L.dMB_xl_smul c y x

theorem b2_neg_left (x y : E) : L.b2 (-x) y = -L.b2 x y := by
  rw [← neg_one_smul ℝ x, b2_smul_left, neg_one_smul]

theorem b2_neg_right (x y : E) : L.b2 x (-y) = -L.b2 x y := by
  rw [← neg_one_smul ℝ y, b2_smul_right, neg_one_smul]

/-- `b₂` as a bilinear map. -/
def b2Bilin : E →ₗ[ℝ] E →ₗ[ℝ] E :=
  LinearMap.mk₂ ℝ L.b2 L.b2_add_left L.b2_smul_left L.b2_add_right L.b2_smul_right

@[simp]
theorem b2Bilin_apply (x y : E) : L.b2Bilin x y = L.b2 x y := rfl

/-- `b₂` as a second derivative of the multiplication. -/
theorem b2_eq_dMB_dMB (x y : E) :
    L.b2 x y = dMB (dMB L.mul) (((L.one, L.one), ((0 : E), y)), ((x, (0 : E)), 0)) :=
  L.dMB_xl y L.one x

/-- **`b₂` is continuous** ([GN26, Remark 5.1.8(a)]). -/
theorem continuous_b2 : Continuous fun p : E × E ↦ L.b2 p.1 p.2 := by
  have hc : ContinuousOn (dMB (dMB L.mul)) ((L.dom ×ˢ univ) ×ˢ univ) := (L.smooth 2).2.2.2.2
  refine (hc.comp_continuous (f := fun p : E × E ↦
    (((L.one, L.one), ((0 : E), p.2)), ((p.1, (0 : E)), (0 : E × E)))) (by fun_prop)
      fun _ ↦ ⟨⟨L.one_one_mem, mem_univ _⟩, mem_univ _⟩).congr fun p ↦ ?_
  exact (L.b2_eq_dMB_dMB p.1 p.2).symm

/-- **`b₂` is a mixed second derivative** ([GN26, Remark 5.1.8(a)]):
`b₂(x, y) = ∂_t ∂_s ((1 + s x) ∗ (1 + t y))` at `s = t = 0`. -/
theorem b2_eq_mixed (x y : E) :
    L.b2 x y = dMB (fun t : ℝ ↦ dMB (fun s : ℝ ↦ L.mul (L.one + s • x, L.one + t • y)) (0, 1))
      (0, 1) :=
  L.clm_dMB_xl (ContinuousLinearMap.id ℝ E) x y

/-! ### First and second derivatives of the multiplication at the identity -/

/-- `m(·, 1)` is the identity near `1`, so `dm(a, 1)(x, 0) = x`. -/
theorem dMB_mul_fst {a : E} (ha : a ∈ L.domR) (x : E) : dMB L.mul ((a, L.one), (x, 0)) = x := by
  rw [dMB_slice]
  have h : (fun z ↦ L.mul (z, L.one)) =ᶠ[𝓝 a] fun z ↦ (ContinuousLinearMap.id ℝ E) z :=
    eventuallyEq_of_mem (L.isOpen_domR.mem_nhds ha) fun z hz ↦ L.mul_one z hz
  rw [dMB_congr_of_eventuallyEq h, ((ContinuousLinearMap.id ℝ E).hasDirDerivAt a x).dMB_eq]
  rfl

/-- `m(1, ·)` is the identity near `1`, so `dm(1, b)(0, y) = y`. -/
theorem dMB_mul_snd {b : E} (hb : b ∈ L.domL L.one) (y : E) :
    dMB L.mul ((L.one, b), (0, y)) = y := by
  rw [dMB_slice₂]
  have h : (fun w ↦ L.mul (L.one, w)) =ᶠ[𝓝 b] fun w ↦ (ContinuousLinearMap.id ℝ E) w :=
    eventuallyEq_of_mem ((L.isOpen_domL L.one).mem_nhds hb) fun w hw ↦ L.one_mul w hw
  rw [dMB_congr_of_eventuallyEq h, ((ContinuousLinearMap.id ℝ E).hasDirDerivAt b y).dMB_eq]
  rfl

/-- **The first order term of the multiplication** ([GN26, Remark 5.1.8(a)]):
`dm(1, 1)(x, y) = x + y`, i.e. `b₁(x, y) = x + y`. -/
theorem dMB_mul_one (v : E × E) : dMB L.mul ((L.one, L.one), v) = v.1 + v.2 := by
  obtain ⟨x, y⟩ := v
  rw [show ((x, y) : E × E) = (x, 0) + (0, y) by simp,
    (L.smooth 1).dMB_add L.isOpen_dom L.one_one_mem, L.dMB_mul_fst L.one_mem_domR,
    L.dMB_mul_snd L.one_one_mem]
  simp

/-- The second derivative of `m` at `(1, 1)` is additive in the direction of differentiation. -/
theorem dMB_dMB_mul_add_right (h k k' : E × E) :
    dMB (dMB L.mul) (((L.one, L.one), h), (k + k', 0)) =
      dMB (dMB L.mul) (((L.one, L.one), h), (k, 0)) +
        dMB (dMB L.mul) (((L.one, L.one), h), (k', 0)) := by
  simp only [dMB_slice]
  exact ((L.smooth.dMB_dir L.isOpen_dom h) 1).dMB_add L.isOpen_dom L.one_one_mem k k'

/-- The second derivative of `m` at `(1, 1)` is additive in the first direction. -/
theorem dMB_dMB_mul_add_left (h h' k : E × E) :
    dMB (dMB L.mul) (((L.one, L.one), h + h'), (k, 0)) =
      dMB (dMB L.mul) (((L.one, L.one), h), (k, 0)) +
        dMB (dMB L.mul) (((L.one, L.one), h'), (k, 0)) := by
  have hs := (L.smooth 2).dMB_dMB_symm L.isOpen_dom L.one_one_mem
  rw [hs, hs h, hs h', dMB_dMB_mul_add_right]

/-- The pure second derivative in the first factor vanishes. -/
theorem dMB_dMB_mul_fst (x x' : E) :
    dMB (dMB L.mul) (((L.one, L.one), (x, 0)), ((x', 0), 0)) = 0 := by
  have h := dMB_comp_affine (fun z : E × E ↦ dMB L.mul (z, (x, 0)))
    (LinearMap.inl ℝ E E) ((0 : E), L.one) L.one x'
  simp only [LinearMap.inl_apply, Prod.mk_add_mk, add_zero, zero_add] at h
  rw [dMB_slice, ← h]
  exact dMB_eq_zero_of_eqOn_const L.isOpen_domR L.one_mem_domR
    (fun a ha ↦ L.dMB_mul_fst ha x) x'

/-- The pure second derivative in the second factor vanishes. -/
theorem dMB_dMB_mul_snd (y y' : E) :
    dMB (dMB L.mul) (((L.one, L.one), (0, y)), ((0, y'), 0)) = 0 := by
  have h := dMB_comp_affine (fun z : E × E ↦ dMB L.mul (z, (0, y)))
    (LinearMap.inr ℝ E E) (L.one, (0 : E)) L.one y'
  simp only [LinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add] at h
  rw [dMB_slice, ← h]
  exact dMB_eq_zero_of_eqOn_const (L.isOpen_domL L.one) L.one_one_mem
    (fun b hb ↦ L.dMB_mul_snd hb y) y'

/-- **The second order term of the multiplication** ([GN26, Remark 5.1.8(a), Lemma 5.1.7]):
`d²m(1, 1)((x, y), (x, y)) = 2 b₂(x, y)`, i.e. the quadratic term of the Taylor expansion of `m`
at `(1, 1)` is `b₂(x, y)`. -/
theorem dMB_dMB_mul_one (v : E × E) :
    dMB (dMB L.mul) (((L.one, L.one), v), (v, 0)) = (2 : ℝ) • L.b2 v.1 v.2 := by
  obtain ⟨x, y⟩ := v
  have hv : ((x, y) : E × E) = (x, 0) + (0, y) := by simp
  have hs := (L.smooth 2).dMB_dMB_symm L.isOpen_dom L.one_one_mem
  rw [hv, dMB_dMB_mul_add_left, dMB_dMB_mul_add_right, dMB_dMB_mul_add_right,
    dMB_dMB_mul_fst, dMB_dMB_mul_snd, hs (x, 0) (0, y), ← L.b2_eq_dMB_dMB]
  simp only [Prod.fst_add, Prod.snd_add, add_zero, zero_add]
  rw [two_smul]

/-! ### Composites with the multiplication -/

variable {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X]

omit [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X] in
/-- First derivatives of `m ∘ τ` at a point `p` with `τ(p) = (1, 1)`. -/
theorem dMB_mul_comp {τ : X → E × E} {U : Set X} (hτ : ContDiffMBOn 1 τ U)
    (hτU : MapsTo τ U L.dom) {p : X} (hp : p ∈ U) (hτp : τ p = (L.one, L.one)) (v : X) :
    dMB (L.mul ∘ τ) (p, v) = (dMB τ (p, v)).1 + (dMB τ (p, v)).2 := by
  rw [ContDiffMBOn.dMB_comp L.isOpen_dom (L.smooth 1) hτ hτU hp, hτp, dMB_mul_one]

/-- **Second derivatives of `m ∘ τ`** at a point `p` with `τ(p) = (1, 1)`:
`d²(m ∘ τ)(p)(v, v) = 2 b₂(dτ₁ v, dτ₂ v) + d²τ₁(v, v) + d²τ₂(v, v)`. -/
theorem dMB_dMB_mul_comp {τ : X → E × E} {U : Set X} (hU : IsOpen U) (hτ : ContDiffMBOn 2 τ U)
    (hτU : MapsTo τ U L.dom) {p : X} (hp : p ∈ U) (hτp : τ p = (L.one, L.one)) (v : X) :
    dMB (dMB (L.mul ∘ τ)) ((p, v), (v, 0)) =
      (2 : ℝ) • L.b2 (dMB τ (p, v)).1 (dMB τ (p, v)).2 +
        ((dMB (dMB τ) ((p, v), (v, 0))).1 + (dMB (dMB τ) ((p, v), (v, 0))).2) := by
  rw [dMB_dMB_comp hU L.isOpen_dom (L.smooth 2) hτ hτU hp v v, hτp, dMB_dMB_mul_one,
    dMB_mul_one]

/-! ### The inversion -/

/-- **A local inversion** of a local group law: a `C²` map `ι` near the identity with
`x ∗ ι(x) = 1` ([GN26, Remark 5.1.8(b)]). -/
structure LocalInverse where
  /-- The inversion. -/
  inv : E → E
  /-- Its domain, a neighborhood of the identity. -/
  dom : Set E
  isOpen_dom : IsOpen dom
  one_mem : L.one ∈ dom
  contDiffMBOn : ContDiffMBOn 2 inv dom
  mul_inv_mem : ∀ a ∈ dom, (a, inv a) ∈ L.dom
  mul_inv : ∀ a ∈ dom, L.mul (a, inv a) = L.one

namespace LocalInverse

variable {L} (ι : L.LocalInverse)

private theorem hid1 : ContDiffMBOn 1 (fun a : E ↦ a) ι.dom := smoothMBOn_id _ 1

private theorem hid2 : ContDiffMBOn 2 (fun a : E ↦ a) ι.dom := smoothMBOn_id _ 2

theorem inv_one : ι.inv L.one = L.one := by
  have h := ι.mul_inv L.one ι.one_mem
  rwa [L.one_mul _ (ι.mul_inv_mem L.one ι.one_mem)] at h

/-- `a ↦ (a, ι(a))`. -/
def graph (a : E) : E × E := (a, ι.inv a)

theorem graph_eq : ι.graph = fun a ↦ (a, ι.inv a) := rfl

theorem contDiffMBOn_graph : ContDiffMBOn 2 ι.graph ι.dom :=
  ContDiffMBOn.prodMk ι.isOpen_dom (hid2 ι) ι.contDiffMBOn

theorem graph_one : ι.graph L.one = (L.one, L.one) := by
  simp only [graph, inv_one]

theorem mul_comp_graph : EqOn (L.mul ∘ ι.graph) (fun _ ↦ L.one) ι.dom :=
  fun a ha ↦ ι.mul_inv a ha

/-- **The first order term of the inversion** ([GN26, (5.6)]): `dι(1) x = −x`. -/
theorem dMB_inv_one (x : E) : dMB ι.inv (L.one, x) = -x := by
  have h0 := dMB_eq_zero_of_eqOn_const ι.isOpen_dom ι.one_mem ι.mul_comp_graph x
  rw [L.dMB_mul_comp (ι.contDiffMBOn_graph.of_le (by norm_num)) (fun a ha ↦ ι.mul_inv_mem a ha)
    ι.one_mem ι.graph_one, graph_eq, dMB_prodMk (hid1 ι)
      (ι.contDiffMBOn.of_le (by norm_num)) ι.one_mem] at h0
  have hid : dMB (fun a : E ↦ a) (L.one, x) = x :=
    ((ContinuousLinearMap.id ℝ E).hasDirDerivAt L.one x).dMB_eq
  rw [hid] at h0
  exact (neg_eq_of_add_eq_zero_right h0).symm

/-- **The second order term of the inversion** ([GN26, (5.6)]): `d²ι(1)(x, x) = 2 b₂(x, x)`,
i.e. `s₂(x) = b₂(x, x)`. -/
theorem dMB_dMB_inv_one (x : E) :
    dMB (dMB ι.inv) ((L.one, x), (x, 0)) = (2 : ℝ) • L.b2 x x := by
  have hU : IsOpen (ι.dom ×ˢ (univ : Set E)) := ι.isOpen_dom.prod isOpen_univ
  -- `d(m ∘ graph)` vanishes on `dom × E`
  have hd0 : EqOn (dMB (L.mul ∘ ι.graph)) (fun _ ↦ 0) (ι.dom ×ˢ univ) := by
    rintro ⟨a, h⟩ hq
    exact dMB_eq_zero_of_eqOn_const ι.isOpen_dom hq.1 ι.mul_comp_graph h
  have h0 := dMB_eq_zero_of_eqOn_const (y := (L.one, x)) hU ⟨ι.one_mem, mem_univ x⟩ hd0 (x, 0)
  rw [L.dMB_dMB_mul_comp ι.isOpen_dom ι.contDiffMBOn_graph (fun a ha ↦ ι.mul_inv_mem a ha)
    ι.one_mem ι.graph_one, graph_eq, dMB_prodMk (hid1 ι)
      (ι.contDiffMBOn.of_le (by norm_num)) ι.one_mem,
    dMB_dMB_prodMk ι.isOpen_dom (hid2 ι) ι.contDiffMBOn ι.one_mem] at h0
  have hid : dMB (fun a : E ↦ a) (L.one, x) = x :=
    ((ContinuousLinearMap.id ℝ E).hasDirDerivAt L.one x).dMB_eq
  have hid2 : dMB (dMB (fun a : E ↦ a)) ((L.one, x), (x, 0)) = 0 :=
    dMB_dMB_clm (ContinuousLinearMap.id ℝ E) L.one x x
  simp only [hid, hid2, ι.dMB_inv_one, L.b2_neg_right, smul_neg, zero_add] at h0
  exact (neg_add_eq_zero.mp h0).symm

/-! ### Conjugation and commutators -/

/-- `(a, b) ↦ (a ∗ b, ι(a))`. -/
def conjAux (q : E × E) : E × E := (L.mul q, (ι.inv ∘ ContinuousLinearMap.fst ℝ E E) q)

/-- **The conjugation** `(a, b) ↦ (a ∗ b) ∗ ι(a)`. -/
def conj (q : E × E) : E := L.mul (ι.conjAux q)

theorem conj_eq : ι.conj = L.mul ∘ ι.conjAux := rfl

/-- The pairs where `a ∗ b` and `ι(a)` are defined. -/
def conjAuxDom : Set (E × E) := L.dom ∩ Prod.fst ⁻¹' ι.dom

/-- The domain of the conjugation. -/
def conjDom : Set (E × E) := ι.conjAuxDom ∩ ι.conjAux ⁻¹' L.dom

theorem isOpen_conjAuxDom : IsOpen ι.conjAuxDom :=
  L.isOpen_dom.inter (ι.isOpen_dom.preimage continuous_fst)

/-- `ι ∘ A` is `C²` for continuous linear maps `A`. -/
theorem contDiffMBOn_inv_comp (A : (E × E) →L[ℝ] E) :
    ContDiffMBOn 2 (ι.inv ∘ ⇑A) (A ⁻¹' ι.dom) :=
  ContDiffMBOn.comp (ι.isOpen_dom.preimage A.continuous) ι.isOpen_dom ι.contDiffMBOn
    (A.contDiffMBOn 2 _) fun _ hq ↦ hq

theorem contDiffMBOn_conjAux : ContDiffMBOn 2 ι.conjAux ι.conjAuxDom :=
  ContDiffMBOn.prodMk ι.isOpen_conjAuxDom ((L.smooth 2).mono fun _ hq ↦ hq.1)
    ((ι.contDiffMBOn_inv_comp (ContinuousLinearMap.fst ℝ E E)).mono fun _ hq ↦ hq.2)

theorem isOpen_conjDom : IsOpen ι.conjDom :=
  ι.contDiffMBOn_conjAux.continuousOn.isOpen_inter_preimage ι.isOpen_conjAuxDom L.isOpen_dom

theorem one_one_mem_conjAuxDom : (L.one, L.one) ∈ ι.conjAuxDom :=
  ⟨L.one_one_mem, ι.one_mem⟩

theorem conjAux_one : ι.conjAux (L.one, L.one) = (L.one, L.one) := by
  simp only [conjAux, Function.comp_apply, ContinuousLinearMap.coe_fst', ι.inv_one,
    L.mul_one L.one L.one_one_mem]

theorem one_one_mem_conjDom : (L.one, L.one) ∈ ι.conjDom :=
  ⟨ι.one_one_mem_conjAuxDom, by
    change ι.conjAux (L.one, L.one) ∈ L.dom
    rw [conjAux_one]; exact L.one_one_mem⟩

theorem contDiffMBOn_conj : ContDiffMBOn 2 ι.conj ι.conjDom :=
  ContDiffMBOn.comp ι.isOpen_conjDom L.isOpen_dom (L.smooth 2)
    (ι.contDiffMBOn_conjAux.mono inter_subset_left) fun _ hq ↦ hq.2

theorem conj_one : ι.conj (L.one, L.one) = L.one := by
  rw [conj, conjAux_one, L.mul_one L.one L.one_one_mem]

theorem dMB_conjAux_one (v : E × E) :
    dMB ι.conjAux ((L.one, L.one), v) = (v.1 + v.2, -v.1) := by
  have h := dMB_prodMk ((L.smooth 1).mono fun _ (hq : _ ∈ ι.conjAuxDom) ↦ hq.1)
    (((ι.contDiffMBOn_inv_comp (ContinuousLinearMap.fst ℝ E E)).mono
      fun _ (hq : _ ∈ ι.conjAuxDom) ↦ hq.2).of_le
      (by norm_num)) ι.one_one_mem_conjAuxDom v
  rw [L.dMB_mul_one, dMB_comp_clm] at h
  simp only [ContinuousLinearMap.coe_fst', ι.dMB_inv_one] at h
  exact h

theorem dMB_dMB_conjAux_one (v : E × E) :
    dMB (dMB ι.conjAux) (((L.one, L.one), v), (v, 0)) =
      ((2 : ℝ) • L.b2 v.1 v.2, (2 : ℝ) • L.b2 v.1 v.1) := by
  have h := dMB_dMB_prodMk ι.isOpen_conjAuxDom
    ((L.smooth 2).mono fun _ (hq : _ ∈ ι.conjAuxDom) ↦ hq.1)
    ((ι.contDiffMBOn_inv_comp (ContinuousLinearMap.fst ℝ E E)).mono
      fun _ (hq : _ ∈ ι.conjAuxDom) ↦ hq.2) ι.one_one_mem_conjAuxDom v v
  rw [L.dMB_dMB_mul_one, dMB_dMB_comp_clm] at h
  simp only [ContinuousLinearMap.coe_fst'] at h
  rw [ι.dMB_dMB_inv_one] at h
  exact h

/-- **The first order term of the conjugation** ([GN26, (5.7)]): the derivative of
`(a, b) ↦ (a ∗ b) ∗ ι(a)` at `(1, 1)` is `(x, y) ↦ y`. -/
theorem dMB_conj_one (v : E × E) : dMB ι.conj ((L.one, L.one), v) = v.2 := by
  have h := L.dMB_mul_comp ((ι.contDiffMBOn_conjAux.mono inter_subset_left).of_le
    (by norm_num)) (fun _ hq ↦ hq.2) ι.one_one_mem_conjDom ι.conjAux_one v
  rw [ι.dMB_conjAux_one] at h
  rw [conj_eq, h]
  simp

/-- **The second order term of the conjugation** ([GN26, (5.7)]):
`d²((a, b) ↦ (a ∗ b) ∗ ι(a))(1, 1)((x, y), (x, y)) = 2 [x, y]`, i.e.
`(x ∗ y) ∗ x⁻¹ = y + [x, y] + ⋯`. -/
theorem dMB_dMB_conj_one (v : E × E) :
    dMB (dMB ι.conj) (((L.one, L.one), v), (v, 0)) = (2 : ℝ) • L.bracket v.1 v.2 := by
  have h := L.dMB_dMB_mul_comp ι.isOpen_conjDom (ι.contDiffMBOn_conjAux.mono inter_subset_left)
    (fun _ hq ↦ hq.2) ι.one_one_mem_conjDom ι.conjAux_one v
  rw [ι.dMB_conjAux_one, ι.dMB_dMB_conjAux_one] at h
  rw [conj_eq, h,
    bracket_eq_b2_sub_b2]
  simp only [L.b2_add_left, L.b2_neg_right, smul_add, smul_neg, smul_sub]
  abel

/-- `(a, b) ↦ ((a ∗ b) ∗ ι(a), ι(b))`. -/
def commAux (q : E × E) : E × E := (ι.conj q, (ι.inv ∘ ContinuousLinearMap.snd ℝ E E) q)

/-- **The commutator** `(a, b) ↦ ((a ∗ b) ∗ ι(a)) ∗ ι(b)`. -/
def commutator (q : E × E) : E := L.mul (ι.commAux q)

theorem commutator_eq : ι.commutator = L.mul ∘ ι.commAux := rfl

/-- The pairs where the conjugation and `ι(b)` are defined. -/
def commAuxDom : Set (E × E) := ι.conjDom ∩ Prod.snd ⁻¹' ι.dom

/-- The domain of the commutator. -/
def commutatorDom : Set (E × E) := ι.commAuxDom ∩ ι.commAux ⁻¹' L.dom

theorem isOpen_commAuxDom : IsOpen ι.commAuxDom :=
  ι.isOpen_conjDom.inter (ι.isOpen_dom.preimage continuous_snd)

theorem contDiffMBOn_commAux : ContDiffMBOn 2 ι.commAux ι.commAuxDom :=
  ContDiffMBOn.prodMk ι.isOpen_commAuxDom (ι.contDiffMBOn_conj.mono fun _ hq ↦ hq.1)
    ((ι.contDiffMBOn_inv_comp (ContinuousLinearMap.snd ℝ E E)).mono fun _ hq ↦ hq.2)

theorem isOpen_commutatorDom : IsOpen ι.commutatorDom :=
  ι.contDiffMBOn_commAux.continuousOn.isOpen_inter_preimage ι.isOpen_commAuxDom L.isOpen_dom

theorem one_one_mem_commAuxDom : (L.one, L.one) ∈ ι.commAuxDom :=
  ⟨ι.one_one_mem_conjDom, ι.one_mem⟩

theorem commAux_one : ι.commAux (L.one, L.one) = (L.one, L.one) := by
  simp only [commAux, Function.comp_apply, ContinuousLinearMap.coe_snd', ι.inv_one, ι.conj_one]

theorem one_one_mem_commutatorDom : (L.one, L.one) ∈ ι.commutatorDom :=
  ⟨ι.one_one_mem_commAuxDom, by
    change ι.commAux (L.one, L.one) ∈ L.dom
    rw [commAux_one]; exact L.one_one_mem⟩

theorem dMB_commAux_one (v : E × E) : dMB ι.commAux ((L.one, L.one), v) = (v.2, -v.2) := by
  have h := dMB_prodMk ((ι.contDiffMBOn_conj.mono fun _ (hq : _ ∈ ι.commAuxDom) ↦ hq.1).of_le
      (by norm_num))
    (((ι.contDiffMBOn_inv_comp (ContinuousLinearMap.snd ℝ E E)).mono
      fun _ (hq : _ ∈ ι.commAuxDom) ↦ hq.2).of_le (by norm_num)) ι.one_one_mem_commAuxDom v
  rw [ι.dMB_conj_one, dMB_comp_clm] at h
  simp only [ContinuousLinearMap.coe_snd', ι.dMB_inv_one] at h
  exact h

theorem dMB_dMB_commAux_one (v : E × E) :
    dMB (dMB ι.commAux) (((L.one, L.one), v), (v, 0)) =
      ((2 : ℝ) • L.bracket v.1 v.2, (2 : ℝ) • L.b2 v.2 v.2) := by
  have h := dMB_dMB_prodMk ι.isOpen_commAuxDom
    (ι.contDiffMBOn_conj.mono fun _ (hq : _ ∈ ι.commAuxDom) ↦ hq.1)
    ((ι.contDiffMBOn_inv_comp (ContinuousLinearMap.snd ℝ E E)).mono
      fun _ (hq : _ ∈ ι.commAuxDom) ↦ hq.2) ι.one_one_mem_commAuxDom v v
  rw [ι.dMB_dMB_conj_one, dMB_dMB_comp_clm] at h
  simp only [ContinuousLinearMap.coe_snd'] at h
  rw [ι.dMB_dMB_inv_one] at h
  exact h

/-- **The first order term of the commutator** ([GN26, (5.8)]): the derivative of
`(a, b) ↦ ((a ∗ b) ∗ ι(a)) ∗ ι(b)` at `(1, 1)` vanishes. -/
theorem dMB_commutator_one (v : E × E) : dMB ι.commutator ((L.one, L.one), v) = 0 := by
  have h := L.dMB_mul_comp ((ι.contDiffMBOn_commAux.mono inter_subset_left).of_le
    (by norm_num)) (fun _ hq ↦ hq.2) ι.one_one_mem_commutatorDom ι.commAux_one v
  rw [ι.dMB_commAux_one] at h
  rw [commutator_eq, h]
  simp

/-- **The second order term of the commutator** ([GN26, (5.8)]):
`d²((a, b) ↦ ((a ∗ b) ∗ ι(a)) ∗ ι(b))(1, 1)((x, y), (x, y)) = 2 [x, y]`, i.e.
`x ∗ y ∗ x⁻¹ ∗ y⁻¹ = [x, y] + ⋯`. -/
theorem dMB_dMB_commutator_one (v : E × E) :
    dMB (dMB ι.commutator) (((L.one, L.one), v), (v, 0)) = (2 : ℝ) • L.bracket v.1 v.2 := by
  have h := L.dMB_dMB_mul_comp ι.isOpen_commutatorDom
    (ι.contDiffMBOn_commAux.mono inter_subset_left) (fun _ hq ↦ hq.2)
    ι.one_one_mem_commutatorDom ι.commAux_one v
  rw [ι.dMB_commAux_one, ι.dMB_dMB_commAux_one] at h
  rw [commutator_eq, h]
  simp only [L.b2_neg_right, smul_neg]
  abel

end LocalInverse

end LocalGroupLaw

/-! ### Lie groups -/

namespace MBLieGroup

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]

variable (E G)

/-- **The inversion of `G` in the chart `φ` at the identity**, `z ↦ φ(φ⁻¹(z)⁻¹)`, a local
inversion of `localGroupLaw E G` ([GN26, Remark 5.1.8(b)]). -/
def localInverse : (localGroupLaw E G).LocalInverse where
  inv z := chartAt E (1 : G) ((chartAt E (1 : G)).symm z)⁻¹
  dom := chartDomain (fun g : G ↦ g⁻¹) univ (chartAt E (1 : G)) (chartAt E (1 : G))
  isOpen_dom := isOpen_chartDomain isOpen_univ
    (continuousOn_univ.2 (isTopologicalGroup E G).continuous_inv) _ _
  one_mem := by
    have h1 := mem_chart_source E (1 : G)
    refine ⟨(chartAt E (1 : G)).map_source h1, mem_univ _, ?_⟩
    change ((chartAt E (1 : G)).symm (chartAt E (1 : G) 1))⁻¹ ∈ (chartAt E (1 : G)).source
    rw [(chartAt E (1 : G)).left_inv h1, inv_one]
    exact h1
  contDiffMBOn := by
    have hk := (smoothMBM_inv (E := E) (G := G) 2).2 (1 : G) (mem_univ _)
    simp only [inv_one] at hk
    exact hk
  mul_inv_mem a ha := by
    set φ := chartAt E (1 : G)
    refine ⟨⟨ha.1, φ.map_source ha.2.2⟩, ?_⟩
    change φ.symm a * φ.symm (φ (φ.symm a)⁻¹) ∈ φ.source
    rw [φ.left_inv ha.2.2, _root_.mul_inv_cancel]
    exact mem_chart_source E (1 : G)
  mul_inv a ha := by
    set φ := chartAt E (1 : G)
    change φ (φ.symm a * φ.symm (φ (φ.symm a)⁻¹)) = φ 1
    rw [φ.left_inv ha.2.2, _root_.mul_inv_cancel]

variable {E G}

/-- In the chart, the commutator of `localInverse E G` is the commutator of `G`. -/
theorem localInverse_commutator {q : E × E} (hq : q ∈ (localInverse E G).commutatorDom) :
    (localInverse E G).commutator q =
      chartAt E (1 : G) ((chartAt E (1 : G)).symm q.1 * (chartAt E (1 : G)).symm q.2 *
        ((chartAt E (1 : G)).symm q.1)⁻¹ * ((chartAt E (1 : G)).symm q.2)⁻¹) := by
  set φ := chartAt E (1 : G)
  have h1 : φ.symm q.1 * φ.symm q.2 ∈ φ.source := hq.1.1.1.1.2
  have h2 : (φ.symm q.1)⁻¹ ∈ φ.source := hq.1.1.1.2.2.2
  have h3 : (φ.symm q.2)⁻¹ ∈ φ.source := hq.1.2.2.2
  have h4 : φ.symm (φ (φ.symm q.1 * φ.symm q.2)) * φ.symm (φ (φ.symm q.1)⁻¹) ∈ φ.source :=
    hq.1.1.2.2
  rw [φ.left_inv h1, φ.left_inv h2] at h4
  change φ (φ.symm (φ (φ.symm (φ (φ.symm q.1 * φ.symm q.2)) * φ.symm (φ (φ.symm q.1)⁻¹))) *
    φ.symm (φ (φ.symm q.2)⁻¹)) = _
  rw [φ.left_inv h1, φ.left_inv h2, φ.left_inv h4, φ.left_inv h3]

/-- **The commutator of `G` in the chart at the identity** ([GN26, Remark 5.1.8(c), (5.8)]):
`(g, h) ↦ φ(g h g⁻¹ h⁻¹)` has vanishing first derivative at `(1, 1)`, and its second order term
is the Lie bracket: `d²(1, 1)((x, y), (x, y)) = 2 [x, y]`. -/
theorem LieAlg.dMB_dMB_commutator (x y : LieAlg E G) :
    dMB (dMB (localInverse E G).commutator)
      ((((localGroupLaw E G).one, (localGroupLaw E G).one), ((x : E), (y : E))),
        (((x : E), (y : E)), 0)) = (2 : ℝ) • ⁅x, y⁆ :=
  (localInverse E G).dMB_dMB_commutator_one (x, y)

end MBLieGroup

end LocallyConvex.LieGroups
