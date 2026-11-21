/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.VectorField.Basic

/-!
# Local group laws and their Lie brackets

The Lie bracket of a Lie group `G` is computed in a chart `φ` at the identity
([GN26, Definition 5.1.6, (5.5)]). In such a chart the multiplication becomes a smooth map
`x ∗ y = φ(φ⁻¹(x) φ⁻¹(y))`, defined on an open set of pairs, which is associative and has the
neutral element `φ(1)` wherever both sides are defined: a *local group law*
(`LocalGroupLaw`, the data of [GN26, Remark 5.1.8]). This file develops the Lie bracket of a
local group law; `LieAlgebra/Basic.lean` applies it to Lie groups.

For `x ∈ E` the local representative of the left invariant vector field with value `x` at the
identity is `x̃_l(z) = d(b ↦ z ∗ b)(1) x` (`LocalGroupLaw.xl`, [GN26, (5.4)]), and the bracket is
the local bracket of these fields at the identity,
`[x, y] = [x̃_l, ỹ_l](1) = dỹ_l(1) x − dx̃_l(1) y` ([GN26, (5.5)]).

## Main definitions

* `LocalGroupLaw E`: a smooth local group law on an open subset of `E`.
* `LocalGroupLaw.xl x`: the local left invariant vector field with value `x` at the identity.
* `LocalGroupLaw.bracket`: the Lie bracket `[x, y] = [x̃_l, ỹ_l](1)`.

## Main results

* `LocalGroupLaw.xl_mul`: the fields `x̃_l` are left invariant.
* `LocalGroupLaw.localBracket_xl`: `[x̃_l, ỹ_l] = [x, y]~_l` near the identity ([GN26, (5.3)]).
* `LocalGroupLaw.bracket_jacobi`, `bracket_swap`, `bracket_self`, `add_bracket`, `bracket_add`,
  `smul_bracket`, `bracket_smul`: the bracket is a Lie bracket.
* `LocalGroupLaw.continuous_bracket`: the bracket is continuous ([GN26, Definition 5.1.6]).
* `LocalGroupLaw.dMB_bracket_of_hom`: the derivative at the identity of a local homomorphism
  preserves brackets ([GN26, Proposition 5.1.10]).
* `LocalGroupLaw.bracket_eq_zero_of_comm`: commutative local group laws have vanishing bracket
  ([GN26, Example 5.1.9(a)]).

## Implementation notes

The left invariance `x̃_l(a ∗ w) = d(b ↦ a ∗ b)(w) x̃_l(w)` follows from differentiating the
associativity `(a ∗ w) ∗ c = a ∗ (w ∗ c)` in `c` at the identity. With it, the left translations
`b ↦ a ∗ b` relate the fields `x̃_l` to themselves, and the transformation rule of local brackets
(lc-manifolds, `localBracket_transition`) gives `[x̃_l, ỹ_l](a) = [x, y]~_l(a)`; the Jacobi
identity then follows from the Jacobi identity of local brackets (`localBracket_jacobi`). This
avoids the tangent bundle of `G` altogether.

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

/-- **A smooth local group law** on the locally convex space `E` (the multiplication of a Lie
group in a chart at the identity, [GN26, Remark 5.1.8]): a smooth map `mul` on an open set `dom`
of pairs, with a neutral element `one` and associative wherever both sides are defined. -/
structure LocalGroupLaw (E : Type u) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] where
  /-- The multiplication. -/
  mul : E × E → E
  /-- The domain of the multiplication. -/
  dom : Set (E × E)
  /-- The neutral element. -/
  one : E
  isOpen_dom : IsOpen dom
  one_one_mem : (one, one) ∈ dom
  smooth : SmoothMBOn mul dom
  one_mul : ∀ b, (one, b) ∈ dom → mul (one, b) = b
  mul_one : ∀ a, (a, one) ∈ dom → mul (a, one) = a
  mul_assoc : ∀ a b c, (a, b) ∈ dom → (b, c) ∈ dom → (mul (a, b), c) ∈ dom →
    (a, mul (b, c)) ∈ dom → mul (mul (a, b), c) = mul (a, mul (b, c))

namespace LocalGroupLaw

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] (L : LocalGroupLaw E)

/-- The points `b` with `a ∗ b` defined. -/
def domL (a : E) : Set E := {b | (a, b) ∈ L.dom}

/-- The points `a` with `a ∗ 1` defined, where the left invariant fields are defined. -/
def domR : Set E := {a | (a, L.one) ∈ L.dom}

theorem isOpen_domL (a : E) : IsOpen (L.domL a) :=
  L.isOpen_dom.preimage (by fun_prop)

theorem isOpen_domR : IsOpen L.domR :=
  L.isOpen_dom.preimage (by fun_prop)

theorem one_mem_domR : L.one ∈ L.domR :=
  L.one_one_mem

/-- The left multiplications `b ↦ a ∗ b` are smooth. -/
theorem contDiffMBOn_mul_left (k : ℕ) (a : E) :
    ContDiffMBOn k (fun b ↦ L.mul (a, b)) (L.domL a) :=
  ContDiffMBOn.comp (g := L.mul) (f := fun b ↦ (a, b)) (L.isOpen_domL a) L.isOpen_dom (L.smooth k)
    ((contDiffMBOn_const k a _).prodMk (L.isOpen_domL a) (smoothMBOn_id _ k)) fun _ h ↦ h

/-! ### Left invariant vector fields -/

/-- **The local left invariant vector field** with value `x` at the identity,
`x̃_l(z) = d(b ↦ z ∗ b)(1) x` ([GN26, (5.4)]). -/
def xl (x z : E) : E := dMB L.mul ((z, L.one), (0, x))

theorem xl_eq (x z : E) : L.xl x z = dMB (fun b ↦ L.mul (z, b)) (L.one, x) :=
  dMB_slice₂ L.mul z L.one x

/-- The fields `x̃_l` are smooth. -/
theorem contDiffMBOn_xl (k : ℕ) (x : E) : ContDiffMBOn k (L.xl x) L.domR := by
  have hin : ContDiffMBOn k (fun z : E ↦ ((z, L.one), ((0 : E), x))) L.domR :=
    ((smoothMBOn_id _ k).prodMk L.isOpen_domR (contDiffMBOn_const k L.one _)).prodMk
      L.isOpen_domR (contDiffMBOn_const k ((0 : E), x) _)
  exact ContDiffMBOn.comp (g := dMB L.mul) L.isOpen_domR (L.isOpen_dom.prod isOpen_univ)
    (L.smooth (k + 1)).2.2 hin fun _ hz ↦ ⟨hz, mem_univ _⟩

/-- `x̃_l(1) = x`. -/
theorem xl_one (x : E) : L.xl x L.one = x := by
  rw [xl_eq]
  have h : (fun b ↦ L.mul (L.one, b)) =ᶠ[𝓝 L.one] fun b ↦ (ContinuousLinearMap.id ℝ E) b :=
    eventuallyEq_of_mem ((L.isOpen_domL L.one).mem_nhds L.one_one_mem) fun b hb ↦ L.one_mul b hb
  rw [dMB_congr_of_eventuallyEq h, ((ContinuousLinearMap.id ℝ E).hasDirDerivAt L.one x).dMB_eq]
  rfl

theorem xl_add (x x' : E) {z : E} (hz : z ∈ L.domR) :
    L.xl (x + x') z = L.xl x z + L.xl x' z := by
  simp only [xl]
  rw [show ((0 : E), x + x') = (0, x) + (0, x') by simp]
  exact (L.smooth 1).dMB_add L.isOpen_dom hz _ _

theorem xl_smul (c : ℝ) (x : E) {z : E} (hz : z ∈ L.domR) : L.xl (c • x) z = c • L.xl x z := by
  simp only [xl]
  rw [show ((0 : E), c • x) = c • (0, x) by simp]
  exact (L.smooth 1).dMB_smul hz c _

/-- `dx̃_l(z) v` as a second derivative of the multiplication. -/
theorem dMB_xl (y z x : E) :
    dMB (L.xl y) (z, x) = dMB (dMB L.mul) (((z, L.one), (0, y)), ((x, 0), 0)) := by
  have h := dMB_comp_affine (dMB L.mul)
    ((LinearMap.inl ℝ (E × E) (E × E)).comp (LinearMap.inl ℝ E E)) (((0 : E), L.one), ((0 : E), y))
    z x
  simp only [LinearMap.comp_apply, LinearMap.inl_apply, Prod.mk_add_mk, zero_add, add_zero] at h
  exact h

/-- **The fields `x̃_l` are left invariant**: `x̃_l(a ∗ w) = d(b ↦ a ∗ b)(w) x̃_l(w)`. -/
theorem xl_mul (x : E) {a w : E} (haw : (a, w) ∈ L.dom) (hw : (w, L.one) ∈ L.dom)
    (haw1 : (L.mul (a, w), L.one) ∈ L.dom) :
    L.xl x (L.mul (a, w)) = dMB (fun b ↦ L.mul (a, b)) (w, L.xl x w) := by
  rw [xl_eq, xl_eq]
  set U := L.domL w ∩ (fun c ↦ L.mul (w, c)) ⁻¹' L.domL a
  have hU : IsOpen U :=
    (L.contDiffMBOn_mul_left 0 w).continuousOn.isOpen_inter_preimage (L.isOpen_domL w)
      (L.isOpen_domL a)
  have hwa : L.mul (w, L.one) = w := L.mul_one w hw
  have h1U : L.one ∈ U := ⟨hw, show (a, L.mul (w, L.one)) ∈ L.dom by rw [hwa]; exact haw⟩
  have hh : (fun c ↦ L.mul (L.mul (a, w), c)) =ᶠ[𝓝 L.one]
      (fun b ↦ L.mul (a, b)) ∘ fun c ↦ L.mul (w, c) := by
    filter_upwards [hU.mem_nhds h1U, (L.isOpen_domL _).mem_nhds haw1] with c hc hc'
    exact L.mul_assoc a w c haw hc.1 hc' hc.2
  rw [dMB_eq_comp_of_eventuallyEq (L.isOpen_domL a) (L.contDiffMBOn_mul_left 1 a)
    ((L.contDiffMBOn_mul_left 1 w).mono inter_subset_left) (fun _ hc ↦ hc.2) h1U hh x, hwa]

/-! ### The bracket -/

/-- **The Lie bracket** of a local group law, `[x, y] = [x̃_l, ỹ_l](1)` ([GN26, (5.5)]). -/
def bracket (x y : E) : E := localBracket (L.xl x) (L.xl y) L.one

theorem bracket_eq (x y : E) :
    L.bracket x y = dMB (L.xl y) (L.one, x) - dMB (L.xl x) (L.one, y) := by
  rw [bracket, localBracket, xl_one, xl_one]

/-- **Brackets of left invariant fields are left invariant** ([GN26, (5.3)]):
`[x̃_l, ỹ_l](a) = [x, y]~_l(a)`. -/
theorem localBracket_xl (x y : E) {a : E} (ha : a ∈ L.domR) :
    localBracket (L.xl x) (L.xl y) a = L.xl (L.bracket x y) a := by
  set U := L.domR ∩ (L.domL a ∩ (fun b ↦ L.mul (a, b)) ⁻¹' L.domR)
  have hU : IsOpen U := L.isOpen_domR.inter
    ((L.contDiffMBOn_mul_left 0 a).continuousOn.isOpen_inter_preimage (L.isOpen_domL a)
      L.isOpen_domR)
  have ha1 : L.mul (a, L.one) = a := L.mul_one a ha
  have h1U : L.one ∈ U := ⟨L.one_one_mem, ha, by simpa only [mem_preimage, ha1] using ha⟩
  have hrel : ∀ z : E, ∀ w ∈ U,
      L.xl z (L.mul (a, w)) = dMB (fun b ↦ L.mul (a, b)) (w, L.xl z w) :=
    fun z w hw ↦ L.xl_mul z hw.2.1 hw.1 hw.2.2
  have h := localBracket_transition (τ := fun b ↦ L.mul (a, b)) (L.isOpen_domL a) hU L.isOpen_domR
    (fun _ hw ↦ hw.2.1) (L.contDiffMBOn_mul_left 2 a) (fun _ hw ↦ hw.2.2)
    ((L.contDiffMBOn_xl 1 x).mono fun _ hw ↦ hw.1) ((L.contDiffMBOn_xl 1 y).mono fun _ hw ↦ hw.1)
    (L.contDiffMBOn_xl 1 x) (L.contDiffMBOn_xl 1 y) (hrel x) (hrel y) h1U
  simp only [ha1] at h
  rw [h, xl_eq]
  rfl

theorem localBracket_xl_eventuallyEq (x y : E) :
    localBracket (L.xl x) (L.xl y) =ᶠ[𝓝 L.one] L.xl (L.bracket x y) :=
  eventuallyEq_of_mem (L.isOpen_domR.mem_nhds L.one_mem_domR) fun _ ha ↦ L.localBracket_xl x y ha

/-- **The Jacobi identity.** -/
theorem bracket_jacobi (x y z : E) :
    L.bracket x (L.bracket y z) + L.bracket y (L.bracket z x) + L.bracket z (L.bracket x y) =
      0 := by
  have h := localBracket_jacobi L.isOpen_domR (L.contDiffMBOn_xl 2 x) (L.contDiffMBOn_xl 2 y)
    (L.contDiffMBOn_xl 2 z) L.one_mem_domR
  rwa [localBracket_congr_right (L.localBracket_xl_eventuallyEq y z),
    localBracket_congr_right (L.localBracket_xl_eventuallyEq z x),
    localBracket_congr_right (L.localBracket_xl_eventuallyEq x y)] at h

theorem bracket_swap (x y : E) : L.bracket y x = -L.bracket x y :=
  localBracket_swap _ _ _

theorem bracket_self (x : E) : L.bracket x x = 0 :=
  sub_self _

theorem dMB_xl_add (y y' v : E) :
    dMB (L.xl (y + y')) (L.one, v) = dMB (L.xl y) (L.one, v) + dMB (L.xl y') (L.one, v) :=
  dMB_eq_add_of_eqOn L.isOpen_domR L.one_mem_domR (L.contDiffMBOn_xl 1 y)
    (L.contDiffMBOn_xl 1 y') (fun _ hz ↦ L.xl_add y y' hz) v

theorem dMB_xl_smul (c : ℝ) (y v : E) :
    dMB (L.xl (c • y)) (L.one, v) = c • dMB (L.xl y) (L.one, v) :=
  dMB_eq_smul_of_eqOn L.isOpen_domR L.one_mem_domR (L.contDiffMBOn_xl 1 y) c
    (fun _ hz ↦ L.xl_smul c y hz) v

theorem add_bracket (x x' y : E) : L.bracket (x + x') y = L.bracket x y + L.bracket x' y := by
  rw [bracket_eq, bracket_eq, bracket_eq, L.dMB_xl_add,
    (L.contDiffMBOn_xl 1 y).dMB_add L.isOpen_domR L.one_mem_domR]
  abel

theorem bracket_add (x y y' : E) : L.bracket x (y + y') = L.bracket x y + L.bracket x y' := by
  rw [bracket_eq, bracket_eq, bracket_eq, L.dMB_xl_add,
    (L.contDiffMBOn_xl 1 x).dMB_add L.isOpen_domR L.one_mem_domR]
  abel

theorem bracket_smul (c : ℝ) (x y : E) : L.bracket x (c • y) = c • L.bracket x y := by
  rw [bracket_eq, bracket_eq, L.dMB_xl_smul, (L.contDiffMBOn_xl 1 x).dMB_smul L.one_mem_domR,
    smul_sub]

theorem bracket_neg (x y : E) : L.bracket x (-y) = -L.bracket x y := by
  rw [← neg_one_smul ℝ y, bracket_smul, neg_one_smul]

theorem smul_bracket (c : ℝ) (x y : E) : L.bracket (c • x) y = c • L.bracket x y := by
  rw [bracket_eq, bracket_eq, L.dMB_xl_smul, (L.contDiffMBOn_xl 1 y).dMB_smul L.one_mem_domR,
    smul_sub]

/-- **The bracket is continuous** ([GN26, Definition 5.1.6]): it is a second derivative of the
multiplication. -/
theorem continuous_bracket : Continuous fun p : E × E ↦ L.bracket p.1 p.2 := by
  have hc : ContinuousOn (dMB (dMB L.mul)) ((L.dom ×ˢ univ) ×ˢ univ) := (L.smooth 2).2.2.2.2
  have hβ : Continuous fun p : E × E ↦
      dMB (dMB L.mul) (((L.one, L.one), ((0 : E), p.2)), ((p.1, (0 : E)), (0 : E × E))) :=
    hc.comp_continuous (by fun_prop) fun _ ↦ ⟨⟨L.one_one_mem, mem_univ _⟩, mem_univ _⟩
  have hβ' : Continuous fun p : E × E ↦
      dMB (dMB L.mul) (((L.one, L.one), ((0 : E), p.1)), ((p.2, (0 : E)), (0 : E × E))) :=
    hc.comp_continuous (by fun_prop) fun _ ↦ ⟨⟨L.one_one_mem, mem_univ _⟩, mem_univ _⟩
  refine (hβ.sub hβ').congr fun p ↦ ?_
  rw [bracket_eq, dMB_xl, dMB_xl]
  rfl

/-! ### Homomorphisms -/

variable {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

/-- **Local homomorphisms preserve brackets** ([GN26, Proposition 5.1.10]): if `f` is `C^2` near
the identity and `f(a ∗ b) = f(a) ∗' f(b)` wherever both sides are defined, then `df(1)` is a
homomorphism of brackets. -/
theorem dMB_bracket_of_hom (L' : LocalGroupLaw F) {f : E → F} {W : Set E} (hW : IsOpen W)
    (h1W : L.one ∈ W) (hf : ContDiffMBOn 2 f W) (hf1 : f L.one = L'.one)
    (hhom : ∀ a b, (a, b) ∈ L.dom → a ∈ W → b ∈ W → L.mul (a, b) ∈ W → (f a, f b) ∈ L'.dom →
      f (L.mul (a, b)) = L'.mul (f a, f b)) (x y : E) :
    dMB f (L.one, L.bracket x y) = L'.bracket (dMB f (L.one, x)) (dMB f (L.one, y)) := by
  have hf1' : ContDiffMBOn 1 f W := hf.of_le (by norm_num)
  set U := (W ∩ f ⁻¹' L'.domR) ∩ L.domR
  have hU : IsOpen U :=
    (hf.continuousOn.isOpen_inter_preimage hW L'.isOpen_domR).inter L.isOpen_domR
  have h1U : L.one ∈ U := ⟨⟨h1W, by rw [mem_preimage, hf1]; exact L'.one_mem_domR⟩,
    L.one_mem_domR⟩
  -- the fields `x̃_l` and `(df(1) x)~_l` are `f`-related
  have hrel : ∀ x : E, ∀ z ∈ U, L'.xl (dMB f (L.one, x)) (f z) = dMB f (z, L.xl x z) := by
    intro x z hz
    have hzW : z ∈ W := hz.1.1
    have hz1 : L.mul (z, L.one) = z := L.mul_one z hz.2
    -- `b ↦ f (z ∗ b)` near the identity
    set V₁ := L.domL z ∩ (fun b ↦ L.mul (z, b)) ⁻¹' W
    have hV₁ : IsOpen V₁ :=
      (L.contDiffMBOn_mul_left 0 z).continuousOn.isOpen_inter_preimage (L.isOpen_domL z) hW
    have h1V₁ : L.one ∈ V₁ := ⟨hz.2, by rw [mem_preimage, hz1]; exact hzW⟩
    set V₂ := W ∩ f ⁻¹' L'.domL (f z)
    have hV₂ : IsOpen V₂ := hf.continuousOn.isOpen_inter_preimage hW (L'.isOpen_domL _)
    have h1V₂ : L.one ∈ V₂ := ⟨h1W, by
      change (f z, f L.one) ∈ L'.dom
      rw [hf1]; exact hz.1.2⟩
    have hh : (fun b ↦ f (L.mul (z, b))) =ᶠ[𝓝 L.one] (fun b' ↦ L'.mul (f z, b')) ∘ f := by
      filter_upwards [hV₁.mem_nhds h1V₁, hV₂.mem_nhds h1V₂] with b hb hb'
      exact hhom z b hb.1 hzW hb'.1 hb.2 hb'.2
    have e₁ := dMB_eq_comp_of_eventuallyEq (L'.isOpen_domL (f z)) (L'.contDiffMBOn_mul_left 1 _)
      (hf1'.mono inter_subset_left) (fun _ hb ↦ hb.2) h1V₂ hh x
    have e₂ : dMB (fun b ↦ f (L.mul (z, b))) (L.one, x) =
        dMB f (L.mul (z, L.one), dMB (fun b ↦ L.mul (z, b)) (L.one, x)) :=
      dMB_eq_comp_of_eventuallyEq hW hf1'
        ((L.contDiffMBOn_mul_left 1 z).mono inter_subset_left) (fun _ hb ↦ hb.2) h1V₁
        (EventuallyEq.refl _ _) x
    rw [xl_eq, ← hf1, ← e₁, e₂, hz1, xl_eq]
  have h := localBracket_transition (τ := f) hW hU L'.isOpen_domR (fun _ hz ↦ hz.1.1) hf
    (fun _ hz ↦ hz.1.2) ((L.contDiffMBOn_xl 1 x).mono fun _ hz ↦ hz.2)
    ((L.contDiffMBOn_xl 1 y).mono fun _ hz ↦ hz.2) (L'.contDiffMBOn_xl 1 _)
    (L'.contDiffMBOn_xl 1 _) (hrel x) (hrel y) h1U
  rw [hf1] at h
  exact h.symm

/-! ### Commutative local group laws -/

/-- **Commutative local group laws have vanishing bracket** ([GN26, Example 5.1.9(a)]): the
second derivative of the multiplication at `(1, 1)` is then symmetric in the two factors. -/
theorem bracket_eq_zero_of_comm
    (hc : ∀ a b, (a, b) ∈ L.dom → (b, a) ∈ L.dom ∧ L.mul (b, a) = L.mul (a, b)) (x y : E) :
    L.bracket x y = 0 := by
  set S : E × E →ₗ[ℝ] E × E := (LinearEquiv.prodComm ℝ E E).toLinearMap
  have hS : ∀ p : E × E, S p = p.swap := fun _ ↦ rfl
  -- `dm(p, h) = dm(p.swap, h.swap)` on `dom × E²`
  have hd : ∀ q ∈ L.dom ×ˢ (univ : Set (E × E)),
      dMB L.mul q = dMB L.mul (S q.1, S q.2) := by
    rintro ⟨p, h⟩ ⟨hp, -⟩
    have hev : L.mul =ᶠ[𝓝 p] L.mul ∘ S :=
      eventuallyEq_of_mem (L.isOpen_dom.mem_nhds hp) fun p' hp' ↦ by
        simp only [Function.comp_apply, hS, Prod.swap]
        exact (hc p'.1 p'.2 hp').2.symm
    rw [dMB_congr_of_eventuallyEq hev, dMB_comp_linearMap]
  set SS : (E × E) × (E × E) →ₗ[ℝ] (E × E) × (E × E) := S.prodMap S
  have hev : dMB L.mul =ᶠ[𝓝 (((L.one, L.one), ((0 : E), y)))] dMB L.mul ∘ SS :=
    eventuallyEq_of_mem ((L.isOpen_dom.prod isOpen_univ).mem_nhds ⟨L.one_one_mem, mem_univ _⟩)
      fun q hq ↦ hd q hq
  have key : dMB (dMB L.mul) (((L.one, L.one), ((0 : E), y)), ((x, (0 : E)), (0 : E × E))) =
      dMB (dMB L.mul) (((L.one, L.one), ((0 : E), x)), ((y, (0 : E)), (0 : E × E))) := by
    rw [dMB_congr_of_eventuallyEq hev, dMB_comp_linearMap]
    simp only [SS, LinearMap.prodMap_apply, hS, Prod.swap_prod_mk]
    exact (L.smooth 2).dMB_dMB_symm L.isOpen_dom L.one_one_mem _ _
  rw [bracket_eq, dMB_xl, dMB_xl, key, sub_self]

end LocalGroupLaw

end LocallyConvex.LieGroups
