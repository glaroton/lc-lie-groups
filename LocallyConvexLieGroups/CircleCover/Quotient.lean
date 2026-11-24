/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.CircleCover.DiffCircleRegular
public import LocallyConvexLieGroups.CircleCover.Exponential
public import LocallyConvexLieGroups.LieGroup.Quotient

/-!
# `Diff⁺(S¹) = \widetilde{Diff}⁺(S¹)/ℤ`

The covering morphism `q : \widetilde{Diff}⁺(S¹) → Diff(S¹)` (`CircleCover.coverHom`) sends
`id + a` to the diffeomorphism `e^{2πit} ↦ e^{2πi(t + a(t))}` of the circle. Its kernel consists
of the `a` with `a(t) ∈ ℤ` for all `t`, that is, by continuity, of the constant functions `n ∈ ℤ`:
the translations `x ↦ x + n` of `ℝ`. They form a central subgroup isomorphic to `ℤ`
(`CircleCover.kerEquivInt`).

The image of `q` is the identity component `Diff⁺(S¹)`. It is contained in it because
`\widetilde{Diff}⁺(S¹) = Ω` is convex, hence connected; it contains it because, by the local right
inverse `ρ` of `DiffCircleRegular.lean`, it contains a neighbourhood of the identity, so it is an
open subgroup. Hence `q` induces an isomorphism of groups `\widetilde{Diff}⁺(S¹)/ℤ ≅ Diff⁺(S¹)`,
which is also a homeomorphism for the quotient topology, since `q` is an open map
(`CircleCover.quotientEquiv`; [GN26, §13.3]).

The kernel is discrete, so `\widetilde{Diff}⁺(S¹)/ℤ` is a Lie group
(`MBLieGroup.instMBLieGroupQuotient`), and the isomorphism is an isomorphism of Lie groups: it is
smooth because `q` is, and its inverse is smooth because `q` has the smooth local section
`g ↦ ρ(φ(g))` near the identity (`MBLieGroup.smoothMBM_symm_of_local`).

## Main definitions

* `CircleCover.intConst`: the constant function `n`, as an element of `\widetilde{Diff}⁺(S¹)`.
* `CircleCover.intHom`: the morphism `ℤ → \widetilde{Diff}⁺(S¹)`, `n ↦ (x ↦ x + n)`.
* `CircleCover.kerEquivInt`: **`ker q ≅ ℤ`**.
* `CircleCover.quotientMulEquiv`, `CircleCover.quotientEquiv`:
  **`\widetilde{Diff}⁺(S¹)/ker q ≅ Diff⁺(S¹)`**, as groups and as topological groups.

## Main results

* `CircleCover.coverHom_eq_iff`: `q(a) = q(b)` if and only if `b - a` is a constant integer.
* `CircleCover.ker_coverHom`: `ker q = ℤ`.
* `CircleCover.ker_coverHom_le_center`: the kernel is central.
* `CircleCover.range_coverHom`: **the image of `q` is `Diff⁺(S¹)`**.
* `CircleCover.isOpenMap_coverHom`: `q` is an open map.
* `CircleCover.isHom_quotientMulEquiv`, `CircleCover.isHom_quotientMulEquiv_symm`:
  **`\widetilde{Diff}⁺(S¹)/ℤ ≅ Diff⁺(S¹)` as Lie groups**.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology ContDiff Real
open LocallyConvex.Analysis LocallyConvex.Manifolds CInfPer DiffCircle

noncomputable section

namespace LocallyConvex.LieGroups.CircleCover

/-! ### The kernel -/

/-- `e^{2πis} = e^{2πit}` if and only if `s - t ∈ ℤ`. -/
theorem circ_eq_circ_iff (s t : ℝ) : circ s = circ t ↔ ∃ n : ℤ, s = t + n := by
  have hE : ∀ x : ℝ, expC x = 1 ↔ ∃ n : ℤ, x = n := fun x ↦ by
    rw [expC, Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have h2 : ((2 * π * x : ℝ) : ℂ) * Complex.I = ((n * (2 * π) : ℝ) : ℂ) * Complex.I := by
        rw [hn]; push_cast; ring
      have h3 := Complex.ofReal_injective (mul_right_cancel₀ Complex.I_ne_zero h2)
      have hπ : (2 * π) ≠ 0 := by positivity
      exact mul_left_cancel₀ hπ (h3.trans (mul_comm _ _))
    · rintro ⟨n, rfl⟩
      exact ⟨n, by push_cast; ring⟩
  constructor
  · intro h
    have h1 : J.symm (expC s) = J.symm (expC t) := congrArg Subtype.val h
    have h2 : expC s = expC t := J.symm.injective h1
    obtain ⟨n, hn⟩ := (hE (s - t)).1 (by
      have : expC (s - t) * expC t = expC t * 1 := by rw [← expC_add, sub_add_cancel, h2, mul_one]
      have ht : expC t ≠ 0 := by rw [expC]; exact Complex.exp_ne_zero _
      rw [mul_comm] at this
      exact mul_left_cancel₀ ht this)
    exact ⟨n, by linarith⟩
  · rintro ⟨n, rfl⟩
    refine Subtype.ext ?_
    change J.symm (expC (t + n)) = J.symm (expC t)
    rw [expC_add, (hE n).2 ⟨n, rfl⟩, mul_one]

/-- The constant function `n`. -/
def intPer (n : ℤ) : CInfPer := CInfPer.mk (fun _ ↦ n) contDiff_const fun _ ↦ rfl

@[simp] theorem intPer_apply (n : ℤ) (x : ℝ) : intPer n x = n := rfl

theorem intPer_mem (n : ℤ) : intPer n ∈ domain := fun x ↦ by
  have h : deriv (intPer n) x = 0 := by
    change deriv (fun _ : ℝ ↦ (n : ℝ)) x = 0
    exact deriv_const x _
  rw [h, add_zero]
  exact one_pos

/-- **The translation `x ↦ x + n`** of `ℝ`, as an element of `\widetilde{Diff}⁺(S¹)`. -/
def intConst (n : ℤ) : CoverGroup := ⟨intPer n, intPer_mem n⟩

@[simp] theorem coe_intConst (n : ℤ) : ((intConst n : CoverGroup) : CInfPer) = intPer n := rfl

/-- `n ↦ (x ↦ x + n)`, a morphism `ℤ → \widetilde{Diff}⁺(S¹)`. -/
def intHom : Multiplicative ℤ →* CoverGroup where
  toFun n := intConst n.toAdd
  map_one' := Subtype.ext (by
    ext x
    change (((0 : ℤ)) : ℝ) = 0
    simp)
  map_mul' m n := Subtype.ext (by
    ext x
    change ((m.toAdd + n.toAdd : ℤ) : ℝ) =
      intPer n.toAdd x + intPer m.toAdd (lift (intPer n.toAdd) x)
    simp only [intPer_apply]
    push_cast
    ring)

theorem intHom_apply (n : Multiplicative ℤ) : intHom n = intConst n.toAdd := rfl

theorem injective_intHom : Injective intHom := fun m n h ↦ by
  have h1 := congrArg (fun a : CoverGroup ↦ (a : CInfPer) 0) h
  simp only [intHom_apply, coe_intConst, intPer_apply, Int.cast_inj] at h1
  exact Multiplicative.toAdd.injective h1

/-- A continuous function with integer values is constant. -/
theorem exists_int_of_forall_int {f : ℝ → ℝ} (hf : Continuous f) (h : ∀ x, ∃ n : ℤ, f x = n) :
    ∃ n : ℤ, ∀ x, f x = n := by
  have hT : IsDiscrete (range ((↑) : ℤ → ℝ)) := by
    rw [isDiscrete_iff_discreteTopology]
    exact Real.isClosedEmbedding_intCast.isEmbedding.toHomeomorph.discreteTopology
  obtain ⟨n, hn⟩ := h 0
  refine ⟨n, fun x ↦ ?_⟩
  rw [← hn]
  exact isPreconnected_univ.constant_of_mapsTo hT hf.continuousOn
    (fun y _ ↦ (h y).imp fun m hm ↦ hm.symm) (mem_univ _) (mem_univ _)

theorem coverHom_eq_one_iff (a : CoverGroup) :
    coverHom a = 1 ↔ ∀ x, ∃ n : ℤ, (a : CInfPer) x = n := by
  constructor
  · intro h x
    have h1 : act (a, circ x) = circ x := by
      have := congrArg (fun g : DiffCircle ↦
        (show diffeos CircleModel UnitCircle from g).1 (circ x)) h
      exact this
    rw [act_circ, circ_eq_circ_iff] at h1
    obtain ⟨n, hn⟩ := h1
    exact ⟨n, by rw [lift] at hn; linarith⟩
  · intro h
    refine Subtype.ext (SmoothMap.ext fun p ↦ ?_)
    change act (a, p) = p
    rw [← circ_ang p, act_circ, circ_eq_circ_iff]
    obtain ⟨n, hn⟩ := h (ang (J p.1))
    exact ⟨n, by rw [lift, hn]⟩

/-- **The kernel of the covering morphism is `ℤ`**: the translations by integers. -/
theorem ker_coverHom : coverHom.ker = intHom.range := by
  ext a
  rw [MonoidHom.mem_ker, coverHom_eq_one_iff, MonoidHom.mem_range]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := exists_int_of_forall_int (a : CInfPer).contDiff.continuous h
    refine ⟨Multiplicative.ofAdd n, Subtype.ext ?_⟩
    ext x
    rw [intHom_apply, coe_intConst, intPer_apply, hn x]
    rfl
  · rintro ⟨n, rfl⟩ x
    exact ⟨n.toAdd, rfl⟩

/-- **`ker q ≅ ℤ`.** -/
def kerEquivInt : coverHom.ker ≃* Multiplicative ℤ :=
  (MulEquiv.subgroupCongr ker_coverHom).trans (MonoidHom.ofInjective injective_intHom).symm

theorem coe_mul_intConst (a : CoverGroup) (n : ℤ) :
    ((a * intConst n : CoverGroup) : CInfPer) = a + intPer n := by
  ext x
  change intPer n x + (a : CInfPer) (lift (intPer n) x) = (a : CInfPer) x + intPer n x
  simp only [intPer_apply, lift]
  rw [show x + (n : ℝ) = x + n * 1 by ring, (a : CInfPer).periodic.int_mul n x]
  ring

theorem coe_intConst_mul (n : ℤ) (a : CoverGroup) :
    ((intConst n * a : CoverGroup) : CInfPer) = a + intPer n := by
  ext x
  change (a : CInfPer) x + intPer n (lift a x) = (a : CInfPer) x + intPer n x
  simp only [intPer_apply]

theorem intConst_mul (n : ℤ) (a : CoverGroup) : intConst n * a = a * intConst n :=
  Subtype.ext (by rw [coe_intConst_mul, coe_mul_intConst])

/-- **The kernel is central.** -/
theorem ker_coverHom_le_center : coverHom.ker ≤ Subgroup.center CoverGroup := by
  rw [ker_coverHom]
  rintro _ ⟨n, rfl⟩
  exact Subgroup.mem_center_iff.2 fun a ↦ (intConst_mul n.toAdd a).symm

theorem coverHom_intConst (n : ℤ) : coverHom (intConst n) = 1 := by
  rw [← MonoidHom.mem_ker, ker_coverHom]
  exact ⟨Multiplicative.ofAdd n, rfl⟩

/-- **`q(a) = q(b)` if and only if `b - a` is a constant integer.** -/
theorem coverHom_eq_iff (a b : CoverGroup) :
    coverHom a = coverHom b ↔ ∃ n : ℤ, (b : CInfPer) = a + intPer n := by
  constructor
  · intro h
    have hk : a⁻¹ * b ∈ coverHom.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    rw [ker_coverHom] at hk
    obtain ⟨n, hn⟩ := hk
    refine ⟨n.toAdd, ?_⟩
    rw [← coe_mul_intConst, ← intHom_apply, hn, mul_inv_cancel_left]
  · rintro ⟨n, hn⟩
    have hb : b = a * intConst n := Subtype.ext (by rw [hn, coe_mul_intConst])
    rw [hb, map_mul, coverHom_intConst, mul_one]

/-! ### The image -/

instance : IsTopologicalGroup CoverGroup := MBLieGroup.isTopologicalGroup CInfPer CoverGroup

instance : IsTopologicalGroup DiffCircle :=
  MBLieGroup.isTopologicalGroup (DiffeoModel UnitCircle.localAddition) DiffCircle

theorem continuous_coverHom : Continuous (coverHom : CoverGroup → DiffCircle) :=
  continuousOn_univ.1 (isHom_coverHom 0).1

instance : ConnectedSpace CoverGroup :=
  isConnected_iff_connectedSpace.1 ⟨⟨0, zero_mem⟩, convex_domain.isPreconnected⟩

/-- The image of `q` lies in the identity component, since `\widetilde{Diff}⁺(S¹)` is connected. -/
theorem range_coverHom_le : coverHom.range ≤ DiffPlusCircle.toSubgroup := by
  rintro _ ⟨a, rfl⟩
  change coverHom a ∈ connectedComponent (1 : DiffCircle)
  exact (isPreconnected_range continuous_coverHom).subset_connectedComponent ⟨1, map_one _⟩
    ⟨a, rfl⟩

/-- The chart of `Diff(S¹)` at the identity, as a chart of the Lie group. -/
abbrev c1 : OpenPartialHomeomorph DiffCircle Mod :=
  chartAt (DiffeoModel UnitCircle.localAddition) (1 : DiffCircle)

/-- The domain of the local right inverse `ρ`. -/
def Wρ : Set Mod := φ1.target ∩ rho ⁻¹' domain

theorem isOpen_Wρ : IsOpen Wρ :=
  (smoothMBOn_rho 0).continuousOn.isOpen_inter_preimage φ1.open_target isOpen_domain

theorem c1_one_mem_Wρ : c1 1 ∈ Wρ := by
  rw [chartAt_diffCircle_apply]
  refine ⟨one_mem_target, ?_⟩
  change rho (φ1 1) ∈ domain
  rw [rho_one]
  exact zero_mem

theorem coverHom_rho_mem_source {y : Mod} (hy : y ∈ Wρ) :
    coverHom ⟨rho y, hy.2⟩ ∈ c1.source ∧ c1 (coverHom ⟨rho y, hy.2⟩) = y := by
  refine ⟨⟨mem_univ _, ?_⟩, ?_⟩
  · change (1 : DiffCircle)⁻¹ * coverHom ⟨rho y, hy.2⟩ ∈ φ1.source
    rw [inv_one, one_mul]
    change (show diffeos CircleModel UnitCircle from coverHom ⟨rho y, hy.2⟩) ∈ φ1.source
    rw [coverHom_rho hy.1 hy.2]
    exact φ1.map_target hy.1
  · rw [chartAt_diffCircle_apply]
    change φ1 (show diffeos CircleModel UnitCircle from coverHom ⟨rho y, hy.2⟩) = y
    rw [coverHom_rho hy.1 hy.2]
    exact φ1.right_inv hy.1

/-- The neighbourhood of the identity of `Diff(S¹)` on which `ρ` is a section of `q`. -/
def N1 : Set DiffCircle := c1.source ∩ c1 ⁻¹' Wρ

theorem N1_mem_nhds : N1 ∈ 𝓝 (1 : DiffCircle) :=
  (c1.isOpen_inter_preimage isOpen_Wρ).mem_nhds
    ⟨mem_chart_source _ (1 : DiffCircle), c1_one_mem_Wρ⟩

/-- **The local section** `g ↦ ρ(φ(g))` of `q`, near the identity. -/
def sec (g : DiffCircle) : CoverGroup := (chartAt CInfPer (1 : CoverGroup)).symm (rho (c1 g))

theorem coverHom_sec {g : DiffCircle} (hg : g ∈ N1) : coverHom (sec g) = g := by
  have hs : sec g = ⟨rho (c1 g), hg.2.2⟩ := chartAt_coverGroup_symm hg.2.2
  obtain ⟨h1, h2⟩ := coverHom_rho_mem_source hg.2
  rw [hs]
  exact c1.injOn h1 hg.1 h2

theorem sec_one : sec 1 = 1 := by
  have h : rho (c1 1) = 0 := by
    rw [chartAt_diffCircle_apply]
    exact rho_one
  rw [sec, h]
  exact chartAt_coverGroup_symm zero_mem

theorem continuousAt_sec : ContinuousAt sec 1 := by
  have h1 : c1 1 ∈ φ1.target := c1_one_mem_Wρ.1
  have hr : ContinuousAt rho (c1 1) :=
    (smoothMBOn_rho 0).continuousOn.continuousAt (φ1.open_target.mem_nhds h1)
  have h0 : rho (c1 1) ∈ (chartAt CInfPer (1 : CoverGroup)).target :=
    mem_chart_target CInfPer (⟨rho (c1 1), c1_one_mem_Wρ.2⟩ : CoverGroup)
  have hrc : ContinuousAt (rho ∘ c1) 1 := hr.comp (c1.continuousAt (mem_chart_source _ _))
  exact ContinuousAt.comp (g := (chartAt CInfPer (1 : CoverGroup)).symm) (f := rho ∘ c1)
    ((chartAt CInfPer (1 : CoverGroup)).continuousAt_symm h0) hrc

/-- **The image of `q` is a neighbourhood of the identity.** -/
theorem range_coverHom_mem_nhds : (coverHom.range : Set DiffCircle) ∈ 𝓝 (1 : DiffCircle) :=
  Filter.mem_of_superset N1_mem_nhds fun g hg ↦ ⟨sec g, coverHom_sec hg⟩

/-- **The image of the covering morphism is `Diff⁺(S¹)`.** -/
theorem range_coverHom : coverHom.range = DiffPlusCircle.toSubgroup := by
  refine le_antisymm range_coverHom_le ?_
  have ho : IsOpen (coverHom.range : Set DiffCircle) :=
    Subgroup.isOpen_of_mem_nhds _ range_coverHom_mem_nhds
  have hc : IsClosed (coverHom.range : Set DiffCircle) :=
    (⟨coverHom.range, ho⟩ : OpenSubgroup DiffCircle).isClosed
  intro g hg
  exact IsClopen.connectedComponent_subset ⟨hc, ho⟩ (one_mem _) (by exact hg)

/-- **The covering morphism is an open map.** -/
theorem isOpenMap_coverHom : IsOpenMap (coverHom : CoverGroup → DiffCircle) := by
  refine isOpenMap_iff_nhds_le.2 fun a U hU ↦ ?_
  rw [Filter.mem_map] at hU
  set f : DiffCircle → CoverGroup := fun g ↦ a * sec ((coverHom a)⁻¹ * g)
  have hl : ContinuousAt (fun g : DiffCircle ↦ (coverHom a)⁻¹ * g) (coverHom a) :=
    (continuous_const.mul continuous_id).continuousAt
  have hs : ContinuousAt sec ((coverHom a)⁻¹ * coverHom a) := by
    rw [inv_mul_cancel]; exact continuousAt_sec
  have hf : ContinuousAt f (coverHom a) :=
    (continuous_const.mul continuous_id).continuousAt.comp (hs.comp hl)
  have hfa : f (coverHom a) = a := by
    simp only [f, inv_mul_cancel, sec_one, mul_one]
  have hU' : coverHom ⁻¹' U ∈ 𝓝 (f (coverHom a)) := by
    rw [hfa]; exact hU
  have hN : (fun g : DiffCircle ↦ (coverHom a)⁻¹ * g) ⁻¹' N1 ∈ 𝓝 (coverHom a) :=
    hl.preimage_mem_nhds (by rw [inv_mul_cancel]; exact N1_mem_nhds)
  filter_upwards [hf.preimage_mem_nhds hU', hN] with g hg1 hg2
  have hfg : coverHom (f g) = g := by
    simp only [f, map_mul, coverHom_sec hg2, mul_inv_cancel_left]
  rw [← hfg]
  exact hg1

/-! ### The quotient -/

/-- `q` as a surjective morphism onto `Diff⁺(S¹)`. -/
def coverHomPlus : CoverGroup →* DiffPlusCircle :=
  coverHom.codRestrict DiffPlusCircle.toSubgroup fun a ↦ range_coverHom_le ⟨a, rfl⟩

theorem coe_coverHomPlus (a : CoverGroup) : (coverHomPlus a : DiffCircle) = coverHom a := rfl

theorem surjective_coverHomPlus : Surjective coverHomPlus := fun g ↦ by
  obtain ⟨a, ha⟩ := (range_coverHom ▸ g.2 : (g : DiffCircle) ∈ coverHom.range)
  exact ⟨a, Subtype.ext ha⟩

theorem ker_coverHomPlus : coverHomPlus.ker = coverHom.ker :=
  MonoidHom.ker_codRestrict _ _ _

theorem continuous_coverHomPlus : Continuous coverHomPlus :=
  continuous_coverHom.subtype_mk _

theorem isOpenMap_coverHomPlus : IsOpenMap coverHomPlus :=
  (DiffPlusCircle.isOpen.isOpenEmbedding_subtypeVal.isOpenMap_iff).2 isOpenMap_coverHom

/-- **`\widetilde{Diff}⁺(S¹)/ℤ ≅ Diff⁺(S¹)`** as groups. -/
def quotientMulEquiv : CoverGroup ⧸ coverHom.ker ≃* DiffPlusCircle :=
  (QuotientGroup.quotientMulEquivOfEq ker_coverHomPlus.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective coverHomPlus surjective_coverHomPlus)

theorem quotientMulEquiv_mk (a : CoverGroup) :
    quotientMulEquiv (a : CoverGroup ⧸ coverHom.ker) = coverHomPlus a := rfl

theorem continuous_quotientMulEquiv : Continuous quotientMulEquiv :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 continuous_coverHomPlus

theorem isOpenMap_quotientMulEquiv : IsOpenMap quotientMulEquiv :=
  (QuotientGroup.isOpenQuotientMap_mk.isOpenMap_iff).2 isOpenMap_coverHomPlus

/-- **`Diff⁺(S¹) = \widetilde{Diff}⁺(S¹)/ℤ`** ([GN26, §13.3]): the covering morphism induces an
isomorphism of topological groups `\widetilde{Diff}⁺(S¹)/ker q ≅ Diff⁺(S¹)`, and `ker q ≅ ℤ`
(`kerEquivInt`). -/
def quotientEquiv : CoverGroup ⧸ coverHom.ker ≃ₜ* DiffPlusCircle where
  toMulEquiv := quotientMulEquiv
  continuous_toFun := continuous_quotientMulEquiv
  continuous_invFun :=
    (quotientMulEquiv.toEquiv.toHomeomorphOfContinuousOpen continuous_quotientMulEquiv
      isOpenMap_quotientMulEquiv).symm.continuous

/-! ### `Diff⁺(S¹) ≅ \widetilde{Diff}⁺(S¹)/ℤ` as Lie groups -/

/-- **The kernel of `q` is discrete**: `|a(0)| < 1/2` only for `a = 0` in the kernel. -/
instance : DiscreteTopology coverHom.ker := by
  rw [discreteTopology_iff_isOpen_singleton_one]
  set O : Set CoverGroup := {a | |(a : CInfPer) 0| < 1 / 2}
  have hO : IsOpen O := isOpen_lt
    (continuous_abs.comp ((evalCLM 0).continuous.comp continuous_subtype_val)) continuous_const
  refine isOpen_induced_iff.2 ⟨O, hO, ?_⟩
  ext x
  simp only [mem_preimage, mem_singleton_iff]
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := (ker_coverHom ▸ x.2 : (x : CoverGroup) ∈ intHom.range)
    have h0 : ((x : CoverGroup) : CInfPer) 0 = (n.toAdd : ℝ) := by
      rw [← hn, intHom_apply, coe_intConst, intPer_apply]
    change |((x : CoverGroup) : CInfPer) 0| < 1 / 2 at hx
    rw [h0] at hx
    have h1 : |n.toAdd| < 1 := by
      have : |(n.toAdd : ℝ)| < 1 := lt_trans hx (by norm_num)
      exact_mod_cast this
    have h2 : n.toAdd = 0 := Int.abs_lt_one_iff.1 h1
    refine Subtype.ext ?_
    rw [← hn, intHom_apply, h2]
    exact Subtype.ext (by ext; simp)
  · rintro rfl
    change |(0 : CInfPer) 0| < 1 / 2
    norm_num

/-- `q` as a smooth map into `Diff⁺(S¹)`. -/
theorem smoothMBM_coverHomPlus :
    SmoothMBM CInfPer (DiffeoModel UnitCircle.localAddition) coverHomPlus :=
  smoothMBM_of_val_comp (DiffPlusCircle : Opens DiffCircle) isHom_coverHom

/-- **The isomorphism `\widetilde{Diff}⁺(S¹)/ℤ ≅ Diff⁺(S¹)` is smooth.** -/
theorem isHom_quotientMulEquiv : MBLieGroup.IsHom CInfPer (DiffeoModel UnitCircle.localAddition)
    quotientMulEquiv.toMonoidHom :=
  MBLieGroup.smoothMBM_of_comp_mk _ smoothMBM_coverHomPlus

/-- The local section `sec` of `q` is smooth near the identity. -/
theorem smoothMBMOn_sec : SmoothMBMOn (DiffeoModel UnitCircle.localAddition) CInfPer sec N1 := by
  intro k
  have hN1 : IsOpen N1 := c1.isOpen_inter_preimage isOpen_Wρ
  have hc : ContMDiffMBOn (E := Mod) (F := Mod) k c1 N1 :=
    contMDiffMBOn_mono (contMDiffMBOn_chart (chart_mem_atlas _ (1 : DiffCircle)))
      inter_subset_left
  have hr : ContMDiffMBOn (E := Mod) (F := CInfPer) k rho φ1.target :=
    (contMDiffMBOn_iff_contDiffMBOn φ1.open_target).2 (smoothMBOn_rho k)
  have hrc := ContMDiffMBOn.comp (g := rho) (f := c1) hN1 φ1.open_target hr hc
    fun g hg ↦ hg.2.1
  have hs : ContMDiffMBOn (E := CInfPer) (F := CInfPer) k
      (chartAt CInfPer (1 : CoverGroup)).symm (chartAt CInfPer (1 : CoverGroup)).target :=
    contMDiffMBOn_chart_symm (chart_mem_atlas CInfPer (1 : CoverGroup))
  exact ContMDiffMBOn.comp (g := (chartAt CInfPer (1 : CoverGroup)).symm) (f := rho ∘ c1) hN1
    (chartAt CInfPer (1 : CoverGroup)).open_target hs hrc fun g hg ↦
      mem_chart_target CInfPer (⟨rho (c1 g), hg.2.2⟩ : CoverGroup)

/-- **The inverse isomorphism `Diff⁺(S¹) → \widetilde{Diff}⁺(S¹)/ℤ` is smooth.** -/
theorem isHom_quotientMulEquiv_symm :
    MBLieGroup.IsHom (DiffeoModel UnitCircle.localAddition) CInfPer
      quotientMulEquiv.symm.toMonoidHom := by
  set N : Set DiffPlusCircle := Subtype.val ⁻¹' N1
  have hN : IsOpen N := (c1.isOpen_inter_preimage isOpen_Wρ).preimage continuous_subtype_val
  have h1 : (1 : DiffPlusCircle) ∈ N := ⟨mem_chart_source _ (1 : DiffCircle), c1_one_mem_Wρ⟩
  refine MBLieGroup.smoothMBM_symm_of_local quotientMulEquiv hN h1
    (σ := fun g ↦ ((sec g.1 : CoverGroup) : CoverGroup ⧸ coverHom.ker)) (fun k ↦ ?_)
    fun g hg ↦ ?_
  · have hv : ContMDiffMBOn (E := Mod) (F := Mod) k (Subtype.val : DiffPlusCircle → DiffCircle)
        N := contMDiffMBOn_mono (smoothMBM_subtype_val (DiffPlusCircle : Opens DiffCircle) k)
          (subset_univ _)
    have h2 := ContMDiffMBOn.comp (g := sec) (f := Subtype.val) hN
      (c1.isOpen_inter_preimage isOpen_Wρ) (smoothMBMOn_sec k) hv fun g hg ↦ hg
    exact ContMDiffMBOn.comp (g := (QuotientGroup.mk : CoverGroup → CoverGroup ⧸ coverHom.ker))
      (f := sec ∘ Subtype.val) hN isOpen_univ (MBLieGroup.smoothMBM_mk _ k) h2 (mapsTo_univ _ _)
  · rw [MulEquiv.eq_symm_apply]
    exact Subtype.ext (coverHom_sec hg)

end LocallyConvex.LieGroups.CircleCover
