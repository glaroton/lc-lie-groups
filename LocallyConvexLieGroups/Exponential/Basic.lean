/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.LieGroup.Prod
public import LocallyConvexLieGroups.LieGroup.Vector
public import LocallyConvexLieGroups.LieGroup.Units
public import LocallyConvexLieGroups.LieGroup.OpenSubgroup
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Exponential functions of Lie groups

An **exponential function** of a Lie group `G` with Lie algebra `𝔤 = L(G)` is a smooth map
`exp : 𝔤 → G` such that, for each `x ∈ 𝔤`, `t ↦ exp(t x)` is a one-parameter group with
derivative `x` at `0` ([GN26, Definition 5.6.1]). Here `𝔤` is the model space `E`, identified with
`T_1 G` by the chart `φ` at the identity, so the last condition reads `d(φ ∘ exp)(0) x = x`
([GN26, (5.14)]).

## Main definitions

* `MBLieGroup.IsExp exp`: `exp : E → G` is an exponential function.
* `MBLieGroup.IsExp.oneParam`: the one-parameter groups `t ↦ exp(t x)`.

## Main results

* `MBLieGroup.IsExp.exp_zero`, `MBLieGroup.IsExp.exp_neg`.
* `VectorGroup.isExp`: the exponential function of a vector group is the identity
  ([GN26, Example 5.6.5]).
* `UnitGroup.isExp_exp`: for a real Banach algebra `A`, the exponential series is the exponential
  function of `A^×` ([GN26, Example 5.6.6]).
* `MBLieGroup.IsExp.prod`: products of exponential functions.
* `MBLieGroup.IsExp.mem_identityComponent`, `MBLieGroup.IsExp.identityComponent`: an exponential
  function takes values in the identity component, and is an exponential function of it.

## Implementation notes

We do not prove that a Lie group has at most one exponential function ([GN26,
Proposition 5.6.3]): this needs the uniqueness of solutions of `γ' = γ x` ([GN26, Lemma 5.5.4]),
which is not formalized here.

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

namespace MBLieGroup

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]

variable (E) in
/-- **An exponential function** of the Lie group `G` ([GN26, Definition 5.6.1]): a smooth map
`exp : 𝔤 → G` (with `𝔤 = E` through the chart `φ` at the identity) such that each
`t ↦ exp(t x)` is a one-parameter group with derivative `x` at `0`, i.e.
`d(φ ∘ exp)(0) x = x` ([GN26, (5.14)]). -/
structure IsExp (exp : E → G) : Prop where
  smooth : SmoothMBM E E exp
  map_add_smul : ∀ (x : E) (s t : ℝ), exp ((s + t) • x) = exp (s • x) * exp (t • x)
  dMB_chart : ∀ x : E, dMB (fun y ↦ chartAt E (1 : G) (exp y)) (0, x) = x

namespace IsExp

variable {exp : E → G} (h : IsExp E exp)
include h

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] in
theorem exp_zero : exp 0 = 1 := by
  have h1 := h.map_add_smul 0 0 0
  rw [smul_zero, smul_zero] at h1
  exact mul_eq_left.mp h1.symm

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] in
theorem exp_neg (x : E) : exp (-x) = (exp x)⁻¹ := by
  have h1 := h.map_add_smul x 1 (-1)
  rw [add_neg_cancel, zero_smul, one_smul, neg_one_smul, h.exp_zero] at h1
  exact (inv_eq_of_mul_eq_one_right h1.symm).symm

/-- **The one-parameter groups** `t ↦ exp(t x)` of an exponential function. -/
def oneParam (x : E) : Multiplicative ℝ →* G where
  toFun t := exp (Multiplicative.toAdd t • x)
  map_one' := by simp [h.exp_zero]
  map_mul' s t := h.map_add_smul x _ _

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] in
theorem oneParam_apply (x : E) (t : ℝ) :
    h.oneParam x (Multiplicative.ofAdd t) = exp (t • x) := rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] in
theorem continuous : Continuous exp :=
  continuousOn_univ.1 (h.smooth 0).continuousOn

omit [MBLieGroup E G] in
/-- In the chart at the identity, `exp` is smooth near `0`. -/
theorem contDiffMBOn_chart (k : ℕ) :
    ContDiffMBOn k (fun y ↦ chartAt E (1 : G) (exp y)) (exp ⁻¹' (chartAt E (1 : G)).source) := by
  have h2 := (h.smooth k).2 0 (mem_univ _)
  rw [h.exp_zero] at h2
  refine (ContDiffMBOn.congr_of_isOpen ?_ (fun y _ ↦ rfl) h2).mono fun y hy ↦ ?_
  · exact isOpen_chartDomain isOpen_univ h.continuous.continuousOn _ _
  · exact ⟨mem_univ _, mem_univ _, hy⟩

omit [IsTopologicalAddGroup E] [LocallyConvexSpace ℝ E] [T2Space E] [MBLieGroup E G] in
/-- **An exponential function takes values in the identity component.** -/
theorem mem_connectedComponent (x : E) : exp x ∈ connectedComponent (1 : G) := by
  have hc : Continuous fun t : ℝ ↦ exp (t • x) := h.continuous.comp (by fun_prop)
  have hpc : IsPreconnected (range fun t : ℝ ↦ exp (t • x)) :=
    isPreconnected_range hc
  refine hpc.subset_connectedComponent ⟨0, ?_⟩ ⟨1, ?_⟩
  · simp [h.exp_zero]
  · simp

theorem mem_identityComponent (x : E) : exp x ∈ MBLieGroup.identityComponent E G :=
  h.mem_connectedComponent x

/-- **The exponential function of the identity component.** -/
theorem toIdentityComponent :
    IsExp E (fun x : E ↦
      (⟨exp x, h.mem_identityComponent x⟩ : MBLieGroup.identityComponent E G)) where
  smooth := smoothMBM_of_val_comp
    ((MBLieGroup.identityComponent E G : OpenSubgroup G) : Opens G)
    (g := fun x : E ↦ (⟨exp x, h.mem_identityComponent x⟩ : MBLieGroup.identityComponent E G))
    h.smooth
  map_add_smul x s t := Subtype.ext (h.map_add_smul x s t)
  dMB_chart x := h.dMB_chart x

end IsExp

/-! ### Products -/

variable {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {H : Type*} [Group H] [TopologicalSpace H] [ChartedSpace F H] [MBLieGroup F H]

omit [MBLieGroup E G] [MBLieGroup F H] in
/-- **Products of exponential functions.** -/
theorem IsExp.prod {expG : E → G} {expH : F → H} (hG : IsExp E expG) (hH : IsExp F expH) :
    IsExp (ModelProd E F) (fun x : ModelProd E F ↦ (expG x.1, expH x.2)) where
  smooth k := by
    have hc : Continuous fun x : ModelProd E F ↦ (expG x.1, expH x.2) :=
      (hG.continuous.comp continuous_fst).prodMk (hH.continuous.comp continuous_snd)
    refine ⟨hc.continuousOn, fun x _ ↦ ?_⟩
    set V₁ : Set E := expG ⁻¹' (chartAt E (expG x.1)).source
    set V₂ : Set F := expH ⁻¹' (chartAt F (expH x.2)).source
    have hV₁ : IsOpen V₁ := (chartAt E _).open_source.preimage hG.continuous
    have hV₂ : IsOpen V₂ := (chartAt F _).open_source.preimage hH.continuous
    have hA : ContDiffMBOn k (fun y : E ↦ chartAt E (expG x.1) (expG y)) V₁ :=
      ((hG.smooth k).2 x.1 (mem_univ _)).mono fun y hy ↦ ⟨mem_univ _, mem_univ _, hy⟩
    have hB : ContDiffMBOn k (fun y : F ↦ chartAt F (expH x.2) (expH y)) V₂ :=
      ((hH.smooth k).2 x.2 (mem_univ _)).mono fun y hy ↦ ⟨mem_univ _, mem_univ _, hy⟩
    set W : Set (ModelProd E F) := Prod.fst ⁻¹' V₁ ∩ Prod.snd ⁻¹' V₂
    have hW : IsOpen W := (hV₁.preimage continuous_fst).inter (hV₂.preimage continuous_snd)
    have hA' : ContDiffMBOn k (fun y : ModelProd E F ↦ chartAt E (expG x.1) (expG y.1)) W :=
      ContDiffMBOn.comp (g := fun y : E ↦ chartAt E (expG x.1) (expG y))
        (f := ⇑(ContinuousLinearMap.fst ℝ E F)) hW hV₁ hA
        ((ContinuousLinearMap.fst ℝ E F).contDiffMBOn k _) fun _ hy ↦ hy.1
    have hB' : ContDiffMBOn k (fun y : ModelProd E F ↦ chartAt F (expH x.2) (expH y.2)) W :=
      ContDiffMBOn.comp (g := fun y : F ↦ chartAt F (expH x.2) (expH y))
        (f := ⇑(ContinuousLinearMap.snd ℝ E F)) hW hV₂ hB
        ((ContinuousLinearMap.snd ℝ E F).contDiffMBOn k _) fun _ hy ↦ hy.2
    refine ContDiffMBOn.congr_of_isOpen
      (isOpen_chartDomain isOpen_univ hc.continuousOn _ _) (fun _ _ ↦ rfl)
      ((hA'.prodMk hW hB').mono fun y hy ↦ ⟨hy.2.2.1, hy.2.2.2⟩)
  map_add_smul x s t := Prod.ext (hG.map_add_smul x.1 s t) (hH.map_add_smul x.2 s t)
  dMB_chart x := by
    set U : Set (ModelProd E F) :=
      Prod.fst ⁻¹' (expG ⁻¹' (chartAt E (1 : G)).source) ∩
        Prod.snd ⁻¹' (expH ⁻¹' (chartAt F (1 : H)).source)
    have hU : IsOpen U :=
      (((chartAt E (1 : G)).open_source.preimage hG.continuous).preimage continuous_fst).inter
        (((chartAt F (1 : H)).open_source.preimage hH.continuous).preimage continuous_snd)
    have e1 : expG (0 : ModelProd E F).1 = 1 := hG.exp_zero
    have e2 : expH (0 : ModelProd E F).2 = 1 := hH.exp_zero
    have h0U : (0 : ModelProd E F) ∈ U := by
      refine ⟨?_, ?_⟩
      · rw [mem_preimage, mem_preimage, e1]; exact mem_chart_source E 1
      · rw [mem_preimage, mem_preimage, e2]; exact mem_chart_source F 1
    have hf : ContDiffMBOn 1 ((fun y ↦ chartAt E (1 : G) (expG y)) ∘
        ⇑(ContinuousLinearMap.fst ℝ E F)) U :=
      ContDiffMBOn.comp hU ((chartAt E (1 : G)).open_source.preimage hG.continuous)
        (hG.contDiffMBOn_chart 1) ((ContinuousLinearMap.fst ℝ E F).contDiffMBOn 1 _)
        fun _ hy ↦ hy.1
    have hg : ContDiffMBOn 1 ((fun y ↦ chartAt F (1 : H) (expH y)) ∘
        ⇑(ContinuousLinearMap.snd ℝ E F)) U :=
      ContDiffMBOn.comp hU ((chartAt F (1 : H)).open_source.preimage hH.continuous)
        (hH.contDiffMBOn_chart 1) ((ContinuousLinearMap.snd ℝ E F).contDiffMBOn 1 _)
        fun _ hy ↦ hy.2
    have h := dMB_prodMk hf hg h0U x
    rw [dMB_comp_clm, dMB_comp_clm] at h
    simp only [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] at h
    change dMB (fun z : ModelProd E F ↦ (((fun y ↦ chartAt E (1 : G) (expG y)) ∘ Prod.fst) z,
      ((fun y ↦ chartAt F (1 : H) (expH y)) ∘ Prod.snd) z)) (0, x) = x
    exact h.trans (Prod.ext (hG.dMB_chart x.1) (hH.dMB_chart x.2))

end MBLieGroup

/-! ### Vector groups -/

namespace VectorGroup

variable (E : Type u) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

/-- **The exponential function of a vector group is the identity** ([GN26, Example 5.6.5]). -/
theorem isExp : MBLieGroup.IsExp E (fun x : E ↦ Multiplicative.ofAdd x) where
  smooth k := by
    refine ⟨continuous_ofAdd.continuousOn, fun x _ ↦ ?_⟩
    exact ContDiffMBOn.congr_of_isOpen
      (isOpen_chartDomain isOpen_univ continuous_ofAdd.continuousOn _ _) (fun _ _ ↦ rfl)
      ((smoothMBOn_id univ k).mono (subset_univ _))
  map_add_smul x s t := by rw [add_smul]; rfl
  dMB_chart x := ((ContinuousLinearMap.id ℝ E).hasDirDerivAt 0 x).dMB_eq

end VectorGroup

/-! ### Unit groups of Banach algebras -/

namespace UnitGroup

variable {A : Type u} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

open NormedSpace

omit [CompleteSpace A] in
theorem mem_eball (x : A) : x ∈ Metric.eball (0 : A) (expSeries ℝ A).radius := by
  rw [expSeries_radius_eq_top]; exact edist_lt_top _ _

theorem exp_add' {x y : A} (hxy : Commute x y) : exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_mem_ball (𝕂 := ℝ) hxy (mem_eball x) (mem_eball y)

theorem contDiff_exp (k : ℕ) : ContDiff ℝ k (exp : A → A) :=
  contDiff_iff_contDiffAt.2 fun x ↦ (analyticAt_exp_of_mem_ball (𝕂 := ℝ) x (mem_eball x)).contDiffAt

/-- `exp x` as a unit. -/
def expUnit (x : A) : UnitGroup A :=
  (⟨exp x, exp (-x), by rw [← exp_add' (Commute.neg_right (Commute.refl x)), add_neg_cancel,
      exp_zero],
    by rw [← exp_add' (Commute.neg_left (Commute.refl x)), neg_add_cancel, exp_zero]⟩ : Aˣ)

@[simp] theorem val_expUnit (x : A) : val (expUnit x) = exp x := rfl

/-- **The exponential series is the exponential function of the unit group of a real Banach
algebra** ([GN26, Example 5.6.6]). -/
theorem isExp_exp : MBLieGroup.IsExp A (expUnit (A := A)) where
  smooth k := by
    have hc : Continuous (expUnit (A := A)) :=
      (isOpenEmbedding_val A).isInducing.continuous_iff.2 (contDiff_exp 0).continuous
    refine ⟨hc.continuousOn, fun x _ ↦ ?_⟩
    have hs : ContDiffMBOn k (fun y : A ↦ exp y - 1) univ :=
      ((contDiff_exp k).contDiffOn.contDiffMBOn isOpen_univ).sub isOpen_univ
        (contDiffMBOn_const k 1 univ)
    exact ContDiffMBOn.congr_of_isOpen (isOpen_chartDomain isOpen_univ hc.continuousOn _ _)
      (fun _ _ ↦ rfl) (hs.mono (subset_univ _))
  map_add_smul x s t := by
    refine Units.ext ?_
    change exp ((s + t) • x) = exp (s • x) * exp (t • x)
    rw [add_smul]
    exact exp_add' (((Commute.refl x).smul_left s).smul_right t)
  dMB_chart x := by
    change dMB (fun y : A ↦ exp y - 1) (0, x) = x
    have h := (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A)).sub_const 1
    exact (h.hasDirDerivAt x).dMB_eq

end UnitGroup

end LocallyConvex.LieGroups
