/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Regular.Basic
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.ContinuousMap.LocallyConvex

/-!
# `C⁰`-regular Lie groups

A Lie group `G` with Lie algebra `𝔤` is **`C⁰`-semiregular** if for every continuous curve
`ξ : [0, 1] → 𝔤` the initial value problem `γ(0) = 1`, `δ(γ) = ξ` has a solution `γ_ξ`, and
**`C⁰`-regular** if moreover the evolution map `evol : C([0, 1], 𝔤) → G`, `ξ ↦ γ_ξ(1)`, is smooth
([GN26, Definition 6.1.1], `k = 0`). `C⁰`-regularity implies `C^k`-regularity for every `k`, in
particular regularity in the sense of Milnor ([GN26, Remark 6.1.2(c)]).

## Main definitions

* `MBLieGroup.extendCurve ξ`: the extension of `ξ ∈ C([0, 1], E)` to `ℝ` by constants.
* `MBLieGroup.IsEvol ξ γ`: `γ(0) = 1` and `δ(γ)(t) = ξ(t)` for all `t ∈ ℝ`.
* `MBLieGroup.IsC0Semiregular`, `MBLieGroup.evol`, `MBLieGroup.IsC0Regular`.

## Main results

* `MBLieGroup.IsEvol.unique`: solutions are unique ([GN26, Lemma 5.5.4]).
* `MBLieGroup.IsEvol.map_add`: for a constant curve `x`, `γ_x` is a one-parameter group, and
  `MBLieGroup.IsEvol.comp_mul`: `γ_{c x}(t) = γ_x(c t)`.
* `MBLieGroup.IsC0Regular.isExp`: **a `C⁰`-regular Lie group has an exponential function**,
  `exp(x) = evol(x)` for constant curves `x` ([GN26, Remark 6.1.2(a)]).

## Implementation notes

* Curves are solved on all of `ℝ`, for the extension `ξ̃` of `ξ` by the constants `ξ(0)` and
  `ξ(1)`; this avoids one-sided derivatives at the endpoints of `[0, 1]`. Since the restriction to
  `[0, 1]` of a solution on `ℝ` solves the problem of [GN26], our `C⁰`-semiregularity implies
  theirs; the converse, by continuing solutions with one-parameter groups, is
  `MBLieGroup.isC0Semiregular_iff` and `MBLieGroup.isC0Regular_iff`
  (`LocallyConvexLieGroups.Regular.Interval`).
* `C^k([0, 1], 𝔤)` for `k ≥ 1` is not yet available as a locally convex space (lc-analysis has
  `C^k(U, F)` for open `U`), so only the case `k = 0`, the strongest, is formalized.
* The logarithmic derivative is read in the chart at the identity (`MBLieGroup.HasLogDerivAt`).

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

/-! ### Curves and their evolutions -/

/-- The extension of `ξ ∈ C([0, 1], E)` to `ℝ` by the constants `ξ(0)` and `ξ(1)`. -/
def extendCurve (ξ : C(I, E)) : ℝ → E := IccExtend zero_le_one ξ

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] in
theorem continuous_extendCurve (ξ : C(I, E)) : Continuous (extendCurve ξ) :=
  ξ.continuous.Icc_extend'

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] in
@[simp] theorem extendCurve_const (x : E) : extendCurve (ContinuousMap.const I x) = fun _ ↦ x :=
  rfl

variable (E) in
/-- `γ` is the evolution of `ξ`: `γ(0) = 1` and `δ(γ)(t) = ξ(t)` for all `t`. -/
def IsEvol (ξ : ℝ → E) (γ : ℝ → G) : Prop := γ 0 = 1 ∧ ∀ t, HasLogDerivAt E γ (ξ t) t

/-- **Evolutions are unique** ([GN26, Lemma 5.5.4]). -/
theorem IsEvol.unique {ξ : ℝ → E} {γ₁ γ₂ : ℝ → G} (h₁ : IsEvol E ξ γ₁) (h₂ : IsEvol E ξ γ₂) :
    γ₁ = γ₂ :=
  eq_of_hasLogDerivAt h₁.2 h₂.2 (t₀ := 0) (h₁.1.trans h₂.1.symm)

variable (E G) in
/-- **`C⁰`-semiregularity** ([GN26, Definition 6.1.1], `k = 0`): every `ξ ∈ C([0, 1], 𝔤)` has an
evolution. -/
def IsC0Semiregular : Prop := ∀ ξ : C(I, E), ∃ γ : ℝ → G, IsEvol E (extendCurve ξ) γ

open Classical in
variable (E G) in
/-- **The evolution map** `evol(ξ) = γ_ξ(1)` (`1` if `ξ` has no evolution). -/
def evol (ξ : C(I, E)) : G :=
  if h : ∃ γ : ℝ → G, IsEvol E (extendCurve ξ) γ then h.choose 1 else 1

theorem evol_eq {ξ : C(I, E)} {γ : ℝ → G} (h : IsEvol E (extendCurve ξ) γ) :
    evol E G ξ = γ 1 := by
  have hex : ∃ γ : ℝ → G, IsEvol E (extendCurve ξ) γ := ⟨γ, h⟩
  simp only [evol, hex, ↓reduceDIte]
  rw [IsEvol.unique hex.choose_spec h]

variable (E G) in
/-- **`C⁰`-regularity** ([GN26, Definition 6.1.1], `k = 0`): `G` is `C⁰`-semiregular and the
evolution map `C([0, 1], 𝔤) → G` is smooth. -/
structure IsC0Regular : Prop where
  semiregular : IsC0Semiregular E G
  smooth : SmoothMBM C(I, E) E (evol E G)

/-! ### Constant curves -/

omit [IsTopologicalAddGroup E] [LocallyConvexSpace ℝ E] in
/-- Reparametrization of curves: `(f(c ·))'(r) = c f'(c r)`. -/
theorem hasDirDerivAt_comp_mul {f : ℝ → E} {c r : ℝ} {y : E} (h : HasDirDerivAt f (c * r) 1 y) :
    HasDirDerivAt (fun s ↦ f (c * s)) r 1 (c • y) := by
  have h' := h.smul_dir c
  rw [smul_eq_mul, mul_one] at h'
  unfold HasDirDerivAt at h' ⊢
  refine h'.congr fun t ↦ ?_
  simp only [smul_eq_mul, mul_one, mul_add, mul_comm t c]

omit [IsTopologicalAddGroup E] [LocallyConvexSpace ℝ E] [MBLieGroup E G] in
/-- **`γ_{c x}(t) = γ_x(c t)`.** -/
theorem IsEvol.comp_mul {x : E} {γ : ℝ → G} (h : IsEvol E (fun _ ↦ x) γ) (c : ℝ) :
    IsEvol E (fun _ ↦ c • x) (fun r ↦ γ (c * r)) := by
  refine ⟨by change γ (c * 0) = 1; rw [mul_zero]; exact h.1, fun r ↦ ⟨?_, ?_⟩⟩
  · exact ContinuousAt.comp (g := γ) (f := fun s ↦ c * s) (h.2 (c * r)).1 (by fun_prop)
  · exact hasDirDerivAt_comp_mul (f := fun s ↦ chartAt E (1 : G) ((γ (c * r))⁻¹ * γ s))
      (h.2 (c * r)).2

/-- **For a constant curve `x`, `γ_x` is a one-parameter group.** -/
theorem IsEvol.map_add {x : E} {γ : ℝ → G} (h : IsEvol E (fun _ ↦ x) γ) (s t : ℝ) :
    γ (s + t) = γ s * γ t := by
  have := isTopologicalGroup E G
  have key : ∀ a : ℝ, (fun r ↦ γ (r + a)) = fun r ↦ γ a * γ r := by
    intro a
    refine eq_of_hasLogDerivAt (ξ := fun _ ↦ x) (fun r ↦ (h.2 (r + a)).comp_add_const a)
      (fun r ↦ (h.2 r).mul_left (γ a)) (t₀ := 0) ?_
    simp [h.1]
  have := congrFun (key s) t
  rw [add_comm t s] at this
  exact this

theorem evol_const_smul {x : E} {γ : ℝ → G} (h : IsEvol E (fun _ ↦ x) γ) (c : ℝ) :
    evol E G (ContinuousMap.const I (c • x)) = γ c := by
  rw [evol_eq (γ := fun r ↦ γ (c * r)) (by rw [extendCurve_const]; exact h.comp_mul c), mul_one]

/-! ### The exponential function of a `C⁰`-regular Lie group -/

theorem smoothMBM_const : SmoothMBM E C(I, E) (ContinuousMap.const I : E → C(I, E)) := by
  set A : E →L[ℝ] C(I, E) :=
    { toFun := ContinuousMap.const I
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      cont := ContinuousMap.continuous_const' }
  intro k
  exact (contMDiffMBOn_iff_contDiffMBOn isOpen_univ).2 (A.contDiffMBOn k univ)

/-- **A `C⁰`-regular Lie group has an exponential function** ([GN26, Remark 6.1.2(a)]):
`exp(x) = γ_x(1)`, the evolution of the constant curve `x`. -/
theorem IsC0Regular.isExp (h : IsC0Regular E G) :
    IsExp E (fun x : E ↦ evol E G (ContinuousMap.const I x)) where
  smooth := h.smooth.comp smoothMBM_const
  map_add_smul x s t := by
    obtain ⟨γ, hγ⟩ := h.semiregular (ContinuousMap.const I x)
    rw [extendCurve_const] at hγ
    simp only [evol_const_smul hγ]
    exact hγ.map_add s t
  dMB_chart x := by
    obtain ⟨γ, hγ⟩ := h.semiregular (ContinuousMap.const I x)
    rw [extendCurve_const] at hγ
    have hd := (hγ.2 0).2
    simp only [hγ.1, inv_one, one_mul] at hd
    refine HasDirDerivAt.dMB_eq ?_
    unfold HasDirDerivAt at hd ⊢
    refine hd.congr fun t ↦ ?_
    have h0 : evol E G (ContinuousMap.const I (0 : E)) = 1 := by
      rw [← zero_smul ℝ x, evol_const_smul hγ, hγ.1]
    simp only [zero_add, smul_eq_mul, mul_one, evol_const_smul hγ, h0, hγ.1]

end LocallyConvex.LieGroups.MBLieGroup
