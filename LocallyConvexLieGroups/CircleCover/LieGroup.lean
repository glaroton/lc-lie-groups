/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.CircleCover.Inverse
public import LocallyConvexLieGroups.LieGroup.OpenSubgroup

/-!
# The universal cover of `Diff⁺(S¹)` is a Lie group

[GN26, §13.3]: the universal covering group `\widetilde{Diff}⁺(S¹)` of `Diff⁺(S¹)` is the group of
diffeomorphisms `id + u` of `ℝ` with `u` periodic, identified by the global chart `id + u ↦ u`
with the open set `Ω = {u ∈ C^∞_per : 1 + u' > 0}` (lc-manifolds, `DiffCircle.Ω`; we use period
`1`). With the composition `m(u, w) = w + u ∘ (id + w)` (`CircleCover.coverLaw`) and the inversion
`η` (`CircleCover.smoothMBOn_η`), `Ω` is a Lie group modeled on the Fréchet space `C^∞_per`, and
its Lie algebra is `C^∞_per` with the bracket `[x, y] = x' y − x y'`.

## Main definitions

* `CircleCover.CoverGroup`: the group `Ω`, with the charted space structure of an open subset of
  `C^∞_per`.

## Main results

* `CircleCover.CoverGroup.instMBLieGroup`: **`\widetilde{Diff}⁺(S¹)` is a Lie group**
  ([GN26, §13.3]).
* `CircleCover.CoverGroup.lie_eq`: **its Lie algebra is `C^∞_per` with `[x, y] = x' y − x y'`**.

## Implementation notes

The group law of `Ω` in [GN26, p. 678] is printed as `m(f, g)(x) = f(g(x) + x) − x`; the
composition `(id + f) ∘ (id + g) = id + (g + f ∘ (id + g))` gives `m(f, g)(x) = g(x) + f(x + g(x))`,
which is what we use.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology
open LocallyConvex.Analysis LocallyConvex.Manifolds CInfPer DiffCircle

noncomputable section

namespace LocallyConvex.LieGroups.CircleCover

/-- **The universal cover `\widetilde{Diff}⁺(S¹)`** in its global chart: the open set
`Ω = {u ∈ C^∞_per : 1 + u' > 0}`. -/
abbrev CoverGroup : Type := DiffCircle.Ω

namespace CoverGroup

theorem lift_zero : lift 0 = id := by
  funext x; simp [lift]

theorem mem (a : CoverGroup) : (a : CInfPer) ∈ domain := a.2

instance : Group CoverGroup where
  mul a b := ⟨DiffCircle.comp a.1 b.1, comp_mem (mem a) (mem b)⟩
  one := ⟨0, zero_mem⟩
  inv a := ⟨inv (mem a), inv_mem (mem a)⟩
  mul_assoc a b c := Subtype.ext (coverLaw.mul_assoc a.1 b.1 c.1 (mem_univ _) (mem_univ _)
    (mem_univ _) (mem_univ _))
  one_mul a := Subtype.ext (coverLaw.one_mul a.1 (mem_univ _))
  mul_one a := Subtype.ext (coverLaw.mul_one a.1 (mem_univ _))
  inv_mul_cancel a := Subtype.ext (lift_injective (by
    change lift (DiffCircle.comp (inv (mem a)) a.1) = lift 0
    rw [lift_comp, lift_inv, lift_zero]
    funext x
    rw [Function.comp_apply, ← liftHomeomorph_apply (mem a), Homeomorph.symm_apply_apply]
    rfl))

@[simp] theorem coe_mul (a b : CoverGroup) :
    ((a * b : CoverGroup) : CInfPer) = DiffCircle.comp a b := rfl

@[simp] theorem coe_one : ((1 : CoverGroup) : CInfPer) = 0 := rfl

@[simp] theorem coe_inv (a : CoverGroup) : ((a⁻¹ : CoverGroup) : CInfPer) = η a := by
  change inv (mem a) = η a.1
  rw [η_of_mem (mem a)]

/-- The composition as a smooth map of manifolds `C^∞_per × C^∞_per → C^∞_per`. -/
theorem smoothMBM_comp : SmoothMBM (ModelProd CInfPer CInfPer) CInfPer
    (fun p : CInfPer × CInfPer ↦ DiffCircle.comp p.1 p.2) := by
  intro k
  refine ⟨(smoothMBOn_comp 0).continuousOn, fun x _ ↦ ?_⟩
  exact ContDiffMBOn.congr_of_isOpen
    (isOpen_chartDomain isOpen_univ (smoothMBOn_comp 0).continuousOn _ _) (fun _ _ ↦ rfl)
    ((smoothMBOn_comp k).mono (subset_univ _))

/-- **`\widetilde{Diff}⁺(S¹)` is a Lie group** ([GN26, §13.3]). -/
instance instMBLieGroup : MBLieGroup CInfPer CoverGroup where
  smoothMBM_mul := by
    have hval : SmoothMBM CInfPer CInfPer (Subtype.val : CoverGroup → CInfPer) :=
      smoothMBM_subtype_val DiffCircle.Ω
    have h : SmoothMBM (ModelProd CInfPer CInfPer) CInfPer
        (fun p : CoverGroup × CoverGroup ↦ DiffCircle.comp (p.1 : CInfPer) p.2) :=
      smoothMBM_comp.comp (fun k ↦ ContMDiffMBOn.prodMk isOpen_univ
        ((hval.comp smoothMBM_fst) k) ((hval.comp smoothMBM_snd) k))
    exact smoothMBM_of_val_comp DiffCircle.Ω (g := fun p : CoverGroup × CoverGroup ↦ p.1 * p.2) h
  smoothMBM_inv := by
    have hval : SmoothMBM CInfPer CInfPer (Subtype.val : CoverGroup → CInfPer) :=
      smoothMBM_subtype_val DiffCircle.Ω
    have hη : SmoothMBMOn CInfPer CInfPer η domain := fun k ↦
      (contMDiffMBOn_iff_contDiffMBOn isOpen_domain).2 (smoothMBOn_η k)
    have h : SmoothMBMOn CInfPer CInfPer (η ∘ (Subtype.val : CoverGroup → CInfPer)) univ :=
      hη.comp isOpen_univ isOpen_domain hval (fun a _ ↦ mem a)
    have h' : SmoothMBM CInfPer CInfPer (fun a : CoverGroup ↦ ((a⁻¹ : CoverGroup) : CInfPer)) := by
      have hf : (fun a : CoverGroup ↦ ((a⁻¹ : CoverGroup) : CInfPer)) =
          η ∘ (Subtype.val : CoverGroup → CInfPer) := funext coe_inv
      rw [hf]
      exact h
    exact smoothMBM_of_val_comp DiffCircle.Ω (g := fun a : CoverGroup ↦ a⁻¹) h'

/-! ### The Lie algebra -/

theorem localGroupLaw_one : (MBLieGroup.localGroupLaw CInfPer CoverGroup).one = 0 := rfl

theorem localGroupLaw_eqOn :
    EqOn (MBLieGroup.localGroupLaw CInfPer CoverGroup).mul coverLaw.mul
      (MBLieGroup.localGroupLaw CInfPer CoverGroup).dom := by
  rintro p ⟨⟨hp1, hp2⟩, -⟩
  set e := chartAt CInfPer (0 : CInfPer)
  have h1 : (((chartAt CInfPer (1 : CoverGroup)).symm p.1 : CoverGroup) : CInfPer) = p.1 :=
    e.subtypeRestr_symm_apply ⟨(1 : CoverGroup)⟩ hp1
  have h2 : (((chartAt CInfPer (1 : CoverGroup)).symm p.2 : CoverGroup) : CInfPer) = p.2 :=
    e.subtypeRestr_symm_apply ⟨(1 : CoverGroup)⟩ hp2
  change (((chartAt CInfPer (1 : CoverGroup)).symm p.1 *
    (chartAt CInfPer (1 : CoverGroup)).symm p.2 : CoverGroup) : CInfPer) = DiffCircle.comp p.1 p.2
  rw [coe_mul, h1, h2]

/-- **The Lie algebra of `\widetilde{Diff}⁺(S¹)`** is `C^∞_per` with the bracket
`[x, y] = x' y − x y'`, the opposite of the bracket of the vector fields `x ∂_θ`, `y ∂_θ`. -/
theorem lie_eq (x y : MBLieGroup.LieAlg CInfPer CoverGroup) :
    MBLieGroup.LieAlg.toModel ⁅x, y⁆ =
      mul (D (MBLieGroup.LieAlg.toModel x)) (MBLieGroup.LieAlg.toModel y) -
        mul (D (MBLieGroup.LieAlg.toModel y)) (MBLieGroup.LieAlg.toModel x) := by
  rw [← coverLaw_bracket]
  exact LocalGroupLaw.bracket_congr (MBLieGroup.localGroupLaw CInfPer CoverGroup) coverLaw
    localGroupLaw_one (MBLieGroup.localGroupLaw CInfPer CoverGroup).isOpen_dom
    (MBLieGroup.localGroupLaw CInfPer CoverGroup).one_one_mem localGroupLaw_eqOn _ _

end CoverGroup

end LocallyConvex.LieGroups.CircleCover
