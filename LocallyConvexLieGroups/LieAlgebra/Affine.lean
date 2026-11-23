/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.LieAlgebra.Semidirect
public import LocallyConvexLieGroups.LieGroup.Units

/-!
# Affine groups

Let `A` be a continuous inverse algebra acting continuously on a locally convex space `E`. The
unit group `A^×` acts smoothly on the vector group `(E, +)`, and the semidirect product
`E ⋊ A^×` is a Lie group with Lie algebra `E ⋊ A`:
`[(a, X), (a', X')] = (X a' − X' a, X X' − X' X)`. For a Banach space `E` and `A = L(E)` this is
the affine group `Aff(E) ≅ E ⋊ GL(E)` with `aff(E) ≅ E ⋊ gl(E)` ([GN26, Example 5.2.9]).

## Main definitions

* `AffineGroup.action A E`: `u ↦ (v ↦ u v)`, as a homomorphism `A^× → Aut(E, +)`.
* `AffineGroup A E`: the semidirect product `E ⋊ A^×`.

## Main results

* `AffineGroup.isSmoothAction`: the action is smooth; in the charts it is `(x, v) ↦ (x + 1) v`.
* `AffineGroup.derivedAction_eq`: the derived action is `D_X a = X a`.
* `AffineGroup.bracket_eq`: **the Lie algebra of `E ⋊ A^×`** ([GN26, Example 5.2.9]).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups.AffineGroup

universe u

variable (A : Type u) [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
  [ContinuousInverseAlgebra A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
  [ContinuousSMul ℝ A] [LocallyConvexSpace ℝ A] [T2Space A]
  (E : Type u) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [Module A E] [IsScalarTower ℝ A E] [SMulCommClass A ℝ E] [ContinuousSMul A E]

/-- The action `(X, v) ↦ X v`, as a continuous bilinear map. -/
def smulBilin : A →ₗ[ℝ] E →ₗ[ℝ] E :=
  LinearMap.mk₂ ℝ (fun X v ↦ X • v) (fun _ _ _ ↦ add_smul _ _ _) (fun _ _ _ ↦ smul_assoc _ _ _)
    (fun _ _ _ ↦ smul_add _ _ _) fun _ _ _ ↦ smul_comm _ _ _

omit [IsTopologicalRing A] [ContinuousInverseAlgebra A] [IsScalarTower ℝ A A]
  [SMulCommClass ℝ A A] [ContinuousSMul ℝ A] [LocallyConvexSpace ℝ A] [T2Space A]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem continuous_smulBilin : Continuous fun p : A × E ↦ smulBilin A E p.1 p.2 :=
  continuous_smul

/-- **The action of `A^×` on `(E, +)`.** -/
def action : UnitGroup A →* MulAut (Multiplicative E) where
  toFun u := AddEquiv.toMultiplicative
    { toFun := fun v ↦ UnitGroup.val u • v
      invFun := fun v ↦ UnitGroup.val u⁻¹ • v
      left_inv := fun v ↦ by
        change UnitGroup.val u⁻¹ • UnitGroup.val u • v = v
        rw [smul_smul, ← UnitGroup.val_mul, inv_mul_cancel, UnitGroup.val_one, one_smul]
      right_inv := fun v ↦ by
        change UnitGroup.val u • UnitGroup.val u⁻¹ • v = v
        rw [smul_smul, ← UnitGroup.val_mul, mul_inv_cancel, UnitGroup.val_one, one_smul]
      map_add' := fun _ _ ↦ smul_add _ _ _ }
  map_one' := by
    ext v
    change Multiplicative.ofAdd (UnitGroup.val (1 : UnitGroup A) • v.toAdd) = v
    rw [UnitGroup.val_one, one_smul]; rfl
  map_mul' u w := by
    refine MulEquiv.ext fun v ↦ ?_
    change Multiplicative.ofAdd (UnitGroup.val (u * w) • v.toAdd) =
      Multiplicative.ofAdd (UnitGroup.val u • UnitGroup.val w • v.toAdd)
    rw [UnitGroup.val_mul, mul_smul]

omit [TopologicalSpace A] [IsTopologicalRing A] [ContinuousInverseAlgebra A] [Module ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [ContinuousSMul ℝ A] [LocallyConvexSpace ℝ A]
  [T2Space A] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [IsScalarTower ℝ A E] [SMulCommClass A ℝ E]
  [ContinuousSMul A E] in
theorem action_apply (u : UnitGroup A) (v : E) :
    (action A E u (Multiplicative.ofAdd v)).toAdd = UnitGroup.val u • v := by
  unfold action
  rfl

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] in
/-- **The action is smooth**: in the charts it is `(x, v) ↦ (x + 1) v`. -/
theorem isSmoothAction : SDProd.IsSmoothAction A E (action A E) := by
  have hc : Continuous fun q : UnitGroup A × Multiplicative E ↦ action A E q.1 q.2 :=
    continuous_ofAdd.comp ((continuous_smulBilin A E).comp
      (((UnitGroup.isOpenEmbedding_val A).continuous.comp continuous_fst).prodMk
        (continuous_toAdd.comp continuous_snd)))
  intro k
  refine ⟨hc.continuousOn, fun x _ ↦ ?_⟩
  have hs : ContDiffMBOn k (fun q : A × E ↦ smulBilin A E q.1 q.2 + q.2) univ :=
    (contDiffMBOn_bilin (smulBilin A E) (continuous_smulBilin A E) k).add isOpen_univ
      ((ContinuousLinearMap.snd ℝ A E).contDiffMBOn k univ)
  refine ContDiffMBOn.congr_of_isOpen (isOpen_chartDomain isOpen_univ hc.continuousOn _ _)
    (fun q hq ↦ ?_) (hs.mono (subset_univ _))
  obtain ⟨⟨hq1, -⟩, -⟩ := hq
  change smulBilin A E q.1 q.2 + q.2 = UnitGroup.val ((chartAt A x.1).symm q.1) • q.2
  rw [UnitGroup.val_chartAt_symm _ hq1, add_smul, one_smul]
  rfl

/-- **The affine group** `E ⋊ A^×`. -/
abbrev _root_.LocallyConvex.LieGroups.AffineGroup : Type u := SDProd (action A E)

instance : MBLieGroup (ModelProd E A) (AffineGroup A E) :=
  SDProd.mbLieGroup (isSmoothAction A E)

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [ContinuousSMul ℝ A] [LocallyConvexSpace ℝ A]
  [T2Space A] [ContinuousSMul A E] in
/-- In the charts, `w_a(y) = φ⁻¹(y) a`. -/
theorem derivAct_eq (a : E) (y : A) :
    LocalGroupLaw.derivAct (MBLieGroup.localGroupLaw E (Multiplicative E))
      (SDProd.actRep A E (action A E)) a y =
      UnitGroup.val ((chartAt A (1 : UnitGroup A)).symm y) • a := by
  set c := UnitGroup.val ((chartAt A (1 : UnitGroup A)).symm y)
  unfold LocalGroupLaw.derivAct
  rw [dMB_slice₂]
  have h : (fun x ↦ SDProd.actRep A E (action A E) (y, x)) =
      fun x ↦ smulBilin A E c x := by
    funext x
    change Multiplicative.toAdd (action A E ((chartAt A (1 : UnitGroup A)).symm y)
      (Multiplicative.ofAdd x)) = _
    rw [action_apply]; rfl
  rw [h, ← dMB_slice₂ (fun q : A × E ↦ smulBilin A E q.1 q.2),
    (hasDirDerivAt_bilin (smulBilin A E) _ _).dMB_eq]
  change c • a + (0 : A) • _ = c • a
  rw [zero_smul, add_zero]

omit [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [LocallyConvexSpace ℝ A] [T2Space A]
  [ContinuousSMul A E] in
/-- **The derived action is `D_X a = X a`** ([GN26, Example 5.2.9]). -/
theorem derivedAction_eq (X : A) (a : E) : SDProd.derivedAction (action A E) X a = X • a := by
  set φ := chartAt A (1 : UnitGroup A)
  unfold SDProd.derivedAction
  rw [funext (derivAct_eq A E a)]
  have hev : (fun y ↦ UnitGroup.val (φ.symm y) • a) =ᶠ[𝓝 (φ 1)]
      fun y ↦ smulBilin A E y a + a := by
    filter_upwards [φ.open_target.mem_nhds (φ.map_source (mem_chart_source A (1 : UnitGroup A)))]
      with y hy
    rw [UnitGroup.val_chartAt_symm _ hy, add_smul, one_smul]
    rfl
  rw [dMB_congr_of_eventuallyEq hev]
  have hd : HasDirDerivAt (fun y ↦ smulBilin A E y a) (φ 1) X (X • a) := by
    have h := hasDirDerivAt_bilin (smulBilin A E) (φ 1, a) (X, 0)
    rw [hasDirDerivAt_slice] at h
    convert h using 1
    change X • a = φ 1 • (0 : E) + X • a
    rw [smul_zero, zero_add]
  have h0 : HasDirDerivAt (fun _ : A ↦ a) (φ 1) X 0 := by
    simp only [HasDirDerivAt, sub_self, smul_zero]; exact tendsto_const_nhds
  have := (hd.add h0).dMB_eq
  rw [add_zero] at this
  exact this

/-- **The Lie algebra of the affine group** `E ⋊ A^×` is `E ⋊ A` ([GN26, Example 5.2.9]):
`[(a, X), (a', X')] = (X a' − X' a, X X' − X' X)`. -/
theorem bracket_eq (v v' : E × A) :
    (MBLieGroup.localGroupLaw (ModelProd E A) (AffineGroup A E)).bracket v v' =
      (v.2 • v'.1 - v'.2 • v.1, v.2 * v'.2 - v'.2 * v.2) := by
  rw [SDProd.bracket_eq (isSmoothAction A E), derivedAction_eq, derivedAction_eq]
  have h0 : (MBLieGroup.localGroupLaw E (Multiplicative E)).bracket v.1 v'.1 = 0 :=
    VectorGroup.lie_eq_zero E v.1 v'.1
  rw [h0, zero_add]
  congr 1
  exact UnitGroup.lie_eq (MBLieGroup.LieAlg.toModel.symm v.2)
    (MBLieGroup.LieAlg.toModel.symm v'.2)

end LocallyConvex.LieGroups.AffineGroup
