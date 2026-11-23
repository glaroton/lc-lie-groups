/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.LieAlgebra.Morphisms
public import LocallyConvexLieGroups.LieGroup.Units

/-!
# The adjoint representation

For `g ∈ G` the conjugation `c_g(x) = g x g⁻¹` is a smooth automorphism, and
`Ad(g) = L(c_g) : L(G) → L(G)` is a Lie algebra automorphism; `Ad(g₁ g₂) = Ad(g₁) Ad(g₂)` by the
functoriality of `L` ([GN26, Definition 5.2.4]). If `G` is connected, the kernel of `Ad` is the
center of `G` ([GN26, Corollary 5.5.8]).

## Main definitions

* `MBLieGroup.conjHom g`: the conjugation `x ↦ g x g⁻¹`, a morphism of Lie groups
  (`MBLieGroup.isHom_conjHom`).
* `MBLieGroup.Ad g`: the adjoint representation `Ad(g) = L(c_g)`.

## Main results

* `MBLieGroup.Ad_one`, `MBLieGroup.Ad_mul`: `Ad` is a representation ([GN26, Definition 5.2.4]).
* `MBLieGroup.Ad_eq_id_iff`: **for connected `G`, `Ad(g) = id` iff `g` is central**
  ([GN26, Corollary 5.5.8]).
* `UnitGroup.Ad_apply`: for the unit group of a continuous inverse algebra, `Ad(g) x = g x g⁻¹`
  ([GN26, Example 5.2.6(a)]).

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
  {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {H : Type*} [Group H] [TopologicalSpace H] [ChartedSpace F H] [MBLieGroup F H]

/-- `L(φ)` only depends on `φ`. -/
theorem IsHom.lieHom_congr {φ ψ : G →* H} (h : φ = ψ) (hφ : IsHom E F φ) (hψ : IsHom E F ψ) :
    hφ.lieHom = hψ.lieHom := by
  subst h; rfl

/-- The conjugation `c_g(x) = g x g⁻¹`. -/
def conjHom (g : G) : G →* G := (MulAut.conj g).toMonoidHom

omit [TopologicalSpace G] in
@[simp] theorem conjHom_apply (g x : G) : conjHom g x = g * x * g⁻¹ := rfl

variable (E) in
/-- **Conjugations are morphisms of Lie groups.** -/
theorem isHom_conjHom (g : G) : IsHom E E (conjHom g) := smoothMBM_conj g

variable (E) in
/-- **The adjoint representation** `Ad(g) = L(c_g)` ([GN26, Definition 5.2.4]). -/
def Ad (g : G) : LieAlg E G →ₗ⁅ℝ⁆ LieAlg E G := (isHom_conjHom E g).lieHom

theorem Ad_one : Ad E (1 : G) = LieHom.id := by
  rw [Ad, IsHom.lieHom_congr (ψ := MonoidHom.id G) (by ext; simp) _ (IsHom.id (E := E)),
    IsHom.lieHom_id]

theorem Ad_mul (g h : G) : Ad E (g * h) = (Ad E g).comp (Ad E h) := by
  rw [Ad, IsHom.lieHom_congr (ψ := (conjHom g).comp (conjHom h)) (by ext; simp [mul_assoc]) _
    (IsHom.comp (E := E) (F := E) (D := E) (isHom_conjHom E g) (isHom_conjHom E h)),
    IsHom.lieHom_comp (isHom_conjHom E h) (isHom_conjHom E g)]
  rfl

/-- **For connected `G`, the kernel of `Ad` is the center** ([GN26, Corollary 5.5.8]):
`Ad(g) = id` iff `g` commutes with every element of `G`. -/
theorem Ad_eq_id_iff [PreconnectedSpace G] (g : G) :
    Ad E g = LieHom.id ↔ g ∈ Subgroup.center G := by
  constructor
  · intro h
    have hc : conjHom g = MonoidHom.id G := by
      refine IsHom.eq_of_lieHom_eq (isHom_conjHom E g) (IsHom.id (E := E)) fun x ↦ ?_
      rw [IsHom.lieHom_id]
      exact LieHom.congr_fun h x
    rw [Subgroup.mem_center_iff]
    intro x
    have hx := DFunLike.congr_fun hc x
    simp only [conjHom_apply, MonoidHom.id_apply] at hx
    calc x * g = g * x * g⁻¹ * g := by rw [hx]
      _ = g * x := by group
  · intro h
    rw [Ad, IsHom.lieHom_congr (ψ := MonoidHom.id G) _ _ (IsHom.id (E := E)), IsHom.lieHom_id]
    ext x
    simp only [conjHom_apply, MonoidHom.id_apply]
    rw [(Subgroup.mem_center_iff.1 h x).symm, mul_inv_cancel_right]

end MBLieGroup

/-! ### Unit groups -/

namespace UnitGroup

variable {A : Type u} [Ring A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
  [TopologicalSpace A] [IsTopologicalRing A] [ContinuousSMul ℝ A] [LocallyConvexSpace ℝ A]
  [T2Space A] [ContinuousInverseAlgebra A]

/-- `z ↦ a z b`, as a continuous linear map. -/
def mulLeftRight (a b : A) : A →L[ℝ] A where
  toFun z := a * z * b
  map_add' z w := by simp [mul_add, add_mul]
  map_smul' c z := by simp [mul_smul_comm, smul_mul_assoc]
  cont := (continuous_const.mul continuous_id).mul continuous_const

/-- **The adjoint representation of `A^×` is conjugation** ([GN26, Example 5.2.6(a)]):
`Ad(g) x = g x g⁻¹`. -/
theorem Ad_apply (g : UnitGroup A) (x : MBLieGroup.LieAlg A (UnitGroup A)) :
    MBLieGroup.LieAlg.toModel (MBLieGroup.Ad A g x) =
      val g * MBLieGroup.LieAlg.toModel x * val g⁻¹ := by
  change dMB (MBLieGroup.IsHom.localRep (E := A) (F := A) (MBLieGroup.conjHom g))
    (chartAt A (1 : UnitGroup A) 1, (MBLieGroup.LieAlg.toModel x : A)) = _
  have h0 : chartAt A (1 : UnitGroup A) 1 = 0 := by
    change unitChart A 1 = 0; simp [unitChart]
  have hev : MBLieGroup.IsHom.localRep (E := A) (F := A) (MBLieGroup.conjHom g) =ᶠ[𝓝 (0 : A)]
      ⇑(mulLeftRight (val g) (val g⁻¹)) := by
    have ht : (chartAt A (1 : UnitGroup A)).target ∈ 𝓝 (0 : A) := by
      rw [← h0]
      exact (chartAt A (1 : UnitGroup A)).open_target.mem_nhds
        ((chartAt A (1 : UnitGroup A)).map_source (mem_chart_source A 1))
    filter_upwards [ht] with z hz
    change unitChart A (g * (chartAt A (1 : UnitGroup A)).symm z * g⁻¹) = val g * z * val g⁻¹
    rw [unitChart, val_mul, val_mul, val_chartAt_symm _ hz, mul_add, add_mul, mul_one]
    have hg : val g * val g⁻¹ = 1 := by rw [← val_mul, mul_inv_cancel, val_one]
    rw [hg, add_sub_cancel_right]
  rw [h0, dMB_congr_of_eventuallyEq hev]
  exact ((mulLeftRight (val g) (val g⁻¹)).hasDirDerivAt 0 _).dMB_eq

end UnitGroup

end LocallyConvex.LieGroups
