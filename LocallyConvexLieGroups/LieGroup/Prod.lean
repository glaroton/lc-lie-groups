/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.LieAlgebra.Taylor
public import LocallyConvexManifolds.Manifold.Product
public import Mathlib.Algebra.Lie.Prod

/-!
# Products of Lie groups

If `G` and `H` are Lie groups modeled on `E` and `F`, then `G × H` is a Lie group modeled on
`E × F` (with lc-manifolds' product manifold structure), and its Lie algebra is the product of
the Lie algebras: `L(G × H) ≅ L(G) × L(H)`, with the componentwise bracket. In the charts at the
identity the multiplication of `G × H` is the product of the two local group laws, whose bracket
is computed componentwise.

## Main definitions

* `LocalGroupLaw.prod`: the product of two local group laws.
* `MBLieGroup.LieAlg.prodEquiv`: the Lie algebra isomorphism `L(G × H) ≃ L(G) × L(H)`.

## Main results

* `LocalGroupLaw.b2_prod`, `LocalGroupLaw.bracket_prod`: second order terms and brackets of
  product laws are computed componentwise.
* `MBLieGroup.instProd`: **the product of two Lie groups is a Lie group**.
* `MBLieGroup.LieAlg.prod_lie`: **the bracket of `L(G × H)` is componentwise**.

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

variable {E F : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

/-! ### Products of local group laws -/

namespace LocalGroupLaw

variable (L : LocalGroupLaw E) (L' : LocalGroupLaw F)

/-- `((a, b), (a', b')) ↦ (a, a')`. -/
def prodFst : (ModelProd E F × ModelProd E F) →L[ℝ] E × E :=
  ((ContinuousLinearMap.fst ℝ E F).comp (ContinuousLinearMap.fst ℝ (E × F) (E × F))).prod
    ((ContinuousLinearMap.fst ℝ E F).comp (ContinuousLinearMap.snd ℝ (E × F) (E × F)))

/-- `((a, b), (a', b')) ↦ (b, b')`. -/
def prodSnd : (ModelProd E F × ModelProd E F) →L[ℝ] F × F :=
  ((ContinuousLinearMap.snd ℝ E F).comp (ContinuousLinearMap.fst ℝ (E × F) (E × F))).prod
    ((ContinuousLinearMap.snd ℝ E F).comp (ContinuousLinearMap.snd ℝ (E × F) (E × F)))

/-- **The product of two local group laws**, on `E × F`. -/
def prod : LocalGroupLaw (ModelProd E F) where
  mul q := (L.mul (prodFst q), L'.mul (prodSnd q))
  dom := prodFst ⁻¹' L.dom ∩ prodSnd ⁻¹' L'.dom
  one := (L.one, L'.one)
  isOpen_dom := (L.isOpen_dom.preimage prodFst.continuous).inter
    (L'.isOpen_dom.preimage prodSnd.continuous)
  one_one_mem := ⟨L.one_one_mem, L'.one_one_mem⟩
  smooth k := ContDiffMBOn.prodMk
    ((L.isOpen_dom.preimage prodFst.continuous).inter (L'.isOpen_dom.preimage prodSnd.continuous))
    (ContDiffMBOn.comp ((L.isOpen_dom.preimage prodFst.continuous).inter
      (L'.isOpen_dom.preimage prodSnd.continuous)) L.isOpen_dom (L.smooth k)
      ((prodFst (E := E) (F := F)).contDiffMBOn k _) fun _ hq ↦ hq.1)
    (ContDiffMBOn.comp ((L.isOpen_dom.preimage prodFst.continuous).inter
      (L'.isOpen_dom.preimage prodSnd.continuous)) L'.isOpen_dom (L'.smooth k)
      ((prodSnd (E := E) (F := F)).contDiffMBOn k _) fun _ hq ↦ hq.2)
  one_mul b hb := Prod.ext (L.one_mul b.1 hb.1) (L'.one_mul b.2 hb.2)
  mul_one a ha := Prod.ext (L.mul_one a.1 ha.1) (L'.mul_one a.2 ha.2)
  mul_assoc a b c hab hbc habc habc' :=
    Prod.ext (L.mul_assoc a.1 b.1 c.1 hab.1 hbc.1 habc.1 habc'.1)
      (L'.mul_assoc a.2 b.2 c.2 hab.2 hbc.2 habc.2 habc'.2)

theorem prod_mul (a b : ModelProd E F) :
    (L.prod L').mul (a, b) = (L.mul (a.1, b.1), L'.mul (a.2, b.2)) := rfl

theorem prod_one : (L.prod L').one = (L.one, L'.one) := rfl

theorem mem_prod_dom {a b : ModelProd E F} :
    (a, b) ∈ (L.prod L').dom ↔ (a.1, b.1) ∈ L.dom ∧ (a.2, b.2) ∈ L'.dom := Iff.rfl

/-- The left invariant fields of a product law are products. -/
theorem prod_xl (y : ModelProd E F) {z : ModelProd E F} (hz : z ∈ (L.prod L').domR) :
    (L.prod L').xl y z = (L.xl y.1 z.1, L'.xl y.2 z.2) := by
  rw [xl_eq, xl_eq, xl_eq]
  set U : Set (ModelProd E F) :=
    Prod.fst ⁻¹' L.domL z.1 ∩ Prod.snd ⁻¹' L'.domL z.2
  have hU : IsOpen U := ((L.isOpen_domL z.1).preimage continuous_fst).inter
    ((L'.isOpen_domL z.2).preimage continuous_snd)
  have hf : ContDiffMBOn 1 ((fun b ↦ L.mul (z.1, b)) ∘ ⇑(ContinuousLinearMap.fst ℝ E F)) U :=
    ContDiffMBOn.comp hU (L.isOpen_domL z.1) (L.contDiffMBOn_mul_left 1 z.1)
      ((ContinuousLinearMap.fst ℝ E F).contDiffMBOn 1 _) fun _ hb ↦ hb.1
  have hg : ContDiffMBOn 1 ((fun b ↦ L'.mul (z.2, b)) ∘ ⇑(ContinuousLinearMap.snd ℝ E F)) U :=
    ContDiffMBOn.comp hU (L'.isOpen_domL z.2) (L'.contDiffMBOn_mul_left 1 z.2)
      ((ContinuousLinearMap.snd ℝ E F).contDiffMBOn 1 _) fun _ hb ↦ hb.2
  have h := dMB_prodMk hf hg (p := (L.prod L').one) ⟨hz.1, hz.2⟩ y
  rw [dMB_comp_clm, dMB_comp_clm] at h
  exact h

/-- **Second order terms of product laws are componentwise.** -/
theorem b2_prod (x y : ModelProd E F) :
    (L.prod L').b2 x y = (L.b2 x.1 y.1, L'.b2 x.2 y.2) := by
  set U : Set (ModelProd E F) := Prod.fst ⁻¹' L.domR ∩ Prod.snd ⁻¹' L'.domR
  have hU : IsOpen U := (L.isOpen_domR.preimage continuous_fst).inter
    (L'.isOpen_domR.preimage continuous_snd)
  have h1U : (L.prod L').one ∈ U := ⟨L.one_mem_domR, L'.one_mem_domR⟩
  have hev : (L.prod L').xl y =ᶠ[𝓝 (L.prod L').one]
      fun z : ModelProd E F ↦ (L.xl y.1 z.1, L'.xl y.2 z.2) :=
    eventuallyEq_of_mem ((L.prod L').isOpen_domR.mem_nhds (L.prod L').one_mem_domR)
      fun z hz ↦ L.prod_xl L' y hz
  have hf : ContDiffMBOn 1 (L.xl y.1 ∘ ⇑(ContinuousLinearMap.fst ℝ E F)) U :=
    ContDiffMBOn.comp hU L.isOpen_domR (L.contDiffMBOn_xl 1 y.1)
      ((ContinuousLinearMap.fst ℝ E F).contDiffMBOn 1 _) fun _ hb ↦ hb.1
  have hg : ContDiffMBOn 1 (L'.xl y.2 ∘ ⇑(ContinuousLinearMap.snd ℝ E F)) U :=
    ContDiffMBOn.comp hU L'.isOpen_domR (L'.contDiffMBOn_xl 1 y.2)
      ((ContinuousLinearMap.snd ℝ E F).contDiffMBOn 1 _) fun _ hb ↦ hb.2
  have h := dMB_prodMk hf hg h1U x
  rw [dMB_comp_clm, dMB_comp_clm] at h
  rw [b2, dMB_congr_of_eventuallyEq hev]
  exact h

/-- **Brackets of product laws are componentwise.** -/
theorem bracket_prod (x y : ModelProd E F) :
    (L.prod L').bracket x y = (L.bracket x.1 y.1, L'.bracket x.2 y.2) := by
  rw [bracket_eq_b2_sub_b2, b2_prod, b2_prod, bracket_eq_b2_sub_b2, bracket_eq_b2_sub_b2]
  rfl

end LocalGroupLaw

/-! ### Products of Lie groups -/

namespace MBLieGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]
  {H : Type*} [Group H] [TopologicalSpace H] [ChartedSpace F H] [MBLieGroup F H]

/-- **The product of two Lie groups is a Lie group**, modeled on `E × F`. -/
instance instProd : MBLieGroup (ModelProd E F) (G × H) where
  smoothMBM_mul := by
    have hG : SmoothMBM (ModelProd (ModelProd E F) (ModelProd E F)) E
        (fun p : (G × H) × (G × H) ↦ p.1.1 * p.2.1) :=
      (smoothMBM_mul (E := E) (G := G)).comp (fun k ↦ ContMDiffMBOn.prodMk isOpen_univ
        ((smoothMBM_fst.comp smoothMBM_fst) k) ((smoothMBM_fst.comp smoothMBM_snd) k))
    have hH : SmoothMBM (ModelProd (ModelProd E F) (ModelProd E F)) F
        (fun p : (G × H) × (G × H) ↦ p.1.2 * p.2.2) :=
      (smoothMBM_mul (E := F) (G := H)).comp (fun k ↦ ContMDiffMBOn.prodMk isOpen_univ
        ((smoothMBM_snd.comp smoothMBM_fst) k) ((smoothMBM_snd.comp smoothMBM_snd) k))
    exact fun k ↦ ContMDiffMBOn.prodMk isOpen_univ (hG k) (hH k)
  smoothMBM_inv := by
    have hG : SmoothMBM (ModelProd E F) E (fun p : G × H ↦ p.1⁻¹) :=
      (smoothMBM_inv (E := E) (G := G)).comp smoothMBM_fst
    have hH : SmoothMBM (ModelProd E F) F (fun p : G × H ↦ p.2⁻¹) :=
      (smoothMBM_inv (E := F) (G := H)).comp smoothMBM_snd
    exact fun k ↦ ContMDiffMBOn.prodMk isOpen_univ (hG k) (hH k)

variable (E F G H)

/-- In the charts at the identity, the multiplication of `G × H` is the product of the
multiplications of `G` and `H`. -/
theorem localGroupLaw_prod_eqOn :
    EqOn (localGroupLaw (ModelProd E F) (G × H)).mul
      ((localGroupLaw E G).prod (localGroupLaw F H)).mul
      (localGroupLaw (ModelProd E F) (G × H)).dom :=
  fun _ _ ↦ rfl

/-- **The bracket of `L(G × H)` is componentwise.** -/
theorem LieAlg.prod_lie (x y : LieAlg (ModelProd E F) (G × H)) :
    LieAlg.toModel ⁅x, y⁆ =
      ((localGroupLaw E G).bracket (LieAlg.toModel x).1 (LieAlg.toModel y).1,
        (localGroupLaw F H).bracket (LieAlg.toModel x).2 (LieAlg.toModel y).2) := by
  set L := localGroupLaw (ModelProd E F) (G × H)
  change L.bracket (LieAlg.toModel x) (LieAlg.toModel y) = _
  rw [LocalGroupLaw.bracket_congr L ((localGroupLaw E G).prod (localGroupLaw F H)) rfl
    L.isOpen_dom L.one_one_mem (localGroupLaw_prod_eqOn E F G H)]
  exact LocalGroupLaw.bracket_prod _ _ _ _

/-- **`L(G × H) ≅ L(G) × L(H)`** as Lie algebras. -/
def LieAlg.prodEquiv : LieAlg (ModelProd E F) (G × H) ≃ₗ⁅ℝ⁆ LieAlg E G × LieAlg F H where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_lie' {x y} := LieAlg.prod_lie E F G H x y

end MBLieGroup

end LocallyConvex.LieGroups
