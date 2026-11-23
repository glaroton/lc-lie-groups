/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.LieAlgebra.AdjointAction
public import LocallyConvexLieGroups.Exponential.Basic
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Semidirect products of Lie groups

Let `N`, `G` be Lie groups and `α : G → Aut(N)` a homomorphism defining a smooth action
`(g, n) ↦ α(g)(n)`. The product manifold `N × G` with the multiplication
`(n, g)(n', g') = (n α(g)(n'), g g')` is a Lie group, the semidirect product `N ⋊_α G`
([GN26, Definition 5.2.7]).

## Main definitions

* `SDProd α`: the semidirect product `N ⋊_α G`, a type synonym for `N × G` with the group
  structure of Mathlib's `SemidirectProduct` and the product manifold structure.
* `SDProd.mbLieGroup`: the semidirect product is a Lie group if the action is smooth.
* `SDProd.proj`, `SDProd.sec`, `SDProd.incl`: the morphisms `π`, `σ`, `ι` of
  [GN26, Remark 5.2.10], with `π ∘ σ = id` and `ι(N) = ker π`.
* `MBLieGroup.AdMulAut`: the adjoint action of `G` on the vector group `L(G)`, and
  `MBLieGroup.TangentGroup G = L(G) ⋊_Ad G`, which [GN26, Example 5.2.12] identifies with the
  tangent group `T(G)`.

## Implementation notes

`SDProd α` is a type synonym, not `N × G` itself, so that its group structure does not clash
with the direct product structure of `N × G`. The identification of `L(G) ⋊_Ad G` with the
tangent bundle `T(G)` with the group structure of [GN26, Proposition 5.2.2] is not formalized.

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

variable {E F : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]
  {N : Type*} [Group N] [TopologicalSpace N] [ChartedSpace F N] [MBLieGroup F N]

/-- **The semidirect product** `N ⋊_α G` ([GN26, Definition 5.2.7]), on the product manifold
`N × G`. -/
@[nolint unusedArguments]
def SDProd (_α : G →* MulAut N) : Type _ := N × G

namespace SDProd

variable (α : G →* MulAut N)

instance : Group (SDProd α) :=
  (SemidirectProduct.equivProd (φ := α)).symm.group

instance : TopologicalSpace (SDProd α) := inferInstanceAs (TopologicalSpace (N × G))

instance : ChartedSpace (ModelProd F E) (SDProd α) :=
  inferInstanceAs (ChartedSpace (ModelProd F E) (N × G))

instance : HasGroupoid (SDProd α) (mbGroupoid (ModelProd F E)) :=
  inferInstanceAs (HasGroupoid (N × G) (mbGroupoid (ModelProd F E)))

variable {α}

/-- The underlying pair. -/
def toProd (p : SDProd α) : N × G := p

omit [TopologicalSpace G] [TopologicalSpace N] in
theorem mul_def (p q : SDProd α) :
    toProd (p * q) = ((toProd p).1 * α (toProd p).2 (toProd q).1, (toProd p).2 * (toProd q).2) :=
  rfl

omit [TopologicalSpace G] [TopologicalSpace N] in
theorem inv_def (p : SDProd α) :
    toProd p⁻¹ = (α (toProd p).2⁻¹ (toProd p).1⁻¹, (toProd p).2⁻¹) :=
  rfl

omit [TopologicalSpace G] [TopologicalSpace N] in
theorem one_def : toProd (1 : SDProd α) = (1, 1) := rfl

variable (E F) in
/-- The action `(g, n) ↦ α(g)(n)` is smooth. -/
def IsSmoothAction (α : G →* MulAut N) : Prop :=
  SmoothMBM (ModelProd E F) F (fun q : G × N ↦ α q.1 q.2)

/-- **The semidirect product of Lie groups is a Lie group** ([GN26, Definition 5.2.7]). -/
theorem mbLieGroup (hα : IsSmoothAction E F α) : MBLieGroup (ModelProd F E) (SDProd α) where
  smoothMBM_mul := by
    have hN : SmoothMBM (ModelProd (ModelProd F E) (ModelProd F E)) F
        (fun p : (N × G) × (N × G) ↦ p.1.1 * α p.1.2 p.2.1) := by
      have ha : SmoothMBM (ModelProd (ModelProd F E) (ModelProd F E)) F
          (fun p : (N × G) × (N × G) ↦ α p.1.2 p.2.1) :=
        hα.comp (fun k ↦ ContMDiffMBOn.prodMk (f := fun p : (N × G) × (N × G) ↦ p.1.2)
          (g := fun p : (N × G) × (N × G) ↦ p.2.1) isOpen_univ
          ((smoothMBM_snd.comp smoothMBM_fst) k) ((smoothMBM_fst.comp smoothMBM_snd) k))
      exact (MBLieGroup.smoothMBM_mul (E := F) (G := N)).comp (fun k ↦ ContMDiffMBOn.prodMk
        (f := fun p : (N × G) × (N × G) ↦ p.1.1) (g := fun p : (N × G) × (N × G) ↦ α p.1.2 p.2.1)
        isOpen_univ ((smoothMBM_fst.comp smoothMBM_fst) k) (ha k))
    have hG : SmoothMBM (ModelProd (ModelProd F E) (ModelProd F E)) E
        (fun p : (N × G) × (N × G) ↦ p.1.2 * p.2.2) :=
      (MBLieGroup.smoothMBM_mul (E := E) (G := G)).comp (fun k ↦ ContMDiffMBOn.prodMk
        (f := fun p : (N × G) × (N × G) ↦ p.1.2) (g := fun p : (N × G) × (N × G) ↦ p.2.2)
        isOpen_univ ((smoothMBM_snd.comp smoothMBM_fst) k) ((smoothMBM_snd.comp smoothMBM_snd) k))
    have h : SmoothMBM (ModelProd (ModelProd F E) (ModelProd F E)) (ModelProd F E)
        (fun p : (N × G) × (N × G) ↦ (p.1.1 * α p.1.2 p.2.1, p.1.2 * p.2.2)) :=
      fun k ↦ ContMDiffMBOn.prodMk isOpen_univ (hN k) (hG k)
    exact h
  smoothMBM_inv := by
    have hi : SmoothMBM (ModelProd F E) E (fun p : N × G ↦ p.2⁻¹) :=
      (MBLieGroup.smoothMBM_inv (E := E) (G := G)).comp smoothMBM_snd
    have hn : SmoothMBM (ModelProd F E) F (fun p : N × G ↦ p.1⁻¹) :=
      (MBLieGroup.smoothMBM_inv (E := F) (G := N)).comp smoothMBM_fst
    have hN : SmoothMBM (ModelProd F E) F (fun p : N × G ↦ α p.2⁻¹ p.1⁻¹) :=
      hα.comp (fun k ↦ ContMDiffMBOn.prodMk (f := fun p : N × G ↦ p.2⁻¹)
        (g := fun p : N × G ↦ p.1⁻¹) isOpen_univ (hi k) (hn k))
    have h : SmoothMBM (ModelProd F E) (ModelProd F E)
        (fun p : N × G ↦ (α p.2⁻¹ p.1⁻¹, p.2⁻¹)) :=
      fun k ↦ ContMDiffMBOn.prodMk isOpen_univ (hN k) (hi k)
    exact h

/-! ### The canonical morphisms -/

variable (α)

/-- The projection `π : N ⋊_α G → G`, `(n, g) ↦ g`. -/
def proj : SDProd α →* G where
  toFun p := (toProd p).2
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The section `σ : G → N ⋊_α G`, `g ↦ (1, g)`. -/
def sec : G →* SDProd α where
  toFun g := ((1 : N), g)
  map_one' := rfl
  map_mul' g h := by
    change ((1 : N), g * h) = ((1 : N) * α g (1 : N), g * h)
    rw [map_one, one_mul]

/-- The inclusion `ι : N → N ⋊_α G`, `n ↦ (n, 1)`. -/
def incl : N →* SDProd α where
  toFun n := (n, (1 : G))
  map_one' := rfl
  map_mul' n m := by
    change (n * m, (1 : G)) = (n * α (1 : G) m, (1 : G) * 1)
    rw [map_one, MulAut.one_apply, one_mul]

omit [TopologicalSpace G] [TopologicalSpace N] in
/-- `π ∘ σ = id`. -/
theorem proj_comp_sec : (proj α).comp (sec α) = MonoidHom.id G := rfl

omit [TopologicalSpace G] [TopologicalSpace N] in
/-- `ι` is injective with image `ker π`. -/
theorem range_incl : (incl α).range = (proj α).ker := by
  ext p
  constructor
  · rintro ⟨n, rfl⟩; rfl
  · intro hp
    refine ⟨(toProd p).1, ?_⟩
    change ((toProd p).1, (1 : G)) = p
    have h : (toProd p).2 = 1 := hp
    exact Prod.ext rfl h.symm

omit [TopologicalSpace G] [TopologicalSpace N] in
theorem incl_injective : Function.Injective (incl α) := fun _ _ h ↦ congrArg Prod.fst h

variable {α}

omit [MBLieGroup E G] [MBLieGroup F N] in
/-- **The canonical morphisms of a semidirect product** ([GN26, Remark 5.2.10]): `π`, `σ` and `ι`
are morphisms of Lie groups. -/
theorem isHom_proj : MBLieGroup.IsHom (ModelProd F E) E (proj α) :=
  smoothMBM_snd (M := N) (N := G)

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [MBLieGroup E G]
  [MBLieGroup F N] in
theorem isHom_sec : MBLieGroup.IsHom E (ModelProd F E) (sec α) := fun k ↦
  ContMDiffMBOn.prodMk (f := fun _ : G ↦ (1 : N)) (g := fun g : G ↦ g) isOpen_univ
    (smoothMBMOn_const univ (1 : N) k) (smoothMBMOn_id isOpen_univ k)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [MBLieGroup E G]
  [MBLieGroup F N] in
theorem isHom_incl : MBLieGroup.IsHom F (ModelProd F E) (incl α) := fun k ↦
  ContMDiffMBOn.prodMk (f := fun n : N ↦ n) (g := fun _ : N ↦ (1 : G)) isOpen_univ
    (smoothMBMOn_id isOpen_univ k) (smoothMBMOn_const univ (1 : G) k)

end SDProd

/-! ### The tangent group `L(G) ⋊_Ad G` -/

namespace MBLieGroup

/-- `Ad(g)` as an additive automorphism of the model space. -/
def AdAddAut (g : G) : E ≃+ E where
  toFun := AdCLM g
  invFun := AdCLM g⁻¹
  left_inv y := by
    change LieAlg.toModel (Ad E g⁻¹ (Ad E g (LieAlg.toModel.symm y))) = y
    rw [← LieHom.comp_apply, ← Ad_mul, inv_mul_cancel, Ad_one]; rfl
  right_inv y := by
    change LieAlg.toModel (Ad E g (Ad E g⁻¹ (LieAlg.toModel.symm y))) = y
    rw [← LieHom.comp_apply, ← Ad_mul, mul_inv_cancel, Ad_one]; rfl
  map_add' := (AdCLM g).map_add

variable (E G) in
/-- **The adjoint action on the vector group `L(G)`**, as a homomorphism `G → Aut(L(G), +)`. -/
def AdMulAut : G →* MulAut (Multiplicative E) where
  toFun g := AddEquiv.toMultiplicative (AdAddAut g)
  map_one' := by
    ext y
    change Multiplicative.ofAdd (LieAlg.toModel (Ad E (1 : G) (LieAlg.toModel.symm y.toAdd))) = y
    rw [Ad_one]; rfl
  map_mul' g h := by
    ext y
    change Multiplicative.ofAdd (LieAlg.toModel (Ad E (g * h) (LieAlg.toModel.symm y.toAdd))) =
      Multiplicative.ofAdd (LieAlg.toModel (Ad E g (Ad E h (LieAlg.toModel.symm y.toAdd))))
    rw [Ad_mul]; rfl

theorem smoothMBM_toAdd : SmoothMBM E E (Multiplicative.toAdd : Multiplicative E → E) := by
  intro k
  refine ⟨continuous_toAdd.continuousOn, fun x _ ↦ ?_⟩
  exact ContDiffMBOn.congr_of_isOpen
    (isOpen_chartDomain isOpen_univ continuous_toAdd.continuousOn _ _) (fun _ _ ↦ rfl)
    ((smoothMBOn_id univ k).mono (subset_univ _))

/-- **The adjoint action on `L(G)` is smooth.** -/
theorem isSmoothAction_AdMulAut : SDProd.IsSmoothAction E E (AdMulAut E G) := by
  have hpair : SmoothMBM (ModelProd E E) (ModelProd E E)
      (fun q : G × Multiplicative E ↦ (q.1, Multiplicative.toAdd q.2)) := fun k ↦
    ContMDiffMBOn.prodMk isOpen_univ (smoothMBM_fst k) ((smoothMBM_toAdd.comp smoothMBM_snd) k)
  have h := (VectorGroup.isExp E).smooth.comp (smoothMBM_AdAction.comp hpair)
  exact h

variable (E G) in
/-- **The tangent group** `T(G) ≅ L(G) ⋊_Ad G` ([GN26, Example 5.2.12]). -/
abbrev TangentGroup : Type _ := SDProd (AdMulAut E G)

instance : MBLieGroup (ModelProd E E) (TangentGroup E G) :=
  SDProd.mbLieGroup isSmoothAction_AdMulAut

end MBLieGroup

end LocallyConvex.LieGroups
