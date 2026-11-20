/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.Manifold.Product

/-!
# Lie groups modeled on locally convex spaces

A Lie group is a manifold modeled on a locally convex space, endowed with a group structure
whose multiplication and inversion are smooth in the sense of Michal–Bastiani
([GN26, Definition 5.1.1(b)]). Morphisms of Lie groups are the smooth group homomorphisms
([GN26, Definition 5.1.1(c)]).

## Main definitions

* `MBLieGroup E G`: `G` is a Lie group modeled on the locally convex space `E`.
* `MBLieGroup.IsHom`: smooth group homomorphisms (morphisms of Lie groups).

## Main results

* `MBLieGroup.smoothMBM_mul_left`, `MBLieGroup.smoothMBM_mul_right`: the left and right
  multiplications `λ_g`, `ρ_g` are smooth.
* `MBLieGroup.smoothMBM_conj`: conjugation `x ↦ g x g⁻¹` is smooth.
* `MBLieGroup.isTopologicalGroup`: a Lie group is a topological group ([GN26, Definition
  5.1.1(b)], the remark after it).
* `MBLieGroup.IsHom.id`, `MBLieGroup.IsHom.comp`: identities and composites of morphisms.

## Implementation notes

As in the rest of these libraries, the model space need not be complete ([GN26, §5.7]).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups

universe u

variable (E : Type u) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

/-- **Lie groups** ([GN26, Definition 5.1.1(b)]): a manifold `G` modeled on the locally convex
space `E`, with a group structure such that the multiplication `G × G → G` and the inversion
`G → G` are smooth. The model space need not be complete. -/
class MBLieGroup (G : Type*) [Group G] [TopologicalSpace G] [ChartedSpace E G] : Prop
    extends HasGroupoid G (mbGroupoid E) where
  /-- The multiplication is smooth. -/
  smoothMBM_mul : SmoothMBM (ModelProd E E) E (fun p : G × G ↦ p.1 * p.2)
  /-- The inversion is smooth. -/
  smoothMBM_inv : SmoothMBM E E (fun g : G ↦ g⁻¹)

namespace MBLieGroup

variable {E}
variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]

/-- The left multiplication `λ_g : x ↦ g x` is smooth. -/
theorem smoothMBM_mul_left (g : G) : SmoothMBM E E (fun x : G ↦ g * x) := by
  have hpair : SmoothMBM E (ModelProd E E) (fun x : G ↦ (g, x)) := fun k ↦
    ContMDiffMBOn.prodMk isOpen_univ (smoothMBMOn_const univ g k) (smoothMBMOn_id isOpen_univ k)
  exact (smoothMBM_mul (E := E)).comp hpair

/-- The right multiplication `ρ_g : x ↦ x g` is smooth. -/
theorem smoothMBM_mul_right (g : G) : SmoothMBM E E (fun x : G ↦ x * g) := by
  have hpair : SmoothMBM E (ModelProd E E) (fun x : G ↦ (x, g)) := fun k ↦
    ContMDiffMBOn.prodMk isOpen_univ (smoothMBMOn_id isOpen_univ k) (smoothMBMOn_const univ g k)
  exact (smoothMBM_mul (E := E)).comp hpair

/-- Conjugation `x ↦ g x g⁻¹` is smooth. -/
theorem smoothMBM_conj (g : G) : SmoothMBM E E (fun x : G ↦ g * x * g⁻¹) :=
  (smoothMBM_mul_right (E := E) g⁻¹).comp (smoothMBM_mul_left g)

variable (E G) in
include E in
/-- **A Lie group is a topological group** (the remark after [GN26, Definition 5.1.1]): smooth
maps are continuous. -/
theorem isTopologicalGroup : IsTopologicalGroup G where
  continuous_mul := continuousOn_univ.1 ((smoothMBM_mul (E := E) (G := G)) 0).1
  continuous_inv := continuousOn_univ.1 ((smoothMBM_inv (E := E) (G := G)) 0).1

variable {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

variable (E F) in
/-- **Morphisms of Lie groups** ([GN26, Definition 5.1.1(c)]): group homomorphisms that are
smooth. The groups may be modeled on different spaces. -/
def IsHom {H : Type*} [Group H] [TopologicalSpace H] [ChartedSpace F H] (φ : G →* H) : Prop :=
  SmoothMBM E F φ

omit [MBLieGroup E G] in
/-- The identity is a morphism of Lie groups. -/
theorem IsHom.id : IsHom E E (MonoidHom.id G) :=
  smoothMBMOn_id (E := E) isOpen_univ

/-- The composite of morphisms of Lie groups is a morphism of Lie groups. -/
theorem IsHom.comp {D : Type u} [AddCommGroup D] [Module ℝ D] [TopologicalSpace D]
    [IsTopologicalAddGroup D] [ContinuousSMul ℝ D] [LocallyConvexSpace ℝ D] [T2Space D]
    {H K : Type*} [Group H] [TopologicalSpace H] [ChartedSpace F H] [MBLieGroup F H]
    [Group K] [TopologicalSpace K] [ChartedSpace D K] [MBLieGroup D K]
    {φ : G →* H} {ψ : H →* K} (hψ : IsHom F D ψ) (hφ : IsHom E F φ) : IsHom E D (ψ.comp φ) :=
  show SmoothMBM E D (ψ ∘ φ) from SmoothMBM.comp hψ hφ

end MBLieGroup

end LocallyConvex.LieGroups
