/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.MappingSpace.Diffeomorphism.Inverse
public import LocallyConvexManifolds.Manifold.VaryingAtlasRestrict

/-!
# The group of diffeomorphisms of a compact manifold

For a compact manifold `K` with a local addition `A`, the diffeomorphisms form an open subset
`Diff(K)` of the manifold `C^∞(K, K)` (lc-manifolds, `SmoothMap.isOpen_setOf_isDiffeo`), hence a
manifold (`diffeoAtlas`). Here we prove that the inversion is smooth ([GN26, Proposition
13.1.10(a)], `ℓ = k = ∞`); the composition is smooth by lc-manifolds
(`LocalAddition.smooth_compSm`, [GN26, Proposition 13.1.2(a)]).

## Main definitions

* `SmoothMap.IsDiffeo.inv`: the inverse of a diffeomorphism.
* `diffeos H K`: the set `Diff(K) ⊆ C^∞(K, K)`; `diffeoAtlas A`: its manifold structure.

## Main results

* `smooth_inv`: the inversion `Diff(K) → C^∞(K, K)` is smooth.

## Implementation notes

By the exponential law, the inversion is smooth as soon as `(γ, y) ↦ γ⁻¹(y)` is `C^{k,ℓ}` on
`Diff(K) × K` for all `k, ℓ`. This is [GN26, Lemma 13.1.8] (lc-manifolds,
`ContMDiffMB₂.inverse`) applied to the evaluation map `(γ, x) ↦ γ(x)`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

universe u

variable {H : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
  [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  {K : Type u} [TopologicalSpace K] [ChartedSpace H K] [MBManifold H K]

namespace LocallyConvex.Manifolds.SmoothMap

/-- The inverse of a diffeomorphism `γ ∈ C^∞(K, K)`. -/
def IsDiffeo.inv {γ : SmoothMap H H K K} (h : γ.IsDiffeo) : SmoothMap H H K K :=
  Classical.choose h

omit [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  [MBManifold H K] in
theorem IsDiffeo.inv_apply_apply {γ : SmoothMap H H K K} (h : γ.IsDiffeo) (x : K) :
    h.inv (γ x) = x :=
  (Classical.choose_spec h).1 x

omit [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]
  [MBManifold H K] in
theorem IsDiffeo.apply_inv_apply {γ : SmoothMap H H K K} (h : γ.IsDiffeo) (y : K) :
    γ (h.inv y) = y :=
  (Classical.choose_spec h).2 y

end LocallyConvex.Manifolds.SmoothMap

namespace LocallyConvex.LieGroups

variable [CompactSpace K] [T2Space K]

variable (H K) in
/-- **The group `Diff(K)`** of diffeomorphisms of the compact manifold `K`, as an open subset of
`C^∞(K, K)` ([GN26, Proposition 13.1.10]). -/
abbrev diffeos : Set (SmoothMap H H K K) := {γ | γ.IsDiffeo}

/-- **The manifold structure of `Diff(K)`**: the restriction of the atlas of `C^∞(K, K)`, given
by a local addition `A` on `K`, to the open set of diffeomorphisms. -/
abbrev diffeoAtlas (A : LocalAddition H K) : VaryingAtlas.{u, _, _} (diffeos H K) :=
  (A.mappingAtlasSm (H := H) (M := K)).restrict (diffeos H K) SmoothMap.isOpen_setOf_isDiffeo

/-- **[GN26, Proposition 13.1.10(a)]**, `ℓ = k = ∞`: the inversion `Diff(K) → C^∞(K, K)`,
`γ ↦ γ⁻¹`, is smooth. -/
theorem smooth_inv (A : LocalAddition H K) :
    (diffeoAtlas A).Smooth (A.mappingAtlasSm (H := H) (M := K))
      (fun γ : diffeos H K ↦ SmoothMap.IsDiffeo.inv γ.2) := by
  intro k
  refine A.contMDiffOn_mappingAtlasSm_iff.2 fun ℓ ↦ ?_
  rcases isEmpty_or_nonempty K with hK | hK
  · intro _ y
    exact isEmptyElim y
  have := finiteDimensional_of_compactSpace (H := H) K
  exact ContMDiffMB₂.inverse (f := fun q : diffeos H K × K ↦ q.1.1 q.2)
    (g := fun q : diffeos H K × K ↦ SmoothMap.IsDiffeo.inv q.1.2 q.2)
    (fun n ↦ (A.contMDiffMB₂_evalSm (H := H) (M := K) n n).restrict
      SmoothMap.isOpen_setOf_isDiffeo)
    (fun γ ↦ γ.1.2 1) (fun γ ↦ (SmoothMap.IsDiffeo.inv γ.2).2 1)
    (fun γ x ↦ SmoothMap.IsDiffeo.inv_apply_apply γ.2 x)
    (fun γ y ↦ SmoothMap.IsDiffeo.apply_inv_apply γ.2 y) k ℓ

end LocallyConvex.LieGroups
