/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexManifolds.MappingSpace.Diffeomorphism.Inverse
public import LocallyConvexManifolds.Manifold.VaryingAtlasRestrict
public import LocallyConvexManifolds.MappingSpace.CompositionMap
public import LocallyConvexLieGroups.LieGroup.OfVaryingAtlas

/-!
# The group of diffeomorphisms of a compact manifold

For a compact manifold `K` with a local addition `A`, the diffeomorphisms form an open subset
`Diff(K)` of the manifold `C^∞(K, K)` (lc-manifolds, `SmoothMap.isOpen_setOf_isDiffeo`), hence a
manifold (`diffeoAtlas`). Here we prove that the inversion is smooth ([GN26, Proposition
13.1.10(a)], `ℓ = k = ∞`); the composition is smooth by lc-manifolds
(`LocalAddition.smooth_compSm`, [GN26, Proposition 13.1.2(a)]).

## Main definitions

* `SmoothMap.IsDiffeo.inv`: the inverse of a diffeomorphism.
* `diffeos H K`: the set `Diff(K) ⊆ C^∞(K, K)`, a group under composition; `diffeoAtlas A`: its
  manifold structure.
* `Diffeo A`: `Diff(K)` as a Lie group, modeled on the model `DiffeoModel A` of the chart of
  `C^∞(K, K)` at the identity (the smooth sections along `id`, i.e. the vector fields on `K`).

## Main results

* `smooth_inv`: the inversion `Diff(K) → C^∞(K, K)` is smooth.
* `isVaryingLieGroup_diffeos`: composition and inversion are smooth on `Diff(K)`.
* `Diffeo.instMBLieGroup`: **`Diff(K)` is a Lie group** ([GN26, Proposition 13.1.10(e)]).

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

/-! ### `Diff(K)` is a Lie group -/

/-- `Diff(K)` is a group under composition. -/
instance : Group (diffeos H K) where
  mul γ η := ⟨SmoothMap.comp γ.1 η.1, γ.2.comp η.2⟩
  one := ⟨⟨id, fun k ↦ smoothMBMOn_id isOpen_univ k⟩, SmoothMap.isDiffeo_id⟩
  inv γ := ⟨SmoothMap.IsDiffeo.inv γ.2, SmoothMap.IsDiffeo.symm
    (SmoothMap.IsDiffeo.inv_apply_apply γ.2) (SmoothMap.IsDiffeo.apply_inv_apply γ.2)⟩
  mul_assoc _ _ _ := Subtype.ext (SmoothMap.ext fun _ ↦ rfl)
  one_mul _ := Subtype.ext (SmoothMap.ext fun _ ↦ rfl)
  mul_one _ := Subtype.ext (SmoothMap.ext fun _ ↦ rfl)
  inv_mul_cancel γ := Subtype.ext (SmoothMap.ext fun x ↦ SmoothMap.IsDiffeo.inv_apply_apply γ.2 x)

omit [CompactSpace K] [T2Space K] in
@[simp]
theorem diffeos_coe_mul (γ η : diffeos H K) :
    ((γ * η : diffeos H K) : SmoothMap H H K K) = SmoothMap.comp γ.1 η.1 :=
  rfl

omit [CompactSpace K] [T2Space K] in
@[simp]
theorem diffeos_coe_inv (γ : diffeos H K) :
    ((γ⁻¹ : diffeos H K) : SmoothMap H H K K) = SmoothMap.IsDiffeo.inv γ.2 :=
  rfl

/-- **Composition and inversion are smooth on `Diff(K)`** ([GN26, Proposition 13.1.10(a), (b)],
`ℓ = k = ∞`): composition by [GN26, Proposition 13.1.2(a)] (lc-manifolds,
`LocalAddition.smooth_compSm`), inversion by `smooth_inv`. -/
theorem isVaryingLieGroup_diffeos (A : LocalAddition H K) :
    IsVaryingLieGroup (diffeoAtlas A) := by
  set M := A.mappingAtlasSm (H := H) (M := K)
  have hval := VaryingAtlas.smooth_val M SmoothMap.isOpen_setOf_isDiffeo
  have hpair : ((diffeoAtlas A).prod (diffeoAtlas A)).Smooth (M.prod M)
      (fun p : diffeos H K × diffeos H K ↦
        ((p.1 : SmoothMap H H K K), (p.2 : SmoothMap H H K K))) :=
    VaryingAtlas.Smooth.prodMk (hval.comp (VaryingAtlas.smooth_fst _ _))
      (hval.comp (VaryingAtlas.smooth_snd _ _))
  have hcomp := (LocalAddition.smooth_compSm A A).comp hpair
  refine ⟨fun k ↦ ?_, fun k ↦ ?_⟩
  · exact (M.contMDiffOn_restrict_iff SmoothMap.isOpen_setOf_isDiffeo).2 (hcomp k)
  · exact (M.contMDiffOn_restrict_iff SmoothMap.isOpen_setOf_isDiffeo).2 (smooth_inv A k)

/-- The model space of the Lie group `Diff(K)`: the model of the chart of `C^∞(K, K)` at the
identity, the space of smooth sections of `TK` along `id`, that is, of vector fields on `K`. -/
abbrev DiffeoModel (A : LocalAddition H K) : Type u :=
  (diffeoAtlas A).model ((diffeoAtlas A).chartAt 1)

/-- **The Lie group `Diff(K)`** of diffeomorphisms of the compact manifold `K`, with the manifold
structure given by the local addition `A` (the type does not depend on `A`, its charts do). -/
def Diffeo (_A : LocalAddition H K) : Type u := diffeos H K

namespace Diffeo

variable (A : LocalAddition H K)

instance : Group (Diffeo A) := inferInstanceAs (Group (diffeos H K))

instance : TopologicalSpace (Diffeo A) := inferInstanceAs (TopologicalSpace (diffeos H K))

instance : ChartedSpace (DiffeoModel A) (Diffeo A) := (isVaryingLieGroup_diffeos A).chartedSpace

/-- **[GN26, Proposition 13.1.10(e)]: `Diff(K)` is a Lie group**, for every compact manifold `K`
with a local addition, modeled on the space of vector fields on `K`. -/
instance instMBLieGroup : MBLieGroup (DiffeoModel A) (Diffeo A) :=
  (isVaryingLieGroup_diffeos A).mbLieGroup

end Diffeo

end LocallyConvex.LieGroups
