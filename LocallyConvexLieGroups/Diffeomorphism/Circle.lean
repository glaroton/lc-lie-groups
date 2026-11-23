/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Diffeomorphism.LieAlgebra
public import LocallyConvexLieGroups.LieGroup.OpenSubgroup
public import LocallyConvexManifolds.Examples.SphereLocalAddition

/-!
# The diffeomorphism group of the circle

The circle `S¹` is the unit sphere of `ℝ²`, an embedded submanifold modeled on the line
`e₀^⊥` (lc-manifolds, `isEmbeddedSubmanifold_sphere`), with the normalized local addition
`Σ(p, w) = (p + w)/‖p + w‖` (lc-manifolds, `sphereLocalAddition`). Hence `Diff(S¹)` is a Lie
group ([GN26, Proposition 13.1.10(e)]), and so is its identity component `Diff⁺(S¹)`, the group
of orientation preserving diffeomorphisms ([GN26, §13.3]). Their Lie algebra is the Lie algebra
`V(S¹)` of vector fields on the circle with the opposite bracket ([GN26, Example 5.4.3]).

## Main definitions

* `UnitCircle`: the unit circle of `ℝ²`, with its manifold structure.
* `DiffCircle`: the Lie group `Diff(S¹)`.
* `DiffPlusCircle`: its identity component `Diff⁺(S¹)`, an open subgroup and a Lie group.

## Main results

* `DiffPlusCircle.toField_lie`: **`L(Diff⁺(S¹)) ≅ V(S¹)^op`**: through `L(Diff⁺(S¹)) ≅ L(Diff(S¹))`
  and the identification of the model space with vector fields, `[x, y] = [Y, X]`.

## Implementation notes

* We define `Diff⁺(S¹)` as the identity component of `Diff(S¹)`, which [GN26, §13.3] identifies
  with the group of orientation preserving diffeomorphisms; orientations are not formalized.
* [GN26, §13.3] describes the universal covering group `\widetilde{Diff}⁺(S¹)` by the global chart
  `u ↦ id + u` on `{u ∈ C^∞_{2π} : u' > −1}` (lc-manifolds, `DiffCircle.Ω`, with period `1`);
  that this chart makes it a Lie group is not formalized here.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups

/-- The unit vector `e₀ = (1, 0)` of `ℝ²`. -/
def circleBase : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1

theorem norm_circleBase : ‖circleBase‖ = 1 := by
  simp [circleBase]

/-- The model space of the circle, the line `e₀^⊥ ⊆ ℝ²`. -/
abbrev CircleModel : Type := (ℝ ∙ circleBase)ᗮ

/-- **The unit circle** `S¹ ⊆ ℝ²`. -/
def UnitCircle : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1

namespace UnitCircle

instance : TopologicalSpace UnitCircle :=
  inferInstanceAs (TopologicalSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))

instance : CompactSpace UnitCircle :=
  inferInstanceAs (CompactSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))

instance : T2Space UnitCircle :=
  inferInstanceAs (T2Space (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))

instance : ChartedSpace CircleModel UnitCircle :=
  (isEmbeddedSubmanifold_sphere norm_circleBase).chartedSpace

instance : MBManifold CircleModel UnitCircle :=
  (isEmbeddedSubmanifold_sphere norm_circleBase).mbManifold

/-- The normalized local addition `Σ(p, w) = (p + w)/‖p + w‖` of the circle. -/
def localAddition : LocalAddition CircleModel UnitCircle :=
  sphereLocalAddition norm_circleBase

theorem isNormalized_localAddition : localAddition.IsNormalized :=
  isNormalized_sphereLocalAddition norm_circleBase

end UnitCircle

/-- **The Lie group `Diff(S¹)`** ([GN26, Proposition 13.1.10(e)]). -/
abbrev DiffCircle : Type := Diffeo UnitCircle.localAddition

/-- **The Lie group `Diff⁺(S¹)`**, the identity component of `Diff(S¹)` ([GN26, §13.3]). -/
abbrev DiffPlusCircle : OpenSubgroup DiffCircle :=
  MBLieGroup.identityComponent (DiffeoModel UnitCircle.localAddition) DiffCircle

example : MBLieGroup (DiffeoModel UnitCircle.localAddition) DiffPlusCircle := inferInstance

namespace DiffPlusCircle

/-- The vector field on `S¹` of an element of `L(Diff⁺(S¹))`. -/
def toField (x : MBLieGroup.LieAlg (DiffeoModel UnitCircle.localAddition) DiffPlusCircle) :
    UnitCircle → TangentBundle CircleModel UnitCircle :=
  Diffeo.toField UnitCircle.localAddition (OpenSubgroup.lieEquiv DiffPlusCircle x)

/-- **The Lie algebra of `Diff⁺(S¹)` is `V(S¹)` with the opposite bracket**
([GN26, Example 5.4.3]): `[x, y] = [Y, X]` for the vector fields `X`, `Y` of `x`, `y`. -/
theorem toField_lie
    (x y : MBLieGroup.LieAlg (DiffeoModel UnitCircle.localAddition) DiffPlusCircle) :
    toField ⁅x, y⁆ = lieBracket (toField y) (toField x) := by
  rw [toField, LieEquiv.map_lie]
  exact Diffeo.toField_lie UnitCircle.localAddition UnitCircle.isNormalized_localAddition _ _

end DiffPlusCircle

end LocallyConvex.LieGroups
