/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.CircleCover.Periodic
public import LocallyConvexLieGroups.LieAlgebra.Taylor

/-!
# The group law of the universal cover of `Diff⁺(S¹)`

[GN26, §13.3] describes the universal covering group `\widetilde{Diff}⁺(S¹)` of `Diff⁺(S¹)` as the
group of diffeomorphisms `φ = id + u` of `ℝ` with `u` periodic, with the global chart `φ ↦ u`
(lc-manifolds, `DiffCircle`, with period `1`). In this chart the composition is
`m(u, w) = w + u ∘ (id + w)`, since `(id + u) ∘ (id + w) = id + (w + u ∘ (id + w))`. This formula
makes sense for all `u, w ∈ C^∞_per`, and it is associative with identity `0` there. By the
smoothness of the precomposition (`CInfPer.smoothMBOn_precomp`) it is a smooth global group law on
`C^∞_per` (`coverLaw`), whose bracket we compute:

  `[x, y] = x' y − x y'`.

For the vector fields `X = x ∂_θ`, `Y = y ∂_θ` on the circle, `[X, Y] = (x y' − x' y) ∂_θ`, so
this is the opposite bracket, in accordance with `L(Diff(S¹)) = V(S¹)^op`
([GN26, Example 5.4.3]).

## Main definitions

* `CircleCover.coverLaw`: the group law `m(u, w) = w + u ∘ (id + w)` on `C^∞_per`.

## Main results

* `CircleCover.coverLaw_xl`: the left invariant fields `x̃_l(z) = x + z' x`.
* `CircleCover.coverLaw_b2`: `b₂(x, y) = x' y`.
* `CircleCover.coverLaw_bracket`: **`[x, y] = x' y − x y'`**.

## Implementation notes

The group `\widetilde{Diff}⁺(S¹)` itself is the open subset `Ω = {u : 1 + u' > 0}` (lc-manifolds,
`DiffCircle.Ω`); the smoothness of its inversion `u ↦ (id + u)⁻¹ − id`, which would make it an
`MBLieGroup`, is not proved here. The bracket only depends on the multiplication near the
identity, so it is the bracket of the Lie algebra of `\widetilde{Diff}⁺(S¹)` in its global chart.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function
open scoped Topology
open LocallyConvex.Analysis LocallyConvex.Manifolds CInfPer

noncomputable section

namespace LocallyConvex.LieGroups.CircleCover

theorem comp_eq (u w : CInfPer) : DiffCircle.comp u w = w + precomp u w := by
  ext x; rfl

theorem precomp_zero (u : CInfPer) : precomp u 0 = u := by
  ext x; simp

theorem smoothMBOn_comp : SmoothMBOn (fun p : CInfPer × CInfPer ↦ DiffCircle.comp p.1 p.2) univ :=
  fun k ↦ ContDiffMBOn.congr_of_isOpen isOpen_univ (fun p _ ↦ (comp_eq p.1 p.2).symm)
    ((contDiffMBOn_clm k (ContinuousLinearMap.snd ℝ CInfPer CInfPer) fun _ ↦ rfl).add
      isOpen_univ (smoothMBOn_precomp k))

/-- **The group law of `\widetilde{Diff}⁺(S¹)` in its global chart** ([GN26, §13.3]):
`m(u, w) = w + u ∘ (id + w)`, the periodic part of `(id + u) ∘ (id + w)`. -/
def coverLaw : LocalGroupLaw CInfPer where
  mul p := DiffCircle.comp p.1 p.2
  dom := univ
  one := 0
  isOpen_dom := isOpen_univ
  one_one_mem := mem_univ _
  smooth := smoothMBOn_comp
  one_mul b _ := by ext x; simp [DiffCircle.comp]
  mul_one a _ := by ext x; simp [DiffCircle.comp, DiffCircle.lift]
  mul_assoc a b c _ _ _ _ := DiffCircle.lift_injective (by
    simp only [DiffCircle.lift_comp]; rfl)

/-- `d(b ↦ z ∗ b)` at `b = 0`. -/
theorem hasDirDerivAt_comp_left (z y : CInfPer) :
    HasDirDerivAt (fun b ↦ DiffCircle.comp z b) 0 y (y + mul (D z) y) := by
  have hp := hasDirDerivAt_precomp (z, 0) (0, y)
  have hs : HasDirDerivAt (fun p : CInfPer × CInfPer ↦ p.2) ((z, 0) : CInfPer × CInfPer) (0, y) y :=
    (ContinuousLinearMap.snd ℝ CInfPer CInfPer).hasDirDerivAt _ _
  have h := (hs.add hp)
  rw [hasDirDerivAt_slice₂] at h
  simp only [precomp_zero] at h
  rw [zero_add] at h
  have hf : (fun b ↦ DiffCircle.comp z b) = fun w ↦ w + precomp z w :=
    funext fun b ↦ comp_eq z b
  rw [hf]
  exact h

/-- **The left invariant fields of `\widetilde{Diff}⁺(S¹)`**: `x̃_l(z) = x + z' x`. -/
theorem coverLaw_xl (y z : CInfPer) : coverLaw.xl y z = y + mul (D z) y := by
  rw [LocalGroupLaw.xl_eq]
  exact (hasDirDerivAt_comp_left z y).dMB_eq

/-- **The second order term**: `b₂(x, y) = x' y`. -/
theorem coverLaw_b2 (x y : CInfPer) : coverLaw.b2 x y = mul (D x) y := by
  have hxl : coverLaw.xl y = fun z ↦ y + mul (D z) y := funext fun z ↦ coverLaw_xl y z
  rw [LocalGroupLaw.b2, hxl]
  refine HasDirDerivAt.dMB_eq ?_
  unfold HasDirDerivAt
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
  change mul (D x) y = t⁻¹ • ((y + mul (D (0 + t • x)) y) - (y + mul (D 0) y))
  rw [zero_add, map_smul, map_zero, mul_smul_left, add_sub_add_left_eq_sub]
  have h0 : mul 0 y = 0 := by ext; simp
  rw [h0, sub_zero, smul_smul, inv_mul_cancel₀ ht, one_smul]

/-- **The bracket of `\widetilde{Diff}⁺(S¹)`** in its global chart: `[x, y] = x' y − x y'`, the
opposite of the bracket of the vector fields `x ∂_θ`, `y ∂_θ`. -/
theorem coverLaw_bracket (x y : CInfPer) : coverLaw.bracket x y = mul (D x) y - mul (D y) x := by
  rw [LocalGroupLaw.bracket_eq_b2_sub_b2, coverLaw_b2, coverLaw_b2]

theorem coverLaw_bracket_apply (x y : CInfPer) (θ : ℝ) :
    coverLaw.bracket x y θ = deriv x θ * y θ - x θ * deriv y θ := by
  rw [coverLaw_bracket]
  simp only [coe_sub, Pi.sub_apply, coe_mul, D_apply, coe_deriv']
  ring

end LocallyConvex.LieGroups.CircleCover
