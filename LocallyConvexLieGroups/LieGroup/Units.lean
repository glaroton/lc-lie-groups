/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.LieAlgebra.Taylor
public import LocallyConvexAnalysis.Spaces.InverseAlgebra
public import Mathlib.Topology.Algebra.Group.Units

/-!
# Unit groups of continuous inverse algebras

Let `A` be a continuous inverse algebra: a unital locally convex algebra whose group of units
`A^×` is open and whose inversion is continuous ([GN26, Definition 5.1.3(a)]; lc-analysis,
`ContinuousInverseAlgebra`). Then `A^×` is a Lie group ([GN26, Example 5.1.4]) with the global
chart `φ(x) = x − 1`, in which the multiplication is `x ∗ y = (x + 1)(y + 1) − 1 = x + y + xy`;
the second order term of this multiplication is `b₂(x, y) = xy`, so that
`L(A^×) = (A, [·, ·])` with the commutator bracket `[x, y] = xy − yx`
([GN26, Example 5.1.9(b)]).

## Main definitions

* `quasiLaw A`: the local (in fact global) group law `x ∗ y = x + y + xy` with identity `0` on a
  (possibly non-unital) locally convex algebra `A` ([GN26, Definition 5.1.3(b)]).
* `UnitGroup A`: the group of units of `A`, a type synonym for `Aˣ`, with the charted space
  structure given by the single chart `unitChart u = u − 1`.

## Main results

* `quasiLaw_b2`, `quasiLaw_bracket`: `b₂(x, y) = xy` and `[x, y] = xy − yx`.
* `UnitGroup.instMBLieGroup`: **`A^×` is a Lie group** ([GN26, Example 5.1.4]); inversion is
  smooth by lc-analysis's `smoothMBOn_inverse` ([GN26, Corollary 1.3.8]).
* `UnitGroup.lie_eq`: **the Lie algebra of `A^×` is `A` with the commutator bracket**
  ([GN26, Example 5.1.9(b)]).

## Implementation notes

`UnitGroup A` is a type synonym for `Aˣ`: Mathlib already puts a charted space structure on the
units of a complete normed ring (`Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra`,
with the chart `u ↦ u`), and the chart `u ↦ u − 1` of [GN26] would give a second, different
instance on `Aˣ`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Topology
open scoped Topology Ring
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups

universe u

/-! ### Directional derivatives with constant difference quotients -/

section Aux

variable {X : Type*} [AddCommGroup X] [Module ℝ X] {F : Type*} [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F]

/-- If the difference quotients `t⁻¹ (f(x + t h) − f(x))` are all equal to `y`, then `y` is the
directional derivative. -/
theorem hasDirDerivAt_of_forall {f : X → F} {x h : X} {y : F}
    (hf : ∀ t : ℝ, t ≠ 0 → t⁻¹ • (f (x + t • h) - f x) = y) : HasDirDerivAt f x h y := by
  unfold HasDirDerivAt
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
  exact (hf t ht).symm

end Aux


/-! ### The quasi-multiplication `x ∗ y = x + y + xy` -/

section QuasiMul

variable (A : Type u) [NonUnitalRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
  [TopologicalSpace A] [IsTopologicalRing A] [ContinuousSMul ℝ A] [LocallyConvexSpace ℝ A]
  [T2Space A]

/-- The quasi-multiplication `x ∗ y = x + y + xy` ([GN26, Definition 5.1.3(b)]). -/
def quasiMul (p : A × A) : A := p.1 + p.2 + p.1 * p.2

variable {A}

omit [ContinuousSMul ℝ A] [LocallyConvexSpace ℝ A] [T2Space A] in
theorem continuous_mul_bilin : Continuous fun p : A × A ↦ LinearMap.mul ℝ A p.1 p.2 := by
  simp only [LinearMap.mul_apply']; exact continuous_fst.mul continuous_snd

omit [LocallyConvexSpace ℝ A] [T2Space A] in
theorem hasDirDerivAt_quasiMul (p q : A × A) :
    HasDirDerivAt (quasiMul A) p q (q.1 + q.2 + (p.1 * q.2 + q.1 * p.2)) := by
  have h := ((ContinuousLinearMap.fst ℝ A A + ContinuousLinearMap.snd ℝ A A).hasDirDerivAt p
    q).add (hasDirDerivAt_bilin (LinearMap.mul ℝ A) p q)
  simp only [FunLike.coe_add, Pi.add_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', LinearMap.mul_apply'] at h
  exact h

theorem smoothMBOn_quasiMul : SmoothMBOn (quasiMul A) univ := fun k ↦
  ContDiffMBOn.congr_of_isOpen isOpen_univ (fun _ _ ↦ by simp [quasiMul])
    (((ContinuousLinearMap.fst ℝ A A + ContinuousLinearMap.snd ℝ A A).contDiffMBOn k univ).add
      isOpen_univ (contDiffMBOn_bilin (LinearMap.mul ℝ A) continuous_mul_bilin k))

variable (A)

/-- **The quasi-multiplication as a local group law** with identity `0`, defined everywhere
([GN26, Definition 5.1.3(b)]). -/
def quasiLaw : LocalGroupLaw A where
  mul := quasiMul A
  dom := univ
  one := 0
  isOpen_dom := isOpen_univ
  one_one_mem := mem_univ _
  smooth := smoothMBOn_quasiMul
  one_mul b _ := by simp [quasiMul]
  mul_one a _ := by simp [quasiMul]
  mul_assoc a b c _ _ _ _ := by simp only [quasiMul]; noncomm_ring

variable {A}

theorem quasiLaw_xl (y z : A) : (quasiLaw A).xl y z = y + z * y := by
  have h := (hasDirDerivAt_quasiMul ((z, (0 : A))) ((0 : A), y)).dMB_eq
  simp only [zero_add, mul_zero, add_zero] at h
  exact h

/-- **The second order term of the quasi-multiplication** ([GN26, Example 5.1.9(b)]):
`b₂(x, y) = xy`. -/
theorem quasiLaw_b2 (x y : A) : (quasiLaw A).b2 x y = x * y := by
  have hxl : (quasiLaw A).xl y = fun z ↦ y + z * y := funext (quasiLaw_xl y)
  rw [LocalGroupLaw.b2, hxl]
  refine (hasDirDerivAt_of_forall fun t ht ↦ ?_).dMB_eq
  change t⁻¹ • (y + ((0 : A) + t • x) * y - (y + (0 : A) * y)) = x * y
  rw [zero_add, zero_mul, add_zero, add_sub_cancel_left, smul_mul_assoc, smul_smul,
    inv_mul_cancel₀ ht, one_smul]

/-- **The bracket of the quasi-multiplication is the commutator** ([GN26, Example 5.1.9(b)]). -/
theorem quasiLaw_bracket (x y : A) : (quasiLaw A).bracket x y = x * y - y * x := by
  rw [LocalGroupLaw.bracket_eq_b2_sub_b2, quasiLaw_b2, quasiLaw_b2]

end QuasiMul

/-! ### The unit group as a Lie group -/

section Units

variable (A : Type u) [Ring A]

/-- The group of units of `A`, a type synonym for `Aˣ` carrying the chart `u ↦ u − 1`. -/
@[nolint unusedArguments]
def UnitGroup (A : Type u) [Ring A] : Type u := Aˣ

namespace UnitGroup

instance : Group (UnitGroup A) := inferInstanceAs (Group Aˣ)

instance : Nonempty (UnitGroup A) := ⟨1⟩

variable {A}

/-- The underlying element of `A`. -/
def val (u : UnitGroup A) : A := Units.val (show Aˣ from u)

@[simp]
theorem val_mul (u v : UnitGroup A) : val (u * v) = val u * val v :=
  Units.val_mul (show Aˣ from u) (show Aˣ from v)

@[simp]
theorem val_one : val (1 : UnitGroup A) = 1 := Units.val_one (α := A)

theorem val_inv (u : UnitGroup A) : val u⁻¹ = (val u)⁻¹ʳ :=
  (Ring.inverse_unit (show Aˣ from u)).symm

theorem isUnit_val (u : UnitGroup A) : IsUnit (val u) := Units.isUnit (show Aˣ from u)

variable (A) [TopologicalSpace A] [IsTopologicalRing A]

instance : TopologicalSpace (UnitGroup A) := inferInstanceAs (TopologicalSpace Aˣ)

instance : IsTopologicalGroup (UnitGroup A) := inferInstanceAs (IsTopologicalGroup Aˣ)

variable [ContinuousInverseAlgebra A]

omit [IsTopologicalRing A] in
theorem isOpenEmbedding_val : IsOpenEmbedding (val : UnitGroup A → A) := by
  have h : IsOpenEmbedding (Units.val : Aˣ → A) :=
    ⟨Units.isEmbedding_val_mk' ContinuousInverseAlgebra.continuousOn_inverse
      fun u ↦ Ring.inverse_unit u, ContinuousInverseAlgebra.isOpen_units⟩
  exact h

/-- **The global chart** `u ↦ u − 1` ([GN26, Example 5.1.9(b)]). -/
def unitChart (u : UnitGroup A) : A := val u - 1

theorem isOpenEmbedding_unitChart : IsOpenEmbedding (unitChart A) :=
  (Homeomorph.subRight (1 : A)).isOpenEmbedding.comp (isOpenEmbedding_val A)

instance : ChartedSpace A (UnitGroup A) := (isOpenEmbedding_unitChart A).singletonChartedSpace

variable {A}

theorem coe_chartAt (u : UnitGroup A) : ⇑(chartAt A u) = unitChart A := rfl

theorem chartAt_eq (u v : UnitGroup A) : chartAt A u = chartAt A v := rfl

theorem mem_target_iff {a : A} (u : UnitGroup A) :
    a ∈ (chartAt A u).target ↔ IsUnit (a + 1) := by
  change a ∈ ((isOpenEmbedding_unitChart A).toOpenPartialHomeomorph (unitChart A)).target ↔ _
  rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
  constructor
  · rintro ⟨v, rfl⟩
    simpa [unitChart] using isUnit_val v
  · rintro ⟨w, hw⟩
    exact ⟨w, by simp [unitChart, val, hw]⟩

theorem val_chartAt_symm {a : A} (u : UnitGroup A) (ha : a ∈ (chartAt A u).target) :
    val ((chartAt A u).symm a) = a + 1 := by
  have h := (chartAt A u).right_inv ha
  rw [coe_chartAt, unitChart] at h
  exact eq_add_of_sub_eq h

/-- The chart is an open subset: `{a | a + 1 ∈ A^×}`. -/
theorem isOpen_unitsShift : IsOpen {a : A | IsUnit (a + 1)} :=
  ContinuousInverseAlgebra.isOpen_units.preimage (by fun_prop)

variable [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [ContinuousSMul ℝ A]
  [LocallyConvexSpace ℝ A] [T2Space A]

variable (A) in
instance : HasGroupoid (UnitGroup A) (mbGroupoid A) :=
  (isOpenEmbedding_unitChart A).singleton_hasGroupoid _

/-- The inversion in the chart, `a ↦ (a + 1)⁻¹ − 1`, is smooth. -/
theorem smoothMBOn_invChart :
    SmoothMBOn (fun a : A ↦ (a + 1)⁻¹ʳ - 1) {a : A | IsUnit (a + 1)} := fun k ↦
  ContDiffMBOn.sub isOpen_unitsShift
    (ContDiffMBOn.comp isOpen_unitsShift ContinuousInverseAlgebra.isOpen_units
      (contDiffMBOn_inverse k)
      ((smoothMBOn_id _ k).add isOpen_unitsShift (contDiffMBOn_const k 1 _)) fun _ ha ↦ ha)
    (contDiffMBOn_const k 1 _)

/-- **The unit group of a continuous inverse algebra is a Lie group** ([GN26, Example 5.1.4]). -/
instance instMBLieGroup : MBLieGroup A (UnitGroup A) where
  smoothMBM_mul k := by
    refine ⟨continuous_mul.continuousOn, fun x _ ↦ ?_⟩
    refine ContDiffMBOn.congr_of_isOpen
      (isOpen_chartDomain isOpen_univ continuous_mul.continuousOn _ _) (fun p hp ↦ ?_)
      ((smoothMBOn_quasiMul k).mono (subset_univ _))
    obtain ⟨⟨hp1, hp2⟩, -⟩ := hp
    change quasiMul A p = unitChart A ((chartAt A x.1).symm p.1 * (chartAt A x.2).symm p.2)
    rw [unitChart, val_mul, val_chartAt_symm _ hp1, val_chartAt_symm _ hp2, quasiMul]
    noncomm_ring
  smoothMBM_inv k := by
    refine ⟨continuous_inv.continuousOn, fun x _ ↦ ?_⟩
    refine ContDiffMBOn.congr_of_isOpen
      (isOpen_chartDomain isOpen_univ continuous_inv.continuousOn _ _) (fun a ha ↦ ?_)
      ((smoothMBOn_invChart k).mono fun a ha ↦ (mem_target_iff x).1 ha.1)
    change (a + 1)⁻¹ʳ - 1 = unitChart A ((chartAt A x).symm a)⁻¹
    rw [unitChart, val_inv, val_chartAt_symm _ ha.1]

/-! ### The Lie algebra -/

theorem localGroupLaw_one : (MBLieGroup.localGroupLaw A (UnitGroup A)).one = 0 := by
  change unitChart A 1 = 0
  simp [unitChart]

theorem localGroupLaw_mul_eqOn :
    EqOn (MBLieGroup.localGroupLaw A (UnitGroup A)).mul (quasiMul A)
      (MBLieGroup.localGroupLaw A (UnitGroup A)).dom := by
  rintro p ⟨⟨hp1, hp2⟩, -⟩
  change unitChart A ((chartAt A (1 : UnitGroup A)).symm p.1 *
    (chartAt A (1 : UnitGroup A)).symm p.2) = quasiMul A p
  rw [unitChart, val_mul, val_chartAt_symm _ hp1, val_chartAt_symm _ hp2, quasiMul]
  noncomm_ring

/-- **The Lie algebra of `A^×` is `A` with the commutator bracket** ([GN26, Example 5.1.9(b)]):
`[x, y] = xy − yx`. -/
theorem lie_eq (x y : MBLieGroup.LieAlg A (UnitGroup A)) :
    MBLieGroup.LieAlg.toModel ⁅x, y⁆ =
      MBLieGroup.LieAlg.toModel x * MBLieGroup.LieAlg.toModel y -
        MBLieGroup.LieAlg.toModel y * MBLieGroup.LieAlg.toModel x := by
  set L := MBLieGroup.localGroupLaw A (UnitGroup A)
  change L.bracket (MBLieGroup.LieAlg.toModel x) (MBLieGroup.LieAlg.toModel y) = _
  rw [LocalGroupLaw.bracket_congr L (quasiLaw A) localGroupLaw_one L.isOpen_dom L.one_one_mem
    localGroupLaw_mul_eqOn]
  exact quasiLaw_bracket _ _

end UnitGroup

end Units

end LocallyConvex.LieGroups
