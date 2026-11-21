/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.LieGroup.Basic
public import LocallyConvexLieGroups.LieAlgebra.Local
public import Mathlib.Algebra.Lie.Basic

/-!
# The Lie algebra of a Lie group

The Lie algebra `L(G)` of a Lie group `G` modeled on `E` is the tangent space `T_1 G`, which the
chart `φ` of `G` at the identity identifies with `E`, with the bracket `[x, y] = [x_l, y_l](1)`
of the left invariant vector fields with values `x`, `y` at the identity
([GN26, Definition 5.1.6]). In the chart `φ` this bracket is
`[x, y] = dỹ_l(φ(1)) x − dx̃_l(φ(1)) y` ([GN26, (5.5)]), where `x̃_l(z) = d(b ↦ z ∗ b)(φ(1)) x` and
`z ∗ b = φ(φ⁻¹(z) φ⁻¹(b))` is the multiplication of `G` in the chart. We take this as the
definition of the bracket on `E` (the local theory is in `LieAlgebra/Local.lean`).

## Main definitions

* `MBLieGroup.localGroupLaw E G`: the multiplication of `G` in the chart at the identity.
* `MBLieGroup.LieAlg E G`: the Lie algebra `L(G)`, a type synonym for `E`, with instances
  `LieRing` and `LieAlgebra ℝ`.
* `MBLieGroup.IsHom.lieHom`: the Lie algebra homomorphism `L(φ) = T_1(φ)` of a morphism of Lie
  groups `φ` ([GN26, Proposition 5.1.10]).

## Main results

* `MBLieGroup.LieAlg.continuous_lie`: the bracket of `L(G)` is continuous
  ([GN26, Definition 5.1.6]).
* `MBLieGroup.IsHom.lieHom`, `MBLieGroup.IsHom.continuous_lieHom`: `L(φ)` is a continuous
  homomorphism of Lie algebras ([GN26, Proposition 5.1.10]).
* `MBLieGroup.IsHom.lieHom_id`, `MBLieGroup.IsHom.lieHom_comp`: `L` is a functor
  ([GN26, Corollary 5.1.11]).
* `MBLieGroup.LieAlg.lie_eq_zero_of_comm`: the Lie algebra of an abelian Lie group is abelian
  ([GN26, Example 5.1.9(a)]).

## Implementation notes

The definition depends on the chart at the identity, `chartAt E 1`, which is fixed by the
manifold structure. That the bracket agrees with the bracket of the global left invariant vector
fields on `G` (lc-manifolds, `lieBracket`) is proved in `LieAlgebra/LeftInvariant.lean`
(`MBLieGroup.lieBracket_leftField`).

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

namespace MBLieGroup

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]

/-! ### The multiplication in the chart at the identity -/

section LocalLaw

variable (E G)

/-- The domain of the multiplication in the chart `φ` at the identity: the pairs `(a, b)` of
points of `φ(U)` with `φ⁻¹(a) φ⁻¹(b) ∈ U`. -/
def chartMulDom : Set (E × E) :=
  ((chartAt E (1 : G)).target ×ˢ (chartAt E (1 : G)).target) ∩
    (fun p : E × E ↦ (chartAt E (1 : G)).symm p.1 * (chartAt E (1 : G)).symm p.2) ⁻¹'
      (chartAt E (1 : G)).source

/-- The multiplication `a ∗ b = φ(φ⁻¹(a) φ⁻¹(b))` in the chart `φ` at the identity. -/
def chartMul (p : E × E) : E :=
  chartAt E (1 : G) ((chartAt E (1 : G)).symm p.1 * (chartAt E (1 : G)).symm p.2)

theorem isOpen_chartMulDom : IsOpen (chartMulDom E G) := by
  have := isTopologicalGroup E G
  set φ := chartAt E (1 : G)
  have hc : ContinuousOn (fun p : E × E ↦ φ.symm p.1 * φ.symm p.2) (φ.target ×ˢ φ.target) :=
    continuous_mul.comp_continuousOn
      ((φ.continuousOn_symm.comp continuousOn_fst
        fun _ (hp : _ ∈ φ.target ×ˢ φ.target) ↦ hp.1).prodMk
        (φ.continuousOn_symm.comp continuousOn_snd
          fun _ (hp : _ ∈ φ.target ×ˢ φ.target) ↦ hp.2))
  exact hc.isOpen_inter_preimage (φ.open_target.prod φ.open_target) φ.open_source

theorem smoothMBOn_chartMul : SmoothMBOn (chartMul E G) (chartMulDom E G) := by
  intro k
  have hk := (smoothMBM_mul (E := E) (G := G) k).2 ((1 : G), (1 : G)) (mem_univ _)
  simp only [_root_.mul_one] at hk
  refine ContDiffMBOn.congr_of_isOpen (isOpen_chartMulDom E G) (fun _ _ ↦ rfl) (hk.mono ?_)
  intro p hp
  exact ⟨hp.1, mem_univ _, hp.2⟩

/-- **The multiplication of `G` in the chart at the identity**, a smooth local group law
([GN26, Remark 5.1.8]). -/
def localGroupLaw : LocalGroupLaw E where
  mul := chartMul E G
  dom := chartMulDom E G
  one := chartAt E (1 : G) 1
  isOpen_dom := isOpen_chartMulDom E G
  one_one_mem := by
    have h1 := mem_chart_source E (1 : G)
    refine ⟨⟨(chartAt E (1 : G)).map_source h1, (chartAt E (1 : G)).map_source h1⟩, ?_⟩
    simp only [mem_preimage, (chartAt E (1 : G)).left_inv h1, _root_.mul_one]
    exact h1
  smooth := smoothMBOn_chartMul E G
  one_mul b hb := by
    simp only [chartMul, (chartAt E (1 : G)).left_inv (mem_chart_source E (1 : G)),
      _root_.one_mul, (chartAt E (1 : G)).right_inv hb.1.2]
  mul_one a ha := by
    simp only [chartMul, (chartAt E (1 : G)).left_inv (mem_chart_source E (1 : G)),
      _root_.mul_one, (chartAt E (1 : G)).right_inv ha.1.1]
  mul_assoc a b c hab hbc _ _ := by
    simp only [chartMul, (chartAt E (1 : G)).left_inv hab.2, (chartAt E (1 : G)).left_inv hbc.2,
      _root_.mul_assoc]

end LocalLaw

/-! ### The Lie algebra -/

variable (E G) in
/-- **The Lie algebra `L(G)`** of the Lie group `G` ([GN26, Definition 5.1.6]): the model space
`E`, identified with `T_1 G` by the chart at the identity, with the bracket
`[x, y] = [x_l, y_l](1)` of left invariant vector fields, computed in that chart
([GN26, (5.5)]). -/
@[nolint unusedArguments]
def LieAlg (E : Type u) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    (G : Type*) [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G] : Type u :=
  E

namespace LieAlg

instance : AddCommGroup (LieAlg E G) := inferInstanceAs (AddCommGroup E)

instance : Module ℝ (LieAlg E G) := inferInstanceAs (Module ℝ E)

instance : TopologicalSpace (LieAlg E G) := inferInstanceAs (TopologicalSpace E)

instance : IsTopologicalAddGroup (LieAlg E G) := inferInstanceAs (IsTopologicalAddGroup E)

instance : ContinuousSMul ℝ (LieAlg E G) := inferInstanceAs (ContinuousSMul ℝ E)

instance : LocallyConvexSpace ℝ (LieAlg E G) := inferInstanceAs (LocallyConvexSpace ℝ E)

instance : T2Space (LieAlg E G) := inferInstanceAs (T2Space E)

/-- The identification of `L(G)` with the model space `E`. -/
def toModel : LieAlg E G ≃ₗ[ℝ] E := LinearEquiv.refl ℝ E

instance : Bracket (LieAlg E G) (LieAlg E G) := ⟨(localGroupLaw E G).bracket⟩

theorem lie_def (x y : LieAlg E G) : ⁅x, y⁆ = (localGroupLaw E G).bracket x y :=
  rfl

/-- `L(G)` is a Lie ring: the bracket is biadditive, alternating, and satisfies the Jacobi
identity. -/
instance : LieRing (LieAlg E G) where
  add_lie x y z := (localGroupLaw E G).add_bracket x y z
  lie_add x y z := (localGroupLaw E G).bracket_add x y z
  lie_self x := (localGroupLaw E G).bracket_self x
  leibniz_lie x y z := by
    set L := localGroupLaw E G
    have J := L.bracket_jacobi x y z
    have h1 : L.bracket (L.bracket x y) z = -L.bracket z (L.bracket x y) :=
      L.bracket_swap z (L.bracket x y)
    have h2 : L.bracket y (L.bracket x z) = -L.bracket y (L.bracket z x) := by
      rw [L.bracket_swap z x]
      exact L.bracket_neg y _
    change L.bracket x (L.bracket y z) = L.bracket (L.bracket x y) z + L.bracket y (L.bracket x z)
    rw [h1, h2, ← sub_eq_zero, ← J]
    abel

/-- **`L(G)` is a real Lie algebra** ([GN26, Definition 5.1.6]). -/
instance : LieAlgebra ℝ (LieAlg E G) where
  lie_smul c x y := (localGroupLaw E G).bracket_smul c x y

/-- **The bracket of `L(G)` is continuous** ([GN26, Definition 5.1.6]). -/
theorem continuous_lie : Continuous fun p : LieAlg E G × LieAlg E G ↦ ⁅p.1, p.2⁆ :=
  (localGroupLaw E G).continuous_bracket

/-- **The Lie algebra of an abelian Lie group is abelian** ([GN26, Example 5.1.9(a)]). -/
theorem lie_eq_zero_of_comm (hc : ∀ a b : G, a * b = b * a) (x y : LieAlg E G) : ⁅x, y⁆ = 0 := by
  refine (localGroupLaw E G).bracket_eq_zero_of_comm (fun a b hab ↦ ⟨⟨⟨hab.1.2, hab.1.1⟩, ?_⟩, ?_⟩)
    x y
  · change (chartAt E (1 : G)).symm b * (chartAt E (1 : G)).symm a ∈ (chartAt E (1 : G)).source
    rw [hc]
    exact hab.2
  · change chartMul E G (b, a) = chartMul E G (a, b)
    simp only [chartMul, hc ((chartAt E (1 : G)).symm b)]

end LieAlg

/-! ### Morphisms -/

variable {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {H : Type*} [Group H] [TopologicalSpace H] [ChartedSpace F H] [MBLieGroup F H]

namespace IsHom

/-- The local representative of a map `G → H` in the charts at the identities. -/
def localRep (φ : G →* H) : E → F :=
  chartAt F (1 : H) ∘ φ ∘ (chartAt E (1 : G)).symm

/-- The domain of `localRep φ`. -/
def localRepDom (φ : G →* H) : Set E :=
  chartDomain φ univ (chartAt E (1 : G)) (chartAt F (1 : H))

variable {φ : G →* H} (hφ : IsHom E F φ)
include hφ

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  [T2Space F] [MBLieGroup F H] in
theorem isOpen_localRepDom : IsOpen (localRepDom (E := E) (F := F) φ) :=
  isOpen_chartDomain isOpen_univ (hφ 0).1 _ _

omit hφ [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [MBLieGroup E G] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [MBLieGroup F H] in
theorem one_mem_localRepDom : chartAt E (1 : G) 1 ∈ localRepDom (E := E) (F := F) φ := by
  have h1 := mem_chart_source E (1 : G)
  refine ⟨(chartAt E (1 : G)).map_source h1, mem_univ _, ?_⟩
  simp only [mem_preimage, (chartAt E (1 : G)).left_inv h1, map_one]
  exact mem_chart_source F (1 : H)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  [T2Space F] [MBLieGroup F H] in
theorem smoothMBOn_localRep :
    SmoothMBOn (localRep (E := E) (F := F) φ) (localRepDom (E := E) (F := F) φ) := by
  intro k
  have hk := (hφ k).2 1 (mem_univ _)
  rw [map_one] at hk
  exact hk

omit hφ [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [MBLieGroup E G] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [MBLieGroup F H] in
theorem localRep_one :
    localRep (E := E) (F := F) φ (chartAt E (1 : G) 1) = chartAt F (1 : H) 1 := by
  simp [localRep, (chartAt E (1 : G)).left_inv (mem_chart_source E (1 : G))]

/-- **The Lie algebra homomorphism** `L(φ) = T_1(φ) : L(G) → L(H)` of a morphism of Lie groups,
the derivative at the identity in the charts at the identities ([GN26, Proposition 5.1.10]). -/
def lieHom : LieAlg E G →ₗ⁅ℝ⁆ LieAlg F H where
  toFun x := dMB (localRep (E := E) (F := F) φ) (chartAt E (1 : G) 1, x)
  map_add' := ((hφ.smoothMBOn_localRep) 1).dMB_add hφ.isOpen_localRepDom one_mem_localRepDom
  map_smul' c x := ((hφ.smoothMBOn_localRep) 1).dMB_smul one_mem_localRepDom c x
  map_lie' {x y} := by
    refine (localGroupLaw E G).dMB_bracket_of_hom (localGroupLaw F H) hφ.isOpen_localRepDom
      one_mem_localRepDom (hφ.smoothMBOn_localRep 2) localRep_one ?_ x y
    intro a b hab ha _ _ _
    simp only [localGroupLaw, chartMul, localRep, Function.comp_apply,
      (chartAt E (1 : G)).left_inv hab.2, map_mul, (chartAt F (1 : H)).left_inv ha.2.2]
    rw [(chartAt F (1 : H)).left_inv]
    exact ‹b ∈ localRepDom φ›.2.2

theorem lieHom_apply (x : LieAlg E G) :
    hφ.lieHom x = dMB (localRep (E := E) (F := F) φ) (chartAt E (1 : G) 1, x) :=
  rfl

/-- **`L(φ)` is continuous** ([GN26, Proposition 5.1.10]). -/
theorem continuous_lieHom : Continuous hφ.lieHom :=
  ((hφ.smoothMBOn_localRep) 1).continuous_dMB one_mem_localRepDom

omit hφ in
/-- **`L(id) = id`** ([GN26, Corollary 5.1.11]). -/
theorem lieHom_id : (IsHom.id (E := E) (G := G)).lieHom = LieHom.id := by
  ext x
  rw [lieHom_apply, LieHom.id_apply]
  have h1 := mem_chart_source E (1 : G)
  have hev : localRep (E := E) (F := E) (MonoidHom.id G) =ᶠ[𝓝 (chartAt E (1 : G) 1)]
      fun z ↦ (ContinuousLinearMap.id ℝ E) z :=
    eventuallyEq_of_mem ((chartAt E (1 : G)).open_target.mem_nhds
      ((chartAt E (1 : G)).map_source h1)) fun z hz ↦ (chartAt E (1 : G)).right_inv hz
  exact (dMB_congr_of_eventuallyEq hev x).trans
    ((ContinuousLinearMap.id ℝ E).hasDirDerivAt _ x).dMB_eq

/-- **`L(ψ ∘ φ) = L(ψ) ∘ L(φ)`** ([GN26, Corollary 5.1.11]). -/
theorem lieHom_comp {D : Type u} [AddCommGroup D] [Module ℝ D] [TopologicalSpace D]
    [IsTopologicalAddGroup D] [ContinuousSMul ℝ D] [LocallyConvexSpace ℝ D] [T2Space D]
    {K : Type*} [Group K] [TopologicalSpace K] [ChartedSpace D K] [MBLieGroup D K]
    {ψ : H →* K} (hψ : IsHom F D ψ) : (hψ.comp hφ).lieHom = hψ.lieHom.comp hφ.lieHom := by
  ext x
  rw [LieHom.comp_apply, lieHom_apply, lieHom_apply, lieHom_apply,
    ← localRep_one (E := E) (F := F) (φ := φ)]
  set U := localRepDom (E := E) (F := F) φ ∩
    localRep (E := E) (F := F) φ ⁻¹' localRepDom (E := F) (F := D) ψ
  have hU : IsOpen U := ((hφ.smoothMBOn_localRep 0).continuousOn).isOpen_inter_preimage
    hφ.isOpen_localRepDom hψ.isOpen_localRepDom
  have h1U : chartAt E (1 : G) 1 ∈ U :=
    ⟨one_mem_localRepDom, by rw [mem_preimage, localRep_one]; exact one_mem_localRepDom⟩
  have hev : localRep (E := E) (F := D) (ψ.comp φ) =ᶠ[𝓝 (chartAt E (1 : G) 1)]
      localRep (E := F) (F := D) ψ ∘ localRep (E := E) (F := F) φ := by
    filter_upwards [hU.mem_nhds h1U] with z hz
    simp only [localRep, Function.comp_apply, MonoidHom.coe_comp]
    rw [(chartAt F (1 : H)).left_inv hz.1.2.2]
  exact dMB_eq_comp_of_eventuallyEq hψ.isOpen_localRepDom (hψ.smoothMBOn_localRep 1)
    ((hφ.smoothMBOn_localRep 1).mono inter_subset_left) (fun _ hz ↦ hz.2) h1U hev x

end IsHom

end MBLieGroup

end LocallyConvex.LieGroups
