/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.LieAlgebra.Basic
public import LocallyConvexManifolds.Manifold.Product
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# Open subgroups of Lie groups

An open subgroup `U` of a Lie group `G` is a Lie group, with the restrictions of the charts of `G`
to `U` (Mathlib's charted space structure on `TopologicalSpace.Opens`). In particular the
identity component `G₀` is a Lie group: Lie groups are locally connected, since locally convex
spaces are, so `G₀` is open.

## Main results

* `smoothMBM_subtype_val`, `smoothMBM_of_val_comp`: for an open subset `s` of a manifold, the
  inclusion `s → M` is smooth, and a map into `s` is smooth when its composite with the inclusion
  is.
* `OpenSubgroup.instMBLieGroup`: **open subgroups of Lie groups are Lie groups**.
* `locallyConnectedSpace_of_locallyConvex`, `MBLieGroup.isOpen_connectedComponent_one`: locally
  convex spaces and Lie groups are locally connected, so the identity component is open.
* `MBLieGroup.identityComponent`: the identity component `G₀`, as an open subgroup.
* `OpenSubgroup.localGroupLaw_eq`, `OpenSubgroup.lie_eq`: in the charts at the identity, `U` and
  `G` have the same multiplication near the identity, hence the same Lie algebra.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter TopologicalSpace
open scoped Topology
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups

universe u

/-! ### Locally convex spaces are locally connected -/

/-- **Locally convex spaces are locally connected**: convex neighborhoods form a basis, and convex
sets are connected. -/
theorem locallyConnectedSpace_of_locallyConvex (E : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] : LocallyConnectedSpace E :=
  locallyConnectedSpace_of_connected_bases (fun _ (s : Set E) ↦ s) (fun x s ↦ s ∈ 𝓝 x ∧ Convex ℝ s)
    (fun x ↦ LocallyConvexSpace.convex_basis x) fun _ _ hs ↦ hs.2.isPreconnected

/-! ### Open subsets -/

section Opens

variable {E F G : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace G P]

/-- **The inclusion of an open subset is smooth**: in the restricted charts it is the identity. -/
theorem smoothMBM_subtype_val (s : Opens M) : SmoothMBM E E (Subtype.val : s → M) := by
  intro k
  refine ⟨continuous_subtype_val.continuousOn, fun x _ ↦ ?_⟩
  set e := chartAt E x.1
  refine ContDiffMBOn.congr_of_isOpen
    (isOpen_chartDomain isOpen_univ continuous_subtype_val.continuousOn _ _) (fun y hy ↦ ?_)
    ((smoothMBOn_id univ k).mono (subset_univ _))
  have hy' : y ∈ (e.subtypeRestr ⟨x⟩).target := hy.1
  change y = e ((Subtype.val ∘ (e.subtypeRestr ⟨x⟩).symm) y)
  rw [e.subtypeRestr_symm_apply ⟨x⟩ hy', e.right_inv (e.subtypeRestr_target_subset ⟨x⟩ hy')]

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G] in
/-- **A map into an open subset is smooth** if its composite with the inclusion is: the local
representatives in the restricted charts are the same. -/
theorem smoothMBM_of_val_comp (s : Opens N) {g : P → s}
    (hg : SmoothMBM G F (Subtype.val ∘ g)) : SmoothMBM G F g := by
  intro k
  refine ⟨(continuous_induced_rng.2 (continuousOn_univ.1 (hg k).1)).continuousOn,
    fun x _ ↦ ?_⟩
  have hD : chartDomain g univ (chartAt G x) (chartAt F (g x)) =
      chartDomain (Subtype.val ∘ g) univ (chartAt G x) (chartAt F ((Subtype.val ∘ g) x)) := by
    ext y
    simp [chartDomain, Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
  rw [hD]
  exact (hg k).2 x (mem_univ _)

end Opens

/-! ### Open subgroups -/

namespace OpenSubgroup

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]
  (U : OpenSubgroup G)

instance instChartedSpace : ChartedSpace E U := inferInstanceAs (ChartedSpace E (U : Opens G))

instance instHasGroupoid : HasGroupoid U (mbGroupoid E) :=
  inferInstanceAs (HasGroupoid (U : Opens G) (mbGroupoid E))

/-- **Open subgroups of Lie groups are Lie groups.** -/
instance instMBLieGroup : MBLieGroup E U where
  smoothMBM_mul := by
    have hval : SmoothMBM E E (Subtype.val : U → G) := smoothMBM_subtype_val (U : Opens G)
    have h : SmoothMBM (ModelProd E E) E (fun p : U × U ↦ (p.1 : G) * (p.2 : G)) :=
      (MBLieGroup.smoothMBM_mul (E := E) (G := G)).comp (fun k ↦ ContMDiffMBOn.prodMk
        isOpen_univ ((hval.comp smoothMBM_fst) k) ((hval.comp smoothMBM_snd) k))
    exact smoothMBM_of_val_comp (U : Opens G) (g := fun p : U × U ↦ (p.1 * p.2 : U)) h
  smoothMBM_inv := by
    have hval : SmoothMBM E E (Subtype.val : U → G) := smoothMBM_subtype_val (U : Opens G)
    have h : SmoothMBM E E (fun p : U ↦ (p : G)⁻¹) :=
      (MBLieGroup.smoothMBM_inv (E := E) (G := G)).comp hval
    exact smoothMBM_of_val_comp (U : Opens G) (g := fun p : U ↦ (p⁻¹ : U)) h

/-- In the charts at the identity, the multiplications of `U` and `G` agree on the domain of
that of `U`. -/
theorem localGroupLaw_eqOn :
    EqOn (MBLieGroup.localGroupLaw E U).mul (MBLieGroup.localGroupLaw E G).mul
      (MBLieGroup.localGroupLaw E U).dom := by
  rintro p ⟨⟨hp1, hp2⟩, -⟩
  set e := chartAt E (1 : G)
  have h1 : (((chartAt E (1 : U)).symm p.1 : U) : G) = e.symm p.1 :=
    e.subtypeRestr_symm_apply ⟨(1 : U)⟩ hp1
  have h2 : (((chartAt E (1 : U)).symm p.2 : U) : G) = e.symm p.2 :=
    e.subtypeRestr_symm_apply ⟨(1 : U)⟩ hp2
  change e (((chartAt E (1 : U)).symm p.1 * (chartAt E (1 : U)).symm p.2 : U) : G) =
    e (e.symm p.1 * e.symm p.2)
  rw [Subgroup.coe_mul, h1, h2]

/-- **An open subgroup has the Lie algebra of the group**: the brackets of `L(U)` and `L(G)`
agree (both are `E`, through the chart at the identity of `G`). -/
theorem lie_eq (x y : MBLieGroup.LieAlg E U) :
    MBLieGroup.LieAlg.toModel ⁅x, y⁆ = (MBLieGroup.localGroupLaw E G).bracket
      (MBLieGroup.LieAlg.toModel x) (MBLieGroup.LieAlg.toModel y) :=
  LocalGroupLaw.bracket_congr (MBLieGroup.localGroupLaw E U) (MBLieGroup.localGroupLaw E G) rfl
    (MBLieGroup.localGroupLaw E U).isOpen_dom (MBLieGroup.localGroupLaw E U).one_one_mem
    (localGroupLaw_eqOn U) _ _

/-- **`L(U) ≅ L(G)`** as Lie algebras. -/
def lieEquiv : MBLieGroup.LieAlg E U ≃ₗ⁅ℝ⁆ MBLieGroup.LieAlg E G :=
  { (MBLieGroup.LieAlg.toModel (E := E) (G := U)).trans
      (MBLieGroup.LieAlg.toModel (E := E) (G := G)).symm with
    map_lie' := fun {x y} ↦ lie_eq U x y }

end OpenSubgroup

/-! ### The identity component -/

namespace MBLieGroup

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]

include E in
omit [T2Space E] [Group G] [MBLieGroup E G] in
/-- Lie groups are locally connected. -/
theorem locallyConnectedSpace : LocallyConnectedSpace G :=
  haveI := locallyConnectedSpace_of_locallyConvex E
  ChartedSpace.locallyConnectedSpace E G

include E in
omit [T2Space E] [MBLieGroup E G] in
/-- The identity component of a Lie group is open. -/
theorem isOpen_connectedComponent_one : IsOpen (connectedComponent (1 : G)) :=
  haveI := locallyConnectedSpace (E := E) (G := G)
  isOpen_connectedComponent

variable (E G) in
/-- **The identity component `G₀`** of a Lie group, an open subgroup. -/
def identityComponent : OpenSubgroup G :=
  haveI := isTopologicalGroup E G
  { Subgroup.connectedComponentOfOne G with
    isOpen' := isOpen_connectedComponent_one (E := E) }

end MBLieGroup

end LocallyConvex.LieGroups
