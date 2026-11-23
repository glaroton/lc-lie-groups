/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Regular.Lift
public import LocallyConvexLieGroups.LieGroup.OpenSubgroup

/-!
# Regularity of open subgroups

An open subgroup `U` of a Lie group `G` is `C⁰`-regular if and only if `G` is. The inclusion
`U → G` is a morphism of Lie groups which is the identity in the charts at `1`, so both directions
of [GN26, Proposition 6.1.5] apply: `IsC0Regular.of_hom` with `L(incl) = id`, and
`IsC0Regular.of_localDiffeo` with the local inverse `g ↦ g` on `U`. In particular `G` is
`C⁰`-regular if and only if its identity component `G₀` is.

## Main results

* `MBLieGroup.isC0Regular_openSubgroup_iff`: **`U` is `C⁰`-regular iff `G` is.**
* `MBLieGroup.isC0Regular_identityComponent_iff`: **`G₀` is `C⁰`-regular iff `G` is.**

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups.MBLieGroup

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]
  (U : OpenSubgroup G)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
/-- The derivative of the identity. -/
theorem dMB_id_apply (x h : E) : dMB (fun y : E ↦ y) (x, h) = h :=
  HasDirDerivAt.dMB_eq <| tendsto_const_nhds.congr' <|
    eventually_nhdsWithin_of_forall fun t (ht : t ≠ 0) ↦ by
      simp [smul_smul, inv_mul_cancel₀ ht]

/-- The inclusion of an open subgroup, as a group homomorphism. -/
def openSubgroupIncl : U →* G where
  toFun := Subtype.val
  map_one' := rfl
  map_mul' _ _ := rfl

open scoped Classical in
/-- A left inverse of the inclusion `U → G`, equal to `g ↦ g` on `U`. -/
def openSubgroupRetr (g : G) : U := if h : g ∈ U then ⟨g, h⟩ else 1

omit [MBLieGroup E G] in
theorem openSubgroupRetr_of_mem {g : G} (hg : g ∈ U) : openSubgroupRetr U g = ⟨g, hg⟩ := by
  simp [openSubgroupRetr, hg]

omit [MBLieGroup E G] in
/-- The inclusion of an open subgroup is a morphism of Lie groups. -/
theorem isHom_openSubgroupIncl : IsHom E E (openSubgroupIncl U) :=
  smoothMBM_subtype_val (U : Opens G)

omit [LocallyConvexSpace ℝ E] [MBLieGroup E G] in
/-- In the charts at `1`, the inclusion `U → G` is the identity, so `L(incl) = id`. -/
theorem dMB_localRep_openSubgroupIncl (y : E) :
    dMB (IsHom.localRep (E := E) (F := E) (openSubgroupIncl U)) (chartAt E (1 : U) 1, y) = y := by
  set e := chartAt E (1 : G)
  have hev : IsHom.localRep (E := E) (F := E) (openSubgroupIncl U) =ᶠ[𝓝 (chartAt E (1 : U) 1)]
      fun z ↦ z := by
    filter_upwards [(chartAt E (1 : U)).open_target.mem_nhds (mem_chart_target E (1 : U))]
      with z hz
    have hne : Nonempty (U : Opens G) := ⟨⟨1, U.one_mem⟩⟩
    have hz' : z ∈ (e.subtypeRestr hne).target := hz
    have h1 : (((e.subtypeRestr hne).symm z : (U : Opens G)) : G) = e.symm z :=
      e.subtypeRestr_symm_apply hne hz'
    change e (((e.subtypeRestr hne).symm z : (U : Opens G)) : G) = z
    rw [h1, e.right_inv (e.subtypeRestr_target_subset hne hz')]
  rw [dMB_congr_of_eventuallyEq hev, dMB_id_apply]

omit [MBLieGroup E G] in
/-- `g ↦ g` is smooth on `U`, as a map `G → U`. -/
theorem smoothMBMOn_openSubgroupRetr : SmoothMBMOn E E (openSubgroupRetr U) (U : Set G) := by
  intro k
  have hcont : ContinuousOn (openSubgroupRetr U) (U : Set G) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : (U : Set G).domRestrict (openSubgroupRetr U) = fun g ↦ (⟨g.1, g.2⟩ : U) := by
      funext g; exact openSubgroupRetr_of_mem U g.2
    rw [this]
    exact continuous_subtype_val.subtype_mk _
  refine ⟨hcont, fun x hx ↦ ?_⟩
  set e := chartAt E x
  refine ContDiffMBOn.congr_of_isOpen (isOpen_chartDomain U.isOpen hcont _ _) (fun y hy ↦ ?_)
    ((smoothMBOn_id univ k).mono (subset_univ _))
  have hy1 : e.symm y ∈ (U : Set G) := hy.2.1
  change y = chartAt E (openSubgroupRetr U x) (openSubgroupRetr U (e.symm y))
  rw [openSubgroupRetr_of_mem U hx, openSubgroupRetr_of_mem U hy1]
  change y = e (e.symm y)
  rw [e.right_inv hy.1]

/-- **An open subgroup is `C⁰`-regular if and only if the group is.** -/
theorem isC0Regular_openSubgroup_iff : IsC0Regular E U ↔ IsC0Regular E G :=
  ⟨fun h ↦ h.of_hom (isHom_openSubgroupIncl U) (ContinuousLinearMap.id ℝ E)
      (dMB_localRep_openSubgroupIncl U),
    fun h ↦ h.of_localDiffeo (isHom_openSubgroupIncl U) isOpen_univ U.isOpen (mem_univ _)
      U.one_mem (smoothMBMOn_openSubgroupRetr U) (mapsTo_univ _ _)
      (fun g hg ↦ by simp [openSubgroupRetr_of_mem U hg, openSubgroupIncl])
      (fun g _ ↦ openSubgroupRetr_of_mem U g.2)⟩

variable (E G) in
/-- **The identity component `G₀` is `C⁰`-regular if and only if `G` is.** -/
theorem isC0Regular_identityComponent_iff :
    IsC0Regular E (identityComponent E G) ↔ IsC0Regular E G :=
  isC0Regular_openSubgroup_iff _

end LocallyConvex.LieGroups.MBLieGroup
