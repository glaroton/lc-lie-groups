/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.LieGroup.Basic
public import LocallyConvexManifolds.Manifold.VaryingAtlasProd

/-!
# Lie groups from atlases with varying models

Groups of mappings, such as `Diff(K)`, come with atlases whose model spaces vary from chart to
chart (atlases with varying models, `VaryingAtlas`). If the multiplication and the inversion of a
group `G` are smooth for such an atlas `A`, then the translates `x ↦ φ(g⁻¹ x)` of a single chart
`φ` at the identity form an atlas modeled on one space, the model `E` of `φ`, and `G` is a Lie
group modeled on `E` in the sense of `MBLieGroup`. The charts `φ_g(x) = φ(g⁻¹ x)` are the ones of
the proof of [GN26, Theorem 5.3.1] (Lie groups from local data); here the manifold structure is
given on all of `G`, so the local hypotheses of that theorem are not needed.

## Main definitions

* `IsVaryingLieGroup A`: the multiplication and the inversion of `G` are smooth for `A`.
* `IsVaryingLieGroup.transChart`: the translated chart `x ↦ φ(g⁻¹ x)`.
* `IsVaryingLieGroup.chartedSpace`: the atlas of translated charts, modeled on the model of the
  chart of `A` at the identity.

## Main results

* `IsVaryingLieGroup.hasGroupoid`: the translated charts form a smooth atlas.
* `IsVaryingLieGroup.mbLieGroup`: with this atlas, `G` is a Lie group.

## Implementation notes

The transition maps of the translated charts are local representatives of left translations in
the chart `φ`, and the local representatives of the multiplication and of the inversion in
translated charts are local representatives in `φ` of maps built from the group operations and
translations; all of them are smooth because `A` makes the group operations smooth. The new atlas
need not be compatible with `A` charts-wise, but it defines the same smooth structure (this is not
needed here and not proved).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups

universe u

variable {G : Type*} [Group G] [TopologicalSpace G] (A : VaryingAtlas.{u, _, _} G)

/-- The multiplication and the inversion of the group `G` are smooth for the atlas with varying
models `A`. -/
structure IsVaryingLieGroup : Prop where
  /-- The multiplication is smooth. -/
  smooth_mul : (A.prod A).Smooth A (fun p : G × G ↦ p.1 * p.2)
  /-- The inversion is smooth. -/
  smooth_inv : A.Smooth A (fun g : G ↦ g⁻¹)

namespace IsVaryingLieGroup

variable {A} (hA : IsVaryingLieGroup A)
include hA

theorem continuous_mul : Continuous (fun p : G × G ↦ p.1 * p.2) :=
  continuousOn_univ.1 (hA.smooth_mul 0).1

theorem continuous_inv : Continuous (fun g : G ↦ g⁻¹) :=
  continuousOn_univ.1 (hA.smooth_inv 0).1

/-- Left translations are smooth. -/
theorem smooth_mul_left (g : G) : A.Smooth A (fun x ↦ g * x) :=
  hA.smooth_mul.comp (VaryingAtlas.Smooth.prodMk (VaryingAtlas.smoothOn_const A A g univ)
    (A.smoothOn_id univ))

/-- The maps `(p, q) ↦ c (a p) (b q)` are smooth. -/
theorem smooth_mul_translate (a b c : G) :
    (A.prod A).Smooth A (fun p : G × G ↦ c * ((a * p.1) * (b * p.2))) :=
  (hA.smooth_mul_left c).comp (hA.smooth_mul.comp
    (VaryingAtlas.Smooth.prodMk ((hA.smooth_mul_left a).comp (VaryingAtlas.smooth_fst A A))
      ((hA.smooth_mul_left b).comp (VaryingAtlas.smooth_snd A A))))

/-- The maps `p ↦ c (a p)⁻¹` are smooth. -/
theorem smooth_inv_translate (a c : G) : A.Smooth A (fun p : G ↦ c * (a * p)⁻¹) :=
  (hA.smooth_mul_left c).comp (hA.smooth_inv.comp (hA.smooth_mul_left a))

/-- The left translation `x ↦ g⁻¹ x`, as a homeomorphism. -/
def homeoTrans (g : G) : G ≃ₜ G where
  toFun x := g⁻¹ * x
  invFun y := g * y
  left_inv x := by simp
  right_inv y := by simp
  continuous_toFun := hA.continuous_mul.comp (continuous_const.prodMk continuous_id)
  continuous_invFun := hA.continuous_mul.comp (continuous_const.prodMk continuous_id)

/-- The chart at the identity. -/
abbrev chartOne : OpenPartialHomeomorph G (A.model (A.chartAt 1)) := A.chart (A.chartAt 1)

/-- **The translated chart** `x ↦ φ(g⁻¹ x)`, `φ` the chart of `A` at the identity. -/
def transChart (g : G) : OpenPartialHomeomorph G (A.model (A.chartAt 1)) :=
  (hA.homeoTrans g).toOpenPartialHomeomorph.trans (chartOne (A := A))

theorem transChart_apply (g x : G) : hA.transChart g x = chartOne (A := A) (g⁻¹ * x) :=
  rfl

theorem transChart_symm_apply (g : G) (a : A.model (A.chartAt 1)) :
    (hA.transChart g).symm a = g * (chartOne (A := A)).symm a :=
  rfl

theorem mem_transChart_source {g x : G} :
    x ∈ (hA.transChart g).source ↔ g⁻¹ * x ∈ (chartOne (A := A)).source := by
  simp [transChart, homeoTrans]

theorem transChart_target_subset (g : G) :
    (hA.transChart g).target ⊆ (chartOne (A := A)).target :=
  fun _ ha ↦ ha.1

/-- **The transition maps of translated charts are smooth**: they are local representatives of
left translations in the chart at the identity. -/
theorem smoothMBOn_transChart_trans (g h : G) :
    SmoothMBOn ((hA.transChart g).symm.trans (hA.transChart h))
      ((hA.transChart g).symm.trans (hA.transChart h)).source := by
  set φ := chartOne (A := A)
  set e := (hA.transChart g).symm.trans (hA.transChart h)
  have hrep := fun k ↦ (hA.smooth_mul_left (h⁻¹ * g) k).2 (A.chartAt 1) (A.chartAt 1)
  have hsub : e.source ⊆ chartDomain (fun x ↦ h⁻¹ * g * x) univ φ φ := by
    intro a ha
    simp only [e, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage, transChart_symm_apply, mem_transChart_source] at ha
    refine ⟨hA.transChart_target_subset g ha.1, mem_univ _, ?_⟩
    simpa [mul_assoc] using ha.2
  intro k
  refine ((hrep k).mono hsub).congr_of_isOpen e.open_source fun a _ ↦ ?_
  simp [e, transChart_apply, transChart_symm_apply, mul_assoc]

/-- **The atlas of translated charts**, modeled on the model of the chart of `A` at the
identity. -/
@[instance_reducible]
def chartedSpace : ChartedSpace (A.model (A.chartAt 1)) G where
  atlas := range hA.transChart
  chartAt := hA.transChart
  mem_chart_source g := by
    rw [mem_transChart_source, inv_mul_cancel]
    exact A.mem_chartAt_source 1
  chart_mem_atlas g := mem_range_self g

/-- **The translated charts form a smooth atlas.** -/
theorem hasGroupoid :
    letI := hA.chartedSpace
    HasGroupoid G (mbGroupoid (A.model (A.chartAt 1))) := by
  let := hA.chartedSpace
  refine ⟨?_⟩
  rintro _ _ ⟨g, rfl⟩ ⟨h, rfl⟩
  refine ⟨hA.smoothMBOn_transChart_trans g h, ?_⟩
  have := hA.smoothMBOn_transChart_trans h g
  rw [← OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm]
  exact this

/-- **A group with smooth operations for an atlas with varying models is a Lie group**, modeled on
the model of the chart at the identity, with the atlas of translated charts. -/
theorem mbLieGroup :
    letI := hA.chartedSpace
    MBLieGroup (A.model (A.chartAt 1)) G := by
  let := hA.chartedSpace
  have := hA.hasGroupoid
  set φ := chartOne (A := A)
  refine { smoothMBM_mul := ?_, smoothMBM_inv := ?_ }
  · intro k
    refine ⟨hA.continuous_mul.continuousOn, fun x _ ↦ ?_⟩
    set a := x.1
    set b := x.2
    have hrep := (hA.smooth_mul_translate a b (a * b)⁻¹ k).2 (A.chartAt 1, A.chartAt 1)
      (A.chartAt 1)
    have hsub : chartDomain (fun p : G × G ↦ p.1 * p.2) univ
        (chartAt (ModelProd (A.model (A.chartAt 1)) (A.model (A.chartAt 1))) x)
        (chartAt (A.model (A.chartAt 1)) (x.1 * x.2)) ⊆
        chartDomain (fun p : G × G ↦ (a * b)⁻¹ * ((a * p.1) * (b * p.2))) univ
          ((A.prod A).chart (A.chartAt 1, A.chartAt 1)) φ := by
      rintro ⟨u, v⟩ ⟨⟨hu, hv⟩, -, hs⟩
      refine ⟨⟨hA.transChart_target_subset a hu, hA.transChart_target_subset b hv⟩,
        mem_univ _, ?_⟩
      change (hA.transChart a).symm u * (hA.transChart b).symm v ∈
        (hA.transChart (a * b)).source at hs
      rw [mem_transChart_source, transChart_symm_apply, transChart_symm_apply] at hs
      exact hs
    refine ((hrep.mono hsub).congr_of_isOpen (isOpen_chartDomain isOpen_univ
      hA.continuous_mul.continuousOn _ _) fun _ _ ↦ rfl)
  · intro k
    refine ⟨hA.continuous_inv.continuousOn, fun a _ ↦ ?_⟩
    have hrep := (hA.smooth_inv_translate a (a⁻¹)⁻¹ k).2 (A.chartAt 1) (A.chartAt 1)
    have hsub : chartDomain (fun g : G ↦ g⁻¹) univ (chartAt (A.model (A.chartAt 1)) a)
        (chartAt (A.model (A.chartAt 1)) a⁻¹) ⊆
        chartDomain (fun p : G ↦ (a⁻¹)⁻¹ * (a * p)⁻¹) univ φ φ := by
      rintro u ⟨hu, -, hs⟩
      refine ⟨hA.transChart_target_subset a hu, mem_univ _, ?_⟩
      change ((hA.transChart a).symm u)⁻¹ ∈ (hA.transChart a⁻¹).source at hs
      rw [mem_transChart_source, transChart_symm_apply] at hs
      exact hs
    exact (hrep.mono hsub).congr_of_isOpen (isOpen_chartDomain isOpen_univ
      hA.continuous_inv.continuousOn _ _) fun _ _ ↦ rfl

end IsVaryingLieGroup

end LocallyConvex.LieGroups
