/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.CircleCover.Rotation
public import LocallyConvexLieGroups.CircleCover.LieGroup
public import LocallyConvexLieGroups.Diffeomorphism.Circle
public import LocallyConvexLieGroups.LieGroup.OfVaryingAtlas
public import LocallyConvexManifolds.Manifold.CklProd

/-!
# The covering morphism `\widetilde{Diff}⁺(S¹) → Diff(S¹)`

The universal cover `\widetilde{Diff}⁺(S¹)`, in its global chart `Ω ⊆ C^∞_per`, acts on
`S¹ ⊆ ℝ²` by `act(u, e^{2πit}) = e^{2πi(t + u(t))}` (`CircleCover.rotU` restricted to the circle):
`u` acts as the diffeomorphism of `S¹ = ℝ/ℤ` induced by `id + u`. This action is smooth on
`C^∞_per × S¹`, and the exponential law for `C^∞(S¹, S¹)` (lc-manifolds,
`LocalAddition.contMDiffOn_mappingAtlasSm_iff`, together with `smoothMBM_iff_contMDiffMB₂`) makes
`u ↦ act(u, ·)` a smooth group morphism `\widetilde{Diff}⁺(S¹) → Diff(S¹)`.

We also prepare the local right inverse of `DiffCircleRegular.lean`: evaluation in the chart of
`Diff(S¹)` at the identity is jointly smooth (`smoothMBM_evalChart`), and the relative angle
`relAng` is smooth on `{(z, w) : z w̄ ∉ (-∞, 0]}`.

## Main definitions

* `CircleCover.act`: the action `\widetilde{Diff}⁺(S¹) × S¹ → S¹`.
* `CircleCover.coverHom`: the covering morphism `\widetilde{Diff}⁺(S¹) →* Diff(S¹)`.
* `CircleCover.φ1`, `CircleCover.gT`: the chart of `Diff(S¹)` at the identity and the
  diffeomorphism `γ_σ` with coordinate `σ`.

## Main results

* `CircleCover.smoothMBM_act`: the action is smooth.
* `CircleCover.act_mul`, `CircleCover.act_one`: it is an action.
* `CircleCover.isHom_coverHom`: **`coverHom` is a morphism of Lie groups.**
* `CircleCover.smoothMBM_evalChart`: `(σ, p) ↦ γ_σ(p)` is smooth.
* `CircleCover.smoothMBOn_of_opens_prod`: smoothness on `U × Y`, for `U` open in a vector space,
  from smoothness on the manifold `U × Y`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology ContDiff Real
open LocallyConvex.Analysis LocallyConvex.Manifolds CInfPer DiffCircle

noncomputable section

namespace LocallyConvex.LieGroups.CircleCover

theorem norm_circle (p : UnitCircle) : ‖(p.1 : R2)‖ = 1 := mem_sphere_zero_iff_norm.1 p.2

/-! ### The action of `\widetilde{Diff}⁺(S¹)` on the circle -/

/-- `(a, p) ↦ e^{2πi a(arg p/2π)} p`, the action of `id + a` on `S¹`. -/
def act (x : CoverGroup × UnitCircle) : UnitCircle :=
  show Metric.sphere (0 : R2) 1 from ⟨rotU ((x.1 : CInfPer), x.2.1), by
    rw [mem_sphere_zero_iff_norm, norm_rotU]; exact norm_circle x.2⟩

theorem act_coe (x : CoverGroup × UnitCircle) :
    ((act x).1 : R2) = rotU ((x.1 : CInfPer), x.2.1) := rfl

/-- **The action is smooth.** -/
theorem smoothMBM_act : SmoothMBM (ModelProd CInfPer CircleModel) CircleModel act := by
  have hemb := isEmbeddedSubmanifold_sphere norm_circleBase
  let := hemb.chartedSpace
  have := hemb.mbManifold
  refine hemb.isInitialSubmanifold_val.2.2 act fun k ↦ ?_
  have hΨ : ContMDiffMB (ModelProd CInfPer CircleModel) (ModelProd CInfPer R2) k
      (fun x : CoverGroup × UnitCircle ↦ ((x.1 : CInfPer), (x.2.1 : R2))) :=
    ContMDiffMBOn.prodMk isOpen_univ
      (((smoothMBM_subtype_val DiffCircle.Ω).comp smoothMBM_fst) k)
      ((hemb.smoothMBM_val.comp smoothMBM_snd) k)
  have hR : ContMDiffMBOn (E := ModelProd CInfPer R2) (F := R2) k rotU
      (univ ×ˢ {z : R2 | z ≠ 0}) := by
    refine ⟨(smoothMBOn_rotU 0).continuousOn, fun x _ ↦ ?_⟩
    refine ContDiffMBOn.congr_of_isOpen (isOpen_chartDomain (isOpen_univ.prod isOpen_ne)
      (smoothMBOn_rotU 0).continuousOn _ _) (fun _ _ ↦ rfl)
      ((smoothMBOn_rotU k).mono fun y hy ↦ hy.2.1)
  have h := ContMDiffMBOn.comp (g := rotU)
    (f := fun x : CoverGroup × UnitCircle ↦ ((x.1 : CInfPer), (x.2.1 : R2))) isOpen_univ
    (isOpen_univ.prod isOpen_ne) hR hΨ fun x _ ↦
      ⟨mem_univ _, fun h ↦ by
        have h1 := norm_circle x.2
        change (x.2.1 : R2) = 0 at h
        rw [h, norm_zero] at h1
        exact zero_ne_one h1⟩
  exact h

/-- `t ↦ e^{2πit}`, the covering map `ℝ → S¹`. -/
def circ (t : ℝ) : UnitCircle :=
  show Metric.sphere (0 : R2) 1 from ⟨J.symm (expC t), by
    rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]; exact norm_expC t⟩

theorem circ_ang (p : UnitCircle) : circ (ang (J p.1)) = p := by
  have h : ‖J p.1‖ = 1 := by rw [LinearIsometryEquiv.norm_map]; exact norm_circle p
  refine Subtype.ext ?_
  change J.symm (expC (ang (J p.1))) = p.1
  rw [expC_ang h, LinearIsometryEquiv.symm_apply_apply]

/-- **`id + a` acts on `S¹ = ℝ/ℤ`**: `act(a, e^{2πit}) = e^{2πi(t + a(t))}`. -/
theorem act_circ (a : CoverGroup) (t : ℝ) : act (a, circ t) = circ (lift a t) :=
  Subtype.ext (rotU_expC (a : CInfPer) t)

theorem act_one (p : UnitCircle) : act (1, p) = p := by
  rw [← circ_ang p, act_circ, CoverGroup.coe_one, CoverGroup.lift_zero]
  rfl

theorem act_mul (a b : CoverGroup) (p : UnitCircle) : act (a * b, p) = act (a, act (b, p)) := by
  rw [← circ_ang p, act_circ, act_circ, act_circ, CoverGroup.coe_mul, lift_comp]
  rfl

/-- `act(a, ·)` as a smooth map of the circle. -/
def qMap (a : CoverGroup) : SmoothMap CircleModel CircleModel UnitCircle UnitCircle :=
  ⟨fun p ↦ act (a, p), smoothMBM_act.comp fun k ↦ ContMDiffMBOn.prodMk isOpen_univ
    (smoothMBMOn_const univ a k) (smoothMBMOn_id isOpen_univ k)⟩

theorem qMap_apply (a : CoverGroup) (p : UnitCircle) : qMap a p = act (a, p) := rfl

theorem isDiffeo_qMap (a : CoverGroup) : (qMap a).IsDiffeo :=
  ⟨qMap a⁻¹, fun p ↦ by rw [qMap_apply, qMap_apply, ← act_mul, inv_mul_cancel, act_one],
    fun p ↦ by rw [qMap_apply, qMap_apply, ← act_mul, mul_inv_cancel, act_one]⟩

/-- **The covering morphism** `\widetilde{Diff}⁺(S¹) → Diff(S¹)`, `id + a ↦ act(a, ·)`. -/
def coverHom : CoverGroup →* DiffCircle where
  toFun a := show diffeos CircleModel UnitCircle from ⟨qMap a, isDiffeo_qMap a⟩
  map_one' := Subtype.ext (SmoothMap.ext act_one)
  map_mul' a b := Subtype.ext (SmoothMap.ext (act_mul a b))

theorem coverHom_apply (a : CoverGroup) (p : UnitCircle) :
    (show diffeos CircleModel UnitCircle from coverHom a).1 p = act (a, p) := rfl

/-- **The covering morphism is smooth for the atlas of `Diff(S¹)`**, by the exponential law. -/
theorem smooth_coverHom :
    (VaryingAtlas.ofChartedSpace CInfPer CoverGroup).Smooth
      (diffeoAtlas UnitCircle.localAddition)
      (fun a ↦ (show diffeos CircleModel UnitCircle from coverHom a)) := fun k ↦
  (VaryingAtlas.contMDiffOn_restrict_iff _ SmoothMap.isOpen_setOf_isDiffeo).2
    ((UnitCircle.localAddition.contMDiffOn_mappingAtlasSm_iff (g := qMap)).2 fun ℓ ↦
      (smoothMBM_act (k + ℓ)).contMDiffMB₂)

/-- **The covering morphism is a morphism of Lie groups.** -/
theorem isHom_coverHom : MBLieGroup.IsHom CInfPer (DiffeoModel UnitCircle.localAddition)
    coverHom :=
  (isVaryingLieGroup_diffeos UnitCircle.localAddition).smoothMBM_of_smooth smooth_coverHom

/-! ### A local right inverse in the chart at the identity -/

/-- The atlas of `Diff(S¹)`. -/
abbrev DA : VaryingAtlas (diffeos CircleModel UnitCircle) := diffeoAtlas UnitCircle.localAddition

/-- The model space of `Diff(S¹)`: vector fields on the circle, in fiber coordinates. -/
abbrev Mod : Type := DiffeoModel UnitCircle.localAddition

/-- The chart of `Diff(S¹)` at the identity. -/
abbrev φ1 : OpenPartialHomeomorph (diffeos CircleModel UnitCircle) Mod := DA.chart (DA.chartAt 1)

/-- The target of the chart at the identity, as an open set. -/
def TO : Opens Mod := ⟨φ1.target, φ1.open_target⟩

/-- The diffeomorphism with coordinates `s`. -/
def gT (s : TO) : SmoothMap CircleModel CircleModel UnitCircle UnitCircle :=
  (φ1.symm s : diffeos CircleModel UnitCircle).1

theorem smooth_gT :
    (VaryingAtlas.ofChartedSpace Mod TO).Smooth UnitCircle.localAddition.mappingAtlasSm gT := by
  have h1 : (VaryingAtlas.ofChartedSpace Mod TO).Smooth (VaryingAtlas.ofChartedSpace Mod Mod)
      Subtype.val := fun k ↦
    (VaryingAtlas.contMDiffOn_ofChartedSpace_iff isOpen_univ).2 (smoothMBM_subtype_val TO k)
  have h2 := VaryingAtlas.smoothOn_chart_symm DA (DA.chartAt 1)
  have h3 := VaryingAtlas.smooth_val UnitCircle.localAddition.mappingAtlasSm
    (SmoothMap.isOpen_setOf_isDiffeo (H := CircleModel) (K := UnitCircle))
  exact h3.comp (VaryingAtlas.SmoothOn.comp isOpen_univ φ1.open_target h2 h1 fun s _ ↦ s.2)

/-- **Evaluation in the chart at the identity is smooth**, jointly. -/
theorem smoothMBM_evalChart :
    SmoothMBM (ModelProd Mod CircleModel) CircleModel (fun x : TO × UnitCircle ↦ gT x.1 x.2) :=
  smoothMBM_iff_contMDiffMB₂.2 fun k ℓ ↦
    (UnitCircle.localAddition.contMDiffOn_mappingAtlasSm_iff (g := gT)).1 (smooth_gT k) ℓ

/-- Smoothness on `U × Y`, for `U` open in a vector space, from smoothness on the manifold
`U × Y`: in the charts, the local representatives are the map itself. -/
theorem smoothMBOn_of_opens_prod {X Y Z : Type} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X]
    [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y] [T2Space Y]
    [AddCommGroup Z] [Module ℝ Z] [TopologicalSpace Z]
    [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z] [LocallyConvexSpace ℝ Z] [T2Space Z]
    (U : Opens X) {f : X × Y → Z}
    (hf : SmoothMBM (ModelProd X Y) Z (fun x : U × Y ↦ f ((x.1 : X), x.2))) :
    SmoothMBOn f ((U : Set X) ×ˢ univ) := by
  intro k
  refine ContDiffMBOn.of_local (U.2.prod isOpen_univ) fun p hp ↦ ?_
  set x : U × Y := (⟨p.1, hp.1⟩, p.2)
  set e := chartAt (ModelProd X Y) x
  have hg : Continuous fun x : U × Y ↦ f ((x.1 : X), x.2) := continuousOn_univ.1 (hf 0).1
  set D := chartDomain (fun x : U × Y ↦ f ((x.1 : X), x.2)) univ e (chartAt Z (f p))
  have hD : IsOpen D := isOpen_chartDomain isOpen_univ hg.continuousOn _ _
  have hne : Nonempty U := ⟨⟨p.1, hp.1⟩⟩
  have hsymm : ∀ a ∈ D, ((e.symm a).1 : X) = a.1 ∧ (e.symm a).2 = a.2 := fun a ha ↦ by
    have h1 : a.1 ∈ ((OpenPartialHomeomorph.refl X).subtypeRestr hne).target := ha.1.1
    exact ⟨(OpenPartialHomeomorph.refl X).subtypeRestr_symm_apply hne h1, rfl⟩
  have hDU : D ⊆ (U : Set X) ×ˢ univ := fun a ha ↦ by
    have h1 := e.map_target ha.1
    refine ⟨?_, mem_univ _⟩
    rw [← (hsymm a ha).1]
    exact (e.symm a).1.2
  have hpD : p ∈ D := by
    have hex : e x = p := rfl
    rw [← hex]
    refine ⟨e.map_source (mem_chart_source _ x), mem_univ _, ?_⟩
    rw [mem_preimage, e.left_inv (mem_chart_source _ x)]
    exact mem_chart_source Z _
  refine ⟨D, hD, hpD, ?_⟩
  refine ((hf k).2 x (mem_univ _) |>.congr_of_isOpen hD fun a ha ↦ ?_).mono inter_subset_right
  change f ((e.symm a).1, (e.symm a).2) = f a
  rw [(hsymm a ha).1, (hsymm a ha).2]
  rfl

theorem smoothMBM_circ : SmoothMBM ℝ CircleModel circ := by
  have hemb := isEmbeddedSubmanifold_sphere norm_circleBase
  let := hemb.chartedSpace
  have := hemb.mbManifold
  refine hemb.isInitialSubmanifold_val.2.2 circ fun k ↦ ?_
  have h : ContDiff ℝ ∞ fun t ↦ J.symm (expC t) := contDiff_J_symm.comp contDiff_expC
  exact (contMDiffMBOn_iff_contDiffMBOn isOpen_univ).2
    ((smoothMBOn_iff_contDiffOn isOpen_univ).2 h.contDiffOn k)

theorem circ_add_one (t : ℝ) : circ (t + 1) = circ t := by
  refine Subtype.ext ?_
  change J.symm (expC (t + 1)) = J.symm (expC t)
  rw [expC_add, show expC 1 = 1 by
    rw [expC, mul_one, show ((2 * π : ℝ) : ℂ) * Complex.I = 2 * π * Complex.I by push_cast; ring,
      Complex.exp_two_pi_mul_I], mul_one]

/-- The domain of `relAng`. -/
def relDom : Set (R2 × R2) := {p | J p.1 * starRingEnd ℂ (J p.2) ∈ Complex.slitPlane}

theorem isOpen_relDom : IsOpen relDom :=
  Complex.isOpen_slitPlane.preimage ((J.continuous.comp continuous_fst).mul
    (Complex.continuous_conj.comp (J.continuous.comp continuous_snd)))

theorem re_J_mul_conj (z w : R2) : (J z * starRingEnd ℂ (J w)).re = inner ℝ z w := by
  rw [← J.inner_map_map, Complex.inner]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem contMDiffMBOn_relAng (k : ℕ) :
    ContMDiffMBOn (E := ModelProd R2 R2) (F := ℝ) k (fun p : R2 × R2 ↦ relAng p.1 p.2) relDom := by
  have hs : SmoothMBOn (fun p : R2 × R2 ↦ relAng p.1 p.2) relDom :=
    (smoothMBOn_iff_contDiffOn isOpen_relDom).2 contDiffOn_relAng
  refine ⟨(hs 0).continuousOn, fun x _ ↦ ?_⟩
  exact ContDiffMBOn.congr_of_isOpen (isOpen_chartDomain isOpen_relDom (hs 0).continuousOn _ _)
    (fun _ _ ↦ rfl) ((hs k).mono fun y hy ↦ hy.2.1)

end LocallyConvex.LieGroups.CircleCover
