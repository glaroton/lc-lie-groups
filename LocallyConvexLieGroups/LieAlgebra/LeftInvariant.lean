/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.LieAlgebra.Basic
public import LocallyConvexManifolds.VectorField.Basic

/-!
# Left invariant vector fields

For `x ∈ L(G)`, the left invariant vector field `x_l(g) = T_1(λ_g) x` ([GN26, Definition 5.1.6])
is a vector field on `G` in the sense of lc-manifolds. We prove that the bracket of `L(G)`,
defined in `LieAlgebra/Basic.lean` in the chart at the identity, is the bracket of left
invariant vector fields: `[x_l, y_l] = [x, y]_l` ([GN26, (5.3)]), hence
`[x_l, y_l](1) = [x, y]`.

## Main definitions

* `MBLieGroup.leftField E x`: the left invariant vector field `x_l`.

## Main results

* `MBLieGroup.leftField_one`, `MBLieGroup.leftField_eq_tangentMap`: `x_l(1) = x` and
  `x_l(g) = T_1(λ_g) x`.
* `MBLieGroup.tangentMap_leftField`: left invariance, `T(λ_h) x_l(g) = x_l(h g)` ([GN26, (5.2)]).
* `MBLieGroup.localRep_leftField`: the local representative of `x_l` in the chart at `g`.
* **`MBLieGroup.lieBracket_leftField`**: `[x_l, y_l] = [x, y]_l` ([GN26, (5.3)]);
  `MBLieGroup.lieBracket_leftField_one`: `[x_l, y_l](1) = [x, y]` ([GN26, Definition 5.1.6]).

## Implementation notes

In the chart `ψ` at `g`, `x_l` reads `w ↦ d(b ↦ ψ(ψ⁻¹(w) φ⁻¹(b)))(φ 1) x`, with `φ` the chart at
the identity. The left translation `τ(b) = ψ(g φ⁻¹(b))`, from the chart at `1` to the chart at
`g`, relates the local fields `x̃_l` of `LieAlgebra/Local.lean` to these representatives
(associativity), so the transformation rule of local brackets (lc-manifolds,
`localBracket_transition`) gives `[x_l, y_l](g) = dτ(φ 1)[x, y] = [x, y]_l(g)`. This is the
related vector field lemma [GN26, Lemma 3.4.17] in the form needed here. It does not use the
smoothness of `x_l` on all of `G`.

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

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- The local bracket at `y` only depends on the germs of the two fields at `y`. -/
theorem localBracket_congr {A A' W W' : E → E} {y : E} (hA : A =ᶠ[𝓝 y] A')
    (hW : W =ᶠ[𝓝 y] W') : localBracket A W y = localBracket A' W' y := by
  rw [localBracket, localBracket, dMB_congr_of_eventuallyEq hA, dMB_congr_of_eventuallyEq hW,
    hA.eq_of_nhds, hW.eq_of_nhds]

/-! ### The multiplication in the charts at `g` and at the identity -/

section MixedChart

variable (E) (g : G)

/-- The domain of `mixedMul`. -/
def mixedDom : Set (E × E) :=
  ((chartAt E g).target ×ˢ (chartAt E (1 : G)).target) ∩
    (fun q : E × E ↦ (chartAt E g).symm q.1 * (chartAt E (1 : G)).symm q.2) ⁻¹'
      (chartAt E g).source

/-- The multiplication `(w, b) ↦ ψ(ψ⁻¹(w) φ⁻¹(b))` in the charts `ψ` at `g` and `φ` at the
identity. -/
def mixedMul (q : E × E) : E :=
  chartAt E g ((chartAt E g).symm q.1 * (chartAt E (1 : G)).symm q.2)

theorem isOpen_mixedDom : IsOpen (mixedDom E g) := by
  have := isTopologicalGroup E G
  set ψ := chartAt E g
  set φ := chartAt E (1 : G)
  have hc : ContinuousOn (fun q : E × E ↦ ψ.symm q.1 * φ.symm q.2) (ψ.target ×ˢ φ.target) :=
    continuous_mul.comp_continuousOn
      ((ψ.continuousOn_symm.comp continuousOn_fst
        fun _ (hq : _ ∈ ψ.target ×ˢ φ.target) ↦ hq.1).prodMk
        (φ.continuousOn_symm.comp continuousOn_snd
          fun _ (hq : _ ∈ ψ.target ×ˢ φ.target) ↦ hq.2))
  exact hc.isOpen_inter_preimage (ψ.open_target.prod φ.open_target) ψ.open_source

theorem smoothMBOn_mixedMul : SmoothMBOn (mixedMul E g) (mixedDom E g) := by
  intro k
  have hk := (smoothMBM_mul (E := E) (G := G) k).2 (g, (1 : G)) (mem_univ _)
  simp only [_root_.mul_one] at hk
  refine ContDiffMBOn.congr_of_isOpen (isOpen_mixedDom E g) (fun _ _ ↦ rfl) (hk.mono ?_)
  intro q hq
  exact ⟨hq.1, mem_univ _, hq.2⟩

end MixedChart

/-! ### Left invariant vector fields -/

variable (E) in
/-- **The left invariant vector field** `x_l(g) = T_1(λ_g) x` with value `x` at the identity
([GN26, Definition 5.1.6]), written in the preferred chart at `g`. -/
def leftField (x : LieAlg E G) (g : G) : TangentBundle E G :=
  ⟨g, dMB (chartAt E g ∘ (fun h ↦ g * h) ∘ (chartAt E (1 : G)).symm)
    (chartAt E (1 : G) 1, (x : E))⟩

theorem isVectorField_leftField (x : LieAlg E G) : IsVectorField (leftField E x) :=
  fun _ ↦ rfl

/-- **The local representative of `x_l` in the chart `ψ` at `g`** is
`w ↦ d(b ↦ ψ(ψ⁻¹(w) φ⁻¹(b)))(φ 1) x`. -/
theorem localRep_leftField (x : LieAlg E G) (g : G) {w : E} (hw : w ∈ (chartAt E g).target) :
    localRep ⟨chartAt E g, chart_mem_atlas E g⟩ (leftField E x) w =
      dMB (mixedMul E g) ((w, chartAt E (1 : G) 1), (0, (x : E))) := by
  set ψ := chartAt E g
  set φ := chartAt E (1 : G)
  set g' := ψ.symm w
  have hg' : g' ∈ ψ.source := ψ.map_target hw
  have hlam : ContMDiffMB E E 1 (fun h ↦ g' * h) := smoothMBM_mul_left g' 1
  have h := dMB_comp_chart hlam (chart_mem_atlas E (1 : G)) (chart_mem_atlas E g')
    (chart_mem_atlas E g) (mem_chart_source E (1 : G))
    (by rw [_root_.mul_one]; exact mem_chart_source E g') (by rw [_root_.mul_one]; exact hg') x
  simp only [_root_.mul_one] at h
  change dMB (ψ ∘ (chartAt E g').symm) (chartAt E g' g',
    dMB (chartAt E g' ∘ (fun h ↦ g' * h) ∘ φ.symm) (φ 1, (x : E))) = _
  rw [h]
  exact (dMB_slice₂ (mixedMul E g) w (φ 1) (x : E)).symm

/-- **The bracket of left invariant vector fields** ([GN26, Definition 5.1.6, (5.3)]):
`[x_l, y_l] = [x, y]_l`, where `[x, y]` is the bracket of `L(G)`. In particular
`[x_l, y_l](1) = [x, y]`: the bracket of `L(G)`, defined in the chart at the identity, is the
bracket of left invariant vector fields (`lieBracket_leftField_one`). -/
theorem lieBracket_leftField (x y : LieAlg E G) (g : G) :
    lieBracket (leftField E x) (leftField E y) g = leftField E ⁅x, y⁆ g := by
  set ψ := chartAt E g
  set φ := chartAt E (1 : G)
  set e := φ 1
  set L := localGroupLaw E G
  set F := mixedMul E g
  set DF := mixedDom E g
  have hF := smoothMBOn_mixedMul E g
  have hDF := isOpen_mixedDom E g
  have hg : g ∈ ψ.source := mem_chart_source E g
  have h1 : (1 : G) ∈ φ.source := mem_chart_source E (1 : G)
  have hφe : φ.symm e = 1 := φ.left_inv h1
  -- the fields `x_l` in the chart at `g`
  set Xψ : E → E → E := fun z w ↦ dMB F ((w, e), (0, z))
  set Ω : Set E := {w | (w, e) ∈ DF}
  have hΩ : IsOpen Ω := hDF.preimage (by fun_prop)
  have hXψ : ∀ (z : E) (k : ℕ), ContDiffMBOn k (Xψ z) Ω := fun z k ↦ by
    have hin : ContDiffMBOn k (fun w : E ↦ ((w, e), ((0 : E), z))) Ω :=
      ((smoothMBOn_id _ k).prodMk hΩ (contDiffMBOn_const k e _)).prodMk hΩ
        (contDiffMBOn_const k ((0 : E), z) _)
    exact ContDiffMBOn.comp (g := dMB F) hΩ (hDF.prod isOpen_univ) (hF (k + 1)).2.2 hin
      fun _ hw ↦ ⟨hw, mem_univ _⟩
  -- the left translation by `g`, from the chart at `1` to the chart at `g`
  set T : Set E := {b | (ψ g, b) ∈ DF}
  have hT : IsOpen T := hDF.preimage (by fun_prop)
  set τ : E → E := fun b ↦ F (ψ g, b)
  have hτ : ContDiffMBOn 2 τ T :=
    ContDiffMBOn.comp (g := F) (f := fun b ↦ (ψ g, b)) hT hDF (hF 2)
      ((contDiffMBOn_const 2 (ψ g) _).prodMk hT (smoothMBOn_id _ 2)) fun _ h ↦ h
  have heT : e ∈ T := by
    refine ⟨⟨ψ.map_source hg, φ.map_source h1⟩, ?_⟩
    change ψ.symm (ψ g) * φ.symm e ∈ ψ.source
    rw [ψ.left_inv hg, hφe, _root_.mul_one]
    exact hg
  have hτe : τ e = ψ g := by
    change ψ (ψ.symm (ψ g) * φ.symm e) = ψ g
    rw [ψ.left_inv hg, hφe, _root_.mul_one]
  -- `τ` relates the fields `x̃_l` in the chart at `1` to the fields in the chart at `g`
  have hrel : ∀ (z : E), ∀ b ∈ T ∩ L.domR, Xψ z (τ b) = dMB τ (b, L.xl z b) := by
    intro z b hb
    have hgb : ψ.symm (ψ g) * φ.symm b ∈ ψ.source := hb.1.2
    have key : ∀ b', (b, b') ∈ L.dom → F (τ b, b') = τ (L.mul (b, b')) := by
      intro b' hbb'
      change ψ (ψ.symm (ψ (ψ.symm (ψ g) * φ.symm b)) * φ.symm b') =
        ψ (ψ.symm (ψ g) * φ.symm (φ (φ.symm b * φ.symm b')))
      rw [ψ.left_inv hgb, φ.left_inv hbb'.2, _root_.mul_assoc]
    have hb1 : L.mul (b, L.one) = b := L.mul_one b hb.2
    set U' := L.domL b ∩ (fun b' ↦ L.mul (b, b')) ⁻¹' T
    have heU' : L.one ∈ U' := ⟨hb.2, by rw [mem_preimage, hb1]; exact hb.1⟩
    have hh : (fun b' ↦ F (τ b, b')) =ᶠ[𝓝 L.one] τ ∘ fun b' ↦ L.mul (b, b') :=
      eventuallyEq_of_mem ((L.isOpen_domL b).mem_nhds hb.2) fun b' hb' ↦ key b' hb'
    rw [show Xψ z (τ b) = dMB (fun b' ↦ F (τ b, b')) (e, z) from dMB_slice₂ F (τ b) e z,
      L.xl_eq]
    change dMB (fun b' ↦ F (τ b, b')) (L.one, z) = _
    rw [dMB_eq_comp_of_eventuallyEq hT (hτ.of_le (by norm_num))
      ((L.contDiffMBOn_mul_left 1 b).mono inter_subset_left) (fun _ h ↦ h.2) heU' hh z, hb1]
  have hU : IsOpen (T ∩ L.domR) := hT.inter L.isOpen_domR
  have heU : e ∈ T ∩ L.domR := ⟨heT, L.one_mem_domR⟩
  have hmaps : MapsTo τ (T ∩ L.domR) Ω := by
    intro b hb
    have hgb : ψ.symm (ψ g) * φ.symm b ∈ ψ.source := hb.1.2
    refine ⟨⟨ψ.map_source hgb, φ.map_source h1⟩, ?_⟩
    change ψ.symm (ψ (ψ.symm (ψ g) * φ.symm b)) * φ.symm e ∈ ψ.source
    rw [ψ.left_inv hgb, hφe, _root_.mul_one]
    exact hgb
  have htrans := localBracket_transition hT hU hΩ inter_subset_left hτ hmaps
    ((L.contDiffMBOn_xl 1 x).mono inter_subset_right)
    ((L.contDiffMBOn_xl 1 y).mono inter_subset_right) (hXψ x 1) (hXψ y 1) (hrel x) (hrel y) heU
  rw [hτe] at htrans
  -- the local representatives of `x_l` in the chart at `g` are the `Xψ x`
  have hloc : ∀ z : LieAlg E G, localRep ⟨ψ, chart_mem_atlas E g⟩ (leftField E z) =ᶠ[𝓝 (ψ g)]
      Xψ z :=
    fun z ↦ eventuallyEq_of_mem (ψ.open_target.mem_nhds (ψ.map_source hg)) fun w hw ↦
      localRep_leftField z g hw
  change (⟨g, (localBracket (localRep ⟨ψ, chart_mem_atlas E g⟩ (leftField E x))
    (localRep ⟨ψ, chart_mem_atlas E g⟩ (leftField E y)) (ψ g) : E)⟩ : TangentBundle E G) = _
  rw [localBracket_congr (hloc x) (hloc y), htrans]
  change (⟨g, (dMB (fun b ↦ ψ (ψ.symm (ψ g) * φ.symm b)) (e, L.bracket x y) : E)⟩ :
    TangentBundle E G) = ⟨g, (dMB (fun b ↦ ψ (g * φ.symm b)) (e, L.bracket x y) : E)⟩
  rw [ψ.left_inv hg]

/-- `x_l(1) = x`. -/
theorem leftField_one (x : LieAlg E G) : leftField E x 1 = ⟨1, (x : E)⟩ := by
  set φ := chartAt E (1 : G)
  have h1 : (1 : G) ∈ φ.source := mem_chart_source E (1 : G)
  have hev : (φ ∘ (fun h ↦ (1 : G) * h) ∘ φ.symm) =ᶠ[𝓝 (φ 1)]
      fun b ↦ (ContinuousLinearMap.id ℝ E) b :=
    eventuallyEq_of_mem (φ.open_target.mem_nhds (φ.map_source h1)) fun b hb ↦ by
      simp [φ.right_inv hb]
  change (⟨1, (dMB (φ ∘ (fun h ↦ (1 : G) * h) ∘ φ.symm) (φ 1, (x : E)) : E)⟩ :
    TangentBundle E G) = _
  refine congrArg (Bundle.TotalSpace.mk (F := E) (1 : G)) ?_
  exact (dMB_congr_of_eventuallyEq hev (x : E)).trans
    ((ContinuousLinearMap.id ℝ E).hasDirDerivAt _ _).dMB_eq

/-- **The bracket of `L(G)` is the bracket of left invariant vector fields at the identity**
([GN26, Definition 5.1.6]): `[x_l, y_l](1) = [x, y]`. -/
theorem lieBracket_leftField_one (x y : LieAlg E G) :
    lieBracket (leftField E x) (leftField E y) 1 = ⟨1, ((⁅x, y⁆ : LieAlg E G) : E)⟩ := by
  rw [lieBracket_leftField, leftField_one]

/-- `x_l(g) = T_1(λ_g) x` for the tangent map of lc-manifolds. -/
theorem leftField_eq_tangentMap (x : LieAlg E G) (g : G) :
    leftField E x g = tangentMap E E (fun h ↦ g * h) ⟨1, (x : E)⟩ := by
  have key : ∀ a : G, a = g → leftField E x g = (⟨a, (dMB (chartAt E a ∘ (fun h ↦ g * h) ∘
      (chartAt E (1 : G)).symm) (chartAt E (1 : G) 1, (x : E)) : E)⟩ : TangentBundle E G) := by
    rintro a rfl
    rfl
  exact key (g * 1) (_root_.mul_one g)

/-- **The fields `x_l` are left invariant** ([GN26, (5.2)]): `T(λ_h) x_l(g) = x_l(h g)`. -/
theorem tangentMap_leftField (x : LieAlg E G) (h g : G) :
    tangentMap E E (fun k ↦ h * k) (leftField E x g) = leftField E x (h * g) := by
  rw [leftField_eq_tangentMap, leftField_eq_tangentMap,
    tangentMap_comp (smoothMBM_mul_left h 1) (smoothMBM_mul_left g 1)]
  congr 1
  funext k
  exact (_root_.mul_assoc h g k).symm

end MBLieGroup

end LocallyConvex.LieGroups
