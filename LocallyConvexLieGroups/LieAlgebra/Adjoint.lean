/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.LieAlgebra.Morphisms
public import LocallyConvexLieGroups.LieGroup.Units

/-!
# The adjoint representation

For `g ∈ G` the conjugation `c_g(x) = g x g⁻¹` is a smooth automorphism, and
`Ad(g) = L(c_g) : L(G) → L(G)` is a Lie algebra automorphism; `Ad(g₁ g₂) = Ad(g₁) Ad(g₂)` by the
functoriality of `L` ([GN26, Definition 5.2.4]). If `G` is connected, the kernel of `Ad` is the
center of `G` ([GN26, Corollary 5.5.8]).

## Main definitions

* `MBLieGroup.conjHom g`: the conjugation `x ↦ g x g⁻¹`, a morphism of Lie groups
  (`MBLieGroup.isHom_conjHom`).
* `MBLieGroup.Ad g`: the adjoint representation `Ad(g) = L(c_g)`.

## Main results

* `MBLieGroup.Ad_one`, `MBLieGroup.Ad_mul`: `Ad` is a representation ([GN26, Definition 5.2.4]).
* `MBLieGroup.Ad_eq_id_iff`: **for connected `G`, `Ad(g) = id` iff `g` is central**
  ([GN26, Corollary 5.5.8]).
* `MBLieGroup.dMB_Ad`: **`L(Ad) = ad`**: the derivative of `g ↦ Ad(g) y` at the identity in
  the direction `x` is `[x, y]` ([GN26, Proposition 5.2.5]).
* `MBLieGroup.comm_iff_lie_eq_zero`: **a connected Lie group is abelian iff its Lie algebra is
  abelian** ([GN26, Proposition 5.5.9]).
* `UnitGroup.Ad_apply`: for the unit group of a continuous inverse algebra, `Ad(g) x = g x g⁻¹`
  ([GN26, Example 5.2.6(a)]).

## Implementation notes

For `L(Ad) = ad` we use the conjugation `C(a, b) = (a ∗ b) ∗ ι(a)` of the local group law in the
chart at the identity: `Ad(g) y = ∂_b C(z, 1) y` for `z = φ(g)`, so the derivative in `x` is the
mixed second derivative of `C`. Since `C(a, 1) = 1` and `C(1, b) = b`, the pure second
derivatives vanish, and `d²C((x, y), (x, y)) = 2 [x, y]` (`LocalGroupLaw.LocalInverse.
dMB_dMB_conj_one`) gives the mixed derivative by polarization.

For Proposition 5.5.9, Glöckner and Neeb differentiate `t ↦ Ad(γ(t)) x` along smooth curves. We
use `L(Ad) = ad` instead: if `L(G)` is abelian, then `z ↦ Ad(φ⁻¹(z)) y` has vanishing derivative at
`φ(1)`, hence near `φ(1)` by `Ad(g k) = Ad(g) Ad(k)` (as in `LieAlgebra/Morphisms.lean`); so
`Ad = id` near `1`, the subgroup `{Ad = id}` is open, closed, hence all of `G`, and every element is
central by Corollary 5.5.8.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups

universe u

namespace MBLieGroup

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]
  {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {H : Type*} [Group H] [TopologicalSpace H] [ChartedSpace F H] [MBLieGroup F H]

/-- `L(φ)` only depends on `φ`. -/
theorem IsHom.lieHom_congr {φ ψ : G →* H} (h : φ = ψ) (hφ : IsHom E F φ) (hψ : IsHom E F ψ) :
    hφ.lieHom = hψ.lieHom := by
  subst h; rfl

/-- The conjugation `c_g(x) = g x g⁻¹`. -/
def conjHom (g : G) : G →* G := (MulAut.conj g).toMonoidHom

omit [TopologicalSpace G] in
@[simp] theorem conjHom_apply (g x : G) : conjHom g x = g * x * g⁻¹ := rfl

variable (E) in
/-- **Conjugations are morphisms of Lie groups.** -/
theorem isHom_conjHom (g : G) : IsHom E E (conjHom g) := smoothMBM_conj g

variable (E) in
/-- **The adjoint representation** `Ad(g) = L(c_g)` ([GN26, Definition 5.2.4]). -/
def Ad (g : G) : LieAlg E G →ₗ⁅ℝ⁆ LieAlg E G := (isHom_conjHom E g).lieHom

theorem Ad_one : Ad E (1 : G) = LieHom.id := by
  rw [Ad, IsHom.lieHom_congr (ψ := MonoidHom.id G) (by ext; simp) _ (IsHom.id (E := E)),
    IsHom.lieHom_id]

theorem Ad_mul (g h : G) : Ad E (g * h) = (Ad E g).comp (Ad E h) := by
  rw [Ad, IsHom.lieHom_congr (ψ := (conjHom g).comp (conjHom h)) (by ext; simp [mul_assoc]) _
    (IsHom.comp (E := E) (F := E) (D := E) (isHom_conjHom E g) (isHom_conjHom E h)),
    IsHom.lieHom_comp (isHom_conjHom E h) (isHom_conjHom E g)]
  rfl

/-- **For connected `G`, the kernel of `Ad` is the center** ([GN26, Corollary 5.5.8]):
`Ad(g) = id` iff `g` commutes with every element of `G`. -/
theorem Ad_eq_id_iff [PreconnectedSpace G] (g : G) :
    Ad E g = LieHom.id ↔ g ∈ Subgroup.center G := by
  constructor
  · intro h
    have hc : conjHom g = MonoidHom.id G := by
      refine IsHom.eq_of_lieHom_eq (isHom_conjHom E g) (IsHom.id (E := E)) fun x ↦ ?_
      rw [IsHom.lieHom_id]
      exact LieHom.congr_fun h x
    rw [Subgroup.mem_center_iff]
    intro x
    have hx := DFunLike.congr_fun hc x
    simp only [conjHom_apply, MonoidHom.id_apply] at hx
    calc x * g = g * x * g⁻¹ * g := by rw [hx]
      _ = g * x := by group
  · intro h
    rw [Ad, IsHom.lieHom_congr (ψ := MonoidHom.id G) _ _ (IsHom.id (E := E)), IsHom.lieHom_id]
    ext x
    simp only [conjHom_apply, MonoidHom.id_apply]
    rw [(Subgroup.mem_center_iff.1 h x).symm, mul_inv_cancel_right]

end MBLieGroup


/-! ### The mixed second derivative of the conjugation -/

namespace LocalGroupLaw.LocalInverse

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {L : LocalGroupLaw E} (ι : L.LocalInverse)

theorem conj_apply (q : E × E) : ι.conj q = L.mul (L.mul q, ι.inv q.1) := rfl

/-- **The mixed second derivative of the conjugation is the bracket**:
`∂_a ∂_b ((a ∗ b) ∗ ι(a)) (x, y) = [x, y]` at `(1, 1)`. -/
theorem dMB_dMB_conj_mixed (x y : E) :
    dMB (dMB ι.conj) (((L.one, L.one), ((0 : E), y)), ((x, (0 : E)), 0)) = L.bracket x y := by
  set C := ι.conj
  set P : E × E := (L.one, L.one)
  set D : E × E → E × E → E := fun h k ↦ dMB (dMB C) ((P, h), (k, 0))
  have hC := ι.contDiffMBOn_conj
  have hU := ι.isOpen_conjDom
  have hP : P ∈ ι.conjDom := ι.one_one_mem_conjDom
  have hs : ∀ h k, D h k = D k h := fun h k ↦ hC.dMB_dMB_symm hU hP h k
  have hdir : ∀ h, ContDiffMBOn 1 (fun z ↦ dMB C (z, h)) ι.conjDom := fun h ↦
    ContDiffMBOn.comp (g := dMB C) (f := fun z ↦ (z, h)) hU (hU.prod isOpen_univ) hC.2.2
      ((smoothMBOn_id _ 1).prodMk hU (contDiffMBOn_const 1 h _)) fun _ hz ↦ ⟨hz, mem_univ _⟩
  have hR : ∀ h k k', D h (k + k') = D h k + D h k' := by
    intro h k k'
    simp only [D, dMB_slice]
    exact (hdir h).dMB_add hU hP k k'
  have hL : ∀ h h' k, D (h + h') k = D h k + D h' k := by
    intro h h' k
    rw [hs, hs h, hs h', hR]
  -- pure terms
  have hxx : D (x, 0) (x, 0) = 0 := by
    set V : Set E := {a | (a, L.one) ∈ L.dom ∧ a ∈ ι.dom ∧ (a, L.one) ∈ ι.conjDom}
    have hV : IsOpen V := (L.isOpen_dom.preimage (by fun_prop)).inter
      (ι.isOpen_dom.inter (hU.preimage (by fun_prop)))
    have h1V : L.one ∈ V := ⟨L.one_one_mem, ι.one_mem, hP⟩
    have hconst : ∀ a ∈ V, dMB C ((a, L.one), (x, (0 : E))) = 0 := by
      intro a ha
      rw [dMB_slice]
      refine dMB_eq_zero_of_eqOn_const (c := L.one) hV ha (fun a' ha' ↦ ?_) x
      change L.mul (L.mul (a', L.one), ι.inv a') = L.one
      rw [L.mul_one a' ha'.1]
      exact ι.mul_inv a' ha'.2.1
    have h := dMB_comp_affine (fun z : E × E ↦ dMB C (z, (x, (0 : E))))
      (LinearMap.inl ℝ E E) ((0 : E), L.one) L.one x
    simp only [LinearMap.inl_apply, Prod.mk_add_mk, add_zero, zero_add] at h
    simp only [D, dMB_slice]
    rw [← h]
    exact dMB_eq_zero_of_eqOn_const hV h1V hconst x
  have hyy : D (0, y) (0, y) = 0 := by
    set W : Set E := {b | (L.one, b) ∈ L.dom ∧ (b, L.one) ∈ L.dom ∧ (L.one, b) ∈ ι.conjDom}
    have hW : IsOpen W := (L.isOpen_dom.preimage (by fun_prop)).inter
      ((L.isOpen_dom.preimage (by fun_prop)).inter (hU.preimage (by fun_prop)))
    have h1W : L.one ∈ W := ⟨L.one_one_mem, L.one_one_mem, hP⟩
    have hconst : ∀ b ∈ W, dMB C ((L.one, b), ((0 : E), y)) = y := by
      intro b hb
      rw [dMB_slice₂]
      have hev : (fun b' ↦ C (L.one, b')) =ᶠ[𝓝 b] fun b' ↦ (ContinuousLinearMap.id ℝ E) b' :=
        eventuallyEq_of_mem (hW.mem_nhds hb) fun b' hb' ↦ by
          change L.mul (L.mul (L.one, b'), ι.inv L.one) = b'
          rw [L.one_mul b' hb'.1, ι.inv_one, L.mul_one b' hb'.2.1]
      rw [dMB_congr_of_eventuallyEq hev]
      exact ((ContinuousLinearMap.id ℝ E).hasDirDerivAt b y).dMB_eq
    have h := dMB_comp_affine (fun z : E × E ↦ dMB C (z, ((0 : E), y)))
      (LinearMap.inr ℝ E E) (L.one, (0 : E)) L.one y
    simp only [LinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add] at h
    simp only [D, dMB_slice]
    rw [← h]
    exact dMB_eq_zero_of_eqOn_const hW h1W hconst y
  -- polarization
  have hv := ι.dMB_dMB_conj_one (x, y)
  have hsplit : ((x, y) : E × E) = (x, 0) + (0, y) := by simp
  change D (x, y) (x, y) = (2 : ℝ) • L.bracket x y at hv
  rw [hsplit, hL, hR, hR, hxx, hyy, hs (x, 0) (0, y), zero_add, add_zero, ← two_smul ℝ] at hv
  exact smul_right_injective E two_ne_zero hv

end LocalGroupLaw.LocalInverse


/-! ### The derived representation -/

namespace MBLieGroup

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]

/-- In the chart `φ` at the identity, `Ad(g) y = ∂_b ((z ∗ b) ∗ ι(z))(1) y` for `z = φ(g)`. -/
theorem Ad_eq_dMB_conj {z : E} (hz : z ∈ (chartAt E (1 : G)).target)
    (hz' : ((chartAt E (1 : G)).symm z)⁻¹ ∈ (chartAt E (1 : G)).source) (y : E) :
    LieAlg.toModel (Ad E ((chartAt E (1 : G)).symm z) y) =
      dMB (localInverse E G).conj ((z, (localGroupLaw E G).one), ((0 : E), y)) := by
  have := isTopologicalGroup E G
  have hg : (chartAt E (1 : G)).symm z ∈ (chartAt E (1 : G)).source :=
    (chartAt E (1 : G)).map_target hz
  have h1 := mem_chart_source E (1 : G)
  rw [dMB_slice₂]
  change dMB (IsHom.localRep (E := E) (F := E) (conjHom ((chartAt E (1 : G)).symm z)))
    (chartAt E (1 : G) 1, y) = dMB (fun w ↦ (localInverse E G).conj (z, w))
      (chartAt E (1 : G) 1, y)
  refine dMB_congr_of_eventuallyEq ?_ y
  set O : Set G := {k | (chartAt E (1 : G)).symm z * k ∈ (chartAt E (1 : G)).source ∧
    (chartAt E (1 : G)).symm z * k * ((chartAt E (1 : G)).symm z)⁻¹ ∈ (chartAt E (1 : G)).source}
  have hO : IsOpen O :=
    ((chartAt E (1 : G)).open_source.preimage (continuous_const.mul continuous_id)).inter
      ((chartAt E (1 : G)).open_source.preimage
        ((continuous_const.mul continuous_id).mul continuous_const))
  have hmem : (chartAt E (1 : G)).target ∩ (chartAt E (1 : G)).symm ⁻¹' O ∈
      𝓝 (chartAt E (1 : G) 1) :=
    ((chartAt E (1 : G)).isOpen_inter_preimage_symm hO).mem_nhds
      ⟨(chartAt E (1 : G)).map_source h1, by
        change (chartAt E (1 : G)).symm (chartAt E (1 : G) 1) ∈ O
        rw [(chartAt E (1 : G)).left_inv h1]
        exact ⟨by rwa [mul_one], by rw [mul_one, mul_inv_cancel]; exact h1⟩⟩
  filter_upwards [hmem] with w hw
  obtain ⟨hwt, hw1, hw2⟩ := hw
  have hwg : (chartAt E (1 : G)).symm w ∈ (chartAt E (1 : G)).source :=
    (chartAt E (1 : G)).map_target hwt
  have e1 : (localGroupLaw E G).mul (z, w) =
      chartAt E (1 : G) ((chartAt E (1 : G)).symm z * (chartAt E (1 : G)).symm w) := by
    have h := chart_mul_eq (E := E) (G := G) hg hwg
    rwa [(chartAt E (1 : G)).right_inv hz, (chartAt E (1 : G)).right_inv hwt] at h
  change chartAt E (1 : G) ((chartAt E (1 : G)).symm z * (chartAt E (1 : G)).symm w *
      ((chartAt E (1 : G)).symm z)⁻¹) =
    (localGroupLaw E G).mul ((localGroupLaw E G).mul (z, w),
      chartAt E (1 : G) ((chartAt E (1 : G)).symm z)⁻¹)
  rw [e1, chart_mul_eq hw1 hz']

/-- **The derived representation of `Ad` is `ad`** ([GN26, Proposition 5.2.5]): the derivative of
`g ↦ Ad(g) y` at the identity in the direction `x` is `[x, y]`. -/
theorem dMB_Ad (x y : LieAlg E G) :
    dMB (fun z : E ↦ LieAlg.toModel (Ad E ((chartAt E (1 : G)).symm z) y))
      (chartAt E (1 : G) 1, LieAlg.toModel x) = LieAlg.toModel ⁅x, y⁆ := by
  have := isTopologicalGroup E G
  set L := localGroupLaw E G
  set ι := localInverse E G
  have h1 := mem_chart_source E (1 : G)
  set Φ : E → E := fun z ↦ dMB ι.conj ((z, L.one), ((0 : E), LieAlg.toModel y))
  have hev : (fun z : E ↦ LieAlg.toModel (Ad E ((chartAt E (1 : G)).symm z) y)) =ᶠ[𝓝 L.one]
      Φ := by
    have hO : IsOpen {g : G | g⁻¹ ∈ (chartAt E (1 : G)).source} :=
      (chartAt E (1 : G)).open_source.preimage continuous_inv
    have hmem : (chartAt E (1 : G)).target ∩ (chartAt E (1 : G)).symm ⁻¹'
        {g : G | g⁻¹ ∈ (chartAt E (1 : G)).source} ∈ 𝓝 L.one :=
      ((chartAt E (1 : G)).isOpen_inter_preimage_symm hO).mem_nhds
        ⟨(chartAt E (1 : G)).map_source h1, by
          change ((chartAt E (1 : G)).symm (chartAt E (1 : G) 1))⁻¹ ∈ (chartAt E (1 : G)).source
          rw [(chartAt E (1 : G)).left_inv h1, inv_one]; exact h1⟩
    filter_upwards [hmem] with z hz
    exact Ad_eq_dMB_conj hz.1 hz.2 _
  change dMB _ (L.one, LieAlg.toModel x) = _
  rw [dMB_congr_of_eventuallyEq hev]
  have h := dMB_comp_affine (dMB ι.conj)
    ((LinearMap.inl ℝ (E × E) (E × E)).comp (LinearMap.inl ℝ E E))
    (((0 : E), L.one), ((0 : E), LieAlg.toModel y)) L.one (LieAlg.toModel x)
  simp only [LinearMap.comp_apply, LinearMap.inl_apply, Prod.mk_add_mk, zero_add,
    add_zero] at h
  rw [show Φ = fun z ↦ dMB ι.conj ((z, L.one), ((0 : E), LieAlg.toModel y)) from rfl, h]
  exact ι.dMB_dMB_conj_mixed _ _

end MBLieGroup


/-! ### Connected Lie groups with abelian Lie algebras are abelian -/

section Abelian

variable {X F : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

omit [LocallyConvexSpace ℝ X] [T2Space X] in
/-- A `C¹` map with vanishing derivative on an open convex set is constant there. -/
theorem eq_of_dMB_eq_zero {f : X → F} {U V : Set X} (hU : IsOpen U) (hf : ContDiffMBOn 1 f U)
    (hV : IsOpen V) (hVc : Convex ℝ V) (hVU : V ⊆ U) (h : ∀ z ∈ V, ∀ u, dMB f (z, u) = 0)
    {z₀ z : X} (hz₀ : z₀ ∈ V) (hz : z ∈ V) : f z = f z₀ := by
  set ℓ : ℝ → X := fun t ↦ t • (z - z₀) + z₀
  have hℓ : ℓ = ⇑(AffineMap.lineMap z₀ z : ℝ →ᵃ[ℝ] X) := by
    funext t; rw [AffineMap.lineMap_apply]; rfl
  set J := ℓ ⁻¹' V
  have hJ : IsOpen J := hV.preimage (by fun_prop)
  have hJc : IsPreconnected J := by
    rw [show J = (AffineMap.lineMap z₀ z : ℝ →ᵃ[ℝ] X) ⁻¹' V by rw [← hℓ]]
    exact (hVc.affine_preimage _).isPreconnected
  have hd : ∀ t ∈ J, HasDirDerivAt (f ∘ ℓ) t 1 0 := by
    intro t ht
    have hin : HasDirDerivAt ℓ t 1 (z - z₀) := by
      unfold HasDirDerivAt
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r (hr : r ≠ 0)
      simp only [ℓ, smul_eq_mul, mul_one, add_smul, add_sub_add_right_eq_sub,
        add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr, one_smul]
    have h' := hf.hasDirDerivAt_comp hU hin (hVU ht)
    rwa [h _ ht] at h'
  have h0J : (0 : ℝ) ∈ J := by simpa [J, ℓ] using hz₀
  have h1J : (1 : ℝ) ∈ J := by simpa [J, ℓ] using hz
  have he := eq_of_hasDirDerivAt_zero hJ hJc hd h1J h0J
  simpa [ℓ] using he

end Abelian

namespace MBLieGroup

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]

/-- `Ad(g)` as a continuous linear map of the model space. -/
def AdCLM (g : G) : E →L[ℝ] E where
  toFun y := LieAlg.toModel (Ad E g (LieAlg.toModel.symm y))
  map_add' y y' := by simp
  map_smul' c y := by simp
  cont := (isHom_conjHom E g).continuous_lieHom

/-- **`d(z ∗ ·)(1)` is onto**: it is inverted by `d(z⁻¹ ∗ ·)(z)`. -/
theorem exists_xl_eq {z : E} (hz : z ∈ (chartAt E (1 : G)).target)
    (hz' : ((chartAt E (1 : G)).symm z)⁻¹ ∈ (chartAt E (1 : G)).source) (u : E) :
    ∃ v, (localGroupLaw E G).xl v z = u := by
  have := isTopologicalGroup E G
  set χ := chartAt E (1 : G)
  set LG := localGroupLaw E G
  have h1 := mem_chart_source E (1 : G)
  have hk : χ.symm z ∈ χ.source := χ.map_target hz
  have hχk : χ (χ.symm z) = z := χ.right_inv hz
  set z' := χ (χ.symm z)⁻¹
  have hz1 : (z, LG.one) ∈ LG.dom := by
    rw [← hχk]; exact chart_mem_dom hk h1 (by rw [mul_one]; exact hk)
  have hz'z : (z', z) ∈ LG.dom := by
    rw [← hχk]; exact chart_mem_dom hz' hk (by rw [inv_mul_cancel]; exact h1)
  have hz'z1 : LG.mul (z', z) = LG.one := by
    rw [← hχk, chart_mul_eq hz' hk, inv_mul_cancel]; rfl
  refine ⟨dMB (fun y ↦ LG.mul (z', y)) (z, u), ?_⟩
  rw [LocalGroupLaw.xl_eq]
  have hin := (LG.contDiffMBOn_mul_left 1 z').hasDirDerivAt (k := 0) hz'z u
  have h := (LG.contDiffMBOn_mul_left 1 z).hasDirDerivAt_comp (LG.isOpen_domL z) hin
    (by rw [hz'z1]; exact hz1)
  rw [hz'z1] at h
  have hid : (fun y ↦ LG.mul (z, y)) ∘ (fun y ↦ LG.mul (z', y)) =ᶠ[𝓝 z] fun y ↦ y := by
    set O : Set G := {g | g ∈ χ.source ∧ (χ.symm z)⁻¹ * g ∈ χ.source}
    have hO : IsOpen O := χ.open_source.inter
      (χ.open_source.preimage (continuous_const.mul continuous_id))
    have hmem : χ.target ∩ χ.symm ⁻¹' O ∈ 𝓝 z :=
      (χ.isOpen_inter_preimage_symm hO).mem_nhds ⟨hz, hk, by rw [inv_mul_cancel]; exact h1⟩
    filter_upwards [hmem] with y hy'
    obtain ⟨hy, hy1, hy2⟩ := hy'
    change χ (χ.symm z * χ.symm (χ (χ.symm (χ (χ.symm z)⁻¹) * χ.symm y))) = y
    rw [χ.left_inv hz', χ.left_inv hy2, mul_inv_cancel_left, χ.right_inv hy]
  have hid' : HasDirDerivAt (fun y : E ↦ y) z u u :=
    (ContinuousLinearMap.id ℝ E).hasDirDerivAt z u
  exact tendsto_nhds_unique (h.congr_of_eventuallyEq hid) hid'

/-- **`Ad = id` near the identity if `L(G)` is abelian.** -/
theorem eventually_Ad_eq_id (h : ∀ x y : LieAlg E G, ⁅x, y⁆ = 0) :
    ∀ᶠ g in 𝓝 (1 : G), Ad E g = LieHom.id := by
  have := isTopologicalGroup E G
  set χ := chartAt E (1 : G)
  set L := localGroupLaw E G
  set ι := localInverse E G
  have h1 := mem_chart_source E (1 : G)
  have hC := ι.contDiffMBOn_conj
  have hU := ι.isOpen_conjDom
  set Z : Set E := {z | (z, L.one) ∈ ι.conjDom}
  have hZ : IsOpen Z := hU.preimage (by fun_prop)
  -- `Φ_y(z) = ∂_b C(z, 1) y`
  set Φ : E → E → E := fun y z ↦ dMB ι.conj ((z, L.one), ((0 : E), y))
  have hΦ : ∀ y, ContDiffMBOn 1 (Φ y) Z := fun y ↦
    ContDiffMBOn.comp (g := dMB ι.conj) (f := fun z ↦ ((z, L.one), ((0 : E), y))) hZ
      (hU.prod isOpen_univ) hC.2.2
      (((smoothMBOn_id _ 1).prodMk hZ (contDiffMBOn_const 1 L.one _)).prodMk hZ
        (contDiffMBOn_const 1 ((0 : E), y) _)) fun _ hz ↦ ⟨hz, mem_univ _⟩
  have hΦone : ∀ y v, dMB (Φ y) (L.one, v) = 0 := by
    intro y v
    have hd := dMB_comp_affine (dMB ι.conj)
      ((LinearMap.inl ℝ (E × E) (E × E)).comp (LinearMap.inl ℝ E E))
      (((0 : E), L.one), ((0 : E), y)) L.one v
    simp only [LinearMap.comp_apply, LinearMap.inl_apply, Prod.mk_add_mk, zero_add,
      add_zero] at hd
    change dMB (fun z ↦ dMB ι.conj ((z, L.one), ((0 : E), y))) (L.one, v) = 0
    rw [hd, ι.dMB_dMB_conj_mixed]
    exact h v y
  have hΦ1 : ∀ y, Φ y L.one = y := fun y ↦ by
    simpa using ι.dMB_conj_one ((0 : E), y)
  -- the good set
  set O : Set G := {g | g ∈ χ.source ∧ g⁻¹ ∈ χ.source}
  have hO : IsOpen O := χ.open_source.inter (χ.open_source.preimage continuous_inv)
  set W : Set E := (χ.target ∩ χ.symm ⁻¹' O) ∩ Z
  have hW : IsOpen W := (χ.isOpen_inter_preimage_symm hO).inter hZ
  have h1W : L.one ∈ W := ⟨⟨χ.map_source h1, by
    change χ.symm (χ 1) ∈ O
    rw [χ.left_inv h1]; exact ⟨h1, by rw [inv_one]; exact h1⟩⟩, ι.one_one_mem_conjDom⟩
  -- `Φ_y` agrees with `Ad(φ⁻¹ ·) y` on `W`
  have hΦAd : ∀ y, ∀ z ∈ W, Φ y z = AdCLM (χ.symm z) y := fun y z hz ↦
    (Ad_eq_dMB_conj hz.1.1 hz.1.2.2 y).symm
  -- `dΦ_y = 0` on `W`
  have hd0 : ∀ y, ∀ z ∈ W, ∀ u, dMB (Φ y) (z, u) = 0 := by
    intro y z hz u
    obtain ⟨⟨hzt, hg, hgi⟩, hzZ⟩ := hz
    obtain ⟨v, rfl⟩ := exists_xl_eq hzt hgi u
    have hz1 : (z, L.one) ∈ L.dom := by
      rw [← χ.right_inv hzt]; exact chart_mem_dom hg h1 (by rw [mul_one]; exact hg)
    -- derivative of `w ↦ Φ_y(z ∗ w)` at `1`
    have hA : HasDirDerivAt (Φ y ∘ fun w ↦ L.mul (z, w)) L.one v (dMB (Φ y) (z, L.xl v z)) := by
      have hin := (L.contDiffMBOn_mul_left 1 z).hasDirDerivAt (k := 0) hz1 v
      have h' := (hΦ y).hasDirDerivAt_comp hZ hin (by rw [L.mul_one z hz1]; exact hzZ)
      rwa [L.mul_one z hz1, ← LocalGroupLaw.xl_eq] at h'
    -- `Φ_y(z ∗ w) = Ad(g) Φ_y(w)` near `1`
    have hB : HasDirDerivAt (fun w ↦ AdCLM (χ.symm z) (Φ y w)) L.one v 0 := by
      have h' := ((hΦ y).hasDirDerivAt (k := 0) h1W.2 v).clm_comp_real (AdCLM (χ.symm z))
      rwa [hΦone, map_zero] at h'
    have hev : (fun w ↦ AdCLM (χ.symm z) (Φ y w)) =ᶠ[𝓝 L.one] Φ y ∘ fun w ↦ L.mul (z, w) := by
      set O' : Set G := {k | k ∈ χ.source ∧ k⁻¹ ∈ χ.source ∧ χ.symm z * k ∈ χ.source ∧
        (χ.symm z * k)⁻¹ ∈ χ.source}
      have hO' : IsOpen O' := χ.open_source.inter ((χ.open_source.preimage continuous_inv).inter
        ((χ.open_source.preimage (continuous_const.mul continuous_id)).inter
          (χ.open_source.preimage (continuous_const.mul continuous_id).inv)))
      have hmem : (χ.target ∩ χ.symm ⁻¹' O') ∩ Z ∈ 𝓝 L.one := by
        refine ((χ.isOpen_inter_preimage_symm hO').inter hZ).mem_nhds ⟨⟨χ.map_source h1, ?_⟩,
          ι.one_one_mem_conjDom⟩
        change χ.symm (χ 1) ∈ O'
        rw [χ.left_inv h1]
        exact ⟨h1, by rw [inv_one]; exact h1, by rw [mul_one]; exact hg,
          by rw [mul_one]; exact hgi⟩
      have hmZ : ∀ᶠ w in 𝓝 L.one, L.mul (z, w) ∈ Z := by
        have hc : ContinuousAt (fun w ↦ L.mul (z, w)) L.one :=
          ((L.contDiffMBOn_mul_left 0 z).continuousOn).continuousAt
            ((L.isOpen_domL z).mem_nhds hz1)
        exact hc.preimage_mem_nhds (hZ.mem_nhds (by
          change (L.mul (z, L.one), L.one) ∈ ι.conjDom
          rw [L.mul_one z hz1]; exact hzZ))
      filter_upwards [hmem, hmZ] with w hw hwZ
      obtain ⟨⟨hwt, hk, hki, hgk, hgki⟩, hwZ'⟩ := hw
      have hmul : L.mul (z, w) = χ (χ.symm z * χ.symm w) := by
        have h' := chart_mul_eq (E := E) (G := G) hg (χ.map_target hwt)
        rwa [χ.right_inv hzt, χ.right_inv hwt] at h'
      have hmulW : L.mul (z, w) ∈ W := by
        refine ⟨⟨?_, ?_⟩, hwZ⟩
        · rw [hmul]; exact χ.map_source hgk
        · change χ.symm (L.mul (z, w)) ∈ O
          rw [hmul, χ.left_inv hgk]; exact ⟨hgk, hgki⟩
      simp only [Function.comp_apply]
      rw [hΦAd y w ⟨⟨hwt, hk, hki⟩, hwZ'⟩, hΦAd y _ hmulW, hmul, χ.left_inv hgk]
      simp only [AdCLM, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, Ad_mul,
        LieHom.comp_apply]
      rfl
    exact tendsto_nhds_unique hA (hB.congr_of_eventuallyEq hev)
  -- `Φ_y` is constant near `1`
  obtain ⟨S, ⟨hSn, hSc⟩, hSW⟩ := (LocallyConvexSpace.convex_basis (𝕜 := ℝ) L.one).mem_iff.1
    (hW.mem_nhds h1W)
  set V := interior S
  have hV : IsOpen V := isOpen_interior
  have h1V : L.one ∈ V := mem_interior_iff_mem_nhds.2 hSn
  have hVW : V ⊆ W := interior_subset.trans hSW
  have hconst : ∀ y, ∀ z ∈ V, Φ y z = y := fun y z hz ↦ by
    rw [eq_of_dMB_eq_zero hZ (hΦ y) hV hSc.interior (hVW.trans inter_subset_right)
      (fun z hz ↦ hd0 y z (hVW hz)) h1V hz, hΦ1]
  have hN : χ.source ∩ χ ⁻¹' V ∈ 𝓝 (1 : G) :=
    inter_mem (χ.open_source.mem_nhds h1) ((χ.continuousAt h1).preimage_mem_nhds
      (hV.mem_nhds h1V))
  filter_upwards [hN] with g hg'
  obtain ⟨hg, hgV⟩ := hg'
  ext y
  have h' := hΦAd y (χ g) (hVW hgV)
  rw [hconst y _ hgV, χ.left_inv hg] at h'
  exact h'.symm

/-- **A connected Lie group is abelian iff its Lie algebra is abelian**
([GN26, Proposition 5.5.9]). -/
theorem comm_iff_lie_eq_zero [PreconnectedSpace G] :
    (∀ a b : G, a * b = b * a) ↔ ∀ x y : LieAlg E G, ⁅x, y⁆ = 0 := by
  refine ⟨fun hc ↦ LieAlg.lie_eq_zero_of_comm hc, fun h a b ↦ ?_⟩
  have := isTopologicalGroup E G
  -- the subgroup `{g | Ad(g) = id}`
  set S : Subgroup G :=
    { carrier := {g | Ad E g = LieHom.id}
      mul_mem' := fun {g k} hg hk ↦ by
        change Ad E (g * k) = LieHom.id
        rw [Ad_mul, show Ad E g = LieHom.id from hg, show Ad E k = LieHom.id from hk]; rfl
      one_mem' := Ad_one
      inv_mem' := fun {g} hg ↦ by
        change Ad E g⁻¹ = LieHom.id
        have h' := Ad_mul (E := E) g g⁻¹
        rw [mul_inv_cancel, Ad_one, show Ad E g = LieHom.id from hg] at h'
        exact h'.symm }
  have hO := Subgroup.isOpen_of_mem_nhds S (eventually_Ad_eq_id h)
  have hU := IsClopen.eq_univ ⟨Subgroup.isClosed_of_isOpen S hO, hO⟩ ⟨1, S.one_mem⟩
  have ha : Ad E a = LieHom.id := by
    have : a ∈ (S : Set G) := hU ▸ mem_univ a
    exact this
  exact ((Subgroup.mem_center_iff.1 ((Ad_eq_id_iff a).1 ha)) b).symm

end MBLieGroup

/-! ### Unit groups -/

namespace UnitGroup

variable {A : Type u} [Ring A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
  [TopologicalSpace A] [IsTopologicalRing A] [ContinuousSMul ℝ A] [LocallyConvexSpace ℝ A]
  [T2Space A] [ContinuousInverseAlgebra A]

/-- `z ↦ a z b`, as a continuous linear map. -/
def mulLeftRight (a b : A) : A →L[ℝ] A where
  toFun z := a * z * b
  map_add' z w := by simp [mul_add, add_mul]
  map_smul' c z := by simp [mul_smul_comm, smul_mul_assoc]
  cont := (continuous_const.mul continuous_id).mul continuous_const

/-- **The adjoint representation of `A^×` is conjugation** ([GN26, Example 5.2.6(a)]):
`Ad(g) x = g x g⁻¹`. -/
theorem Ad_apply (g : UnitGroup A) (x : MBLieGroup.LieAlg A (UnitGroup A)) :
    MBLieGroup.LieAlg.toModel (MBLieGroup.Ad A g x) =
      val g * MBLieGroup.LieAlg.toModel x * val g⁻¹ := by
  change dMB (MBLieGroup.IsHom.localRep (E := A) (F := A) (MBLieGroup.conjHom g))
    (chartAt A (1 : UnitGroup A) 1, (MBLieGroup.LieAlg.toModel x : A)) = _
  have h0 : chartAt A (1 : UnitGroup A) 1 = 0 := by
    change unitChart A 1 = 0; simp [unitChart]
  have hev : MBLieGroup.IsHom.localRep (E := A) (F := A) (MBLieGroup.conjHom g) =ᶠ[𝓝 (0 : A)]
      ⇑(mulLeftRight (val g) (val g⁻¹)) := by
    have ht : (chartAt A (1 : UnitGroup A)).target ∈ 𝓝 (0 : A) := by
      rw [← h0]
      exact (chartAt A (1 : UnitGroup A)).open_target.mem_nhds
        ((chartAt A (1 : UnitGroup A)).map_source (mem_chart_source A 1))
    filter_upwards [ht] with z hz
    change unitChart A (g * (chartAt A (1 : UnitGroup A)).symm z * g⁻¹) = val g * z * val g⁻¹
    rw [unitChart, val_mul, val_mul, val_chartAt_symm _ hz, mul_add, add_mul, mul_one]
    have hg : val g * val g⁻¹ = 1 := by rw [← val_mul, mul_inv_cancel, val_one]
    rw [hg, add_sub_cancel_right]
  rw [h0, dMB_congr_of_eventuallyEq hev]
  exact ((mulLeftRight (val g) (val g⁻¹)).hasDirDerivAt 0 _).dMB_eq

end UnitGroup

end LocallyConvex.LieGroups
