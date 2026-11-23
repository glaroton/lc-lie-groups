/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Regular.MaurerCartan
public import LocallyConvexLieGroups.Regular.Evol
public import LocallyConvexLieGroups.LieAlgebra.AdjointAction
public import LocallyConvexLieGroups.Regular.Lift
public import LocallyConvexAnalysis.MappingSpace.Pushforward

/-!
# The Fundamental Theorem for Lie group-valued functions

Let `G` be a `C⁰`-regular Lie group with Lie algebra `𝔤`, and `U ∋ 0` an open convex subset of a
locally convex space `X`. A smooth `𝔤`-valued `1`-form `α` on `U` (a smooth map `U × X → 𝔤`, linear
in the second variable) satisfying the Maurer–Cartan equation
`d_k α(h) − d_h α(k) = [α(h), α(k)]` is the logarithmic derivative `δ(f)` of a smooth map
`f : U → G` ([GN26, Lemma 6.1.9]); conversely `δ(f)` always satisfies the Maurer–Cartan equation
(`MBLieGroup.logDeriv_maurerCartan`, [GN26, Lemma 5.5.5]). This is part (i) of the Fundamental
Theorem [GN26, Theorem 6.1.13] on open convex subsets of locally convex spaces; GN26 states it
for regular `G`, and `C⁰`-regularity suffices.

## Main results

* `MBLieGroup.eq_zero_of_hasDirDerivAt_bracket`: **uniqueness** for `η' = [η, ξ]`, `η(0) = 0`,
  when `ξ` has an evolution `γ` ([GN26, Lemma 6.1.7]): `Ad(γ(t)) η(t)` is constant.
* `MBLieGroup.hasDirDerivAt_ray`: along the ray `t ↦ t x`, a `1`-form `A` satisfying the
  Maurer–Cartan equation obeys `d/dt A_{t x}(t h) = [A_{t x}(t h), A_{t x}(x)] +
  d/ds A_{t (x + s h)}(x + s h)|_{s = 0}`.
* `MBLieGroup.exists_logDeriv_eq`: **the Fundamental Theorem on convex sets**
  ([GN26, Lemma 6.1.9]).

## Proof

As in [GN26], `f(y) = evol(ξ_y)` with `ξ_y(t) = α_{t y}(y)`; it is smooth since `y ↦ ξ_y` is a
superposition operator (lc-analysis, `pushforward`), and `f(t y) = γ_{ξ_y}(t)` by rescaling, so
`δf(t y)(y) = α_{t y}(y)` for `0 < t < 1`. Instead of the two-parameter map `(s, t) ↦ f(t(x + s h))`
of [GN26, Lemma 6.1.8] we apply `hasDirDerivAt_ray` to both `α` and `δ(f)`, which satisfies the
Maurer–Cartan equation; the `s`-derivatives agree since `δ(f) = α` on rays, so
`η(t) = α_{t x}(t h) − δf(t x)(t h)` solves `η' = [η, ξ_x]`, `η(0) = 0`, and the uniqueness lemma
gives `η(1) = 0`, that is, `δf(x)(h) = α_x(h)`.

The global statements of [GN26, Theorem 6.1.13] (manifolds, coverings, simply connected domains,
the period map) are not formalized.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology unitInterval
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups.MBLieGroup

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]

/-! ### Uniqueness for `η' = [η, ξ]` -/

theorem AdRep_one (y : E) : AdRep (G := G) (chartAt E (1 : G) 1, y) = y := by
  rw [show AdRep (G := G) (chartAt E (1 : G) 1, y) = LieAlg.toModel (Ad E
      ((chartAt E (1 : G)).symm (chartAt E (1 : G) 1)) (LieAlg.toModel.symm y)) from
      (Ad_eq_dMB_conjRep _ y).symm, (chartAt E (1 : G)).left_inv (mem_chart_source E (1 : G)),
    Ad_one]
  rfl

theorem AdAction_inv_AdAction (g : G) (y : E) : AdAction ((g⁻¹ : G), AdAction (g, y)) = y := by
  change LieAlg.toModel (Ad E g⁻¹ (LieAlg.toModel.symm
    (LieAlg.toModel (Ad E g (LieAlg.toModel.symm y))))) = y
  rw [LinearEquiv.symm_apply_apply, ← LieHom.comp_apply, ← Ad_mul, inv_mul_cancel, Ad_one]
  rfl

theorem AdAction_zero (g : G) : AdAction (g, (0 : E)) = 0 := by
  change LieAlg.toModel (Ad E g (LieAlg.toModel.symm 0)) = 0
  simp

/-- `t ↦ Ad(γ(t)) η(t)` is stationary when `δ(γ) = ξ` and `η' = [η, ξ]`. -/
theorem hasDirDerivAt_AdAction {γ : ℝ → G} {ξ η : E} {ηf : ℝ → E} {t : ℝ}
    (hγ : HasLogDerivAt E γ ξ t) (hη : HasDirDerivAt ηf t 1 ((localGroupLaw E G).bracket η ξ))
    (hηt : ηf t = η) :
    HasDirDerivAt (fun s ↦ AdAction (γ s, ηf s)) t 1 0 := by
  have := isTopologicalGroup E G
  set φ := chartAt E (1 : G)
  set L := localGroupLaw E G
  subst hηt
  have hsrc : ∀ᶠ s in 𝓝 t, (γ t)⁻¹ * γ s ∈ φ.source := by
    have hc : ContinuousAt (fun s ↦ (γ t)⁻¹ * γ s) t := continuousAt_const.mul hγ.1
    have h0 : (γ t)⁻¹ * γ t ∈ φ.source := by rw [inv_mul_cancel]; exact mem_chart_source E (1 : G)
    exact hc.preimage_mem_nhds (φ.open_source.mem_nhds h0)
  have hκ : HasDirDerivAt (fun s ↦ (φ ((γ t)⁻¹ * γ s), ηf s)) t 1
      (ξ, L.bracket (ηf t) ξ) := hγ.2.prodMk hη
  have hκt : (φ ((γ t)⁻¹ * γ t), ηf t) = (φ 1, ηf t) := by rw [inv_mul_cancel]
  have hmem : (φ ((γ t)⁻¹ * γ t), ηf t) ∈ AdRepDom E G := by
    rw [hκt]; exact one_mem_conjRepDom
  have hcomp := (contDiffMBOn_AdRep (G := G) 1).hasDirDerivAt_comp isOpen_AdRepDom hκ hmem
  have hval : dMB (AdRep (G := G)) ((φ ((γ t)⁻¹ * γ t), ηf t), (ξ, L.bracket (ηf t) ξ)) = 0 := by
    rw [hκt, show (ξ, L.bracket (ηf t) ξ) = (ξ, (0 : E)) + ((0 : E), L.bracket (ηf t) ξ) by simp,
      (contDiffMBOn_AdRep (G := G) 1).dMB_add isOpen_AdRepDom one_mem_conjRepDom, dMB_slice,
      dMB_slice₂]
    have h1 : (fun z ↦ AdRep (G := G) (z, ηf t)) = fun z ↦
        LieAlg.toModel (Ad E (φ.symm z) (LieAlg.toModel.symm (ηf t))) :=
      funext fun z ↦ (Ad_eq_dMB_conjRep z (ηf t)).symm
    have h2 : (fun y ↦ AdRep (G := G) (φ 1, y)) = fun y ↦ y := funext AdRep_one
    have hA := dMB_Ad (G := G) (LieAlg.toModel.symm ξ) (LieAlg.toModel.symm (ηf t))
    simp only [LinearEquiv.apply_symm_apply] at hA
    rw [h1, h2, hA, show dMB (fun y : E ↦ y) (ηf t, L.bracket (ηf t) ξ) = L.bracket (ηf t) ξ from
      ((ContinuousLinearMap.id ℝ E).hasDirDerivAt _ _).dMB_eq]
    change L.bracket ξ (ηf t) + L.bracket (ηf t) ξ = 0
    rw [L.bracket_swap (ηf t) ξ, neg_add_cancel]
  rw [hval] at hcomp
  have hA := ((AdCLM (G := G) (γ t)).contDiffMBOn 1 univ).hasDirDerivAt_comp isOpen_univ hcomp
    (mem_univ _)
  rw [((AdCLM (G := G) (γ t)).hasDirDerivAt _ _).dMB_eq, map_zero] at hA
  refine hA.congr_of_eventuallyEq ?_
  filter_upwards [hsrc] with s hs
  exact (AdAction_eq (γ t) (γ s) hs (ηf s)).symm

/-- **[GN26, Lemma 6.1.7]**, uniqueness: if `δ(γ) = ξ` on `(a, b)`, a solution of
`η' = [η, ξ]` on `(a, b)`, continuous on `[a, b]`, with `η(a) = 0` vanishes on `[a, b]`. -/
theorem eq_zero_of_hasDirDerivAt_bracket {γ : ℝ → G} {ξ η : ℝ → E} {a b : ℝ}
    (hγc : ContinuousOn γ (Icc a b)) (hγ : ∀ t ∈ Ioo a b, HasLogDerivAt E γ (ξ t) t)
    (hηc : ContinuousOn η (Icc a b))
    (hη : ∀ t ∈ Ioo a b, HasDirDerivAt η t 1 ((localGroupLaw E G).bracket (η t) (ξ t)))
    (ha : η a = 0) : ∀ t ∈ Icc a b, η t = 0 := by
  set ζ : ℝ → E := fun t ↦ AdAction (γ t, η t)
  have hζc : ContinuousOn ζ (Icc a b) :=
    continuous_AdAction.comp_continuousOn (hγc.prodMk hηc)
  have hζd : ∀ t ∈ Ioo a b, HasDirDerivAt ζ t 1 0 := fun t ht ↦
    hasDirDerivAt_AdAction (hγ t ht) (hη t ht) rfl
  have hζa : ζ a = 0 := by simp only [ζ, ha, AdAction_zero]
  intro t ht
  have hζt : ζ t = 0 := by
    rcases eq_or_lt_of_le ht.1 with rfl | hat
    · exact hζa
    rw [← hζa, SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)]
    intro ℓ
    have hd : ∀ c ∈ Ioo a t, HasDerivAt (fun s ↦ ℓ (ζ s)) 0 c := fun c hc ↦ by
      have h := (ℓ.continuous.tendsto _).comp (hζd c ⟨hc.1, hc.2.trans_le ht.2⟩)
      rw [map_zero] at h
      rw [hasDerivAt_iff_tendsto_slope_zero]
      refine h.congr fun r ↦ ?_
      simp [smul_eq_mul]
    obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope (fun s ↦ ℓ (ζ s)) (fun _ ↦ 0) hat
      ((ℓ.continuous.comp_continuousOn hζc).mono (Icc_subset_Icc le_rfl ht.2)) hd
    rw [eq_comm, div_eq_zero_iff, sub_eq_zero, sub_eq_zero] at hc'
    exact hc'.resolve_right hat.ne'
  rw [← AdAction_inv_AdAction (γ t) (η t)]
  change AdAction ((γ t)⁻¹, ζ t) = 0
  rw [hζt, AdAction_zero]

/-! ### The curves `ξ_y(t) = α(t y, y)` -/

section Ray

variable {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X]

/-- `[0, 1]`, in the universe of `X`. -/
abbrev IU : Type u := ULift.{u} I

omit [LocallyConvexSpace ℝ X] [T2Space X] in
theorem continuous_down : Continuous fun t : IU ↦ ((t.down : I) : ℝ) :=
  continuous_subtype_val.comp continuous_uliftDown

/-- `y ↦ (t ↦ (t y, y))`. -/
def rayCLM : X →L[ℝ] C(IU, X × X) where
  toFun y := ⟨fun t ↦ (((t.down : I) : ℝ) • y, y),
    (continuous_down.smul continuous_const).prodMk continuous_const⟩
  map_add' _ _ := ContinuousMap.ext fun _ ↦ Prod.ext (smul_add _ _ _) rfl
  map_smul' _ _ := ContinuousMap.ext fun _ ↦ Prod.ext (smul_comm _ _ _) rfl
  cont := ContinuousMap.continuous_of_continuous_uncurry _ <|
    ((continuous_down.comp continuous_snd).smul continuous_fst).prodMk continuous_fst

variable (E) in
/-- `C(IU, E) → C(I, E)`. -/
def downCLM : C(IU, E) →L[ℝ] C(I, E) where
  toFun f := f.comp ⟨ULift.up, continuous_uliftUp⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := ContinuousMap.continuous_precomp _

/-- **`ξ_y(t) = α(t y, y)`**, the curve whose evolution integrates `α` along the ray to `y`. -/
def rayField (α : X × X → E) (U : Set X) (y : X) : C(I, E) :=
  downCLM E (pushforward IU α (U ×ˢ univ) (rayCLM y))

omit [LocallyConvexSpace ℝ E] [T2Space E] [LocallyConvexSpace ℝ X] [T2Space X] in
theorem rayField_apply {α : X × X → E} {U : Set X} (hα : ContinuousOn α (U ×ˢ univ))
    (hUc : Convex ℝ U) (h0 : (0 : X) ∈ U) {y : X} (hy : y ∈ U) (t : I) :
    rayField α U y t = α ((t : ℝ) • y, y) := by
  rw [rayField, downCLM, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousMap.comp_apply, pushforward_apply hα]
  · rfl
  · exact fun s ↦ ⟨hUc.smul_mem_of_zero_mem h0 hy s.down.2, mem_univ _⟩

theorem smoothMBOn_rayField {α : X × X → E} {U : Set X} (hU : IsOpen U)
    (hα : SmoothMBOn α (U ×ˢ univ)) (hUc : Convex ℝ U) (h0 : (0 : X) ∈ U) :
    SmoothMBOn (rayField α U) U := fun k ↦ by
  have hP := contDiffMBOn_pushforward (K := IU) k (hU.prod isOpen_univ) (hα k)
  have h1 := ContDiffMBOn.comp (g := pushforward IU α (U ×ˢ univ)) (f := ⇑(rayCLM (X := X)))
    hU (isOpen_valuedIn (hU.prod isOpen_univ)) hP (((rayCLM (X := X)).contDiffMBOn k univ).mono
      (subset_univ U)) fun y hy s ↦ ⟨hUc.smul_mem_of_zero_mem h0 hy s.down.2, mem_univ _⟩
  exact ContDiffMBOn.comp hU isOpen_univ ((downCLM E).contDiffMBOn k univ) h1 (mapsTo_univ _ _)

omit [LocallyConvexSpace ℝ E] [T2Space E] [LocallyConvexSpace ℝ X] [T2Space X] in
/-- `ξ_{s y} = S(ξ_y, s)`. -/
theorem rayField_smul {α : X × X → E} {U : Set X} (hα : ContinuousOn α (U ×ˢ univ))
    (hUc : Convex ℝ U) (h0 : (0 : X) ∈ U)
    (hsmul : ∀ z ∈ U, ∀ (c : ℝ) h, α (z, c • h) = c • α (z, h)) {y : X} (hy : y ∈ U) (s : I) :
    rayField α U ((s : ℝ) • y) = scaleCurve (rayField α U y) s := by
  have hsy : (s : ℝ) • y ∈ U := hUc.smul_mem_of_zero_mem h0 hy s.2
  ext t
  rw [rayField_apply hα hUc h0 hsy, scaleCurve, ContinuousMap.smul_apply, ContinuousMap.comp_apply,
    rayField_apply hα hUc h0 hy, smul_smul,
    hsmul _ (hUc.smul_mem_of_zero_mem h0 hy (unitInterval.mul_mem t.2 s.2))]
  simp [scaleMap, mul_comm]

end Ray

/-! ### The Fundamental Theorem on convex sets -/

section Fundamental

variable {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X]

omit [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [LocallyConvexSpace ℝ X] [T2Space X] in
/-- Directional derivatives along lines. -/
theorem dMB_eq_line {F' : Type*} [AddCommGroup F'] [Module ℝ F'] [TopologicalSpace F']
    (g : X → F') (x h : X) : dMB g (x, h) = dMB (fun s : ℝ ↦ g (x + s • h)) (0, 1) := by
  simp only [dMB, zero_add, smul_eq_mul, mul_one, zero_smul, add_zero]

omit [LocallyConvexSpace ℝ X] [T2Space X] in
/-- **Along the ray `t ↦ t x`**, a `1`-form `A` satisfying the Maurer–Cartan equation obeys
`d/dt A_{t x}(t h) = [A_{t x}(t h), A_{t x}(x)] + d/ds A_{t (x + s h)}(x + s h)|_{s = 0}`. -/
theorem hasDirDerivAt_ray {U : Set X} (hU : IsOpen U) {A : X × X → E}
    (hA : ContDiffMBOn 1 A (U ×ˢ univ))
    (hadd : ∀ z ∈ U, ∀ h k, A (z, h + k) = A (z, h) + A (z, k))
    (hsmul : ∀ z ∈ U, ∀ (c : ℝ) h, A (z, c • h) = c • A (z, h))
    (hMC : ∀ z ∈ U, ∀ h k, dMB A ((z, h), (k, 0)) - dMB A ((z, k), (h, 0)) =
      (localGroupLaw E G).bracket (A (z, h)) (A (z, k)))
    (x h : X) {t : ℝ} (ht : t • x ∈ U) :
    HasDirDerivAt (fun r : ℝ ↦ A (r • x, r • h)) t 1
      ((localGroupLaw E G).bracket (A (t • x, t • h)) (A (t • x, x)) +
        dMB (fun s : ℝ ↦ A (t • (x + s • h), x + s • h)) (0, 1)) := by
  set L := localGroupLaw E G
  set z := t • x
  have hO : IsOpen (U ×ˢ (univ : Set X)) := hU.prod isOpen_univ
  have hzO : (z, (0 : X)) ∈ U ×ˢ (univ : Set X) := ⟨ht, mem_univ _⟩
  have hlin : ∀ a c, dMB A ((z, a), (0, c)) = A (z, c) := fun a c ↦ by
    rw [dMB_slice₂]
    refine HasDirDerivAt.dMB_eq ?_
    unfold HasDirDerivAt
    refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun r (hr : r ≠ 0) ↦ ?_)
    simp only
    rw [hadd z ht, hsmul z ht, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr, one_smul]
  -- the two curves
  have h1 : HasDirDerivAt (fun r : ℝ ↦ (r • x, r • h)) t 1 (x, h) := by
    unfold HasDirDerivAt
    refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun r (hr : r ≠ 0) ↦ ?_)
    have e : ((t + r • (1 : ℝ)) • x, (t + r • (1 : ℝ)) • h) - (t • x, t • h) = r • (x, h) := by
      ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd] <;> module
    simp only
    rw [e, smul_smul, inv_mul_cancel₀ hr, one_smul]
  have h2 : HasDirDerivAt (fun s : ℝ ↦ (t • (x + s • h), x + s • h)) 0 1 (t • h, h) := by
    unfold HasDirDerivAt
    refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun r (hr : r ≠ 0) ↦ ?_)
    have e : (t • (x + (0 + r • (1 : ℝ)) • h), x + (0 + r • (1 : ℝ)) • h) -
        (t • (x + (0 : ℝ) • h), x + (0 : ℝ) • h) = r • (t • h, h) := by
      ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd] <;> module
    simp only
    rw [e, smul_smul, inv_mul_cancel₀ hr, one_smul]
  have h20 : (t • (x + (0 : ℝ) • h), x + (0 : ℝ) • h) = (z, x) := by simp [z]
  have hd1 := hA.hasDirDerivAt_comp hO h1 ⟨ht, mem_univ _⟩
  have hd2 := hA.hasDirDerivAt_comp hO h2 (by rw [h20]; exact ⟨ht, mem_univ _⟩)
  rw [h20] at hd2
  have e2 : dMB (fun s : ℝ ↦ A (t • (x + s • h), x + s • h)) (0, 1) =
      dMB A ((z, x), (t • h, h)) := hd2.dMB_eq
  rw [e2]
  suffices hval : dMB A ((z, t • h), (x, h)) =
      L.bracket (A (z, t • h)) (A (z, x)) + dMB A ((z, x), (t • h, h)) by
    rw [← hval]; exact hd1
  rw [show ((x, h) : X × X) = (x, 0) + (0, h) by simp, show ((t • h, h) : X × X) =
      (t • h, 0) + (0, h) by simp, hA.dMB_add hO ⟨ht, mem_univ _⟩,
    hA.dMB_add hO ⟨ht, mem_univ _⟩, hlin, hlin, dMB_slice, dMB_slice]
  have e1 : dMB (fun z' ↦ A (z', t • h)) (z, x) = t • dMB (fun z' ↦ A (z', h)) (z, x) := by
    have hd : HasDirDerivAt (fun z' ↦ A (z', h)) z x (dMB (fun z' ↦ A (z', h)) (z, x)) := by
      rw [← dMB_slice]
      exact hasDirDerivAt_slice.1 (hA.hasDirDerivAt ⟨ht, mem_univ _⟩ (x, 0))
    refine ((hd.const_smul t).congr_of_eventuallyEq ?_).dMB_eq
    filter_upwards [hU.mem_nhds ht] with z' hz'
    exact (hsmul z' hz' t h).symm
  have e2 : dMB (fun z' ↦ A (z', x)) (z, t • h) = t • dMB (fun z' ↦ A (z', x)) (z, h) := by
    rw [← dMB_slice, ← dMB_slice, show ((t • h, (0 : X)) : X × X) = t • (h, 0) by simp,
      hA.dMB_smul ⟨ht, mem_univ _⟩]
  have hmc := hMC z ht h x
  rw [dMB_slice, dMB_slice] at hmc
  rw [e1, e2, hsmul z ht, L.smul_bracket, ← hmc, smul_sub]
  abel

theorem _root_.LocallyConvex.LieGroups.LocalGroupLaw.sub_bracket (L : LocalGroupLaw E)
    (a b c : E) : L.bracket (a - b) c = L.bracket a c - L.bracket b c := by
  rw [eq_sub_iff_add_eq, ← L.add_bracket, sub_add_cancel]

/-- **The Fundamental Theorem for Lie group-valued functions on convex sets**
([GN26, Lemma 6.1.9], for `C⁰`-regular `G`): on an open convex set `U ∋ 0`, a smooth `𝔤`-valued
`1`-form `α` satisfying the Maurer–Cartan equation `d_k α(h) − d_h α(k) = [α(h), α(k)]` is the
logarithmic derivative of a smooth map `f : U → G` with `f(0) = 1`, namely
`f(y) = evol(t ↦ α_{t y}(y))`. -/
theorem exists_logDeriv_eq (hG : IsC0Regular E G) {U : Set X} (hU : IsOpen U)
    (hUc : Convex ℝ U) (h0 : (0 : X) ∈ U) {α : X × X → E} (hα : SmoothMBOn α (U ×ˢ univ))
    (hadd : ∀ z ∈ U, ∀ h k, α (z, h + k) = α (z, h) + α (z, k))
    (hsmul : ∀ z ∈ U, ∀ (c : ℝ) h, α (z, c • h) = c • α (z, h))
    (hMC : ∀ z ∈ U, ∀ h k, dMB α ((z, h), (k, 0)) - dMB α ((z, k), (h, 0)) =
      (localGroupLaw E G).bracket (α (z, h)) (α (z, k))) :
    ∃ f : X → G, SmoothMBMOn X E f U ∧ f 0 = 1 ∧
      ∀ x ∈ U, ∀ h, logDeriv E f x h = α (x, h) := by
  have := isTopologicalGroup E G
  set L := localGroupLaw E G
  set φ := chartAt E (1 : G)
  have hαc : ContinuousOn α (U ×ˢ univ) := (hα 0).continuousOn
  have hα0 : ∀ z ∈ U, α (z, 0) = 0 := fun z hz ↦ by
    simpa using hsmul z hz 0 0
  set f : X → G := fun y ↦ evol E G (rayField α U y)
  have hP : ∀ x : E, ∃ P : ℝ → G, IsEvol E (fun _ ↦ x) P := hG.isExp.exists_isEvol_const
  have hf : SmoothMBMOn X E f U := SmoothMBMOn.comp (g := evol E G) (f := rayField α U) hU
    isOpen_univ (fun k ↦ hG.smooth k)
    (fun k ↦ (contMDiffMBOn_iff_contDiffMBOn hU).2 (smoothMBOn_rayField hU hα hUc h0 k))
    (mapsTo_univ _ _)
  have hray : ∀ y ∈ U, ∃ Γ : ℝ → G, IsEvol E (extendCurve (rayField α U y)) Γ ∧
      ∀ r : I, f ((r : ℝ) • y) = Γ r := by
    intro y hy
    obtain ⟨Γ, hΓ⟩ := hG.semiregular (rayField α U y)
    refine ⟨Γ, hΓ, fun r ↦ ?_⟩
    change evol E G (rayField α U ((r : ℝ) • y)) = Γ r
    rw [rayField_smul hαc hUc h0 hsmul hy r, evol_eq_of_isEvolOn hP (hΓ.isEvolOn_scale r),
      mul_one]
  -- the logarithmic derivative of `f`, as a `1`-form
  set D : X × X → E := fun qk ↦ logDeriv E f qk.1 qk.2
  have hD : ContDiffMBOn 1 D (U ×ˢ univ) := contDiffMBOn_logDeriv₂ hU hf
  have hDadd : ∀ z ∈ U, ∀ h k, D (z, h + k) = D (z, h) + D (z, k) := fun z hz h k ↦
    logDeriv_add hU hf hz h k
  have hDsmul : ∀ z ∈ U, ∀ (c : ℝ) h, D (z, c • h) = c • D (z, h) := fun z hz c h ↦
    logDeriv_smul hU hf hz c h
  have hDMC : ∀ z ∈ U, ∀ h k, dMB D ((z, h), (k, 0)) - dMB D ((z, k), (h, 0)) =
      L.bracket (D (z, h)) (D (z, k)) := fun z hz h k ↦ by
    rw [dMB_slice, dMB_slice]
    exact logDeriv_maurerCartan hU hf hz h k
  -- along rays, `δf(t y)(y) = α_{t y}(y)`
  have hrayD : ∀ y ∈ U, ∀ t ∈ Ioo (0 : ℝ) 1, D (t • y, y) = α (t • y, y) := by
    intro y hy t ht
    obtain ⟨Γ, hΓ, hfΓ⟩ := hray y hy
    have hfΓ' : ∀ r ∈ Icc (0 : ℝ) 1, f (r • y) = Γ r := fun r hr ↦ hfΓ ⟨r, hr⟩
    change dMB _ _ = _
    rw [dMB_eq_line]
    have hev : (fun s : ℝ ↦ φ ((f (t • y))⁻¹ * f (t • y + s • y))) =ᶠ[𝓝 0]
        fun s ↦ φ ((Γ t)⁻¹ * Γ (t + s)) := by
      have hmem : ∀ᶠ s in 𝓝 (0 : ℝ), t + s ∈ Ioo (0 : ℝ) 1 :=
        (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
          (by simpa using isOpen_Ioo.mem_nhds ht)
      filter_upwards [hmem] with s hs
      rw [← add_smul, hfΓ' t (Ioo_subset_Icc_self ht), hfΓ' _ (Ioo_subset_Icc_self hs)]
    rw [dMB_congr_of_eventuallyEq hev]
    have hd := (hΓ.2 t).2
    have hd' : HasDirDerivAt (fun s : ℝ ↦ φ ((Γ t)⁻¹ * Γ (t + s))) 0 1
        (extendCurve (rayField α U y) t) := by
      unfold HasDirDerivAt at hd ⊢
      refine hd.congr fun r ↦ ?_
      simp only [smul_eq_mul, mul_one, zero_add, add_zero, inv_mul_cancel]
      rfl
    rw [hd'.dMB_eq, MBLieGroup.extendCurve_apply, projIcc_of_mem _ (Ioo_subset_Icc_self ht),
      rayField_apply hαc hUc h0 hy]
  refine ⟨f, hf, ?_, fun x hx h ↦ ?_⟩
  · change evol E G (rayField α U 0) = 1
    have h00 : rayField α U 0 = 0 := by
      ext t
      rw [rayField_apply hαc hUc h0 h0, smul_zero, hα0 0 h0]
      rfl
    rw [h00, evol_zero]
  -- `η(t) = α_{t x}(t h) − δf(t x)(t h)` solves `η' = [η, ξ_x]`
  have hrx : ∀ t ∈ Icc (0 : ℝ) 1, t • x ∈ U := fun t ht ↦ hUc.smul_mem_of_zero_mem h0 hx ht
  set η : ℝ → E := fun t ↦ α (t • x, t • h) - D (t • x, t • h)
  obtain ⟨Γ, hΓ, -⟩ := hray x hx
  have hξ : ∀ t ∈ Icc (0 : ℝ) 1, extendCurve (rayField α U x) t = α (t • x, x) := fun t ht ↦ by
    rw [MBLieGroup.extendCurve_apply, projIcc_of_mem _ ht, rayField_apply hαc hUc h0 hx]
  have hη : ∀ t ∈ Ioo (0 : ℝ) 1, HasDirDerivAt η t 1
      (L.bracket (η t) (extendCurve (rayField α U x) t)) := by
    intro t ht
    have htU := hrx t (Ioo_subset_Icc_self ht)
    have h1 := hasDirDerivAt_ray (G := G) hU (hα 1) hadd hsmul hMC x h htU
    have h2 := hasDirDerivAt_ray (G := G) hU hD hDadd hDsmul hDMC x h htU
    have hg : (fun s : ℝ ↦ α (t • (x + s • h), x + s • h)) =ᶠ[𝓝 0]
        fun s ↦ D (t • (x + s • h), x + s • h) := by
      have hS : ∀ᶠ s in 𝓝 (0 : ℝ), x + s • h ∈ U :=
        (continuous_const.add (continuous_id.smul continuous_const)).continuousAt.preimage_mem_nhds
          (by simpa using hU.mem_nhds hx)
      filter_upwards [hS] with s hs
      exact (hrayD _ hs t ht).symm
    have hx' : D (t • x, x) = α (t • x, x) := hrayD x hx t ht
    rw [dMB_congr_of_eventuallyEq hg] at h1
    rw [hx'] at h2
    convert h1.sub h2 using 1
    rw [hξ t (Ioo_subset_Icc_self ht), L.sub_bracket]
    abel
  have hηc : ContinuousOn η (Icc 0 1) := by
    have hpath : MapsTo (fun t : ℝ ↦ (t • x, t • h)) (Icc 0 1) (U ×ˢ univ) :=
      fun t ht ↦ ⟨hrx t ht, mem_univ _⟩
    have hc : Continuous fun t : ℝ ↦ (t • x, t • h) :=
      (continuous_id.smul continuous_const).prodMk (continuous_id.smul continuous_const)
    exact (hαc.comp hc.continuousOn hpath).sub (hD.continuousOn.comp hc.continuousOn hpath)
  have hη0 : η 0 = 0 := by
    have hD0 : D (0, 0) = 0 := by simpa using hDsmul 0 h0 0 0
    simp only [η, zero_smul, hα0 0 h0, hD0, sub_zero]
  have hzero := eq_zero_of_hasDirDerivAt_bracket (a := 0) (b := 1)
    (fun t _ ↦ (hΓ.2 t).1.continuousWithinAt) (fun t _ ↦ hΓ.2 t) hηc hη hη0 1
    ⟨zero_le_one, le_rfl⟩
  have h1 := sub_eq_zero.1 hzero
  simp only [one_smul] at h1
  exact h1.symm

end Fundamental

end LocallyConvex.LieGroups.MBLieGroup
