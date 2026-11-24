/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Regular.Fundamental
public import Mathlib.Topology.Homotopy.Lifting
public import LocallyConvexManifolds.Manifold.LocalDiffeo

/-!
# The Fundamental Theorem on simply connected open sets

Let `G` be a `C⁰`-regular Lie group and `U` a simply connected open subset of a locally convex space
`X`. A smooth `𝔤`-valued `1`-form `α` on `U` satisfying the Maurer–Cartan equation is the
logarithmic derivative of a smooth map `f : U → G` ([GN26, Theorem 6.1.13], parts (i) and
(ii)(a), for open subsets of locally convex spaces).

## Proof

As in [GN26, Proposition 6.1.10], `α` has primitives on convex open subsets of `U` (the
Fundamental Theorem on convex sets, `MBLieGroup.exists_logDeriv_eq`, translated), unique up to
left translation (`MBLieGroup.IsLogPrimitive.eqOn`). The space of germs `U × G`, topologized by
the graphs of primitives over convex open sets (`MBLieGroup.Germs`), is a covering space of `U`
(`MBLieGroup.isCoveringMap_proj`): over a convex open set `C` with a primitive `f`, the preimage
is `C × G`, with `G` discrete, through `(y, h) ↦ (y, h f(y)⁻¹)`. Since `U` is simply connected and
locally path connected, the identity of `U` lifts to the space of germs (Mathlib,
`IsCoveringMap.existsUnique_continuousMap_lifts`); the second component of the lift is locally a
left translate of a primitive, hence a global primitive.

The uniqueness lemma on intervals (`MBLieGroup.eqOn_of_hasLogDerivAt`) extends
`MBLieGroup.eq_of_hasLogDerivAt` from `ℝ` to open intervals.

## Main results

* `MBLieGroup.IsLogPrimitive`: `f` is smooth on `V` with `δ(f) = α` there.
* `MBLieGroup.exists_isLogPrimitive`: primitives on convex open sets.
* `MBLieGroup.IsLogPrimitive.eqOn`: uniqueness on convex open sets.
* `MBLieGroup.isCoveringMap_proj`: the space of germs covers `U`.
* `MBLieGroup.exists_logDeriv_eq_of_simplyConnected`: **the Fundamental Theorem**.

For `1`-forms on manifolds, see `Regular/FundamentalManifold.lean`. The period map of
[GN26, Theorem 6.1.13(ii)(b)] is not formalized.

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

/-! ### Uniqueness on intervals -/

/-- **A curve with vanishing logarithmic derivative on an open interval is constant there.** -/
theorem eqOn_of_hasLogDerivAt_zero {P : ℝ → G} {J : Set ℝ} (hJ : IsOpen J)
    (hJc : IsPreconnected J) (hP : ∀ t ∈ J, HasLogDerivAt E P 0 t) {s t : ℝ} (hs : s ∈ J)
    (ht : t ∈ J) : P s = P t := by
  set φ := chartAt E (1 : G)
  set L := localGroupLaw E G
  have h1 := mem_chart_source E (1 : G)
  have := isTopologicalGroup E G
  have hc : ContinuousOn P J := fun t ht ↦ (hP t ht).1.continuousWithinAt
  have hloc : ∀ s₀ ∈ J, ∀ᶠ s in 𝓝 s₀, P s = P s₀ := by
    intro s₀ hs₀J
    set S : Set ℝ := {s | (P s₀)⁻¹ * P s ∈ φ.source}
    have hS : S ∩ J ∈ 𝓝 s₀ := by
      refine inter_mem ?_ (hJ.mem_nhds hs₀J)
      have hc' : ContinuousAt (fun s ↦ (P s₀)⁻¹ * P s) s₀ :=
        continuousAt_const.mul (hP s₀ hs₀J).1
      have h0 : (P s₀)⁻¹ * P s₀ ∈ φ.source := by rw [inv_mul_cancel]; exact h1
      exact hc'.preimage_mem_nhds (φ.open_source.mem_nhds h0)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hS
    set e : ℝ → E := fun s ↦ φ ((P s₀)⁻¹ * P s)
    have he : ∀ s₁ ∈ Metric.ball s₀ ε, HasDirDerivAt e s₁ 1 0 := by
      intro s₁ hs₁
      have ha : (P s₀)⁻¹ * P s₁ ∈ φ.source := (hball hs₁).1
      have hJ₁ : s₁ ∈ J := (hball hs₁).2
      have hmem : φ ((P s₁)⁻¹ * P s₁) ∈ L.domL (φ ((P s₀)⁻¹ * P s₁)) := by
        rw [inv_mul_cancel]
        exact chart_mem_dom ha h1 (by rw [mul_one]; exact ha)
      have hd := (L.contDiffMBOn_mul_left 1 (φ ((P s₀)⁻¹ * P s₁))).hasDirDerivAt_comp
        (L.isOpen_domL _) (hP s₁ hJ₁).2 hmem
      have h0 : dMB (fun b ↦ L.mul (φ ((P s₀)⁻¹ * P s₁), b)) (φ ((P s₁)⁻¹ * P s₁), (0 : E)) =
          0 := by
        have := (L.contDiffMBOn_mul_left 1 (φ ((P s₀)⁻¹ * P s₁))).dMB_smul hmem (0 : ℝ) (0 : E)
        simpa using this
      rw [h0] at hd
      refine hd.congr_of_eventuallyEq ?_
      have hw : ∀ᶠ s in 𝓝 s₁, (P s₁)⁻¹ * P s ∈ φ.source := by
        have hc' : ContinuousAt (fun s ↦ (P s₁)⁻¹ * P s) s₁ :=
          continuousAt_const.mul (hP s₁ hJ₁).1
        have h0' : (P s₁)⁻¹ * P s₁ ∈ φ.source := by rw [inv_mul_cancel]; exact h1
        exact hc'.preimage_mem_nhds (φ.open_source.mem_nhds h0')
      filter_upwards [hw] with s hs
      change L.mul (φ ((P s₀)⁻¹ * P s₁), φ ((P s₁)⁻¹ * P s)) = φ ((P s₀)⁻¹ * P s)
      rw [chart_mul_eq ha hs]
      congr 1
      group
    filter_upwards [Metric.ball_mem_nhds s₀ hε] with s hs
    have heq := eq_of_hasDirDerivAt_zero Metric.isOpen_ball (convex_ball s₀ ε).isPreconnected he
      hs (Metric.mem_ball_self hε)
    have hsrc : (P s₀)⁻¹ * P s ∈ φ.source := (hball hs).1
    have hsrc₀ : (P s₀)⁻¹ * P s₀ ∈ φ.source := (hball (Metric.mem_ball_self hε)).1
    have h := φ.injOn hsrc hsrc₀ heq
    rw [inv_mul_cancel] at h
    exact inv_mul_eq_one.1 h |>.symm
  have := isPreconnected_iff_preconnectedSpace.1 hJc
  have hlc : IsLocallyConstant (J.domRestrict P) := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun s₀ ↦ ?_
    have h := hloc s₀ s₀.2
    rw [nhds_subtype, eventually_comap]
    filter_upwards [h] with s hs s' hs'
    rw [← hs'] at hs
    exact hs
  exact hlc.apply_eq_of_preconnectedSpace ⟨s, hs⟩ ⟨t, ht⟩

/-- **The Uniqueness Lemma on an open interval.** -/
theorem eqOn_of_hasLogDerivAt {γ₁ γ₂ : ℝ → G} {ξ : ℝ → E} {J : Set ℝ} (hJ : IsOpen J)
    (hJc : IsPreconnected J) (h₁ : ∀ t ∈ J, HasLogDerivAt E γ₁ (ξ t) t)
    (h₂ : ∀ t ∈ J, HasLogDerivAt E γ₂ (ξ t) t) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (h₀ : γ₁ t₀ = γ₂ t₀) :
    EqOn γ₁ γ₂ J := fun s hs ↦ by
  have h := eqOn_of_hasLogDerivAt_zero hJ hJc (fun t ht ↦ (h₁ t ht).mul_inv (h₂ t ht)) hs ht₀
  simp only [h₀, mul_inv_cancel] at h
  exact (mul_inv_eq_one.1 h).symm

/-! ### Local primitives -/

section Primitive

variable {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X]

variable (E) in
/-- `f` is a **primitive** of the `𝔤`-valued `1`-form `α` on `V`: `f` is smooth on `V` and
`δ(f) = α` there. -/
def IsLogPrimitive (α : X × X → E) (f : X → G) (V : Set X) : Prop :=
  SmoothMBMOn X E f V ∧ ∀ y ∈ V, ∀ h, logDeriv E f y h = α (y, h)

variable {α : X × X → E} {f : X → G} {V : Set X}

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] in
theorem IsLogPrimitive.mono (hf : IsLogPrimitive E α f V) {W : Set X} (hWV : W ⊆ V) :
    IsLogPrimitive E α f W :=
  ⟨fun k ↦ ContMDiffMBOn.mono' (hf.1 k) hWV, fun y hy h ↦ hf.2 y (hWV hy) h⟩

/-- Left translates of primitives are primitives. -/
theorem IsLogPrimitive.mul_left (hV : IsOpen V) (hf : IsLogPrimitive E α f V) (g : G) :
    IsLogPrimitive E α (fun y ↦ g * f y) V := by
  refine ⟨SmoothMBMOn.comp (g := fun x : G ↦ g * x) hV isOpen_univ
    (fun k ↦ smoothMBM_mul_left (E := E) g k) hf.1 (mapsTo_univ _ _), fun y hy h ↦ ?_⟩
  rw [← hf.2 y hy h]
  unfold logDeriv
  congr 1
  funext r
  congr 1
  group

/-- Along a line, a smooth map has logarithmic derivative `δf(q)(v)`. -/
theorem hasLogDerivAt_line (hV : IsOpen V) (hf : SmoothMBMOn X E f V) {y₀ v : X} {t : ℝ}
    (ht : y₀ + t • v ∈ V) :
    HasLogDerivAt E (fun s ↦ f (y₀ + s • v)) (logDeriv E f (y₀ + t • v) v) t := by
  have := isTopologicalGroup E G
  set q := y₀ + t • v
  have hℓ : HasDirDerivAt (fun s : ℝ ↦ y₀ + s • v) t 1 v := by
    unfold HasDirDerivAt
    refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun r (hr : r ≠ 0) ↦ ?_)
    simp only [smul_eq_mul, mul_one, add_smul]
    rw [show y₀ + (t • v + r • v) - (y₀ + t • v) = r • v by abel, smul_smul,
      inv_mul_cancel₀ hr, one_smul]
  have hℓc : Continuous fun s : ℝ ↦ y₀ + s • v := continuous_const.add
    (continuous_id.smul continuous_const)
  refine ⟨((hf 0).1.continuousAt (hV.mem_nhds ht)).comp (f := fun s : ℝ ↦ y₀ + s • v) (x := t)
    hℓc.continuousAt, ?_⟩
  have hd := ((smoothMBOn_rel hV hf q) 1).hasDirDerivAt_comp (isOpen_relDom hV hf q) hℓ
    (mem_relDom ht)
  exact hd

/-- **Uniqueness of primitives on convex open sets.** -/
theorem IsLogPrimitive.eqOn (hV : IsOpen V) (hVc : Convex ℝ V) {f₁ f₂ : X → G}
    (h₁ : IsLogPrimitive E α f₁ V) (h₂ : IsLogPrimitive E α f₂ V) {y₀ : X} (hy₀ : y₀ ∈ V)
    (h₀ : f₁ y₀ = f₂ y₀) : EqOn f₁ f₂ V := by
  intro y hy
  set J : Set ℝ := {s | y₀ + s • (y - y₀) ∈ V}
  have hJ : IsOpen J := hV.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have hJc : Convex ℝ J := by
    intro a ha b hb c d hc hd hcd
    have := hVc ha hb hc hd hcd
    obtain rfl : d = 1 - c := by linarith
    change y₀ + (c • a + (1 - c) • b) • (y - y₀) ∈ V
    convert this using 1
    simp only [smul_eq_mul]
    module
  have h0 : (0 : ℝ) ∈ J := by simpa [J] using hy₀
  have h1 : (1 : ℝ) ∈ J := by simpa [J] using hy
  have heq := eqOn_of_hasLogDerivAt (ξ := fun t ↦ α (y₀ + t • (y - y₀), y - y₀)) hJ
    hJc.isPreconnected
    (fun t ht ↦ by
      have := hasLogDerivAt_line hV h₁.1 ht; rwa [h₁.2 _ ht] at this)
    (fun t ht ↦ by
      have := hasLogDerivAt_line hV h₂.1 ht; rwa [h₂.2 _ ht] at this)
    h0 (by simpa using h₀) h1
  simpa using heq

omit [LocallyConvexSpace ℝ X] [T2Space X] in
/-- Directional derivatives commute with translations. -/
theorem dMB_comp_add_const {Y F' : Type*} [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace F']
    [AddCommGroup F'] [Module ℝ F'] (g : Y → F') (c p v : Y) :
    dMB (fun z ↦ g (z + c)) (p, v) = dMB g (p + c, v) := by
  simp only [dMB, add_right_comm]

/-- **Local primitives exist on convex open sets** ([GN26, Lemma 6.1.9], translated): if `α`
satisfies the Maurer–Cartan equation on `U`, `G` is `C⁰`-regular and `V ⊆ U` is open convex, `α`
has a primitive `f` on `V` with `f(x) = 1` at any `x ∈ V`. -/
theorem exists_isLogPrimitive (hG : IsC0Regular E G) {U : Set X} (hα : SmoothMBOn α (U ×ˢ univ))
    (hadd : ∀ z ∈ U, ∀ h k, α (z, h + k) = α (z, h) + α (z, k))
    (hsmul : ∀ z ∈ U, ∀ (c : ℝ) h, α (z, c • h) = c • α (z, h))
    (hMC : ∀ z ∈ U, ∀ h k, dMB α ((z, h), (k, 0)) - dMB α ((z, k), (h, 0)) =
      (localGroupLaw E G).bracket (α (z, h)) (α (z, k)))
    (hV : IsOpen V) (hVc : Convex ℝ V) (hVU : V ⊆ U) {x : X} (hx : x ∈ V) :
    ∃ f : X → G, IsLogPrimitive E α f V ∧ f x = 1 := by
  set V' := (fun z ↦ z + x) ⁻¹' V
  have hV' : IsOpen V' := hV.preimage (continuous_id.add continuous_const)
  have hV'c : Convex ℝ V' := by
    have e : (fun z ↦ z + x) = fun z ↦ x + z := funext fun z ↦ add_comm z x
    change Convex ℝ ((fun z ↦ z + x) ⁻¹' V)
    rw [e]
    exact hVc.translate_preimage_right x
  have h0 : (0 : X) ∈ V' := by
    change (0 : X) + x ∈ V
    simpa using hx
  set α' : X × X → E := fun p ↦ α (p.1 + x, p.2)
  have hα'eq : α' = fun p ↦ α (p + (x, 0)) := by
    funext p
    change α (p.1 + x, p.2) = α (p + (x, 0))
    congr 1
    ext <;> simp
  have hα' : SmoothMBOn α' (V' ×ˢ univ) := fun k ↦ by
    have hin : ContDiffMBOn k (fun p : X × X ↦ p + (x, 0)) (V' ×ˢ univ) :=
      ((smoothMBOn_id _ k).add (hV'.prod isOpen_univ) (contDiffMBOn_const k _ _))
    rw [hα'eq]
    exact ContDiffMBOn.comp (g := α) (hV'.prod isOpen_univ) (hV.prod isOpen_univ)
      ((hα k).mono (prod_mono hVU subset_rfl)) hin
      fun p hp ↦ ⟨hp.1, mem_univ _⟩
  have hMC' : ∀ z ∈ V', ∀ h k, dMB α' ((z, h), (k, 0)) - dMB α' ((z, k), (h, 0)) =
      (localGroupLaw E G).bracket (α' (z, h)) (α' (z, k)) := fun z hz h k ↦ by
    rw [hα'eq, dMB_comp_add_const, dMB_comp_add_const]
    have := hMC _ (hVU hz) h k
    simpa using this
  obtain ⟨f', hf', hf'0, hδ⟩ := exists_logDeriv_eq hG hV' hV'c h0 hα'
    (fun z hz ↦ hadd _ (hVU hz)) (fun z hz ↦ hsmul _ (hVU hz)) hMC'
  refine ⟨fun y ↦ f' (y + -x), ⟨?_, fun y hy h ↦ ?_⟩, by simpa using hf'0⟩
  · refine SmoothMBMOn.comp (g := f') (f := fun y ↦ y + -x) hV hV' hf' (fun k ↦ ?_)
      fun y hy ↦ by simpa [V'] using hy
    exact (contMDiffMBOn_iff_contDiffMBOn hV).2
      ((smoothMBOn_id _ k).add hV (contDiffMBOn_const k _ _))
  · have hy' : y + -x ∈ V' := by simpa [V'] using hy
    have := hδ _ hy' h
    simp only [α', neg_add_cancel_right] at this
    rw [← this]
    unfold logDeriv
    exact dMB_comp_add_const (fun r ↦ chartAt E (1 : G) ((f' (y + -x))⁻¹ * f' r)) (-x) y h

end Primitive

/-! ### The space of germs of primitives -/

section Germs

variable {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X]

omit [T2Space X] in
/-- Open sets contain convex open neighborhoods of their points. -/
theorem exists_convex_open {W : Set X} (hW : IsOpen W) {y : X} (hy : y ∈ W) :
    ∃ C, IsOpen C ∧ Convex ℝ C ∧ y ∈ C ∧ C ⊆ W := by
  obtain ⟨S, ⟨hS, hSc⟩, hSW⟩ :=
    (LocallyConvexSpace.convex_basis (𝕜 := ℝ) y).mem_iff.1 (hW.mem_nhds hy)
  exact ⟨interior S, isOpen_interior, hSc.interior, mem_interior_iff_mem_nhds.2 hS,
    interior_subset.trans hSW⟩

variable (G) in
/-- The space `U × G`, to be topologized by the graphs of primitives of `α`. -/
@[nolint unusedArguments]
def Germs (_α : X × X → E) (U : Set X) : Type _ := U × G

variable {α : X × X → E} {U : Set X}

/-- The germ `(x, g)`. -/
def Germs.mk (x : U) (g : G) : Germs G α U := (x, g)

/-- The graph of `f` over `V`, a subset of `Germs`. -/
def sheet (V : Set X) (f : X → G) : Set (Germs G α U) := {p | (p.1 : X) ∈ V ∧ p.2 = f p.1}

variable (G α U) in
/-- The sheets over convex open subsets of `U` of the primitives of `α`. -/
def sheets : Set (Set (Germs G α U)) :=
  {S | ∃ V f, IsOpen V ∧ Convex ℝ V ∧ V ⊆ U ∧ IsLogPrimitive E α f V ∧ S = sheet V f}

instance : TopologicalSpace (Germs G α U) := generateFrom (sheets G α U)

/-- The projection `Germs → U`. -/
def proj (p : Germs G α U) : U := p.1

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [T2Space X] in
theorem isOpen_sheet {V : Set X} {f : X → G} (hV : IsOpen V) (hVc : Convex ℝ V) (hVU : V ⊆ U)
    (hf : IsLogPrimitive E α f V) : IsOpen (sheet (α := α) (U := U) V f) :=
  isOpen_generateFrom_of_mem ⟨V, f, hV, hVc, hVU, hf, rfl⟩

variable (hG : IsC0Regular E G) (hU : IsOpen U) (hα : SmoothMBOn α (U ×ˢ univ))
  (hadd : ∀ z ∈ U, ∀ h k, α (z, h + k) = α (z, h) + α (z, k))
  (hsmul : ∀ z ∈ U, ∀ (c : ℝ) h, α (z, c • h) = c • α (z, h))
  (hMC : ∀ z ∈ U, ∀ h k, dMB α ((z, h), (k, 0)) - dMB α ((z, k), (h, 0)) =
    (localGroupLaw E G).bracket (α (z, h)) (α (z, k)))
include hG hα hadd hsmul hMC

include hU in
/-- Every germ lies on a sheet inside any given open set. -/
theorem exists_sheet (p : Germs G α U) {W : Set X} (hW : IsOpen W) (hp : (p.1 : X) ∈ W) :
    ∃ V f, IsOpen V ∧ Convex ℝ V ∧ V ⊆ U ∧ V ⊆ W ∧ IsLogPrimitive E α f V ∧
      p ∈ sheet (α := α) (U := U) V f := by
  obtain ⟨C, hC, hCc, hyC, hCW⟩ := exists_convex_open (hU.inter hW) ⟨p.1.2, hp⟩
  obtain ⟨f, hf, hf1⟩ := exists_isLogPrimitive hG hα hadd hsmul hMC hC hCc
    (hCW.trans inter_subset_left) hyC
  exact ⟨C, fun y ↦ p.2 * f y, hC, hCc, hCW.trans inter_subset_left,
    hCW.trans inter_subset_right, hf.mul_left hC p.2, hyC, by simp [hf1]⟩

include hU in
theorem continuous_proj : Continuous (proj (α := α) (U := U) (G := G)) := by
  rw [continuous_def]
  intro W hW
  obtain ⟨W', hW', rfl⟩ := isOpen_induced_iff.1 hW
  rw [isOpen_iff_forall_mem_open]
  intro p hp
  obtain ⟨V, f, hV, hVc, hVU, hVW, hf, hpV⟩ := exists_sheet hG hU hα hadd hsmul hMC p hW' hp
  exact ⟨sheet V f, fun q hq ↦ hVW hq.1, isOpen_sheet hV hVc hVU hf, hpV⟩

omit hG hα hadd hsmul hMC in
/-- The section `y ↦ (y, g f(y))` over `V` is continuous. -/
theorem continuous_section {V : Set X} {f : X → G} (hV : IsOpen V) (hf : IsLogPrimitive E α f V)
    (g : G) : Continuous fun y : ((↑) ⁻¹' V : Set U) ↦ Germs.mk (α := α) y.1 (g * f y.1) := by
  refine (continuous_generateFrom_iff (b := sheets G α U)).2 ?_
  rintro _ ⟨W, fW, hW, hWc, hWU, hfW, rfl⟩
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨hyW, hyeq⟩ : ((y.1 : X) ∈ W ∧ g * f y.1 = fW y.1) := hy
  obtain ⟨C, hC, hCc, hyC, hCVW⟩ := exists_convex_open (hV.inter hW) ⟨y.2, hyW⟩
  have heq := (hf.mul_left hV g).mono (hCVW.trans inter_subset_left) |>.eqOn hC hCc
    (hfW.mono (hCVW.trans inter_subset_right)) hyC hyeq
  refine ⟨{z | (z.1 : X) ∈ C}, fun z hz ↦ ⟨(hCVW hz).2, heq hz⟩,
    hC.preimage (continuous_subtype_val.comp continuous_subtype_val), hyC⟩

variable (G) in
/-- `G` with the discrete topology. -/
def Disc : Type _ := G

instance : TopologicalSpace (Disc G) := ⊥

instance : DiscreteTopology (Disc G) := ⟨rfl⟩

/-- `G → Disc G`. -/
def toDisc (g : G) : Disc G := g

/-- `Disc G → G`. -/
def ofDisc (d : Disc G) : G := d

include hU in
/-- **The projection `Germs → U` is a covering map.** -/
theorem isCoveringMap_proj : IsCoveringMap (proj (α := α) (U := U) (G := G)) := by
  intro x
  refine IsEvenlyCovered.to_isEvenlyCovered_preimage (I := Disc G) ?_
  obtain ⟨C, hC, hCc, hxC, hCU⟩ := exists_convex_open hU x.2
  obtain ⟨f, hf, -⟩ := exists_isLogPrimitive hG hα hadd hsmul hMC hC hCc hCU hxC
  set VU : Set U := (↑) ⁻¹' C
  have hVU : IsOpen VU := hC.preimage continuous_subtype_val
  have hcp := continuous_proj (G := G) hG hU hα hadd hsmul hMC
  let H : proj (α := α) ⁻¹' VU ≃ₜ VU × Disc G :=
  { toFun := fun p ↦ (⟨p.1.1, p.2⟩, toDisc (p.1.2 * (f p.1.1)⁻¹))
    invFun := fun q ↦ ⟨Germs.mk q.1 (ofDisc q.2 * f q.1.1), q.1.2⟩
    left_inv := fun p ↦ Subtype.ext (Prod.ext rfl (inv_mul_cancel_right (G := G) _ _))
    right_inv := fun q ↦ Prod.ext rfl (mul_inv_cancel_right (ofDisc q.2) _)
    continuous_toFun := by
      refine ((hcp.comp continuous_subtype_val).subtype_mk _).prodMk ?_
      refine continuous_discrete_rng.2 fun g ↦ ?_
      have : (fun p : proj (α := α) ⁻¹' VU ↦ toDisc (p.1.2 * (f p.1.1)⁻¹)) ⁻¹' {g} =
          (↑) ⁻¹' sheet (α := α) (U := U) C (fun y ↦ ofDisc g * f y) := by
        ext p
        simp only [mem_preimage, mem_singleton_iff, sheet]
        constructor
        · intro h; exact ⟨p.2, by rw [← h]; exact (inv_mul_cancel_right (G := G) _ _).symm⟩
        · intro h; change p.1.2 * (f p.1.1)⁻¹ = ofDisc g; rw [h.2]
          exact mul_inv_cancel_right _ _
      rw [this]
      exact (isOpen_sheet hC hCc hCU (hf.mul_left hC (ofDisc g))).preimage continuous_subtype_val
    continuous_invFun := by
      refine continuous_prod_of_discrete_right.2 fun g ↦ ?_
      exact (continuous_section hC hf (ofDisc g)).subtype_mk _ }
  exact ⟨inferInstance, VU, hxC, hVU, hVU.preimage hcp, H, fun _ ↦ rfl⟩

include hU in
/-- **The Fundamental Theorem for Lie group-valued functions on simply connected open sets**
([GN26, Theorem 6.1.13], for open subsets of locally convex spaces and `C⁰`-regular `G`): on a
simply connected open set `U`, a smooth `𝔤`-valued `1`-form satisfying the Maurer–Cartan equation
is the logarithmic derivative of a smooth map `f : U → G`, with `f(x₀) = 1`. -/
theorem exists_logDeriv_eq_of_simplyConnected [SimplyConnectedSpace U] {x₀ : X} (hx₀ : x₀ ∈ U) :
    ∃ f : X → G, SmoothMBMOn X E f U ∧ f x₀ = 1 ∧
      ∀ x ∈ U, ∀ h, logDeriv E f x h = α (x, h) := by
  have : LocallyPathConnectedSpace U := hU.locallyPathConnectedSpace
  have cov := isCoveringMap_proj (G := G) hG hU hα hadd hsmul hMC
  obtain ⟨F, ⟨hF0, hFp⟩, -⟩ := cov.existsUnique_continuousMap_lifts (ContinuousMap.id U)
    ⟨x₀, hx₀⟩ (Germs.mk (α := α) ⟨x₀, hx₀⟩ 1) rfl
  have hF1 : ∀ a : U, (F a).1 = a := fun a ↦ congrFun hFp a
  classical
  set f : X → G := fun y ↦ if hy : y ∈ U then (F ⟨y, hy⟩).2 else 1
  -- near each point, `f` is a left translate of a primitive
  have hloc : ∀ y₀ ∈ U, ∃ C, IsOpen C ∧ y₀ ∈ C ∧ C ⊆ U ∧ IsLogPrimitive E α f C := by
    intro y₀ hy₀
    obtain ⟨C₀, hC₀, hC₀c, hy₀C₀, hC₀U⟩ := exists_convex_open hU hy₀
    obtain ⟨f₀, hf₀, hf₀1⟩ := exists_isLogPrimitive hG hα hadd hsmul hMC hC₀ hC₀c hC₀U hy₀C₀
    set a : U := ⟨y₀, hy₀⟩
    set g := (F a).2
    have hP₀ := hf₀.mul_left hC₀ g
    have hS := isOpen_sheet (α := α) (U := U) hC₀ hC₀c hC₀U hP₀
    obtain ⟨W', hW', hW'eq⟩ := isOpen_induced_iff.1 (hS.preimage F.continuous)
    have hamem : a ∈ F ⁻¹' sheet (α := α) (U := U) C₀ (fun y ↦ g * f₀ y) := by
      refine ⟨by rw [hF1 a]; exact hy₀C₀, ?_⟩
      change g = g * f₀ (F a).1
      rw [hF1 a]
      change g = g * f₀ y₀
      rw [hf₀1, mul_one]
    have hy₀W' : y₀ ∈ W' := by
      rw [← hW'eq] at hamem; exact hamem
    obtain ⟨C, hC, -, hy₀C, hCsub⟩ :=
      exists_convex_open (hC₀.inter (hW'.inter hU)) ⟨hy₀C₀, hy₀W', hy₀⟩
    have heq : EqOn f (fun y ↦ g * f₀ y) C := by
      intro y hy
      have hyU := (hCsub hy).2.2
      have hmem : (⟨y, hyU⟩ : U) ∈ F ⁻¹' sheet (α := α) (U := U) C₀ (fun y ↦ g * f₀ y) := by
        rw [← hW'eq]; exact (hCsub hy).2.1
      have h2 : (F ⟨y, hyU⟩).2 = g * f₀ (F ⟨y, hyU⟩).1 := hmem.2
      rw [hF1] at h2
      simp only [f, hyU, ↓reduceDIte]
      exact h2
    have hP := hP₀.mono fun y hy ↦ (hCsub hy).1
    refine ⟨C, hC, hy₀C, fun y hy ↦ (hCsub hy).2.2,
      fun k ↦ ContMDiffMBOn.congr' hC (hP.1 k) heq, fun y hy h ↦ ?_⟩
    rw [← hP.2 y hy h]
    unfold logDeriv
    refine dMB_congr_of_eventuallyEq ?_ h
    filter_upwards [hC.mem_nhds hy] with r hr
    rw [heq hy, heq hr]
  refine ⟨f, fun k ↦ ContMDiffMBOn.of_local hU fun y hy ↦ ?_, ?_, fun x hx h ↦ ?_⟩
  · obtain ⟨C, hC, hyC, -, hP⟩ := hloc y hy
    exact ⟨C, hC, hyC, hP.1 k⟩
  · simp only [f, hx₀, ↓reduceDIte]
    rw [hF0]
    rfl
  · obtain ⟨C, -, hxC, -, hP⟩ := hloc x hx
    exact hP.2 x hxC h

end Germs

end LocallyConvex.LieGroups.MBLieGroup
