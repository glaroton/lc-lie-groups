/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Regular.Evol

/-!
# The local regularity criterion

If the evolution equation `γ(0) = 1`, `δ(γ) = ξ` has solutions for all `ξ` near `0` in
`C([0, 1], 𝔤)`, it has solutions for all `ξ`; if moreover `evol` is smooth near `0`, it is smooth
everywhere ([GN26, Lemma 6.1.4], `k = 0`). Regularity is thus a local property.

## Main results

* `MBLieGroup.HasLogDerivAt.piecewise`: two curves with the same logarithmic derivative at `t₀`
  that agree at `t₀` can be glued at `t₀`.
* `MBLieGroup.IsEvol.concat`: if `γ₀`, `γ₁` are the evolutions of the halves
  `ξ₀(t) = ξ(t/2)/2` and `ξ₁(t) = ξ((1 + t)/2)/2` of `ξ`, then `γ₀(2t)` followed by
  `γ₀(1) γ₁(2t − 1)` is the evolution of `ξ`; hence `evol(ξ) = evol(ξ₀) evol(ξ₁)`.
* `MBLieGroup.isC0Semiregular_of_local`, `MBLieGroup.isC0Regular_of_local`:
  **the local regularity criterion** ([GN26, Lemma 6.1.4], `k = 0`).

## Proof

Glöckner–Neeb cut `ξ` into `N` pieces `ξᵢ(t) = ξ((i + t)/N)/N`. We halve `ξ` repeatedly instead:
if `ξ` takes values in `2ᵐ W`, its halves take values in `2^{m-1} W`, and every `ξ` takes values in
some `2ᵐ W` since its image is compact, hence bounded. Existence and smoothness of `evol` on
`{ξ | ξ([0, 1]) ⊆ 2ᵐ W}` follow by induction on `m`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology unitInterval Pointwise
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups.MBLieGroup

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]

/-! ### Gluing curves -/

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] in
theorem HasLogDerivAt.congr_of_eventuallyEq {γ γ' : ℝ → G} {x : E} {t : ℝ}
    (h : HasLogDerivAt E γ x t) (heq : γ' =ᶠ[𝓝 t] γ) : HasLogDerivAt E γ' x t := by
  refine ⟨h.1.congr heq.symm, ?_⟩
  rw [heq.eq_of_nhds]
  exact h.2.congr_of_eventuallyEq (heq.mono fun s hs ↦ by simp only [hs])

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] in
/-- **Gluing**: two curves with the same logarithmic derivative at `t₀` that agree at `t₀`. -/
theorem HasLogDerivAt.piecewise {γ₁ γ₂ : ℝ → G} {x : E} {t₀ : ℝ} (h₁ : HasLogDerivAt E γ₁ x t₀)
    (h₂ : HasLogDerivAt E γ₂ x t₀) (heq : γ₁ t₀ = γ₂ t₀) :
    HasLogDerivAt E (fun s ↦ if s ≤ t₀ then γ₁ s else γ₂ s) x t₀ := by
  set γ := fun s ↦ if s ≤ t₀ then γ₁ s else γ₂ s
  have hγ₀ : γ t₀ = γ₁ t₀ := by simp [γ]
  have hL : EqOn γ γ₁ (Iic t₀) := fun s (hs : s ≤ t₀) ↦ by simp [γ, hs]
  have hR : EqOn γ γ₂ (Ici t₀) := fun s hs ↦ by
    rcases eq_or_lt_of_le (hs : t₀ ≤ s) with rfl | hlt
    · exact hγ₀.trans heq
    · simp [γ, not_le.2 hlt]
  refine ⟨continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩, ?_⟩
  · exact h₁.1.continuousWithinAt.congr hL hγ₀
  · exact h₂.1.continuousWithinAt.congr hR (hR (mem_Ici.2 le_rfl))
  · have d₁ := h₁.2
    have d₂ := h₂.2
    unfold HasDirDerivAt at d₁ d₂ ⊢
    rw [← nhdsLT_sup_nhdsGT]
    refine Tendsto.sup ?_ ?_
    · refine (d₁.mono_left (nhdsWithin_mono _ fun t (ht : t ∈ Iio (0 : ℝ)) ↦
        show t ≠ 0 from ne_of_lt ht)).congr'
        (eventually_nhdsWithin_of_forall fun t (ht : t < 0) ↦ ?_)
      have hs : t₀ + t • (1 : ℝ) ≤ t₀ := by simp [ht.le]
      simp only [hL hs, hγ₀]
    · refine (d₂.mono_left (nhdsWithin_mono _ fun t (ht : t ∈ Ioi (0 : ℝ)) ↦
        show t ≠ 0 from ne_of_gt ht)).congr'
        (eventually_nhdsWithin_of_forall fun t (ht : 0 < t) ↦ ?_)
      have hs : t₀ ≤ t₀ + t • (1 : ℝ) := by simp [ht.le]
      simp only [hR hs, hγ₀, heq]

omit [IsTopologicalAddGroup E] [LocallyConvexSpace ℝ E] [MBLieGroup E G] in
/-- `δ(γ(c ·))(r) = c δ(γ)(c r)`. -/
theorem HasLogDerivAt.comp_mul {γ : ℝ → G} {x : E} {c r : ℝ} (h : HasLogDerivAt E γ x (c * r)) :
    HasLogDerivAt E (fun s ↦ γ (c * s)) (c • x) r :=
  ⟨ContinuousAt.comp (g := γ) (f := fun s ↦ c * s) h.1 (by fun_prop),
    hasDirDerivAt_comp_mul (f := fun s ↦ chartAt E (1 : G) ((γ (c * r))⁻¹ * γ s)) h.2⟩

/-! ### Halves of a curve -/

/-- `t ↦ t / 2` on `[0, 1]`. -/
def halfMap₀ : C(I, I) :=
  ⟨fun t ↦ ⟨t / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩, by fun_prop⟩

/-- `t ↦ (1 + t) / 2` on `[0, 1]`. -/
def halfMap₁ : C(I, I) :=
  ⟨fun t ↦ ⟨(1 + t) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩, by fun_prop⟩

omit [IsTopologicalAddGroup E] [LocallyConvexSpace ℝ E] [T2Space E] in
/-- The halves `ξ₀(t) = ξ(t/2)/2`, `ξ₁(t) = ξ((1 + t)/2)/2`, as continuous linear maps. -/
def halfCLM (p : C(I, I)) : C(I, E) →L[ℝ] C(I, E) where
  toFun ξ := (2 : ℝ)⁻¹ • ξ.comp p
  map_add' ξ η := by
    ext t
    change (2 : ℝ)⁻¹ • (ξ (p t) + η (p t)) = (2 : ℝ)⁻¹ • ξ (p t) + (2 : ℝ)⁻¹ • η (p t)
    exact smul_add _ _ _
  map_smul' c ξ := by
    ext t
    change (2 : ℝ)⁻¹ • (c • ξ (p t)) = c • ((2 : ℝ)⁻¹ • ξ (p t))
    exact smul_comm _ _ _
  cont := (continuous_const_smul _).comp (ContinuousMap.continuous_precomp p)

omit [LocallyConvexSpace ℝ E] [T2Space E] in
@[simp] theorem halfCLM_apply (p : C(I, I)) (ξ : C(I, E)) (t : I) :
    halfCLM p ξ t = (2 : ℝ)⁻¹ • ξ (p t) := rfl

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] in
theorem extendCurve_apply (ξ : C(I, E)) (s : ℝ) : extendCurve ξ s = ξ (projIcc 0 1 zero_le_one s) :=
  rfl

omit [LocallyConvexSpace ℝ E] [T2Space E] in
theorem extendCurve_half₀ (ξ : C(I, E)) {s : ℝ} (hs : s ≤ 1) :
    extendCurve (halfCLM halfMap₀ ξ) s = (2 : ℝ)⁻¹ • extendCurve ξ (s / 2) := by
  rw [extendCurve_apply, extendCurve_apply, halfCLM_apply]
  congr 2
  apply Subtype.ext
  change (projIcc 0 1 zero_le_one s : ℝ) / 2 = projIcc 0 1 zero_le_one (s / 2)
  rcases le_or_gt s 0 with h | h
  · rw [projIcc_of_le_left _ h, projIcc_of_le_left _ (by linarith)]; simp
  · rw [projIcc_of_mem _ ⟨h.le, hs⟩, projIcc_of_mem _ ⟨by linarith, by linarith⟩]

omit [LocallyConvexSpace ℝ E] [T2Space E] in
theorem extendCurve_half₁ (ξ : C(I, E)) {s : ℝ} (hs : 0 ≤ s) :
    extendCurve (halfCLM halfMap₁ ξ) s = (2 : ℝ)⁻¹ • extendCurve ξ ((1 + s) / 2) := by
  rw [extendCurve_apply, extendCurve_apply, halfCLM_apply]
  congr 2
  apply Subtype.ext
  change (1 + (projIcc 0 1 zero_le_one s : ℝ)) / 2 = projIcc 0 1 zero_le_one ((1 + s) / 2)
  rcases le_or_gt s 1 with h | h
  · rw [projIcc_of_mem _ ⟨hs, h⟩, projIcc_of_mem _ ⟨by linarith, by linarith⟩]
  · rw [projIcc_of_right_le _ h.le, projIcc_of_right_le _ (by linarith)]; norm_num

/-! ### Concatenation -/

/-- **Concatenation**: from the evolutions of the halves of `ξ`, the evolution of `ξ`. -/
theorem IsEvol.concat {ξ : C(I, E)} {γ₀ γ₁ : ℝ → G}
    (h₀ : IsEvol E (extendCurve (halfCLM halfMap₀ ξ)) γ₀)
    (h₁ : IsEvol E (extendCurve (halfCLM halfMap₁ ξ)) γ₁) :
    IsEvol E (extendCurve ξ)
      (fun s ↦ if s ≤ 1 / 2 then γ₀ (2 * s) else γ₀ 1 * γ₁ (2 * s - 1)) := by
  have := isTopologicalGroup E G
  -- the two pieces
  have hA : ∀ t, t ≤ 1 / 2 → HasLogDerivAt E (fun s ↦ γ₀ (2 * s)) (extendCurve ξ t) t := by
    intro t ht
    have h := (h₀.2 (2 * t)).comp_mul (c := 2) (r := t)
    rwa [extendCurve_half₀ ξ (by linarith), smul_smul, mul_inv_cancel₀ (two_ne_zero),
      one_smul, mul_div_cancel_left₀ _ two_ne_zero] at h
  have hB : ∀ t, 1 / 2 ≤ t →
      HasLogDerivAt E (fun s ↦ γ₀ 1 * γ₁ (2 * s - 1)) (extendCurve ξ t) t := by
    intro t ht
    have h := ((h₁.2 (2 * t - 1)).comp_add_const (-1)).comp_mul (c := 2) (r := t)
    simp only [← sub_eq_add_neg] at h
    rw [extendCurve_half₁ ξ (by linarith), smul_smul, mul_inv_cancel₀ (two_ne_zero),
      one_smul] at h
    have h2 : (1 + (2 * t - 1)) / 2 = t := by ring
    rw [h2] at h
    exact h.mul_left (γ₀ 1)
  refine ⟨?_, fun t ↦ ?_⟩
  · simp [h₀.1]
  rcases lt_trichotomy t (1 / 2) with ht | rfl | ht
  · refine (hA t ht.le).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds ht] with s hs
    have hs' : s ≤ 1 / 2 := le_of_lt hs
    simp only [hs', ↓reduceIte]
  · refine (hA _ le_rfl).piecewise (hB _ le_rfl) ?_
    simp [h₁.1]
  · refine (hB t ht.le).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht] with s hs
    have hs' : ¬ s ≤ 1 / 2 := not_le.2 hs
    simp only [hs', ↓reduceIte]

theorem evol_eq_mul {ξ : C(I, E)} {γ₀ γ₁ : ℝ → G}
    (h₀ : IsEvol E (extendCurve (halfCLM halfMap₀ ξ)) γ₀)
    (h₁ : IsEvol E (extendCurve (halfCLM halfMap₁ ξ)) γ₁) :
    evol E G ξ = evol E G (halfCLM halfMap₀ ξ) * evol E G (halfCLM halfMap₁ ξ) := by
  rw [evol_eq (h₀.concat h₁), evol_eq h₀, evol_eq h₁]
  norm_num

/-! ### Smoothness on open subsets -/

section ContMDiff

variable {E' F' : Type u} [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E']
  [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
  [AddCommGroup F'] [Module ℝ F'] [TopologicalSpace F']
  [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] [LocallyConvexSpace ℝ F'] [T2Space F']
  {M : Type*} [TopologicalSpace M] [ChartedSpace E' M] {N : Type*} [TopologicalSpace N]
  [ChartedSpace F' N] {k : ℕ} {f g : M → N} {U V : Set M}

omit [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] [LocallyConvexSpace ℝ F'] [T2Space F'] in
theorem _root_.LocallyConvex.Manifolds.ContMDiffMBOn.mono'
    (hf : ContMDiffMBOn (E := E') (F := F') k f U)
    (hVU : V ⊆ U) : ContMDiffMBOn (E := E') (F := F') k f V :=
  ⟨hf.1.mono hVU, fun x hx ↦ (hf.2 x (hVU hx)).mono fun _ hy ↦
    ⟨hy.1, hVU hy.2.1, hy.2.2⟩⟩

omit [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] [LocallyConvexSpace ℝ F'] in
theorem _root_.LocallyConvex.Manifolds.ContMDiffMBOn.congr' (hU : IsOpen U)
    (hf : ContMDiffMBOn (E := E') (F := F') k f U)
    (h : EqOn g f U) : ContMDiffMBOn (E := E') (F := F') k g U := by
  refine ⟨hf.1.congr h, fun x hx ↦ ?_⟩
  have hD : chartDomain g U (chartAt E' x) (chartAt F' (g x)) =
      chartDomain f U (chartAt E' x) (chartAt F' (f x)) := by
    rw [h hx]
    ext y
    simp only [chartDomain, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rwa [← h h2]⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rwa [h h2]⟩
  rw [hD, h hx]
  exact ContDiffMBOn.congr_of_isOpen (isOpen_chartDomain hU hf.1 _ _)
    (fun y hy ↦ by simp only [Function.comp_apply, h hy.2.1]) (hf.2 x hx)

end ContMDiff

/-! ### The local regularity criterion -/

/-- The curves with values in `W`, an open set of `C([0, 1], E)` if `W` is open. -/
def valIn (W : Set E) : Set C(I, E) := {ξ | ∀ t, ξ t ∈ W}

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] in
theorem isOpen_valIn {W : Set E} (hW : IsOpen W) : IsOpen (valIn W) := by
  have h := ContinuousMap.isOpen_setOfPred_mapsTo (X := I) isCompact_univ hW
  convert h using 1
  ext ξ
  simp [valIn, MapsTo]

omit [LocallyConvexSpace ℝ E] [T2Space E] in
theorem halfCLM_mem_valIn {W : Set E} {m : ℕ} {ξ : C(I, E)}
    (hξ : ξ ∈ valIn ((2 : ℝ) ^ (m + 1) • W)) (p : C(I, I)) :
    halfCLM p ξ ∈ valIn ((2 : ℝ) ^ m • W) := by
  intro t
  obtain ⟨w, hw, hwe⟩ := Set.mem_smul_set.1 (hξ (p t))
  refine Set.mem_smul_set.2 ⟨w, hw, ?_⟩
  rw [halfCLM_apply, ← hwe, smul_smul, pow_succ]
  congr 1
  field_simp

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- Every curve takes values in some `2ᵐ W`: its image is compact, hence bounded. -/
theorem exists_mem_valIn {W : Set E} (hW : W ∈ 𝓝 (0 : E)) (ξ : C(I, E)) :
    ∃ m : ℕ, ξ ∈ valIn ((2 : ℝ) ^ m • W) := by
  have hb : Bornology.IsVonNBounded ℝ (range ξ) :=
    (isCompact_range ξ.continuous).isVonNBounded (𝕜 := ℝ)
  have ht : Tendsto (fun m : ℕ ↦ (2 : ℝ) ^ m) atTop (Bornology.cobounded ℝ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    simpa using tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  obtain ⟨m, hm⟩ := (ht.eventually (hb hW)).exists
  exact ⟨m, fun t ↦ hm (mem_range_self t)⟩

variable {W : Set E}

/-- Existence on `{ξ | ξ([0, 1]) ⊆ 2ᵐ W}`, by induction on `m`. -/
theorem exists_isEvol_of_valIn
    (hsol : ∀ ξ ∈ valIn W, ∃ γ : ℝ → G, IsEvol E (extendCurve ξ) γ) (m : ℕ) :
    ∀ ξ ∈ valIn ((2 : ℝ) ^ m • W), ∃ γ : ℝ → G, IsEvol E (extendCurve ξ) γ := by
  induction m with
  | zero => intro ξ hξ; exact hsol ξ (by simpa using hξ)
  | succ m ih =>
    intro ξ hξ
    obtain ⟨γ₀, h₀⟩ := ih _ (halfCLM_mem_valIn hξ halfMap₀)
    obtain ⟨γ₁, h₁⟩ := ih _ (halfCLM_mem_valIn hξ halfMap₁)
    exact ⟨_, h₀.concat h₁⟩

/-- **The local regularity criterion, existence** ([GN26, Lemma 6.1.4], `k = 0`): if every curve
with values in a `0`-neighborhood `W` has an evolution, every curve has one. -/
theorem isC0Semiregular_of_local (hW : W ∈ 𝓝 (0 : E))
    (hsol : ∀ ξ ∈ valIn W, ∃ γ : ℝ → G, IsEvol E (extendCurve ξ) γ) : IsC0Semiregular E G :=
  fun ξ ↦ by
    obtain ⟨m, hm⟩ := exists_mem_valIn hW ξ
    exact exists_isEvol_of_valIn hsol m ξ hm

/-- `C^k` on `{ξ | ξ([0, 1]) ⊆ 2ᵐ W}`, by induction on `m`. -/
theorem contMDiffMBOn_evol_valIn (hWo : IsOpen W) (hsemi : IsC0Semiregular E G) {k : ℕ}
    (hsm : ContMDiffMBOn (E := C(I, E)) (F := E) k (evol E G) (valIn W)) (m : ℕ) :
    ContMDiffMBOn (E := C(I, E)) (F := E) k (evol E G) (valIn ((2 : ℝ) ^ m • W)) := by
  induction m with
  | zero => simpa using hsm
  | succ m ih =>
    have hV : IsOpen (valIn ((2 : ℝ) ^ (m + 1) • W)) :=
      isOpen_valIn (hWo.smul₀ (by positivity))
    have hV' : IsOpen (valIn ((2 : ℝ) ^ m • W)) := isOpen_valIn (hWo.smul₀ (by positivity))
    have hh : ∀ p, ContMDiffMBOn (E := C(I, E)) (F := C(I, E)) k (halfCLM p)
        (valIn ((2 : ℝ) ^ (m + 1) • W)) :=
      fun p ↦ (contMDiffMBOn_iff_contDiffMBOn hV).2 ((halfCLM (E := E) p).contDiffMBOn k _)
    have h₀ := ih.comp hV hV' (hh halfMap₀) fun ξ hξ ↦ halfCLM_mem_valIn hξ halfMap₀
    have h₁ := ih.comp hV hV' (hh halfMap₁) fun ξ hξ ↦ halfCLM_mem_valIn hξ halfMap₁
    have hprod := (smoothMBM_mul (E := E) (G := G) k).comp hV isOpen_univ
      (ContMDiffMBOn.prodMk hV h₀ h₁) (mapsTo_univ _ _)
    refine ContMDiffMBOn.congr' hV hprod fun ξ _ ↦ ?_
    obtain ⟨γ₀, hγ₀⟩ := hsemi (halfCLM halfMap₀ ξ)
    obtain ⟨γ₁, hγ₁⟩ := hsemi (halfCLM halfMap₁ ξ)
    exact evol_eq_mul hγ₀ hγ₁

/-- **The local regularity criterion, smoothness** ([GN26, Lemma 6.1.4], `k = 0`): for a
`C⁰`-semiregular group, if for every `k` the evolution map is `C^k` on the curves with values in
some open `0`-neighborhood `W_k`, then `G` is `C⁰`-regular. -/
theorem isC0Regular_of_local' (hsemi : IsC0Semiregular E G)
    (hsm : ∀ k : ℕ, ∃ W : Set E, IsOpen W ∧ (0 : E) ∈ W ∧
      ContMDiffMBOn (E := C(I, E)) (F := E) k (evol E G) (valIn W)) : IsC0Regular E G where
  semiregular := hsemi
  smooth k := by
    obtain ⟨W, hWo, hW0, hsmk⟩ := hsm k
    have hV : ∀ m : ℕ, IsOpen (valIn ((2 : ℝ) ^ m • W)) := fun m ↦
      isOpen_valIn (hWo.smul₀ (by positivity))
    have hsmooth := contMDiffMBOn_evol_valIn hWo hsemi hsmk
    obtain ⟨W₀, hW₀o, hW₀0, hsm₀⟩ := hsm 0
    have hsmooth₀ := contMDiffMBOn_evol_valIn hW₀o hsemi hsm₀
    have hc : Continuous (evol E G) := continuous_iff_continuousAt.2 fun ξ ↦ by
      obtain ⟨m, hm⟩ := exists_mem_valIn (hW₀o.mem_nhds hW₀0) ξ
      exact ((hsmooth₀ m).1 ξ hm).continuousAt
        ((isOpen_valIn (hW₀o.smul₀ (by positivity))).mem_nhds hm)
    refine contMDiffMB_of_chartAt hc fun ξ ↦ ?_
    obtain ⟨m, hm⟩ := exists_mem_valIn (hWo.mem_nhds hW0) ξ
    set e := chartAt C(I, E) ξ
    set e' := chartAt E (evol E G ξ)
    refine ⟨chartDomain (evol E G) (valIn ((2 : ℝ) ^ m • W)) e e',
      isOpen_chartDomain (hV m) (hsmooth m).1 e e', ?_, fun y hy ↦ ⟨hy.1, mem_univ _, hy.2.2⟩,
      (hsmooth m).2 ξ hm⟩
    refine ⟨e.map_source (mem_chart_source _ ξ), ?_, ?_⟩
    · rw [e.left_inv (mem_chart_source _ ξ)]
      exact hm
    · change evol E G (e.symm (e ξ)) ∈ e'.source
      rw [e.left_inv (mem_chart_source _ ξ)]
      exact mem_chart_source E _

/-- **The local regularity criterion** ([GN26, Lemma 6.1.4], `k = 0`): if every curve with values
in an open `0`-neighborhood `W` has an evolution, and `evol` is smooth on these curves, then `G` is
`C⁰`-regular. -/
theorem isC0Regular_of_local (hWo : IsOpen W) (hW0 : (0 : E) ∈ W)
    (hsol : ∀ ξ ∈ valIn W, ∃ γ : ℝ → G, IsEvol E (extendCurve ξ) γ)
    (hsm : SmoothMBMOn C(I, E) E (evol E G) (valIn W)) : IsC0Regular E G :=
  isC0Regular_of_local' (isC0Semiregular_of_local (hWo.mem_nhds hW0) hsol)
    fun k ↦ ⟨W, hWo, hW0, hsm k⟩

/-- **The local regularity criterion** in the form of [GN26, Lemma 6.1.4] (`k = 0`): for an open
`0`-neighborhood `U` of `C([0, 1], 𝔤)` on which evolutions exist and `evol` is smooth. -/
theorem isC0Regular_of_nhds {U : Set C(I, E)} (hU : IsOpen U) (h0 : (0 : C(I, E)) ∈ U)
    (hsol : ∀ ξ ∈ U, ∃ γ : ℝ → G, IsEvol E (extendCurve ξ) γ)
    (hsm : SmoothMBMOn C(I, E) E (evol E G) U) : IsC0Regular E G := by
  have hb := (𝓝 (0 : E)).basis_sets.nhds_continuousMapConst (X := I)
  obtain ⟨⟨K, W⟩, ⟨-, hW⟩, hsub⟩ := hb.mem_iff.1 (hU.mem_nhds h0)
  have hWU : valIn (interior W) ⊆ U := fun ξ hξ ↦ hsub fun t _ ↦ interior_subset (hξ t)
  exact isC0Regular_of_local isOpen_interior (mem_interior_iff_mem_nhds.2 hW)
    (fun ξ hξ ↦ hsol ξ (hWU hξ)) (fun k ↦ ContMDiffMBOn.mono' (hsm k) hWU)

end LocallyConvex.LieGroups.MBLieGroup
