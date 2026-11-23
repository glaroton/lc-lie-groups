/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.CircleCover.Group
public import LocallyConvexAnalysis.Calculus.ImplicitFinite
public import LocallyConvexAnalysis.MappingSpace.SuperpositionParam

/-!
# The inversion of the universal cover of `Diff⁺(S¹)` is smooth

For `u ∈ Ω = {u ∈ C^∞_per : 1 + u' > 0}`, the inverse of `id + u` is `id + η(u)` with
`η(u) ∈ Ω` (lc-manifolds, `DiffCircle.inv`). We show that `η : Ω → C^∞_per` is smooth.

## Proof

* `G(u, y) = η(u)(y)` solves `Φ((u, y), G(u, y)) = 0` for `Φ((u, y), σ) = σ + u(y + σ)`, and
  `∂_σ Φ = 1 + u'(y + σ) > 0`. `Φ` is smooth on `C^∞_per × ℝ × ℝ` (evaluation is a
  precomposition), and `G` is continuous on `Ω × ℝ`: if `c ≤ 1 + u₀'`, then
  `c |z − z₀| ≤ p₀(u − u₀) + |y − y₀|` for `z = y + G(u, y)`, `z₀ = y₀ + G(u₀, y₀)`. By the implicit
  function theorem with locally convex parameters and finite-dimensional values (lc-analysis,
  `contDiffMBOn_of_implicit`), `G` is smooth on `Ω × ℝ`.
* The `y`-derivatives `G_m(u, y) = ∂_y^m G(u, y)` are smooth on `Ω × ℝ`, and the superposition
  operators with parameters of lc-analysis (`contDiffMBOn_superposeParam_of_contDiffMBOn`) show
  that `u ↦ G_m(u, ·)|_{[0,1]} ∈ C([0, 1])` is smooth.
* For periodic functions the sup norm over `ℝ` is the sup norm over `[0, 1]`, so
  `u ↦ (u^{(m)}|_{[0,1]})_m` is a uniform embedding of `C^∞_per` into `∏_m C([0, 1])`, with closed
  range since `C^∞_per` is complete. Hence `η` is smooth into `C^∞_per`.

## Main results

* `CircleCover.contDiffMBOn_implicitInv`: `G` is smooth on `Ω × ℝ`.
* `CircleCover.smoothMBOn_inv`: **`η` is smooth on `Ω`**.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function
open scoped Topology BoundedContinuousFunction
open LocallyConvex.Analysis LocallyConvex.Manifolds CInfPer DiffCircle

noncomputable section

namespace LocallyConvex.LieGroups.CircleCover

/-! ### Constants and evaluation -/

/-- Constant functions, as a continuous linear map `ℝ → C^∞_per`. -/
def constCLM : ℝ →L[ℝ] CInfPer where
  toFun := const
  map_add' a b := by ext; simp
  map_smul' c a := by ext; simp
  cont := continuous_iff.2 fun k ↦ by
    cases k with
    | zero =>
      refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun a b ↦ ?_)
      rw [NNReal.coe_one, one_mul]
      refine (BoundedContinuousFunction.dist_le dist_nonneg).2 fun x ↦ ?_
      simp
    | succ k =>
      have h : ∀ z : ℝ, derivBCF (k + 1) (const z) = 0 := fun z ↦ by
        ext x
        simp [iteratedDeriv_succ']
      simp only [h]
      exact continuous_const

@[simp] theorem constCLM_apply (z : ℝ) : constCLM z = const z := rfl

/-- The evaluation `(u, z) ↦ u(z)`. -/
def ev (p : CInfPer × ℝ) : ℝ := p.1 p.2

theorem smoothMBOn_ev : SmoothMBOn ev univ := fun k ↦ by
  set A : CInfPer × ℝ →L[ℝ] CInfPer × CInfPer :=
    (ContinuousLinearMap.fst ℝ CInfPer ℝ).prod (constCLM.comp (ContinuousLinearMap.snd ℝ _ _))
  have hP : ContDiffMBOn k (fun p ↦ precompBCF (A p)) univ := by
    have := ContDiffMBOn.comp_clm A isOpen_univ (contDiffMBOn_precompBCF k)
    rwa [preimage_univ] at this
  have h := ContDiffMBOn.comp isOpen_univ isOpen_univ
    ((BoundedContinuousFunction.evalCLM ℝ (0 : ℝ)).contDiffMBOn k univ) hP (mapsTo_univ _ _)
  refine ContDiffMBOn.congr_of_isOpen isOpen_univ (fun p _ ↦ ?_) h
  simp [A, ev, precompBCF_apply]

/-! ### The implicit equation -/

/-- `Φ((u, y), σ) = σ + u(y + σ)`. -/
def Φ (q : (CInfPer × ℝ) × ℝ) : ℝ := q.2 + q.1.1 (q.1.2 + q.2)

theorem smoothMBOn_Φ : SmoothMBOn Φ univ := fun k ↦ by
  set A : (CInfPer × ℝ) × ℝ →L[ℝ] CInfPer × ℝ :=
    ((ContinuousLinearMap.fst ℝ CInfPer ℝ).comp (ContinuousLinearMap.fst ℝ _ ℝ)).prod
      ((ContinuousLinearMap.snd ℝ CInfPer ℝ).comp (ContinuousLinearMap.fst ℝ _ ℝ) +
        ContinuousLinearMap.snd ℝ _ ℝ)
  have he : ContDiffMBOn k (fun q ↦ ev (A q)) univ := by
    have := ContDiffMBOn.comp_clm A isOpen_univ (smoothMBOn_ev k)
    rwa [preimage_univ] at this
  have h := ((ContinuousLinearMap.snd ℝ (CInfPer × ℝ) ℝ).contDiffMBOn k univ).add isOpen_univ he
  refine ContDiffMBOn.congr_of_isOpen isOpen_univ (fun q _ ↦ ?_) h
  simp [A, ev, Φ]

open Classical in
/-- The inverse `η(u) = (id + u)⁻¹ − id` for `u ∈ Ω`, and `0` otherwise. -/
def η (u : CInfPer) : CInfPer := if hu : u ∈ domain then inv hu else 0

theorem η_of_mem {u : CInfPer} (hu : u ∈ domain) : η u = inv hu := by
  simp [η, hu]

theorem lift_lift_η {u : CInfPer} (hu : u ∈ domain) (y : ℝ) : lift u (lift (η u) y) = y := by
  rw [η_of_mem hu, lift_inv, ← liftHomeomorph_apply hu, Homeomorph.apply_symm_apply]

/-- `G(u, y) = η(u)(y)`. -/
def G (p : CInfPer × ℝ) : ℝ := η p.1 p.2

theorem Φ_G {p : CInfPer × ℝ} (hp : p.1 ∈ domain) : Φ (p, G p) = 0 := by
  have h := lift_lift_η hp p.2
  simp only [lift] at h
  simp only [Φ, G]
  linarith

/-- `c |a − b| ≤ |lift u a − lift u b|` if `c ≤ 1 + u'`. -/
theorem mul_abs_sub_le {u : CInfPer} {c : ℝ} (hc : ∀ x, c ≤ 1 + deriv u x) (a b : ℝ) :
    c * |a - b| ≤ |lift u a - lift u b| := by
  have hd : Differentiable ℝ (lift u) := fun x ↦ (hasDerivAt_lift u x).differentiableAt
  have hd' : ∀ x, c ≤ deriv (lift u) x := fun x ↦ by rw [(hasDerivAt_lift u x).deriv]; exact hc x
  rcases le_total a b with hab | hab
  · have h := mul_sub_le_image_sub_of_le_deriv hd hd' hab
    rw [abs_of_nonpos (sub_nonpos.2 hab), abs_sub_comm (lift u a)]
    refine (le_of_eq (by ring)).trans (h.trans (le_abs_self _))
  · have h := mul_sub_le_image_sub_of_le_deriv hd hd' hab
    rw [abs_of_nonneg (sub_nonneg.2 hab)]
    exact h.trans (le_abs_self _)

/-- **`G` is continuous on `Ω × ℝ`.** -/
theorem continuousOn_G : ContinuousOn G (domain ×ˢ univ) := by
  rintro ⟨u₀, y₀⟩ ⟨hu₀, -⟩
  obtain ⟨c, hc, hc'⟩ := exists_pos_le hu₀
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  set B : CInfPer × ℝ → ℝ := fun p ↦ c⁻¹ * (seminorm 0 (p.1 - u₀) + |p.2 - y₀|) + |p.2 - y₀|
  have hB : Continuous B := by
    have h0 : Continuous (seminorm 0) := (continuous_derivBCF 0).norm
    fun_prop
  have hB0 : B (u₀, y₀) = 0 := by simp [B]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) ?_
    (hB0 ▸ (hB.tendsto (u₀, y₀)).mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with p hp
  obtain ⟨u, y⟩ := p
  have hu : u ∈ domain := hp.1
  set z := lift (η u) y
  set z₀ := lift (η u₀) y₀
  have hz : lift u z = y := lift_lift_η hu y
  have hz₀ : lift u₀ z₀ = y₀ := lift_lift_η hu₀ y₀
  have h1 : c * |z - z₀| ≤ seminorm 0 (u - u₀) + |y - y₀| := by
    refine (mul_abs_sub_le hc' z z₀).trans ?_
    rw [hz₀]
    have e : lift u₀ z - y₀ = (u₀ z - u z) + (y - y₀) := by
      rw [← hz]; simp only [lift]; ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
    have := abs_apply_le (u - u₀) z
    simp only [coe_sub, Pi.sub_apply] at this
    rwa [abs_sub_comm]
  have h2 : |z - z₀| ≤ c⁻¹ * (seminorm 0 (u - u₀) + |y - y₀|) := by
    rw [le_inv_mul_iff₀ hc]; exact h1
  have hG : G (u, y) - G (u₀, y₀) = (z - z₀) - (y - y₀) := by
    simp only [G, z, z₀, lift]; ring
  rw [Real.dist_eq, hG]
  calc |z - z₀ - (y - y₀)| ≤ |z - z₀| + |y - y₀| := abs_sub _ _
    _ ≤ B (u, y) := add_le_add h2 le_rfl

/-- Directional derivatives along `ℝ` are derivatives. -/
theorem hasDirDerivAt_one {f : ℝ → ℝ} {x f' : ℝ} (h : HasDerivAt f f' x) :
    HasDirDerivAt f x 1 f' := by
  unfold HasDirDerivAt
  simpa [smul_eq_mul] using h.tendsto_slope_zero

theorem dMB_Φ_snd (u : CInfPer) (y σ : ℝ) :
    dMB Φ (((u, y), σ), (0, 1)) = 1 + deriv u (y + σ) := by
  rw [dMB_slice₂]
  have h : HasDerivAt (fun s ↦ Φ ((u, y), s)) (1 + deriv u (y + σ)) σ := by
    have := (hasDerivAt_id σ).add ((hasDerivAt u (y + σ)).comp σ
      ((hasDerivAt_id σ).const_add y))
    simp only [mul_one] at this
    exact this
  exact (hasDirDerivAt_one h).dMB_eq

theorem isUnit_partialFDeriv₂ {p : CInfPer × ℝ} (hp : p.1 ∈ domain) :
    IsUnit (partialFDeriv₂ Φ (p, G p)) := by
  set B := partialFDeriv₂ Φ (p, G p)
  have hB : ∀ v, B v = v * (1 + deriv p.1 (p.2 + G p)) := by
    intro v
    rw [(hasFDerivAt_partialFDeriv₂ isOpen_univ (smoothMBOn_Φ 1) (mem_univ _)).2]
    have h1 : B 1 = 1 + deriv p.1 (p.2 + G p) := by
      rw [(hasFDerivAt_partialFDeriv₂ isOpen_univ (smoothMBOn_Φ 1) (mem_univ _)).2]
      exact dMB_Φ_snd p.1 p.2 (G p)
    rw [← (hasFDerivAt_partialFDeriv₂ isOpen_univ (smoothMBOn_Φ 1) (mem_univ _)).2, ← h1,
      ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  set c := 1 + deriv p.1 (p.2 + G p)
  have hc : c ≠ 0 := (hp _).ne'
  refine ⟨⟨B, c⁻¹ • ContinuousLinearMap.id ℝ ℝ, ?_, ?_⟩, rfl⟩
  · ext; simp [hB, hc]
  · ext; simp [hB, hc]

/-- **`G(u, y) = η(u)(y)` is smooth on `Ω × ℝ`** (implicit function theorem). -/
theorem contDiffMBOn_G (k : ℕ) : ContDiffMBOn k G (domain ×ˢ univ) :=
  contDiffMBOn_of_implicit isOpen_univ (smoothMBOn_Φ k) (isOpen_domain.prod isOpen_univ)
    continuousOn_G (fun _ _ ↦ mem_univ _) (fun _ hp ↦ Φ_G hp.1)
    fun _ hp ↦ isUnit_partialFDeriv₂ hp.1


/-! ### Derivatives in `y` -/

section Uncurry

variable {X : Type} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X]
  {U : Set X} {F : X × ℝ → ℝ} {g : X → CInfPer}

/-- `F_m(u, y) = ∂_y^m F(u, y)`, as iterated directional derivatives in the direction `(0, 1)`. -/
def Fd (F : X × ℝ → ℝ) : ℕ → X × ℝ → ℝ
  | 0 => F
  | m + 1 => fun p ↦ dMB (Fd F m) (p, (0, 1))

theorem smoothMBOn_Fd (hU : IsOpen U) (hF : SmoothMBOn F (U ×ˢ univ)) (m : ℕ) :
    SmoothMBOn (Fd F m) (U ×ˢ univ) := by
  induction m with
  | zero => exact hF
  | succ m ih => exact ih.dMB_dir (hU.prod isOpen_univ) (0, 1)

omit [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [T2Space X] in
theorem Fd_apply (hg : ∀ u ∈ U, ∀ y, g u y = F (u, y)) (m : ℕ) {u : X} (hu : u ∈ U)
    (y : ℝ) : Fd F m (u, y) = iteratedDeriv m (g u) y := by
  induction m generalizing y with
  | zero => exact (hg u hu y).symm
  | succ m ih =>
    change dMB (Fd F m) (((u, y) : X × ℝ), ((0 : X), (1 : ℝ))) = _
    rw [dMB_slice₂]
    have hf : (fun y' ↦ Fd F m (u, y')) = iteratedDeriv m (g u) := funext ih
    rw [hf, iteratedDeriv_succ]
    exact (hasDirDerivAt_one ((g u).differentiable_iteratedDeriv m y).hasDerivAt).dMB_eq

end Uncurry

/-! ### Restriction to `[0, 1]` -/

/-- The compact interval `[0, 1]`. -/
abbrev I01 : Type := Icc (0 : ℝ) 1

/-- The restriction `BC(ℝ) → C([0, 1])`. -/
def restrictCLM : (ℝ →ᵇ ℝ) →L[ℝ] C(I01, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ f.toContinuousMap.restrict (Icc (0 : ℝ) 1)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl } 1 fun f ↦ by
    rw [one_mul]
    exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun s ↦ f.norm_coe_le_norm s

@[simp] theorem restrictCLM_apply (f : ℝ →ᵇ ℝ) (s : I01) : restrictCLM f s = f s := rfl

/-- For periodic functions, the sup norm over `ℝ` is the sup norm over `[0, 1]`. -/
theorem norm_restrictCLM_derivBCF (m : ℕ) (u : CInfPer) :
    ‖restrictCLM (derivBCF m u)‖ = ‖derivBCF m u‖ := by
  refine le_antisymm ((restrictCLM.le_opNorm _).trans ?_) ?_
  · refine mul_le_of_le_one_left (norm_nonneg _) ?_
    exact LinearMap.mkContinuous_norm_le _ zero_le_one _
  · refine (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x ↦ ?_
    have hx : Int.fract x ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
    have h := (restrictCLM (derivBCF m u)).norm_coe_le_norm ⟨Int.fract x, hx⟩
    have hp : iteratedDeriv m u (Int.fract x) = iteratedDeriv m u x := by
      unfold Int.fract
      simpa using (u.periodic_iteratedDeriv m).sub_int_mul_eq (x := x) ⌊x⌋
    rw [restrictCLM_apply, coe_derivBCF, hp] at h
    simpa using h

/-- `u ↦ (u^{(m)}|_{[0,1]})_m`. -/
def J' : CInfPer →L[ℝ] (ℕ → C(I01, ℝ)) :=
  ContinuousLinearMap.pi fun m ↦ restrictCLM.comp (derivCLM m)

@[simp] theorem J'_apply (u : CInfPer) (m : ℕ) : J' u m = restrictCLM (derivBCF m u) := rfl

theorem dist_J' (m : ℕ) (u v : CInfPer) :
    dist (J' u m) (J' v m) = dist (derivBCF m u) (derivBCF m v) := by
  rw [dist_eq_norm, dist_eq_norm, J'_apply, J'_apply, ← map_sub]
  have h : derivBCF m u - derivBCF m v = derivBCF m (u - v) := (map_sub (derivL m) u v).symm
  rw [h]
  exact norm_restrictCLM_derivBCF m (u - v)

/-- **`J'` is a uniform embedding**: it induces the uniform structure of `C^∞_per`. -/
theorem isUniformInducing_J' : IsUniformInducing J' := by
  refine ⟨?_⟩
  rw [← isUniformInducing_J.comap_uniformity, Pi.uniformity, Pi.uniformity, comap_iInf,
    comap_iInf]
  refine iInf_congr fun m ↦ ?_
  rw [comap_comap, comap_comap, Metric.uniformity_eq_comap_nhds_zero,
    Metric.uniformity_eq_comap_nhds_zero, comap_comap, comap_comap]
  congr 1
  funext p
  exact dist_J' m p.1 p.2

theorem isEmbedding_J' : Topology.IsEmbedding J' :=
  ⟨isUniformInducing_J'.isInducing, isUniformInducing_J'.isInducing.injective⟩

theorem isClosed_range_J' : IsClosed (range J') :=
  isUniformInducing_J'.isComplete_range.isClosed

/-! ### Smoothness into `C^∞_per` -/

section Uncurry

variable {X : Type} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X]
  {U : Set X} {F : X × ℝ → ℝ} {g : X → CInfPer}

/-- `H̃_m(y, (e, u)) = F_m(u, y)`. -/
def Ht (F : X × ℝ → ℝ) (m : ℕ) (q : ℝ × (ℝ × X)) : ℝ := Fd F m (q.2.2, q.1)

theorem component_contDiffMBOn (hU : IsOpen U) (hF : SmoothMBOn F (U ×ˢ univ))
    (hg : ∀ u ∈ U, ∀ y, g u y = F (u, y)) (k m : ℕ) :
    ContDiffMBOn k (fun u ↦ J' (g u) m) U := by
  set O : Set (ℝ × (ℝ × X)) := (fun q ↦ (q.2.2, q.1)) ⁻¹' (U ×ˢ univ)
  have hO : IsOpen O := (hU.prod isOpen_univ).preimage (by fun_prop)
  set A : ℝ × (ℝ × X) →L[ℝ] X × ℝ :=
    ((ContinuousLinearMap.snd ℝ ℝ X).comp (ContinuousLinearMap.snd ℝ ℝ _)).prod
      (ContinuousLinearMap.fst ℝ ℝ _)
  have hH : ContDiffMBOn k (Ht F m) O := by
    have := ContDiffMBOn.comp_clm A (hU.prod isOpen_univ) (smoothMBOn_Fd hU hF m k)
    exact this
  have hΩ : IsOpen ((univ : Set ℝ) ×ˢ U) := isOpen_univ.prod hU
  have hS := contDiffMBOn_superposeParam_of_contDiffMBOn (K := I01) (E := ℝ) Subtype.val
    continuous_subtype_val k (E' := ℝ) (Z := X) (H := Ht F m) hO hΩ
    (fun _ x hx ↦ ⟨hx.2, mem_univ _⟩) hH
  set ι : X →L[ℝ] C(I01, ℝ) × X :=
    ContinuousLinearMap.inr ℝ C(I01, ℝ) X
  have hmaps : MapsTo ι U (paramDomain I01 ((univ : Set ℝ) ×ˢ U)) :=
    fun u hu _ ↦ ⟨mem_univ _, hu⟩
  have h := ContDiffMBOn.comp hU (isOpen_paramDomain hΩ) hS (ι.contDiffMBOn k U) hmaps
  refine ContDiffMBOn.congr_of_isOpen hU (fun u hu ↦ ?_) h
  ext s
  have hH0 : ContinuousOn (fun r : I01 × (ℝ × X) ↦ Ht F m ((r.1 : ℝ), r.2))
      (univ ×ˢ ((univ : Set ℝ) ×ˢ U)) :=
    (hH.continuousOn).comp ((continuous_subtype_val.comp continuous_fst).prodMk
      continuous_snd).continuousOn fun r hr ↦ ⟨hr.2.2, mem_univ _⟩
  simp only [Function.comp_apply]
  rw [superposeParam_apply hH0 (hmaps hu) s]
  simp [Ht, ι, Fd_apply hg m hu]

/-- **Smoothness into `C^∞_per` from smoothness of the uncurried map**: if `g(u)(y) = F(u, y)`
with `F` smooth on `U × ℝ`, then `g` is smooth on `U`. -/
theorem smoothMBOn_of_uncurry (hU : IsOpen U) (hF : SmoothMBOn F (U ×ˢ univ))
    (hg : ∀ u ∈ U, ∀ y, g u y = F (u, y)) : SmoothMBOn g U := fun k ↦
  contDiffMBOn_of_isClosedEmbedding J' isEmbedding_J' isClosed_range_J' hU
    (contDiffMBOn_pi hU fun m ↦ component_contDiffMBOn hU hF hg k m)

end Uncurry

/-! ### Smoothness of the inversion -/

/-- **The inversion `η(u) = (id + u)⁻¹ − id` is smooth on `Ω`.** -/
theorem smoothMBOn_η : SmoothMBOn η domain :=
  smoothMBOn_of_uncurry isOpen_domain contDiffMBOn_G fun _ _ _ ↦ rfl

end LocallyConvex.LieGroups.CircleCover
