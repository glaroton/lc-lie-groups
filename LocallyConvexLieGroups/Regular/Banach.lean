/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Regular.Primitive
public import LocallyConvexLieGroups.LieAlgebra.Semidirect
public import LocallyConvexAnalysis.ODE.Flow
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Banach–Lie groups are `C⁰`-regular

Let `G` be a Lie group modeled on a Banach space `E`, with the multiplication `∗` in the chart `φ`
at the identity and `z₀ = φ(1)`. In the chart, `δ(γ) = ξ` reads `c' = x̃_l(ξ(t))(c)` for
`c = φ ∘ γ`, where `x̃_l(v)(z) = d(z ∗ ·)(z₀) v` is the left invariant field. With `c = z₀ + u`
and `ψ(a, v) = x̃_l(v)(z₀ + a)`, in integral form `u = J(ψ(u, ξ))`. We solve it by the inverse
function theorem in the Banach space `C([0, 1], E)²` for
`Φ(ξ, u) = (ξ, u − J(ψ ∘ (u, ξ)))`, whose derivative at `0` is `(h, k) ↦ (h, k − J h)` since
`ψ(a, 0) = 0` and `ψ(0, v) = v` ([GN26, Theorem 6.3.4]).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace Metric
open scoped Topology unitInterval ContDiff
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups.MBLieGroup

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]

/-! ### The right-hand side -/

variable (G) in
/-- `ψ(a, v) = x̃_l(v)(z₀ + a)`, the left invariant field in the chart, centered at `z₀ = φ(1)`. -/
def evolRHS (p : E × E) : E := (localGroupLaw E G).xl p.2 ((localGroupLaw E G).one + p.1)

variable (G) in
/-- The domain of `evolRHS`. -/
def evolDom : Set (E × E) := {p | (localGroupLaw E G).one + p.1 ∈ (localGroupLaw E G).domR}

theorem isOpen_evolDom : IsOpen (evolDom (E := E) G) :=
  (localGroupLaw E G).isOpen_domR.preimage (by fun_prop)

theorem zero_mem_evolDom : (0 : E × E) ∈ evolDom (E := E) G := by
  have h : (localGroupLaw E G).one + (0 : E × E).1 ∈ (localGroupLaw E G).domR := by
    rw [Prod.fst_zero, add_zero]; exact (localGroupLaw E G).one_mem_domR
  exact h

theorem smoothMBOn_evolRHS : SmoothMBOn (evolRHS (E := E) G) (evolDom G) := fun k ↦ by
  set L := localGroupLaw E G
  have hin : ContDiffMBOn k (fun p : E × E ↦ (L.one + p.1, p.2)) (evolDom G) :=
    ((contDiffMBOn_const k L.one _).add isOpen_evolDom
      (((ContinuousLinearMap.fst ℝ E E).contDiffMBOn k univ).mono (subset_univ _))).prodMk
      isOpen_evolDom (((ContinuousLinearMap.snd ℝ E E).contDiffMBOn k univ).mono (subset_univ _))
  exact ContDiffMBOn.comp (g := fun p : E × E ↦ L.xl p.2 p.1)
    (f := fun p : E × E ↦ (L.one + p.1, p.2)) isOpen_evolDom (L.isOpen_domR.prod isOpen_univ)
    (LocalGroupLaw.contDiffMBOn_xl₂ L k) hin fun p hp ↦ ⟨hp, mem_univ _⟩

theorem contDiffOn_evolRHS : ContDiffOn ℝ ∞ (evolRHS (E := E) G) (evolDom G) :=
  (smoothMBOn_iff_contDiffOn isOpen_evolDom).1 smoothMBOn_evolRHS

theorem evolRHS_zero_right {a : E} (ha : (a, (0 : E)) ∈ evolDom G) :
    evolRHS G (a, (0 : E)) = 0 := by
  have h := (localGroupLaw E G).xl_smul (0 : ℝ) (0 : E) ha
  rw [zero_smul, zero_smul] at h
  exact h

theorem evolRHS_zero_left (v : E) : evolRHS G ((0 : E), v) = v := by
  change (localGroupLaw E G).xl v ((localGroupLaw E G).one + 0) = v
  rw [add_zero, LocalGroupLaw.xl_one]

/-- **The derivative of `ψ` at `0`** is `(a, v) ↦ v`. -/
theorem hasFDerivAt_evolRHS :
    HasFDerivAt (evolRHS (E := E) G) (ContinuousLinearMap.snd ℝ E E) 0 := by
  have hd : DifferentiableAt ℝ (evolRHS (E := E) G) 0 :=
    (contDiffOn_evolRHS.contDiffAt (isOpen_evolDom.mem_nhds zero_mem_evolDom)).differentiableAt
      (by simp)
  have hf := hd.hasFDerivAt
  convert hf using 1
  -- the derivative in the directions `(a, 0)` and `(0, v)`
  have hinl : fderiv ℝ (evolRHS (E := E) G) 0 ∘L ContinuousLinearMap.inl ℝ E E = 0 := by
    have hf' : HasFDerivAt (evolRHS (E := E) G) (fderiv ℝ (evolRHS (E := E) G) 0)
        (ContinuousLinearMap.inl ℝ E E 0) := by rw [map_zero]; exact hf
    have h1 := hf'.comp (0 : E) (ContinuousLinearMap.inl ℝ E E).hasFDerivAt
    have hev : (evolRHS (E := E) G ∘ ContinuousLinearMap.inl ℝ E E) =ᶠ[𝓝 0] fun _ ↦ 0 := by
      have hU : (ContinuousLinearMap.inl ℝ E E) ⁻¹' evolDom G ∈ 𝓝 (0 : E) :=
        (isOpen_evolDom.preimage (ContinuousLinearMap.inl ℝ E E).continuous).mem_nhds
          (by rw [Set.mem_preimage, map_zero]; exact zero_mem_evolDom)
      filter_upwards [hU] with a ha
      rw [Set.mem_preimage, ContinuousLinearMap.inl_apply] at ha
      rw [Function.comp_apply, ContinuousLinearMap.inl_apply]
      exact evolRHS_zero_right ha
    exact h1.unique ((hasFDerivAt_const (0 : E) (0 : E)).congr_of_eventuallyEq hev)
  have hinr : fderiv ℝ (evolRHS (E := E) G) 0 ∘L ContinuousLinearMap.inr ℝ E E =
      ContinuousLinearMap.id ℝ E := by
    have hf' : HasFDerivAt (evolRHS (E := E) G) (fderiv ℝ (evolRHS (E := E) G) 0)
        (ContinuousLinearMap.inr ℝ E E 0) := by rw [map_zero]; exact hf
    have h1 := hf'.comp (0 : E) (ContinuousLinearMap.inr ℝ E E).hasFDerivAt
    have heq : (evolRHS (E := E) G ∘ ContinuousLinearMap.inr ℝ E E) = id := by
      funext v
      rw [Function.comp_apply, ContinuousLinearMap.inr_apply, id]
      exact evolRHS_zero_left v
    rw [heq] at h1
    exact h1.unique (hasFDerivAt_id 0)
  refine ContinuousLinearMap.ext fun p ↦ ?_
  obtain ⟨a, v⟩ := p
  have hsplit : ((a, v) : E × E) = ContinuousLinearMap.inl ℝ E E a +
      ContinuousLinearMap.inr ℝ E E v := by simp
  rw [hsplit, map_add, map_add]
  have h1 := congrArg (fun L : E →L[ℝ] E ↦ L a) hinl
  have h2 := congrArg (fun L : E →L[ℝ] E ↦ L v) hinr
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h1 h2
  rw [ContinuousLinearMap.inl_apply] at h1
  rw [ContinuousLinearMap.inr_apply] at h2
  simp only [ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
    ContinuousLinearMap.coe_snd', zero_add]
  rw [h1, h2, zero_apply, zero_add]

/-! ### The integral equation in `C([0, 1], E)²` -/

/-- `(ξ, u) ↦ (u, ξ)`, as a curve in `E × E`. -/
def pairCLM : C(I, E) × C(I, E) →L[ℝ] C(I, E × E) :=
  LinearMap.mkContinuous
    { toFun := fun w ↦ ⟨fun t ↦ (w.2 t, w.1 t), by fun_prop⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl } 1 fun w ↦ by
    rw [one_mul]
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun t ↦ ?_
    change ‖(w.2 t, w.1 t)‖ ≤ ‖w‖
    rw [Prod.norm_def, Prod.norm_def]
    exact max_le ((w.2.norm_coe_le_norm t).trans (le_max_right _ _))
      ((w.1.norm_coe_le_norm t).trans (le_max_left _ _))

@[simp] theorem pairCLM_apply (w : C(I, E) × C(I, E)) (t : I) :
    pairCLM w t = (w.2 t, w.1 t) := rfl

variable (G) in
/-- `Ψ(ξ, u) = ψ ∘ (u, ξ)`. -/
def evolOp (w : C(I, E) × C(I, E)) : C(I, E) := superpose (K := I) (evolRHS G) (pairCLM w)

variable (G) in
/-- The domain of `evolOp`: the pairs with `(u(t), ξ(t))` in the domain of `ψ`. -/
def evolOpDom : Set (C(I, E) × C(I, E)) := pairCLM ⁻¹' mapsInto I (evolDom G)

theorem isOpen_evolOpDom : IsOpen (evolOpDom (E := E) G) :=
  (isOpen_mapsInto isOpen_evolDom).preimage pairCLM.continuous

theorem zero_mem_evolOpDom : (0 : C(I, E) × C(I, E)) ∈ evolOpDom G := fun _ ↦ by
  rw [map_zero]; exact zero_mem_evolDom

theorem evolOp_apply {w : C(I, E) × C(I, E)} (hw : w ∈ evolOpDom G) (t : I) :
    evolOp G w t = evolRHS G (w.2 t, w.1 t) :=
  superpose_apply contDiffOn_evolRHS.continuousOn hw t

theorem contDiffOn_evolOp : ContDiffOn ℝ ∞ (evolOp (E := E) G) (evolOpDom G) :=
  (contDiffOn_superpose isOpen_evolDom contDiffOn_evolRHS).comp
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := C(I, E) × C(I, E)) (F := C(I, E × E))
      pairCLM).contDiffOn
    fun _ hw ↦ hw

/-- `DΨ(0)(h, k) = h`. -/
theorem hasFDerivAt_evolOp :
    HasFDerivAt (evolOp (E := E) G) (ContinuousLinearMap.fst ℝ (C(I, E)) (C(I, E))) 0 := by
  have hψ1 : ContDiffOn ℝ 1 (evolRHS (E := E) G) (evolDom G) := contDiffOn_evolRHS.of_le (by simp)
  have h0 : pairCLM (0 : C(I, E) × C(I, E)) ∈ mapsInto I (evolDom (E := E) G) :=
    zero_mem_evolOpDom
  have hs := (hasFDerivAt_superpose (K := I) isOpen_evolDom hψ1 h0).comp 0
    (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := C(I, E) × C(I, E)) (F := C(I, E × E))
      pairCLM)
  have hD : ContinuousOn (fderiv ℝ (evolRHS (E := E) G)) (evolDom G) :=
    hψ1.continuousOn_fderiv_of_isOpen isOpen_evolDom le_rfl
  refine hs.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun w ↦ ?_
  refine ContinuousMap.ext fun t ↦ ?_
  change pointwiseApply ℝ I (E × E) E (superpose (fderiv ℝ (evolRHS G)) (pairCLM 0))
    (pairCLM w) t = w.1 t
  rw [pointwiseApply_apply, superpose_apply hD h0, map_zero, ContinuousMap.zero_apply,
    hasFDerivAt_evolRHS.fderiv]
  rfl

variable (G) in
/-- `Φ(ξ, u) = (ξ, u − J Ψ(ξ, u))`. -/
def evolMap (w : C(I, E) × C(I, E)) : C(I, E) × C(I, E) :=
  (w.1, w.2 - primitiveCLM (evolOp G w))

theorem contDiffOn_evolMap : ContDiffOn ℝ ∞ (evolMap (E := E) G) (evolOpDom G) :=
  contDiffOn_fst.prodMk (contDiffOn_snd.sub
    ((ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := C(I, E)) (F := C(I, E))
      primitiveCLM).comp_contDiffOn
      contDiffOn_evolOp))

/-- `DΦ(0)(h, k) = (h, k − J h)`. -/
def evolMapDeriv : (C(I, E) × C(I, E)) →L[ℝ] (C(I, E) × C(I, E)) :=
  (ContinuousLinearMap.fst ℝ _ _).prod
    (ContinuousLinearMap.snd ℝ _ _ - primitiveCLM.comp (ContinuousLinearMap.fst ℝ _ _))

/-- Its inverse `(h, m) ↦ (h, m + J h)`. -/
def evolMapDerivInv : (C(I, E) × C(I, E)) →L[ℝ] (C(I, E) × C(I, E)) :=
  (ContinuousLinearMap.fst ℝ _ _).prod
    (ContinuousLinearMap.snd ℝ _ _ + primitiveCLM.comp (ContinuousLinearMap.fst ℝ _ _))

/-- `DΦ(0)` is invertible. -/
def evolMapDerivEquiv : (C(I, E) × C(I, E)) ≃L[ℝ] (C(I, E) × C(I, E)) :=
  ContinuousLinearEquiv.equivOfInverse evolMapDeriv evolMapDerivInv
    (fun w ↦ by simp [evolMapDeriv, evolMapDerivInv])
    (fun w ↦ by simp [evolMapDeriv, evolMapDerivInv])

theorem hasFDerivAt_evolMap :
    HasFDerivAt (evolMap (E := E) G)
      ((evolMapDerivEquiv (E := E)) : (C(I, E) × C(I, E)) →L[ℝ] (C(I, E) × C(I, E))) 0 := by
  have h := hasFDerivAt_fst.prodMk (hasFDerivAt_snd.sub
    ((ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := C(I, E)) (F := C(I, E))
      primitiveCLM).comp 0 (hasFDerivAt_evolOp (G := G))))
  convert h using 1 <;> rfl

theorem evolOp_zero : evolOp (E := E) G 0 = 0 := by
  refine ContinuousMap.ext fun t ↦ ?_
  rw [evolOp_apply zero_mem_evolOpDom]
  change evolRHS G ((0 : E), (0 : E)) = 0
  exact evolRHS_zero_right zero_mem_evolDom

theorem evolMap_zero : evolMap (E := E) G 0 = 0 := by
  simp [evolMap, evolOp_zero]

theorem evolMap_fst (w : C(I, E) × C(I, E)) : (evolMap G w).1 = w.1 := rfl

/-! ### Left translations in the chart -/

omit [MBLieGroup E G] in
/-- Fréchet derivatives are directional derivatives. -/
theorem _root_.HasFDerivAt.dMB_eq' {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {f' : E →L[ℝ] F} {x : E} (h : HasFDerivAt f f' x) (v : E) :
    dMB f (x, v) = f' v := by
  have hl := hasDerivAt_iff_tendsto_slope_zero.1 (h.hasLineDerivAt v)
  refine HasDirDerivAt.dMB_eq ?_
  unfold HasDirDerivAt
  simpa using hl

variable (G) in
/-- The left translation by `g⁻¹` in the chart `φ` at the identity: `b ↦ φ(g⁻¹ φ⁻¹(b))`. -/
def leftRep (g : G) (b : E) : E := chartAt E (1 : G) (g⁻¹ * (chartAt E (1 : G)).symm b)

/-- **The left translation by `g⁻¹` inverts the left invariant fields at `φ(g)`**:
`d(λ_{g⁻¹})(φ g)(x̃_l(v)(φ g)) = v`. -/
theorem exists_hasFDerivAt_leftRep {g : G} (hg : g ∈ (chartAt E (1 : G)).source) :
    ∃ D : E →L[ℝ] E, HasFDerivAt (leftRep G g) D (chartAt E (1 : G) g) ∧
      ∀ v, D ((localGroupLaw E G).xl v (chartAt E (1 : G) g)) = v := by
  set φ := chartAt E (1 : G)
  set L := localGroupLaw E G
  have h1 := mem_chart_source E (1 : G)
  -- `λ` is smooth near `φ g`
  set O := chartDomain (fun x : G ↦ g⁻¹ * x) univ φ φ
  have hO : IsOpen O := isOpen_chartDomain isOpen_univ
    (smoothMBM_mul_left (E := E) g⁻¹ 0).continuousOn φ φ
  have hgO : φ g ∈ O := by
    refine ⟨φ.map_source hg, mem_univ _, ?_⟩
    change g⁻¹ * φ.symm (φ g) ∈ φ.source
    rw [φ.left_inv hg, inv_mul_cancel]; exact h1
  have hLam : ContDiffOn ℝ 1 (leftRep G g) O :=
    ((smoothMBM_mul_left (E := E) g⁻¹ 2).contDiffMBOn_chart isOpen_univ
      (chart_mem_atlas E (1 : G)) (chart_mem_atlas E (1 : G))).contDiffOn hO
  have hLd : HasFDerivAt (leftRep G g) (fderiv ℝ (leftRep G g) (φ g)) (φ g) :=
    ((hLam.contDiffAt (hO.mem_nhds hgO)).differentiableAt one_ne_zero).hasFDerivAt
  -- the left multiplication by `φ g` in the chart
  have hgdom : L.one ∈ L.domL (φ g) := chart_mem_dom hg h1 (by rw [mul_one]; exact hg)
  have hm : ContDiffOn ℝ 1 (fun b ↦ L.mul (φ g, b)) (L.domL (φ g)) :=
    (L.contDiffMBOn_mul_left 2 (φ g)).contDiffOn (L.isOpen_domL _)
  have hmd : HasFDerivAt (fun b ↦ L.mul (φ g, b)) (fderiv ℝ (fun b ↦ L.mul (φ g, b)) L.one)
      L.one :=
    ((hm.contDiffAt ((L.isOpen_domL _).mem_nhds hgdom)).differentiableAt one_ne_zero).hasFDerivAt
  have hm1 : L.mul (φ g, L.one) = φ g := L.mul_one _ hgdom
  refine ⟨fderiv ℝ (leftRep G g) (φ g), hLd, fun v ↦ ?_⟩
  -- `λ ∘ m = id` near `φ(1)`
  have hev : (leftRep G g ∘ fun b ↦ L.mul (φ g, b)) =ᶠ[𝓝 L.one] id := by
    have hT : φ.target ∈ 𝓝 L.one := φ.open_target.mem_nhds (φ.map_source h1)
    filter_upwards [(L.isOpen_domL (φ g)).mem_nhds hgdom, hT] with b hb hbt
    have hsrc : φ.symm (φ g) * φ.symm b ∈ φ.source := hb.2
    rw [φ.left_inv hg] at hsrc
    change φ (g⁻¹ * φ.symm (φ (φ.symm (φ g) * φ.symm b))) = b
    rw [φ.left_inv hg, φ.left_inv hsrc, ← mul_assoc, inv_mul_cancel, one_mul, φ.right_inv hbt]
  have hcomp := (hm1 ▸ hLd).comp L.one hmd
  have hid := hcomp.congr_of_eventuallyEq hev.symm
  have hD := hid.unique (hasFDerivAt_id L.one)
  have := congrArg (fun A : E →L[ℝ] E ↦ A v) hD
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
  rw [LocalGroupLaw.xl_eq, hmd.dMB_eq']
  rw [hm1] at this
  exact this

/-! ### From the integral equation to evolutions -/

theorem domR_subset_target :
    (localGroupLaw E G).domR ⊆ (chartAt E (1 : G)).target := fun _ ha ↦ ha.1.1

/-- **A solution of `u = J Ψ(ξ, u)` gives the evolution `γ = φ⁻¹(z₀ + u)` of `ξ` on `[0, 1]`.** -/
theorem isEvolOn_of_eq_primitive [CompleteSpace E] {ξ u : C(I, E)} (hD : (ξ, u) ∈ evolOpDom G)
    (hu : u = primitiveCLM (evolOp G (ξ, u))) :
    IsEvolOn E (extendCurve ξ) fun s ↦
      (chartAt E (1 : G)).symm ((localGroupLaw E G).one + extendCurve u s) := by
  set φ := chartAt E (1 : G)
  set L := localGroupLaw E G
  set c : ℝ → E := fun s ↦ L.one + extendCurve u s
  set η := evolOp G (ξ, u)
  have hcdom : ∀ s, c s ∈ L.domR := fun s ↦ hD (projIcc 0 1 zero_le_one s)
  have hct : ∀ s, c s ∈ φ.target := fun s ↦ domR_subset_target (hcdom s)
  have hη : ∀ s, extendCurve η s = L.xl (extendCurve ξ s) (c s) := fun s ↦
    evolOp_apply hD (projIcc 0 1 zero_le_one s)
  have hcr : ∀ r ∈ Icc (0 : ℝ) 1, c r = L.one + ∫ s in (0 : ℝ)..r, extendCurve η s := by
    intro r hr
    change L.one + extendCurve u r = _
    rw [extendCurve_apply, projIcc_of_mem _ hr, hu]
    rfl
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt c (L.xl (extendCurve ξ t) (c t)) (Icc 0 1) t := by
    intro t ht
    rw [← hη]
    exact (((continuous_extendCurve η).integral_hasStrictDerivAt 0 t).hasDerivAt.const_add
      L.one).hasDerivWithinAt.congr (fun r hr ↦ hcr r hr) (hcr t ht)
  have hcont : Continuous fun s ↦ φ.symm (c s) :=
    φ.continuousOn_symm.comp_continuous (continuous_const.add (continuous_extendCurve u)) hct
  refine ⟨?_, fun t ht ↦ ⟨hcont.continuousWithinAt, ?_⟩⟩
  · change φ.symm (L.one + extendCurve u 0) = 1
    have h0 : extendCurve u 0 = 0 := by
      have := hcr 0 ⟨le_rfl, zero_le_one⟩
      rwa [intervalIntegral.integral_same, add_zero, add_eq_left] at this
    rw [h0, add_zero]
    exact φ.left_inv (mem_chart_source E (1 : G))
  · set g := φ.symm (c t)
    have hg : g ∈ φ.source := φ.map_target (hct t)
    have hφg : φ g = c t := φ.right_inv (hct t)
    obtain ⟨D, hD', hDv⟩ := exists_hasFDerivAt_leftRep hg
    rw [hφg] at hD' hDv
    have hcomp := hD'.comp_hasDerivWithinAt t (hderiv t ht)
    rw [hDv] at hcomp
    exact hasDerivWithinAt_iff_tendsto_slope.1 hcomp

/-! ### The inverse function theorem -/

variable [CompleteSpace E]

omit [CompleteSpace E] in
theorem contDiffAt_evolMap : ContDiffAt ℝ ∞ (evolMap (E := E) G) 0 :=
  contDiffOn_evolMap.contDiffAt (isOpen_evolOpDom.mem_nhds zero_mem_evolOpDom)

omit [CompleteSpace E] in
theorem contDiffAt_evolMap_one : ContDiffAt ℝ 1 (evolMap (E := E) G) 0 :=
  contDiffAt_evolMap.of_le (by exact_mod_cast le_top)

variable (G) in
/-- **`Φ` is a local diffeomorphism at `0`** (inverse function theorem). -/
def evolHomeo : OpenPartialHomeomorph (C(I, E) × C(I, E)) (C(I, E) × C(I, E)) :=
  (contDiffAt_evolMap_one (G := G)).toOpenPartialHomeomorph (evolMap G) hasFDerivAt_evolMap
    one_ne_zero

theorem coe_evolHomeo : ⇑(evolHomeo (E := E) G) = evolMap G := rfl

theorem zero_mem_evolHomeo_source : (0 : C(I, E) × C(I, E)) ∈ (evolHomeo G).source :=
  ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _

theorem zero_mem_evolHomeo_target : (0 : C(I, E) × C(I, E)) ∈ (evolHomeo G).target := by
  have h := (evolHomeo (E := E) G).map_source zero_mem_evolHomeo_source
  rwa [coe_evolHomeo, evolMap_zero] at h

theorem evolHomeo_symm_zero : (evolHomeo (E := E) G).symm 0 = 0 := by
  have h := (evolHomeo (E := E) G).left_inv zero_mem_evolHomeo_source
  rwa [coe_evolHomeo, evolMap_zero] at h

/-- **The local inverse is smooth at `0`.** -/
theorem contDiffAt_evolHomeo_symm (k : ℕ) :
    ContDiffAt ℝ k (evolHomeo (E := E) G).symm 0 := by
  refine (evolHomeo G).contDiffAt_symm zero_mem_evolHomeo_target ?_ ?_ (f₀' := evolMapDerivEquiv)
  · rw [evolHomeo_symm_zero, coe_evolHomeo]; exact hasFDerivAt_evolMap
  · rw [evolHomeo_symm_zero, coe_evolHomeo]
    exact contDiffAt_evolMap.of_le (by exact_mod_cast le_top)

/-- **Local solutions**: for `ξ` near `0`, `w = Φ⁻¹(ξ, 0)` is defined, lies in the domain of `Ψ`,
and solves `w = (ξ, J Ψ(w))`. -/
theorem exists_evolSol : ∃ r > 0, ∀ ξ : C(I, E), ‖ξ‖ < r →
    ((ξ, 0) : C(I, E) × C(I, E)) ∈ (evolHomeo G).target ∧
      (evolHomeo G).symm (ξ, 0) ∈ evolOpDom G ∩ (evolHomeo G).source := by
  set h := evolHomeo (E := E) G
  have hS : IsOpen (h.target ∩ h.symm ⁻¹' (evolOpDom G ∩ h.source)) :=
    h.isOpen_inter_preimage_symm (isOpen_evolOpDom.inter h.open_source)
  have h0 : (0 : C(I, E) × C(I, E)) ∈ h.target ∩ h.symm ⁻¹' (evolOpDom G ∩ h.source) :=
    ⟨zero_mem_evolHomeo_target, by
      rw [mem_preimage, evolHomeo_symm_zero]; exact ⟨zero_mem_evolOpDom, zero_mem_evolHomeo_source⟩⟩
  have hO : IsOpen ((ContinuousLinearMap.inl ℝ (C(I, E)) (C(I, E))) ⁻¹'
      (h.target ∩ h.symm ⁻¹' (evolOpDom G ∩ h.source))) :=
    hS.preimage (ContinuousLinearMap.inl ℝ (C(I, E)) (C(I, E))).continuous
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO 0 (by rw [mem_preimage, map_zero]; exact h0)
  exact ⟨r, hr, fun ξ hξ ↦ hball (mem_ball_zero_iff.2 hξ)⟩

/-! ### Smoothness through the chart at the identity -/

omit [CompleteSpace E] in
/-- A map into `G` with values in the chart `φ` at the identity is `C^k` if it is `C^k` in `φ`. -/
theorem contMDiffMBOn_of_chartOne {k : ℕ} {f : C(I, E) → G} {V : Set C(I, E)} (hV : IsOpen V)
    (hsrc : ∀ x ∈ V, f x ∈ (chartAt E (1 : G)).source)
    (hrep : ContDiffMBOn k (chartAt E (1 : G) ∘ f) V) :
    ContMDiffMBOn (E := C(I, E)) (F := E) k f V := by
  set φ := chartAt E (1 : G)
  have hc : ContinuousOn f V :=
    (φ.continuousOn_symm.comp hrep.continuousOn fun x hx ↦ φ.map_source (hsrc x hx)).congr
      fun x hx ↦ (φ.left_inv (hsrc x hx)).symm
  refine ⟨hc, fun x hx ↦ ?_⟩
  set e' := chartAt E (f x)
  have hT := smoothMBOn_transition (chart_mem_atlas E (1 : G)) (chart_mem_atlas E (f x)) k
  have hD := isOpen_chartDomain hV hc (chartAt C(I, E) x) e'
  have hS : IsOpen (φ.target ∩ φ.symm ⁻¹' e'.source) :=
    φ.isOpen_inter_preimage_symm e'.open_source
  rw [chartAt_self_eq] at hD ⊢
  have hDV : chartDomain f V (OpenPartialHomeomorph.refl C(I, E)) e' ⊆ V := fun y hy ↦ hy.2.1
  have hcomp := ContDiffMBOn.comp hD hS hT (hrep.mono hDV) fun y hy ↦ by
    refine ⟨φ.map_source (hsrc y (hDV hy)), ?_⟩
    change φ.symm (φ (f y)) ∈ e'.source
    rw [φ.left_inv (hsrc y (hDV hy))]
    exact hy.2.2
  refine ContDiffMBOn.congr_of_isOpen hD (fun y hy ↦ ?_) hcomp
  change e' (φ.symm (φ (f y))) = e' (f y)
  rw [φ.left_inv (hsrc y (hDV hy))]

/-! ### Banach–Lie groups are `C⁰`-regular -/

/-- **Banach–Lie groups are `C⁰`-regular** ([GN26, Theorem 6.3.4]). -/
theorem isC0Regular_of_completeSpace : IsC0Regular E G := by
  set φ := chartAt E (1 : G)
  set L := localGroupLaw E G
  set h := evolHomeo (E := E) G
  obtain ⟨r, hr, hsol⟩ := exists_evolSol (E := E) (G := G)
  -- the solution for `‖ξ‖ < r`
  have hfix : ∀ ξ : C(I, E), ‖ξ‖ < r → (h.symm (ξ, 0)).1 = ξ ∧
      (h.symm (ξ, 0)).2 = primitiveCLM (evolOp G (ξ, (h.symm (ξ, 0)).2)) ∧
      (ξ, (h.symm (ξ, 0)).2) ∈ evolOpDom G := by
    intro ξ hξ
    obtain ⟨ht, hD, -⟩ := hsol ξ hξ
    have hrt := h.right_inv ht
    rw [coe_evolHomeo] at hrt
    have h1 : (h.symm (ξ, 0)).1 = ξ := by
      have := congrArg Prod.fst hrt; rwa [evolMap_fst] at this
    have hw : h.symm (ξ, 0) = (ξ, (h.symm (ξ, 0)).2) := Prod.ext h1 rfl
    refine ⟨h1, ?_, hw ▸ hD⟩
    have h2 := congrArg Prod.snd hrt
    change (h.symm (ξ, 0)).2 - primitiveCLM (evolOp G (h.symm (ξ, 0))) = 0 at h2
    rw [sub_eq_zero, hw] at h2
    exact h2
  have hon : ∀ ξ : C(I, E), ‖ξ‖ < r → IsEvolOn E (extendCurve ξ) fun s ↦
      φ.symm (L.one + extendCurve (h.symm (ξ, 0)).2 s) := fun ξ hξ ↦
    isEvolOn_of_eq_primitive (hfix ξ hξ).2.2 (hfix ξ hξ).2.1
  -- one-parameter groups
  have hP : ∀ x : E, ∃ P : ℝ → G, IsEvol E (fun _ ↦ x) P := by
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt (‖x‖ / r)
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    set y := ((n : ℝ) + 1)⁻¹ • x
    have hy : ‖ContinuousMap.const I y‖ < r := by
      refine lt_of_le_of_lt ((ContinuousMap.norm_le _ (norm_nonneg y)).2 fun _ ↦ le_rfl) ?_
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hn1.le, inv_mul_lt_iff₀ hn1]
      rw [div_lt_iff₀ hr] at hn
      nlinarith
    have hγ := hon _ hy
    rw [extendCurve_const] at hγ
    have hc := (hγ.oneParam).comp_mul ((n : ℝ) + 1)
    rw [smul_inv_smul₀ hn1.ne'] at hc
    exact ⟨_, hc⟩
  have hnorm : ∀ {ρ : ℝ}, 0 < ρ → ∀ ξ ∈ valIn (ball (0 : E) ρ), ‖ξ‖ < ρ := fun hρ ξ hξ ↦
    (ContinuousMap.norm_lt_iff _ hρ).2 fun t ↦ mem_ball_zero_iff.1 (hξ t)
  have hsemi : IsC0Semiregular E G := isC0Semiregular_of_local (ball_mem_nhds 0 hr)
    fun ξ hξ ↦ by
      obtain ⟨Γ, hΓ, -⟩ := (hon ξ (hnorm hr ξ hξ)).exists_isEvol hP
      exact ⟨Γ, hΓ⟩
  refine isC0Regular_of_local' hsemi fun k ↦ ?_
  -- `C^k` near `0`
  have hk := (contDiffAt_evolHomeo_symm (E := E) (G := G) k).eventually (by simp)
  obtain ⟨ρ, hρ, hρball⟩ := Metric.eventually_nhds_iff_ball.1 hk
  set ρ' := min r ρ
  have hρ' : 0 < ρ' := lt_min hr hρ
  set one : I := ⟨1, ⟨zero_le_one, le_rfl⟩⟩
  set F : C(I, E) → E := fun ξ ↦ L.one + (h.symm (ξ, 0)).2 one
  have hF : ContDiffOn ℝ k F (ball 0 ρ') := by
    intro ξ hξ
    have hξ' : ‖ξ‖ < ρ := (mem_ball_zero_iff.1 hξ).trans_le (min_le_right _ _)
    have hs := hρball ((ContinuousLinearMap.inl ℝ (C(I, E)) (C(I, E))) ξ) (by
      rw [mem_ball_zero_iff, ContinuousLinearMap.inl_apply, Prod.norm_def, norm_zero,
        max_eq_left (norm_nonneg _)]; exact hξ')
    have hev : ContDiff ℝ k ((ContinuousMap.evalCLM (R := ℝ) (M := E) one).comp
        (ContinuousLinearMap.snd ℝ (C(I, E)) (C(I, E)))) :=
      ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := C(I, E) × C(I, E)) (F := E) _
    have hinl : ContDiff ℝ k (ContinuousLinearMap.inl ℝ (C(I, E)) (C(I, E))) :=
      ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := C(I, E)) (F := C(I, E) × C(I, E)) _
    exact (contDiffAt_const.add
      ((hev.contDiffAt.comp _ hs).comp ξ hinl.contDiffAt)).contDiffWithinAt
  set W : Set E := ball 0 ρ'
  have hVsub : valIn W ⊆ ball 0 ρ' := fun ξ hξ ↦ mem_ball_zero_iff.2 (hnorm hρ' ξ hξ)
  have hVr : ∀ ξ ∈ valIn W, ‖ξ‖ < r := fun ξ hξ ↦
    (hnorm hρ' ξ hξ).trans_le (min_le_left _ _)
  have hev : ∀ ξ (hξ : ξ ∈ valIn W), evol E G ξ =
      φ.symm (L.one + extendCurve (h.symm (ξ, 0)).2 1) := fun ξ hξ ↦
    evol_eq_of_isEvolOn hP (hon ξ (hVr ξ hξ))
  have hct : ∀ ξ ∈ valIn W, L.one + extendCurve (h.symm (ξ, 0)).2 1 ∈ φ.target :=
    fun ξ hξ ↦ domR_subset_target ((hfix ξ (hVr ξ hξ)).2.2 (projIcc 0 1 zero_le_one 1))
  refine ⟨W, isOpen_ball, mem_ball_self hρ', contMDiffMBOn_of_chartOne (isOpen_valIn isOpen_ball)
    (fun ξ hξ ↦ by rw [hev ξ hξ]; exact φ.map_target (hct ξ hξ)) ?_⟩
  refine ContDiffMBOn.congr_of_isOpen (isOpen_valIn isOpen_ball) (fun ξ hξ ↦ ?_)
    ((ContDiffOn.contDiffMBOn isOpen_ball hF).mono hVsub)
  change F ξ = φ (evol E G ξ)
  rw [hev ξ hξ, φ.right_inv (hct ξ hξ), extendCurve_apply, projIcc_of_mem _ ⟨zero_le_one, le_rfl⟩]

end LocallyConvex.LieGroups.MBLieGroup
