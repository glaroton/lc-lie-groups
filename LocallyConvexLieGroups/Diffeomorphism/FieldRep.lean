/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Diffeomorphism.LieAlgebra
public import LocallyConvexAnalysis.Calculus.MBFrechetFinite
public import LocallyConvexAnalysis.Calculus.Operations

/-!
# Local representatives of the vector fields in `L(Diff(K))`

For a compact manifold `K` modeled on a finite-dimensional normed space `H`, with a local addition
`A`, an element `u` of the model space `Γ_id` of `Diff(K)` is a vector field on `K` written in the
preferred charts. Its local representative `ũ_i(z)` in a chart `i` of `K` depends smoothly on
`(u, z)` (`Diffeo.smoothMBOn_rep`): `u ↦ ũ_i` is continuous linear into `C^ℓ(i(dom i), H)` for
every `ℓ`, and uncurrying ([GN26, Theorem 1.7.30(a)]) gives a `C^{k,ℓ}` map, hence a `C^k` map
for `k = ℓ`. The representatives transform under the derivatives of the transition maps
(`Diffeo.rep_transition`).

Near `u = 0` the representatives are uniformly small with small derivatives on compact sets
(`exists_isOpen_bound`), and then Lipschitz with a small constant on convex sets
(`norm_sub_le_of_dMB_le`).

## Main definitions

* `Diffeo.rep A i u z`: the local representative of `u ∈ Γ_id` in the chart `i` of `K`.

## Main results

* `Diffeo.smoothMBOn_rep`: `(u, z) ↦ ũ_i(z)` is smooth.
* `Diffeo.rep_transition`: `ũ_j(τ z) = dτ(z) ũ_i(z)` for `τ = j ∘ i⁻¹`.
* `exists_isOpen_bound`: smallness near `0`, uniformly on a compact set.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function Metric
open scoped Topology
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups

/-! ### Smallness near `0` -/

section Small

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] [T2Space W]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

omit [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] [T2Space W] in
/-- **Smallness near `0`, uniformly on a compact set**: if `f` is `C¹` on `W × O` and vanishes on
`{0} × O`, then near `w = 0`, `‖f(w, z)‖ < ε` and `‖∂_z f(w, z)‖ ≤ ε` for all `z` in a compact set
`C ⊆ O`. -/
theorem exists_isOpen_bound {f : W × H → H} {O : Set H} (hO : IsOpen O)
    (hf : ContDiffMBOn 1 f (univ ×ˢ O)) (h0 : ∀ z ∈ O, f (0, z) = 0) {C : Set H}
    (hC : IsCompact C) (hCO : C ⊆ O) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : Set W, IsOpen N ∧ (0 : W) ∈ N ∧ ∀ w ∈ N, ∀ z ∈ C,
      ‖f (w, z)‖ < ε ∧ ∀ h, ‖dMB f ((w, z), (0, h))‖ ≤ ε * ‖h‖ := by
  have hU : IsOpen (univ ×ˢ O : Set (W × H)) := isOpen_univ.prod hO
  have hcd : ContinuousOn (dMB f) ((univ ×ˢ O) ×ˢ univ) := hf.2.2
  -- `∂_z f(0, z) = 0`
  have hd0 : ∀ z ∈ O, ∀ h, dMB f (((0 : W), z), (0, h)) = 0 := by
    intro z hz h
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] 0,
        t⁻¹ • (f (((0 : W), z) + t • ((0 : W), h)) - f ((0 : W), z)) = 0 := by
      have : ∀ᶠ t : ℝ in 𝓝 0, z + t • h ∈ O := by
        have hc : Continuous fun t : ℝ ↦ z + t • h := by fun_prop
        exact hc.continuousAt.preimage_mem_nhds (by simpa using hO.mem_nhds hz)
      filter_upwards [nhdsWithin_le_nhds this] with t ht
      simp [h0 _ ht, h0 z hz]
    exact tendsto_nhds_unique (hf.2.1 _ ⟨mem_univ _, hz⟩ _) (tendsto_const_nhds.congr' (hev.mono
      fun t ht ↦ ht.symm))
  have hP : ∀ y ∈ C ×ˢ closedBall (0 : H) 1, ∀ᶠ q : W × (H × H) in 𝓝 ((0 : W), y),
      ‖f (q.1, q.2.1)‖ < ε ∧ ‖dMB f ((q.1, q.2.1), (0, q.2.2))‖ < ε := by
    rintro ⟨z, h⟩ ⟨hz, -⟩
    have hzO := hCO hz
    have hmem : ∀ᶠ q : W × (H × H) in 𝓝 ((0 : W), (z, h)), (q.1, q.2.1) ∈ univ ×ˢ O := by
      have hc : Continuous fun q : W × (H × H) ↦ (q.1, q.2.1) := by fun_prop
      exact hc.continuousAt.preimage_mem_nhds (hU.mem_nhds ⟨mem_univ _, hzO⟩)
    have h1 : ContinuousAt (fun q : W × (H × H) ↦ ‖f (q.1, q.2.1)‖) ((0 : W), (z, h)) := by
      have hc : ContinuousAt f ((0 : W), z) :=
        (hf.continuousOn).continuousAt (hU.mem_nhds ⟨mem_univ _, hzO⟩)
      exact continuous_norm.continuousAt.comp
        (ContinuousAt.comp (g := f) (f := fun q : W × (H × H) ↦ (q.1, q.2.1)) hc (by fun_prop))
    have h2 : ContinuousAt (fun q : W × (H × H) ↦ ‖dMB f ((q.1, q.2.1), (0, q.2.2))‖)
        ((0 : W), (z, h)) := by
      have hc : ContinuousAt (dMB f) (((0 : W), z), ((0 : W), h)) :=
        hcd.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨⟨mem_univ _, hzO⟩, mem_univ _⟩)
      exact continuous_norm.continuousAt.comp
        (ContinuousAt.comp (g := dMB f)
          (f := fun q : W × (H × H) ↦ ((q.1, q.2.1), ((0 : W), q.2.2))) hc (by fun_prop))
    have hv1 : ‖f ((0 : W), z)‖ < ε := by rw [h0 z hzO, norm_zero]; exact hε
    have hv2 : ‖dMB f (((0 : W), z), ((0 : W), h))‖ < ε := by rw [hd0 z hzO, norm_zero]; exact hε
    exact (h1.eventually (gt_mem_nhds hv1)).and (h2.eventually (gt_mem_nhds hv2))
  have hK : IsCompact (C ×ˢ closedBall (0 : H) 1) := hC.prod (isCompact_closedBall 0 1)
  have hev := hK.eventually_forall_of_forall_eventually (x₀ := (0 : W))
    (P := fun w y ↦ ‖f (w, y.1)‖ < ε ∧ ‖dMB f ((w, y.1), (0, y.2))‖ < ε) hP
  obtain ⟨N, hN, hNo, hN0⟩ := eventually_nhds_iff.1 hev
  refine ⟨N, hNo, hN0, fun w hw z hz ↦ ⟨(hN w hw (z, 0) ⟨hz, by simp⟩).1, fun h ↦ ?_⟩⟩
  have hzO := hCO hz
  have hlin : ∀ c : ℝ, dMB f ((w, z), (0, c • h)) = c • dMB f ((w, z), (0, h)) := fun c ↦ by
    have := hf.dMB_smul (x := (w, z)) ⟨mem_univ _, hzO⟩ c ((0 : W), h)
    simpa using this
  rcases eq_or_ne h 0 with rfl | hh
  · have := hlin 0
    simp only [zero_smul] at this
    rw [this]; simp
  · have hpos : 0 < ‖h‖ := norm_pos_iff.2 hh
    have hb := (hN w hw (z, ‖h‖⁻¹ • h) ⟨hz, by
      rw [mem_closedBall, dist_zero_right, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hpos.ne']⟩).2
    rw [hlin, norm_smul, norm_inv, norm_norm] at hb
    have := (inv_mul_lt_iff₀ hpos).1 hb
    linarith

/-- **Lipschitz bounds from bounds on the derivative**, on convex sets of a finite-dimensional
space. -/
theorem norm_sub_le_of_dMB_le {g : H → H} {U : Set H} (hU : IsOpen U) (hg : ContDiffMBOn 1 g U)
    {s : Set H} (hs : Convex ℝ s) (hsU : s ⊆ U) {c : ℝ} (hc0 : 0 ≤ c)
    (hb : ∀ z ∈ s, ∀ h, ‖dMB g (z, h)‖ ≤ c * ‖h‖) {z z' : H} (hz : z ∈ s) (hz' : z' ∈ s) :
    ‖g z - g z'‖ ≤ c * ‖z - z'‖ := by
  have hc : ContDiffOn ℝ 1 g U := (contDiffMBOn_iff_contDiffOn hU).1 hg
  have hD : ∀ y ∈ s, HasFDerivWithinAt g (fderiv ℝ g y) s y := fun y hy ↦
    (((hc.contDiffAt (hU.mem_nhds (hsU hy))).differentiableAt one_ne_zero).hasFDerivAt
      ).hasFDerivWithinAt
  have hB : ∀ y ∈ s, ‖fderiv ℝ g y‖ ≤ c := fun y hy ↦
    ContinuousLinearMap.opNorm_le_bound _ hc0 fun h ↦ by
      rw [← dMB_eq_fderiv hU hc (hsU hy)]; exact hb y hy h
  exact hs.norm_image_sub_le_of_norm_hasFDerivWithin_le hD hB hz' hz

end Small

/-! ### Local representatives -/

namespace Diffeo

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
  {K : Type} [TopologicalSpace K] [ChartedSpace H K] [MBManifold H K] [CompactSpace K] [T2Space K]
  (A : LocalAddition H K)

/-- **The local representative** `ũ_i` of `u ∈ Γ_id` in the chart `i` of `K`: the vector `u(q)`
in the fiber coordinates of `i`, at `q = i⁻¹ z`. -/
def rep (i : atlas H K) (u : DiffeoModel A) (z : H) : H :=
  localCoord (H := H) (E := H) (fid (H := H)) i i (fun q ↦ evalAt A q u) z

omit [CompactSpace K] [T2Space K] in
theorem mem_chartDomOpens_fid (i : atlas H K) {z : H} (hz : z ∈ i.1.target) :
    z ∈ chartDomOpens (H := H) (E := H) (fid (H := H) (K := K)) i i :=
  mem_chartDomOpens.2 ⟨hz, i.1.map_target hz⟩

omit [CompactSpace K] [T2Space K] in
theorem chartDomOpens_fid (i : atlas H K) :
    (chartDomOpens (H := H) (E := H) (fid (H := H) (K := K)) i i : Set H) = i.1.target :=
  Subset.antisymm (fun _ hz ↦ (mem_chartDomOpens.1 hz).1) fun _ hz ↦ mem_chartDomOpens_fid i hz

theorem rep_apply (i : atlas H K) (u : DiffeoModel A) (z : H) :
    rep A i u z = coordAt i ⟨i.1.symm z, evalAt A (i.1.symm z) u⟩ :=
  rfl

theorem rep_add_smul (i : atlas H K) (u w : DiffeoModel A) (a b : ℝ) {z : H}
    (hz : z ∈ i.1.target) : rep A i (a • u + b • w) z = a • rep A i u z + b • rep A i w z := by
  have h := localCoord_linearCombination (H := H) (E := H) (fid (H := H) (K := K)) i i
    (fun q ↦ evalAt A q u) (fun q ↦ evalAt A q w) a b (mem_chartDomOpens_fid i hz)
  simp only [rep]
  rw [← h]
  congr 1

theorem rep_zero (i : atlas H K) {z : H} (hz : z ∈ i.1.target) : rep A i 0 z = 0 := by
  have h := rep_add_smul A i 0 0 0 0 hz
  simpa using h

/-- **The representatives transform under the transition maps**:
`ũ_j(j(i⁻¹ z)) = d(j ∘ i⁻¹)(z) ũ_i(z)`. -/
theorem rep_transition (i j : atlas H K) (u : DiffeoModel A) {z : H} (hz : z ∈ i.1.target)
    (hzj : i.1.symm z ∈ j.1.source) :
    rep A j u (j.1 (i.1.symm z)) = dMB (j.1 ∘ i.1.symm) (z, rep A i u z) := by
  set q := i.1.symm z
  have hq : q ∈ i.1.source := i.1.map_target hz
  rw [rep_apply, rep_apply, j.1.left_inv hzj]
  set c : atlas H K := ⟨chartAt H q, chart_mem_atlas H q⟩
  have h := tangentCoordChange_comp c i j (x := q) ⟨⟨mem_chart_source H q, hq⟩, hzj⟩
    (evalAt A q u)
  change tangentCoordChange c j q (evalAt A q u) =
    dMB (j.1 ∘ i.1.symm) (z, tangentCoordChange c i q (evalAt A q u))
  rw [← h, tangentCoordChange, i.1.right_inv hz]

variable [FiniteDimensional ℝ H]

/-- **The representatives depend smoothly on `(u, z)`**: `u ↦ ũ_i` is continuous linear into
`C^ℓ(i(dom i), H)`, and uncurrying gives a `C^{ℓ,ℓ}` map, hence a `C^ℓ` map. -/
theorem smoothMBOn_rep (i : atlas H K) :
    SmoothMBOn (fun q : DiffeoModel A × H ↦ rep A i q.1 q.2) (univ ×ˢ i.1.target) := fun ℓ ↦ by
  set V := chartDomOpens (H := H) (E := H) (fid (H := H) (K := K)) i i
  set Ψ : DiffeoModel A →L[ℝ] ContDiffMBMap H ℓ V :=
    (SecCk.coordCLM (H := H) (E := H) (ℓ := ℓ) (f := fid (H := H) (K := K)) (i, i)).comp
      (SecSm.toCkCLM ℓ)
  have h2 := contDiffMBOn₂_of_curry (k := ℓ) isOpen_univ (V := V) (Ψ := Ψ) (Ψ.contDiffMBOn ℓ univ)
  have h := h2.contDiffMBOn_prod isOpen_univ V.isOpen
  rw [show (V : Set H) = i.1.target from chartDomOpens_fid i] at h
  refine h.congr_of_isOpen (isOpen_univ.prod i.1.open_target) (fun q hq ↦ ?_)
  change SecCk.coordFun (i, i) (SecSm.toCkCLM ℓ q.1) q.2 = _
  rw [SecCk.coordFun_apply _ _ (mem_chartDomOpens_fid i hq.2)]
  rfl

end Diffeo

end LocallyConvex.LieGroups
