/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Diffeomorphism.FieldRep
public import LocallyConvexLieGroups.Diffeomorphism.ParamODE
public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Integral curves of time dependent vector fields on a compact manifold

Let `K` be a compact manifold modeled on a finite-dimensional normed space, with a local addition
`A`, and `ξ ∈ C([0, 1], Γ_id)` a continuous curve of vector fields. An **integral curve of `-ξ`**
is a curve `c` with `ċ(t) = -ξ(t)(c(t))` on `[0, 1]`, read in every chart
(`Diffeo.IsIntCurve`). In a chart, the solutions of `ParamODE` are integral curves
(`Diffeo.isIntCurve_sol`), and integral curves with the same initial value agree
(`Diffeo.IsIntCurve.eqOn`): in a chart around a common point the local representatives of `-ξ(t)`
are Lipschitz uniformly in `t`, so the uniqueness theorem for ODEs (Gronwall) applies, and a
connectedness argument on `[0, 1]` concludes.

## Main definitions

* `Diffeo.vf A i`: the local representative `(u, z) ↦ -ũ_i(z)` of `-u` in the chart `i`.
* `Diffeo.IsIntCurve A ξ c`: `c` is an integral curve of `-ξ` on `[0, 1]`.

## Main results

* `Diffeo.hasDerivWithinAt_transfer`: the equation in one chart gives it in any other.
* `Diffeo.isIntCurve_sol`: solutions in a chart are integral curves.
* `Diffeo.IsIntCurve.eqOn`: **uniqueness of integral curves.**
-/

@[expose] public section

open Set Filter Function Metric
open scoped Topology NNReal unitInterval
open LocallyConvex.Analysis LocallyConvex.Manifolds
open LocallyConvex.LieGroups.MBLieGroup (extendCurve valIn)

noncomputable section

namespace LocallyConvex.LieGroups

/-! ### Homogeneous bounds -/

theorem norm_le_mul_of_closedBall {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {L : H → H} (hL : ∀ (c : ℝ) h, L (c • h) = c • L h) {M : ℝ}
    (hM : ∀ h ∈ closedBall (0 : H) 1, ‖L h‖ ≤ M) (h : H) : ‖L h‖ ≤ M * ‖h‖ := by
  rcases eq_or_ne h 0 with rfl | hh
  · have := hL 0 0
    rw [zero_smul, zero_smul] at this
    rw [this]; simp
  · have hpos : 0 < ‖h‖ := norm_pos_iff.2 hh
    have hb := hM (‖h‖⁻¹ • h) (by
      rw [mem_closedBall, dist_zero_right, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hpos.ne'])
    rw [hL, norm_smul, norm_inv, norm_norm] at hb
    have := (inv_mul_le_iff₀ hpos).1 hb
    linarith

theorem dMB_slice_right {W H : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] (f : W × H → H) (w : W) (z h : H) :
    dMB (fun z' ↦ f (w, z')) (z, h) = dMB f ((w, z), (0, h)) := by
  simp only [dMB, Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero]

namespace Diffeo

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {K : Type} [TopologicalSpace K] [ChartedSpace H K] [MBManifold H K] [CompactSpace K] [T2Space K]
  (A : LocalAddition H K)

/-- The local representative `(u, z) ↦ -ũ_i(z)` of `-u` in the chart `i`. -/
def vf (i : atlas H K) (q : DiffeoModel A × H) : H := -rep A i q.1 q.2

theorem smoothMBOn_vf (i : atlas H K) : SmoothMBOn (vf A i) (univ ×ˢ i.1.target) := fun k ↦ by
  have hU : IsOpen (univ ×ˢ i.1.target : Set (DiffeoModel A × H)) :=
    isOpen_univ.prod i.1.open_target
  refine ContDiffMBOn.congr_of_isOpen hU (fun q _ ↦ ?_)
    (ContDiffMBOn.comp hU isOpen_univ ((-ContinuousLinearMap.id ℝ H).contDiffMBOn k univ)
      (smoothMBOn_rep A i k) (mapsTo_univ _ _))
  simp [vf]

omit [FiniteDimensional ℝ H] in
/-- In a chart `j`, `z ↦ f(w, z)` is `C^k` for a map `f` which is `C^k` on `Γ × j(dom j)`. -/
theorem contDiffMBOn_slice {k : ℕ} {f : DiffeoModel A × H → H} {U : Set H} (hU : IsOpen U)
    (hf : ContDiffMBOn k f (univ ×ˢ U)) (w : DiffeoModel A) :
    ContDiffMBOn k (fun z ↦ f (w, z)) U :=
  ContDiffMBOn.comp (g := f) (f := fun z : H ↦ (w, z)) hU (isOpen_univ.prod hU) hf
    ((contDiffMBOn_const k w U).prodMk hU (smoothMBOn_id U k)) fun _ hz ↦ ⟨mem_univ _, hz⟩

/-! ### Changing charts -/

/-- **The equation `ċ = -w(c)` does not depend on the chart.** -/
theorem hasDerivWithinAt_transfer {c : ℝ → K} {S : Set ℝ} {t : ℝ} (hc : ContinuousWithinAt c S t)
    (i j : atlas H K) (hi : c t ∈ i.1.source) (hj : c t ∈ j.1.source) (w : DiffeoModel A)
    (hd : HasDerivWithinAt (fun s ↦ i.1 (c s)) (-rep A i w (i.1 (c t))) S t) :
    HasDerivWithinAt (fun s ↦ j.1 (c s)) (-rep A j w (j.1 (c t))) S t := by
  set D := i.1.target ∩ i.1.symm ⁻¹' j.1.source
  have hD : IsOpen D := i.1.isOpen_inter_preimage_symm j.1.open_source
  have hzD : i.1 (c t) ∈ D :=
    ⟨i.1.map_source hi, by rw [mem_preimage, i.1.left_inv hi]; exact hj⟩
  have hτ : ContDiffOn ℝ 1 (j.1 ∘ i.1.symm) D :=
    (contDiffMBOn_iff_contDiffOn hD).1 (smoothMBOn_transition i.2 j.2 1)
  have hF : HasFDerivAt (j.1 ∘ i.1.symm) (fderiv ℝ (j.1 ∘ i.1.symm) (i.1 (c t))) (i.1 (c t)) :=
    ((hτ.contDiffAt (hD.mem_nhds hzD)).differentiableAt one_ne_zero).hasFDerivAt
  have hcomp := hF.comp_hasDerivWithinAt t hd
  have hval : fderiv ℝ (j.1 ∘ i.1.symm) (i.1 (c t)) (-rep A i w (i.1 (c t))) =
      -rep A j w (j.1 (c t)) := by
    rw [map_neg, ← dMB_eq_fderiv hD hτ hzD, ← rep_transition A i j w (i.1.map_source hi)
      (by rw [i.1.left_inv hi]; exact hj), i.1.left_inv hi]
  rw [hval] at hcomp
  refine hcomp.congr_of_eventuallyEq ?_ ?_
  · have hev : ∀ᶠ s in 𝓝[S] t, c s ∈ i.1.source :=
      hc (i.1.open_source.mem_nhds hi)
    filter_upwards [hev] with s hs
    simp [i.1.left_inv hs]
  · simp [i.1.left_inv hi]

/-! ### Integral curves -/

/-- **`c` is an integral curve of `-ξ` on `[0, 1]`**: `ċ(t) = -ξ(t)(c(t))`, read in every chart. -/
def IsIntCurve (ξ : C(I, DiffeoModel A)) (c : ℝ → K) : Prop :=
  ContinuousOn c (Icc 0 1) ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ j : atlas H K, c t ∈ j.1.source →
    HasDerivWithinAt (fun s ↦ j.1 (c s)) (-rep A j (extendCurve ξ t) (j.1 (c t))) (Icc 0 1) t

/-- **Solutions in a chart are integral curves.** -/
theorem isIntCurve_sol (i : atlas H K) {N : Set (DiffeoModel A)} {z₀ : H} {r : ℝ}
    (hf : ParamODE.IsData (vf A i) N z₀ r) (hB : ball z₀ (3 * r) ⊆ i.1.target)
    {ξ : C(I, DiffeoModel A)} (hξ : ξ ∈ valIn N) {y : K} (hyr : i.1 y ∈ ball z₀ r) :
    IsIntCurve A ξ (fun s ↦ i.1.symm (extendCurve (ParamODE.sol hf (ξ, i.1 y)) s)) := by
  have hp : (ξ, i.1 y) ∈ ParamODE.par N z₀ r := ⟨hξ, hyr⟩
  set γ := extendCurve (ParamODE.sol hf (ξ, i.1 y))
  have hγ : ∀ s, γ s ∈ i.1.target := fun s ↦ by
    simp only [γ, MBLieGroup.extendCurve_apply]
    exact hB (ParamODE.sol_mem_ball hf hp _)
  have hcont : Continuous fun s ↦ i.1.symm (γ s) :=
    i.1.continuousOn_symm.comp_continuous (MBLieGroup.continuous_extendCurve _) hγ
  refine ⟨hcont.continuousOn, fun t ht j hj ↦ ?_⟩
  have hi : i.1.symm (γ t) ∈ i.1.source := i.1.map_target (hγ t)
  refine hasDerivWithinAt_transfer A hcont.continuousWithinAt i j hi hj _ ?_
  have he : (fun s ↦ i.1 (i.1.symm (γ s))) = γ := funext fun s ↦ i.1.right_inv (hγ s)
  rw [he, i.1.right_inv (hγ t)]
  exact ParamODE.hasDerivWithinAt_sol hf hp ht

/-- **Local Lipschitz bounds**: near a point of a chart, the representatives `-w̃_j` are Lipschitz
with a common constant for `w` in a compact set. -/
theorem exists_lipschitz (j : atlas H K) {z : H} (hz : z ∈ j.1.target) {Q : Set (DiffeoModel A)}
    (hQ : IsCompact Q) : ∃ ρ > 0, ∃ M : ℝ≥0, ball z ρ ⊆ j.1.target ∧
      ∀ w ∈ Q, LipschitzOnWith M (fun z' ↦ -rep A j w z') (ball z ρ) := by
  obtain ⟨ε, hε, hεt⟩ := Metric.isOpen_iff.1 j.1.open_target z hz
  set ρ := ε / 2
  have hρ : 0 < ρ := by positivity
  have hcl : closedBall z ρ ⊆ j.1.target :=
    (closedBall_subset_ball (by simp only [ρ]; linarith)).trans hεt
  set f : DiffeoModel A × H → H := fun q ↦ rep A j q.1 q.2
  have hU : IsOpen (univ ×ˢ j.1.target : Set (DiffeoModel A × H)) :=
    isOpen_univ.prod j.1.open_target
  have hf : ContDiffMBOn 1 f (univ ×ˢ j.1.target) := smoothMBOn_rep A j 1
  set Qc : Set (DiffeoModel A × (H × H)) := Q ×ˢ (closedBall z ρ ×ˢ closedBall 0 1)
  have hQc : IsCompact Qc := hQ.prod ((isCompact_closedBall z ρ).prod (isCompact_closedBall 0 1))
  have hcd : ContinuousOn (dMB f) ((univ ×ˢ j.1.target) ×ˢ univ) := hf.2.2
  have hφ : ContinuousOn (fun q : DiffeoModel A × (H × H) ↦ dMB f ((q.1, q.2.1), (0, q.2.2))) Qc :=
    ContinuousOn.comp (g := dMB f)
      (f := fun q : DiffeoModel A × (H × H) ↦ ((q.1, q.2.1), ((0 : DiffeoModel A), q.2.2))) hcd
      (Continuous.continuousOn (by fun_prop))
      fun q hq ↦ ⟨⟨mem_univ _, hcl hq.2.1⟩, mem_univ _⟩
  obtain ⟨C, hC⟩ := hQc.exists_bound_of_continuousOn hφ
  set M : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  refine ⟨ρ, hρ, M, (ball_subset_closedBall).trans hcl, fun w hw ↦ ?_⟩
  have hg : ContDiffMBOn 1 (fun z' ↦ rep A j w z') j.1.target :=
    contDiffMBOn_slice A j.1.open_target hf w
  have hb : ∀ z' ∈ ball z ρ, ∀ h, ‖dMB (fun z' ↦ rep A j w z') (z', h)‖ ≤ (M : ℝ) * ‖h‖ := by
    intro z' hz' h
    rw [dMB_slice_right f w z' h]
    refine norm_le_mul_of_closedBall (L := fun h ↦ dMB f ((w, z'), (0, h))) (fun c h ↦ ?_)
      (fun h hh ↦ (hC (w, z', h) ⟨hw, ball_subset_closedBall hz', hh⟩).trans
        (le_max_left _ _)) h
    have := hf.dMB_smul (x := (w, z')) ⟨mem_univ _, hcl (ball_subset_closedBall hz')⟩ c
      ((0 : DiffeoModel A), h)
    simpa using this
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb' ↦ ?_
  rw [dist_eq_norm, dist_eq_norm, neg_sub_neg, norm_sub_rev]
  exact norm_sub_le_of_dMB_le j.1.open_target hg (convex_ball z ρ)
    ((ball_subset_closedBall).trans hcl) M.2 hb ha hb'

/-- **Uniqueness of integral curves.** -/
theorem IsIntCurve.eqOn {ξ : C(I, DiffeoModel A)} {c₁ c₂ : ℝ → K} (h₁ : IsIntCurve A ξ c₁)
    (h₂ : IsIntCurve A ξ c₂) (h0 : c₁ 0 = c₂ 0) : EqOn c₁ c₂ (Icc 0 1) := by
  set S := {t | c₁ t = c₂ t}
  have hS : IsClosed (S ∩ Icc 0 1) := by
    have hc : ContinuousOn (fun t ↦ (c₁ t, c₂ t)) (Icc 0 1) := h₁.1.prodMk h₂.1
    have := hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_diagonal
    rw [inter_comm]
    exact this
  refine fun t ht ↦ hS.Icc_subset_of_forall_mem_nhdsWithin h0 ?_ ht
  rintro t₁ ⟨ht₁, ht₁I⟩
  have ht₁c : t₁ ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self ht₁I
  set q := c₁ t₁
  set j : atlas H K := ⟨chartAt H q, chart_mem_atlas H q⟩
  have hq : q ∈ j.1.source := mem_chart_source H q
  have hQ : IsCompact (range ξ) := isCompact_range ξ.continuous
  have hrange : ∀ s, extendCurve ξ s ∈ range ξ := fun s ↦ by
    rw [MBLieGroup.extendCurve_apply]; exact mem_range_self _
  obtain ⟨ρ, hρ, M, -, hlip⟩ := exists_lipschitz A j (j.1.map_source hq) hQ
  set O := j.1.source ∩ j.1 ⁻¹' ball (j.1 q) ρ
  have hO : O ∈ 𝓝 q := (j.1.isOpen_inter_preimage isOpen_ball).mem_nhds ⟨hq, mem_ball_self hρ⟩
  have hI : Icc (0 : ℝ) 1 ∈ 𝓝[≥] t₁ :=
    mem_of_superset (Icc_mem_nhdsGE ht₁I.2) (Icc_subset_Icc_left ht₁I.1)
  have hev : ∀ᶠ s in 𝓝[≥] t₁, c₁ s ∈ O ∧ c₂ s ∈ O := by
    have e₁ : ∀ᶠ s in 𝓝[Icc 0 1] t₁, c₁ s ∈ O := h₁.1 t₁ ht₁c hO
    have e₂ : ∀ᶠ s in 𝓝[Icc 0 1] t₁, c₂ s ∈ O := h₂.1 t₁ ht₁c (by rw [← ht₁]; exact hO)
    exact nhdsWithin_le_of_mem hI (e₁.and e₂)
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset).1 hev
  set b := min ((t₁ + u) / 2) 1
  have htb : t₁ < b := lt_min (by linarith [hu.out]) ht₁I.2
  have hbu : b < u := (min_le_left _ _).trans_lt (by linarith [hu.out])
  have hb1 : b ≤ 1 := min_le_right _ _
  have hP : ∀ s ∈ Icc t₁ b, c₁ s ∈ O ∧ c₂ s ∈ O := fun s hs ↦ hsub ⟨hs.1, hs.2.trans_lt hbu⟩
  have hIcc : Icc t₁ b ⊆ Icc 0 1 := Icc_subset_Icc ht₁I.1 hb1
  have hder : ∀ {c : ℝ → K}, IsIntCurve A ξ c → (∀ s ∈ Icc t₁ b, c s ∈ O) →
      ∀ s ∈ Ico t₁ b, HasDerivWithinAt (fun s ↦ j.1 (c s))
        ((fun s z ↦ -rep A j (extendCurve ξ s) z) s (j.1 (c s))) (Ici s) s := by
    intro c hc hcO s hs
    have hs1 : s ∈ Ico (0 : ℝ) 1 := ⟨ht₁I.1.trans hs.1, hs.2.trans_le hb1⟩
    exact (hc.2 s (Ico_subset_Icc_self hs1) j
      (hcO s (Ico_subset_Icc_self hs)).1).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE hs1.2) (Icc_subset_Icc_left hs1.1))
  have hcont : ∀ {c : ℝ → K}, IsIntCurve A ξ c → (∀ s ∈ Icc t₁ b, c s ∈ O) →
      ContinuousOn (fun s ↦ j.1 (c s)) (Icc t₁ b) := fun hc hcO ↦
    j.1.continuousOn.comp (hc.1.mono hIcc) fun s hs ↦ (hcO s hs).1
  have heq := ODE_solution_unique_of_mem_Icc_right (K := M)
    (v := fun s z ↦ -rep A j (extendCurve ξ s) z) (s := fun _ ↦ ball (j.1 q) ρ)
    (fun s _ ↦ hlip _ (hrange s)) (hcont h₁ fun s hs ↦ (hP s hs).1)
    (hder h₁ fun s hs ↦ (hP s hs).1) (fun s hs ↦ (hP s (Ico_subset_Icc_self hs)).1.2)
    (hcont h₂ fun s hs ↦ (hP s hs).2) (hder h₂ fun s hs ↦ (hP s hs).2)
    (fun s hs ↦ (hP s (Ico_subset_Icc_self hs)).2.2) (congrArg (fun x ↦ j.1 x) ht₁)
  refine (mem_nhdsGT_iff_exists_Ioc_subset).2 ⟨b, htb, fun s hs ↦ ?_⟩
  have hs' : s ∈ Icc t₁ b := Ioc_subset_Icc_self hs
  exact j.1.injOn (hP s hs').1.1 (hP s hs').2.1 (heq hs')

end Diffeo

end LocallyConvex.LieGroups
