/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.CircleCover.Inverse
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Rotations of the plane by periodic angles

Identifying `ℝ²` with `ℂ` (`CircleCover.J`), a periodic function `u ∈ C^∞_per` acts on the
punctured plane by `rotU(u, z) = e^{2πi u(arg z/2π)} z`. Since `u` is `1`-periodic, `u(arg z/2π)`
does not depend on the choice of the argument, and `rotU` is smooth on `C^∞_per × (ℝ² ∖ 0)`. On
the circle, `rotU(u, e^{2πit}) = e^{2πi(t + u(t))}`: this is the action of the diffeomorphism
`id + u` of `ℝ` on `S¹ = ℝ/ℤ`.

## Main definitions

* `CircleCover.J`: the isometry `ℝ² ≅ ℂ`.
* `CircleCover.expC t = e^{2πit}` and `CircleCover.ang w = arg w/2π`.
* `CircleCover.rotU (u, z) = e^{2πi u(arg z/2π)} z`.
* `CircleCover.relAng z w = arg(z w̄)/2π`, the angle from `w` to `z`.

## Main results

* `CircleCover.smoothMBOn_rotU`: `rotU` is smooth on `C^∞_per × (ℝ² ∖ 0)`.
* `CircleCover.rotU_expC`: `rotU(u, e^{2πit}) = e^{2πi(t + u(t))}`.
* `CircleCover.rotU_relAng`: for unit vectors, rotating `w` by `relAng z w` gives `z`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function Complex
open scoped Topology ContDiff Real ComplexConjugate
open LocallyConvex.Analysis LocallyConvex.Manifolds CInfPer DiffCircle

noncomputable section

namespace LocallyConvex.LieGroups.CircleCover

/-- The plane. -/
abbrev R2 : Type := EuclideanSpace ℝ (Fin 2)

/-- **`ℝ² ≅ ℂ`**, `(x, y) ↦ x + iy`. -/
def J : R2 ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm

theorem contDiff_J : ContDiff ℝ ∞ (J : R2 → ℂ) := J.toContinuousLinearEquiv.contDiff

theorem contDiff_J_symm : ContDiff ℝ ∞ (J.symm : ℂ → R2) := J.symm.toContinuousLinearEquiv.contDiff

/-- `e^{2πit}`. -/
def expC (t : ℝ) : ℂ := Complex.exp (↑(2 * π * t) * I)

/-- `arg w/2π`. -/
def ang (w : ℂ) : ℝ := Complex.arg w / (2 * π)

theorem norm_expC (t : ℝ) : ‖expC t‖ = 1 := by
  rw [expC, Complex.norm_exp_ofReal_mul_I]

theorem expC_add (s t : ℝ) : expC (s + t) = expC s * expC t := by
  rw [expC, expC, expC, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem expC_ang {w : ℂ} (hw : ‖w‖ = 1) : expC (ang w) = w := by
  have h := Complex.norm_mul_exp_arg_mul_I w
  rw [hw, Complex.ofReal_one, one_mul] at h
  rw [expC, ang, show 2 * π * (Complex.arg w / (2 * π)) = Complex.arg w by
    field_simp]
  exact h

/-- `arg(e^{2πit})/2π ≡ t` modulo `1`. -/
theorem exists_ang_expC (t : ℝ) : ∃ n : ℤ, ang (expC t) = t + n := by
  refine ⟨-toIocDiv Real.two_pi_pos (-π) (2 * π * t), ?_⟩
  rw [ang, expC, Complex.arg_exp_mul_I]
  have h := toIocMod_add_toIocDiv_zsmul Real.two_pi_pos (-π) (2 * π * t)
  rw [zsmul_eq_mul] at h
  field_simp
  push_cast
  linarith

/-- `arg(-w)/2π ≡ arg(w)/2π + 1/2` modulo `1`. -/
theorem exists_ang_neg {w : ℂ} (hw : w ≠ 0) : ∃ n : ℤ, ang (-w) = ang w + 1 / 2 + n := by
  have h := Complex.arg_neg_coe_angle hw
  rw [← Real.Angle.coe_add, Real.Angle.angle_eq_iff_two_pi_dvd_sub] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  rw [ang, ang]
  field_simp
  linarith

/-- `u(arg z/2π)`. -/
def uz (u : CInfPer) (z : R2) : ℝ := u (ang (J z))

theorem uz_eq_neg (u : CInfPer) {z : R2} (hz : z ≠ 0) : uz u z = u (ang (-J z) + 1 / 2) := by
  have hJ : J z ≠ 0 := by simpa using hz
  obtain ⟨n, hn⟩ := exists_ang_neg hJ
  rw [uz, hn, show ang (J z) + 1 / 2 + n + 1 / 2 = ang (J z) + ((n + 1 : ℤ) : ℝ) by
    push_cast; ring]
  exact (show u (ang (J z) + ((n + 1 : ℤ) : ℝ)) = u (ang (J z)) by
    simpa using u.periodic.int_mul (n + 1) (ang (J z))).symm

/-- **The rotation by the periodic angle `u`**: `rotU(u, z) = e^{2πi u(arg z/2π)} z`. -/
def rotU (p : CInfPer × R2) : R2 := J.symm (expC (uz p.1 p.2) * J p.2)

theorem norm_rotU (p : CInfPer × R2) : ‖rotU p‖ = ‖p.2‖ := by
  rw [rotU, LinearIsometryEquiv.norm_map, norm_mul, norm_expC, one_mul,
    LinearIsometryEquiv.norm_map]

/-- **`rotU(u, e^{2πit}) = e^{2πi(t + u(t))}`.** -/
theorem rotU_expC (u : CInfPer) (t : ℝ) :
    rotU (u, J.symm (expC t)) = J.symm (expC (t + u t)) := by
  obtain ⟨n, hn⟩ := exists_ang_expC t
  have hu : uz u (J.symm (expC t)) = u t := by
    rw [uz, LinearIsometryEquiv.apply_symm_apply, hn]
    simpa using u.periodic.int_mul n t
  rw [rotU, hu, LinearIsometryEquiv.apply_symm_apply, ← expC_add, add_comm]

/-- `arg(z w̄)/2π`, the angle from `w` to `z`. -/
def relAng (z w : R2) : ℝ := ang (J z * conj (J w))

/-- **Rotating `w` by the angle from `w` to `z` gives `z`**, for unit vectors. -/
theorem rotU_relAng {z w : R2} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    J.symm (expC (relAng z w) * J w) = z := by
  have hv : ‖J z * conj (J w)‖ = 1 := by
    rw [norm_mul, Complex.norm_conj, LinearIsometryEquiv.norm_map,
      LinearIsometryEquiv.norm_map, hz, hw, one_mul]
  rw [relAng, expC_ang hv, mul_assoc, Complex.conj_mul', LinearIsometryEquiv.norm_map, hw]
  simp

/-! ### Smoothness -/

/-- `w ↦ arg w/2π` is smooth on the slit plane. -/
theorem contDiffAt_ang {w : ℂ} (hw : w ∈ Complex.slitPlane) : ContDiffAt ℝ ∞ ang w := by
  have hlog : ContDiffAt ℝ ∞ Complex.log w := (Complex.contDiffAt_log hw).restrict_scalars ℝ
  have h : ang = fun w ↦ Complex.imCLM (Complex.log w) / (2 * π) := by
    funext w; simp [ang, Complex.log_im]
  rw [h]
  exact (Complex.imCLM.contDiff.contDiffAt.comp w hlog).div_const _

theorem contDiff_expC : ContDiff ℝ ∞ expC := by
  have h0 : ContDiff ℝ ∞ fun t : ℝ ↦ 2 * π * t := contDiff_const.mul contDiff_id
  have h1 : ContDiff ℝ ∞ fun t : ℝ ↦ (↑(2 * π * t) : ℂ) * I :=
    (Complex.ofRealCLM.contDiff.comp h0).mul contDiff_const
  have hexp : ContDiff ℝ ∞ Complex.exp :=
    ContDiff.restrict_scalars (𝕜 := ℝ) (𝕜' := ℂ) Complex.contDiff_exp
  exact hexp.comp h1

theorem mem_slitPlane_or_neg {w : ℂ} (hw : w ≠ 0) :
    w ∈ Complex.slitPlane ∨ -w ∈ Complex.slitPlane := by
  by_contra h
  push Not at h
  rw [Complex.mem_slitPlane_iff, Complex.mem_slitPlane_iff] at h
  push Not at h
  apply hw
  apply Complex.ext
  · simp only [Complex.neg_re] at h; simp; linarith [h.1.1, h.2.1]
  · simpa using h.1.2

/-- The angle function, read through a smooth branch of the argument on an open set. -/
theorem contDiffMBOn_uz_of {A : Set R2} (hA : IsOpen A) {a : R2 → ℝ}
    (ha : ContDiffOn ℝ ∞ a A) (heq : ∀ u : CInfPer, ∀ z ∈ A, uz u z = u (a z)) (k : ℕ) :
    ContDiffMBOn k (fun p : CInfPer × R2 ↦ uz p.1 p.2) (univ ×ˢ A) := by
  have hO : IsOpen ((univ : Set CInfPer) ×ˢ A) := isOpen_univ.prod hA
  have haMB : ContDiffMBOn k a A := ((smoothMBOn_iff_contDiffOn hA).2 ha) k
  have hin : ContDiffMBOn k (fun p : CInfPer × R2 ↦ (p.1, a p.2)) (univ ×ˢ A) :=
    (((ContinuousLinearMap.fst ℝ CInfPer R2).contDiffMBOn k univ).mono (subset_univ _)).prodMk hO
      (ContDiffMBOn.comp (g := a) (f := fun p : CInfPer × R2 ↦ p.2) hO hA haMB
        (((ContinuousLinearMap.snd ℝ CInfPer R2).contDiffMBOn k univ).mono (subset_univ _))
        fun p hp ↦ hp.2)
  refine ContDiffMBOn.congr_of_isOpen hO (fun p hp ↦ ?_)
    (ContDiffMBOn.comp (g := ev) hO isOpen_univ (smoothMBOn_ev k) hin (mapsTo_univ _ _))
  exact (heq p.1 p.2 hp.2).symm

/-- **`(u, z) ↦ u(arg z/2π)` is smooth** on `C^∞_per × (ℝ² ∖ 0)`. -/
theorem smoothMBOn_uz :
    SmoothMBOn (fun p : CInfPer × R2 ↦ uz p.1 p.2) (univ ×ˢ {z : R2 | z ≠ 0}) := by
  intro k
  have hO : IsOpen ((univ : Set CInfPer) ×ˢ {z : R2 | z ≠ 0}) := isOpen_univ.prod isOpen_ne
  refine ContDiffMBOn.of_local hO fun p hp ↦ ?_
  have hJ : J p.2 ≠ 0 := by simpa using hp.2
  rcases mem_slitPlane_or_neg hJ with h1 | h2
  · set A := {z : R2 | J z ∈ Complex.slitPlane}
    have hA : IsOpen A := Complex.isOpen_slitPlane.preimage J.continuous
    have ha : ContDiffOn ℝ ∞ (fun z ↦ ang (J z)) A := fun z hz ↦
      ((contDiffAt_ang hz).comp z contDiff_J.contDiffAt).contDiffWithinAt
    exact ⟨univ ×ˢ A, isOpen_univ.prod hA, ⟨mem_univ _, h1⟩,
      (contDiffMBOn_uz_of hA ha (fun _ _ _ ↦ rfl) k).mono inter_subset_right⟩
  · set A := {z : R2 | -J z ∈ Complex.slitPlane}
    have hA : IsOpen A := Complex.isOpen_slitPlane.preimage J.continuous.neg
    have ha : ContDiffOn ℝ ∞ (fun z ↦ ang (-J z) + 1 / 2) A := fun z hz ↦
      (((contDiffAt_ang hz).comp z
        contDiff_J.neg.contDiffAt).add contDiffAt_const).contDiffWithinAt
    refine ⟨univ ×ˢ A, isOpen_univ.prod hA, ⟨mem_univ _, h2⟩,
      (contDiffMBOn_uz_of hA ha (fun u z hz ↦ uz_eq_neg u ?_) k).mono inter_subset_right⟩
    intro h0
    change -J z ∈ Complex.slitPlane at hz
    rw [h0, map_zero, neg_zero] at hz
    exact Complex.zero_notMem_slitPlane hz

/-- `(c, z) ↦ e^{2πic} z`. -/
def rotC (p : ℝ × R2) : R2 := J.symm (expC p.1 * J p.2)

theorem contDiff_rotC : ContDiff ℝ ∞ rotC := by
  have h1 : ContDiff ℝ ∞ fun p : ℝ × R2 ↦ expC p.1 := contDiff_expC.comp contDiff_fst
  have h2 : ContDiff ℝ ∞ fun p : ℝ × R2 ↦ J p.2 := contDiff_J.comp contDiff_snd
  have h3 : ContDiff ℝ ∞ fun p : ℝ × R2 ↦ expC p.1 * J p.2 := h1.mul h2
  exact contDiff_J_symm.comp h3

theorem smoothMBOn_rotC : SmoothMBOn rotC univ :=
  (smoothMBOn_iff_contDiffOn isOpen_univ).2 contDiff_rotC.contDiffOn

/-- **`rotU` is smooth** on `C^∞_per × (ℝ² ∖ 0)`. -/
theorem smoothMBOn_rotU : SmoothMBOn rotU (univ ×ˢ {z : R2 | z ≠ 0}) := fun k ↦ by
  have hO : IsOpen ((univ : Set CInfPer) ×ˢ {z : R2 | z ≠ 0}) := isOpen_univ.prod isOpen_ne
  have hin : ContDiffMBOn k (fun p : CInfPer × R2 ↦ (uz p.1 p.2, p.2))
      (univ ×ˢ {z : R2 | z ≠ 0}) :=
    (smoothMBOn_uz k).prodMk hO
      (((ContinuousLinearMap.snd ℝ CInfPer R2).contDiffMBOn k univ).mono (subset_univ _))
  have h := ContDiffMBOn.comp (g := rotC) (f := fun p : CInfPer × R2 ↦ (uz p.1 p.2, p.2)) hO
    isOpen_univ (smoothMBOn_rotC k) hin (mapsTo_univ _ _)
  exact h

/-- `(z, w) ↦ arg(z w̄)/2π` is smooth where `z w̄` is in the slit plane. -/
theorem contDiffOn_relAng :
    ContDiffOn ℝ ∞ (fun p : R2 × R2 ↦ relAng p.1 p.2)
      {p | J p.1 * conj (J p.2) ∈ Complex.slitPlane} := by
  intro p hp
  have hm : ContDiff ℝ ∞ fun p : R2 × R2 ↦ J p.1 * conj (J p.2) :=
    (contDiff_J.comp contDiff_fst).mul
      (Complex.conjCLE.contDiff.comp (contDiff_J.comp contDiff_snd))
  exact ((contDiffAt_ang hp).comp p hm.contDiffAt).contDiffWithinAt

end LocallyConvex.LieGroups.CircleCover
