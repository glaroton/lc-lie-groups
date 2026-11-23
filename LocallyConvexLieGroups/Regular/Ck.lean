/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Regular.Evol
public import LocallyConvexAnalysis.Calculus.DenseInterior.SmoothExpLaw

/-!
# `C^k`-regular and regular Lie groups

A Lie group `G` is **`C^k`-regular** if every `ξ ∈ C^k([0, 1], 𝔤)` has an evolution and
`evol : C^k([0, 1], 𝔤) → G` is smooth, and **regular** (in the sense of Milnor) if the same holds
for `C^∞([0, 1], 𝔤)` ([GN26, Definition 6.1.1]). The spaces `C^k([0, 1], 𝔤)` and
`C^∞([0, 1], 𝔤)` carry the compact-open `C^k` and `C^∞` topologies (lc-analysis, `ContDiffLCMap`
and `SmoothLCMap` on the interval `[0, 1]`, which has dense interior). Since the inclusions
`C^r ⊆ C^k ⊆ C⁰` are continuous linear maps, `C^k`-regularity implies `C^r`-regularity for
`k ≤ r`, and `C⁰`-regularity implies all of them ([GN26, Remark 6.1.2(c)]).

## Main definitions

* `MBLieGroup.CkCurve E k`, `MBLieGroup.SmoothCurve E`: `C^k([0, 1], E)` and `C^∞([0, 1], E)`.
* `MBLieGroup.CkCurve.toC0`, `MBLieGroup.CkCurve.ofLE`, `MBLieGroup.SmoothCurve.toCk`: the
  inclusions, as continuous linear maps.
* `MBLieGroup.IsCkRegular E G k`, `MBLieGroup.IsRegular E G`.

## Main results

* `MBLieGroup.IsCkRegular.mono`: `C^k`-regular implies `C^r`-regular for `k ≤ r`.
* `MBLieGroup.IsCkRegular.isRegular`: `C^k`-regular implies regular.
* `MBLieGroup.IsC0Regular.isCkRegular`, `MBLieGroup.IsC0Regular.isRegular`:
  **`C⁰`-regular Lie groups are `C^k`-regular for all `k` and regular** ([GN26, Remark 6.1.2(c)]).

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

/-- `[0, 1]` has dense interior. -/
theorem hasDenseInterior_Icc : HasDenseInterior (Icc (0 : ℝ) 1) :=
  (convex_Icc 0 1).hasDenseInterior ⟨1 / 2, by rw [interior_Icc]; constructor <;> norm_num⟩

variable (E : Type u) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

/-- **`C^k([0, 1], E)`**, with the compact-open `C^k` topology. -/
abbrev CkCurve (k : ℕ) : Type u := ContDiffLCMap E k (Icc (0 : ℝ) 1) hasDenseInterior_Icc

/-- **`C^∞([0, 1], E)`**, with the compact-open `C^∞` topology. -/
abbrev SmoothCurve : Type u := SmoothLCMap E (Icc (0 : ℝ) 1) hasDenseInterior_Icc

variable {E}

variable (E) in
/-- `f ↦ (t ↦ f(t, ()))`. -/
def precompCLM : C(I × (Fin 0 → ℝ), E) →L[ℝ] C(I, E) where
  toFun f := f.comp ⟨fun t ↦ (t, Fin.elim0), by fun_prop⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := ContinuousMap.continuous_precomp _

namespace CkCurve

/-- The inclusion `C^k([0, 1], E) → C([0, 1], E)`. -/
def toC0 {k : ℕ} : CkCurve E k →L[ℝ] C(I, E) :=
  (precompCLM E).comp (ContDiffLCMap.iteratedDCLM 0 (Nat.zero_le k))

@[simp] theorem toC0_apply {k : ℕ} (γ : CkCurve E k) (t : I) : toC0 γ t = γ t := rfl

/-- The inclusion `C^r([0, 1], E) → C^k([0, 1], E)` for `k ≤ r`. -/
def ofLE {k r : ℕ} (h : k ≤ r) : CkCurve E r →L[ℝ] CkCurve E k where
  toFun γ := ContDiffLCMap.mk γ (γ.contDiffLC.of_le h) fun _ hx ↦ γ.apply_of_notMem hx
  map_add' _ _ := ContDiffLCMap.ext fun _ ↦ rfl
  map_smul' _ _ := ContDiffLCMap.ext fun _ ↦ rfl
  cont := continuous_induced_rng.2 (continuous_pi fun j ↦
    ContDiffLCMap.continuous_iteratedD (F := E) (k := r) (hV := hasDenseInterior_Icc) j
      (by have := j.2; omega))

@[simp] theorem toC0_ofLE {k r : ℕ} (h : k ≤ r) (γ : CkCurve E r) : toC0 (ofLE h γ) = toC0 γ :=
  rfl

end CkCurve

namespace SmoothCurve

/-- The inclusion `C^∞([0, 1], E) → C^k([0, 1], E)`. -/
def toCk (k : ℕ) : SmoothCurve E →L[ℝ] CkCurve E k :=
  ⟨SmoothLCMap.toContDiff k, SmoothLCMap.continuous_toContDiff k⟩

/-- The inclusion `C^∞([0, 1], E) → C([0, 1], E)`. -/
def toC0 : SmoothCurve E →L[ℝ] C(I, E) := CkCurve.toC0.comp (toCk 0)

@[simp] theorem toC0_toCk (k : ℕ) (γ : SmoothCurve E) : CkCurve.toC0 (toCk k γ) = toC0 γ := rfl

end SmoothCurve

variable (E) (G : Type*) [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]

/-- **`C^k`-regular Lie groups** ([GN26, Definition 6.1.1]): every `ξ ∈ C^k([0, 1], 𝔤)` has an
evolution, and `evol : C^k([0, 1], 𝔤) → G` is smooth. -/
structure IsCkRegular (k : ℕ) : Prop where
  semiregular : ∀ ξ : CkCurve E k, ∃ γ : ℝ → G, IsEvol E (extendCurve (CkCurve.toC0 ξ)) γ
  smooth : SmoothMBM (CkCurve E k) E fun ξ : CkCurve E k ↦ evol E G (CkCurve.toC0 ξ)

/-- **Regular Lie groups** in the sense of Milnor ([GN26, Definition 6.1.1], `k = ∞`): every
`ξ ∈ C^∞([0, 1], 𝔤)` has an evolution, and `evol : C^∞([0, 1], 𝔤) → G` is smooth. -/
structure IsRegular : Prop where
  semiregular : ∀ ξ : SmoothCurve E, ∃ γ : ℝ → G, IsEvol E (extendCurve (SmoothCurve.toC0 ξ)) γ
  smooth : SmoothMBM (SmoothCurve E) E fun ξ : SmoothCurve E ↦ evol E G (SmoothCurve.toC0 ξ)

variable {E G}

/-- Smoothness of `evol ∘ L` for a continuous linear map `L`. -/
theorem smoothMBM_evol_comp {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X]
    {Y : Type u} [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y] [T2Space Y]
    {f : Y → G} (hf : SmoothMBM Y E f) (L : X →L[ℝ] Y) : SmoothMBM X E fun x ↦ f (L x) :=
  hf.comp fun k ↦ (contMDiffMBOn_iff_contDiffMBOn isOpen_univ).2 (L.contDiffMBOn k univ)

/-- **`C^k`-regular implies `C^r`-regular for `k ≤ r`** ([GN26, Remark 6.1.2(c)]). -/
theorem IsCkRegular.mono {k r : ℕ} (h : IsCkRegular E G k) (hkr : k ≤ r) :
    IsCkRegular E G r where
  semiregular ξ := h.semiregular (CkCurve.ofLE hkr ξ)
  smooth := smoothMBM_evol_comp h.smooth (CkCurve.ofLE hkr)

/-- **`C^k`-regular implies regular** ([GN26, Remark 6.1.2(c)]). -/
theorem IsCkRegular.isRegular {k : ℕ} (h : IsCkRegular E G k) : IsRegular E G where
  semiregular ξ := h.semiregular (SmoothCurve.toCk k ξ)
  smooth := smoothMBM_evol_comp h.smooth (SmoothCurve.toCk k)

/-- **`C⁰`-regular implies `C^k`-regular** ([GN26, Remark 6.1.2(c)]). -/
theorem IsC0Regular.isCkRegular (h : IsC0Regular E G) (k : ℕ) : IsCkRegular E G k where
  semiregular ξ := h.semiregular (CkCurve.toC0 ξ)
  smooth := smoothMBM_evol_comp h.smooth CkCurve.toC0

/-- **`C⁰`-regular implies regular** ([GN26, Remark 6.1.2(c)]). -/
theorem IsC0Regular.isRegular (h : IsC0Regular E G) : IsRegular E G :=
  (h.isCkRegular 0).isRegular

end LocallyConvex.LieGroups.MBLieGroup
