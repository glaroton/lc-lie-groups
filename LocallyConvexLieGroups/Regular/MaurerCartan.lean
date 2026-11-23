/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.LieAlgebra.Adjoint

/-!
# The Maurer–Cartan equation of logarithmic derivatives

For a smooth map `F : O → G` on an open subset `O` of a locally convex space, the left
logarithmic derivative `δF(q)(h) = F(q)⁻¹ dF(q) h` is read in the chart `φ` at the identity: it is
the derivative of `r ↦ φ(F(q)⁻¹ F(r))` at `q` in the direction `h` (`MBLieGroup.logDeriv`). It is
`C¹` in `q`, and satisfies the **Maurer–Cartan equation**
`d_k(δF(h)) − d_h(δF(k)) = [δF(h), δF(k)]`, that is, `dα + ½[α, α] = 0` for `α = δ(F)`
([GN26, Lemma 5.5.5]).

## Main definitions

* `MBLieGroup.logDeriv E F q h`: the left logarithmic derivative `δF(q)(h)`.

## Main results

* `MBLieGroup.contDiffMBOn_logDeriv`: `q ↦ δF(q)(h)` is `C¹`.
* `MBLieGroup.logDeriv_maurerCartan`: **the Maurer–Cartan equation** ([GN26, Lemma 5.5.5]).
* `dMB_dMB_swap`: Schwarz's theorem for second derivatives along two directions.

## Implementation notes

GN26 evaluates the Maurer–Cartan form on left invariant vector fields. We work in the chart:
with `c(r) = φ(F(p)⁻¹ F(r))` and `c(p) = φ(1)`, the relation `F(r) = F(q) (F(q)⁻¹ F(r))` gives
`dc(q) h = (δF(q) h)~_l(c q)`, where `x̃_l(z) = d(b ↦ z ∗ b)(1) x` is the local left invariant
field. Differentiating in `q` at `p` in the direction `k`, using that `x ↦ x̃_l(z)` is linear and
`x̃_l(φ(1)) = x`, gives `d²c(p)(h, k) = d_k(δF(h)) + dδF(h)~_l(φ(1)) δF(k)`; Schwarz's theorem
`d²c(p)(h, k) = d²c(p)(k, h)` then yields the equation, the right-hand side being the bracket
`[x, y] = dỹ_l(1) x − dx̃_l(1) y`. To see that `q ↦ δF(q)(h)` is differentiable, we write
`φ(F(q)⁻¹ F(r)) = ι(c q) ∗ c r` with the local inversion `ι`, a smooth function of `(q, r)`.

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

section Schwarz

variable {X F : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

/-- **Schwarz's theorem** for second derivatives along two directions. -/
theorem dMB_dMB_swap {f : X → F} {U : Set X} (hU : IsOpen U) (hf : ContDiffMBOn 2 f U) {x : X}
    (hx : x ∈ U) (h k : X) :
    dMB (fun z ↦ dMB f (z, h)) (x, k) = dMB (fun z ↦ dMB f (z, k)) (x, h) := by
  have hs := hf.iteratedDMB_swap hU 1 le_rfl x hx ![h, k] 0
  rw [iteratedDMB_add_two, iteratedDMB_add_two, dMB_slice, dMB_slice] at hs
  simpa [Fin.init, Equiv.swap_apply_def, iteratedDMB_zero] using hs.symm

end Schwarz

namespace MBLieGroup

variable {E X : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]
  {F : X → G} {O : Set X}

variable (E) in
/-- **The left logarithmic derivative** `δF(q)(h) = F(q)⁻¹ dF(q) h`, read in the chart at the
identity: the derivative of `r ↦ φ(F(q)⁻¹ F(r))` at `q` in the direction `h`. -/
def logDeriv (F : X → G) (q h : X) : E :=
  dMB (fun r ↦ chartAt E (1 : G) ((F q)⁻¹ * F r)) (q, h)

variable (E) in
/-- The points `r ∈ O` with `F(b)⁻¹ F(r)` in the chart domain at the identity. -/
def relDom (F : X → G) (O : Set X) (b : X) : Set X :=
  {r | r ∈ O ∧ (F b)⁻¹ * F r ∈ (chartAt E (1 : G)).source}

omit [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X] in
theorem isOpen_relDom (hO : IsOpen O) (hF : SmoothMBMOn X E F O) (b : X) :
    IsOpen (relDom E F O b) := by
  have := isTopologicalGroup E G
  have hc : ContinuousOn (fun r ↦ (F b)⁻¹ * F r) O := continuousOn_const.mul (hF 0).1
  exact hc.isOpen_inter_preimage hO (chartAt E (1 : G)).open_source

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X]
  [MBLieGroup E G] in
theorem mem_relDom {b : X} (hb : b ∈ O) : b ∈ relDom E F O b :=
  ⟨hb, by rw [inv_mul_cancel]; exact mem_chart_source E (1 : G)⟩

/-- `r ↦ φ(F(b)⁻¹ F(r))` is smooth. -/
theorem smoothMBOn_rel (hO : IsOpen O) (hF : SmoothMBMOn X E F O) (b : X) :
    SmoothMBOn (fun r ↦ chartAt E (1 : G) ((F b)⁻¹ * F r)) (relDom E F O b) := fun k ↦ by
  have hL : SmoothMBMOn X E (fun r ↦ (F b)⁻¹ * F r) O :=
    SmoothMBMOn.comp (g := fun x : G ↦ (F b)⁻¹ * x) hO isOpen_univ
      (fun k ↦ smoothMBM_mul_left (E := E) (F b)⁻¹ k) hF (mapsTo_univ _ _)
  have h := (hL k).contDiffMBOn_chart hO (chart_mem_atlas X b) (chart_mem_atlas E (1 : G))
  rw [chartAt_self_eq] at h
  have hD : chartDomain (fun r ↦ (F b)⁻¹ * F r) O (OpenPartialHomeomorph.refl X)
      (chartAt E (1 : G)) = relDom E F O b := by
    ext r; simp [chartDomain, relDom]
  rw [hD] at h
  exact h

/-- `x ↦ x̃_l(z)` is linear, so it is its own derivative. -/
theorem _root_.LocallyConvex.LieGroups.LocalGroupLaw.hasDirDerivAt_xl_left
    (L : LocalGroupLaw E) {z : E} (hz : z ∈ L.domR) (x a : E) :
    HasDirDerivAt (fun x' ↦ L.xl x' z) x a (L.xl a z) := by
  unfold HasDirDerivAt
  refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t (ht : t ≠ 0) ↦ ?_)
  simp only
  rw [L.xl_add _ _ hz, L.xl_smul _ _ hz, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht,
    one_smul]

/-- **The Maurer–Cartan equation of logarithmic derivatives**:
`d_k(δF(·)(h)) − d_h(δF(·)(k)) = [δF(h), δF(k)]` for a smooth map `F` into a Lie group. -/
theorem logDeriv_maurerCartan (hO : IsOpen O) (hF : SmoothMBMOn X E F O) {p : X} (hp : p ∈ O)
    (h k : X) :
    dMB (fun q ↦ logDeriv E F q h) (p, k) - dMB (fun q ↦ logDeriv E F q k) (p, h) =
      (localGroupLaw E G).bracket (logDeriv E F p h) (logDeriv E F p k) := by
  set φ := chartAt E (1 : G)
  set L := localGroupLaw E G
  set ι := localInverse E G
  set c : X → E := fun r ↦ φ ((F p)⁻¹ * F r)
  set D := relDom E F O p
  have hD : IsOpen D := isOpen_relDom hO hF p
  have hpD : p ∈ D := mem_relDom hp
  have hc : SmoothMBOn c D := smoothMBOn_rel hO hF p
  have hcp : c p = L.one := by
    change φ ((F p)⁻¹ * F p) = φ 1
    rw [inv_mul_cancel]
  -- `Ψ(q, r) = ι(c q) ∗ c r = φ(F(q)⁻¹ F(r))`
  set A := D ∩ c ⁻¹' ι.dom
  have hA : IsOpen A := (hc 0).continuousOn.isOpen_inter_preimage hD ι.isOpen_dom
  set g : X × X → E × E := fun qr ↦ (ι.inv (c qr.1), c qr.2)
  have hg : ContDiffMBOn 2 g (A ×ˢ D) := by
    have h1 : ContDiffMBOn 2 (fun qr : X × X ↦ c qr.1) (A ×ˢ D) :=
      ContDiffMBOn.comp (g := c) (f := fun qr : X × X ↦ qr.1) (hA.prod hD) hD (hc 2)
        (((ContinuousLinearMap.fst ℝ X X).contDiffMBOn 2 univ).mono (subset_univ _))
        fun qr hqr ↦ hqr.1.1
    have h2 : ContDiffMBOn 2 (fun qr : X × X ↦ c qr.2) (A ×ˢ D) :=
      ContDiffMBOn.comp (g := c) (f := fun qr : X × X ↦ qr.2) (hA.prod hD) hD (hc 2)
        (((ContinuousLinearMap.snd ℝ X X).contDiffMBOn 2 univ).mono (subset_univ _))
        fun qr hqr ↦ hqr.2
    exact (ContDiffMBOn.comp (g := ι.inv) (f := fun qr : X × X ↦ c qr.1) (hA.prod hD)
      ι.isOpen_dom ι.contDiffMBOn h1
      fun qr hqr ↦ hqr.1.2).prodMk (hA.prod hD) h2
  set W := A ×ˢ D ∩ g ⁻¹' L.dom
  have hW : IsOpen W := hg.continuousOn.isOpen_inter_preimage (hA.prod hD) L.isOpen_dom
  set Ψ : X × X → E := fun qr ↦ L.mul (g qr)
  have hΨ : ContDiffMBOn 2 Ψ W :=
    ContDiffMBOn.comp hW L.isOpen_dom (L.smooth 2) (hg.mono inter_subset_left)
      fun qr hqr ↦ hqr.2
  have hΨeq : ∀ q ∈ A, ∀ r ∈ D, φ ((F q)⁻¹ * F r) = Ψ (q, r) := by
    intro q hq r hr
    have hq1 : φ.symm (c q) = (F p)⁻¹ * F q := φ.left_inv hq.1.2
    have hq2 : ((F p)⁻¹ * F q)⁻¹ ∈ φ.source := by
      have := hq.2.2.2; rw [← hq1]; exact this
    have hr1 : φ.symm (c r) = (F p)⁻¹ * F r := φ.left_inv hr.2
    change φ ((F q)⁻¹ * F r) = φ (φ.symm (φ (φ.symm (c q))⁻¹) * φ.symm (c r))
    rw [hq1, φ.left_inv hq2, hr1]
    group
  -- `δF(q)(h) = d₂Ψ((q, q), h)`
  have hV : ∀ q, (q, q) ∈ W → ∀ h, logDeriv E F q h = dMB Ψ ((q, q), (0, h)) := by
    intro q hq h
    rw [dMB_slice₂]
    refine dMB_congr_of_eventuallyEq ?_ h
    filter_upwards [hD.mem_nhds hq.1.2] with r hr
    exact hΨeq q hq.1.1 r hr
  -- `dc(q)(h) = (δF(q)(h))~_l(c q)`
  have hR : ∀ q, (q, q) ∈ W → c q ∈ L.domR → ∀ h,
      dMB c (q, h) = L.xl (logDeriv E F q h) (c q) := by
    intro q hq hqR h
    have hqD' : q ∈ relDom E F O q := mem_relDom hq.1.2.1
    have hΦ := (smoothMBOn_rel hO hF q 1).hasDirDerivAt hqD' h
    have hΦq : φ ((F q)⁻¹ * F q) = L.one := by
      change φ ((F q)⁻¹ * F q) = φ 1
      rw [inv_mul_cancel]
    have hgd : HasDirDerivAt (fun r ↦ (c q, φ ((F q)⁻¹ * F r))) q h (0, logDeriv E F q h) :=
      (show HasDirDerivAt (fun _ : X ↦ c q) q h 0 by
        simp only [HasDirDerivAt, sub_self, smul_zero]; exact tendsto_const_nhds).prodMk hΦ
    have hmem : (c q, φ ((F q)⁻¹ * F q)) ∈ L.dom := by rw [hΦq]; exact hqR
    have hcomp := (L.smooth 1).hasDirDerivAt_comp L.isOpen_dom hgd hmem
    rw [hΦq] at hcomp
    refine (hcomp.congr_of_eventuallyEq ?_).dMB_eq
    filter_upwards [(hD.inter (isOpen_relDom hO hF q)).mem_nhds ⟨hq.1.2, hqD'⟩] with r hr
    change φ (φ.symm (c q) * φ.symm (φ ((F q)⁻¹ * F r))) = φ ((F p)⁻¹ * F r)
    rw [φ.left_inv hq.1.1.1.2, φ.left_inv hr.2.2]
    group
  -- the neighborhood `N` of `p`
  have hdiag : Continuous fun q : X ↦ (q, q) := continuous_id.prodMk continuous_id
  set N := {q : X | (q, q) ∈ W} ∩ (D ∩ c ⁻¹' L.domR)
  have hN : IsOpen N :=
    (hW.preimage hdiag).inter ((hc 0).continuousOn.isOpen_inter_preimage hD L.isOpen_domR)
  have hpW : (p, p) ∈ W := by
    have hpA : p ∈ A := ⟨hpD, by change c p ∈ ι.dom; rw [hcp]; exact ι.one_mem⟩
    refine ⟨⟨hpA, hpD⟩, ?_⟩
    change (ι.inv (c p), c p) ∈ L.dom
    have hι1 : ι.inv L.one = L.one := by
      change φ (φ.symm (φ 1))⁻¹ = φ 1
      rw [φ.left_inv (mem_chart_source E (1 : G)), inv_one]
    rw [hcp, hι1]
    exact L.one_one_mem
  have hpN : p ∈ N := ⟨hpW, hpD, by change c p ∈ L.domR; rw [hcp]; exact L.one_mem_domR⟩
  -- `q ↦ δF(q)(h)` is `C¹` near `p`
  have hVs : ∀ h, ContDiffMBOn 1 (fun q ↦ dMB Ψ ((q, q), (0, h))) N := fun h ↦ by
    have hin : ContDiffMBOn 1 (fun q : X ↦ (((q, q), ((0 : X), h)) : (X × X) × (X × X))) N :=
      ((smoothMBOn_id _ 1).prodMk hN (smoothMBOn_id _ 1)).prodMk hN (contDiffMBOn_const 1 _ _)
    exact ContDiffMBOn.comp (g := dMB Ψ) hN (hW.prod isOpen_univ) hΨ.2.2 hin
      fun q hq ↦ ⟨hq.1, mem_univ _⟩
  have hVev : ∀ h, (fun q ↦ logDeriv E F q h) =ᶠ[𝓝 p] fun q ↦ dMB Ψ ((q, q), (0, h)) :=
    fun h ↦ by
      filter_upwards [hN.mem_nhds hpN] with q hq
      exact hV q hq.1 h
  -- `x̃_l(z)` as a function of `(x, z)`
  set Xl : E × E → E := fun xz ↦ L.xl xz.1 xz.2
  have hXl : ContDiffMBOn 1 Xl (univ ×ˢ L.domR) := by
    have hin : ContDiffMBOn 1 (fun xz : E × E ↦ (((xz.2, L.one), ((0 : E), xz.1)) :
        (E × E) × (E × E))) (univ ×ˢ L.domR) := by
      have hs : ContDiffMBOn 1 (fun xz : E × E ↦ xz.2) (univ ×ˢ L.domR) :=
        ((ContinuousLinearMap.snd ℝ E E).contDiffMBOn 1 univ).mono (subset_univ _)
      have hf : ContDiffMBOn 1 (fun xz : E × E ↦ xz.1) (univ ×ˢ L.domR) :=
        ((ContinuousLinearMap.fst ℝ E E).contDiffMBOn 1 univ).mono (subset_univ _)
      exact (hs.prodMk (isOpen_univ.prod L.isOpen_domR) (contDiffMBOn_const 1 _ _)).prodMk
        (isOpen_univ.prod L.isOpen_domR)
        ((contDiffMBOn_const 1 (0 : E) _).prodMk (isOpen_univ.prod L.isOpen_domR) hf)
    exact ContDiffMBOn.comp (g := dMB L.mul) (isOpen_univ.prod L.isOpen_domR)
      (L.isOpen_dom.prod isOpen_univ) (L.smooth 2).2.2 hin fun xz hxz ↦ ⟨hxz.2, mem_univ _⟩
  -- differentiating `dc(q)(h) = (δF(q)(h))~_l(c q)` at `p`
  have key : ∀ h k, dMB (fun q ↦ dMB c (q, h)) (p, k) =
      dMB (fun q ↦ logDeriv E F q h) (p, k) +
        dMB (L.xl (logDeriv E F p h)) (L.one, logDeriv E F p k) := by
    intro h k
    have hev : (fun q ↦ dMB c (q, h)) =ᶠ[𝓝 p]
        Xl ∘ fun q ↦ (dMB Ψ ((q, q), (0, h)), c q) := by
      filter_upwards [hN.mem_nhds hpN] with q hq
      change dMB c (q, h) = L.xl (dMB Ψ ((q, q), (0, h))) (c q)
      rw [← hV q hq.1 h]
      exact hR q hq.1 hq.2.2 h
    have hVd := (hVs h).hasDirDerivAt hpN k
    have hcd := (hc 1).hasDirDerivAt hpD k
    have hcomp := hXl.hasDirDerivAt_comp (isOpen_univ.prod L.isOpen_domR) (hVd.prodMk hcd)
      ⟨mem_univ _, by change c p ∈ L.domR; rw [hcp]; exact L.one_mem_domR⟩
    have hpR : c p ∈ L.domR := by rw [hcp]; exact L.one_mem_domR
    set x0 := dMB Ψ ((p, p), ((0 : X), h))
    set a := dMB (fun q ↦ dMB Ψ ((q, q), ((0 : X), h))) (p, k)
    have e1 : dMB Xl ((x0, c p), (a, 0)) = a := by
      rw [dMB_slice]
      refine ((LocalGroupLaw.hasDirDerivAt_xl_left L hpR x0 a).dMB_eq).trans ?_
      rw [hcp]; exact L.xl_one a
    have e2 : ∀ b, dMB Xl ((x0, c p), (0, b)) = dMB (L.xl x0) (L.one, b) := fun b ↦ by
      rw [dMB_slice₂, hcp]
    have e3 : dMB c (p, k) = logDeriv E F p k := by
      rw [hR p hpW hpR k, hcp, L.xl_one]
    rw [dMB_congr_of_eventuallyEq hev, hcomp.dMB_eq,
      show (a, dMB c (p, k)) = (a, (0 : E)) + ((0 : E), dMB c (p, k)) by simp,
      hXl.dMB_add (isOpen_univ.prod L.isOpen_domR) ⟨mem_univ _, hpR⟩, e1, e2,
      dMB_congr_of_eventuallyEq (hVev h), e3, hV p hpW h]
  have hsw := dMB_dMB_swap hD (hc 2) hpD h k
  rw [key h k, key k h] at hsw
  rw [L.bracket_eq]
  rw [← sub_eq_zero] at hsw ⊢
  rw [← hsw]
  abel

/-- **Logarithmic derivatives of smooth maps are `C¹`**, jointly in the base point and the
direction. -/
theorem contDiffMBOn_logDeriv₂ (hO : IsOpen O) (hF : SmoothMBMOn X E F O) :
    ContDiffMBOn 1 (fun qk : X × X ↦ logDeriv E F qk.1 qk.2) (O ×ˢ univ) := by
  refine ContDiffMBOn.of_local (hO.prod isOpen_univ) fun pk hpk ↦ ?_
  obtain ⟨p, k₀⟩ := pk
  have hp : p ∈ O := hpk.1
  set φ := chartAt E (1 : G)
  set L := localGroupLaw E G
  set ι := localInverse E G
  set c : X → E := fun r ↦ φ ((F p)⁻¹ * F r)
  set D := relDom E F O p
  have hD : IsOpen D := isOpen_relDom hO hF p
  have hpD : p ∈ D := mem_relDom hp
  have hc : SmoothMBOn c D := smoothMBOn_rel hO hF p
  have hcp : c p = L.one := by
    change φ ((F p)⁻¹ * F p) = φ 1
    rw [inv_mul_cancel]
  set A := D ∩ c ⁻¹' ι.dom
  have hA : IsOpen A := (hc 0).continuousOn.isOpen_inter_preimage hD ι.isOpen_dom
  set g : X × X → E × E := fun qr ↦ (ι.inv (c qr.1), c qr.2)
  have hg : ContDiffMBOn 2 g (A ×ˢ D) := by
    have h1 : ContDiffMBOn 2 (fun qr : X × X ↦ c qr.1) (A ×ˢ D) :=
      ContDiffMBOn.comp (g := c) (f := fun qr : X × X ↦ qr.1) (hA.prod hD) hD (hc 2)
        (((ContinuousLinearMap.fst ℝ X X).contDiffMBOn 2 univ).mono (subset_univ _))
        fun qr hqr ↦ hqr.1.1
    have h2 : ContDiffMBOn 2 (fun qr : X × X ↦ c qr.2) (A ×ˢ D) :=
      ContDiffMBOn.comp (g := c) (f := fun qr : X × X ↦ qr.2) (hA.prod hD) hD (hc 2)
        (((ContinuousLinearMap.snd ℝ X X).contDiffMBOn 2 univ).mono (subset_univ _))
        fun qr hqr ↦ hqr.2
    exact (ContDiffMBOn.comp (g := ι.inv) (f := fun qr : X × X ↦ c qr.1) (hA.prod hD)
      ι.isOpen_dom ι.contDiffMBOn h1 fun qr hqr ↦ hqr.1.2).prodMk (hA.prod hD) h2
  set W := A ×ˢ D ∩ g ⁻¹' L.dom
  have hW : IsOpen W := hg.continuousOn.isOpen_inter_preimage (hA.prod hD) L.isOpen_dom
  set Ψ : X × X → E := fun qr ↦ L.mul (g qr)
  have hΨ : ContDiffMBOn 2 Ψ W :=
    ContDiffMBOn.comp hW L.isOpen_dom (L.smooth 2) (hg.mono inter_subset_left)
      fun qr hqr ↦ hqr.2
  have hΨeq : ∀ q ∈ A, ∀ r ∈ D, φ ((F q)⁻¹ * F r) = Ψ (q, r) := by
    intro q hq r hr
    have hq1 : φ.symm (c q) = (F p)⁻¹ * F q := φ.left_inv hq.1.2
    have hq2 : ((F p)⁻¹ * F q)⁻¹ ∈ φ.source := by
      have := hq.2.2.2; rw [← hq1]; exact this
    have hr1 : φ.symm (c r) = (F p)⁻¹ * F r := φ.left_inv hr.2
    change φ ((F q)⁻¹ * F r) = φ (φ.symm (φ (φ.symm (c q))⁻¹) * φ.symm (c r))
    rw [hq1, φ.left_inv hq2, hr1]
    group
  have hdiag : Continuous fun q : X ↦ (q, q) := continuous_id.prodMk continuous_id
  set N := {q : X | (q, q) ∈ W}
  have hN : IsOpen N := hW.preimage hdiag
  have hpN : p ∈ N := by
    have hpA : p ∈ A := ⟨hpD, by change c p ∈ ι.dom; rw [hcp]; exact ι.one_mem⟩
    refine ⟨⟨hpA, hpD⟩, ?_⟩
    change (ι.inv (c p), c p) ∈ L.dom
    have hι1 : ι.inv L.one = L.one := by
      change φ (φ.symm (φ 1))⁻¹ = φ 1
      rw [φ.left_inv (mem_chart_source E (1 : G)), inv_one]
    rw [hcp, hι1]
    exact L.one_one_mem
  have hNu : IsOpen (N ×ˢ (univ : Set X)) := hN.prod isOpen_univ
  have hin : ContDiffMBOn 1 (fun qk : X × X ↦ (((qk.1, qk.1), ((0 : X), qk.2)) :
      (X × X) × (X × X))) (N ×ˢ univ) := by
    have h1 : ContDiffMBOn 1 (fun qk : X × X ↦ qk.1) (N ×ˢ univ) :=
      ((ContinuousLinearMap.fst ℝ X X).contDiffMBOn 1 univ).mono (subset_univ _)
    have h2 : ContDiffMBOn 1 (fun qk : X × X ↦ qk.2) (N ×ˢ univ) :=
      ((ContinuousLinearMap.snd ℝ X X).contDiffMBOn 1 univ).mono (subset_univ _)
    exact (h1.prodMk hNu h1).prodMk hNu ((contDiffMBOn_const 1 (0 : X) _).prodMk hNu h2)
  have hN1 : ContDiffMBOn 1 (fun qk : X × X ↦ logDeriv E F qk.1 qk.2) (N ×ˢ univ) := by
    refine ContDiffMBOn.congr_of_isOpen hNu (fun qk hqk ↦ ?_)
      (ContDiffMBOn.comp (g := dMB Ψ) hNu (hW.prod isOpen_univ) hΨ.2.2 hin
        fun qk hqk ↦ ⟨hqk.1, mem_univ _⟩)
    obtain ⟨q, h⟩ := qk
    change dMB Ψ ((q, q), (0, h)) = logDeriv E F q h
    rw [dMB_slice₂]
    refine (dMB_congr_of_eventuallyEq ?_ h).symm
    filter_upwards [hD.mem_nhds hqk.1.1.2] with r hr
    exact hΨeq q hqk.1.1.1 r hr
  exact ⟨N ×ˢ univ, hNu, ⟨hpN, mem_univ _⟩, hN1.mono inter_subset_right⟩

/-- **Logarithmic derivatives of smooth maps are `C¹`** in the base point. -/
theorem contDiffMBOn_logDeriv (hO : IsOpen O) (hF : SmoothMBMOn X E F O) (h : X) :
    ContDiffMBOn 1 (fun q ↦ logDeriv E F q h) O := by
  have hin : ContDiffMBOn 1 (fun q : X ↦ (q, h)) O :=
    ((ContinuousLinearMap.id ℝ X).contDiffMBOn 1 O).prodMk hO (contDiffMBOn_const 1 h _)
  have h1 := ContDiffMBOn.comp (g := fun qk : X × X ↦ logDeriv E F qk.1 qk.2)
    (f := fun q : X ↦ (q, h)) hO (hO.prod isOpen_univ) (contDiffMBOn_logDeriv₂ hO hF) hin
    fun _ hq ↦ ⟨hq, mem_univ _⟩
  exact h1

theorem logDeriv_add (hO : IsOpen O) (hF : SmoothMBMOn X E F O) {q : X} (hq : q ∈ O) (h k : X) :
    logDeriv E F q (h + k) = logDeriv E F q h + logDeriv E F q k :=
  (smoothMBOn_rel hO hF q 1).dMB_add (isOpen_relDom hO hF q) (mem_relDom hq) h k

theorem logDeriv_smul (hO : IsOpen O) (hF : SmoothMBMOn X E F O) {q : X} (hq : q ∈ O) (c : ℝ)
    (h : X) : logDeriv E F q (c • h) = c • logDeriv E F q h :=
  (smoothMBOn_rel hO hF q 1).dMB_smul (mem_relDom hq) c h

end MBLieGroup

end LocallyConvex.LieGroups
