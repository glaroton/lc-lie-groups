/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.LieGroup.Semidirect

/-!
# The Lie algebra of a semidirect product

`L(N ⋊_α G) ≅ L(N) ⋊_D L(G)`, with the bracket
`[(a, b), (a', b')] = ([a, a'] + D_b a' − D_{b'} a, [b, b'])`, where `D_b a' = ∂_y ∂_x α̃(y, x)` is
the derived action, `α̃` the action in charts ([GN26, Proposition 5.2.8]). For the tangent group
`L(G) ⋊_Ad G`, `D_b = ad b`, so `L(T(G)) ≅ |𝔤| ⋊_ad 𝔤` ([GN26, Example 5.2.12]).

## Main results

* `LocalGroupLaw.b2_semidirect`: if a local group law on `F × E` agrees near the identity with
  `((x, y), (x', y')) ↦ (x ∗ α̃(y, x'), y ∗ y')`, where `α̃(y, 1) = 1` and `α̃(1, x) = x`, then
  `b₂((a, b), (a', b')) = (b₂(a, a') + D_b a', b₂(b, b'))`.
* `LocalGroupLaw.bracket_semidirect`: the corresponding bracket.

## Proof

As in [GN26, Proposition 5.2.8], via the second order terms of Remark 5.1.8: the left invariant
field of `(a', b')` at `(x, y)` is `(dm_N((x, 1), (0, w(y))), ỹ_l(y))` with
`w(y) = ∂_x α̃(y, 1) a'`, whose derivative at the identity in the direction `(a, b)` is
`(b₂(a, a') + dw(1) b, b₂(b, b'))`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups.LocalGroupLaw

universe u

variable {E F : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem hasDirDerivAt_const' {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    (c : F) (p v : X) : HasDirDerivAt (fun _ : X ↦ c) p v 0 := by
  simp only [HasDirDerivAt, sub_self, smul_zero]; exact tendsto_const_nhds

/-- The left invariant fields, jointly in the point and the value at the identity. -/
theorem contDiffMBOn_xl₂ (L : LocalGroupLaw F) (k : ℕ) :
    ContDiffMBOn k (fun p : F × F ↦ L.xl p.2 p.1) (L.domR ×ˢ univ) := by
  have hU : IsOpen (L.domR ×ˢ (univ : Set F)) := L.isOpen_domR.prod isOpen_univ
  have hfst : ContDiffMBOn k (fun p : F × F ↦ p.1) (L.domR ×ˢ univ) :=
    ((ContinuousLinearMap.fst ℝ F F).contDiffMBOn k univ).mono (subset_univ _)
  have hsnd : ContDiffMBOn k (fun p : F × F ↦ p.2) (L.domR ×ˢ univ) :=
    ((ContinuousLinearMap.snd ℝ F F).contDiffMBOn k univ).mono (subset_univ _)
  have hin : ContDiffMBOn k (fun p : F × F ↦ ((p.1, L.one), ((0 : F), p.2))) (L.domR ×ˢ univ) :=
    (hfst.prodMk hU (contDiffMBOn_const k L.one _)).prodMk hU
      ((contDiffMBOn_const k (0 : F) _).prodMk hU hsnd)
  exact ContDiffMBOn.comp (g := dMB L.mul) hU (L.isOpen_dom.prod isOpen_univ)
    (L.smooth (k + 1)).2.2 hin fun _ hz ↦ ⟨hz.1, mem_univ _⟩

variable (LN : LocalGroupLaw F) (LG : LocalGroupLaw E) {α : E × F → F} {D : Set (E × F)}

/-- **The derived action** in charts, `w(y) = ∂_x α̃(y, 1) a'`, so that `D_b a' = dw(1) b`. -/
def derivAct (α : E × F → F) (a' : F) (y : E) : F := dMB α ((y, LN.one), ((0 : E), a'))

/-- **The second order term of a semidirect local group law** ([GN26, Proposition 5.2.8]). -/
theorem b2_semidirect (hD : IsOpen D) (hα : ContDiffMBOn 2 α D) (h1D : (LG.one, LN.one) ∈ D)
    (hαy : ∀ y, α (y, LN.one) = LN.one) (hαx : ∀ᶠ x in 𝓝 LN.one, α (LG.one, x) = x)
    (L : LocalGroupLaw (F × E)) (hone : L.one = (LN.one, LG.one))
    (hmul : L.mul =ᶠ[𝓝 (L.one, L.one)]
      fun q ↦ (LN.mul (q.1.1, α (q.1.2, q.2.1)), LG.mul (q.1.2, q.2.2)))
    (v v' : F × E) :
    L.b2 v v' = (LN.b2 v.1 v'.1 + dMB (derivAct LN α v'.1) (LG.one, v.2), LG.b2 v.2 v'.2) := by
  obtain ⟨a, b⟩ := v
  obtain ⟨a', b'⟩ := v'
  set w := derivAct LN α a' with hw_def
  obtain ⟨W, hWsub, hWo, hW1⟩ := mem_nhds_iff.1 hmul
  -- the open set of points where the left invariant field is computed
  set V : Set (F × E) := {z | (z, L.one) ∈ W ∧ (z.1, LN.one) ∈ LN.dom ∧ (z.2, LN.one) ∈ D ∧
    (z.2, LG.one) ∈ LG.dom}
  have hVo : IsOpen V :=
    (hWo.preimage (by fun_prop)).inter ((LN.isOpen_dom.preimage (by fun_prop)).inter
      ((hD.preimage (by fun_prop)).inter (LG.isOpen_dom.preimage (by fun_prop))))
  have h1V : L.one ∈ V := by
    refine ⟨hW1, ?_, ?_, ?_⟩ <;> rw [hone]
    exacts [LN.one_one_mem, h1D, LG.one_one_mem]
  have hα1 : ContDiffMBOn 1 α D := hα.of_le (by norm_num)
  -- the left invariant field of `(a', b')`
  have hxl : ∀ z ∈ V, L.xl (a', b') z = (LN.xl (w z.2) z.1, LG.xl b' z.2) := by
    intro z hz
    obtain ⟨hzW, hzN, hzD, hzG⟩ := hz
    rw [xl_eq]
    have hev : (fun q : F × E ↦ L.mul (z, q)) =ᶠ[𝓝 L.one]
        fun q ↦ (LN.mul (z.1, α (z.2, q.1)), LG.mul (z.2, q.2)) :=
      eventuallyEq_of_mem ((hWo.preimage (by fun_prop : Continuous fun q : F × E ↦ (z, q))).mem_nhds
        hzW) fun q hq ↦ hWsub hq
    rw [dMB_congr_of_eventuallyEq hev, hone]
    have hfst : HasDirDerivAt (fun q : F × E ↦ q.1) (LN.one, LG.one) (a', b') a' :=
      (ContinuousLinearMap.fst ℝ F E).hasDirDerivAt _ _
    have hsnd : HasDirDerivAt (fun q : F × E ↦ q.2) (LN.one, LG.one) (a', b') b' :=
      (ContinuousLinearMap.snd ℝ F E).hasDirDerivAt _ _
    have hin : HasDirDerivAt (fun q : F × E ↦ (z.2, q.1)) (LN.one, LG.one) (a', b') (0, a') :=
      (hasDirDerivAt_const' z.2 _ _).prodMk hfst
    have hact := hα1.hasDirDerivAt_comp hD hin hzD
    have hN := (LN.smooth 1).hasDirDerivAt_comp LN.isOpen_dom
      ((hasDirDerivAt_const' z.1 _ _).prodMk hact) (by
        change (z.1, α (z.2, LN.one)) ∈ LN.dom
        rw [hαy]; exact hzN)
    have hG := (LG.smooth 1).hasDirDerivAt_comp LG.isOpen_dom
      ((hasDirDerivAt_const' z.2 _ _).prodMk hsnd) hzG
    refine ((hN.prodMk hG).dMB_eq).trans ?_
    change (dMB LN.mul ((z.1, α (z.2, LN.one)), (0, w z.2)), LG.xl b' z.2) = _
    rw [hαy]; rfl
  have hev : L.xl (a', b') =ᶠ[𝓝 L.one] fun z ↦ (LN.xl (w z.2) z.1, LG.xl b' z.2) :=
    eventuallyEq_of_mem (hVo.mem_nhds h1V) hxl
  change dMB (L.xl (a', b')) (L.one, (a, b)) = _
  rw [dMB_congr_of_eventuallyEq hev, hone]
  -- derivatives of the two components
  have hfst : HasDirDerivAt (fun z : F × E ↦ z.1) (LN.one, LG.one) (a, b) a :=
    (ContinuousLinearMap.fst ℝ F E).hasDirDerivAt _ _
  have hsnd : HasDirDerivAt (fun z : F × E ↦ z.2) (LN.one, LG.one) (a, b) b :=
    (ContinuousLinearMap.snd ℝ F E).hasDirDerivAt _ _
  have hG := (LG.contDiffMBOn_xl 1 b').hasDirDerivAt_comp LG.isOpen_domR hsnd LG.one_mem_domR
  -- `w` is `C¹` near `1`
  set Dy : Set E := {y | (y, LN.one) ∈ D}
  have hDy : IsOpen Dy := hD.preimage (by fun_prop)
  have hwC : ContDiffMBOn 1 w Dy := by
    have hin : ContDiffMBOn 1 (fun y : E ↦ ((y, LN.one), ((0 : E), a'))) Dy :=
      ((smoothMBOn_id _ 1).prodMk hDy (contDiffMBOn_const 1 LN.one _)).prodMk hDy
        (contDiffMBOn_const 1 ((0 : E), a') _)
    exact ContDiffMBOn.comp (g := dMB α) hDy (hD.prod isOpen_univ) hα.2.2 hin
      fun _ hy ↦ ⟨hy, mem_univ _⟩
  have hw := hwC.hasDirDerivAt_comp hDy hsnd h1D
  have hΨ := (contDiffMBOn_xl₂ LN 1).hasDirDerivAt_comp (LN.isOpen_domR.prod isOpen_univ)
    (hfst.prodMk hw) ⟨LN.one_mem_domR, mem_univ _⟩
  refine ((hΨ.prodMk hG).dMB_eq).trans ?_
  -- `w(1) = a'`
  have hw1 : w LG.one = a' := by
    change dMB α ((LG.one, LN.one), ((0 : E), a')) = a'
    rw [dMB_slice₂]
    have h : (fun x ↦ α (LG.one, x)) =ᶠ[𝓝 LN.one] fun x ↦ (ContinuousLinearMap.id ℝ F) x := hαx
    rw [dMB_congr_of_eventuallyEq h, ((ContinuousLinearMap.id ℝ F).hasDirDerivAt _ _).dMB_eq]
    rfl
  change (dMB (fun p : F × F ↦ LN.xl p.2 p.1) ((LN.one, w LG.one), (a, dMB w (LG.one, b))),
    dMB (LG.xl b') (LG.one, b)) = _
  rw [hw1]
  have hsplit : (a, dMB w (LG.one, b)) = (a, (0 : F)) + ((0 : F), dMB w (LG.one, b)) := by
    simp
  rw [hsplit, (contDiffMBOn_xl₂ LN 1).dMB_add (LN.isOpen_domR.prod isOpen_univ)
    ⟨LN.one_mem_domR, mem_univ _⟩, dMB_slice, dMB_slice₂]
  have hone' : (fun u : F ↦ LN.xl u LN.one) = fun u ↦ (ContinuousLinearMap.id ℝ F) u :=
    funext fun u ↦ LN.xl_one u
  rw [hone', ((ContinuousLinearMap.id ℝ F).hasDirDerivAt _ _).dMB_eq]
  rfl

/-- **The bracket of a semidirect local group law** ([GN26, Proposition 5.2.8]):
`[(a, b), (a', b')] = ([a, a'] + D_b a' − D_{b'} a, [b, b'])`. -/
theorem bracket_semidirect (hD : IsOpen D) (hα : ContDiffMBOn 2 α D) (h1D : (LG.one, LN.one) ∈ D)
    (hαy : ∀ y, α (y, LN.one) = LN.one) (hαx : ∀ᶠ x in 𝓝 LN.one, α (LG.one, x) = x)
    (L : LocalGroupLaw (F × E)) (hone : L.one = (LN.one, LG.one))
    (hmul : L.mul =ᶠ[𝓝 (L.one, L.one)]
      fun q ↦ (LN.mul (q.1.1, α (q.1.2, q.2.1)), LG.mul (q.1.2, q.2.2)))
    (v v' : F × E) :
    L.bracket v v' = (LN.bracket v.1 v'.1 + dMB (derivAct LN α v'.1) (LG.one, v.2) -
      dMB (derivAct LN α v.1) (LG.one, v'.2), LG.bracket v.2 v'.2) := by
  rw [bracket_eq_b2_sub_b2, b2_semidirect LN LG hD hα h1D hαy hαx L hone hmul,
    b2_semidirect LN LG hD hα h1D hαy hαx L hone hmul, bracket_eq_b2_sub_b2,
    bracket_eq_b2_sub_b2]
  ext
  · simp only [Prod.fst_sub]; abel
  · rfl

end LocallyConvex.LieGroups.LocalGroupLaw

/-! ### The Lie algebra of `N ⋊_α G` -/

namespace LocallyConvex.LieGroups.SDProd

universe u

variable {E F : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]
  {N : Type*} [Group N] [TopologicalSpace N] [ChartedSpace F N] [MBLieGroup F N]
  (α : G →* MulAut N)

/-- The action `(g, n) ↦ α(g)(n)`. -/
def actMap (q : G × N) : N := α q.1 q.2

omit [TopologicalSpace G] [TopologicalSpace N] in
theorem actMap_one : actMap α ((1 : G), (1 : N)) = 1 := map_one _

variable (E F) in
/-- **The action in the charts at the identity**, `α̃(y, x) = φ_N(α(φ_G⁻¹ y)(φ_N⁻¹ x))`. -/
def actRep (q : E × F) : F :=
  chartAt F (1 : N) (α ((chartAt E (1 : G)).symm q.1) ((chartAt F (1 : N)).symm q.2))

variable (E F) in
/-- The domain of `actRep`. -/
def actRepDom : Set (E × F) :=
  chartDomain (actMap α) univ (chartAt (ModelProd E F) ((1 : G), (1 : N))) (chartAt F (1 : N))

variable {α}

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [MBLieGroup E G] [MBLieGroup F N] in
theorem smoothMBOn_actRep (hα : IsSmoothAction E F α) :
    SmoothMBOn (actRep E F α) (actRepDom E F α) := by
  intro k
  have h : ContMDiffMBOn (E := ModelProd E F) (F := F) k (actMap α) univ := hα k
  have h' := h.2 ((1 : G), (1 : N)) (mem_univ _)
  rw [actMap_one] at h'
  exact h'

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [MBLieGroup E G] [MBLieGroup F N] in
theorem isOpen_actRepDom (hα : IsSmoothAction E F α) : IsOpen (actRepDom E F α) :=
  isOpen_chartDomain isOpen_univ (hα 0).1 _ _

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [MBLieGroup E G]
  [AddCommGroup F] [Module ℝ F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] [T2Space F] [MBLieGroup F N] in
theorem one_mem_actRepDom :
    (chartAt E (1 : G) 1, chartAt F (1 : N) 1) ∈ actRepDom E F α := by
  have hG := mem_chart_source E (1 : G)
  have hN := mem_chart_source F (1 : N)
  refine ⟨⟨(chartAt E (1 : G)).map_source hG, (chartAt F (1 : N)).map_source hN⟩, mem_univ _, ?_⟩
  change actMap α ((chartAt E (1 : G)).symm (chartAt E (1 : G) 1),
    (chartAt F (1 : N)).symm (chartAt F (1 : N) 1)) ∈ (chartAt F (1 : N)).source
  rw [(chartAt E (1 : G)).left_inv hG, (chartAt F (1 : N)).left_inv hN, actMap_one]
  exact hN

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [MBLieGroup E G]
  [AddCommGroup F] [Module ℝ F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] [T2Space F] [MBLieGroup F N] in
theorem actRep_one_right (y : E) : actRep E F α (y, chartAt F (1 : N) 1) = chartAt F (1 : N) 1 := by
  simp only [actRep, (chartAt F (1 : N)).left_inv (mem_chart_source F (1 : N)), map_one]

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [MBLieGroup E G]
  [AddCommGroup F] [Module ℝ F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] [T2Space F] [MBLieGroup F N] in
theorem actRep_one_left :
    ∀ᶠ x in 𝓝 (chartAt F (1 : N) 1), actRep E F α (chartAt E (1 : G) 1, x) = x := by
  filter_upwards [(chartAt F (1 : N)).open_target.mem_nhds
    ((chartAt F (1 : N)).map_source (mem_chart_source F (1 : N)))] with x hx
  simp only [actRep, (chartAt E (1 : G)).left_inv (mem_chart_source E (1 : G)), map_one,
    MulAut.one_apply, (chartAt F (1 : N)).right_inv hx]

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [AddCommGroup F] [Module ℝ F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- The multiplication of `N ⋊_α G` in the chart at the identity. -/
theorem chartMul_eq (q : (F × E) × (F × E)) :
    MBLieGroup.chartMul (ModelProd F E) (SDProd α) q =
      (chartAt F (1 : N) ((chartAt F (1 : N)).symm q.1.1 *
        α ((chartAt E (1 : G)).symm q.1.2) ((chartAt F (1 : N)).symm q.2.1)),
       chartAt E (1 : G) ((chartAt E (1 : G)).symm q.1.2 * (chartAt E (1 : G)).symm q.2.2)) :=
  rfl

variable (α) in
/-- **The derived action** `D_b a = dw_a(1) b` of `L(G)` on `L(N)`, where
`w_a(y) = ∂_x α̃(y, 1) a`. -/
def derivedAction (b : E) (a : F) : F :=
  dMB (LocalGroupLaw.derivAct (MBLieGroup.localGroupLaw F N) (actRep E F α) a)
    (chartAt E (1 : G) 1, b)

variable [MBLieGroup (ModelProd F E) (SDProd α)] (hα : IsSmoothAction E F α)
include hα

/-- The multiplication of `N ⋊_α G` in the chart at the identity is semidirect near `(1, 1)`. -/
theorem localGroupLaw_mul_eventuallyEq :
    (MBLieGroup.localGroupLaw (ModelProd F E) (SDProd α)).mul =ᶠ[𝓝
      ((MBLieGroup.localGroupLaw (ModelProd F E) (SDProd α)).one,
        (MBLieGroup.localGroupLaw (ModelProd F E) (SDProd α)).one)]
      fun q : (F × E) × (F × E) ↦
        ((MBLieGroup.localGroupLaw F N).mul (q.1.1, actRep E F α (q.1.2, q.2.1)),
          (MBLieGroup.localGroupLaw E G).mul (q.1.2, q.2.2)) := by
  have hW : IsOpen {q : (F × E) × (F × E) | (q.1.2, q.2.1) ∈ actRepDom E F α} :=
    (isOpen_actRepDom hα).preimage (by fun_prop)
  refine eventuallyEq_of_mem (hW.mem_nhds one_mem_actRepDom) fun q hq ↦ ?_
  obtain ⟨-, -, hsrc⟩ := hq
  change MBLieGroup.chartMul (ModelProd F E) (SDProd α) q = _
  rw [chartMul_eq]
  have hsrc' : α ((chartAt E (1 : G)).symm q.1.2) ((chartAt F (1 : N)).symm q.2.1) ∈
      (chartAt F (1 : N)).source := hsrc
  change _ = (chartAt F (1 : N) ((chartAt F (1 : N)).symm q.1.1 *
    (chartAt F (1 : N)).symm (chartAt F (1 : N)
      (α ((chartAt E (1 : G)).symm q.1.2) ((chartAt F (1 : N)).symm q.2.1)))), _)
  rw [(chartAt F (1 : N)).left_inv hsrc']
  rfl

/-- **The Lie algebra of a semidirect product** ([GN26, Proposition 5.2.8]):
`L(N ⋊_α G) ≅ L(N) ⋊_D L(G)`, i.e.
`[(a, b), (a', b')] = ([a, a'] + D_b a' − D_{b'} a, [b, b'])`. -/
theorem bracket_eq (v v' : F × E) :
    (MBLieGroup.localGroupLaw (ModelProd F E) (SDProd α)).bracket v v' =
      ((MBLieGroup.localGroupLaw F N).bracket v.1 v'.1 + derivedAction α v.2 v'.1 -
        derivedAction α v'.2 v.1, (MBLieGroup.localGroupLaw E G).bracket v.2 v'.2) :=
  LocalGroupLaw.bracket_semidirect (MBLieGroup.localGroupLaw F N) (MBLieGroup.localGroupLaw E G)
    (isOpen_actRepDom hα) (smoothMBOn_actRep hα 2) one_mem_actRepDom actRep_one_right
    actRep_one_left _ rfl (localGroupLaw_mul_eventuallyEq hα) v v'

end LocallyConvex.LieGroups.SDProd

/-! ### The Lie algebra of the tangent group `L(G) ⋊_Ad G` -/

namespace LocallyConvex.LieGroups.MBLieGroup

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]

/-- For the adjoint action, `w_a(y) = Ad(φ⁻¹ y) a`. -/
theorem TangentGroup.derivAct_eq (a y : E) :
    LocalGroupLaw.derivAct (localGroupLaw E (Multiplicative E))
      (SDProd.actRep E E (AdMulAut E G)) a y = AdCLM ((chartAt E (1 : G)).symm y) a := by
  unfold LocalGroupLaw.derivAct
  rw [dMB_slice₂]
  have h : (fun x ↦ SDProd.actRep E E (AdMulAut E G) (y, x)) =
      ⇑(AdCLM ((chartAt E (1 : G)).symm y)) := rfl
  rw [h, ((AdCLM _).hasDirDerivAt _ _).dMB_eq]

/-- **The derived action of the adjoint action is `ad`** ([GN26, Example 5.2.12]):
`D_b a = [b, a]`. -/
theorem TangentGroup.derivedAction_eq (b a : E) :
    SDProd.derivedAction (AdMulAut E G) b a =
      (localGroupLaw E G).bracket b a := by
  unfold SDProd.derivedAction
  rw [funext (TangentGroup.derivAct_eq (G := G) a)]
  exact dMB_Ad (E := E) (G := G) (LieAlg.toModel.symm b) (LieAlg.toModel.symm a)

/-- **The Lie algebra of the tangent group is `|𝔤| ⋊_ad 𝔤`** ([GN26, Example 5.2.12]):
`[(a, b), (a', b')] = ([b, a'] − [b', a], [b, b'])`. -/
theorem TangentGroup.bracket_eq (v v' : E × E) :
    (localGroupLaw (ModelProd E E) (TangentGroup E G)).bracket v v' =
      ((localGroupLaw E G).bracket v.2 v'.1 - (localGroupLaw E G).bracket v'.2 v.1,
        (localGroupLaw E G).bracket v.2 v'.2) := by
  rw [SDProd.bracket_eq isSmoothAction_AdMulAut, TangentGroup.derivedAction_eq,
    TangentGroup.derivedAction_eq]
  have h0 : (localGroupLaw E (Multiplicative E)).bracket v.1 v'.1 = 0 :=
    VectorGroup.lie_eq_zero E v.1 v'.1
  rw [h0, zero_add]

end LocallyConvex.LieGroups.MBLieGroup
