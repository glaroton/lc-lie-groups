/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.LieAlgebra.LeftInvariant
public import LocallyConvexManifolds.Metric.FinslerMaps
public import LocallyConvexManifolds.Metric.FinslerTopology

/-!
# Left invariant Finsler metrics

A Finsler seminorm `|·|` on the Lie algebra `L(G)` defines a **left invariant Finsler metric** on
the Lie group `G` by `|v|_g = |g⁻¹ v|`, where `g⁻¹ v = T_g(λ_{g⁻¹}) v ∈ T_1 G = L(G)`
([Lar19, Remark 2.5]). It is continuous on the tangent bundle, every left translation is an
isometry for the induced distance, and every left invariant Finsler metric arises in this way.

The Lie algebra `L(G)` is the model space `E` read in the chart at the identity
(`LieAlgebra/Basic.lean`), so a Finsler seminorm on `L(G)` is a `FinslerSeminorm E`, and
`g⁻¹ v` is the **left trivialization** `leftTriv E p ∈ E` of `p = (g, v) ∈ TG`.

## Main definitions

* `MBLieGroup.leftTriv`: the left trivialization `TG → L(G)`, `(g, v) ↦ g⁻¹ v`.
* `MBLieGroup.leftFinsler`: the left invariant Finsler metric `|v|_g = |g⁻¹ v|` defined by a
  Finsler seminorm on `L(G)` ([Lar19, Remark 2.5]).

## Main results

* `MBLieGroup.continuous_leftTriv`: the left trivialization is continuous on `TG`. This is what
  makes `leftFinsler` continuous on the tangent bundle, a Finsler metric and not only a Finsler
  length structure. In charts, `g⁻¹ v` is the partial derivative of `(a, b) ↦ a⁻¹ b` at `(g, g)`,
  which is continuous because the group operations are `C¹` on `G × G`.
* `MBLieGroup.leftTriv_tangentMap_mul_left`: `(h g)⁻¹ (h v) = g⁻¹ v`.
* `MBLieGroup.leftTriv_leftField`: `g⁻¹ x_l(g) = x`.
* `MBLieGroup.leftFinsler_tangentMap_mul_left`: `leftFinsler` is left invariant.
* `MBLieGroup.length_mul_left`, `MBLieGroup.dist_mul_left`: left translations preserve lengths
  and distances ([Lar19, Prop. 2.10(3)] with `L ≡ 1`).
* `MBLieGroup.eq_leftFinsler`: every left invariant field of Finsler seminorms is
  `leftFinsler` of its value at the identity ([Lar19, Remark 2.5]).
* `MBLieGroup.leftFinsler_isReversible`, `MBLieGroup.leftFinsler_isNondegenerate`: the metric is
  reversible, resp. nondegenerate, exactly when the seminorm on `L(G)` is.

## References

* [G. Larotonda, *The metric geometry of infinite dimensional Lie groups and their homogeneous
  spaces*][Lar19]
-/

@[expose] public section

open Set Filter Bundle
open scoped Topology
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups.MBLieGroup

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]

/-! ### The left trivialization `TG → L(G)` -/

variable (E) in
/-- **The left trivialization** `(g, v) ↦ g⁻¹ v = T_g(λ_{g⁻¹}) v ∈ L(G)`, in the preferred chart
at `g` and the chart at the identity. -/
def leftTriv (p : TangentBundle E G) : E :=
  dMB (chartAt E (1 : G) ∘ (fun h ↦ p.proj⁻¹ * h) ∘ (chartAt E p.proj).symm)
    (chartAt E p.proj p.proj, (p.2 : E))

/-- `T_g(λ_{g⁻¹}) v = (1, g⁻¹ v)`: the left trivialization is the tangent map of `λ_{g⁻¹}`. -/
theorem tangentMap_inv_mul (p : TangentBundle E G) :
    tangentMap E E (fun h ↦ p.proj⁻¹ * h) p = ⟨1, leftTriv E p⟩ := by
  have key : ∀ a : G, a = 1 → (⟨a, (dMB (chartAt E a ∘ (fun h ↦ p.proj⁻¹ * h) ∘
      (chartAt E p.proj).symm) (chartAt E p.proj p.proj, (p.2 : E)) : E)⟩ : TangentBundle E G) =
      ⟨1, leftTriv E p⟩ := by
    rintro a rfl
    rfl
  exact key _ (inv_mul_cancel _)

/-- The domain on which the local representative of `λ_{g⁻¹}` used by `leftTriv` is `C¹`. -/
theorem contDiffMBOn_leftTrivRep (g : G) :
    ContDiffMBOn 1 (chartAt E (1 : G) ∘ (fun h ↦ g⁻¹ * h) ∘ (chartAt E g).symm)
      (chartDomain (fun h ↦ g⁻¹ * h) univ (chartAt E g) (chartAt E (1 : G))) :=
  ContMDiffMBOn.contDiffMBOn_chart isOpen_univ (smoothMBM_mul_left (E := E) g⁻¹ 1)
    (chart_mem_atlas E g) (chart_mem_atlas E (1 : G))

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [MBLieGroup E G] in
theorem mem_leftTrivDom (g : G) :
    chartAt E g g ∈ chartDomain (fun h ↦ g⁻¹ * h) univ (chartAt E g) (chartAt E (1 : G)) := by
  have hg := mem_chart_source E g
  refine ⟨(chartAt E g).map_source hg, mem_univ _, ?_⟩
  simp [(chartAt E g).left_inv hg, mem_chart_source]

theorem isOpen_leftTrivDom (g : G) :
    IsOpen (chartDomain (fun h ↦ g⁻¹ * h) univ (chartAt E g) (chartAt E (1 : G))) :=
  isOpen_chartDomain isOpen_univ (smoothMBM_mul_left (E := E) g⁻¹ 0).1 _ _

theorem leftTriv_add (g : G) (v w : E) :
    leftTriv E (⟨g, v + w⟩ : TangentBundle E G) =
      leftTriv E (⟨g, v⟩ : TangentBundle E G) + leftTriv E (⟨g, w⟩ : TangentBundle E G) :=
  (contDiffMBOn_leftTrivRep g).dMB_add (isOpen_leftTrivDom g) (mem_leftTrivDom g) v w

theorem leftTriv_smul (g : G) (c : ℝ) (v : E) :
    leftTriv E (⟨g, c • v⟩ : TangentBundle E G) = c • leftTriv E (⟨g, v⟩ : TangentBundle E G) :=
  (contDiffMBOn_leftTrivRep g).dMB_smul (mem_leftTrivDom g) c v

theorem leftTriv_neg (g : G) (v : E) :
    leftTriv E (⟨g, -v⟩ : TangentBundle E G) = -leftTriv E (⟨g, v⟩ : TangentBundle E G) := by
  rw [← neg_one_smul ℝ v, leftTriv_smul, neg_one_smul]

theorem continuous_leftTriv_fiber (g : G) :
    Continuous fun v : E ↦ leftTriv E (⟨g, v⟩ : TangentBundle E G) := by
  have h : ContinuousOn (dMB (chartAt E (1 : G) ∘ (fun h ↦ g⁻¹ * h) ∘ (chartAt E g).symm))
      ((chartDomain (fun h ↦ g⁻¹ * h) univ (chartAt E g) (chartAt E (1 : G))) ×ˢ univ) :=
    (contDiffMBOn_leftTrivRep g).2.2
  have hc : Continuous fun v : E ↦ ((chartAt E g g, v) : E × E) :=
    continuous_const.prodMk continuous_id
  have := h.comp_continuous hc fun v ↦ ⟨mem_leftTrivDom g, mem_univ _⟩
  exact this

/-- **The left trivialization is continuous on `TG`.** Near `p₀ = (g₀, v₀)`, in the chart `ψ` at
`g₀` of `TG`, `g⁻¹ v` is the partial derivative `∂₂F((y, y), (0, w))` of the local representative
`F(a, b) = φ((ψ⁻¹ a)⁻¹ ψ⁻¹ b)` of `(a, b) ↦ a⁻¹ b`, where `(y, w)` are the coordinates of `(g, v)`.
Since `(a, b) ↦ a⁻¹ b` is `C¹` on `G × G`, this is continuous in `(y, w)`. -/
theorem continuous_leftTriv : Continuous (leftTriv E : TangentBundle E G → E) := by
  rw [continuous_iff_continuousAt]
  intro p₀
  set g₀ := p₀.proj
  set ψ := chartAt E g₀
  set φ := chartAt E (1 : G)
  set i : atlas E G := ⟨ψ, chart_mem_atlas E g₀⟩
  set Φ := tangentChart i ψ
  -- the map `(a, b) ↦ a⁻¹ b` on `G × G` and its local representative
  set D : G × G → G := fun q ↦ q.1⁻¹ * q.2
  have hD : SmoothMBM (ModelProd E E) E D :=
    (smoothMBM_mul (E := E) (G := G)).comp fun k ↦ ContMDiffMBOn.prodMk isOpen_univ
      ((smoothMBM_inv (E := E) (G := G)).comp smoothMBM_fst k) (smoothMBM_snd k)
  set e := chartAt (ModelProd E E) (g₀, g₀)
  set Dom := chartDomain D univ e φ
  have hDom : IsOpen Dom := isOpen_chartDomain isOpen_univ (hD 0).1 e φ
  set F : E × E → E := φ ∘ D ∘ e.symm
  have hF : ContDiffMBOn 1 F Dom :=
    ContMDiffMBOn.contDiffMBOn_chart isOpen_univ (hD 1) (chart_mem_atlas _ _)
      (chart_mem_atlas E (1 : G))
  have he : e = ψ.prod ψ := rfl
  -- `(y, y) ∈ Dom` for `y = ψ g`, `g ∈ ψ.source`
  have hdiag : ∀ g ∈ ψ.source, (ψ g, ψ g) ∈ Dom := by
    intro g hg
    refine ⟨?_, mem_univ _, ?_⟩
    · rw [he]; exact ⟨ψ.map_source hg, ψ.map_source hg⟩
    · change (ψ.symm (ψ g))⁻¹ * ψ.symm (ψ g) ∈ φ.source
      rw [ψ.left_inv hg, inv_mul_cancel]
      exact mem_chart_source E (1 : G)
  -- the formula in the chart
  set H : E × E → E := fun q ↦ dMB F ((q.1, q.1), (0, q.2))
  have hform : ∀ p ∈ Φ.source, leftTriv E p = H (Φ p) := by
    intro p hp
    obtain ⟨hpi, -⟩ := (mem_tangentChart_source i ψ p).mp hp
    set g := p.proj
    have h1 : dMB (φ ∘ (fun h ↦ g⁻¹ * h) ∘ ψ.symm)
        (ψ g, dMB (ψ ∘ (chartAt E g).symm) (chartAt E g g, (p.2 : E))) = leftTriv E p :=
      dMB_chart_comp (smoothMBM_mul_left (E := E) g⁻¹ 1) (chart_mem_atlas E g)
        (chart_mem_atlas E g₀) (chart_mem_atlas E (1 : G)) (mem_chart_source E g) hpi
        (by simp [mem_chart_source]) (p.2 : E)
    rw [← h1]
    have key : ∀ g' : G, g' = ψ.symm (ψ g) → ∀ w : E,
        dMB (φ ∘ (fun h ↦ g'⁻¹ * h) ∘ ψ.symm) (ψ g, w) = H (ψ g, w) := by
      rintro g' rfl w
      rw [he] at *
      exact (dMB_slice₂ F (ψ g) (ψ g) w).symm
    exact key g (ψ.left_inv hpi).symm _
  -- continuity of `H` at `Φ p₀`
  have hp₀ : p₀ ∈ Φ.source :=
    (mem_tangentChart_source i ψ p₀).mpr ⟨mem_chart_source E g₀, mem_chart_source E g₀⟩
  have hΦp₀ : (Φ p₀).1 = ψ g₀ := rfl
  have hdF : ContinuousOn (dMB F) (Dom ×ˢ univ) := hF.2.2
  have hH : ContinuousAt H (Φ p₀) := by
    have hmap : Continuous fun q : E × E ↦ (((q.1, q.1), ((0 : E), q.2)) : (E × E) × E × E) := by
      fun_prop
    refine (hdF.continuousAt ?_).comp hmap.continuousAt
    refine (hDom.prod isOpen_univ).mem_nhds ⟨?_, mem_univ _⟩
    rw [hΦp₀]
    exact hdiag g₀ (mem_chart_source E g₀)
  have hev : leftTriv E =ᶠ[𝓝 p₀] H ∘ Φ :=
    eventuallyEq_of_mem (Φ.open_source.mem_nhds hp₀) hform
  exact (hH.comp (Φ.continuousAt hp₀)).congr hev.symm

/-- **Left translations commute with the left trivialization**: `(h g)⁻¹ (h v) = g⁻¹ v`. -/
theorem leftTriv_tangentMap_mul_left (h : G) (p : TangentBundle E G) :
    leftTriv E (tangentMap E E (fun k ↦ h * k) p) = leftTriv E p := by
  set q := tangentMap E E (fun k ↦ h * k) p
  have h1 := tangentMap_inv_mul (E := E) q
  have h2 : tangentMap E E (fun k ↦ q.proj⁻¹ * k) q =
      tangentMap E E (fun k ↦ p.proj⁻¹ * k) p := by
    rw [tangentMap_comp (smoothMBM_mul_left (E := E) q.proj⁻¹ 1)
      (smoothMBM_mul_left (E := E) h 1)]
    congr 1
    funext k
    change (h * p.proj)⁻¹ * (h * k) = p.proj⁻¹ * k
    group
  rw [h2, tangentMap_inv_mul] at h1
  exact (TotalSpace.mk_inj.mp h1).symm

/-- At the identity the left trivialization is the identity: `1⁻¹ w = w`. -/
theorem leftTriv_one (w : E) : leftTriv E (⟨1, w⟩ : TangentBundle E G) = w := by
  set φ := chartAt E (1 : G)
  have h1 : (1 : G) ∈ φ.source := mem_chart_source E (1 : G)
  have hev : (φ ∘ (fun h ↦ (1 : G)⁻¹ * h) ∘ φ.symm) =ᶠ[𝓝 (φ 1)]
      fun b ↦ (ContinuousLinearMap.id ℝ E) b :=
    eventuallyEq_of_mem (φ.open_target.mem_nhds (φ.map_source h1)) fun b hb ↦ by
      simp [φ.right_inv hb]
  exact (dMB_congr_of_eventuallyEq hev w).trans
    ((ContinuousLinearMap.id ℝ E).hasDirDerivAt _ _).dMB_eq

/-- **`g⁻¹ x_l(g) = x`**: the left trivialization of a left invariant vector field is its value
at the identity. -/
theorem leftTriv_leftField (x : LieAlg E G) (g : G) : leftTriv E (leftField E x g) = x := by
  rw [leftField_eq_tangentMap, leftTriv_tangentMap_mul_left]
  exact leftTriv_one _

/-- `g (g⁻¹ v) = v`: the left trivialization is inverted by the tangent map of `λ_g`. -/
theorem tangentMap_mul_left_leftTriv (p : TangentBundle E G) :
    tangentMap E E (fun k ↦ p.proj * k) ⟨1, leftTriv E p⟩ = p := by
  rw [← tangentMap_inv_mul, tangentMap_comp (smoothMBM_mul_left (E := E) p.proj 1)
    (smoothMBM_mul_left (E := E) p.proj⁻¹ 1)]
  have : ((fun k ↦ p.proj * k) ∘ fun k ↦ p.proj⁻¹ * k) = (id : G → G) := by
    funext k; simp
  rw [this, tangentMap_id]

/-- The left trivialization is injective on each tangent space. -/
theorem leftTriv_injective (g : G) :
    Function.Injective fun v : E ↦ leftTriv E (⟨g, v⟩ : TangentBundle E G) := by
  intro v w h
  have hv := tangentMap_mul_left_leftTriv (E := E) (⟨g, v⟩ : TangentBundle E G)
  have hw := tangentMap_mul_left_leftTriv (E := E) (⟨g, w⟩ : TangentBundle E G)
  change leftTriv E (⟨g, v⟩ : TangentBundle E G) = leftTriv E (⟨g, w⟩ : TangentBundle E G) at h
  rw [h] at hv
  exact TotalSpace.mk_inj.mp (hv.symm.trans hw)

theorem leftTriv_zero (g : G) : leftTriv E (⟨g, 0⟩ : TangentBundle E G) = 0 := by
  have := leftTriv_smul (E := E) g 0 0
  rwa [zero_smul, zero_smul] at this

/-! ### The left invariant Finsler metric -/

/-- **The left invariant Finsler metric** `|v|_g = |g⁻¹ v|` defined by a Finsler seminorm `ν` on
`L(G)` ([Lar19, Remark 2.5]). It is continuous on `TG` (`continuous_leftTriv`). -/
def leftFinsler (ν : FinslerSeminorm E) : FinslerMetric E G where
  toFun p := ν (leftTriv E p)
  nonneg' _ := ν.nonneg _
  add_le' x v w := by rw [leftTriv_add]; exact ν.add_le _ _
  smul_eq' x c hc v := by rw [leftTriv_smul]; exact ν.smul_eq hc _
  continuous_fiber' x := ν.continuous.comp (continuous_leftTriv_fiber x)
  continuous' := ν.continuous.comp continuous_leftTriv

variable (ν : FinslerSeminorm E)

theorem leftFinsler_apply (p : TangentBundle E G) :
    (leftFinsler ν).toFun p = ν (leftTriv E p) :=
  rfl

/-- `|x_l(g)|_g = |x|`. -/
theorem leftFinsler_leftField (x : LieAlg E G) (g : G) :
    (leftFinsler ν).toFun (leftField E x g) = ν x := by
  rw [leftFinsler_apply, leftTriv_leftField]

/-- **`leftFinsler ν` is left invariant**: `|h v|_{h g} = |v|_g`. -/
theorem leftFinsler_tangentMap_mul_left (h : G) (p : TangentBundle E G) :
    (leftFinsler ν).toFun (tangentMap E E (fun k ↦ h * k) p) = (leftFinsler ν).toFun p := by
  rw [leftFinsler_apply, leftFinsler_apply, leftTriv_tangentMap_mul_left]

/-- **Left translations preserve lengths.** -/
theorem length_mul_left (h : G) {γ : ℝ → G} (hγ : IsCkCurve E 1 γ) (a b : ℝ) :
    (leftFinsler ν).length (fun t ↦ h * γ t) a b = (leftFinsler ν).length γ a b :=
  FinslerLengthStructure.length_comp_eq _ _ (smoothMBM_mul_left (E := E) h 1)
    (leftFinsler_tangentMap_mul_left ν h) hγ a b

/-- **Left translations are isometries** of the Finsler distance: `d(h x, h y) = d(x, y)`
([Lar19, Remark 2.5 and Prop. 2.10(3)]). -/
theorem dist_mul_left (h x y : G) :
    (leftFinsler ν).dist (h * x) (h * y) = (leftFinsler ν).dist x y := by
  have hle : ∀ (h x y : G), (leftFinsler ν).dist (h * x) (h * y) ≤ (leftFinsler ν).dist x y :=
    fun h x y ↦ FinslerLengthStructure.dist_map_le_of_le _ _
      (smoothMBM_mul_left (E := E) h 1)
      (fun p ↦ (leftFinsler_tangentMap_mul_left ν h p).le) x y
  refine le_antisymm (hle h x y) ?_
  simpa using hle h⁻¹ (h * x) (h * y)

/-- **Every left invariant field of Finsler seminorms is `leftFinsler` of its value at the
identity** ([Lar19, Remark 2.5]). -/
theorem eq_leftFinsler (μ : FinslerSeminormField E G)
    (hμ : ∀ (h : G) (p : TangentBundle E G), μ (tangentMap E E (fun k ↦ h * k) p) = μ p)
    (p : TangentBundle E G) : μ p = (leftFinsler (μ.fiber 1)).toFun p := by
  rw [leftFinsler_apply, ← hμ p.proj⁻¹ p, tangentMap_inv_mul]
  rfl

/-- `leftFinsler ν` is reversible exactly when `ν` is. -/
theorem leftFinsler_isReversible_iff :
    (leftFinsler (G := G) ν).IsReversible ↔ ν.IsReversible := by
  constructor
  · intro h v
    have := h 1 v
    change ν (leftTriv E (⟨(1 : G), -v⟩ : TangentBundle E G)) =
      ν (leftTriv E (⟨(1 : G), v⟩ : TangentBundle E G)) at this
    rwa [leftTriv_one, leftTriv_one] at this
  · intro h x v
    change ν (leftTriv E (⟨x, -v⟩ : TangentBundle E G)) =
      ν (leftTriv E (⟨x, v⟩ : TangentBundle E G))
    rw [leftTriv_neg]
    exact h _

/-- `leftFinsler ν` is nondegenerate (each `|·|_g` is a Finsler norm) exactly when `ν` is a
Finsler norm. -/
theorem leftFinsler_isNondegenerate_iff :
    (leftFinsler (G := G) ν).IsNondegenerate ↔ ν.IsNorm := by
  constructor
  · intro h v hv
    refine h 1 v ?_
    change ν (leftTriv E (⟨(1 : G), v⟩ : TangentBundle E G)) = 0
    rwa [leftTriv_one]
  · intro h x v hv
    change ν (leftTriv E (⟨x, v⟩ : TangentBundle E G)) = 0 at hv
    refine leftTriv_injective (E := E) x ?_
    change leftTriv E (⟨x, v⟩ : TangentBundle E G) = leftTriv E (⟨x, 0⟩ : TangentBundle E G)
    rw [leftTriv_zero, h _ hv]

end LocallyConvex.LieGroups.MBLieGroup
