/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Metric.LeftInvariant
public import LocallyConvexLieGroups.LieAlgebra.Adjoint

/-!
# Uniform and bi-invariant Finsler metrics on Lie groups

A Finsler metric on a Lie group is **L-uniform** (resp. **R-uniform**) if the left (resp. right)
translations have differentials bounded by an upper semicontinuous function `L` with `L(1) = 1`
([Lar19, Def. 2.4]). Translations are then Lipschitz for the Finsler distance, and for a left
invariant R-uniform metric the group operations are continuous for the distance
([Lar19, Prop. 2.10(3), (4)]).

For the left invariant metric `|v|_g = |g⁻¹ v|` of a Finsler seminorm on `L(G)`, the right
translations act through the adjoint representation: `(x g)⁻¹ (v g) = Ad(g⁻¹)(x⁻¹ v)`. So the
metric is R-uniform with function `R` iff `|Ad(g⁻¹) v| ≤ R(g) |v|`, and it is **bi-invariant**
iff the seminorm is `Ad`-invariant ([Lar19, Remark 2.5 and Remark 3.7]).

## Main definitions

* `MBLieGroup.IsLUniform`, `MBLieGroup.IsRUniform`: [Lar19, Def. 2.4].
* `MBLieGroup.IsAdInvariant`: a Finsler seminorm on `L(G)` invariant under `Ad(G)`.

## Main results

* `MBLieGroup.IsLUniform.dist_mul_left_le`, `MBLieGroup.IsRUniform.dist_mul_right_le`:
  translations are Lipschitz ([Lar19, Prop. 2.10(3)]).
* `MBLieGroup.leftTriv_tangentMap_mul_right`: `(x g)⁻¹ (v g) = Ad(g⁻¹)(x⁻¹ v)`.
* `MBLieGroup.isRUniform_leftFinsler`: the left invariant metric is R-uniform when the adjoint
  representation is bounded by `R`.
* `MBLieGroup.dist_mul_right`: for an `Ad`-invariant seminorm, right translations are isometries
  too: the metric is bi-invariant.
* `MBLieGroup.tendsto_dist_mul`, `MBLieGroup.tendsto_dist_inv`: for a left invariant R-uniform
  metric, multiplication and inversion are continuous for the distance ([Lar19, Prop. 2.10(4)]).
  The proofs do not use reversibility; for a reversible metric they give the joint continuity of
  the group operations for the topology of the distance.

## References

* [G. Larotonda, *The metric geometry of infinite dimensional Lie groups and their homogeneous
  spaces*][Lar19]
-/

@[expose] public section

open Set Filter Bundle
open scoped Topology ENNReal
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups.MBLieGroup

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]

/-! ### Uniform metrics -/

/-- **L-uniform Finsler metrics** ([Lar19, Def. 2.4]): `|g v|_{g h} ≤ L(g) |v|_h` for an upper
semicontinuous `L` with `L(1) = 1`. -/
structure IsLUniform (μ : FinslerMetric E G) (L : G → ℝ) : Prop where
  upperSemicontinuous : UpperSemicontinuous L
  map_one : L 1 = 1
  le : ∀ (g : G) (p : TangentBundle E G),
    μ.toFun (tangentMap E E (fun k ↦ g * k) p) ≤ L g * μ.toFun p

/-- **R-uniform Finsler metrics** ([Lar19, Def. 2.4]): `|v g|_{h g} ≤ R(g) |v|_h` for an upper
semicontinuous `R` with `R(1) = 1`. -/
structure IsRUniform (μ : FinslerMetric E G) (R : G → ℝ) : Prop where
  upperSemicontinuous : UpperSemicontinuous R
  map_one : R 1 = 1
  le : ∀ (g : G) (p : TangentBundle E G),
    μ.toFun (tangentMap E E (fun k ↦ k * g) p) ≤ R g * μ.toFun p

variable {μ : FinslerMetric E G} {L R : G → ℝ}

/-- **Left translations are `L(g)`-Lipschitz** for an L-uniform metric
([Lar19, Prop. 2.10(3)]). -/
theorem IsLUniform.dist_mul_left_le (hL : IsLUniform μ L) {g : G} (hg : 0 < L g) (x y : G) :
    μ.dist (g * x) (g * y) ≤ ENNReal.ofReal (L g) * μ.dist x y :=
  FinslerLengthStructure.dist_map_le _ _ (smoothMBM_mul_left (E := E) g 1) hg (hL.le g) x y

/-- **Right translations are `R(g)`-Lipschitz** for an R-uniform metric
([Lar19, Prop. 2.10(3)]). -/
theorem IsRUniform.dist_mul_right_le (hR : IsRUniform μ R) {g : G} (hg : 0 < R g) (x y : G) :
    μ.dist (x * g) (y * g) ≤ ENNReal.ofReal (R g) * μ.dist x y :=
  FinslerLengthStructure.dist_map_le _ _ (smoothMBM_mul_right (E := E) g 1) hg (hR.le g) x y

variable (ν : FinslerSeminorm E)

/-- **Left invariant metrics are L-uniform** with `L ≡ 1` ([Lar19, Remark 2.5]). -/
theorem isLUniform_leftFinsler : IsLUniform (leftFinsler (G := G) ν) fun _ ↦ 1 where
  upperSemicontinuous := upperSemicontinuous_const
  map_one := rfl
  le g p := by rw [one_mul, leftFinsler_tangentMap_mul_left]

/-! ### Right translations and the adjoint representation -/

/-- `T_1(c_g) w = Ad(g) w`, written in the tangent bundle. -/
theorem tangentMap_conj_one (g : G) (w : E) :
    tangentMap E E (fun k ↦ g * k * g⁻¹) (⟨1, w⟩ : TangentBundle E G) =
      ⟨1, (Ad E g w : E)⟩ := by
  have key : ∀ a : G, a = 1 → (⟨a, (dMB (chartAt E a ∘ (fun k ↦ g * k * g⁻¹) ∘
      (chartAt E (1 : G)).symm) (chartAt E (1 : G) 1, w) : E)⟩ : TangentBundle E G) =
      ⟨1, (Ad E g w : E)⟩ := by
    rintro a rfl
    rfl
  exact key _ (by group)

/-- **Right translations act on the left trivialization through `Ad`**:
`(x g)⁻¹ (v g) = Ad(g⁻¹)(x⁻¹ v)`. -/
theorem leftTriv_tangentMap_mul_right (g : G) (p : TangentBundle E G) :
    leftTriv E (tangentMap E E (fun k ↦ k * g) p) = (Ad E g⁻¹ (leftTriv E p) : E) := by
  set q := tangentMap E E (fun k ↦ k * g) p
  have h1 := tangentMap_inv_mul (E := E) q
  have h2 : tangentMap E E (fun k ↦ q.proj⁻¹ * k) q =
      tangentMap E E (fun k ↦ g⁻¹ * k * g⁻¹⁻¹) (tangentMap E E (fun k ↦ p.proj⁻¹ * k) p) := by
    rw [tangentMap_comp (smoothMBM_mul_left (E := E) q.proj⁻¹ 1)
      (smoothMBM_mul_right (E := E) g 1),
      tangentMap_comp (smoothMBM_conj (E := E) g⁻¹ 1) (smoothMBM_mul_left (E := E) p.proj⁻¹ 1)]
    congr 1
    funext k
    change (p.proj * g)⁻¹ * (k * g) = g⁻¹ * (p.proj⁻¹ * k) * g⁻¹⁻¹
    group
  rw [h2, tangentMap_inv_mul, tangentMap_conj_one] at h1
  exact (TotalSpace.mk_inj.mp h1).symm

/-- `|v g|_{x g} = |Ad(g⁻¹)(x⁻¹ v)|` for the left invariant metric. -/
theorem leftFinsler_tangentMap_mul_right (g : G) (p : TangentBundle E G) :
    (leftFinsler ν).toFun (tangentMap E E (fun k ↦ k * g) p) =
      ν (Ad E g⁻¹ (leftTriv E p) : E) := by
  rw [leftFinsler_apply, leftTriv_tangentMap_mul_right]

/-- **The left invariant metric is R-uniform when `Ad` is bounded by `R`**:
if `|Ad(g⁻¹) v| ≤ R(g) |v|`, with `R` upper semicontinuous and `R(1) = 1`
([Lar19, Remark 2.5]). -/
theorem isRUniform_leftFinsler (hR : UpperSemicontinuous R) (hR1 : R 1 = 1)
    (hAd : ∀ (g : G) (v : E), ν (Ad E g⁻¹ v : E) ≤ R g * ν v) :
    IsRUniform (leftFinsler (G := G) ν) R where
  upperSemicontinuous := hR
  map_one := hR1
  le g p := by
    rw [leftFinsler_tangentMap_mul_right, leftFinsler_apply]
    exact hAd g _

variable (G) in
/-- A Finsler seminorm on `L(G)` is **`Ad`-invariant** if `|Ad(g) v| = |v|` for all `g ∈ G`. -/
def IsAdInvariant : Prop := ∀ (g : G) (v : E), ν (Ad E g v : E) = ν v

variable {ν}

/-- **For an `Ad`-invariant seminorm, `leftFinsler` is right invariant too.** -/
theorem leftFinsler_tangentMap_mul_right_of_isAdInvariant (hν : IsAdInvariant G ν) (g : G)
    (p : TangentBundle E G) :
    (leftFinsler ν).toFun (tangentMap E E (fun k ↦ k * g) p) = (leftFinsler ν).toFun p := by
  rw [leftFinsler_tangentMap_mul_right, hν, leftFinsler_apply]

/-- **An `Ad`-invariant seminorm gives a bi-invariant metric**: right translations preserve
lengths. -/
theorem length_mul_right (hν : IsAdInvariant G ν) (g : G) {γ : ℝ → G} (hγ : IsCkCurve E 1 γ)
    (a b : ℝ) : (leftFinsler ν).length (fun t ↦ γ t * g) a b = (leftFinsler ν).length γ a b :=
  FinslerLengthStructure.length_comp_eq _ _ (smoothMBM_mul_right (E := E) g 1)
    (leftFinsler_tangentMap_mul_right_of_isAdInvariant hν g) hγ a b

/-- **An `Ad`-invariant seminorm gives a bi-invariant metric**: right translations are
isometries. -/
theorem dist_mul_right (hν : IsAdInvariant G ν) (g x y : G) :
    (leftFinsler ν).dist (x * g) (y * g) = (leftFinsler ν).dist x y := by
  have hle : ∀ (g x y : G), (leftFinsler ν).dist (x * g) (y * g) ≤ (leftFinsler ν).dist x y :=
    fun g x y ↦ FinslerLengthStructure.dist_map_le_of_le _ _
      (smoothMBM_mul_right (E := E) g 1)
      (fun p ↦ (leftFinsler_tangentMap_mul_right_of_isAdInvariant hν g p).le) x y
  refine le_antisymm (hle g x y) ?_
  simpa using hle g⁻¹ (x * g) (y * g)

/-- An `Ad`-invariant seminorm gives an R-uniform metric with `R ≡ 1`. -/
theorem isRUniform_leftFinsler_of_isAdInvariant (hν : IsAdInvariant G ν) :
    IsRUniform (leftFinsler (G := G) ν) fun _ ↦ 1 :=
  isRUniform_leftFinsler ν upperSemicontinuous_const rfl fun g v ↦ by rw [hν, one_mul]

/-! ### Continuity of the group operations for the distance ([Lar19, Prop. 2.10(4)]) -/

/-- **Multiplication is continuous for the distance** of a left invariant R-uniform metric
([Lar19, Prop. 2.10(4)]): `d(a b, g h) ≤ d(b, h) + R(h) d(a, g)`. -/
theorem tendsto_dist_mul (hR : IsRUniform (leftFinsler (G := G) ν) R) (hRpos : ∀ g, 0 < R g)
    {ι : Type*} {l : Filter ι} {a b : ι → G} {g h : G}
    (ha : Tendsto (fun i ↦ (leftFinsler ν).dist (a i) g) l (𝓝 0))
    (hb : Tendsto (fun i ↦ (leftFinsler ν).dist (b i) h) l (𝓝 0)) :
    Tendsto (fun i ↦ (leftFinsler ν).dist (a i * b i) (g * h)) l (𝓝 0) := by
  have hbound : ∀ i, (leftFinsler ν).dist (a i * b i) (g * h) ≤
      (leftFinsler ν).dist (b i) h + ENNReal.ofReal (R h) * (leftFinsler ν).dist (a i) g := by
    intro i
    calc (leftFinsler ν).dist (a i * b i) (g * h)
        ≤ (leftFinsler ν).dist (a i * b i) (a i * h) + (leftFinsler ν).dist (a i * h) (g * h) :=
          (leftFinsler ν).toFinslerLengthStructure.dist_triangle _ _ _
      _ ≤ (leftFinsler ν).dist (b i) h + ENNReal.ofReal (R h) * (leftFinsler ν).dist (a i) g := by
          rw [dist_mul_left]
          gcongr
          exact hR.dist_mul_right_le (hRpos h) _ _
  have hlim : Tendsto (fun i ↦ (leftFinsler ν).dist (b i) h +
      ENNReal.ofReal (R h) * (leftFinsler ν).dist (a i) g) l (𝓝 0) := by
    have := hb.add (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (R h)) ha
      (Or.inr ENNReal.ofReal_ne_top))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ bot_le) hbound

/-- **Inversion is continuous for the distance** of a left invariant R-uniform metric
([Lar19, Prop. 2.10(4)]): `d(a⁻¹, g⁻¹) ≤ R(g⁻¹) d(g, a)`. -/
theorem tendsto_dist_inv (hR : IsRUniform (leftFinsler (G := G) ν) R) (hRpos : ∀ g, 0 < R g)
    {ι : Type*} {l : Filter ι} {a : ι → G} {g : G}
    (ha : Tendsto (fun i ↦ (leftFinsler ν).dist g (a i)) l (𝓝 0)) :
    Tendsto (fun i ↦ (leftFinsler ν).dist (a i)⁻¹ g⁻¹) l (𝓝 0) := by
  have hbound : ∀ i, (leftFinsler ν).dist (a i)⁻¹ g⁻¹ ≤
      ENNReal.ofReal (R g⁻¹) * (leftFinsler ν).dist g (a i) := by
    intro i
    have e1 : (leftFinsler ν).dist (a i)⁻¹ g⁻¹ = (leftFinsler ν).dist (g * g⁻¹) (a i * g⁻¹) := by
      rw [mul_inv_cancel, ← dist_mul_left ν (a i)⁻¹ 1 (a i * g⁻¹)]
      simp
    rw [e1]
    exact hR.dist_mul_right_le (hRpos g⁻¹) _ _
  have hlim : Tendsto (fun i ↦ ENNReal.ofReal (R g⁻¹) * (leftFinsler ν).dist g (a i)) l
      (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (R g⁻¹)) ha
      (Or.inr ENNReal.ofReal_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ bot_le) hbound

end LocallyConvex.LieGroups.MBLieGroup
