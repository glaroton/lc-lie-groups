/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexLieGroups.Regular.FundamentalGlobal
public import LocallyConvexLieGroups.LieGroup.Quotient
public import LocallyConvexManifolds.DifferentialForm.Basic

/-!
# The Fundamental Theorem on manifolds

Let `G` be a `C⁰`-regular Lie group with Lie algebra `𝔤` and `M` a simply connected manifold. A
`𝔤`-valued `1`-form `α` on `M` satisfying the Maurer–Cartan equation is the logarithmic derivative
of a smooth map `f : M → G` ([GN26, Theorem 6.1.13], parts (i) and (ii)(a)), unique up to left
translation if `M` is connected.

## Proof

The passage from local to global primitives only uses formal properties of primitives, so we
isolate them in `MBLieGroup.PrimSystem`: on a topological space `T`, a class of "primitives"
`f : T → G` on open sets, closed under restriction, left translation and gluing, with primitives
on a basis of open sets on which they are unique up to left translation. As in
`Regular/FundamentalGlobal.lean`, the germs of primitives form a covering space of `T`
(`PrimSystem.isCoveringMap_proj`), and if `T` is simply connected and locally path connected the
identity of `T` lifts to it, which gives a global primitive (`PrimSystem.exists_prim_univ`).

On a manifold, `f` is a primitive of `α` on `V` if it is smooth there and its logarithmic
derivative, read in the preferred chart at each point, is `α`. In a chart `c` this is the
condition that `f ∘ c⁻¹` is a primitive of the local representative `α_c` of `α`, because the
logarithmic derivative and the local representatives transform in the same way under the
transition maps (`MBLieGroup.logDeriv_comp`). The basic open sets are the preimages `c⁻¹(C)` of
convex open subsets of chart ranges, where the Fundamental Theorem on convex sets
(`MBLieGroup.exists_isLogPrimitive`) gives primitives, unique up to left translation.

## Main definitions

* `MBLieGroup.PrimSystem`: systems of primitives; `MBLieGroup.PrimSystem.HasPrim`: primitives
  exist on the basic open sets.
* `MBLieGroup.formRep`: the local representative `α_c(y, h)` of a `1`-form in a chart.
* `MBLieGroup.IsLogPrimitiveM`: `f` is a primitive of `α` on `V`.
* `MBLieGroup.IsMaurerCartan`: `α` satisfies the Maurer–Cartan equation in the preferred charts.

## Main results

* `MBLieGroup.PrimSystem.exists_prim_univ`, `MBLieGroup.PrimSystem.eqOn_univ`: global primitives
  on simply connected spaces, unique up to left translation on connected ones.
* `MBLieGroup.PrimSystem.per`, `MBLieGroup.PrimSystem.exists_prim_univ_iff_per_eq_one`: the
  period homomorphism, and global primitives exist if and only if it is trivial.
* `MBLieGroup.logDeriv_comp`: the chain rule for logarithmic derivatives.
* `MBLieGroup.isMaurerCartan_of_logDeriv`: logarithmic derivatives satisfy the Maurer–Cartan
  equation.
* `MBLieGroup.exists_logDeriv_eq_of_simplyConnected_manifold`: **the Fundamental Theorem on
  manifolds**; `MBLieGroup.eq_of_logDeriv_eq`: uniqueness up to left translation.
* `MBLieGroup.perForm`, `MBLieGroup.exists_logDeriv_eq_iff_perForm_eq_one`: **`α` is integrable
  if and only if its period homomorphism vanishes** ([GN26, Theorem 6.1.13(ii)(b)]).

The period homomorphism `MBLieGroup.PrimSystem.per` is the monodromy of the covering of germs on
the germ `(x₀, 1)`; it commutes with left translations of germs, hence is a homomorphism, and it is
trivial exactly when the identity of `T` lifts to the germs (`exists_prim_univ_iff_per_eq_one`).

## Implementation notes

The Maurer–Cartan equation `dα + ½[α, α] = 0` is stated in the preferred charts, in the form
`∂_k α_c(z, h) − ∂_h α_c(z, k) = [α_c(z, h), α_c(z, k)]` used in `Regular/Fundamental.lean`.

[GN26, Definition 6.1.12] defines the period of a piecewise smooth loop `γ` as `evol_G(γ*α)`; here
it is the endpoint of the lift of `γ` to the germs, defined for all continuous loops. For a smooth
loop the two agree ([GN26, Lemma 6.1.11]), but this identification is not formalized. Mathlib's
fundamental group composes loops in the opposite order (`p * q` is `q` followed by `p`), so the
period map is a homomorphism into `Gᵐᵒᵖ`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology
open LocallyConvex.Analysis LocallyConvex.Manifolds

noncomputable section

namespace LocallyConvex.LieGroups.MBLieGroup

universe u

/-! ### Systems of primitives -/

/-- A **system of primitives** on `T` with values in the group `G`: `prim V f` says that `f` is a
primitive on the open set `V`. Primitives restrict, translate on the left and glue; and on the
open sets of a basis they are unique up to left translation. Their existence on the basic sets is
a separate hypothesis (`PrimSystem.HasPrim`). -/
structure PrimSystem (T : Type*) [TopologicalSpace T] (G : Type*) [Group G] where
  /-- `f` is a primitive on `V`. -/
  prim : Set T → (T → G) → Prop
  /-- The basic open sets. -/
  basic : Set (Set T)
  isOpen_basic : ∀ V ∈ basic, IsOpen V
  exists_basic : ∀ {W : Set T} {x : T}, IsOpen W → x ∈ W → ∃ V ∈ basic, x ∈ V ∧ V ⊆ W
  mono : ∀ {V W : Set T} {f : T → G}, prim V f → IsOpen W → W ⊆ V → prim W f
  mul_left : ∀ {V : Set T} {f : T → G} (g : G), prim V f → prim V fun y ↦ g * f y
  eqOn : ∀ {V : Set T} {f₁ f₂ : T → G} {x : T}, V ∈ basic → prim V f₁ → prim V f₂ → x ∈ V →
    f₁ x = f₂ x → EqOn f₁ f₂ V
  of_local : ∀ {V : Set T} {f : T → G}, IsOpen V →
    (∀ x ∈ V, ∃ W, IsOpen W ∧ x ∈ W ∧ ∃ f', prim W f' ∧ EqOn f f' W) → prim V f

namespace PrimSystem

variable {T : Type*} [TopologicalSpace T] {G : Type*} [Group G] (S : PrimSystem T G)

/-- Primitives exist on the basic open sets. -/
def HasPrim : Prop := ∀ V ∈ S.basic, ∃ f, S.prim V f

/-- The germs of primitives: `T × G`, topologized by the graphs of primitives over basic sets. -/
@[nolint unusedArguments]
def Germs (_S : PrimSystem T G) : Type _ := T × G

/-- The graph of `f` over `V`. -/
def sheet (V : Set T) (f : T → G) : Set S.Germs := {p | p.1 ∈ V ∧ p.2 = f p.1}

instance : TopologicalSpace S.Germs :=
  generateFrom {A | ∃ V f, V ∈ S.basic ∧ S.prim V f ∧ A = S.sheet V f}

/-- The projection of germs to `T`. -/
def proj (p : S.Germs) : T := p.1

theorem isOpen_sheet {V : Set T} {f : T → G} (hV : V ∈ S.basic) (hf : S.prim V f) :
    IsOpen (S.sheet V f) :=
  isOpen_generateFrom_of_mem ⟨V, f, hV, hf, rfl⟩

/-- A primitive through a given germ, on a basic set inside a given open set. -/
theorem exists_sheet (hS : S.HasPrim) (p : S.Germs) {W : Set T} (hW : IsOpen W) (hp : p.1 ∈ W) :
    ∃ V ∈ S.basic, ∃ f, V ⊆ W ∧ S.prim V f ∧ p ∈ S.sheet V f := by
  obtain ⟨V, hV, hpV, hVW⟩ := S.exists_basic hW hp
  obtain ⟨f, hf⟩ := hS V hV
  refine ⟨V, hV, fun y ↦ (p.2 * (f p.1)⁻¹) * f y, hVW, S.mul_left _ hf, hpV, ?_⟩
  simp

theorem continuous_proj (hS : S.HasPrim) : Continuous S.proj := by
  rw [continuous_def]
  intro W hW
  rw [isOpen_iff_forall_mem_open]
  intro p hp
  obtain ⟨V, hV, f, hVW, hf, hpV⟩ := S.exists_sheet hS p hW hp
  exact ⟨S.sheet V f, fun q hq ↦ hVW hq.1, S.isOpen_sheet hV hf, hpV⟩

/-- The section `y ↦ (y, f(y))` over `V`, for a primitive `f` on the open set `V`. -/
theorem continuous_section {V : Set T} (hV : IsOpen V) {f : T → G} (hf : S.prim V f) :
    Continuous fun y : V ↦ (show S.Germs from (y.1, f y.1)) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨W, fW, hW, hfW, rfl⟩
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨hyW, hyeq⟩ : (y.1 ∈ W ∧ f y.1 = fW y.1) := hy
  obtain ⟨C, hC, hyC, hCVW⟩ := S.exists_basic (hV.inter (S.isOpen_basic W hW)) ⟨y.2, hyW⟩
  have hCo := S.isOpen_basic C hC
  have heq := S.eqOn hC (S.mono hf hCo (hCVW.trans inter_subset_left))
    (S.mono hfW hCo (hCVW.trans inter_subset_right)) hyC hyeq
  exact ⟨{z | z.1 ∈ C}, fun z hz ↦ ⟨(hCVW hz).2, heq hz⟩,
    (S.isOpen_basic C hC).preimage continuous_subtype_val, hyC⟩

/-- **The germs of primitives form a covering space.** -/
theorem isCoveringMap_proj (hS : S.HasPrim) : IsCoveringMap S.proj := by
  intro x
  refine IsEvenlyCovered.to_isEvenlyCovered_preimage (I := Disc G) ?_
  obtain ⟨C, hC, hxC, -⟩ := S.exists_basic isOpen_univ (mem_univ x)
  obtain ⟨f, hf⟩ := hS C hC
  have hCo := S.isOpen_basic C hC
  have hcp := S.continuous_proj hS
  let H : S.proj ⁻¹' C ≃ₜ C × Disc G :=
  { toFun := fun p ↦ (⟨p.1.1, p.2⟩, toDisc (p.1.2 * (f p.1.1)⁻¹))
    invFun := fun q ↦ ⟨(show S.Germs from (q.1.1, ofDisc q.2 * f q.1.1)), q.1.2⟩
    left_inv := fun p ↦ Subtype.ext (Prod.ext rfl (inv_mul_cancel_right (G := G) _ _))
    right_inv := fun q ↦ Prod.ext rfl (mul_inv_cancel_right (ofDisc q.2) _)
    continuous_toFun := by
      refine ((hcp.comp continuous_subtype_val).subtype_mk _).prodMk ?_
      refine continuous_discrete_rng.2 fun g ↦ ?_
      have : (fun p : S.proj ⁻¹' C ↦ toDisc (p.1.2 * (f p.1.1)⁻¹)) ⁻¹' {g} =
          (↑) ⁻¹' S.sheet C (fun y ↦ ofDisc g * f y) := by
        ext p
        simp only [mem_preimage, mem_singleton_iff, sheet]
        constructor
        · intro h; exact ⟨p.2, by rw [← h]; exact (inv_mul_cancel_right (G := G) _ _).symm⟩
        · intro h; change p.1.2 * (f p.1.1)⁻¹ = ofDisc g; rw [h.2]
          exact mul_inv_cancel_right _ _
      rw [this]
      exact (S.isOpen_sheet hC (S.mul_left (ofDisc g) hf)).preimage continuous_subtype_val
    continuous_invFun := by
      refine continuous_prod_of_discrete_right.2 fun g ↦ ?_
      exact (S.continuous_section hCo (S.mul_left (ofDisc g) hf)).subtype_mk _ }
  exact ⟨inferInstance, C, hxC, hCo, hCo.preimage hcp, H, fun _ ↦ rfl⟩

/-- **A continuous section of the germs gives a global primitive.** -/
theorem prim_of_section (hS : S.HasPrim) (F : C(T, S.Germs)) (hF1 : ∀ a, (F a).1 = a) :
    S.prim univ fun y ↦ (F y).2 := by
  refine S.of_local isOpen_univ fun y₀ _ ↦ ?_
  obtain ⟨C₀, hC₀, hy₀C₀, -⟩ := S.exists_basic isOpen_univ (mem_univ y₀)
  obtain ⟨f₀, hf₀⟩ := hS C₀ hC₀
  set g := (F y₀).2 * (f₀ y₀)⁻¹
  have hP₀ := S.mul_left g hf₀
  have hSo := (S.isOpen_sheet hC₀ hP₀).preimage F.continuous
  have hy₀ : y₀ ∈ F ⁻¹' S.sheet C₀ (fun y ↦ g * f₀ y) := by
    refine ⟨by rw [hF1]; exact hy₀C₀, ?_⟩
    change (F y₀).2 = g * f₀ (F y₀).1
    rw [hF1]
    simp [g]
  refine ⟨_, hSo, hy₀, fun y ↦ g * f₀ y, S.mono hP₀ hSo fun y hy ↦ ?_, fun y hy ↦ ?_⟩
  · have := hy.1; rwa [hF1] at this
  · have h2 : (F y).2 = g * f₀ (F y).1 := hy.2
    rw [hF1] at h2
    exact h2

/-- **Global primitives on simply connected spaces.** -/
theorem exists_prim_univ (hS : S.HasPrim) [SimplyConnectedSpace T] [LocallyPathConnectedSpace T]
    (x₀ : T) (g₀ : G) : ∃ f, S.prim univ f ∧ f x₀ = g₀ := by
  obtain ⟨F, ⟨hF0, hFp⟩, -⟩ := (S.isCoveringMap_proj hS).existsUnique_continuousMap_lifts
    (ContinuousMap.id T) x₀ (show S.Germs from (x₀, g₀)) rfl
  exact ⟨_, S.prim_of_section hS F fun a ↦ congrFun hFp a, by rw [hF0]⟩

/-- **Uniqueness of global primitives** on preconnected spaces, up to left translation. -/
theorem eqOn_univ [PreconnectedSpace T] {f₁ f₂ : T → G} (h₁ : S.prim univ f₁)
    (h₂ : S.prim univ f₂) {x₀ : T} (h₀ : f₁ x₀ = f₂ x₀) : f₁ = f₂ := by
  set A := {x | f₁ x = f₂ x}
  have hloc : ∀ x, ∃ V ∈ S.basic, x ∈ V ∧ (∀ y ∈ V, f₁ y = f₂ y ↔ f₁ x = f₂ x) := by
    intro x
    obtain ⟨V, hV, hxV, -⟩ := S.exists_basic isOpen_univ (mem_univ x)
    refine ⟨V, hV, hxV, fun y hy ↦ ?_⟩
    set g := f₂ x * (f₁ x)⁻¹
    have hVo := S.isOpen_basic V hV
    have hg := S.eqOn hV (S.mono (S.mul_left g h₁) hVo (subset_univ V))
      (S.mono h₂ hVo (subset_univ V)) hxV (by simp [g])
    have hy' : g * f₁ y = f₂ y := hg hy
    rw [← hy']
    constructor
    · intro h
      have hg1 : g = 1 := mul_right_cancel (h.symm.trans (one_mul _).symm)
      exact (mul_inv_eq_one.1 hg1).symm
    · intro h
      have hg1 : g = 1 := mul_inv_eq_one.2 h.symm
      rw [hg1, one_mul]
  have hopen : IsOpen A := isOpen_iff_forall_mem_open.2 fun x hx ↦ by
    obtain ⟨V, hV, hxV, hiff⟩ := hloc x
    exact ⟨V, fun y hy ↦ (hiff y hy).2 hx, S.isOpen_basic V hV, hxV⟩
  have hclosed : IsClosed A := by
    rw [← isOpen_compl_iff]
    refine isOpen_iff_forall_mem_open.2 fun x hx ↦ ?_
    obtain ⟨V, hV, hxV, hiff⟩ := hloc x
    exact ⟨V, fun y hy hyA ↦ hx ((hiff y hy).1 hyA), S.isOpen_basic V hV, hxV⟩
  have := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨x₀, h₀⟩
  funext x
  have hx : x ∈ A := this ▸ mem_univ x
  exact hx

/-! ### The period homomorphism -/

/-- Left translation of germs, `(x, h) ↦ (x, g h)`. -/
def lmul (g : G) (p : S.Germs) : S.Germs := show T × G from (p.1, g * p.2)

theorem continuous_lmul (g : G) : Continuous (S.lmul g) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨V, f, hV, hf, rfl⟩
  have : S.lmul g ⁻¹' S.sheet V f = S.sheet V (fun y ↦ g⁻¹ * f y) := by
    ext p
    change (p.1 ∈ V ∧ g * p.2 = f p.1) ↔ (p.1 ∈ V ∧ p.2 = g⁻¹ * f p.1)
    rw [eq_inv_mul_iff_mul_eq]
  rw [this]
  exact S.isOpen_sheet hV (S.mul_left _ hf)

/-- The germ `(x, 1)`, in the fiber over `x`. -/
def base (x : T) : S.proj ⁻¹' {x} := ⟨show T × G from (x, 1), rfl⟩

theorem fiber_eq_lmul {x : T} (m : S.proj ⁻¹' {x}) : (m : S.Germs) = S.lmul (m.1.2) (S.base x) :=
  Prod.ext m.2 (mul_one _).symm

/-- Monodromy commutes with left translations. -/
theorem monodromy_lmul (hS : S.HasPrim) {x y : T} (γ : Path.Homotopic.Quotient x y)
    (e : S.proj ⁻¹' {x}) (g : G) :
    ((S.isCoveringMap_proj hS).monodromy γ ⟨S.lmul g e, e.2⟩ : S.Germs) =
      S.lmul g ((S.isCoveringMap_proj hS).monodromy γ e) := by
  set cov := S.isCoveringMap_proj hS
  obtain ⟨γ⟩ := γ
  set L := cov.liftPath γ e (γ.source.trans e.2.symm)
  set Γ : C(unitInterval, S.Germs) := (⟨S.lmul g, S.continuous_lmul g⟩ : C(S.Germs, S.Germs)).comp L
  have hpΓ : S.proj ∘ Γ = γ := by
    funext t
    exact congrFun (cov.liftPath_lifts γ e (γ.source.trans e.2.symm)) t
  have hΓ0 : Γ 0 = (⟨S.lmul g e, e.2⟩ : S.proj ⁻¹' {x}) := by
    change S.lmul g (L 0) = S.lmul g e
    rw [cov.liftPath_zero]
  have k2 := cov.coe_monodromy_mk γ e
  calc _ = Γ 1 := cov.monodromy_eq_apply_one hpΓ hΓ0
    _ = S.lmul g (L 1) := rfl
    _ = _ := by rw [← k2]; rfl

/-- **The period homomorphism** of a system of primitives with primitives on the basic sets: the
monodromy of the germ covering on the germ `(x₀, 1)`. With Mathlib's convention for the
fundamental group (`p * q` is `q` followed by `p`), it is a homomorphism into `Gᵐᵒᵖ`. -/
def per (hS : S.HasPrim) (x₀ : T) : FundamentalGroup T x₀ →* Gᵐᵒᵖ where
  toFun γ := MulOpposite.op ((S.isCoveringMap_proj hS).monodromy γ.asHom (S.base x₀) : S.Germs).2
  map_one' := by
    rw [FundamentalGroup.one_def]
    change MulOpposite.op ((S.isCoveringMap_proj hS).monodromy (.refl x₀) (S.base x₀) :
      S.Germs).2 = 1
    rw [IsCoveringMap.monodromy_refl]
    rfl
  map_mul' p q := by
    rw [FundamentalGroup.mul_def]
    change MulOpposite.op ((S.isCoveringMap_proj hS).monodromy (q.asHom.trans p.asHom)
      (S.base x₀) : S.Germs).2 = _
    rw [IsCoveringMap.monodromy_trans_apply]
    set m := (S.isCoveringMap_proj hS).monodromy q.asHom (S.base x₀)
    have hm : m = ⟨S.lmul m.1.2 (S.base x₀), (S.base x₀).2⟩ := Subtype.ext (S.fiber_eq_lmul m)
    rw [hm, S.monodromy_lmul hS]
    change MulOpposite.op (m.1.2 * _) = _
    rw [MulOpposite.op_mul, ← hm]

theorem per_apply (hS : S.HasPrim) (x₀ : T) (γ : FundamentalGroup T x₀) :
    (S.per hS x₀ γ).unop =
      ((S.isCoveringMap_proj hS).monodromy γ.asHom (S.base x₀) : S.Germs).2 := rfl

/-- **Global primitives exist if and only if the periods vanish**, on a path connected, locally
path connected space ([GN26, Theorem 6.1.13(ii)(b)] in this setting). -/
theorem exists_prim_univ_iff_per_eq_one (hS : S.HasPrim) [PathConnectedSpace T]
    [LocallyPathConnectedSpace T] (x₀ : T) : (∃ f, S.prim univ f) ↔ S.per hS x₀ = 1 := by
  set cov := S.isCoveringMap_proj hS
  constructor
  · rintro ⟨f, hf⟩
    set f' : T → G := fun y ↦ (f x₀)⁻¹ * f y
    have hf' : S.prim univ f' := S.mul_left _ hf
    set s : C(T, S.Germs) := ⟨fun y ↦ show T × G from (y, f' y),
      (S.continuous_section isOpen_univ hf').comp (continuous_id.subtype_mk fun y ↦ mem_univ y)⟩
    have hloop : ∀ δ : Path.Homotopic.Quotient x₀ x₀,
        (cov.monodromy δ (S.base x₀) : S.Germs).2 = 1 := by
      rintro ⟨δ⟩
      have hpΓ : S.proj ∘ s.comp δ.toContinuousMap = δ := rfl
      have hΓ0 : s.comp δ.toContinuousMap 0 = S.base x₀ := by
        change (show T × G from (δ 0, f' (δ 0))) = (x₀, 1)
        rw [δ.source]
        simp [f']
      have key := cov.monodromy_eq_apply_one hpΓ hΓ0
      change (cov.monodromy (Path.Homotopic.Quotient.mk δ) (S.base x₀) : S.Germs).2 = 1
      rw [key]
      change f' (δ 1) = 1
      rw [δ.target]
      simp [f']
    refine MonoidHom.ext fun γ ↦ MulOpposite.unop_injective ?_
    rw [per_apply]
    exact hloop _
  · intro hper
    have hloop : ∀ δ : Path.Homotopic.Quotient x₀ x₀, cov.monodromy δ (S.base x₀) = S.base x₀ := by
      intro δ
      have h1 := congrArg MulOpposite.unop (DFunLike.congr_fun hper (FundamentalGroup.fromPath δ))
      change (cov.monodromy δ (S.base x₀) : S.Germs).2 = 1 at h1
      refine Subtype.ext ?_
      rw [S.fiber_eq_lmul, h1]
      exact Prod.ext rfl (one_mul _)
    obtain ⟨F, ⟨-, hFp⟩, -⟩ := cov.isLocalHomeomorph.existsUnique_continuousMap_lifts
      (ContinuousMap.id T) x₀ (S.base x₀).1 rfl
      (fun γ γ_0 ↦ by
        simpa [and_comm] using cov.exists_path_lifts ((ContinuousMap.id T).comp γ) (S.base x₀).1
          (by simp [γ_0]; rfl))
      fun γ γ' Γ Γ' γ_0 γ'_0 Γ_0 Γ'_0 Γ_lifts Γ'_lifts γγ'1 ↦ by
        set P : Path x₀ (γ 1) := ⟨γ, γ_0, rfl⟩
        set P' : Path x₀ (γ 1) := ⟨γ', γ'_0, γγ'1.symm⟩
        have h1 := cov.monodromy_eq_apply_one (γ := P) (e := S.base x₀) (Γ := Γ) Γ_lifts Γ_0
        have h2 := cov.monodromy_eq_apply_one (γ := P') (e := S.base x₀) (Γ := Γ') Γ'_lifts Γ'_0
        rw [← h1, ← h2]
        set δ := (Path.Homotopic.Quotient.mk P').trans (Path.Homotopic.Quotient.mk P).symm
        have hδ : δ.trans (Path.Homotopic.Quotient.mk P) = Path.Homotopic.Quotient.mk P' := by
          simp [δ, Path.Homotopic.Quotient.trans_assoc]
        rw [← hδ, IsCoveringMap.monodromy_trans_apply, hloop]
    exact ⟨_, S.prim_of_section hS F fun a ↦ congrFun hFp a⟩

end PrimSystem

/-! ### Logarithmic derivatives under changes of variables -/

section Chain

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]
  {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] [LocallyConvexSpace ℝ X] [T2Space X] in
/-- The logarithmic derivative is local. -/
theorem logDeriv_congr {F₁ F₂ : X → G} {q : X} (h : F₁ =ᶠ[𝓝 q] F₂) (v : X) :
    logDeriv E F₁ q v = logDeriv E F₂ q v := by
  unfold logDeriv
  rw [h.eq_of_nhds]
  exact dMB_congr_of_eventuallyEq (h.mono fun r hr ↦ by simp only [hr]) v

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBLieGroup E G] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [LocallyConvexSpace ℝ X] [T2Space X] in
/-- Left translation does not change the logarithmic derivative. -/
theorem logDeriv_mul_left (F : X → G) (g : G) (q v : X) :
    logDeriv E (fun y ↦ g * F y) q v = logDeriv E F q v := by
  unfold logDeriv
  congr 1
  funext r
  congr 1
  group

/-- **The chain rule for logarithmic derivatives**: `δ(F ∘ τ)(y)(v) = δF(τ y)(dτ(y)(v))`. -/
theorem logDeriv_comp {F : X → G} {O : Set X} (hO : IsOpen O) (hF : SmoothMBMOn X E F O)
    {τ : X → X} {U : Set X} (hτ : ContDiffMBOn 1 τ U) {y : X} (hy : y ∈ U) (hτy : τ y ∈ O)
    (v : X) : logDeriv E (F ∘ τ) y v = logDeriv E F (τ y) (dMB τ (y, v)) := by
  have hd : HasDirDerivAt τ y v (dMB τ (y, v)) := ContDiffMBOn.hasDirDerivAt (k := 0) hτ hy v
  exact (((smoothMBOn_rel hO hF (τ y)) 1).hasDirDerivAt_comp (isOpen_relDom hO hF (τ y)) hd
    (mem_relDom hτy)).dMB_eq

end Chain

/-! ### Primitives of `1`-forms on manifolds -/

section Manifold

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace E G] [MBLieGroup E G]
  {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X]
  {M : Type*} [TopologicalSpace M] [ChartedSpace X M] [MBManifold X M]
  (α : DifferentialForm X M E 1)

/-- The local representative `α_c(y, h)` of the `1`-form `α` in the chart `c`. -/
def formRep (i : atlas X M) (p : X × X) : E := α.localRep i (p.1, fun _ ↦ p.2)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [LocallyConvexSpace ℝ X] [MBManifold X M] in
theorem formRep_prefChart (x : M) (h : X) :
    formRep α (prefChart (E := X) x) (chartAt X x x, h) = α x fun _ ↦ h :=
  α.localRep_prefChart x _

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
/-- On chart overlaps, `α_i(y, h) = α_j(τ y, dτ(y) h)` for the transition map `τ = j ∘ i⁻¹`. -/
theorem formRep_transition (i j : atlas X M) {y : X}
    (hy : y ∈ i.1.target ∩ i.1.symm ⁻¹' j.1.source) (h : X) :
    formRep α i (y, h) = formRep α j ((j.1 ∘ i.1.symm) y, dMB (j.1 ∘ i.1.symm) (y, h)) :=
  α.localRep_eq_pullbackLoc i j hy _

theorem smoothMBOn_formRep (i : atlas X M) : SmoothMBOn (formRep α i) (i.1.target ×ˢ univ) := by
  intro k
  set L : X × X →L[ℝ] X × (Fin 1 → X) := (ContinuousLinearMap.fst ℝ X X).prod
    (ContinuousLinearMap.pi fun _ ↦ ContinuousLinearMap.snd ℝ X X)
  have hO : IsOpen (i.1.target ×ˢ (univ : Set X)) := i.1.open_target.prod isOpen_univ
  exact ContDiffMBOn.comp (g := α.localRep i) (f := L) hO (i.1.open_target.prod isOpen_univ)
    ((α.isLocalForm_localRep i).smooth k) (L.contDiffMBOn k _) fun p hp ↦ ⟨hp.1, mem_univ _⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem formRep_add (i : atlas X M) {z : X} (hz : z ∈ i.1.target) (h k : X) :
    formRep α i (z, h + k) = formRep α i (z, h) + formRep α i (z, k) := by
  obtain ⟨A, hA⟩ := (α.isLocalForm_localRep i).alternating z hz
  have hu : ∀ x : X, Function.update (fun _ : Fin 1 ↦ h) 0 x = fun _ ↦ x := fun x ↦
    funext fun j ↦ by rw [Subsingleton.elim j 0, Function.update_self]
  simp only [formRep, hA]
  rw [← hu (h + k), A.map_update_add, hu, hu]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem formRep_smul (i : atlas X M) {z : X} (hz : z ∈ i.1.target) (c : ℝ) (h : X) :
    formRep α i (z, c • h) = c • formRep α i (z, h) := by
  obtain ⟨A, hA⟩ := (α.isLocalForm_localRep i).alternating z hz
  have hu : ∀ x : X, Function.update (fun _ : Fin 1 ↦ h) 0 x = fun _ ↦ x := fun x ↦
    funext fun j ↦ by rw [Subsingleton.elim j 0, Function.update_self]
  simp only [formRep, hA]
  rw [← hu (c • h), A.map_update_smul, hu]

variable (G) in
/-- **The Maurer–Cartan equation** for `α`, in the preferred charts:
`∂_k α_c(z, h) − ∂_h α_c(z, k) = [α_c(z, h), α_c(z, k)]`. -/
def IsMaurerCartan : Prop :=
  ∀ x : M, ∀ z ∈ (chartAt X x).target, ∀ h k,
    dMB (formRep α (prefChart (E := X) x)) ((z, h), (k, 0)) -
      dMB (formRep α (prefChart (E := X) x)) ((z, k), (h, 0)) =
    (localGroupLaw E G).bracket (formRep α (prefChart (E := X) x) (z, h))
      (formRep α (prefChart (E := X) x) (z, k))

variable (E) in
/-- `f` is a **primitive** of `α` on `V`: `f` is smooth on `V`, and at each `x ∈ V` its
logarithmic derivative, read in the preferred chart at `x`, is `αₓ`. -/
def IsLogPrimitiveM (f : M → G) (V : Set M) : Prop :=
  SmoothMBMOn X E f V ∧
    ∀ x ∈ V, ∀ h, logDeriv E (f ∘ (chartAt X x).symm) (chartAt X x x) h = α x fun _ ↦ h

/-- **Primitives in a chart give primitives on `M`.** -/
theorem isLogPrimitiveM_comp (i : atlas X M) {C : Set X} (hC : IsOpen C)
    {F : X → G} (hF : IsLogPrimitive E (formRep α i) F C) :
    IsLogPrimitiveM E α (F ∘ i.1) (i.1.source ∩ i.1 ⁻¹' C) := by
  have hV : IsOpen (i.1.source ∩ i.1 ⁻¹' C) := i.1.isOpen_inter_preimage hC
  refine ⟨fun k ↦ ?_, fun x hx h ↦ ?_⟩
  · exact ContMDiffMBOn.comp (g := F) (f := i.1) hV hC (hF.1 k)
      (contMDiffMBOn_mono (contMDiffMBOn_chart i.2) inter_subset_left) fun z hz ↦ hz.2
  · set j := prefChart (E := X) x
    have hjx : j.1 x = chartAt X x x := rfl
    have hy : chartAt X x x ∈ j.1.target ∩ j.1.symm ⁻¹' i.1.source :=
      ⟨(chartAt X x).map_source (mem_chart_source X x), by
        change (chartAt X x).symm (chartAt X x x) ∈ i.1.source
        rw [(chartAt X x).left_inv (mem_chart_source X x)]; exact hx.1⟩
    have hτx : (i.1 ∘ j.1.symm) (chartAt X x x) = i.1 x := by
      change i.1 ((chartAt X x).symm (chartAt X x x)) = i.1 x
      rw [(chartAt X x).left_inv (mem_chart_source X x)]
    have hτ : ContDiffMBOn 1 (i.1 ∘ j.1.symm) (j.1.target ∩ j.1.symm ⁻¹' i.1.source) :=
      smoothMBOn_transition j.2 i.2 1
    change logDeriv E (F ∘ (i.1 ∘ j.1.symm)) (chartAt X x x) h = _
    rw [logDeriv_comp hC hF.1 hτ hy (by rw [hτx]; exact hx.2), hF.2 _ (by rw [hτx]; exact hx.2),
      ← formRep_transition α j i hy, ← hjx, formRep_prefChart]

/-- **Primitives on `M` give primitives in charts.** -/
theorem IsLogPrimitiveM.comp_symm {f : M → G} {V : Set M} (hV : IsOpen V)
    (hf : IsLogPrimitiveM E α f V) (i : atlas X M) :
    IsLogPrimitive E (formRep α i) (f ∘ i.1.symm) (i.1.target ∩ i.1.symm ⁻¹' V) := by
  have hW : IsOpen (i.1.target ∩ i.1.symm ⁻¹' V) := i.1.isOpen_inter_preimage_symm hV
  refine ⟨fun k ↦ ?_, fun y hy h ↦ ?_⟩
  · exact ContMDiffMBOn.comp (g := f) (f := i.1.symm) hW hV (hf.1 k)
      (contMDiffMBOn_mono (contMDiffMBOn_chart_symm i.2) inter_subset_left) fun z hz ↦ hz.2
  · set x := i.1.symm y
    set j := prefChart (E := X) x
    have hD : IsOpen (i.1.target ∩ i.1.symm ⁻¹' j.1.source) :=
      i.1.isOpen_inter_preimage_symm j.1.open_source
    have hyD : y ∈ i.1.target ∩ i.1.symm ⁻¹' j.1.source := ⟨hy.1, mem_chart_source X x⟩
    have heq : f ∘ i.1.symm =ᶠ[𝓝 y] (f ∘ j.1.symm) ∘ (j.1 ∘ i.1.symm) := by
      filter_upwards [hD.mem_nhds hyD] with y' hy'
      change f (i.1.symm y') = f (j.1.symm (j.1 (i.1.symm y')))
      rw [j.1.left_inv hy'.2]
    have hO : IsOpen (j.1.target ∩ j.1.symm ⁻¹' V) := j.1.isOpen_inter_preimage_symm hV
    have hfj : SmoothMBMOn X E (f ∘ j.1.symm) (j.1.target ∩ j.1.symm ⁻¹' V) := fun k ↦
      ContMDiffMBOn.comp (g := f) (f := j.1.symm) hO hV (hf.1 k)
        (contMDiffMBOn_mono (contMDiffMBOn_chart_symm j.2) inter_subset_left) fun z hz ↦ hz.2
    have hτy : (j.1 ∘ i.1.symm) y = chartAt X x x := rfl
    have hjxO : chartAt X x x ∈ j.1.target ∩ j.1.symm ⁻¹' V :=
      ⟨(chartAt X x).map_source (mem_chart_source X x), by
        change (chartAt X x).symm (chartAt X x x) ∈ V
        rw [(chartAt X x).left_inv (mem_chart_source X x)]; exact hy.2⟩
    rw [logDeriv_congr heq, logDeriv_comp hO hfj (smoothMBOn_transition i.2 j.2 1) hyD
      (by rw [hτy]; exact hjxO), hτy, hf.2 x hy.2, ← formRep_prefChart α x,
      formRep_transition α i j hyD]
    rfl

omit [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [T2Space X] in
/-- A partial derivative of a map on a product. -/
theorem dMB_slice {F' : Type*} [AddCommGroup F'] [Module ℝ F'] [TopologicalSpace F']
    (g : X × X → F') (z h k : X) : dMB g ((z, h), (k, 0)) = dMB (fun q ↦ g (q, h)) (z, k) := by
  simp only [dMB, Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero]

/-- **Logarithmic derivatives satisfy the Maurer–Cartan equation** ([GN26, Lemma 5.5.5], on
manifolds; the "only if" part of [GN26, Theorem 6.1.13(i)]). -/
theorem isMaurerCartan_of_logDeriv {f : M → G} (hf : SmoothMBM X E f)
    (hδ : ∀ x h, logDeriv E (f ∘ (chartAt X x).symm) (chartAt X x x) h = α x fun _ ↦ h) :
    IsMaurerCartan G α := by
  intro x z hz h k
  set i := prefChart (E := X) x
  have hP := IsLogPrimitiveM.comp_symm α isOpen_univ ⟨hf, fun y _ h ↦ hδ y h⟩ i
  have hW : IsOpen (i.1.target ∩ i.1.symm ⁻¹' univ) := i.1.isOpen_inter_preimage_symm isOpen_univ
  have hzW : z ∈ i.1.target ∩ i.1.symm ⁻¹' univ := ⟨hz, mem_univ _⟩
  have he : ∀ v, (fun q ↦ formRep α i (q, v)) =ᶠ[𝓝 z]
      fun q ↦ logDeriv E (f ∘ i.1.symm) q v := fun v ↦ by
    filter_upwards [hW.mem_nhds hzW] with q hq
    exact (hP.2 q hq v).symm
  rw [dMB_slice, dMB_slice, dMB_congr_of_eventuallyEq (he h), dMB_congr_of_eventuallyEq (he k),
    (he h).eq_of_nhds, (he k).eq_of_nhds]
  exact logDeriv_maurerCartan hW hP.1 hzW h k

/-- **The system of primitives of `α`**, with the basic open sets `c⁻¹(C)` for `C` convex open in
the range of a preferred chart `c`. -/
def primSystem : PrimSystem M G where
  prim V f := IsOpen V ∧ IsLogPrimitiveM E α f V
  basic := {V | ∃ x C, IsOpen C ∧ Convex ℝ C ∧ C ⊆ (chartAt X x).target ∧
    V = (chartAt X x).source ∩ chartAt X x ⁻¹' C}
  isOpen_basic := by
    rintro _ ⟨x, C, hC, -, -, rfl⟩
    exact (chartAt X x).isOpen_inter_preimage hC
  exists_basic := by
    intro W x hW hxW
    set c := chartAt X x
    obtain ⟨C, hC, hCc, hcxC, hCsub⟩ := exists_convex_open (c.isOpen_inter_preimage_symm hW)
      ⟨c.map_source (mem_chart_source X x), by
        change c.symm (c x) ∈ W; rw [c.left_inv (mem_chart_source X x)]; exact hxW⟩
    refine ⟨_, ⟨x, C, hC, hCc, fun y hy ↦ (hCsub hy).1, rfl⟩, ⟨mem_chart_source X x, hcxC⟩,
      fun z hz ↦ ?_⟩
    have := (hCsub hz.2).2
    rwa [mem_preimage, c.left_inv hz.1] at this
  mono hf hW hWV := ⟨hW, fun k ↦ (hf.2.1 k).mono' hWV, fun x hx h ↦ hf.2.2 x (hWV hx) h⟩
  mul_left g hf := ⟨hf.1, fun k ↦ ContMDiffMBOn.comp (g := fun x : G ↦ g * x) hf.1 isOpen_univ
      (smoothMBM_mul_left (E := E) g k) (hf.2.1 k) (mapsTo_univ _ _),
    fun x hx h ↦ (logDeriv_mul_left _ g _ h).trans (hf.2.2 x hx h)⟩
  eqOn := by
    rintro _ f₁ f₂ x₁ ⟨x, C, hC, hCc, hCt, rfl⟩ h₁ h₂ hx heq
    set c := chartAt X x
    have hsub : C ⊆ c.target ∩ c.symm ⁻¹' (c.source ∩ c ⁻¹' C) := fun y hy ↦
      ⟨hCt hy, c.map_target (hCt hy), by
        change c (c.symm y) ∈ C; rw [c.right_inv (hCt hy)]; exact hy⟩
    have h₁' := (h₂.2.comp_symm α h₂.1 (prefChart (E := X) x)).mono hsub
    have h₀' := (h₁.2.comp_symm α h₁.1 (prefChart (E := X) x)).mono hsub
    have he := h₀'.eqOn hC hCc h₁' hx.2 (by
      change f₁ (c.symm (c x₁)) = f₂ (c.symm (c x₁))
      rw [c.left_inv hx.1, heq])
    intro z hz
    have := he hz.2
    change f₁ (c.symm (c z)) = f₂ (c.symm (c z)) at this
    rwa [c.left_inv hz.1] at this
  of_local := by
    intro V f hV hloc
    refine ⟨hV, fun k ↦ ContMDiffMBOn.of_local hV fun x hx ↦ ?_, fun x hx h ↦ ?_⟩
    · obtain ⟨W, hW, hxW, f', hf', heq⟩ := hloc x hx
      exact ⟨W, hW, hxW, ContMDiffMBOn.congr' hW (hf'.2.1 k) heq⟩
    · obtain ⟨W, hW, hxW, f', hf', heq⟩ := hloc x hx
      set c := chartAt X x
      have hev : f ∘ c.symm =ᶠ[𝓝 (c x)] f' ∘ c.symm := by
        have hc : ContinuousAt c.symm (c x) :=
          c.continuousAt_symm (c.map_source (mem_chart_source X x))
        have : c.symm ⁻¹' W ∈ 𝓝 (c x) := hc.preimage_mem_nhds (by
          rw [c.left_inv (mem_chart_source X x)]; exact hW.mem_nhds hxW)
        filter_upwards [this] with y hy
        exact heq hy
      rw [logDeriv_congr hev]
      exact hf'.2.2 x hxW h

/-- **Primitives of `α` exist on the basic open sets**, if `G` is `C⁰`-regular and `α` satisfies
the Maurer–Cartan equation. -/
theorem hasPrim_primSystem (hG : IsC0Regular E G) (hMC : IsMaurerCartan G α) :
    (primSystem (G := G) α).HasPrim := by
  rintro _ ⟨x, C, hC, hCc, hCt, rfl⟩
  set i := prefChart (E := X) x
  rcases C.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
  · refine ⟨fun _ ↦ 1, by simp, fun k ↦ ?_, fun z hz ↦ by simp at hz⟩
    simp only [preimage_empty, inter_empty]
    exact ⟨continuousOn_empty _, fun z hz ↦ hz.elim⟩
  obtain ⟨F, hF, -⟩ := exists_isLogPrimitive (X := X) hG (U := i.1.target)
    (smoothMBOn_formRep α i) (fun z hz h k ↦ formRep_add α i hz h k)
    (fun z hz c h ↦ formRep_smul α i hz c h) (hMC x) hC hCc hCt hy
  exact ⟨F ∘ i.1, i.1.isOpen_inter_preimage hC, isLogPrimitiveM_comp α i hC hF⟩

/-- **The Fundamental Theorem for Lie group-valued functions on manifolds** ([GN26, Theorem
6.1.13], (i) and (ii)(a)): on a simply connected manifold `M`, a `𝔤`-valued `1`-form `α`
satisfying the Maurer–Cartan equation is the logarithmic derivative of a smooth `f : M → G`, with
`f(x₀) = 1`, if `G` is `C⁰`-regular. -/
theorem exists_logDeriv_eq_of_simplyConnected_manifold (hG : IsC0Regular E G)
    (hMC : IsMaurerCartan G α) [SimplyConnectedSpace M] (x₀ : M) :
    ∃ f : M → G, SmoothMBM X E f ∧ f x₀ = 1 ∧
      ∀ x h, logDeriv E (f ∘ (chartAt X x).symm) (chartAt X x x) h = α x fun _ ↦ h := by
  have : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace X M
  obtain ⟨f, ⟨-, hf⟩, hf0⟩ := (primSystem (G := G) α).exists_prim_univ
    (hasPrim_primSystem α hG hMC) x₀ 1
  exact ⟨f, hf.1, hf0, fun x h ↦ hf.2 x (mem_univ x) h⟩

/-- **Uniqueness**: on a connected manifold, primitives agreeing at one point are equal. -/
theorem eq_of_logDeriv_eq [PreconnectedSpace M] {f₁ f₂ : M → G}
    (h₁ : SmoothMBM X E f₁) (h₁' : ∀ x h, logDeriv E (f₁ ∘ (chartAt X x).symm) (chartAt X x x) h =
      α x fun _ ↦ h)
    (h₂ : SmoothMBM X E f₂) (h₂' : ∀ x h, logDeriv E (f₂ ∘ (chartAt X x).symm) (chartAt X x x) h =
      α x fun _ ↦ h) {x₀ : M} (h₀ : f₁ x₀ = f₂ x₀) : f₁ = f₂ :=
  (primSystem (G := G) α).eqOn_univ ⟨isOpen_univ, h₁, fun x _ h ↦ h₁' x h⟩
    ⟨isOpen_univ, h₂, fun x _ h ↦ h₂' x h⟩ h₀

/-- **The period homomorphism of `α`** at `x₀` ([GN26, Definition 6.1.12]): the monodromy of the
covering of germs of primitives of `α`, on the germ `(x₀, 1)`. With Mathlib's convention for the
fundamental group, it takes values in `Gᵐᵒᵖ`. -/
def perForm (hG : IsC0Regular E G) (hMC : IsMaurerCartan G α) (x₀ : M) :
    FundamentalGroup M x₀ →* Gᵐᵒᵖ :=
  (primSystem (G := G) α).per (hasPrim_primSystem α hG hMC) x₀

/-- **`α` is integrable if and only if its periods vanish** ([GN26, Theorem 6.1.13(ii)(b)]), on a
connected manifold, for `G` `C⁰`-regular and `α` satisfying the Maurer–Cartan equation. -/
theorem exists_logDeriv_eq_iff_perForm_eq_one (hG : IsC0Regular E G) (hMC : IsMaurerCartan G α)
    [ConnectedSpace M] (x₀ : M) :
    (∃ f : M → G, SmoothMBM X E f ∧
      ∀ x h, logDeriv E (f ∘ (chartAt X x).symm) (chartAt X x x) h = α x fun _ ↦ h) ↔
      perForm α hG hMC x₀ = 1 := by
  have : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace X M
  have : PathConnectedSpace M := pathConnectedSpace_iff_connectedSpace.2 ‹_›
  rw [perForm, ← PrimSystem.exists_prim_univ_iff_per_eq_one]
  constructor
  · rintro ⟨f, hf, hδ⟩
    exact ⟨f, isOpen_univ, hf, fun x _ h ↦ hδ x h⟩
  · rintro ⟨f, -, hf⟩
    exact ⟨f, hf.1, fun x h ↦ hf.2 x (mem_univ x) h⟩

end Manifold

end LocallyConvex.LieGroups.MBLieGroup
