/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib

/-!
# Cup products in continuous group cohomology

This file constructs the cup product pairing on the coinduced resolutions computing continuous
group cohomology.

## Main definitions

* `ContRepresentation.linHom ρ2 ρ3`: the continuous representation of `G` on `M2 →L[k] M3` by
  conjugation, `g • φ = ρ3 g ∘L φ ∘L ρ2 g⁻¹`, where `M2 →L[k] M3` carries the topology induced
  from the compact-open topology on `C(M2, M3)`.
* `ContinuousMap.continuous_prodMk_of_discrete`: the pairing `C(α, β) × C(α, δ) → C(α, β × δ)`
  is continuous when `δ` is discrete, without any local compactness assumption on `α`.
* `ContRepresentation.resolutionCLM ρ2 ρ3 u i`: the functorial extension of a (not necessarily
  equivariant) continuous linear map `u : M2 →L[k] M3` to the `i`-th level of the standard
  resolutions.
* `ContRepresentation.cupZeroSucc f n`: the degree-`(0, n)` cup product pairing on the coinduced
  resolutions induced by an intertwining map `f : ρ1 →ⁱL linHom ρ2 ρ3`.
* `ContRepresentation.cupSucc F hF`: the inductive step of the cup product, turning an
  intertwining map `π₁ →ⁱL linHom π₂ π₃` with jointly continuous underlying pairing into an
  intertwining map `π₁.coind₁ →ⁱL linHom π₂ π₃.coind₁`.
* `ContRepresentation.cupComplex`: the degree-`(m, n)` cup product pairing on the coinduced
  resolutions, as a morphism `(resolution' (of ρ1)).X m ⟶ iHom ((resolution' (of ρ2)).X n)
  ((resolution' (of ρ3)).X (m + n))`.

## Main results

* `ContRepresentation.cupPair_d_comm` and `ContRepresentation.cup_d_comm`: the Leibniz rule
  `d (σ ∪ τ) = (d σ) ∪ τ + (-1) ^ m • (σ ∪ d τ)` for the cup product, on the resolutions and on
  homogeneous cochains respectively.

## TODO

* Use `ContRepresentation.cupComplex` to define the cup product `ContRepresentation.cup` on
  continuous cohomology.
* Minimise the imports once the constructions are complete.
-/

@[expose] public section

universe u v w

namespace TopCup

variable {k : Type u} {M1 M2 : Type w} [CommRing k] [TopologicalSpace k]
  [AddCommGroup M1] [Module k M1] [TopologicalSpace M1] [IsTopologicalAddGroup M1]
  [AddCommGroup M2] [Module k M2] [TopologicalSpace M2] [IsTopologicalAddGroup M2]

scoped instance : TopologicalSpace (M1 →L[k] M2) :=
  TopologicalSpace.induced (fun f ↦ ⟨f.toFun, f.cont⟩ : (M1 →L[k] M2) → C(M1, M2)) inferInstance

scoped instance : IsTopologicalAddGroup (M1 →L[k] M2) :=
  Topology.IsInducing.topologicalAddGroup
    ({ toFun f := ⟨f, f.cont⟩
       map_zero' := rfl
       map_add' _ _ := rfl } : (M1 →L[k] M2) →+ C(M1, M2)) ⟨rfl⟩

scoped instance [ContinuousSMul k M2] :
    ContinuousSMul k (M1 →L[k] M2) :=
  Topology.IsInducing.continuousSMul (X := C(M1, M2)) ⟨rfl⟩ continuous_id rfl

end TopCup

namespace TopModuleCat

open TopCup

variable {k : Type u} [CommRing k] [TopologicalSpace k]

abbrev linHom (M1 M2 : TopModuleCat k) : TopModuleCat k := .of k (M1 →L[k] M2)

end TopModuleCat

open ContinuousMap Set Topology in
/-- The pairing map `C(α, β) × C(α, δ) → C(α, β × δ)` is continuous in the compact-open
topologies when `δ` is discrete. No local compactness of `α` is required: a continuous map into a
discrete space takes finitely many values on a compact set, so on each compact set the maps close
to `g` in `C(α, δ)` agree with `g`. -/
lemma ContinuousMap.continuous_prodMk_of_discrete {α β δ : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [TopologicalSpace δ] [DiscreteTopology δ] :
    Continuous fun p : C(α, β) × C(α, δ) ↦ p.1.prodMk p.2 := by
  simp_rw [continuous_iff_continuousAt, ContinuousAt, tendsto_nhds_compactOpen]
  rintro ⟨f, g⟩ K hK U hU hfg
  have key : ∀ c ∈ g '' K, ∀ᶠ p : C(α, β) × C(α, δ) in 𝓝 (f, g),
      MapsTo p.1 (K ∩ g ⁻¹' {c}) {y | (y, c) ∈ U} ∧ MapsTo p.2 (K ∩ g ⁻¹' {c}) {c} := by
    intro c _
    have hKc : IsCompact (K ∩ g ⁻¹' {c}) :=
      hK.inter_right ((isClosed_discrete _).preimage g.continuous)
    have h1 : ∀ᶠ f' : C(α, β) in 𝓝 f, MapsTo f' (K ∩ g ⁻¹' {c}) {y | (y, c) ∈ U} :=
      eventually_mapsTo hKc (hU.preimage (continuous_id.prodMk continuous_const))
        fun x hx ↦ by simpa [show g x = c from hx.2] using hfg hx.1
    have h2 : ∀ᶠ g' : C(α, δ) in 𝓝 g, MapsTo g' (K ∩ g ⁻¹' {c}) {c} :=
      eventually_mapsTo hKc (isOpen_discrete _) fun x hx ↦ hx.2
    rw [nhds_prod_eq]
    exact (Filter.tendsto_fst.eventually h1).and (Filter.tendsto_snd.eventually h2)
  have hfin : (g '' K).Finite := (hK.image g.continuous).finite_of_discrete
  filter_upwards [(Filter.eventually_all_finite hfin).2 key] with p hp x hxK
  obtain ⟨h1, h2⟩ := hp (g x) (mem_image_of_mem g hxK)
  have hx : x ∈ K ∩ g ⁻¹' {g x} := ⟨hxK, rfl⟩
  simpa [show p.2 x = g x from h2 hx] using h1 hx

open Topology in
/-- A map on `X × D` with `D` discrete is continuous as soon as all its slices `x ↦ g (x, d)`
are continuous. -/
lemma continuous_of_discreteTopology_snd {X D Y : Type*} [TopologicalSpace X]
    [TopologicalSpace D] [DiscreteTopology D] [TopologicalSpace Y] {g : X × D → Y}
    (hg : ∀ d, Continuous fun x ↦ g (x, d)) : Continuous g := by
  simp_rw [continuous_iff_continuousAt, ContinuousAt]
  rintro ⟨x, d⟩
  rw [nhds_prod_eq, nhds_discrete D, Filter.prod_pure]
  exact Filter.tendsto_map'_iff.mp ((hg d).tendsto x)

open CategoryTheory TopCup

namespace ContRepresentation

variable {k : Type u} {G : Type v} [CommRing k] [TopologicalSpace k] [Group G]

section LinHom

variable {M2 M3 : Type w}
  [AddCommGroup M2] [Module k M2] [TopologicalSpace M2] [IsTopologicalAddGroup M2]
  [AddCommGroup M3] [Module k M3] [TopologicalSpace M3] [IsTopologicalAddGroup M3]
  [ContinuousSMul k M3] (ρ2 : ContRepresentation k G M2) (ρ3 : ContRepresentation k G M3)

/-- The continuous representation of `G` on `M2 →L[k] M3` by conjugation,
`g • φ = ρ3 g ∘L φ ∘L ρ2 g⁻¹`, where `M2 →L[k] M3` carries the topology induced from the
compact-open topology on `C(M2, M3)`. -/
def linHom : ContRepresentation k G (M2 →L[k] M3) where
  toMonoidHom.toFun g := {
    toFun f := ρ3 g ∘L f ∘L ρ2 g⁻¹
    map_add' _ _ := by ext; simp
    map_smul' _ _ := by ext; simp
    cont := by
      refine continuous_induced_rng.2 ?_
      change Continuous fun f : M2 →L[k] M3 ↦
        (ρ3 g : C(M3, M3)).comp ((⟨f.toFun, f.cont⟩ : C(M2, M3)).comp (ρ2 g⁻¹ : C(M2, M2)))
      exact ((ρ3 g : C(M3, M3)).continuous_postcomp).comp
        (((ρ2 g⁻¹ : C(M2, M2)).continuous_precomp).comp continuous_induced_dom) }
  toMonoidHom.map_one' := by ext; simp
  toMonoidHom.map_mul' g₁ g₂ := by ext; simp

@[simp]
lemma linHom_apply (g : G) (φ : M2 →L[k] M3) :
    linHom ρ2 ρ3 g φ = ρ3 g ∘L φ ∘L ρ2 g⁻¹ := rfl

/-- The internal hom of two topological representations: the topological representation on the
space of continuous linear maps `A →L[k] B`, with `G` acting by conjugation. -/
abbrev _root_.TopRep.iHom (A B : TopRep k G) : TopRep k G := TopRep.of (linHom A.ρ B.ρ)

end LinHom

section Cup

variable {M1 M2 M3 : Type v}
  [AddCommGroup M1] [Module k M1] [TopologicalSpace M1] [IsTopologicalAddGroup M1]
  [ContinuousSMul k M1]
  [AddCommGroup M2] [Module k M2] [TopologicalSpace M2] [IsTopologicalAddGroup M2]
  [ContinuousSMul k M2]
  [AddCommGroup M3] [Module k M3] [TopologicalSpace M3] [IsTopologicalAddGroup M3]
  [ContinuousSMul k M3]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ1 : ContRepresentation k G M1) (ρ2 : ContRepresentation k G M2)
  (ρ3 : ContRepresentation k G M3) (f : ρ1 →ⁱL linHom ρ2 ρ3)

open TopRep

/-- The functorial extension of a continuous linear map `u : M2 →L[k] M3` (not necessarily
equivariant) to the `i`-th level of the standard resolutions, applying `u` pointwise under the
iterated `C(G, ·)`. -/
def resolutionCLM (u : M2 →L[k] M3) :
    (i : ℕ) → resolutionX (of ρ2) i →L[k] resolutionX (of ρ3) i
  | 0 => u
  | i + 1 => (resolutionCLM u i).compLeftContinuous k G

@[simp]
lemma resolutionCLM_zero_apply (u : M2 →L[k] M3) (v : M2) :
    resolutionCLM ρ2 ρ3 u 0 v = u v := rfl

@[simp]
lemma resolutionCLM_succ_apply (u : M2 →L[k] M3) (i : ℕ)
    (F : resolutionX (of ρ2) (i + 1)) (g : G) :
    resolutionCLM ρ2 ρ3 u (i + 1) F g = resolutionCLM ρ2 ρ3 u i (F g) := rfl

lemma resolutionCLM_add (u w : M2 →L[k] M3) (i : ℕ) :
    resolutionCLM ρ2 ρ3 (u + w) i = resolutionCLM ρ2 ρ3 u i + resolutionCLM ρ2 ρ3 w i := by
  induction i with
  | zero => rfl
  | succ i ih => ext F g; exact congr($(ih) (F g))

lemma resolutionCLM_smul (c : k) (u : M2 →L[k] M3) (i : ℕ) :
    resolutionCLM ρ2 ρ3 (c • u) i = c • resolutionCLM ρ2 ρ3 u i := by
  induction i with
  | zero => rfl
  | succ i ih => ext F g; exact congr($(ih) (F g))

/-- Conjugating `u : M2 →L[k] M3` by the representations corresponds to conjugating
`resolutionCLM u` by the coinduced actions on the resolutions. -/
lemma resolutionCLM_conj (h : G) (u : M2 →L[k] M3) (i : ℕ) :
    resolutionCLM ρ2 ρ3 (ρ3 h ∘L u ∘L ρ2 h⁻¹) i =
      (resolutionX (of ρ3) i).ρ h ∘L resolutionCLM ρ2 ρ3 u i ∘L
        (resolutionX (of ρ2) i).ρ h⁻¹ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    ext F g
    change resolutionCLM ρ2 ρ3 (ρ3 h ∘L u ∘L ρ2 h⁻¹) i (F g) =
      (resolutionX (of ρ3) i).ρ h (resolutionCLM ρ2 ρ3 u i
        ((resolutionX (of ρ2) i).ρ h⁻¹ (F ((h⁻¹)⁻¹ * (h⁻¹ * g)))))
    rw [inv_inv, mul_inv_cancel_left]
    exact congr($(ih) (F g))

section CupSucc

variable {V W2 W3 : Type v}
  [AddCommGroup V] [Module k V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul k V]
  [AddCommGroup W2] [Module k W2] [TopologicalSpace W2] [IsTopologicalAddGroup W2]
  [AddCommGroup W3] [Module k W3] [TopologicalSpace W3] [IsTopologicalAddGroup W3]
  [ContinuousSMul k W3]
  {π₁ : ContRepresentation k G V} {π₂ : ContRepresentation k G W2}
  {π₃ : ContRepresentation k G W3}

/-- The inductive step of the cup product: an intertwining map `F : π₁ →ⁱL linHom π₂ π₃` whose
underlying pairing `(v, w) ↦ F v w` is jointly continuous induces an intertwining map
`π₁.coind₁ →ⁱL linHom π₂ π₃.coind₁` sending `σ` and `τ` to `x ↦ F (σ x) τ`.

The joint continuity hypothesis `hF` cannot be dropped: for a general `F` the continuity of
`τ ↦ (x ↦ F (σ x) τ)` would require an equicontinuity property of `F` on compact subsets of
`C(G, V)`. It is preserved by this construction (`continuous_cupSucc_uncurry`), which allows the
construction to be iterated. -/
def cupSucc (F : π₁ →ⁱL linHom π₂ π₃)
    (hF : Continuous fun p : V × W2 ↦ F p.1 p.2) :
    π₁.coind₁ →ⁱL linHom π₂ π₃.coind₁ where
  toFun σ := {
    toFun τ := ⟨fun x ↦ F (σ x) τ, hF.comp (σ.continuous.prodMk continuous_const)⟩
    map_add' τ₁ τ₂ := by ext x; exact map_add (F (σ x)) τ₁ τ₂
    map_smul' c τ := by ext x; exact map_smul (F (σ x)) c τ
    cont := ((⟨fun p ↦ F p.1 p.2, hF⟩ : C(V × W2, W3)).continuous_postcomp).comp <|
      (ContinuousMap.prodSwap.continuous_postcomp).comp <|
        ContinuousMap.continuous_prodMk_const.comp (continuous_id.prodMk continuous_const) }
  map_add' σ₁ σ₂ := by ext τ x; exact congr($(map_add F (σ₁ x) (σ₂ x)) τ)
  map_smul' c σ := by ext τ x; exact congr($(map_smul F c (σ x)) τ)
  cont := by
    refine continuous_induced_rng.2 (ContinuousMap.continuous_of_continuous_uncurry _ ?_)
    exact ((⟨fun p ↦ F p.1 p.2, hF⟩ : C(V × W2, W3)).continuous_postcomp).comp
      ((ContinuousMap.prodSwap.continuous_postcomp).comp
        (ContinuousMap.continuous_prodMk_const.comp (continuous_snd.prodMk continuous_fst)))
  isIntertwining' h := by ext σ τ x; simp [F.isIntertwining]

@[simp]
lemma cupSucc_apply_apply (F : π₁ →ⁱL linHom π₂ π₃)
    (hF : Continuous fun p : V × W2 ↦ F p.1 p.2) (σ : C(G, V)) (τ : W2) (x : G) :
    cupSucc F hF σ τ x = F (σ x) τ := rfl

/-- The uncurried pairing of `cupSucc F hF` is again jointly continuous, so `cupSucc` can be
iterated. -/
lemma continuous_cupSucc_uncurry (F : π₁ →ⁱL linHom π₂ π₃)
    (hF : Continuous fun p : V × W2 ↦ F p.1 p.2) :
    Continuous fun p : C(G, V) × W2 ↦ cupSucc F hF p.1 p.2 :=
  ((⟨fun p ↦ F p.1 p.2, hF⟩ : C(V × W2, W3)).continuous_postcomp).comp
    ((ContinuousMap.prodSwap.continuous_postcomp).comp
      (ContinuousMap.continuous_prodMk_const.comp (continuous_snd.prodMk continuous_fst)))

end CupSucc

variable [DiscreteTopology M1]

section

variable {ρ1 ρ2 ρ3}

/-- The pairing `resolutionX (of ρ2) n × M1 → resolutionX (of ρ3) n` underlying the cup product,
sending `(y, v)` to `resolutionCLM (f v) n y`, as a continuous map. -/
def cupZeroSuccAux (n : ℕ) : C(resolutionX (of ρ2) n × M1, resolutionX (of ρ3) n) :=
  ⟨fun p ↦ resolutionCLM ρ2 ρ3 (f p.2) n p.1,
    continuous_of_discreteTopology_snd fun v ↦ (resolutionCLM ρ2 ρ3 (f v) n).continuous⟩

/-- The degree-`(0, n)` cup product pairing: an intertwining map `f : ρ1 →ⁱL linHom ρ2 ρ3` pairs
a degree-`0` cochain `σ` with a degree-`n` cochain `τ` by
`(σ ∪ τ) g = resolutionCLM (f (σ g)) n (τ g)`, intertwining the coinduced representations. -/
def cupZeroSucc (n : ℕ) :
    ρ1.coind₁ →ⁱL linHom (resolutionX (of ρ2) (n + 1)).ρ (resolutionX (of ρ3) (n + 1)).ρ where
  toFun σ := {
    toFun τ := ⟨fun g ↦ resolutionCLM ρ2 ρ3 (f (σ g)) n (τ g),
      (cupZeroSuccAux f n).continuous.comp (τ.continuous.prodMk σ.continuous)⟩
    map_add' τ₁ τ₂ := by ext g; exact map_add (resolutionCLM ρ2 ρ3 (f (σ g)) n) _ _
    map_smul' c τ := by ext g; exact map_smul (resolutionCLM ρ2 ρ3 (f (σ g)) n) c _
    cont := ((cupZeroSuccAux f n).continuous_postcomp).comp <|
      ContinuousMap.continuous_prodMk_of_discrete.comp <|
        continuous_id.prodMk continuous_const }
  map_add' σ₁ σ₂ := by ext τ g; simp [resolutionCLM_add]
  map_smul' c σ := by ext τ g; simp [resolutionCLM_smul]
  cont := by
    refine continuous_induced_rng.2 (ContinuousMap.continuous_of_continuous_uncurry _ ?_)
    exact ((cupZeroSuccAux f n).continuous_postcomp).comp
      (ContinuousMap.continuous_prodMk_of_discrete.comp (continuous_snd.prodMk continuous_fst))
  isIntertwining' h := by ext σ τ g; simp [f.isIntertwining, resolutionCLM_conj]

@[simp]
lemma cupZeroSucc_apply_apply (n : ℕ) (σ : C(G, M1)) (τ : C(G, resolutionX (of ρ2) n))
    (g : G) : cupZeroSucc f n σ τ g = resolutionCLM ρ2 ρ3 (f (σ g)) n (τ g) := rfl

/-- The uncurried pairing of `cupZeroSucc f n` is jointly continuous, so `cupSucc` applies
to it. -/
lemma continuous_cupZeroSucc_uncurry (n : ℕ) :
    Continuous fun p : C(G, M1) × C(G, resolutionX (of ρ2) n) ↦ cupZeroSucc f n p.1 p.2 :=
  ((cupZeroSuccAux f n).continuous_postcomp).comp
    (ContinuousMap.continuous_prodMk_of_discrete.comp (continuous_snd.prodMk continuous_fst))

/-- The degree-`(m, n)` cup product pairing on the coinduced resolutions, defined by iterating
`cupSucc` starting from `cupZeroSucc`, bundled with the joint continuity of its underlying
pairing (which is needed to keep iterating). -/
def cupPair (n : ℕ) : (m : ℕ) →
    { F : (resolutionX (of ρ1) (m + 1)).ρ →ⁱL
        linHom (resolutionX (of ρ2) (n + 1)).ρ (resolutionX (of ρ3) (n + 1 + m)).ρ //
      Continuous fun p : ↥(resolutionX (of ρ1) (m + 1)) × ↥(resolutionX (of ρ2) (n + 1)) ↦
        F p.1 p.2 }
  | 0 => ⟨cupZeroSucc f n, continuous_cupZeroSucc_uncurry f n⟩
  | m + 1 =>
    ⟨cupSucc (cupPair n m).1 (cupPair n m).2,
      continuous_cupSucc_uncurry (cupPair n m).1 (cupPair n m).2⟩

end

def cupComplex (m n r : ℕ) (hr : r = m + n) :
    (TopRep.resolution' (.of ρ1)).X m ⟶
      iHom ((TopRep.resolution' (.of ρ2)).X n) ((TopRep.resolution' (.of ρ3)).X r) :=
  (TopRep.ofHom (cupPair f n m).1 :
      _ ⟶ ((TopRep.of ρ2).resolution'.X n).iHom (TopRep.resolutionX (.of ρ3) (n + 1 + m))) ≫
    eqToHom (by subst hr; rw [show n + 1 + m = m + n + 1 from by omega])

/-- Transport between two levels of the standard resolution along an equality of indices, as a
continuous linear map. -/
def resolutionXCast (X : TopRep k G) {i j : ℕ} (h : i = j) :
    ↥(resolutionX X i) →L[k] ↥(resolutionX X j) :=
  h ▸ ContinuousLinearMap.id k ↥(resolutionX X i)

lemma resolutionXCast_apply (X : TopRep k G) {i j : ℕ} (h : i + 1 = j + 1)
    (F : ↥(resolutionX X (i + 1))) (x : G) :
    resolutionXCast X h F x = resolutionXCast X (by omega : i = j) (F x) := by
  obtain rfl : i = j := by omega
  rfl

lemma resolutionXCast_trans (X : TopRep k G) {i j l : ℕ} (h1 : i = j) (h2 : j = l)
    (y : ↥(resolutionX X i)) :
    resolutionXCast X h2 (resolutionXCast X h1 y) = resolutionXCast X (h1.trans h2) y := by
  subst h1; subst h2; rfl

lemma d_hom_resolutionXCast (X : TopRep k G) {i j : ℕ} (h : i = j) (y : ↥(resolutionX X i)) :
    (d X j).hom (resolutionXCast X h y) =
      resolutionXCast X (by omega : i + 1 = j + 1) ((d X i).hom y) := by
  subst h; rfl

/-- The zeroth differential of the standard resolution is the constant-function embedding. -/
lemma d_hom_zero (X : TopRep k G) (v : ↥X) :
    (d X 0).hom v = ContinuousMap.const G v := rfl

/-- The pointwise formula for the differentials of the standard resolution. -/
lemma d_hom_succ_apply (X : TopRep k G) (i : ℕ) (F : ↥(resolutionX X (i + 1))) (x : G) :
    (d X (i + 1)).hom F x = F - (d X i).hom (F x) := rfl

/-- The differentials of the standard resolutions are compatible with the functorial extension
`resolutionCLM` of a continuous linear map. -/
lemma resolutionCLM_comp_d (u : M2 →L[k] M3) (i : ℕ) (y : ↥(resolutionX (of ρ2) i)) :
    (d (of ρ3) i).hom (resolutionCLM ρ2 ρ3 u i y) =
      resolutionCLM ρ2 ρ3 u (i + 1) ((d (of ρ2) i).hom y) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    ext x : 1
    calc (d (of ρ3) (i + 1)).hom (resolutionCLM ρ2 ρ3 u (i + 1) y) x
        = resolutionCLM ρ2 ρ3 u (i + 1) y -
            (d (of ρ3) i).hom (resolutionCLM ρ2 ρ3 u i (y x)) := by
          rw [d_hom_succ_apply, resolutionCLM_succ_apply]
      _ = resolutionCLM ρ2 ρ3 u (i + 1) y -
            resolutionCLM ρ2 ρ3 u (i + 1) ((d (of ρ2) i).hom (y x)) := by rw [ih]
      _ = resolutionCLM ρ2 ρ3 u (i + 1) (y - (d (of ρ2) i).hom (y x)) := (map_sub _ _ _).symm
      _ = resolutionCLM ρ2 ρ3 u (i + 1 + 1) ((d (of ρ2) (i + 1)).hom y) x := by
          rw [resolutionCLM_succ_apply, d_hom_succ_apply, map_sub]

section

variable {ρ1 ρ2 ρ3}

@[simp]
lemma cupPair_zero (n : ℕ) : (cupPair f n 0).1 = cupZeroSucc f n := rfl

@[simp]
lemma cupPair_succ_apply (n m : ℕ) (σ : ↥(resolutionX (of ρ1) (m + 1 + 1)))
    (τ : ↥(resolutionX (of ρ2) (n + 1))) (x : G) :
    (cupPair f n (m + 1)).1 σ τ x = (cupPair f n m).1 (σ x) τ := rfl

/-- Cupping with a constant `0`-cochain acts through the functorial extension of `f v`. -/
lemma cupZeroSucc_const_apply (n : ℕ) (v : M1) (τ : ↥(resolutionX (of ρ2) (n + 1))) :
    cupZeroSucc f n (ContinuousMap.const G v) τ = resolutionCLM ρ2 ρ3 (f v) (n + 1) τ := rfl

/-- The Leibniz rule for the cup product pairing on the levels of the standard resolutions:
`d (σ ∪ τ) = (d σ) ∪ τ + (-1) ^ m • (σ ∪ d τ)`. -/
lemma cupPair_d_comm (n m : ℕ) (σ : ↥(resolutionX (of ρ1) (m + 1)))
    (τ : ↥(resolutionX (of ρ2) (n + 1))) :
    (d (of ρ3) (n + 1 + m)).hom ((cupPair f n m).1 σ τ) =
      (cupPair f n (m + 1)).1 ((d (of ρ1) (m + 1)).hom σ) τ +
        (-1 : ℤ) ^ m • resolutionXCast (.of ρ3) (by omega : n + 1 + 1 + m = n + 1 + m + 1)
          ((cupPair f (n + 1) m).1 σ ((d (of ρ2) (n + 1)).hom τ)) := by
  induction m with
  | zero =>
    ext x : 1
    change (cupPair f n 0).1 σ τ -
        (d (of ρ3) n).hom (resolutionCLM ρ2 ρ3 (f (σ x)) n (τ x)) =
      (cupPair f n 0).1 ((d (of ρ1) 1).hom σ x) τ +
        (-1 : ℤ) ^ 0 • (resolutionXCast (.of ρ3) (by omega : n + 1 + 1 + 0 = n + 1 + 0 + 1)
          ((cupPair f (n + 1) 0).1 σ ((d (of ρ2) (n + 1)).hom τ))) x
    have h1 : (d (of ρ1) 1).hom σ x = σ - ContinuousMap.const G (σ x) := by
      rw [d_hom_succ_apply, d_hom_zero]
    -- The reindexing cast on the left is along a definitional equality, so it evaluates away.
    have h2 : (resolutionXCast (.of ρ3) (by omega : n + 1 + 1 + 0 = n + 1 + 0 + 1)
        ((cupPair f (n + 1) 0).1 σ ((d (of ρ2) (n + 1)).hom τ))) x =
        resolutionCLM ρ2 ρ3 (f (σ x)) (n + 1) ((d (of ρ2) (n + 1)).hom τ x) := rfl
    have h3 : (cupPair f n 0).1 (ContinuousMap.const G (σ x)) τ =
        resolutionCLM ρ2 ρ3 (f (σ x)) (n + 1) τ := by
      rw [cupPair_zero, cupZeroSucc_const_apply]
    rw [h1, h2, resolutionCLM_comp_d, map_sub ((cupPair f n 0).1),
      sub_apply, h3, d_hom_succ_apply, map_sub, pow_zero, one_smul]
    abel
  | succ m ih =>
    ext x : 1
    change (cupPair f n (m + 1)).1 σ τ -
        (d (of ρ3) (n + 1 + m)).hom ((cupPair f n m).1 (σ x) τ) =
      (cupPair f n (m + 1)).1 ((d (of ρ1) (m + 1 + 1)).hom σ x) τ +
        (-1 : ℤ) ^ (m + 1) • (resolutionXCast (.of ρ3)
          (by omega : n + 1 + 1 + (m + 1) = n + 1 + (m + 1) + 1)
          ((cupPair f (n + 1) (m + 1)).1 σ ((d (of ρ2) (n + 1)).hom τ))) x
    have h1 : (d (of ρ1) (m + 1 + 1)).hom σ x = σ - (d (of ρ1) (m + 1)).hom (σ x) :=
      d_hom_succ_apply _ _ σ x
    have h2 : (resolutionXCast (.of ρ3)
        (by omega : n + 1 + 1 + (m + 1) = n + 1 + (m + 1) + 1)
        ((cupPair f (n + 1) (m + 1)).1 σ ((d (of ρ2) (n + 1)).hom τ))) x =
        resolutionXCast (.of ρ3) (by omega : n + 1 + 1 + m = n + 1 + m + 1)
          ((cupPair f (n + 1) m).1 (σ x) ((d (of ρ2) (n + 1)).hom τ)) :=
      resolutionXCast_apply _ _ _ x
    rw [ih, h1, h2, map_sub ((cupPair f n (m + 1)).1), sub_apply,
      pow_succ, mul_comm, mul_smul, neg_one_smul]
    abel

end

abbrev invariantsObjIHom (n r : ℕ) : (invariantsFunctor k G).obj
    (((of ρ2).resolution'.X n).iHom ((of ρ3).resolution'.X r)) ⟶
    ((of ρ2).homogeneousCochains.X n).linHom ((of ρ3).homogeneousCochains.X r) :=
  TopModuleCat.ofHom {
    toFun := fun ⟨F, hF⟩ ↦ F.restrict fun x hx g ↦ by
      have h1 : ((of ρ3).resolution'.X r).ρ g (F (((of ρ2).resolution'.X n).ρ g⁻¹ x)) = F x :=
        congr($(hF g) x)
      rwa [hx g⁻¹] at h1
    map_add' _ _ := by ext x; rfl
    map_smul' _ _ := by ext x; rfl
    cont := by
      refine continuous_induced_rng.2 ?_
      refine (ContinuousMap.isInducing_postcomp
        (⟨_, continuous_subtype_val⟩ :
          C(((of ρ3).resolution'.X r).ρ.invariants, (of ρ3).resolution'.X r))
        Topology.IsInducing.subtypeVal).continuous_iff.2 ?_
      have hι : Continuous fun F : ↥((of ρ2).resolution'.X n) →L[k] ↥((of ρ3).resolution'.X r) ↦
          (⟨F.toFun, F.cont⟩ : C((of ρ2).resolution'.X n, (of ρ3).resolution'.X r)) :=
        continuous_induced_dom
      exact (ContinuousMap.continuous_precomp
        (⟨_, continuous_subtype_val⟩ :
          C(((of ρ2).resolution'.X n).ρ.invariants, (of ρ2).resolution'.X n))).comp
        (hι.comp continuous_subtype_val) }

/-- Applying the `eqToHom` reindexing morphism of `cupComplex` to elements is transport along
the index equality. -/
lemma eqToHom_iHom_apply (A : TopRep k G) {i j : ℕ} (h : i = j)
    (pf : A.iHom (resolutionX (.of ρ3) i) = A.iHom (resolutionX (.of ρ3) j))
    (Φ : ↥(A.iHom (resolutionX (.of ρ3) i))) (τ : ↥A) :
    (eqToHom pf) Φ τ = resolutionXCast (.of ρ3) h (Φ τ) := by
  subst h
  rfl

variable {ρ1 ρ2 ρ3} in
abbrev cupCochain (m n r : ℕ) (hr : r = m + n) :
    (homogeneousCochains (.of ρ1)).X m ⟶ TopModuleCat.linHom ((homogeneousCochains (.of ρ2)).X n)
      ((homogeneousCochains (.of ρ3)).X r) :=
  (invariantsFunctor k G).map (cupComplex ρ1 ρ2 ρ3 f m n r hr) ≫
    invariantsObjIHom ρ2 ρ3 n r

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex in
variable {ρ1 ρ2 ρ3} in
/-- The value of the cup product of two homogeneous cochains, as an element of the resolution. -/
lemma cupCochain_coe (m n r : ℕ) (hr : r = m + n) (σ : (homogeneousCochains (.of ρ1)).X m)
    (τ : (homogeneousCochains (.of ρ2)).X n) :
    (cupCochain f m n r hr σ τ : ↥((of ρ3).resolution'.X r)) =
      resolutionXCast (.of ρ3) (by omega : n + 1 + m = r + 1)
        ((cupPair f n m).1 σ.1 τ.1) := by
  subst hr
  exact eqToHom_iHom_apply ρ3 ((TopRep.of ρ2).resolution'.X n)
    (show n + 1 + m = m + n + 1 by omega)
    (by rw [show n + 1 + m = m + n + 1 from by omega]) ((cupPair f n m).1 σ.1) τ.1

variable {ρ1 ρ2 ρ3} in
@[simp]
lemma cupCochain_apply_zero (m n r : ℕ) (hr : r = m + n)
    (σ : (homogeneousCochains (.of ρ1)).X m) :
    cupCochain f m n r hr σ 0 = 0 :=
  map_zero (cupCochain f m n r hr σ : ↥((homogeneousCochains (.of ρ2)).X n) →L[k]
    ↥((homogeneousCochains (.of ρ3)).X r))

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex in
lemma cup_d_comm (m n r : ℕ) (hr : r = m + n) (σ : (homogeneousCochains (.of ρ1)).X m)
    (τ : (homogeneousCochains (.of ρ2)).X n) :
    (homogeneousCochains (.of ρ3)).d r (r + 1) (cupCochain f m n r hr σ τ) =
    cupCochain f (m + 1) n (r + 1) (by omega) ((homogeneousCochains (.of ρ1)).d m (m + 1) σ) τ +
    (-1) ^ m • cupCochain f m (n + 1) (r + 1) (by omega) σ
    ((homogeneousCochains (.of ρ2)).d n (n + 1) τ) := by
  subst hr
  refine Subtype.ext ?_
  rw [homogeneousCochains.d_apply, cupCochain_coe, d_hom_resolutionXCast, cupPair_d_comm,
    map_add, map_zsmul, resolutionXCast_trans, Submodule.coe_add, Submodule.coe_smul_of_tower,
    cupCochain_coe, cupCochain_coe, homogeneousCochains.d_apply, homogeneousCochains.d_apply]

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex

/-- Applying two consecutive differentials of the homogeneous cochain complex gives zero. -/
lemma _root_.TopRep.homogeneousCochains.d_comp_d_apply (X : TopRep k G) (i j l : ℕ)
    (σ : (homogeneousCochains X).X i) :
    (homogeneousCochains X).d j l ((homogeneousCochains X).d i j σ) = 0 := by
  simpa using congr($((homogeneousCochains X).d_comp_d i j l) σ)

variable {ρ1 ρ2 ρ3} in
/-- The cup product with a doubly-applied differential vanishes. -/
lemma cupCochain_d_comp_d (m i j l r : ℕ) (hr : r = m + l)
    (σ : (homogeneousCochains (.of ρ1)).X m) (τ : (homogeneousCochains (.of ρ2)).X i) :
    cupCochain f m l r hr σ
      ((homogeneousCochains (.of ρ2)).d j l ((homogeneousCochains (.of ρ2)).d i j τ)) = 0 := by
  rw [homogeneousCochains.d_comp_d_apply]
  exact map_zero (cupCochain f m l r hr σ : ↥((homogeneousCochains (.of ρ2)).X l) →L[k]
    ↥((homogeneousCochains (.of ρ3)).X r))

/-- The cup product of two coboundaries is a coboundary: `(d σ) ∪ (d τ) = d (σ ∪ d τ)`. This is
the special case of the Leibniz rule `cup_d_comm` where the second argument is a coboundary.

Note that `(d σ) ∪ (d τ)` is *not* zero in general: by the Leibniz rule it is the coboundary of
`σ ∪ d τ`. -/
lemma d_cup_d (m n r : ℕ) (hr : r = m + n) (σ : (homogeneousCochains (.of ρ1)).X m)
    (τ : (homogeneousCochains (.of ρ2)).X n) :
    cupCochain f (m + 1) (n + 1) (r + 2) (by omega) ((homogeneousCochains (.of ρ1)).d m (m + 1) σ)
      ((homogeneousCochains (.of ρ2)).d n (n + 1) τ) =
    (homogeneousCochains (.of ρ3)).d (r + 1) (r + 2) (cupCochain f m (n + 1) (r + 1) (by omega) σ
      ((homogeneousCochains (.of ρ2)).d n (n + 1) τ)) := by
  subst hr
  have h := cup_d_comm ρ1 ρ2 ρ3 f m (n + 1) (m + n + 1) (by omega) σ
    ((homogeneousCochains (.of ρ2)).d n (n + 1) τ)
  rw [cupCochain_d_comp_d] at h
  simpa only [smul_zero, add_zero] using h.symm

-- #check HomologicalComplex.cyclesMap
def cup (m n r : ℕ) (hr : r = m + n) :
  continuousCohomology m (.of ρ1) ⟶ TopModuleCat.linHom (continuousCohomology n (.of ρ2))
    (continuousCohomology r (.of ρ3)) :=
  sorry

end Cup

end ContRepresentation
