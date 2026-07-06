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

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex

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

abbrev cupCochain (m n r : ℕ) (hr : r = m + n) :
    (homogeneousCochains (.of ρ1)).X m ⟶ TopModuleCat.linHom ((homogeneousCochains (.of ρ2)).X n)
      ((homogeneousCochains (.of ρ3)).X r) :=
  (invariantsFunctor k G).map (cupComplex ρ1 ρ2 ρ3 f m n r hr) ≫
    invariantsObjIHom ρ2 ρ3 n r

def cup (m n r : ℕ) (hr : r = m + n) :
  continuousCohomology m (.of ρ1) →L[k] continuousCohomology n (.of ρ2) →L[k]
    continuousCohomology r (.of ρ3) := sorry

end Cup

end ContRepresentation
