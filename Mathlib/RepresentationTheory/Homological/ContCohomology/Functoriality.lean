/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Richard Hill
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

/-!
# Functoriality of continuous cohomology

Given topological groups `G` and `H`, a continuous group homomorphism `φ : H →ₜ* G`, a topological
representation `X` of `G`, a topological representation `Y` of `H`, and a morphism of topological
`H`-representations `f : res φ X ⟶ Y`, we construct a cochain map
`homogeneousCochains X ⟶ homogeneousCochains Y` and hence maps on continuous cohomology
`Hⁿ(G, X) ⟶ Hⁿ(H, Y)`.

## Main definitions

* `ContinuousCohomology.cochainsMap φ f` : the cochain map
  `homogeneousCochains X ⟶ homogeneousCochains Y` induced by `φ : H →ₜ* G` and
  `f : res φ X ⟶ Y`, sending an invariant function `σ : C(G, C(G, ⋯))` to `f ∘ σ ∘ φ`.
* `ContinuousCohomology.map φ f n` : the induced map `Hⁿ(G, X) ⟶ Hⁿ(H, Y)` on continuous
  cohomology.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Functor

namespace ContinuousCohomology

open TopRep ContRepresentation

variable {k : Type u} {G H K : Type v} [Ring k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  {X X' X'' : TopRep k G} {Y : TopRep k H} {Z : TopRep k K}

instance (φ : H →* G) : (resFunctor (k := k) φ).Additive where

abbrev resolutionMap₁ (f : X ⟶ X') :
    (i : ℕ) → (resolutionX X i) ⟶ (resolutionX X' i)
  | 0 => f
  | i + 1 => ((coind₁Functor k G).map (resolutionMap₁ f i))

@[simp]
lemma resolutionMap₁_zero (f : X ⟶ X') : resolutionMap₁ f 0 = f := rfl

lemma resolutionMap₁_succ (f : X ⟶ X') (n : ℕ) :
    resolutionMap₁ f (n + 1) = (coind₁Functor k G).map (resolutionMap₁ f n) := rfl

/-- The maps `resolutionMap₁ f` commute with the differentials of the resolutions. -/
lemma resolutionMap₁_comp_d (f : X ⟶ X') (i : ℕ) :
    resolutionMap₁ f i ≫ d X' i = (d X i) ≫ resolutionMap₁ f (i + 1) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [d_succ, d_succ, resolutionMap₁_succ f (i + 1), Preadditive.comp_sub,
      Preadditive.sub_comp]
    congr 1
    rw [resolutionMap₁_succ f i, ← Functor.map_comp, ← Functor.map_comp, ih]

lemma resolutionMap₁_id (i : ℕ) : resolutionMap₁ (𝟙 X) i = 𝟙 (resolutionX X i) := by
  induction i with
  | zero => rw [resolutionMap₁_zero]
  | succ _ ih => rw [resolutionMap₁_succ, ih, map_id]

lemma resolutionMap₁_comp (f : X ⟶ X') (f' : X' ⟶ X'') (i : ℕ) :
    resolutionMap₁ (f ≫ f') i = (resolutionMap₁ f i) ≫ resolutionMap₁ f' i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [resolutionMap₁_succ, resolutionMap₁_succ, resolutionMap₁_succ, ih,
      map_comp]

variable (k G) in
abbrev resolution'Functor : TopRep k G ⥤ CochainComplex (TopRep k G) ℕ where
  obj           := resolution'
  map {X Y} f   := {
    f n := resolutionMap₁ f (n + 1)
    comm' := by simp +contextual [resolution'd_eq, resolutionMap₁_comp_d f _]
  }
  map_id _      := HomologicalComplex.hom_ext _ _ <| fun _ ↦ resolutionMap₁_id _
  map_comp _ _  := HomologicalComplex.hom_ext _ _ <| fun _ ↦ resolutionMap₁_comp _ _ _

variable (k G) in
abbrev homogeneousCochainsFunctor : TopRep k G ⥤ CochainComplex (TopModuleCat k) ℕ :=
    resolution'Functor k G ⋙ (invariantsFunctor k G).mapHomologicalComplex (.up ℕ)

variable (X) in
/-- The morphisms between the levels of the standard resolutions of `X` and `Y` induced by a
continuous group homomorphism `φ : H →ₜ* G` and a morphism `f : res φ X ⟶ Y`, given by
`F ↦ f ∘ F ∘ φ`. -/
abbrev _root_.TopRep.resolutionXRes (φ : H →ₜ* G) :
    (i : ℕ) → (res φ (resolutionX X i)) ⟶ (resolutionX (res φ.toMonoidHom X) i)
  | 0 => 𝟙 _
  | i + 1 => ofHom (coind₁ResMap φ (resolutionXRes φ i).hom)

@[simp]
lemma resolutionXRes_zero (φ : H →ₜ* G) : X.resolutionXRes φ 0 = 𝟙 _ := rfl

lemma resolutionXRes_one (φ : H →ₜ* G) : X.resolutionXRes φ 1 = ofHom (coind₁ResMap φ .id) := rfl

lemma resolutionXRes_succ (φ : H →ₜ* G) (i : ℕ) :
    resolutionXRes X φ (i + 1) = ofHom (coind₁ResMap φ (resolutionXRes _ φ i).hom) := rfl

@[simp]
lemma resolutionXRes_id (X : TopRep k G) (i : ℕ) :
    resolutionXRes X (ContinuousMonoidHom.id G) i = 𝟙 (resolutionX X i) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionXRes_succ, ih]
    rfl

lemma resolutionXRes_comp (φ : H →ₜ* G) (ψ : K →ₜ* H) (i : ℕ) :
    resolutionXRes X (φ.comp ψ) i =
      (resFunctor ψ.toMonoidHom).map (resolutionXRes X φ i) ≫ resolutionXRes _ ψ i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionXRes_succ, resolutionXRes_succ, resolutionXRes_succ, ih]
    rfl

/-- The maps `resolutionMap φ f` commute with the differentials of the resolutions. -/
lemma resolutionXRes_comp_d (φ : H →ₜ* G) (i : ℕ) :
    resolutionXRes X φ i ≫ d _ i =
      (resFunctor (φ : H →* G)).map (d X i) ≫ resolutionXRes X φ (i + 1) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    ext : 1
    replace ih := congr($(ih).hom)
    simp only [TopRep.hom_comp, TopRep.hom_ofHom, hom_d_succ,
      ContIntertwiningMap.restrict_sub, ContIntertwiningMap.sub_comp,
      ContIntertwiningMap.comp_sub, coind₁Map_comp_coind₁ResMap,
      coind₁ResMap_comp_coind₁Map_restrict] at ih ⊢
    rw [ih, ← coind₁ResMap_comp_coind₁ι_restrict]

/-- The maps `resolutionXRes X φ` are natural in `X`. -/
lemma resolutionXRes_naturality (φ : H →ₜ* G) (f : X ⟶ X') (i : ℕ) :
    (resFunctor (φ : H →* G)).map (resolutionMap₁ f i) ≫ resolutionXRes X' φ i =
      resolutionXRes X φ i ≫ resolutionMap₁ ((resFunctor φ.toMonoidHom).map f) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionXRes_succ, resolutionXRes_succ, resolutionMap₁_succ, resolutionMap₁_succ]
    ext F x
    exact congr($(ih).hom (F (φ x)))

instance (φ : H →* G) : (resFunctor (k := k) φ).PreservesZeroMorphisms where
  map_zero _ _ := rfl

abbrev resolution'Res (φ : H →ₜ* G) :
    ((resFunctor φ.toMonoidHom).mapHomologicalComplex (.up ℕ)).obj (resolution' X)
    ⟶ resolution' (res φ.toMonoidHom X) where
  f n := resolutionXRes X φ (n + 1)
  comm' := by
    intro _ _ rfl
    simp only [mapHomologicalComplex_obj_d, ContinuousMonoidHom.coe_toMonoidHom,
      CochainComplex.of_d, resolution'd_eq]
    exact resolutionXRes_comp_d φ _

def resolution'ResNatTrans (φ : H →ₜ* G) :
    resolution'Functor k G ⋙ (resFunctor ↑φ).mapHomologicalComplex (.up ℕ)
    ⟶ (resFunctor φ) ⋙ resolution'Functor k H where
  app X := resolution'Res φ
  naturality X Y f := by
    ext n : 1
    exact resolutionXRes_naturality φ f (n + 1)

def _root_.TopRep.invariantsRes (φ : H →* G) (X : TopRep k G) :
    X.invariants ⟶ (X.res φ).invariants :=
  TopModuleCat.ofHom (ContIntertwiningMap.mapInvariantsOfRes φ ContIntertwiningMap.id)

abbrev _root_.TopRep.invariantsResNatTrans (φ : H →* G) :
    invariantsFunctor k G ⟶ resFunctor φ ⋙ invariantsFunctor k H where
  app := invariantsRes φ
  naturality X Y f := (eq_of_comp_right_eq'
    (invariantsRes φ X ≫ (resFunctor φ ⋙ invariantsFunctor k H).map f)
    ((invariantsFunctor k G).map f ≫ invariantsRes φ Y) rfl).symm

def _root_.TopRep.homogeneousCochainsXRes (φ : H →ₜ* G) (X : TopRep k G) (n : ℕ) :
    X.homogeneousCochains.X n ⟶ (X.res φ.toMonoidHom).homogeneousCochains.X n :=
  (X.resolutionX _).invariantsRes φ.toMonoidHom ≫ ((invariantsFunctor (k := k) (G := H)).map
  (resolutionXRes X φ _))

lemma _root_.TopRep.homogeneousCochainsXRes_zero (φ : H →ₜ* G) (X : TopRep k G) :
    X.homogeneousCochainsXRes φ 0 =
    X.coind₁.invariantsRes φ ≫ (invariantsFunctor k H).map (ofHom (coind₁ResMap φ .id)) := rfl

lemma _root_.TopRep.homogeneousCochainsXRes_succ (φ : H →ₜ* G) (X : TopRep k G) (n : ℕ) :
    X.homogeneousCochainsXRes φ (n + 1) = sorry := sorry


variable (k) in
def homogeneousCochainsResNatTrans (φ : H →ₜ* G) :
    homogeneousCochainsFunctor k G
    ⟶ (resFunctor φ.toMonoidHom) ⋙ homogeneousCochainsFunctor k H :=
  ((𝟙 (resolution'Functor k G))
  ◫ ((invariantsResNatTrans φ.toMonoidHom (k := k)).mapHomologicalComplex (.up ℕ)
  ≫ (mapHomologicalComplexCompIso (Iso.refl _) (.up ℕ)).inv))
  ≫ (associator _ _ _).inv ≫ (resolution'ResNatTrans φ (k := k)
  ◫ (𝟙 (invariantsFunctor (k := k) (G := H).mapHomologicalComplex _)))
  ≫ (associator _ _ _).hom

lemma homogeneousCochainsResNatTrans_app_f (φ : H →ₜ* G) (X : TopRep k G) (n : ℕ) :
    ((homogeneousCochainsResNatTrans k φ).app X).f n = homogeneousCochainsXRes φ X n := rfl

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex

/-- The morphisms between the levels of the standard resolutions of `X` and `Y` induced by a
continuous group homomorphism `φ : H →ₜ* G` and a morphism `f : res φ X ⟶ Y`, given by
`F ↦ f ∘ F ∘ φ`. -/
def resolutionMap (φ : H →ₜ* G) (f : res φ X ⟶ Y) :
    (i : ℕ) → res φ (resolutionX X i) ⟶ resolutionX Y i
  | 0 => f
  | i + 1 => ofHom (coind₁ResMap φ (resolutionMap φ f i).hom)

@[simp]
lemma resolutionMap_zero (φ : H →ₜ* G) (f : res φ X ⟶ Y) :
    resolutionMap φ f 0 = f := rfl

lemma resolutionMap_succ (φ : H →ₜ* G) (f : res φ X ⟶ Y) (i : ℕ) :
    resolutionMap φ f (i + 1) = ofHom (coind₁ResMap φ (resolutionMap φ f i).hom) := rfl

@[simp]
lemma resolutionMap_id (X : TopRep k G) (i : ℕ) :
    resolutionMap (ContinuousMonoidHom.id G) (𝟙 X) i = 𝟙 (resolutionX X i) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionMap_succ, ih]
    ext F x
    rfl

lemma resolutionMap_comp (φ : H →ₜ* G) (ψ : K →ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z)
    (i : ℕ) :
    resolutionMap (φ.comp ψ) (X := X) ((resFunctor (ψ : K →* H)).map f ≫ g) i =
      (resFunctor (ψ : K →* H)).map (resolutionMap φ f i) ≫ resolutionMap ψ g i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionMap_succ, resolutionMap_succ, resolutionMap_succ, ih]
    ext F x
    rfl


/-- The maps `resolutionMap φ f` commute with the differentials of the resolutions. -/
lemma resolutionMap_comp_d (φ : H →ₜ* G) (f : res φ X ⟶ Y) (i : ℕ) :
    resolutionMap φ f i ≫ d Y i =
      (resFunctor (φ : H →* G)).map (d X i) ≫ resolutionMap φ f (i + 1) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    ext : 1
    replace ih := congr($(ih).hom)
    simp only [TopRep.hom_comp, resolutionMap_succ, TopRep.hom_ofHom, hom_d_succ,
      ContIntertwiningMap.restrict_sub, ContIntertwiningMap.sub_comp,
      ContIntertwiningMap.comp_sub, coind₁Map_comp_coind₁ResMap,
      coind₁ResMap_comp_coind₁Map_restrict] at ih ⊢
    rw [ih, ← coind₁ResMap_comp_coind₁ι_restrict]

/-- The cochain map `homogeneousCochains X ⟶ homogeneousCochains Y` induced by a continuous
group homomorphism `φ : H →ₜ* G` and a morphism of topological `H`-representations
`f : res φ X ⟶ Y`, sending an invariant function `σ : C(G, C(G, ⋯))` to `f ∘ σ ∘ φ`. -/
@[simps! -isSimp f f_hom]
def cochainsMap (φ : H →ₜ* G) (f : res φ X ⟶ Y) :
    homogeneousCochains X ⟶ homogeneousCochains Y where
  f i := invariantsResMap φ (resolutionMap φ f (i + 1))
  comm' i j (hij : _ = _) := by
    subst hij
    rw [homogeneousCochains.d_eq, homogeneousCochains.d_eq, ← invariantsResMap_comp,
      resolutionMap_comp_d, invariantsResMap_map_comp]

@[simp]
lemma cochainsMap_id (X : TopRep k G) :
    cochainsMap (ContinuousMonoidHom.id G) (𝟙 X) = 𝟙 (homogeneousCochains X) := by
  ext i : 1
  rw [cochainsMap_f, resolutionMap_id]
  ext v
  rfl

@[reassoc]
lemma cochainsMap_comp (φ : H →ₜ* G) (ψ : K →ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z) :
    cochainsMap (φ.comp ψ) (X := X) ((resFunctor (ψ : K →* H)).map f ≫ g) =
      cochainsMap φ f ≫ cochainsMap ψ g := by
  ext i v x
  exact congr($(resolutionMap_comp φ ψ f g (i + 1)).hom v.1 x)

/-- The map `Zⁿ(G, X) ⟶ Zⁿ(H, Y)` on cocycles induced by a continuous group homomorphism
`φ : H →ₜ* G` and a morphism of topological `H`-representations `f : res φ X ⟶ Y`. -/
noncomputable abbrev cocyclesMap (φ : H →ₜ* G) (f : res φ X ⟶ Y) (n : ℕ) :
    cocycles X n ⟶ cocycles Y n :=
  HomologicalComplex.cyclesMap (cochainsMap φ f) n

@[simp]
lemma cocyclesMap_id (X : TopRep k G) (n : ℕ) :
    cocyclesMap (ContinuousMonoidHom.id G) (𝟙 X) n = 𝟙 _ := by
  simp [cocyclesMap]

@[reassoc]
lemma cocyclesMap_comp (φ : H →ₜ* G) (ψ : K →ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z)
    (n : ℕ) :
    cocyclesMap (φ.comp ψ) (X := X) ((resFunctor (ψ : K →* H)).map f ≫ g) n =
      cocyclesMap φ f n ≫ cocyclesMap ψ g n := by
  simp [cocyclesMap, ← HomologicalComplex.cyclesMap_comp, ← cochainsMap_comp]

/-- The map `Hⁿ(G, X) ⟶ Hⁿ(H, Y)` on continuous cohomology induced by a continuous group
homomorphism `φ : H →ₜ* G` and a morphism of topological `H`-representations
`f : res φ X ⟶ Y`. -/
noncomputable abbrev map (φ : H →ₜ* G) (f : res φ X ⟶ Y) (n : ℕ) :
    continuousCohomology n X ⟶ continuousCohomology n Y :=
  HomologicalComplex.homologyMap (cochainsMap φ f) n

@[reassoc]
theorem π_map (φ : H →ₜ* G) (f : res φ X ⟶ Y) (n : ℕ) :
    π X n ≫ map φ f n = cocyclesMap φ f n ≫ π Y n := by
  simp [map, cocyclesMap]

@[simp]
lemma map_id (X : TopRep k G) (n : ℕ) :
    map (ContinuousMonoidHom.id G) (𝟙 X) n = 𝟙 _ := by
  simp [map]

@[reassoc]
lemma map_comp (φ : H →ₜ* G) (ψ : K →ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z) (n : ℕ) :
    map (φ.comp ψ) (X := X) ((resFunctor (ψ : K →* H)).map f ≫ g) n = map φ f n ≫ map ψ g n := by
  simp [map, ← HomologicalComplex.homologyMap_comp, ← cochainsMap_comp]

end ContinuousCohomology
