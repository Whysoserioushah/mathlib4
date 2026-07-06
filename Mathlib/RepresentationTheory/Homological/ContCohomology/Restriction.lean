/-
Copyright (c) 2026 Richard Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Hill
-/
-- import Mathlib.Algebra.Category.ContinuousCohomology'.Basic
import Mathlib.RepresentationTheory.Continuous.Basic
import Mathlib.RepresentationTheory.Homological.ContCohomology.forMathlib
/-!
Define the resFunctortriction maps $Hⁿ(H,M) ⟶ Hⁿ(G,M)$, given an `H`-module `M`
and a continuous homomorphism `φ : G →ₜ* H`.
This is defined as a natural transformation of functors.

The definition is in several steps.

1. We define a functor `resFunctor R φ : TopRep R H ⥤ TopRep R G`, which composes with `φ`.

2. We define a continuous linear map `C_resFunctor φ V : C(H,V) →L[R] C(G,V)`,
  which is composition with `φ`.

3. We show that `C_resFunctor φ` defines a natural transformation
  `I_resNatTrans R φ : I R H ⋙ resFunctor R φ ⟶ resFunctor R φ ⋙ I R G`.

4. Note that iterating `I_resNatTrans R φ`, we obtain a natural transformation
  `(I R H) ^ n ⋙ resFunctor R φ ⟶ resFunctor R φ ⋙ (I R G) ^ n`.
  In other words
  `MultiInd.functor R H n ⋙ resFunctor R φ ⟶ resFunctor R φ ⋙ MultiInd.functor R G n`.

5. We show that these maps commute with the coboundary maps, and so we obtain a
  natural transformation
  `(complex R H).asFunctor ⋙ resFunctor' R φ ⟶ (resFunctor R φ ⋙ (complex R G).asFunctor)`.
-/


open CategoryTheory Functor NatTrans
  ConcreteCategory
  TopModuleCat
  ContRepresentation

/-
The trhee universe levels used are:
  `u₁` The level of rings of scalars,
  `u₂` the level of groups,
  `u₃` the level of representation spaces.
-/
universe u₁ u₂ u₃
variable {R : Type u₁} [CommRing R]
  {G H K : Type u₂} [Group G] [Group H] [Group K]

namespace ContRepresentation
variable {V : Type u₃} [AddCommGroup V] [TopologicalSpace V]
  [Module R V] [IsTopologicalAddGroup V]
  (π : ContRepresentation R H V)


variable [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace K]
  (φ : G →ₜ* H) (ψ : K →ₜ* G)

abbrev res : ContRepresentation R G V := π.comp φ

variable [TopologicalSpace R] [ContinuousSMul R V] [IsTopologicalGroup G] [IsTopologicalGroup H]

/--
Given `φ : G →ₜ* H`, this is the intertwining operator from `π.coind₁.resFunctor' φ` to
`(π.resFunctor φ).coind₁`. As a continuous linear map from `C(H,V)` to `C(G,V)`, this function takes
`f : C(H,V)` to the composition of `f` and `φ`.
-/
def coind₁_res : (π.coind₁.res φ) →ⁱL (π.res φ).coind₁ where
  toFun             := φ.toContinuousMap.compRightContinuousMap V
  map_add' _ _      := rfl
  map_smul' _ _     := rfl
  cont              := (φ.toContinuousMap.compRightContinuousMap V).continuous
  isIntertwining' _ := by ext; simp

@[simp] lemma coind₁_res_apply (f : C(H, V)) : π.coind₁_res φ f = f.comp φ := rfl

end ContRepresentation

variable (R H) [TopologicalSpace R]

-- abbrev TopRep := Action (TopModuleCat R) H

variable [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace K]
  (φ : G →ₜ* H) (ψ : K →ₜ* G) {H}

infixr:90 " ∘ₜ* " => ContinuousMonoidHom.comp

namespace TopRep
variable [IsTopologicalRing R]

/--
For a continuous group homomorphism `φ : G →ₜ* H`, the functor
`resFunctor R φ : TopRep R H ⥤ TopRep R G` is the restriction functor
`Action.resFunctor (TopModuleCat R) φ.toMonoidHom`.
-/
abbrev resFunctor (φ : G →* H) : TopRep R H ⥤ TopRep R G where
  obj rep := TopRep.of (rep.ρ.comp φ)
  map f   := TopRep.ofHom ⟨f.hom.toContinuousLinearMap, fun g ↦ f.hom.isIntertwining' (φ g)⟩

instance (φ : G →* H) : (resFunctor R φ).Additive where

--lemma resFunctor_id : resFunctor R (.id H) = 𝟭 (TopRep R H) := rfl
variable (H) in
/--
The isomorphism of functors between `resFunctor R (.id H)` and the identity functor
`𝟭 (TopRep R H)`.
-/
abbrev resFunctor_id_iso : resFunctor R (.id H) ≅ 𝟭 (TopRep R H) := Iso.refl _

/--
The isomorphism of functors between `resFunctor R (φ ∘ₜ ψ)` and the composition
`resFunctor R φ ⋙ resFunctor R ψ`.
-/
abbrev resFunctor_comp_iso (φ : G →* H) (ψ : H →* K) :
    resFunctor R (ψ.comp φ) ≅ resFunctor R ψ ⋙ resFunctor R φ := Iso.refl _

variable {R}

def toContRepresentation (rep : TopRep R G) : ContRepresentation R G rep.V where
  toFun         := rep.ρ
  map_one'      := by simp [ContinuousLinearMap.one_def]
  map_mul' _ _  := by simp [ContinuousLinearMap.mul_def]

end TopRep

namespace ContinuousCohomology
open TopRep
variable [IsTopologicalRing R] (rep : TopRep R H)
  [IsTopologicalGroup G] [IsTopologicalGroup H] [IsTopologicalGroup K]

/--
Given `φ : G →ₜ* H` and a representation of `H` on `V`,
this is the natural intertwining operator from `C(H,V)|_G` to `C(G,V|_G)`,
defined as a natural transformation from the functor `I R H ⋙ resFunctor R φ` to
`resFunctor R φ ⋙ I R G`.
-/
def I_resNatTrans :
     coind₁ R H ⋙ resFunctor R φ.toMonoidHom ⟶ resFunctor R φ.toMonoidHom ⋙ coind₁ R G where
  app rep           := TopRep.ofHom ((toContRepresentation rep).coind₁_res φ)
  naturality _ _ _  := rfl

lemma const_hcomp_id_comp_I_resNatTrans :
    (coind₁ι R H ◫ 𝟙 (resFunctor R φ.toMonoidHom)) ≫ I_resNatTrans R φ
    = (leftUnitor (resFunctor R φ.toMonoidHom)).hom
    ≫ (rightUnitor (resFunctor R φ.toMonoidHom)).inv
    ≫ 𝟙 (resFunctor R φ.toMonoidHom) ◫ coind₁ι R G := rfl

def invariants_resNatTrans : invariants R H ⟶ resFunctor R φ.toMonoidHom ⋙ invariants R G where
  app _             := TopModuleCat.ofHom {
    toFun v       := ⟨v.val,fun g ↦ v.property (φ g)⟩
    map_add' _ _  := rfl
    map_smul' _ _ := rfl
    cont          := continuous_inclusion (by exact fun _ hv g ↦ hv (φ g))
  }
  naturality _ _ _ := rfl

namespace MultiInd

def functor_resNatTrans : ∀ n,
    (functor R H n ⋙ resFunctor R φ.toMonoidHom) ⟶ (resFunctor R φ.toMonoidHom ⋙ functor R G n)
| 0 =>
    ((functor_zero_iso R H).hom ◫ 𝟙 _) ≫ (leftUnitor _).hom
    ≫ (rightUnitor _).inv ≫ (𝟙 _ ◫ (functor_zero_iso R G).inv)
| n + 1 =>
    ((functor_succ_iso R H n).hom ◫ 𝟙 (resFunctor R φ.toMonoidHom)) ≫ (associator _ _ _).hom
    ≫ (𝟙 (functor R H n) ◫ I_resNatTrans R φ) ≫ (associator _ _ _).inv
    ≫ (functor_resNatTrans n ◫ 𝟙 (coind₁ R G)) ≫ (associator _ _ _).hom
    ≫ (𝟙 (resFunctor R φ.toMonoidHom) ◫ (functor_succ_iso R G n).inv)

lemma functor_resNatTrans_zero : functor_resNatTrans R φ 0
    = ((functor_zero_iso R H).hom ◫ 𝟙 _) ≫ (leftUnitor _).hom
    ≫ (rightUnitor _).inv ≫ (𝟙 _ ◫ (functor_zero_iso R G).inv) := rfl

lemma functor_resNatTrans_succ (n : ℕ) : functor_resNatTrans R φ (n + 1)
    = ((functor_succ_iso R H n).hom ◫ 𝟙 (resFunctor R φ.toMonoidHom)) ≫ (associator _ _ _).hom
    ≫ (𝟙 (functor R H n) ◫ I_resNatTrans R φ) ≫ (associator _ _ _).inv
    ≫ (functor_resNatTrans R φ n ◫ 𝟙 (coind₁ R G)) ≫ (associator _ _ _).hom
    ≫ (𝟙 (resFunctor R φ.toMonoidHom) ◫ (functor_succ_iso R G n).inv) := rfl

lemma functor_resNatTrans_comp_d (n : ℕ) :
    functor_resNatTrans R φ n ≫ 𝟙 (resFunctor R φ.toMonoidHom) ◫ d R G n
    = (d R H n ◫ 𝟙 (resFunctor R φ.toMonoidHom)) ≫ functor_resNatTrans R φ (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [d_succ', hcomp_sub, Preadditive.comp_sub, d_succ', sub_hcomp, Preadditive.sub_comp]
    congr 1
    rw [functor_resNatTrans_succ, Category.assoc, Category.assoc, Category.assoc, Category.assoc,
      Category.assoc, Category.assoc, id_hcomp, id_hcomp, id_hcomp, ←whiskerLeft_comp,
      ←Category.assoc, ←Category.assoc, ←Category.assoc, ←Category.assoc, ←Category.assoc,
      ←Category.assoc, Iso.inv_hom_id, Category.id_comp, whiskerLeft_comp, ←id_hcomp, ←id_hcomp,
      hcomp_assoc'', Category.assoc, Category.assoc, ←Category.assoc (associator _ _ _).hom,
      ←Category.assoc (associator _ _ _).hom, Iso.hom_inv_id, Category.id_comp,
      ←Category.assoc (_ ◫ (𝟙 _)), ←Category.assoc (_ ◫ (𝟙 _)), ←exchange, ih, ←id_hcomp]
    rfl

lemma functor_resNatTrans_app_comp_d_app (n : ℕ) : (functor_resNatTrans R φ n).app rep
    ≫ (d R G n).app ((TopRep.resFunctor R φ.toMonoidHom).obj rep)
    = (resFunctor R φ.toMonoidHom).map ((d R H n).app rep)
    ≫ (functor_resNatTrans R φ (n + 1)).app rep := by
  convert! NatTrans.congr_app (functor_resNatTrans_comp_d R φ n) rep
  simp
  rfl

set_option backward.isDefEq.respectTransparency false in
def complex_resNatTrans :
    (complex R H).asFunctor ⋙ (resFunctor R φ.toMonoidHom).mapHomologicalComplex (.up ℕ) ⟶
    resFunctor R φ.toMonoidHom ⋙ (complex R G).asFunctor where
      app rep := {
        f n := (functor_resNatTrans R φ n).app rep
        comm' n _ := by
          intro rfl
          dsimp only [complex, comp_obj, mapHomologicalComplex_obj_X,
            HomologicalComplex.asFunctor_obj_X, HomologicalComplex.asFunctor_obj_d,
            mapHomologicalComplex_obj_d]
          convert! functor_resNatTrans_app_comp_d_app R φ rep n
          · change ((complex R G).asFunctor.obj _).d _ _ = _
            simp only [ContinuousMonoidHom.coe_toMonoidHom, HomologicalComplex.asFunctor_obj_d]
            congr
            apply CochainComplex.of_d
          · change (resFunctor R φ.toMonoidHom).map _ = _
            simp
      }
      naturality _ _ f := by
        ext1 n
        exact (functor_resNatTrans R φ n).naturality f

def _root_.Functor.mapHomologicalComplex_comp_iso {A B C : Type*} [Category A] [Category B]
    [Category C] [Limits.HasZeroMorphisms A] [Limits.HasZeroMorphisms B] [Limits.HasZeroMorphisms C]
    (F : A ⥤ B) (G : B ⥤ C) [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    {α : Type} (c : ComplexShape α) :
    (F ⋙ G).mapHomologicalComplex c ≅ F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c :=
  Iso.refl _

def complex_invariants_resNatTrans :
    (complex R H).asFunctor ⋙ (invariants R H).mapHomologicalComplex (.up ℕ) ⟶
    resFunctor R φ.toMonoidHom ⋙ (complex R G).asFunctor
    ⋙ (invariants R G).mapHomologicalComplex (.up ℕ) :=
  (𝟙 (complex R H).asFunctor ◫ (invariants_resNatTrans R φ).mapHomologicalComplex _) ≫
  (𝟙 _ ◫ (mapHomologicalComplex_comp_iso _ _ _).hom) ≫
  (associator _ _ _).inv ≫
  (complex_resNatTrans R φ ◫ 𝟙 ((invariants R G).mapHomologicalComplex (.up ℕ))) ≫
  (associator _ _ _).hom

def functor_invariants_resNatTrans (n : ℕ) :
    functor R H n ⋙ invariants R H ⟶ resFunctor R φ.toMonoidHom ⋙ functor R G n ⋙ invariants R G :=
  (𝟙 (functor R H n) ◫ ((rightUnitor _).inv ≫ invariants_resNatTrans R φ))
  ≫ (associator (functor R H n) (resFunctor R φ.toMonoidHom) (invariants R G)).inv
  ≫ (functor_resNatTrans R φ n ◫ 𝟙 (invariants R G))
  ≫ (associator (resFunctor R φ.toMonoidHom) (functor R G n) (invariants R G)).hom

end MultiInd

variable (H) in
def homogeneousCochains_iso : homogeneousCochains R H ≅
    (MultiInd.complex R H).asFunctor ⋙ (invariants R H).mapHomologicalComplex _ ⋙
    (ComplexShape.embeddingUp'Add 1 1).restrictionFunctor _ := Iso.refl _

/--
The map from the homogeneous cochains on `H` with values in `rep`
to the the homogeneous cochains on `G` with values in the restriction of `rep` to `G`.
This is defined by composing a cochain with the map `φ : G →ₜ* H` in each of the variables.
The resulting function is a morphism of cochain complexes.
-/
def homogeneousCochains_resNatTrans :
    homogeneousCochains R H ⟶ resFunctor R φ.toMonoidHom ⋙ homogeneousCochains R G :=
  (homogeneousCochains_iso _ _).hom ≫ (associator _ _ _).inv ≫
  (MultiInd.complex_invariants_resNatTrans R φ ◫
    𝟙 ((ComplexShape.embeddingUp'Add 1 1).restrictionFunctor (TopModuleCat R))) ≫
  (associator _ _ _).hom ≫ 𝟙 _ ◫ (homogeneousCochains_iso R G).inv

open HomologicalComplex

noncomputable def resNatTrans (n : ℕ) :
    continuousCohomology R H n ⟶ resFunctor R φ.toMonoidHom ⋙ continuousCohomology R G n :=
  (homogeneousCochains_resNatTrans R φ ◫ 𝟙 (homologyFunctor (TopModuleCat R) (.up ℕ) n))
  ≫ (associator (resFunctor R φ.toMonoidHom) (homogeneousCochains R G)
    (homologyFunctor (TopModuleCat R) (.up ℕ) n)).hom

end ContinuousCohomology
