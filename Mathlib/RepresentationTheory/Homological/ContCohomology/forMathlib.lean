/-
Copyright (c) 2026 Richard Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Hill
-/
import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Combinatorics.Quiver.ReflQuiver
import CtsToDiscrete.continuousCohomology'
import Mathlib.RepresentationTheory.Rep.Basic

/-!
Some random stuff that should go into Mathlib fairly easily.

-/
open CategoryTheory Functor NatTrans TopRep

variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
  {F₁ F₂ : C ⥤ D} {G₁ G₂ G₃ : D ⥤ E} {H₁ H₂ : E ⥤ F}
  (α α' : F₁ ⟶ F₂) (β β' : G₁ ⟶ G₂) (γ : H₁ ⟶ H₂) (δ δ' : G₂ ⟶ G₃)
  (Φ : F₁ ≅ F₂) (Ψ : G₁ ≅ G₂)

@[simp] lemma Iso.comp_inv_app_eq {rep : D} {rep' : C} (f₁ : rep ⟶ F₁.obj rep')
    (f₂ : rep ⟶ F₂.obj rep') (h : f₁ = f₂ ≫ Φ.inv.app rep') : f₁ ≫ (Φ.hom.app rep') = f₂ := by
  rw [←Iso.app_hom, ←Iso.eq_comp_inv, h, Iso.app_inv]

@[simp] lemma Iso.eq_comp_inv_app {rep : D} {rep' : C} (f₁ : rep ⟶ F₁.obj rep')
    (f₂ : rep ⟶ F₂.obj rep') (h : f₂ ≫ Φ.inv.app rep' = f₁) : f₁ ≫ (Φ.hom.app rep') = f₂ := by
  rw [←Iso.app_hom, ←Iso.eq_comp_inv, ←h, Iso.app_inv]

set_option backward.isDefEq.respectTransparency false
@[simp] lemma Functor.id_whiskerLeft :
    (𝟭 C).whiskerLeft α = (leftUnitor _).hom ≫ α ≫ (leftUnitor _).inv := by
  ext
  simp only [whiskerLeft_app, comp_app, leftUnitor_hom_app, leftUnitor_inv_app,
    Functor.id_obj]
  erw [Category.comp_id, Category.id_comp]

@[simp] lemma NatTrans.id_app_id (V : C) : NatTrans.app (𝟙 (𝟭 C)) V = 𝟙 V := rfl

lemma hcomp_assoc : ((α ◫ β) ◫ γ) =
    (associator F₁ G₁ H₁).hom ≫ (α ◫ (β ◫ γ)) ≫ (associator F₂ G₂ H₂).inv := by
  aesop

lemma hcomp_assoc'' : α ◫ (β ◫ γ) =
    (associator F₁ G₁ H₁).inv ≫ ((α ◫ β) ◫ γ) ≫ (associator F₂ G₂ H₂).hom := by
  aesop

lemma associator_hcomp_hcomp : (associator F₁ G₁ H₁).hom ≫ (α ◫ (β ◫ γ)) =
    ((α ◫ β) ◫ γ) ≫ (associator F₂ G₂ H₂).hom := by aesop_cat

lemma hcomp_assoc' : (α ◫ β) ◫ γ = α ◫ (β ◫ γ) := by
  aesop

variable (F₁ G₁) in
lemma id_hcomp_id : 𝟙 F₁ ◫ 𝟙 G₁ = 𝟙 (F₁ ⋙ G₁) := by
  aesop

@[simps] def CategoryTheory.Iso.hcomp : F₁ ⋙ G₁ ≅ F₂ ⋙ G₂ where
  hom := Φ.hom ◫ Ψ.hom
  inv := Φ.inv ◫ Ψ.inv
  hom_inv_id := by rw [←exchange, hom_inv_id, hom_inv_id, id_hcomp_id]
  inv_hom_id := by rw [←exchange, inv_hom_id, inv_hom_id, id_hcomp_id]

infixl:80 " ≅◫≅ " => Iso.hcomp

variable [Preadditive E]

@[simp] lemma hcomp_add : α ◫ (β + β') = α ◫ β + α ◫ β' := by aesop

@[simp] lemma hcomp_sub : α ◫ (β - β') = α ◫ β - α ◫ β' := by aesop

@[simp] lemma whiskerLeft_add : F₁.whiskerLeft (β + β') = F₁.whiskerLeft β + F₁.whiskerLeft β' :=
  rfl

@[simp] lemma whiskerLeft_sub : F₁.whiskerLeft (β - β') = F₁.whiskerLeft β - F₁.whiskerLeft β' :=
  rfl

variable [Preadditive D] [G₂.Additive]

@[simp] lemma add_hcomp : (α + α') ◫ β  = α ◫ β + α' ◫ β := by aesop

@[simp] lemma sub_hcomp : (α - α') ◫ β  = α ◫ β - α' ◫ β := by aesop

@[simp] lemma whiskerRight_add :
    whiskerRight (α + α') G₂ = whiskerRight α G₂ + whiskerRight α' G₂ := by
  simp only [←hcomp_id, add_hcomp]

@[simp] lemma whiskerRight_sub :
    whiskerRight (α - α') G₂ = whiskerRight α G₂ - whiskerRight α' G₂ := by
  simp only [←hcomp_id, sub_hcomp]

lemma zero_hcomp (C D E : Type*) [Category C] [Category D] [Preadditive D]
    [Category E] [Preadditive E] (F F' : C ⥤ D) (G G' : D ⥤ E) [G'.Additive] (α : G ⟶ G') :
    (0 : F ⟶ F') ◫ α = 0 := by
  ext; simp

lemma hcomp_zero (C D E : Type*) [Category C] [Category D] [Preadditive D]
    [Category E] [Preadditive E] (F F' : C ⥤ D) (G G' : D ⥤ E) [G'.Additive] (α : F ⟶ F') :
    α ◫ (0 : G ⟶ G') = 0 := by ext; simp

open HomologicalComplex ComplexShape

@[simps] def Homotopy.of {C : Type} [Category C] [Preadditive C] {A B : CochainComplex C ℕ}
    (φ : A ⟶ B) (ho : ∀ i, A.X (i + 1) ⟶ B.X i)
    (h_zero : A.d 0 1 ≫ ho 0 = φ.f 0)
    (h_succ : ∀ n, A.d (n + 1) (n + 2) ≫ ho (n + 1) + ho n ≫ B.d n (n + 1) = φ.f (n + 1)) :
    Homotopy φ 0 :=
  let ho' (i j : ℕ) : A.X i ⟶ B.X j := if h : (up ℕ).Rel j i then h ▸ ho j else 0
  {
    hom := ho'
    comm i := by
      rw [zero_f, add_zero]
      cases i with
      | zero =>
        have h₁ : ¬ ∃ j, (up ℕ).Rel j 0 := by tauto
        have h₂ :   ∃ j, (up ℕ).Rel 0 j := ⟨1,rfl⟩
        rw [prevD, AddMonoidHom.mk'_apply, prev, dif_neg h₁, shape _ 0 0 (by simp),
          Limits.comp_zero, add_zero, dNext, AddMonoidHom.mk'_apply, next, dif_pos h₂,
          ←h₂.choose_spec]
        exact h_zero.symm
      | succ n =>
        have h₁ : ∃ j, (up ℕ).Rel (n + 1) j := ⟨n + 2,rfl⟩
        have h₂ : ∃ i, (up ℕ).Rel i (n + 1) := ⟨n,rfl⟩
        have := h₂.choose_spec
        rw [up_Rel, Nat.add_right_cancel_iff] at this
        rw [dNext, AddMonoidHom.mk'_apply, next, dif_pos h₁, ←h₁.choose_spec,
          prevD, AddMonoidHom.mk'_apply, prev, dif_pos h₂, this, ←h_succ]
        simp only [ho', up_Rel, dif_pos, add_assoc]
        rfl
  }

@[ext]
lemma TopModuleCat.Hom.ext (R : Type*) [CommRing R] [TopologicalSpace R] {V W : TopModuleCat R}
    (f₁ f₂ : V ⟶ W) (h : f₁.hom = f₂.hom) :
    f₁ = f₂ := by rw [←ofHom_hom _ f₁, h, ofHom_hom]

@[ext]
lemma TopModuleCat.End.ext (R : Type*) [CommRing R] [TopologicalSpace R] {V : TopModuleCat R}
    (f₁ f₂ : End V) (h : f₁.hom = f₂.hom) :
    f₁ = f₂ := by rw [←ofHom_hom _ f₁, h, ofHom_hom]

@[simp]
lemma TopModuleCat.Hom.hom_one (R : Type*) [CommRing R] [TopologicalSpace R] {V : TopModuleCat R} :
    (1 : End V).hom = 1 := rfl

@[simp]
lemma TopModuleCat.Hom.hom_comp (R : Type*) [CommRing R] [TopologicalSpace R]
    {V₁ V₂ V₃ : TopModuleCat R} (φ : V₁ ⟶ V₂) (ψ : V₂ ⟶ V₃) :
    (φ ≫ ψ).hom = ψ.hom ∘L φ.hom := rfl

namespace ContinuousCohomology.MultiInd
variable (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/--
The isomorphism of functors between `functor R G 0` and the identity functor.
-/
abbrev functor_zero_iso : functor R G 0 ≅ 𝟭 (TopRep R G) := Iso.refl _

/--
The isomorphism of functors between `functor R G (n + 1)` and the composition
`functor R G n ⋙ I R G`.
-/
abbrev functor_succ_iso (n : ℕ) : functor R G (n + 1) ≅ functor R G n ⋙ coind₁ R G := Iso.refl _

/--
This is a version of `ContinuousCohomology.MultiInd.d_zero` which type checks.
-/
lemma d_zero' : d R G 0 = (functor_zero_iso R G).hom ≫ coind₁ι R G ≫ (leftUnitor (coind₁ R G)).inv
    ≫ ((functor_zero_iso R G).inv ◫ 𝟙 (coind₁ R G)) ≫ (functor_succ_iso R G 0).inv := rfl

/--
This is a version of `ContinuousCohomology.MultiInd.d_succ` which type checks.
-/
lemma d_succ' (n : ℕ) : d R G (n + 1) =
    (functor_succ_iso R G n).hom
    ≫ (rightUnitor (functor R G (n + 1))).inv
    ≫ (𝟙 (functor R G (n + 1)) ◫ coind₁ι R G)
    ≫ (functor_succ_iso R G (n + 1)).inv
    - (functor_succ_iso R G n).hom
    ≫ ((d R G n) ◫ 𝟙 (coind₁ R G))
    ≫ (functor_succ_iso R G (n + 1)).inv := rfl

instance (n : ℕ) : (functor R G n).Additive := by
  induction n <;>
  · unfold functor; infer_instance


end ContinuousCohomology.MultiInd

/--
Construct an isomorphism in the category `ModuleCat R`
from a Typeland linear equivalence `V ≃ₗ[R] V'`.
-/
@[simps] def ModuleCat.Hom.isoOfEquiv {R : Type*} {V V' : Type u} [Ring R] [AddCommGroup V]
    [AddCommGroup V'] [Module R V] [Module R V'] (φ : V ≃ₗ[R] V') :
    ModuleCat.of R V ≅ ModuleCat.of R V' where
  hom := ModuleCat.ofHom φ
  inv := ModuleCat.ofHom φ.symm


namespace Representation

infixr:80 " →ⁱ " => IntertwiningMap
infixr:80 " ≃ⁱ " => Equiv
infixr:80 " ∘ⁱ " => IntertwiningMap.comp

end Representation


/--
Construct an isomorphism in the category `Rep R G`
from a Typeland equivalence `ρ ≃ⁱ ρ'`.
-/
@[simps] def Rep.Hom.isoOfEquiv {R G : Type*} {V V' : Type u} [Ring R] [Monoid G] [AddCommGroup V]
    [AddCommGroup V'] [Module R V] [Module R V'] {ρ : Representation R G V}
    {ρ' : Representation R G V'} (φ : ρ ≃ⁱ ρ') : Rep.of ρ ≅ Rep.of ρ' where
  hom := Rep.ofHom φ.toIntertwiningMap
  inv := Rep.ofHom φ.symm.toIntertwiningMap
