/-
Copyright (c) 2026 Richard Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Hill
-/
import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
/-!
Define inflation maps in continuous cohomology.
-/

universe u₁ u₂ u₃
open CategoryTheory
  TopRep
  ContRepresentation

variable {R : Type u₁} [CommRing R]
variable {G H : Type u₂} [Group G] [Group H]

namespace ContRepresentation

variable {V W : Type u₃} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [Module R V] (ρ : ContRepresentation R G V)
    [AddCommGroup W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [Module R W] (ρ' : ContRepresentation R G W)
    (N : Subgroup G)


/--
For `ρ : ContRepresentation R G V`,= and a subgroup `N` of `G`,
`ρ.relInvariants N` is the `R`-submodule of `V` consisting of the `N`-invariant elements.
-/
def relInvariants : Submodule R V where
  carrier := {v : V | ∀ n ∈ N, ρ n v = v}
  add_mem' h₁ h₂ _ h  := by rw [map_add, h₁, h₂] <;> exact h
  zero_mem' _ _       := map_zero _
  smul_mem' _ _ h _ _ := by rwa [map_smul, h]

variable [hN : N.Normal]
lemma rho_mem_relInvariants {v : V} (hv : v ∈ ρ.relInvariants N) (g : G) :
    ρ g v ∈ ρ.relInvariants N := by
  intro n hn
  calc
    _ = ρ (n * g) v             := by rw [map_mul, mul_apply_eq_comp]
    _ = ρ (g * (g⁻¹ * n * g)) v := by simp_rw [←mul_assoc, mul_inv_cancel, one_mul]
    _ = ρ g (ρ (g⁻¹ * n * g) v) := by rw [map_mul, mul_apply_eq_comp]
    _ = ρ g v                   := by rw [hv _ (Subgroup.Normal.conj_mem' hN n hn g)]

@[simps] def relInvariantsRho : ContRepresentation R G (ρ.relInvariants N) := ⟨{
  toFun g       := (ρ g).restrict (fun _ hv ↦ ρ.rho_mem_relInvariants N hv g)
  map_one'      := by ext; simp
  map_mul' _ _  := by ext; simp
}⟩

def relInvariantsIntertwining (f : ρ →ⁱL ρ') :
    ρ.relInvariantsRho N →ⁱL ρ'.relInvariantsRho N where
  toContinuousLinearMap := f.toContinuousLinearMap.restrict (by
    intro v hv n hn
    have := (f.isIntertwining n v).symm
    rwa [hv n hn] at this)
  isIntertwining' g := by
    ext v
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_restrict_apply]
    exact f.isIntertwining g v

lemma le_relInvariantsRho_ker : N ≤ (ρ.relInvariantsRho N).toMonoidHom.ker := by
  intro n hn
  rw [MonoidHom.mem_ker]
  ext ⟨_,hv⟩
  apply hv _ hn

def relInvariantsInfl : ContRepresentation R (G ⧸ N) (ρ.relInvariants N) :=
  ⟨QuotientGroup.lift N (ρ.relInvariantsRho N) (ρ.le_relInvariantsRho_ker N)⟩

def relInvariantsIntertwining' (f : ρ →ⁱL ρ') :
    ρ.relInvariantsInfl N →ⁱL ρ'.relInvariantsInfl N where
  toContinuousLinearMap := (relInvariantsIntertwining ρ ρ' N f).toContinuousLinearMap
  isIntertwining' g := by
    obtain ⟨g',rfl⟩ := g.exists_rep
    apply (relInvariantsIntertwining ρ ρ' N f).isIntertwining'

end ContRepresentation

variable [TopologicalSpace R]
variable (N : Subgroup G) [N.Normal]
variable {π_G : TopRep R G} {π_H : TopRep R H}

namespace TopRep

def relInvariantsFunctor : TopRep R G ⥤ TopRep R (G ⧸ N) where
  obj π_G       := TopRep.of (π_G.ρ.relInvariantsInfl N)
  map f         := TopRep.ofHom (ContRepresentation.relInvariantsIntertwining' _ _ N f.hom)

variable (R) in
@[simps] def inflι : (relInvariantsFunctor N ⋙ resFunctor (QuotientGroup.mk' N)) ⟶ 𝟭 (TopRep R G)
    where
  app _ := TopRep.ofHom {
    toFun := Subtype.val
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
    isIntertwining' _ := rfl
  }
  naturality _ _ _ := rfl

end TopRep

variable [TopologicalSpace G]

def QuotientGroup.mk'' : G →ₜ* G ⧸ N where
  toMonoidHom := QuotientGroup.mk' N
  continuous_toFun := by tauto

@[simp] lemma QuotientGroup.coe_mk'' : ↑(mk'' N) = mk' N := rfl

variable [IsTopologicalGroup G]

noncomputable section
namespace ContinuousCohomology

abbrev inflApp (n : ℕ) (π : TopRep R G) :
    (relInvariantsFunctor N ⋙ Functor R (G ⧸ N) n).obj π
    ⟶ (Functor R G n).obj ((𝟭 _).obj π) :=
  (resNatTrans R (QuotientGroup.mk'' N) n).app
  ((relInvariantsFunctor N).obj π)
  ≫ (Functor R G n).map
  ((inflι R N).app π)

/-- The components `inflApp N n` are natural in the representation: they intertwine the
functorial maps on continuous cohomology. -/
lemma inflApp_naturality (n : ℕ) {π₁ π₂ : TopRep R G} (f : π₁ ⟶ π₂) :
    (relInvariantsFunctor N ⋙ Functor R (G ⧸ N) n).map f ≫ inflApp N n π₂ =
      inflApp N n π₁ ≫ (Functor R G n).map f := by
  have h := (Functor R G n).congr_map ((inflι R N).naturality f)
  rw [Functor.map_comp, Functor.map_comp] at h
  refine ((resNatTrans R (QuotientGroup.mk'' N) n).naturality_assoc
    ((relInvariantsFunctor N).map f) _).trans ?_
  rw [Category.assoc]
  exact whisker_eq _ h

noncomputable def inflNatTrans (n : ℕ) :
    relInvariantsFunctor N ⋙ Functor R (G ⧸ N) n ⟶ Functor R G n where
  app            := inflApp N n
  naturality _ _ f := by
    /-
    Note that the following proof is a lot quicker than `exact inflApp_naturality N n f`.
    -/
    have := inflApp_naturality N n f
    simpa only [Functor.id_obj] using this

end ContinuousCohomology
end
