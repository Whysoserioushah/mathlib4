/-
Copyright (c) 2026 Richard Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Hill
-/
import Mathlib.RepresentationTheory.Homological.ContCohomology.Restriction
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

@[simps] def relInvariants_rho : ContRepresentation R G (ρ.relInvariants N) where
  toFun g       := (ρ g).restrict (fun _ hv ↦ ρ.rho_mem_relInvariants N hv g)
  map_one'      := by ext; simp
  map_mul' _ _  := by ext; simp

def relInvariants_intertwining (f : ρ →ⁱL ρ') :
    ρ.relInvariants_rho N →ⁱL ρ'.relInvariants_rho N where
  toContinuousLinearMap := f.toContinuousLinearMap.restrict (by
    intro v hv n hn
    have := (f.isIntertwining n v).symm
    rwa [hv n hn] at this)
  isIntertwining' g := by
    ext v
    simp only [relInvariants_rho_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_restrict_apply]
    exact f.isIntertwining g v

lemma le_relInvariants_ker : N ≤ (ρ.relInvariants_rho N).ker := by
  intro n hn
  rw [MonoidHom.mem_ker]
  ext ⟨_,hv⟩
  apply hv _ hn

def relInvariants_infl : ContRepresentation R (G ⧸ N) (ρ.relInvariants N) :=
  QuotientGroup.lift N (ρ.relInvariants_rho N) (ρ.le_relInvariants_ker N)

def relInvariants_intertwining' (f : ρ →ⁱL ρ') :
    ρ.relInvariants_infl N →ⁱL ρ'.relInvariants_infl N where
  toContinuousLinearMap := (relInvariants_intertwining ρ ρ' N f).toContinuousLinearMap
  isIntertwining' g := by
    obtain ⟨g',rfl⟩ := g.exists_rep
    apply (relInvariants_intertwining ρ ρ' N f).isIntertwining'

end ContRepresentation

variable [TopologicalSpace R] [IsTopologicalRing R]
variable (N : Subgroup G) [N.Normal]
variable {π_G : TopRep R G} {π_H : TopRep R H}

namespace TopRep

def relInvariantsFunctor : TopRep R G ⥤ TopRep R (G ⧸ N) where
  obj π_G       := TopRep.of (π_G.ρ.relInvariants_infl N)
  map f         := TopRep.ofHom (ContRepresentation.relInvariants_intertwining' _ _ N f.hom)

variable (R) in
@[simps] def infl_ι : (relInvariantsFunctor N ⋙ resFunctor R (QuotientGroup.mk' N)) ⟶ 𝟭 (TopRep R G)
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

abbrev infl_app (n : ℕ) (π : TopRep R G) :
    (relInvariantsFunctor N ⋙ continuousCohomology R (G ⧸ N) n).obj π
    ⟶ (continuousCohomology R G n).obj ((𝟭 _).obj π) :=
  (resNatTrans R (QuotientGroup.mk'' N) n).app
  ((relInvariantsFunctor N).obj π)
  ≫ (continuousCohomology R G n).map
  ((infl_ι R N).app π)

set_option backward.isDefEq.respectTransparency false in
lemma infl_naturality (n : ℕ) {π₁ π₂ : TopRep R G} (f : π₁ ⟶ π₂) :
    (relInvariantsFunctor N ⋙ continuousCohomology R (G ⧸ N) n).map f
    ≫ (infl_app N n π₂) = (infl_app N n π₁) ≫ (continuousCohomology R G n).map f := by
  rw [Functor.comp_map, infl_app]
  simp only [←Category.assoc]
  have := (resNatTrans R (QuotientGroup.mk'' N) n).naturality  ((relInvariantsFunctor N).map f)
  simp only [Functor.comp_map] at this
  simp only [this, infl_app, Category.assoc, ←Functor.map_comp]
  apply congr_arg
  apply congr_arg
  convert! (infl_ι R N).naturality f

noncomputable def inflNatTrans (n : ℕ) :
    relInvariantsFunctor N ⋙ continuousCohomology R (G ⧸ N) n ⟶ continuousCohomology R G n where
  app            := infl_app N n
  naturality _ _ f := by
    /-
    Note that the following proof is a lot quicker than `exact infl_naturality N n f`.
    -/
    have := infl_naturality N n f
    simpa only [Functor.id_obj] using this

end ContinuousCohomology
end
