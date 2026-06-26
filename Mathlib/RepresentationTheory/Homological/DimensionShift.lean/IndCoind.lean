/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.RepresentationTheory.FiniteIndex
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Induced

/-!

# Specialized Induced and Coinduced Representations


-/

@[expose] public section

universe w u v

namespace Representation

variable {R G V : Type*} [Ring R] [Monoid G] [AddCommGroup V] [Module R V]
  (ρ : Representation R G V)

/-- Given a representation `ρ` of `G` on `V`, `coind₁' ρ` is the representation of `G`
on `G → V`, where the action of `G` is `(g f) x = ρ g (f (x * g))`. -/
@[simps] def coind₁' : Representation R G (G → V) where
  toFun g := {
    toFun f x := ρ g (f (x * g))
    map_add' _ _ := by ext; simp
    map_smul' _ _ := by ext; simp
  }
  map_one' := by ext; simp
  map_mul' g₁ g₂ := by ext; simp [mul_assoc]

/-- The linear map from `V` to `G → V` taking a vector `v : V` to the comstant function
with value `V`. If `ρ` is a representation of `G` on `V`, then this map intertwines
`ρ` and `ρ.coind₁'`. -/
@[simps] def coind₁'ι : V →ₗ[R] (G → V) where
  toFun     := Function.const G
  map_add'  := by simp
  map_smul' := by simp

/-- `ind₁' ρ` is the representation of `G` on `G →₀ V`, where the action is defined by
`ρ.ind₁' g f x = ρ g (f (x * g))`. -/
@[simps]
noncomputable def ind₁' {G : Type*} [Group G] (ρ : Representation R G V) :
    Representation R G (G →₀ V) where
  toFun g := Finsupp.lmapDomain _ _ (fun x ↦ x * g⁻¹) ∘ₗ Finsupp.mapRange.linearMap (ρ g)
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [mul_assoc]

/-- The natural projection `ind₁' ρ ⟶ ρ`, which takes `f : G →₀ V` to the sum of the
values of `f`. -/
@[simps] def ind₁'π : (G →₀ V) →ₗ[R] V where
  toFun f := f.sum (fun _ ↦ (1 : V →ₗ[R] V))
  map_add' _ _ := Finsupp.sum_add_index' (by simp) fun _ _ ↦ congrFun rfl
  map_smul' _ _ := by simp

end Representation


namespace Rep

variable {R : Type u} [Ring R] {G : Type v} [Group G]

open CategoryTheory Rep

/--
The functor which takes a representation `ρ` of `G` on `V` to the
coinduced representation on `G → V`, where the action of `G` is by `ρ` in `V` and by
right translation on `G`.
-/
def coind₁' : Rep.{w} R G ⥤ Rep R G where
  obj M := of M.ρ.coind₁'
  map φ := ofHom ⟨φ.hom.toLinearMap.compLeft G, fun g ↦ by ext; simp [hom_comm_apply]⟩

/--
The inclusion of a representation `M` of `G` in the coinduced representation `coind₁'.obj M`.
This map takes an element `m : M` to the constant function with value `M`.
-/
def coind₁'ι : 𝟭 (Rep.{max w v} R G) ⟶ coind₁' where
  app M := Rep.ofHom ⟨Representation.coind₁'ι, fun g ↦ by ext; simp⟩

/--
The functor taking a representation `M` of `G` to the induced representation on
the space `G →₀ M`. The action of `G` on `G →₀ M.V` is by left-translation on `G` and
by `M.ρ` on `M.V`.
-/
@[implicit_reducible]
noncomputable def ind₁' : Rep.{w} R G ⥤ Rep R G where
  obj M := of M.ρ.ind₁'
  map f := ofHom ⟨Finsupp.mapRange.linearMap f.hom.toLinearMap,
    fun g ↦ by ext; simp [hom_comm_apply]⟩

/-- The natural projection `ind₁'.obj M ⟶ M`, which takes `f : G →₀ M.V` to the sum of the
values of `f`. -/
@[implicit_reducible]
noncomputable def ind₁'π : ind₁' ⟶ 𝟭 (Rep.{max w v} R G) where
  app M := ofHom ⟨Representation.ind₁'π, fun g ↦ by ext; simp⟩
  naturality X Y f := by
    ext : 2
    simp only [ind₁', Functor.id_obj, hom_comp, ConcreteCategory.hom_ofHom,
      Representation.IntertwiningMap.comp_toLinearMap, Functor.id_map]
    ext; simp

end Rep
