import Mathlib

section should_be_in_mathlib

variable {G M : Type*} [Group G] [AddCommGroup M]

structure Representation.Equiv {R : Type*} [CommSemiring R] {G : Type*} [Group G]
    {M₁ M₂ : Type*} [_root_.AddCommMonoid M₁] [_root_.AddCommMonoid M₂] [Module R M₁] [Module R M₂]
    (ρ₁ : Representation R G M₁) (ρ₂ : Representation R G M₂)
     extends M₁ ≃ₗ[R] M₂ where
     exchange : ∀(g : G), ∀(m : M₁), toFun (ρ₁ g m) = (ρ₂ g (toFun m))

end should_be_in_mathlib

variable (G V W : Type*) [Group G] [Fintype G] [AddCommGroup V] [AddCommGroup W]
  [Module ℂ V] [Module ℂ W] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
  (ρV : Representation ℂ G V) (ρW : Representation ℂ G W)

def homAsGMod_aux (g : G) : (V →ₗ[ℂ] W) → V →ₗ[ℂ] W := fun f ↦ (ρW g ∘ₗ f ∘ₗ ρV g⁻¹)

lemma homAsGMod_aux_map_add (g : G) (f₁ f₂ : V →ₗ[ℂ] W) :
    homAsGMod_aux G V W ρV ρW g (f₁ + f₂) =
   homAsGMod_aux G V W ρV ρW g f₁ + homAsGMod_aux G V W ρV ρW g f₂ := by
  sorry

lemma homAsGMod_aux_map_smul (g : G) (c : ℂ) (f : V →ₗ[ℂ] W) :
    homAsGMod_aux G V W ρV ρW g (c • f) = c • homAsGMod_aux G V W ρV ρW g f := by
  sorry

def homAsGMod_hom (g : G) : (V →ₗ[ℂ] W) →ₗ[ℂ] (V →ₗ[ℂ] W) where
  toFun := homAsGMod_aux G V W ρV ρW g
  map_add' := homAsGMod_aux_map_add G V W ρV ρW g
  map_smul' := homAsGMod_aux_map_smul G V W ρV ρW g

lemma homAsGMod_hom_map_one : homAsGMod_hom G V W ρV ρW 1 = 1 := by sorry

lemma homAsGMod_hom_map_mul (g h : G) : homAsGMod_hom G V W ρV ρW (g * h) =
    homAsGMod_hom G V W ρV ρW g * homAsGMod_hom G V W ρV ρW h := by sorry

def homAsGMod : Representation ℂ G (V →ₗ[ℂ] W) where
  toFun := homAsGMod_hom G V W ρV ρW
  map_one' := homAsGMod_hom_map_one G V W ρV ρW
  map_mul' := homAsGMod_hom_map_mul G V W ρV ρW

-- need to strengthen into iso of representations
theorem isoInvariant : Nonempty ((homAsGMod G V W ρV ρW ).invariants ≃ₗ[ℂ]
  (ρV.asModule →ₗ[MonoidAlgebra ℂ G] ρW.asModule)) := sorry

def dualAsGMod_aux (g : G) : Module.Dual ℂ V → Module.Dual ℂ V := fun f ↦ f ∘ₗ ρV g⁻¹

lemma dualAsGMod_aux_map_add (g : G) (f₁ f₂ : Module.Dual ℂ V) :
    dualAsGMod_aux G V ρV g (f₁ + f₂) =
    dualAsGMod_aux G V ρV g f₁ + dualAsGMod_aux G V ρV g f₂ := by
  sorry

lemma dualAsGMod_aux_map_smul (g : G) (c : ℂ) (f : Module.Dual ℂ V) :
    dualAsGMod_aux G V ρV g (c • f) = c • dualAsGMod_aux G V ρV g f := by sorry

def dualAsGMod_hom (g : G) : Module.Dual ℂ V →ₗ[ℂ] Module.Dual ℂ V where
  toFun := dualAsGMod_aux G V ρV g
  map_add' := dualAsGMod_aux_map_add G V ρV g
  map_smul' := dualAsGMod_aux_map_smul G V ρV g

lemma dualAsGMod_hom_map_one : dualAsGMod_hom G V ρV 1 = 1 := by sorry

lemma dualAsGMod_hom_map_mul (g h : G) : dualAsGMod_hom G V ρV (g * h) =
    dualAsGMod_hom G V ρV g * dualAsGMod_hom G V ρV h := by sorry

def dualAsGMod : Representation ℂ G (Module.Dual ℂ V) where
  toFun := dualAsGMod_hom G V ρV
  map_one' := dualAsGMod_hom_map_one G V ρV
  map_mul' := dualAsGMod_hom_map_mul G V ρV

-- need to strengthen here as well
theorem endHomIsoHomEnd : Nonempty (((Representation.linHom ρV ρV).asModule →ₗ[MonoidAlgebra ℂ G]
    (Representation.linHom ρW ρW).asModule) ≃ₗ[ℂ] Module.End (MonoidAlgebra ℂ G)
    (Representation.linHom ρV ρW).asModule) := sorry

-- missed q2b
