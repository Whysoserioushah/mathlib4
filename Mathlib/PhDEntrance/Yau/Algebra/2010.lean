import Mathlib

theorem Q1 (V : Type*) [AddCommGroup V] [Module ℂ V] (A B : Module.End ℂ V)
  (hAB : A * B - B * A = B) : ∃ c1 c2 : ℂ, 1 ≤ Module.finrank ℂ
    (A.eigenspace c1 ⊓ B.eigenspace c2 : Submodule ℂ V) := sorry

theorem Q2a : ∃ f : ℂ →* Matrix (Fin 2) (Fin 2) ℝ, Function.Injective f := sorry

open Matrix.GeneralLinearGroup

theorem Q2b (f g : ℂ →* Matrix (Fin 2) (Fin 2) ℝ) (hf : Function.Injective f)
    (hg : Function.Injective g) : ∃ u : GL (Fin 2) ℝ, ∀ x : ℂ, f x = u * g x * u⁻¹ := sorry

theorem Q2c (U : GL (Fin 2) ℝ) (hx : Irreducible U.1.charpoly) :
  Nonempty (Subring.closure ((Matrix.scalar (α := ℝ) (Fin 2)).range ∪ {U.1}) ≃+* ℂ) := sorry

-- theorem Q2d (U U' : )