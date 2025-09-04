import Mathlib

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed L] [CharZero K] [CharZero L]

theorem Q2a (h : Module.finrank K L ≠ 1) : ∃ (p : ℕ) (hp : p.Prime) (M : IntermediateField K L),
  Module.finrank K M = p := sorry

variable {K L} in
noncomputable abbrev p (h : Module.finrank K L ≠ 1) := (Q2a K L h).choose

variable {K L} in
noncomputable abbrev M (h : Module.finrank K L ≠ 1) := (Q2a K L h).choose_spec.2.choose

theorem Q2b1 (h : Module.finrank K L ≠ 1) : ∃ x : M h,
  IsPrimitiveRoot x (p h) := sorry

theorem Q2b2 (h : Module.finrank K L ≠ 1) : ∃ β : L, ⊤ = IntermediateField.adjoin K {β} := sorry

variable {K L} in
noncomputable abbrev β (h : Module.finrank K L ≠ 1) := (Q2b2 K L h).choose

variable {K L} in
noncomputable abbrev hβ1 (h : Module.finrank K L ≠ 1) := (Q2b2 K L h).choose_spec

theorem Q2b3 (h : Module.finrank K L ≠ 1) : (β h) ^ (p h) ∈ M h := sorry

theorem Q2b4 (h : Module.finrank K L ≠ 1) : Algebra.norm (M h) ((β h) ^ (p h)) =
  (-1) ^ ((p h) - 1) * ⟨(β h) ^ (p h), Q2b3 K L h⟩ := sorry

theorem Q3c1 (hKL : ∃ k : K, k ^ 2 = -1) (h : Module.finrank K L ≠ 1) :
    ∃ γ : L, (β h) = γ ^ (p h) := sorry

theorem Q3c2 (hKL : ∃ k : K, k ^ 2 = -1) (h : Module.finrank K L ≠ 1) :
    ∃ m : M h, m ^ (p h) = ⟨(β h) ^ (p h), Q2b3 K L h⟩ := by sorry

theorem Q3c3 (hKL : ∃ k : K, k ^ 2 = -1) : Module.finrank K L = 1 := by sorry
