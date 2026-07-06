module

public import Mathlib

@[expose] public section

universe w u v

open CategoryTheory

variable {K : Type u} {p : ℕ} [Fact p.Prime] [Field K] [Algebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] -- this should go away once we prove ℚ_[p] is nonarch and finite extension of nonarch is nonarch http
  {M : Type u} [TopologicalSpace M] [AddCommGroup M] [DiscreteTopology M] [Finite M]
  (ρ : ContRepresentation ℤ (Field.absoluteGaloisGroup K) M)
  -- (A : TopRep ℤ (Field.absoluteGaloisGroup K))

instance (i : ℕ) : Finite (continuousCohomology i (TopRep.of ρ)) := sorry

lemma isZero_of_deg (i : ℕ) (hi : 2 < i) :
    Limits.IsZero (continuousCohomology i (TopRep.of ρ)) :=
  sorry

noncomputable abbrev localEulerChi : ℚ :=
  (Nat.card (continuousCohomology 0 (TopRep.of ρ)) *
      Nat.card (continuousCohomology 2 (TopRep.of ρ))) /
      Nat.card (continuousCohomology 1 (TopRep.of ρ))

notation3:65 "χ("ρ")" => localEulerChi ρ

theorem localEuler_eq : χ(ρ) = ‖(Nat.card M : ℚ_[p]) ^ Module.finrank ℚ_[p] K‖ := sorry

end
