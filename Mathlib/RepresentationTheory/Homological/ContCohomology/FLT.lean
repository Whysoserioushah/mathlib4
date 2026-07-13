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

instance (i : ℕ) : Finite (continuousCohomology i (TopRep.of ρ)) := sorry

lemma isZero_of_deg (i : ℕ) (hi : 2 < i) :
    Limits.IsZero (continuousCohomology i (TopRep.of ρ)) :=
  sorry

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TotallyDisconnectedSpace G] [CompactSpace G] -- this is saying `G` is profinite group

set_option linter.unusedVariables false in
noncomputable def cohDimension (k : Type u) [CommRing k] [TopologicalSpace k] (G : Type v) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [TotallyDisconnectedSpace G] [CompactSpace G]
    (p : k) : WithTop ℕ :=
  sInf {m | ∀ (q : ℕ) (hq : m < q), (∀ (A : TopRep.{max w v} k G) [DiscreteTopology A]
      (hA : Module.IsTorsion k A), Submodule.torsionBy k (continuousCohomology q A) p = ⊥)}

lemma cDimension_le_iff (k : Type u) [CommRing k] [TopologicalSpace k] (p : k) (n : ℕ) :
    List.TFAE [cohDimension k G p ≤ n, (∀ q (hq : n < q), ∀ (B : TopRep k G) [DiscreteTopology B]
    (hB : Module.IsTorsionBy k B p), Limits.IsZero (continuousCohomology q B)),
    (∀ (B : TopRep k G) [IsSimpleModule k B] [DiscreteTopology B],
    Limits.IsZero (continuousCohomology (n + 1) B))] := sorry

noncomputable abbrev localEulerChi : ℚ :=
  (Nat.card (continuousCohomology 0 (TopRep.of ρ)) *
      Nat.card (continuousCohomology 2 (TopRep.of ρ))) /
      Nat.card (continuousCohomology 1 (TopRep.of ρ))

notation3:65 "χ("ρ")" => localEulerChi ρ

theorem localEuler_eq : χ(ρ) = ‖(Nat.card M : ℚ_[p]) ^ Module.finrank ℚ_[p] K‖ := sorry

end
