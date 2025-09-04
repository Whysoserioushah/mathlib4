import Mathlib.RingTheory.Bezout
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Tactic.FieldSimp

variable (K : Type*) [Field K] (A : Subring K) [Nontrivial A]

assert_not_exists ValuationRing.isLocalRing

theorem Q3a (hA : ∀ x : K, x ∈ A ∨ x⁻¹ ∈ A) : IsLocalRing A := sorry

theorem Q3b (hA : ∀ x : K, x ∈ A ∨ x⁻¹ ∈ A) : IsIntegrallyClosed A := sorry
