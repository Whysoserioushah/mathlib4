/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Antoine Chambert-Loir
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Ring.Action.Submonoid

/-!
# More operations on subalgebras

In this file we relate the definitions in `Mathlib/RingTheory/Ideal/Operations.lean` to subalgebras.
The contents of this file are somewhat random since both
`Mathlib/Algebra/Algebra/Subalgebra/Basic.lean` and `Mathlib/RingTheory/Ideal/Operations.lean` are
somewhat of a grab-bag of definitions, and this is whatever ends up in the intersection.
-/

assert_not_exists Cardinal

namespace AlgHom

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem ker_rangeRestrict (f : A →ₐ[R] B) : RingHom.ker f.rangeRestrict = RingHom.ker f :=
  Ideal.ext fun _ ↦ Subtype.ext_iff

end AlgHom

namespace Subalgebra

open Algebra

variable {R S : Type*} [CommSemiring R] [CommRing S] [Algebra R S]
variable (S' : Subalgebra R S)

/-- Suppose we are given `∑ i, lᵢ * sᵢ = 1` ∈ `S`, and `S'` a subalgebra of `S` that contains
`lᵢ` and `sᵢ`. To check that an `x : S` falls in `S'`, we only need to show that
`sᵢ ^ n • x ∈ S'` for some `n` for each `sᵢ`. -/
theorem mem_of_finset_sum_eq_one_of_pow_smul_mem
    {ι : Type*} (ι' : Finset ι) (s : ι → S) (l : ι → S)
    (e : ∑ i ∈ ι', l i * s i = 1) (hs : ∀ i, s i ∈ S') (hl : ∀ i, l i ∈ S') (x : S)
    (H : ∀ i, ∃ n : ℕ, (s i ^ n : S) • x ∈ S') : x ∈ S' := by
  suffices x ∈ Subalgebra.toSubmodule (Algebra.ofId S' S).range by
    obtain ⟨x, rfl⟩ := this
    exact x.2
  choose n hn using H
  let s' : ι → S' := fun x => ⟨s x, hs x⟩
  let l' : ι → S' := fun x => ⟨l x, hl x⟩
  have e' : ∑ i ∈ ι', l' i * s' i = 1 := by
    ext
    change S'.subtype (∑ i ∈ ι', l' i * s' i) = 1
    simpa only [map_sum, map_mul] using e
  have : Ideal.span (s' '' ι') = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← e']
    apply sum_mem
    intros i hi
    exact Ideal.mul_mem_left _ _ <| Ideal.subset_span <| Set.mem_image_of_mem s' hi
  let N := ι'.sup n
  have hN := Ideal.span_pow_eq_top _ this N
  apply (Algebra.ofId S' S).range.toSubmodule.mem_of_span_top_of_smul_mem _ hN
  rintro ⟨_, _, ⟨i, hi, rfl⟩, rfl⟩
  change s' i ^ N • x ∈ _
  rw [← tsub_add_cancel_of_le (show n i ≤ N from Finset.le_sup hi), pow_add, mul_smul]
  refine Submodule.smul_mem _ (⟨_, pow_mem (hs i) _⟩ : S') ?_
  exact ⟨⟨_, hn i⟩, rfl⟩

theorem mem_of_span_eq_top_of_smul_pow_mem
    (s : Set S) (l : s →₀ S) (hs : Finsupp.linearCombination S ((↑) : s → S) l = 1)
    (hs' : s ⊆ S') (hl : ∀ i, l i ∈ S') (x : S) (H : ∀ r : s, ∃ n : ℕ, (r : S) ^ n • x ∈ S') :
    x ∈ S' :=
  mem_of_finset_sum_eq_one_of_pow_smul_mem S' l.support (↑) l hs (fun x => hs' x.2) hl x H

end Subalgebra

section MulSemiringAction

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
variable (G : Type*) [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B]

/-- The set of fixed points under a group action, as a subring. -/
def FixedPoints.subring : Subring B where
  __ := FixedPoints.addSubgroup G B
  __ := FixedPoints.submonoid G B

/-- The set of fixed points under a group action, as a subalgebra. -/
def FixedPoints.subalgebra : Subalgebra A B where
  __ := FixedPoints.addSubgroup G B
  __ := FixedPoints.submonoid G B
  algebraMap_mem' r := by simp

end MulSemiringAction
