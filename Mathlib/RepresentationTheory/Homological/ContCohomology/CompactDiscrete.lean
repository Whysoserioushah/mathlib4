import Mathlib.RepresentationTheory.Homological.ContCohomology.Inflation
import Mathlib.Topology.Algebra.OpenSubgroup


variable (R G M : Type*)
  [CommRing R] [TopologicalSpace R]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : ContRepresentation R G M)

omit [AddCommGroup M] in
lemma ex_open_of_cts_of_compact_of_discrete (f : C(G, M)) :
    ∃ U : OpenSubgroup G, ∀ x : G, ∀ u : U, f (u * x) = f x := by
  -- Since `M` is discrete, the pairs `(g, x)` with `f (g * x) = f x` form an open set.
  have hD : IsOpen {p : G × G | f (p.1 * p.2) = f p.2} :=
    (isOpen_discrete (Set.diagonal M)).preimage
      ((f.continuous.comp (continuous_fst.mul continuous_snd)).prodMk
        (f.continuous.comp continuous_snd))
  -- It contains `{1} × G`, so by the tube lemma it contains `u × G` for some
  -- open neighbourhood `u` of `1`.
  obtain ⟨u, v, hu, -, h1u, hvuniv, huv⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := (1 : G))) isCompact_univ hD
      (by rintro ⟨g, x⟩ ⟨rfl, -⟩; simp)
  -- The elements `g` with `f (g * x) = f x` for all `x` form a subgroup containing `u`,
  -- hence an open subgroup.
  let S : Subgroup G :=
    { carrier := {g : G | ∀ x : G, f (g * x) = f x}
      one_mem' := fun x => by rw [one_mul]
      mul_mem' := fun {a b} ha hb x => by rw [mul_assoc, ha, hb]
      inv_mem' := fun {a} ha x => by
        have h := ha (a⁻¹ * x)
        rw [mul_inv_cancel_left] at h
        exact h.symm }
  have hS : IsOpen (S : Set G) :=
    S.isOpen_of_mem_nhds <| Filter.mem_of_superset (hu.mem_nhds (h1u rfl))
      fun g hg x => huv (Set.mk_mem_prod hg (hvuniv trivial))
  exact ⟨⟨S, hS⟩, fun x u => u.2 x⟩

open TopRep ContinuousCohomology
example (rep : TopRep R G) [DiscreteTopology rep] (n : ℕ) (σ : rep.resolutionX n) :
    ∃ U : OpenSubgroup G, ∀ u ∈ U, (rep.resolutionX n).ρ u σ = σ := by
  sorry
