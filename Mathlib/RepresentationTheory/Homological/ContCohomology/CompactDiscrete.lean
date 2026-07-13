import Mathlib.RepresentationTheory.Homological.ContCohomology.Inflation
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.ClopenNhdofOne


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

/-- The compact-open topology on the space of continuous maps from a compact space to a
discrete space is discrete: such a map takes finitely many values, and prescribing the value
on each (compact) fibre is an open condition. -/
instance ContinuousMap.instDiscreteTopologyOfCompactSpace {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [DiscreteTopology Y] :
    DiscreteTopology C(X, Y) := by
  refine discreteTopology_iff_isOpen_singleton.mpr fun f => ?_
  have hfin : (Set.range f).Finite :=
    (isCompact_range f.continuous).finite DiscreteTopology.isDiscrete
  have key : {f} = ⋂ y ∈ Set.range f, {g : C(X, Y) | Set.MapsTo g (f ⁻¹' {y}) {y}} := by
    ext g
    simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · rintro rfl y -
      exact fun x hx => hx
    · intro h
      ext x
      exact h (f x) ⟨x, rfl⟩ rfl
  rw [key]
  exact hfin.isOpen_biInter fun y _ =>
    ContinuousMap.isOpen_setOf_mapsTo (isClosed_singleton.preimage f.continuous).isCompact
      (isOpen_discrete _)

/-- The resolution of a discrete representation of a compact group consists of discrete
representations, since `C(G, M)` is discrete whenever `G` is compact and `M` is discrete. -/
instance (rep : TopRep R G) [DiscreteTopology rep] (n : ℕ) :
    DiscreteTopology (rep.resolutionX n) := by
  induction n with
  | zero => assumption
  | succ n ih => exact inferInstanceAs (DiscreteTopology C(G, rep.resolutionX n))

class TopRep.IsLocallyConst (rep : TopRep R G) : Prop where
  isLocallyConst (v : rep) : ∃ U : OpenSubgroup G, ∀ u ∈ U, rep.ρ u v = v

variable {R G}

/-- `rep.Descends N n v` states that `v : rep.resolutionX n` is constant on the cosets of `N`
in each of its variables, and that all of its innermost values are fixed by `N`. This is the
condition for `v` to be the inflation of an element of the resolution of the `G ⧸ N`-
representation on the `N`-invariants of `rep`; see `TopRep.Descends.exists_preimage`. -/
def TopRep.Descends (rep : TopRep R G) (N : Subgroup G) : (n : ℕ) → rep.resolutionX n → Prop
  | 0, v => ∀ u ∈ N, rep.ρ u v = v
  | n + 1, v => (∀ u ∈ N, ∀ x : G, v (u * x) = v x) ∧ ∀ x : G, rep.Descends N n (v x)

omit [CompactSpace G] in
lemma TopRep.Descends.mono {rep : TopRep R G} {N N' : Subgroup G} {n : ℕ}
    {v : rep.resolutionX n} (hv : rep.Descends N' n v) (h : N ≤ N') :
    rep.Descends N n v := by
  induction n with
  | zero => exact fun u hu => hv u (h hu)
  | succ n ih => exact ⟨fun u hu x => hv.1 u (h hu) x, fun x => ih (hv.2 x)⟩

/-- Every element of the resolution of a discrete, locally constant representation of a compact
group descends to the quotient by some open subgroup. -/
lemma ex_open_descends (rep : TopRep R G) [DiscreteTopology rep] [rep.IsLocallyConst]
    (n : ℕ) (v : rep.resolutionX n) : ∃ U : OpenSubgroup G, rep.Descends U.toSubgroup n v := by
  induction n with
  | zero => exact IsLocallyConst.isLocallyConst v
  | succ n ih =>
    -- `v` is a continuous map from `G` to a discrete space, so it is invariant under left
    -- translation by some open subgroup `U₁`.
    obtain ⟨U₁, hU₁⟩ := ex_open_of_cts_of_compact_of_discrete G (rep.resolutionX n) v
    -- `v` takes finitely many values, each of which descends by the inductive hypothesis.
    have hfin : (Set.range v).Finite :=
      (isCompact_range (ContinuousMap.continuous v)).finite DiscreteTopology.isDiscrete
    choose Uw hUw using ih
    refine ⟨U₁ ⊓ hfin.toFinset.inf Uw,
      fun u hu x => hU₁ x ⟨u, (OpenSubgroup.mem_inf.mp hu).1⟩, fun x => ?_⟩
    have hle : hfin.toFinset.inf Uw ≤ Uw (v x) :=
      Finset.inf_le (hfin.mem_toFinset.mpr ⟨x, rfl⟩)
    exact (hUw (v x)).mono fun a ha => hle ((OpenSubgroup.mem_inf.mp ha).2)

open CategoryTheory in
/-- The resolution-level inflation map: the morphism in `TopRep R G` from (the restriction to
`G` of) the resolution of the `G ⧸ N`-representation on the `N`-invariants of `rep` to the
resolution of `rep`, precomposing with `G → G ⧸ N` in every variable and including the
`N`-invariants into `rep`. This is the map underlying `ContinuousCohomology.inflApp`. -/
abbrev TopRep.inflResolutionX (N : Subgroup G) [N.Normal] (rep : TopRep R G) (n : ℕ) :
    res (QuotientGroup.mk' N) (resolutionX ((relInvariantsFunctor N).obj rep) n) ⟶
      resolutionX rep n :=
  resolutionXRes ((relInvariantsFunctor N).obj rep) (QuotientGroup.mk'' N) n ≫
    resolutionMap ((inflι R N).app rep) n

omit [CompactSpace G] in
/-- An element of `rep.resolutionX n` which descends with respect to an open normal subgroup
`N` is the inflation of an element of the resolution of the quotient representation. -/
lemma TopRep.Descends.exists_preimage {rep : TopRep R G} {N : OpenNormalSubgroup G} {n : ℕ}
    {v : rep.resolutionX n} (hv : rep.Descends N.toSubgroup n v) :
    ∃ w, (inflResolutionX N.toSubgroup rep n).hom w = v := by
  induction n with
  | zero =>
    refine ⟨⟨v, hv⟩, ?_⟩
    rfl
  | succ n ih =>
    obtain ⟨htrans, hvals⟩ := hv
    -- `v` factors through `G ⧸ N`.
    have hcoset : ∀ x y : G, (x : G ⧸ N.toSubgroup) = (y : G ⧸ N.toSubgroup) → v x = v y := by
      intro x y hxy
      have hu : x⁻¹ * y ∈ N.toSubgroup := QuotientGroup.eq.mp hxy
      have h1 := htrans (x * (x⁻¹ * y) * x⁻¹) (N.isNormal'.conj_mem _ hu x) x
      rw [inv_mul_cancel_right, mul_inv_cancel_left] at h1
      exact h1.symm
    -- Choose a preimage of the value of `v` on each coset; the resulting function on the
    -- discrete space `G ⧸ N` is automatically continuous.
    choose W hW using fun q : G ⧸ N.toSubgroup => ih (hvals q.out)
    refine ⟨⟨W, continuous_of_discreteTopology⟩, ContinuousMap.ext fun x => ?_⟩
    change (inflResolutionX N.toSubgroup rep n).hom (W (x : G ⧸ N.toSubgroup)) = v x
    rw [hW]
    exact hcoset _ _ (QuotientGroup.out_eq' _)

/-- Every element of the resolution of a discrete, locally constant representation of a compact
group is the inflation of an element of the resolution of the `N`-invariants over `G ⧸ N`,
for some open *normal* subgroup `N`. -/
lemma isInflation (rep : TopRep R G) [DiscreteTopology rep] [rep.IsLocallyConst] (n : ℕ)
    (v : rep.resolutionX n) :
    ∃ N : OpenNormalSubgroup G, ∃ w, (inflResolutionX N.toSubgroup rep n).hom w = v := by
  obtain ⟨U, hU⟩ := ex_open_descends rep n v
  obtain ⟨N, hNU⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one
    ⟨U.isClosed, U.isOpen⟩ U.one_mem
  exact ⟨N, (hU.mono fun a ha => hNU ha).exists_preimage⟩


/-- Let `rep` be a discrete representation of a compact group in which every vector is fixed
by an open subgroup of `G`. Then every element of `C(G, C(G, ⋯ C(G, rep)))` in the resolution
of `rep` is also fixed by an open subgroup of `G`.

The hypothesis `hrep` is exactly the `n = 0` case; it is not automatic, since
`ContRepresentation` imposes no continuity in the group variable. -/
lemma ex_open_fixing_resolutionX (rep : TopRep R G) [DiscreteTopology rep]
    (hrep : ∀ σ : rep, ∃ U : OpenSubgroup G, ∀ u ∈ U, rep.ρ u σ = σ)
    (n : ℕ) (σ : rep.resolutionX n) :
    ∃ U : OpenSubgroup G, ∀ u ∈ U, (rep.resolutionX n).ρ u σ = σ := by
  induction n with
  | zero => exact hrep σ
  | succ n ih =>
    -- `σ` is a continuous map from `G` to the discrete space `rep.resolutionX n`,
    -- so it is invariant under left translation by some open subgroup `U₁`.
    obtain ⟨U₁, hU₁⟩ := ex_open_of_cts_of_compact_of_discrete G (rep.resolutionX n) σ
    -- `σ` takes finitely many values, each fixed by an open subgroup
    -- by the inductive hypothesis.
    have hfin : (Set.range σ).Finite :=
      (isCompact_range (ContinuousMap.continuous σ)).finite DiscreteTopology.isDiscrete
    choose Uv hUv using ih
    refine ⟨U₁ ⊓ hfin.toFinset.inf Uv, fun u hu => ?_⟩
    obtain ⟨hu₁, hu₂⟩ := OpenSubgroup.mem_inf.mp hu
    refine ContinuousMap.ext fun x => ?_
    have h₁ : σ (u⁻¹ * x) = σ x := hU₁ x ⟨u⁻¹, inv_mem hu₁⟩
    change (rep.resolutionX n).ρ u (σ (u⁻¹ * x)) = σ x
    rw [h₁]
    have hle : hfin.toFinset.inf Uv ≤ Uv (σ x) :=
      Finset.inf_le (hfin.mem_toFinset.mpr ⟨x, rfl⟩)
    exact hUv (σ x) u (hle hu₂)
