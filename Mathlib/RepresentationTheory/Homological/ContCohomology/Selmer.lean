/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, David Kurniadi Angdinata
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
## The Selmer group of a continuous Galois representation

This file defines a general notion of a *Selmer group* for a continuous Galois representation `A`
over a field `k`, as the intersection of the pullbacks of the maps `Hⁿ(K, A) → Hⁿ(Kᵥ, Aᵥ)` with
respect to a set of local conditions `Lᵥ ⊆ Hⁿ(Kᵥ, Aᵥ)`, sometimes called the *Selmer structure*.

Here `Kᵥ` is a `K`-algebra for each place `v` in an arbitrary indexing set `V`,
which induces maps between absolute Galois groups and hence maps between cohomology groups,
and `Lᵥ` is a choice of a `k`-subspace for each `v` in the indexing set `V`.

When `V` is the set of places of a global field `K`, `A` is the `m`-torsion subgroup of an abelian
variety over `K`, `Lᵥ` is the image of the local Kummer map associated to multiplication by `m`,
and `n = 1`, this recovers the classical definition of the `m`-Selmer group.

## Reference

* [Rubin, *Euler systems*](https://swc-math.github.io/notes/files/99RubinES.pdf)
-/

@[expose] public section

universe u v w

open CategoryTheory

variable {K : Type u} [Field K] (I : Type v) (f : I → Type u) [∀ i, Field (f i)]
  [∀ i, Algebra K (f i)] (k : Type w) [Ring k] [TopologicalSpace k]
  (A : TopRep k (Field.absoluteGaloisGroup K)) {n : ℕ}
  -- Note: the restriction is along the *coercion* of the continuous hom to a `MonoidHom`, which is
  -- what `ContinuousCohomology.map` uses; writing `.toMonoidHom` here instead would only be
  -- defeq to that after unfolding `MonoidHomClass.toMonoidHom`, which breaks `simp`/`rw`.
  (L : (i : I) → Submodule k (continuousCohomology n
    (TopRep.res (Field.absoluteGaloisGroup.map (algebraMap K (f i)) :
      Field.absoluteGaloisGroup (f i) →* _) A)))

namespace ContinuousCohomology

/-- The Selmer group of a continuous Galois representation. -/
@[simps!]
noncomputable def selmer : Submodule k (continuousCohomology n A) :=
  ⨅ i, (L i).comap (ContinuousCohomology.map
    (Field.absoluteGaloisGroup.map (algebraMap K (f i))) (𝟙 _) n).hom.toLinearMap

lemma mem_selmer {c : continuousCohomology n A} :
    c ∈ selmer I f k A L ↔ ∀ i, ContinuousCohomology.map
      (Field.absoluteGaloisGroup.map (algebraMap K (f i))) (𝟙 _) n c ∈ L i := by
  simp [selmer]

-- TODO add selmer_eq_iInf
-- TODO add singular quotients
-- TODO add selmer_eq_ker_pi
-- TODO connect to Tate--Shafarevich groups
-- TODO refactor in terms of Selmer structures
-- TODO add examples of unramified/geometric Selmer structures

end ContinuousCohomology
