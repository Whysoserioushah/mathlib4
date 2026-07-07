/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Cup

/-!
# The cup product on continuous group cohomology

This file descends the cup product pairing on homogeneous cochains constructed in
`Mathlib/RepresentationTheory/Homological/ContCohomology/Cup.lean` to a pairing

`cup : continuousCohomology m (.of ρ1) ⟶
  TopModuleCat.linHom (continuousCohomology n (.of ρ2)) (continuousCohomology r (.of ρ3))`

for `r = m + n`, induced by an intertwining map `f : ρ1 →ⁱL linHom ρ2 ρ3`.

## Implementation notes

The descent is organised so that all topological content is carried by open quotient maps:

* cycles of a complex of topological modules are identified with the kernel of the
  differential carrying the subspace topology (`HomologicalComplex.cyclesIsoKer`);
* the homology projection `homologyπ` is an open quotient map
  (`HomologicalComplex.isOpenQuotientMap_homologyπ`), because homology is the cokernel of
  `toCycles` and cokernels in `TopModuleCat` carry the quotient topology;
* maps out of homology are obtained categorically from the cokernel universal property
  (`HomologicalComplex.homologyIsCokernel`), so their continuity is automatic;
* continuity of the cup product pairing in *both* homology classes simultaneously follows from
  the joint continuity of the cochain-level pairing by descending along a product of open
  quotient maps (`IsOpenQuotientMap.prodMap`) and currying at the very end, which avoids any
  local compactness assumptions.

## Main definitions

* `ContRepresentation.cup`: the cup product on continuous cohomology.
-/

@[expose] public section

universe u v w

open CategoryTheory Limits TopCup

section Phase0

variable {R : Type u} [Ring R] [TopologicalSpace R]

/-- An isomorphism of topological modules as a homeomorphism. -/
def TopModuleCat.homeoOfIso {M N : TopModuleCat.{v} R} (e : M ≅ N) : ↥M ≃ₜ ↥N where
  toFun := e.hom.hom
  invFun := e.inv.hom
  left_inv x := congr($(e.hom_inv_id) x)
  right_inv y := congr($(e.inv_hom_id) y)
  continuous_toFun := e.hom.hom.cont
  continuous_invFun := e.inv.hom.cont

variable {ι : Type w} {c : ComplexShape ι} (K : HomologicalComplex (TopModuleCat.{v} R) c)

/-- The cycles of a complex of topological modules, identified with the kernel of the
differential carrying the subspace topology. -/
noncomputable def HomologicalComplex.cyclesIsoKer (i j : ι) (hij : c.next i = j) :
    K.cycles i ≅ TopModuleCat.ker (K.d i j) :=
  KernelFork.mapIsoOfIsLimit (K.cyclesIsKernel i j hij) (TopModuleCat.isLimitKer _) (Iso.refl _)

@[reassoc (attr := simp)]
lemma HomologicalComplex.cyclesIsoKer_hom_kerι (i j : ι) (hij : c.next i = j) :
    (K.cyclesIsoKer i j hij).hom ≫ TopModuleCat.kerι (K.d i j) = K.iCycles i := by
  refine (KernelFork.mapOfIsLimit_ι _ (TopModuleCat.isLimitKer (K.d i j)) (𝟙 _)).trans ?_
  rfl

@[reassoc (attr := simp)]
lemma HomologicalComplex.cyclesIsoKer_inv_iCycles (i j : ι) (hij : c.next i = j) :
    (K.cyclesIsoKer i j hij).inv ≫ K.iCycles i = TopModuleCat.kerι (K.d i j) := by
  rw [Iso.inv_comp_eq]
  exact (K.cyclesIsoKer_hom_kerι i j hij).symm

@[simp]
lemma HomologicalComplex.cyclesIsoKer_hom_apply_coe (i j : ι) (hij : c.next i = j)
    (z : ↥(K.cycles i)) :
    ((K.cyclesIsoKer i j hij).hom z).1 = K.iCycles i z :=
  congr($(K.cyclesIsoKer_hom_kerι i j hij) z)

@[simp]
lemma HomologicalComplex.iCycles_cyclesIsoKer_inv_apply (i j : ι) (hij : c.next i = j)
    (w : ↥(TopModuleCat.ker (K.d i j))) :
    K.iCycles i ((K.cyclesIsoKer i j hij).inv w) = w.1 :=
  congr($(K.cyclesIsoKer_inv_iCycles i j hij) w)

/-- The homology of a complex of topological modules, identified with the quotient of the
cycles by the boundaries, carrying the quotient topology. -/
noncomputable def HomologicalComplex.homologyIsoCoker (i j : ι) (hij : c.prev j = i) :
    K.homology j ≅ TopModuleCat.coker (K.toCycles i j) :=
  CokernelCofork.mapIsoOfIsColimit (K.homologyIsCokernel i j hij)
    (TopModuleCat.isColimitCoker _) (Iso.refl _)

@[reassoc (attr := simp)]
lemma HomologicalComplex.homologyπ_homologyIsoCoker_hom (i j : ι) (hij : c.prev j = i) :
    K.homologyπ j ≫ (K.homologyIsoCoker i j hij).hom =
      TopModuleCat.cokerπ (K.toCycles i j) := by
  refine (CokernelCofork.π_mapOfIsColimit (K.homologyIsCokernel i j hij) _ (𝟙 _)).trans ?_
  simp

/-- The homology projection of a complex of topological modules is an open quotient map. -/
lemma HomologicalComplex.isOpenQuotientMap_homologyπ (i j : ι) (hij : c.prev j = i) :
    IsOpenQuotientMap ⇑(K.homologyπ j).hom := by
  have h2 : K.homologyπ j =
      TopModuleCat.cokerπ (K.toCycles i j) ≫ (K.homologyIsoCoker i j hij).inv := by
    rw [Iso.eq_comp_inv, K.homologyπ_homologyIsoCoker_hom i j hij]
  rw [h2]
  exact ((TopModuleCat.homeoOfIso (K.homologyIsoCoker i j hij).symm).isOpenQuotientMap).comp
    (Submodule.isOpenQuotientMap_mkQ _)

/-- Applying the homology projection to a boundary gives zero. -/
lemma HomologicalComplex.homologyπ_toCycles_apply (i j : ι) (y : ↥(K.X i)) :
    K.homologyπ j (K.toCycles i j y) = 0 :=
  congr($(K.toCycles_comp_homologyπ i j) y)

end Phase0

namespace ContRepresentation

open TopRep

variable {k : Type u} {G : Type v} [CommRing k] [TopologicalSpace k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]

section Phase1

variable {M1 M2 M3 : Type v}
  [AddCommGroup M1] [Module k M1] [TopologicalSpace M1] [IsTopologicalAddGroup M1]
  [ContinuousSMul k M1] [DiscreteTopology M1]
  [AddCommGroup M2] [Module k M2] [TopologicalSpace M2] [IsTopologicalAddGroup M2]
  [ContinuousSMul k M2]
  [AddCommGroup M3] [Module k M3] [TopologicalSpace M3] [IsTopologicalAddGroup M3]
  [ContinuousSMul k M3]
  {ρ1 : ContRepresentation k G M1} {ρ2 : ContRepresentation k G M2}
  {ρ3 : ContRepresentation k G M3} (f : ρ1 →ⁱL linHom ρ2 ρ3)

/-- `cupCochain` vanishes when its first argument is zero. -/
@[simp]
lemma cupCochain_zero_apply (m n r : ℕ) (hr : r = m + n)
    (τ : (homogeneousCochains (.of ρ2)).X n) :
    cupCochain f m n r hr 0 τ = 0 :=
  congr($(map_zero (cupCochain f m n r hr).hom) τ)

/-- The cup product of two cocycles is a cocycle. -/
lemma d_cupCochain_eq_zero (m n r : ℕ) (hr : r = m + n)
    {σ : (homogeneousCochains (.of ρ1)).X m} {τ : (homogeneousCochains (.of ρ2)).X n}
    (hσ : (homogeneousCochains (.of ρ1)).d m (m + 1) σ = 0)
    (hτ : (homogeneousCochains (.of ρ2)).d n (n + 1) τ = 0) :
    (homogeneousCochains (.of ρ3)).d r (r + 1) (cupCochain f m n r hr σ τ) = 0 := by
  have h := cup_d_comm ρ1 ρ2 ρ3 f m n r hr σ τ
  rw [hσ, hτ, cupCochain_zero_apply, cupCochain_apply_zero] at h
  refine h.trans ?_
  have h0 : (0 : ↥((homogeneousCochains (.of ρ3)).X (r + 1))) +
      (-1 : ℤ) ^ m • (0 : ↥((homogeneousCochains (.of ρ3)).X (r + 1))) = 0 := by simp
  exact h0

/-- Cupping a coboundary with a cocycle gives a coboundary. -/
lemma d_cupCochain_of_d_eq_zero (m n r : ℕ) (hr : r = m + n)
    (σ : (homogeneousCochains (.of ρ1)).X m) {τ : (homogeneousCochains (.of ρ2)).X n}
    (hτ : (homogeneousCochains (.of ρ2)).d n (n + 1) τ = 0) :
    cupCochain f (m + 1) n (r + 1) (by omega) ((homogeneousCochains (.of ρ1)).d m (m + 1) σ) τ =
      (homogeneousCochains (.of ρ3)).d r (r + 1) (cupCochain f m n r hr σ τ) := by
  have h := cup_d_comm ρ1 ρ2 ρ3 f m n r hr σ τ
  rw [hτ, cupCochain_apply_zero] at h
  have h0 : ∀ x : ↥((homogeneousCochains (.of ρ3)).X (r + 1)),
      x = x + (-1 : ℤ) ^ m • (0 : ↥((homogeneousCochains (.of ρ3)).X (r + 1))) := by simp
  exact (h0 _).trans h.symm

/-- Cupping a cocycle with a coboundary gives a coboundary. -/
lemma cupCochain_d_of_d_eq_zero (m n r : ℕ) (hr : r = m + n)
    {σ : (homogeneousCochains (.of ρ1)).X m} (τ : (homogeneousCochains (.of ρ2)).X n)
    (hσ : (homogeneousCochains (.of ρ1)).d m (m + 1) σ = 0) :
    cupCochain f m (n + 1) (r + 1) (by omega) σ ((homogeneousCochains (.of ρ2)).d n (n + 1) τ) =
      (-1 : ℤ) ^ m • (homogeneousCochains (.of ρ3)).d r (r + 1) (cupCochain f m n r hr σ τ) := by
  have h := cup_d_comm ρ1 ρ2 ρ3 f m n r hr σ τ
  rw [hσ, cupCochain_zero_apply] at h
  rw [h]
  have h0 : ∀ x : ↥((homogeneousCochains (.of ρ3)).X (r + 1)),
      (-1 : ℤ) ^ m • ((0 : ↥((homogeneousCochains (.of ρ3)).X (r + 1))) + (-1 : ℤ) ^ m • x) =
        x := by
    intro x
    rw [zero_add, smul_smul, ← pow_add, Even.neg_one_pow ⟨m, rfl⟩, one_smul]
  exact (h0 _).symm

end Phase1

section CupHomology

/-- The projection from the kernel model of the cocycles onto continuous cohomology. -/
noncomputable def cocyclesπ (X : TopRep k G) (i : ℕ) :
    TopModuleCat.ker ((homogeneousCochains X).d i (i + 1)) ⟶ continuousCohomology i X :=
  ((homogeneousCochains X).cyclesIsoKer i (i + 1) (by simp)).inv ≫
    (homogeneousCochains X).homologyπ i

@[reassoc (attr := simp)]
lemma cyclesIsoKer_hom_cocyclesπ (X : TopRep k G) (i : ℕ) :
    ((homogeneousCochains X).cyclesIsoKer i (i + 1) (by simp)).hom ≫ cocyclesπ X i =
      (homogeneousCochains X).homologyπ i := by
  simp [cocyclesπ]

/-- The projection onto continuous cohomology is an open quotient map. -/
lemma isOpenQuotientMap_cocyclesπ (X : TopRep k G) (i : ℕ) :
    IsOpenQuotientMap ⇑(cocyclesπ X i).hom := by
  change IsOpenQuotientMap (⇑((homogeneousCochains X).homologyπ i).hom ∘
    ⇑(((homogeneousCochains X).cyclesIsoKer i (i + 1) (by simp)).inv).hom)
  exact IsOpenQuotientMap.comp
    ((homogeneousCochains X).isOpenQuotientMap_homologyπ _ i rfl)
    ((TopModuleCat.homeoOfIso
      ((homogeneousCochains X).cyclesIsoKer i (i + 1) (by simp)).symm).isOpenQuotientMap)

/-- Coboundaries die in continuous cohomology. -/
lemma cocyclesπ_d_apply (X : TopRep k G) (i : ℕ) (y : ↥((homogeneousCochains X).X i))
    (hmem : (homogeneousCochains X).d i (i + 1) y ∈
      ((homogeneousCochains X).d (i + 1) (i + 1 + 1)).hom.ker) :
    cocyclesπ X (i + 1) ⟨(homogeneousCochains X).d i (i + 1) y, hmem⟩ = 0 := by
  have h1 : (⟨(homogeneousCochains X).d i (i + 1) y, hmem⟩ :
      ↥(TopModuleCat.ker ((homogeneousCochains X).d (i + 1) (i + 1 + 1)))) =
      ((homogeneousCochains X).cyclesIsoKer (i + 1) (i + 1 + 1) (by simp)).hom
        ((homogeneousCochains X).toCycles i (i + 1) y) := by
    refine Subtype.ext ?_
    rw [(homogeneousCochains X).cyclesIsoKer_hom_apply_coe]
    exact congr($((homogeneousCochains X).toCycles_i (i := i) (j := i + 1)) y).symm
  rw [h1]
  exact (congr($(cyclesIsoKer_hom_cocyclesπ X (i + 1))
    ((homogeneousCochains X).toCycles i (i + 1) y))).trans
    ((homogeneousCochains X).homologyπ_toCycles_apply i (i + 1) y)

variable {M1 M2 M3 : Type v}
  [AddCommGroup M1] [Module k M1] [TopologicalSpace M1] [IsTopologicalAddGroup M1]
  [ContinuousSMul k M1] [DiscreteTopology M1]
  [AddCommGroup M2] [Module k M2] [TopologicalSpace M2] [IsTopologicalAddGroup M2]
  [ContinuousSMul k M2]
  [AddCommGroup M3] [Module k M3] [TopologicalSpace M3] [IsTopologicalAddGroup M3]
  [ContinuousSMul k M3]
  {ρ1 : ContRepresentation k G M1} {ρ2 : ContRepresentation k G M2}
  {ρ3 : ContRepresentation k G M3} (f : ρ1 →ⁱL linHom ρ2 ρ3) (m n r : ℕ) (hr : r = m + n)

/-- The cup product on the kernel models of the cocycles, for a fixed cocycle in the first
slot. -/
noncomputable def cupKer (σ : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ1)).d m (m + 1)))) :
    TopModuleCat.ker ((homogeneousCochains (.of ρ2)).d n (n + 1)) ⟶
      TopModuleCat.ker ((homogeneousCochains (.of ρ3)).d r (r + 1)) :=
  TopModuleCat.ofHom ((cupCochain f m n r hr σ.1 :
      ↥((homogeneousCochains (.of ρ2)).X n) →L[k] ↥((homogeneousCochains (.of ρ3)).X r)).restrict
    fun _ hτ ↦ d_cupCochain_eq_zero f m n r hr σ.2 hτ)

@[simp]
lemma cupKer_apply_coe
    (σ : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ1)).d m (m + 1))))
    (τ : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ2)).d n (n + 1)))) :
    (cupKer f m n r hr σ τ).1 = cupCochain f m n r hr σ.1 τ.1 := rfl

/-- The cup product pairing kills boundaries in the second slot. -/
lemma toCycles_comp_cupKer_vanish (i : ℕ)
    (σ : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ1)).d m (m + 1)))) :
    (homogeneousCochains (.of ρ2)).toCycles i n ≫
      ((homogeneousCochains (.of ρ2)).cyclesIsoKer n (n + 1) (by simp)).hom ≫
        cupKer f m n r hr σ ≫ cocyclesπ (.of ρ3) r = 0 := by
  by_cases hin : i + 1 = n
  · subst hin
    obtain rfl : r = m + i + 1 := by omega
    ext y
    have mem1 : (homogeneousCochains (.of ρ2)).d i (i + 1) y ∈
        ((homogeneousCochains (.of ρ2)).d (i + 1) (i + 1 + 1)).hom.ker :=
      homogeneousCochains.d_comp_d_apply (.of ρ2) i (i + 1) (i + 1 + 1) y
    have hiso : ((homogeneousCochains (.of ρ2)).cyclesIsoKer (i + 1) (i + 1 + 1) (by simp)).hom
        ((homogeneousCochains (.of ρ2)).toCycles i (i + 1) y) =
        ⟨(homogeneousCochains (.of ρ2)).d i (i + 1) y, mem1⟩ := by
      refine Subtype.ext ?_
      rw [(homogeneousCochains (.of ρ2)).cyclesIsoKer_hom_apply_coe]
      exact congr($((homogeneousCochains (.of ρ2)).toCycles_i (i := i) (j := i + 1)) y)
    change cocyclesπ (.of ρ3) (m + i + 1) (cupKer f m (i + 1) (m + i + 1) hr σ
      (((homogeneousCochains (.of ρ2)).cyclesIsoKer (i + 1) (i + 1 + 1) (by simp)).hom
        ((homogeneousCochains (.of ρ2)).toCycles i (i + 1) y))) = 0
    rw [hiso]
    have mem2 : (homogeneousCochains (.of ρ3)).d (m + i) (m + i + 1)
        ((-1 : ℤ) ^ m • cupCochain f m i (m + i) rfl σ.1 y) ∈
        ((homogeneousCochains (.of ρ3)).d (m + i + 1) (m + i + 1 + 1)).hom.ker :=
      homogeneousCochains.d_comp_d_apply (.of ρ3) (m + i) (m + i + 1) (m + i + 1 + 1) _
    have hd : (homogeneousCochains (.of ρ3)).d (m + i) (m + i + 1)
        ((-1 : ℤ) ^ m • cupCochain f m i (m + i) rfl σ.1 y) =
        (-1 : ℤ) ^ m • (homogeneousCochains (.of ρ3)).d (m + i) (m + i + 1)
          (cupCochain f m i (m + i) rfl σ.1 y) := by
      exact map_zsmul ((homogeneousCochains (.of ρ3)).d (m + i) (m + i + 1)).hom _ _
    have hval : cupKer f m (i + 1) (m + i + 1) hr σ
        ⟨(homogeneousCochains (.of ρ2)).d i (i + 1) y, mem1⟩ =
        (⟨(homogeneousCochains (.of ρ3)).d (m + i) (m + i + 1)
          ((-1 : ℤ) ^ m • cupCochain f m i (m + i) rfl σ.1 y), mem2⟩ :
          ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ3)).d (m + i + 1) (m + i + 1 + 1)))) :=
      Subtype.ext ((cupCochain_d_of_d_eq_zero f m i (m + i) rfl y σ.2).trans hd.symm)
    rw [hval]
    exact cocyclesπ_d_apply (.of ρ3) (m + i) _ mem2
  · rw [(homogeneousCochains (.of ρ2)).toCycles_eq_zero hin, zero_comp]

/-- The cup product with a fixed cocycle, descended to continuous cohomology in the second
slot. -/
noncomputable def cupHomologyAux
    (σ : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ1)).d m (m + 1)))) :
    continuousCohomology n (.of ρ2) ⟶ continuousCohomology r (.of ρ3) :=
  ((homogeneousCochains (.of ρ2)).homologyIsCokernel _ n rfl).desc
    (CokernelCofork.ofπ
      (((homogeneousCochains (.of ρ2)).cyclesIsoKer n (n + 1) (by simp)).hom ≫
        cupKer f m n r hr σ ≫ cocyclesπ (.of ρ3) r)
      (toCycles_comp_cupKer_vanish f m n r hr _ σ))

/-- The defining property of `cupHomologyAux`. -/
lemma cupHomologyAux_apply_cocyclesπ
    (σ : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ1)).d m (m + 1))))
    (τ : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ2)).d n (n + 1)))) :
    cupHomologyAux f m n r hr σ (cocyclesπ (.of ρ2) n τ) =
      cocyclesπ (.of ρ3) r (cupKer f m n r hr σ τ) := by
  have hfac := congr($(((homogeneousCochains (.of ρ2)).homologyIsCokernel _ n rfl).fac
    (CokernelCofork.ofπ
      (((homogeneousCochains (.of ρ2)).cyclesIsoKer n (n + 1) (by simp)).hom ≫
        cupKer f m n r hr σ ≫ cocyclesπ (.of ρ3) r)
      (toCycles_comp_cupKer_vanish f m n r hr _ σ)) WalkingParallelPair.one)
    (((homogeneousCochains (.of ρ2)).cyclesIsoKer n (n + 1) (by simp)).inv τ))
  have hcancel : ((homogeneousCochains (.of ρ2)).cyclesIsoKer n (n + 1) (by simp)).hom
      (((homogeneousCochains (.of ρ2)).cyclesIsoKer n (n + 1) (by simp)).inv τ) = τ :=
    congr($(Iso.inv_hom_id ((homogeneousCochains (.of ρ2)).cyclesIsoKer n (n + 1) (by simp))) τ)
  have hfac' : cupHomologyAux f m n r hr σ (cocyclesπ (.of ρ2) n τ) =
      cocyclesπ (.of ρ3) r (cupKer f m n r hr σ
        (((homogeneousCochains (.of ρ2)).cyclesIsoKer n (n + 1) (by simp)).hom
          (((homogeneousCochains (.of ρ2)).cyclesIsoKer n (n + 1) (by simp)).inv τ))) := hfac
  rw [hcancel] at hfac'
  exact hfac'

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex

/-- The cup product pairing on the kernel models is jointly continuous. -/
lemma continuous_cupKer_uncurry :
    Continuous fun p : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ1)).d m (m + 1))) ×
        ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ2)).d n (n + 1))) ↦
      cupKer f m n r hr p.1 p.2 := by
  refine continuous_induced_rng.2 (continuous_induced_rng.2 ?_)
  change Continuous fun p : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ1)).d m (m + 1))) ×
      ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ2)).d n (n + 1))) ↦
    (cupCochain f m n r hr p.1.1 p.2.1 : ↥((TopRep.of ρ3).resolution'.X r))
  have h2 : (fun p : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ1)).d m (m + 1))) ×
      ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ2)).d n (n + 1))) ↦
      (cupCochain f m n r hr p.1.1 p.2.1 : ↥((TopRep.of ρ3).resolution'.X r))) =
      fun p ↦ resolutionXCast (.of ρ3) (by omega : n + 1 + m = r + 1)
        ((cupPair f n m).1 p.1.1.1 p.2.1.1) := by
    funext p
    exact cupCochain_coe f m n r hr p.1.1 p.2.1
  rw [h2]
  exact (resolutionXCast (.of ρ3) (by omega : n + 1 + m = r + 1)).continuous.comp
    ((cupPair f n m).2.comp
      (((continuous_subtype_val.comp continuous_subtype_val).comp continuous_fst).prodMk
        ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd)))

/-- The cup product as a morphism from the cocycles into the internal hom of continuous
cohomologies. -/
noncomputable def cupCocyclesHom :
    TopModuleCat.ker ((homogeneousCochains (.of ρ1)).d m (m + 1)) ⟶
      TopModuleCat.linHom (continuousCohomology n (.of ρ2)) (continuousCohomology r (.of ρ3)) :=
  TopModuleCat.ofHom
    { toFun σ := (cupHomologyAux f m n r hr σ).hom
      map_add' σ σ' := by
        ext x
        obtain ⟨τ, rfl⟩ := (isOpenQuotientMap_cocyclesπ (.of ρ2) n).surjective x
        have hadd : cupKer f m n r hr (σ + σ') τ =
            cupKer f m n r hr σ τ + cupKer f m n r hr σ' τ :=
          Subtype.ext (congr($(map_add (cupCochain f m n r hr).hom σ.1 σ'.1) τ.1))
        change cupHomologyAux f m n r hr (σ + σ') (cocyclesπ (.of ρ2) n τ) =
          cupHomologyAux f m n r hr σ (cocyclesπ (.of ρ2) n τ) +
            cupHomologyAux f m n r hr σ' (cocyclesπ (.of ρ2) n τ)
        rw [cupHomologyAux_apply_cocyclesπ, cupHomologyAux_apply_cocyclesπ,
          cupHomologyAux_apply_cocyclesπ, hadd, (cocyclesπ (.of ρ3) r).hom.map_add]
      map_smul' c σ := by
        ext x
        obtain ⟨τ, rfl⟩ := (isOpenQuotientMap_cocyclesπ (.of ρ2) n).surjective x
        have hsmul : cupKer f m n r hr (c • σ) τ = c • cupKer f m n r hr σ τ :=
          Subtype.ext (congr($(map_smul (cupCochain f m n r hr).hom c σ.1) τ.1))
        change cupHomologyAux f m n r hr (c • σ) (cocyclesπ (.of ρ2) n τ) =
          c • cupHomologyAux f m n r hr σ (cocyclesπ (.of ρ2) n τ)
        rw [cupHomologyAux_apply_cocyclesπ, cupHomologyAux_apply_cocyclesπ, hsmul,
          (cocyclesπ (.of ρ3) r).hom.map_smul]
      cont := by
        refine continuous_induced_rng.2 (ContinuousMap.continuous_of_continuous_uncurry _ ?_)
        refine ((IsOpenQuotientMap.id.prodMap
          (isOpenQuotientMap_cocyclesπ (.of ρ2) n)).continuous_comp_iff).1 ?_
        have h3 : (fun q : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ1)).d m (m + 1))) ×
            ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ2)).d n (n + 1))) ↦
            cupHomologyAux f m n r hr q.1 (cocyclesπ (.of ρ2) n q.2)) =
            fun q ↦ cocyclesπ (.of ρ3) r (cupKer f m n r hr q.1 q.2) := by
          funext q
          exact cupHomologyAux_apply_cocyclesπ f m n r hr q.1 q.2
        change Continuous fun q : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ1)).d m (m + 1))) ×
            ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ2)).d n (n + 1))) ↦
          cupHomologyAux f m n r hr q.1 (cocyclesπ (.of ρ2) n q.2)
        rw [h3]
        exact (cocyclesπ (.of ρ3) r).hom.continuous.comp
          (continuous_cupKer_uncurry f m n r hr) }

/-- The defining property of `cupCocyclesHom`. -/
lemma cupCocyclesHom_apply_apply
    (σ : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ1)).d m (m + 1))))
    (τ : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ2)).d n (n + 1)))) :
    cupCocyclesHom f m n r hr σ (cocyclesπ (.of ρ2) n τ) =
      cocyclesπ (.of ρ3) r (cupKer f m n r hr σ τ) :=
  cupHomologyAux_apply_cocyclesπ f m n r hr σ τ

/-- The cup product pairing kills boundaries in the first slot. -/
lemma toCycles_comp_cupCocyclesHom_vanish (i : ℕ) :
    (homogeneousCochains (.of ρ1)).toCycles i m ≫
      ((homogeneousCochains (.of ρ1)).cyclesIsoKer m (m + 1) (by simp)).hom ≫
        cupCocyclesHom f m n r hr = 0 := by
  by_cases him : i + 1 = m
  · subst him
    obtain rfl : r = i + n + 1 := by omega
    ext y x
    obtain ⟨τ, rfl⟩ := (isOpenQuotientMap_cocyclesπ (.of ρ2) n).surjective x
    have mem1 : (homogeneousCochains (.of ρ1)).d i (i + 1) y ∈
        ((homogeneousCochains (.of ρ1)).d (i + 1) (i + 1 + 1)).hom.ker :=
      homogeneousCochains.d_comp_d_apply (.of ρ1) i (i + 1) (i + 1 + 1) y
    have hiso : ((homogeneousCochains (.of ρ1)).cyclesIsoKer (i + 1) (i + 1 + 1) (by simp)).hom
        ((homogeneousCochains (.of ρ1)).toCycles i (i + 1) y) =
        ⟨(homogeneousCochains (.of ρ1)).d i (i + 1) y, mem1⟩ := by
      refine Subtype.ext ?_
      rw [(homogeneousCochains (.of ρ1)).cyclesIsoKer_hom_apply_coe]
      exact congr($((homogeneousCochains (.of ρ1)).toCycles_i (i := i) (j := i + 1)) y)
    change cupCocyclesHom f (i + 1) n (i + n + 1) hr
      (((homogeneousCochains (.of ρ1)).cyclesIsoKer (i + 1) (i + 1 + 1) (by simp)).hom
        ((homogeneousCochains (.of ρ1)).toCycles i (i + 1) y)) (cocyclesπ (.of ρ2) n τ) = 0
    rw [hiso, cupCocyclesHom_apply_apply]
    have mem2 : (homogeneousCochains (.of ρ3)).d (i + n) (i + n + 1)
        (cupCochain f i n (i + n) rfl y τ.1) ∈
        ((homogeneousCochains (.of ρ3)).d (i + n + 1) (i + n + 1 + 1)).hom.ker :=
      homogeneousCochains.d_comp_d_apply (.of ρ3) (i + n) (i + n + 1) (i + n + 1 + 1) _
    have hval : cupKer f (i + 1) n (i + n + 1) hr
        ⟨(homogeneousCochains (.of ρ1)).d i (i + 1) y, mem1⟩ τ =
        (⟨(homogeneousCochains (.of ρ3)).d (i + n) (i + n + 1)
          (cupCochain f i n (i + n) rfl y τ.1), mem2⟩ :
          ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ3)).d (i + n + 1) (i + n + 1 + 1)))) :=
      Subtype.ext (d_cupCochain_of_d_eq_zero f i n (i + n) rfl y τ.2)
    rw [hval]
    exact cocyclesπ_d_apply (.of ρ3) (i + n) _ mem2
  · rw [(homogeneousCochains (.of ρ1)).toCycles_eq_zero him, zero_comp]

/-- The cup product on continuous group cohomology induced by an intertwining map
`f : ρ1 →ⁱL linHom ρ2 ρ3`. -/
noncomputable def cup :
    continuousCohomology m (.of ρ1) ⟶
      TopModuleCat.linHom (continuousCohomology n (.of ρ2)) (continuousCohomology r (.of ρ3)) :=
  ((homogeneousCochains (.of ρ1)).homologyIsCokernel _ m rfl).desc
    (CokernelCofork.ofπ
      (((homogeneousCochains (.of ρ1)).cyclesIsoKer m (m + 1) (by simp)).hom ≫
        cupCocyclesHom f m n r hr)
      (toCycles_comp_cupCocyclesHom_vanish f m n r hr _))

/-- The characterising property of the cup product: on cohomology classes of cocycles it is
induced by the cup product of cochains. -/
lemma cup_apply_apply
    (σ : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ1)).d m (m + 1))))
    (τ : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ2)).d n (n + 1)))) :
    cup f m n r hr (cocyclesπ (.of ρ1) m σ) (cocyclesπ (.of ρ2) n τ) =
      cocyclesπ (.of ρ3) r (cupKer f m n r hr σ τ) := by
  have hfac := congr($(((homogeneousCochains (.of ρ1)).homologyIsCokernel _ m rfl).fac
    (CokernelCofork.ofπ
      (((homogeneousCochains (.of ρ1)).cyclesIsoKer m (m + 1) (by simp)).hom ≫
        cupCocyclesHom f m n r hr)
      (toCycles_comp_cupCocyclesHom_vanish f m n r hr _)) WalkingParallelPair.one)
    (((homogeneousCochains (.of ρ1)).cyclesIsoKer m (m + 1) (by simp)).inv σ))
  have hcancel : ((homogeneousCochains (.of ρ1)).cyclesIsoKer m (m + 1) (by simp)).hom
      (((homogeneousCochains (.of ρ1)).cyclesIsoKer m (m + 1) (by simp)).inv σ) = σ :=
    congr($(Iso.inv_hom_id ((homogeneousCochains (.of ρ1)).cyclesIsoKer m (m + 1) (by simp))) σ)
  have hfac' : cup f m n r hr (cocyclesπ (.of ρ1) m σ) =
      cupCocyclesHom f m n r hr
        (((homogeneousCochains (.of ρ1)).cyclesIsoKer m (m + 1) (by simp)).hom
          (((homogeneousCochains (.of ρ1)).cyclesIsoKer m (m + 1) (by simp)).inv σ)) := hfac
  rw [hcancel] at hfac'
  rw [hfac', cupCocyclesHom_apply_apply]

end CupHomology

end ContRepresentation
