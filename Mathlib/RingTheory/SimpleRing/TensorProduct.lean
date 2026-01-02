/-
Copyright (c) 2025 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Yunzhou Xie
-/
import Mathlib
import Mathlib.RingTheory.TwoSidedIdeal.SpanAsSum

/-!
# Tensor product of simple algebras

# Tensor product of simple algebras over a field

In this file, we show that the tensor product of a simple algebra and a central simple algebra is
simple, which in particular implies that the tensor product of two central simple algebras is
another central simple algebra. This is a prerequisite for defining the group law of the Brauer
group.

## Main Results

* `TensorProduct.nontrivial`: The tensor product of two non-trivial algebras is non-trivial.
* `TensorProduct.simple`: The tensor product of a simple algebra and a central simple algebra
  is simple.

## References

* [StackProject 074B](https://stacks.math.columbia.edu/tag/074B)

## Tags
Noncommutative algebra, tensor product, simple algebra, central simple algebra

-/

universe u v v₁ v₂ v₃

variable (K : Type u) [Field K]
  {A : Type v₁} {B : Type v₂} {C : Type v₃} [Ring A] [Ring B] [Ring C]
  [Algebra K A] [Algebra K B] [Algebra K C]

open scoped TensorProduct

open Module
variable {K} in
/--
a non-zero element in an ideal that can be represented as a sum of tensor products of `n`-terms.
-/
structure is_obtainable_by_sum_tmul
    {ιA A B : Type*} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (x : A ⊗[K] B) (𝒜 : Basis ιA K A) (I : TwoSidedIdeal (A ⊗[K] B)) (n : ℕ) : Prop where
  mem : x ∈ I
  ne_zero : x ≠ 0
  rep : ∃ (s : Finset ιA) (_ : s.card = n) (f : ιA → B),
    x = ∑ i ∈ s, 𝒜 i ⊗ₜ[K] f i

variable {K} in
lemma is_obtainable_by_sum_tmul.exists_minimal_element
    {A B : Type*} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (ιA : Type*) (𝒜 : Basis ιA K A)
    (I : TwoSidedIdeal (A ⊗[K] B)) (hI : I ≠ ⊥) :
    ∃ (n : ℕ) (x : A ⊗[K] B), is_obtainable_by_sum_tmul x 𝒜 I n ∧
      ∀ (m : ℕ) (y : A ⊗[K] B) , is_obtainable_by_sum_tmul y 𝒜 I m → n ≤ m := by
  classical
  have := SetLike.ext_iff.not.mp hI
  push_neg at this
  obtain ⟨x, ⟨hx0, hx1⟩|⟨hx0, hx1⟩⟩ := this
  · obtain ⟨s, rfl⟩ := TensorProduct.eq_repr_basis_left 𝒜 x
    let n := @Nat.find (fun n => ∃ x : A ⊗[K] B, is_obtainable_by_sum_tmul x 𝒜 I n) _
      ⟨s.support.card, ∑ i ∈ s.support, 𝒜 i ⊗ₜ[K] s i, ⟨hx0, hx1, s.support, rfl, s, rfl⟩⟩
    obtain ⟨x, hx⟩ : ∃ x, is_obtainable_by_sum_tmul x 𝒜 I n :=
      @Nat.find_spec (fun n => ∃ x : A ⊗[K] B, is_obtainable_by_sum_tmul x 𝒜 I n) _
      ⟨s.support.card, ∑ i ∈ s.support, 𝒜 i ⊗ₜ[K] s i, ⟨hx0, hx1, s.support, rfl, s, rfl⟩⟩
    refine ⟨n, x, hx, fun m y hy => ?_⟩
    by_contra r
    simp only [not_le] at r
    have := @Nat.find_min (fun n => ∃ x : A ⊗[K] B, is_obtainable_by_sum_tmul x 𝒜 I n) _
      ⟨s.support.card, ∑ i ∈ s.support, 𝒜 i ⊗ₜ[K] s i, ⟨hx0, hx1, s.support, rfl, s, rfl⟩⟩ m r
    simp only [not_exists] at this
    exact this y hy
  · change x = 0 at hx1
    subst hx1
    exact hx0 I.zero_mem |>.elim

-- lemma TensorProduct.sum_tmul_basis_right_eq_zero'
--     (B : Type*) [Ring B] [Algebra K B]
--     (C : Type*) [Ring C] [Algebra K C]
--     {ιC : Type*} (𝒞 : Basis ιC K C)
--     (s : Finset ιC) (b : ιC → B)
--     (h : ∑ i ∈ s, b i ⊗ₜ[K] 𝒞 i = 0) :
--     ∀ i ∈ s, b i = 0 := by
--   classical
--   intro i
--   have := TensorProduct.sum_tmul_basis_right_eq_zero (κ := ιC) 𝒞 (M := B)
--     { support := s.filter fun i ↦ b i ≠ 0
--       toFun := fun x => if x ∈ s then b x else 0
--       mem_support_toFun := by simp }
--     (by
--       simp only [Finsupp.sum, ne_eq, Finsupp.coe_mk, Finset.sum_filter, ite_not]
--       rw [← h]
--       congr!
--       aesop)
--   simpa using Finsupp.ext_iff.mp this i

-- lemma TensorProduct.sum_tmul_basis_left_eq_zero'
--     (B : Type*) [Ring B] [Algebra K B]
--     (C : Type*) [Ring C] [Algebra K C]
--     {ιB : Type*} (ℬ : Basis ιB K B)
--     (s : Finset ιB) (c : ιB → C)
--     (h : ∑ i ∈ s, ℬ i ⊗ₜ[K] c i = 0) :
--     ∀ i ∈ s, c i = 0 := by
--   classical
--   have := TensorProduct.sum_tmul_basis_left_eq_zero (ι := ιB) ℬ (N := C)
--     { support := s.filter fun i ↦ c i ≠ 0
--       toFun := fun x => if x ∈ s then c x else 0
--       mem_support_toFun := by simp }
--     (by
--       simp only [Finsupp.sum, ne_eq, Finsupp.coe_mk, Finset.sum_filter, ite_not]
--       rw [← h]
--       congr!
--       aesop)
--   simpa? using Finsupp.ext_iff.mp this
  -- apply TensorProduct.sum_tmul_basis_right_eq_zero' K C B ℬ s c
  -- apply_fun TensorProduct.comm K B C at h
  -- simpa using h

-- instance TensorProduct.nontrivial
--     (A B : Type v) [Ring A] [Algebra K A] [Ring B] [Algebra K B]
--     [Nontrivial A] [Nontrivial B] :
--     Nontrivial (A ⊗[K] B) :=
--   nontrivial_of_linearMap_injective_of_flat_right K A B (Algebra.linearMap _ _)
--     (FaithfulSMul.algebraMap_injective _ _)

theorem _root_.TwoSidedIdeal.mem_map_of_mem {R S : Type*}
    [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
    {F : Type*} [FunLike F R S] {f : F} {I : TwoSidedIdeal R}
    {x : R} (hx : x ∈ I) : f x ∈ I.map f :=
  TwoSidedIdeal.subset_span ⟨x, hx, rfl⟩

theorem _root_.Submodule.mem_span_range_iff_exists' {α M R : Type*}
    [Semiring R] [AddCommMonoid M] [Module R M] {v : α → M} {x : M} :
    x ∈ Submodule.span R (Set.range v) ↔ ∃ (s : Finset α) (c : α → R), ∑ i ∈ s, c i • v i = x := by
  classical
  rw [← Set.image_univ, Submodule.mem_span_image_iff_exists_fun]
  simp only [Set.subset_univ, Finset.univ_eq_attach, true_and, ← Finset.sum_attach (ι := α)]
  refine ⟨fun ⟨s, c, hsc⟩ ↦ ⟨s, fun x ↦ if h : x ∈ s then c ⟨x, h⟩ else 0, ?_⟩,
    fun ⟨s, c, hsc⟩ ↦ ⟨s, c ∘ Subtype.val, by simpa⟩⟩
  convert hsc
  grind

-- attribute [local instance] Algebra.TensorProduct.rightAlgebra in
lemma TensorProduct.map_comap_eq_zero_if_zero
    {A B : Type v} [DivisionRing A] [Algebra K A] [Ring B] [Algebra K B]
    [isCentral_A : Algebra.IsCentral K A]
    [isSimple_B : IsSimpleRing B]
    (I : TwoSidedIdeal (A ⊗[K] B))
    (hAB : letI f : B →ₐ[K] A ⊗[K] B := Algebra.TensorProduct.includeRight
      (I.comap f).map f = ⊥) : I = ⊥ := by
  set f : B →ₐ[K] A ⊗[K] B := Algebra.TensorProduct.includeRight
  obtain ⟨ι, 𝓑⟩ := Module.Free.exists_basis K B
  have main (s : Finset ι) (a : ι → A) (h : ∑ i ∈ s, a i ⊗ₜ[K] 𝓑 i ∈ I) :
      ∀ i ∈ s, a i = 0 := by
    classical
    induction s using Finset.induction_on generalizing a with
    | empty => simp
    | insert j s hjs ih =>
    rcases eq_or_ne (a j) 0 with hj | hj
    · aesop
    · replace h := I.mul_mem_left ((a j)⁻¹ ⊗ₜ 1) _ h
      simp_rw [Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, Finset.sum_insert hjs, inv_mul_cancel₀ hj] at h
      have key : ∀ i : s, ∃ k, (a j)⁻¹ * a i = algebraMap K A k := by
        have (c : A) := I.sub_mem (I.mul_mem_left (c ⊗ₜ 1) _ h) (I.mul_mem_right _ (c ⊗ₜ 1) h)
        simp_rw [mul_add, add_mul, add_sub_add_comm, Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul, sub_self, zero_add, Finset.mul_sum, Finset.sum_mul,
          ← Finset.sum_sub_distrib, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
          ← sub_tmul] at this
        exact fun i ↦ (Algebra.IsCentral.mem_center_iff K).mp <| Subalgebra.mem_center_iff.mpr
          fun c ↦ sub_eq_zero.mp <| ih _ (this c) i i.2
      choose k hk using key
      rw [← Finset.sum_attach] at h
      simp_rw [hk] at h
      set key : B := 𝓑 j + ∑ i ∈ s.attach, k i • 𝓑 i
      have hkey : f key ∈ I := by
        convert h using 1
        simp [f, key, tmul_add, tmul_sum, -tmul_smul, ← smul_tmul, ← Algebra.algebraMap_eq_smul_one]
      replace hkey : f key = 0 :=
        eq_bot_iff.mp hAB <| TwoSidedIdeal.mem_map_of_mem <| (TwoSidedIdeal.mem_comap _).mpr hkey
      replace hkey := (map_eq_zero_iff _ f.toRingHom.injective).mp hkey
      set g : ι → K := fun i ↦ if h : i ∈ s then k ⟨i, h⟩ else 1
      have hg : ∑ i ∈ insert j s, g i • 𝓑 i = 0 := by
        unfold g
        rw [Finset.sum_insert hjs, dif_neg hjs, one_smul, ← Finset.sum_attach]
        simp_rw [dif_pos (Subtype.prop _)]
        exact hkey
      have hb := linearIndependent_iff'.mp 𝓑.linearIndependent (insert j s) g hg j
        (Finset.mem_insert_self _ _)
      simp [g, dif_neg hjs] at hb
  refine eq_bot_iff.mpr fun x hx ↦ ?_
  obtain ⟨s, c, rfl⟩ := Submodule.mem_span_range_iff_exists'.mp <|
    Submodule.eq_top_iff'.mp (𝓑.baseChange A).span_eq x
  replace main := main s c (by simpa [← TensorProduct.tmul_eq_smul_one_tmul] using hx)
  simp +contextual [main]

@[simp]
lemma TwoSidedIdeal.span_eq_bot {R : Type*} [NonUnitalNonAssocRing R] {s : Set R} :
    span s = ⊥ ↔ ∀ x ∈ s, x = 0 := eq_bot_iff.trans
  ⟨fun H _ h => (mem_bot R).1 <| H <| subset_span h, fun H =>
    span_le.2 fun x h => (mem_bot R).2 <| H x h⟩

lemma TwoSidedIdeal.span_singleton_eq_bot {R : Type*} [NonUnitalNonAssocRing R] {x : R} :
    span ({x} : Set R) = ⊥ ↔ x = 0 := by simp

lemma TwoSidedIdeal.map_bot {R S : Type*}
    [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
    {F : Type*} [FunLike F R S] [ZeroHomClass F R S] {f : F} :
    (⊥ : TwoSidedIdeal R).map f = ⊥ := by
  ext x
  simp [map, coe_bot, Set.image_singleton, map_zero f, mem_bot, span_singleton_eq_bot.2]

lemma TensorProduct.map_comap_eq
    {A B : Type v} [DivisionRing A] [Algebra K A] [Ring B] [Algebra K B]
    [isCentral_A : Algebra.IsCentral K A]
    [isSimple_B : IsSimpleRing B]
    (I : TwoSidedIdeal (A ⊗[K] B)) :
    letI f : B →ₐ[K] A ⊗[K] B := Algebra.TensorProduct.includeRight
    (I.comap f).map f = I := by
  let f : B →ₐ[K] A ⊗[K] B := Algebra.TensorProduct.includeRight
  refine (le_antisymm ?_ ?_).symm
  · obtain rfl | I_ne_bot := eq_or_ne I ⊥
    · exact bot_le
    change I ≤ TwoSidedIdeal.span (Set.image f <| I.comap f)
    have hI : I.comap f = ⊤ := isSimple_B.1.2 _ |>.resolve_left fun r => by
      refine I_ne_bot <| TensorProduct.map_comap_eq_zero_if_zero (hAB := ?_)
      rw [r, TwoSidedIdeal.map_bot]
    rw [hI, TwoSidedIdeal.coe_top, TwoSidedIdeal.le_iff]
    rintro x -
    rw [SetLike.mem_coe]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [show a ⊗ₜ[K] b = (a ⊗ₜ 1) * (1 ⊗ₜ b) by simp]
      exact TwoSidedIdeal.mul_mem_left _ _ _ <| TwoSidedIdeal.subset_span ⟨b, ⟨⟩, rfl⟩
    | add x y hx hy => exact TwoSidedIdeal.add_mem _ hx hy
  · rw [TwoSidedIdeal.map, TwoSidedIdeal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap] at hx
    exact hx

lemma TensorProduct.simple' {A B : Type v} [DivisionRing A] [Algebra K A] [Ring B] [Algebra K B]
    [isCentral_A : Algebra.IsCentral K A] [isSimple_B : IsSimpleRing B] :
    IsSimpleRing (A ⊗[K] B) := by
  let f : B →ₐ[K] A ⊗[K] B := Algebra.TensorProduct.includeRight
  suffices eq1 : ∀ (I : TwoSidedIdeal (A ⊗[K] B)),
      I = TwoSidedIdeal.span (Set.image f <| I.comap f) by
    refine ⟨⟨fun I => ?_⟩⟩
    specialize eq1 I
    rcases isSimple_B.1.2 (I.comap f) with h|h
    · left
      rw [eq1, TwoSidedIdeal.span_eq_bot, h]
      simp
    · right
      rw [← TwoSidedIdeal.one_mem_iff, eq1, h]
      exact TwoSidedIdeal.subset_span ⟨1, by simp⟩
  exact fun _ ↦ TensorProduct.map_comap_eq K _ |>.symm

lemma Matrix.scalar_injective {n α : Type*} [Semiring α] [DecidableEq n]
    [Fintype n] [Nonempty n] : Function.Injective (Matrix.scalar (α := α) n) :=
  fun _ _ h ↦ Matrix.scalar_inj.1 h

lemma Matrix.scalarAlgHom_injective (n R α : Type*) [Fintype n] [DecidableEq n] [Nonempty n]
    [CommSemiring R] [Semiring α] [Algebra R α] : Function.Injective (scalarAlgHom n R (α := α)) :=
  Matrix.scalar_injective

lemma Algebra.IsCentral.of_matrix {n D : Type*} [DivisionRing D] [Algebra K D] [Nonempty n]
    [Fintype n] [DecidableEq n] (h : Algebra.IsCentral K (Matrix n n D)) :
    Algebra.IsCentral K D := by
  refine ⟨le_of_eq ?_⟩
  have := Matrix.subalgebraCenter_eq_scalarAlgHom_map (n := n) (R := K) (A := D)
  rw [center_eq_bot] at this
  apply Subalgebra.map_injective (Matrix.scalarAlgHom_injective n K D)
  simp [← this]

@[stacks 074C]
instance TensorProduct.simple
    (A B : Type v) [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [isSimple_A : IsSimpleRing A] [FiniteDimensional K B]
    [isCentral_B : Algebra.IsCentral K B]
    [isSimple_B : IsSimpleRing B] : IsSimpleRing (A ⊗[K] B) := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite K B
  obtain ⟨n, _, D, _, _, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K B
  haveI := Algebra.IsCentral.of_matrix K <| Algebra.IsCentral.of_algEquiv K _ _ e
  replace e : A ⊗[K] B ≃ₐ[K] Matrix (Fin n) (Fin n) (D ⊗[K] A) :=
    (Algebra.TensorProduct.comm K A B).trans <| (Algebra.TensorProduct.congr (e.trans
      (matrixEquivTensor (Fin n) K D)|>.trans <| Algebra.TensorProduct.comm K D _)
      (@AlgEquiv.refl K A ..)).trans <| (Algebra.TensorProduct.assoc K K _ _ _).trans <|
    (Algebra.TensorProduct.comm K _ _).trans <| (matrixEquivTensor (Fin n) _ _).symm
  refine IsSimpleRing.of_ringEquiv e.toRingEquiv.symm <| @IsSimpleRing.matrix _ _ _ _ _ ?_
  exact TensorProduct.simple' K

lemma TensorProduct.map_comap_eq_of_isSimple_isCentralSimple
    {A B : Type v} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [isSimple_A : IsSimpleOrder <| TwoSidedIdeal A]
    [isCentral_B : Algebra.IsCentral K B]
    [isSimple_B : IsSimpleRing B]
    (I : TwoSidedIdeal (A ⊗[K] B)) :
    letI f : A →ₐ[K] A ⊗[K] B := Algebra.TensorProduct.includeLeft
    (I.comap f).map f = I := by
  classical
  refine (le_antisymm ?_ ?_).symm
  · obtain rfl | I_ne_bot := eq_or_ne I ⊥
    · exact bot_le
    let f : A →ₐ[K] A ⊗[K] B := Algebra.TensorProduct.includeLeft
    change I ≤ TwoSidedIdeal.span (Set.image f <| I.comap f)
    let 𝒜 := Basis.ofVectorSpace K A
    obtain ⟨n, x, ⟨x_mem, x_ne_zero, ⟨s, card_s, b, rfl⟩⟩, H⟩ :=
      is_obtainable_by_sum_tmul.exists_minimal_element _ 𝒜 I I_ne_bot
    have b_ne_zero : ∀ i ∈ s, b i ≠ 0 := by
      by_contra! h
      rcases h with ⟨i, h1, h2⟩
      specialize H (n - 1) (∑ i ∈ s, 𝒜 i ⊗ₜ[K] b i) ⟨x_mem, x_ne_zero, ⟨s.erase i,
        by rw [Finset.card_erase_of_mem, card_s]; exact h1, b, by
        symm
        fapply Finset.sum_subset
        · exact Finset.erase_subset i s
        · intro x hx1 hx2
          simp only [Finset.mem_erase, ne_eq, not_and] at hx2
          rw [show x = i by tauto, h2, TensorProduct.tmul_zero]⟩⟩
      have ineq1 : 0 < n := by
        rw [← card_s, Finset.card_pos]
        exact ⟨i, h1⟩
      omega
    obtain rfl | ⟨i₀, hi₀⟩ := s.eq_empty_or_nonempty
    · simp at *
    have ineq1 : 0 < n := by
      rw [← card_s, Finset.card_pos]
      exact ⟨i₀, hi₀⟩
    have x_eq' :
        ∑ i ∈ s, 𝒜 i ⊗ₜ[K] b i =
        𝒜 i₀ ⊗ₜ[K] b i₀ +
        ∑ i ∈ s.erase i₀, 𝒜 i ⊗ₜ[K] b i := by
      rw [show 𝒜 i₀ ⊗ₜ[K] b i₀ = ∑ i ∈ {i₀}, 𝒜 i ⊗ₜ[K] b i by rw [Finset.sum_singleton],
        ← Finset.sum_disjUnion]
      pick_goal 2
      · simp
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext x
      simp only [Finset.disjUnion_eq_union, Finset.mem_union, Finset.mem_singleton,
        Finset.mem_erase, ne_eq, or_and_left, em, true_and, iff_or_self]
      simp +contextual [hi₀]
    have span_bi₀ : TwoSidedIdeal.span {b i₀} = ⊤ := isSimple_B.1.2 _ |>.resolve_left fun r => by
      have mem : b i₀ ∈ (⊥ : TwoSidedIdeal B) := by
        rw [← r]
        apply TwoSidedIdeal.subset_span
        simp only [Set.mem_singleton_iff]
      exact b_ne_zero i₀ hi₀ mem
    have one_mem : (1 : B) ∈ TwoSidedIdeal.span {b i₀} := by rw [span_bi₀]; trivial
    rw [TwoSidedIdeal.mem_span_iff_exists_fin] at one_mem
    obtain ⟨ℐ, inst1, xL, xR, y, one_eq⟩ := one_mem
    replace one_eq : 1 = ∑ i : ℐ, xL i * b i₀ * xR i := by
      rw [one_eq]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr
      simpa only [Set.mem_singleton_iff] using (y i).2
    let ω := ∑ i ∈ s, 𝒜 i ⊗ₜ[K] b i
    let Ω := ∑ i : ℐ, (1 ⊗ₜ[K] xL i) * ω * (1 ⊗ₜ[K] xR i)
    have Ω_in_I : Ω ∈ I := TwoSidedIdeal.finsetSum_mem _ _ _ fun i _ => I.mul_mem_right _ _ <|
      I.mul_mem_left _ _ x_mem
    have Ω_eq :
        Ω =
        𝒜 i₀ ⊗ₜ[K] (∑ i : ℐ, xL i * b i₀ * xR i) +
        ∑ i ∈ s.erase i₀, 𝒜 i ⊗ₜ[K] (∑ j : ℐ, xL j * b i * xR j) := by
      dsimp only [Ω, ω]
      simp only [x_eq', mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Finset.mul_sum,
        add_mul, mul_one, Finset.sum_mul, Finset.sum_add_distrib, TensorProduct.tmul_sum,
        add_right_inj]
      rw [Finset.sum_comm]
    rw [← one_eq] at Ω_eq
    have Ω_prop_1 (b : B) : (1 ⊗ₜ b) * Ω - Ω * (1 ⊗ₜ b) ∈ I :=
      I.sub_mem (I.mul_mem_left _ _ Ω_in_I) (I.mul_mem_right _ _ Ω_in_I)
    have Ω_prop_2 (x : B) : ((1 : A) ⊗ₜ[K] x) * Ω - Ω * ((1 : A) ⊗ₜ[K] x) =
        ∑ i ∈ s.erase i₀, 𝒜 i ⊗ₜ[K]
          (∑ j : ℐ, (x * (xL j * b i * xR j) - (xL j * b i * xR j) * x)) := by
      rw [Ω_eq]
      simp [TensorProduct.tmul_sum, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        mul_one, Finset.mul_sum, add_mul, Finset.sum_mul, add_sub_add_left_eq_sub,
        Finset.sum_sub_distrib, TensorProduct.tmul_sub]
    have Ω_prop_3 (x : B) : ((1 : A) ⊗ₜ[K] x) * Ω - Ω * ((1 : A) ⊗ₜ[K] x) = 0 := by
      by_contra rid
      specialize H (n - 1) (((1 : A) ⊗ₜ[K] x) * Ω - Ω * ((1 : A) ⊗ₜ[K] x))
        ⟨Ω_prop_1 x, rid, ⟨s.erase i₀, by rw [Finset.card_erase_of_mem, card_s]; exact hi₀, _,
          Ω_prop_2 x⟩⟩
      omega
    simp_rw [Ω_prop_2] at Ω_prop_3
    have Ω_prop_4 : ∀ i ∈ s.erase i₀,
        ∑ j : ℐ, (xL j * b i * xR j) ∈ Subalgebra.center K B := by
      intro i hi
      rw [Subalgebra.mem_center_iff]
      intro x
      specialize Ω_prop_3 x
      simp only [Finset.mul_sum, Finset.sum_mul, ← sub_eq_zero, sub_zero]
      rw [← Finset.sum_sub_distrib, sub_zero]
      have := TensorProduct.sum_tmul_basis_left_eq_zero 𝒜 (M := A) (N := B) {
        support := (s.erase i₀).filter (fun i ↦
          ∑ j, (x * (xL j * b i * xR j) - xL j * b i * xR j * x) ≠ 0)
        toFun := fun i ↦ if i ∈ s.erase i₀ then (∑ j : ℐ, (x * (xL j * b i * xR j) -
          xL j * b i * xR j * x)) else 0
        mem_support_toFun := by grind
      } <| by
        simp only [Finsupp.sum, ne_eq, Finset.mem_erase, Finsupp.coe_mk, Finset.sum_filter, ite_not]
        conv_rhs => rw [← Ω_prop_3]
        congr! with a ha
        split_ifs with hi hi'
        · rw [hi, tmul_zero]
        · rfl
        · simp only [not_and, Finset.mem_erase, ne_eq] at hi' ha
          exact False.elim <| hi' ha.1 ha.2
      simp only [Finsupp.ext_iff, ne_eq, Finsupp.coe_mk, Finsupp.coe_zero,
        Pi.zero_apply, ite_eq_right_iff] at this
      exact this i hi
    simp_rw [Algebra.IsCentral.center_eq_bot, Algebra.mem_bot, Set.mem_range] at Ω_prop_4
    choose k hk using Ω_prop_4
    have Ω_eq2 := calc Ω
      _ = 𝒜 i₀ ⊗ₜ[K] 1 + ∑ i ∈ s.erase i₀, 𝒜 i ⊗ₜ[K] ∑ j : ℐ, xL j * b i * xR j := Ω_eq
      _ = 𝒜 i₀ ⊗ₜ[K] 1 + ∑ i ∈ (s.erase i₀).attach, 𝒜 i ⊗ₜ[K] ∑ j : ℐ, xL j * b i * xR j := by
          congr 1
          exact Finset.sum_attach _ _ |>.symm
      _ = 𝒜 i₀ ⊗ₜ[K] 1 + ∑ i ∈ (s.erase i₀).attach, 𝒜 i ⊗ₜ[K] algebraMap _ _ (k i.1 i.2) := by
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hk i.1 i.2]
      _ = 𝒜 i₀ ⊗ₜ[K] 1 +  ∑ i ∈ (s.erase i₀).attach, 𝒜 i ⊗ₜ[K] (k i.1 i.2 • (1 : B) : B) := by
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Algebra.algebraMap_eq_smul_one]
      _ = 𝒜 i₀ ⊗ₜ[K] 1 + ∑ i ∈ (s.erase i₀).attach, (k i.1 i.2 • 𝒜 i) ⊗ₜ[K] (1 : B) := by
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [TensorProduct.smul_tmul]
      _ = 𝒜 i₀ ⊗ₜ[K] 1 + (∑ i ∈ (s.erase i₀).attach, (k i.1 i.2 • 𝒜 i)) ⊗ₜ[K] (1 : B) := by
          rw [TensorProduct.sum_tmul]
      _ = (𝒜 i₀ + (∑ i ∈ (s.erase i₀).attach, (k i.1 i.2 • 𝒜 i))) ⊗ₜ[K] 1 := by
          rw [TensorProduct.add_tmul]
    rw [Ω_eq2] at Ω_in_I
    have hI : I.comap f = ⊤ := isSimple_A.2 _ |>.resolve_left fun r => by
      have mem : 𝒜 i₀ + (∑ i ∈ (s.erase i₀).attach, (k i.1 i.2 • 𝒜 i)) ∈ I.comap f := by
        rw [TwoSidedIdeal.mem_comap]
        exact Ω_in_I
      rw [r] at mem
      change _ = 0 at mem
      rw [mem, TensorProduct.zero_tmul] at Ω_eq2
      have LI := 𝒜.linearIndependent
      rw [linearIndependent_iff'] at LI
      specialize LI s (fun i =>
        if i = i₀ then 1
        else if h : i ∈ s.erase i₀ then k i h else 0) (by
        dsimp only
        simp_rw [ite_smul, one_smul, dite_smul, zero_smul]
        rw [Finset.sum_ite, Finset.sum_congr (s₁ := s.filter (fun x ↦ x = i₀)) (s₂ := {i₀})
          (by simp [Finset.ext_iff, hi₀]) (fun _ _ => rfl), Finset.sum_singleton,
          show Finset.filter (fun x ↦ ¬x = i₀) s = s.erase i₀ by grind, ← Finset.sum_attach]
        conv_rhs => rw [← mem]
        simp) i₀ hi₀
      rw [if_pos rfl] at LI
      exact zero_ne_one LI.symm
    rw [hI, TwoSidedIdeal.coe_top, TwoSidedIdeal.le_iff]
    rintro x -
    rw [SetLike.mem_coe]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [show a ⊗ₜ[K] b = (a ⊗ₜ 1) * (1 ⊗ₜ b) by simp]
      exact TwoSidedIdeal.mul_mem_right _ _ _ <| TwoSidedIdeal.subset_span ⟨a, ⟨⟩, rfl⟩
    | add x y hx hy => exact TwoSidedIdeal.add_mem _ hx hy
  · rw [TwoSidedIdeal.map, TwoSidedIdeal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap] at hx
    exact hx

@[stacks 074C]
instance TensorProduct.simple_more_general
    (A B : Type v) [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [isSimple_A : IsSimpleRing A]
    [isCentral_B : Algebra.IsCentral K B]
    [isSimple_B : IsSimpleRing B] :
    IsSimpleRing (A ⊗[K] B) := by
  let f : A →ₐ[K] A ⊗[K] B := Algebra.TensorProduct.includeLeft
  suffices eq1 : ∀ (I : TwoSidedIdeal (A ⊗[K] B)),
      I = TwoSidedIdeal.span (Set.image f <| I.comap f) by
    refine ⟨⟨fun I => ?_⟩⟩
    specialize eq1 I
    rcases isSimple_A.1.2 (I.comap f) with h|h
    · left
      rw [eq1, TwoSidedIdeal.span_eq_bot, h]
      simp
    · right
      rw [← TwoSidedIdeal.one_mem_iff, eq1, h]
      exact TwoSidedIdeal.subset_span ⟨1, by simp⟩
  exact fun _ ↦ TensorProduct.map_comap_eq_of_isSimple_isCentralSimple K _ |>.symm
