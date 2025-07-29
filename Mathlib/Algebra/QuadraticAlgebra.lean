/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Kenny Lau, Jiayang Hong
-/

import Mathlib

/-!

# Quadratic Algebra

In this file we define the quadratic algebra `QuadraticAlgebra R a b` over a commutative ring `R`,
and define some algebraic structures on it.

## Main definitions

* `QuadraticAlgebra R a b`:
  [Bourbaki, *Algebra I*][bourbaki1989] with coefficients `a`, `b` in `R`.

## Tags

Quadratic algebra, quadratic extension

-/

universe u

/-- Quadratic algebra over a type with fixed coefficient where $i^2 = a + bi$, implemented as
a structure with two fields, `re` and `im`. When `R` is a commutative ring, this is isomorphic to
`R[X]/(X^2-b*X-a)`. -/
@[ext]
structure QuadraticAlgebra (R : Type u) (a b : R) : Type u where
  /-- Real part of an element in quadratic algebra -/
  re : R
  /-- Imaginaty part of an element in quadratic algerba -/
  im : R
deriving DecidableEq

namespace QuadraticAlgebra

/-- The equivalence between quadratic algebra over `R` and `R × R`. -/
@[simps symm_apply]
def equivProd {R : Type*} (a b : R) : QuadraticAlgebra R a b ≃ R × R where
  toFun z := (z.re, z.im)
  invFun p := ⟨p.1, p.2⟩

@[simp]
theorem mk_eta {R : Type*} {a b} (z : QuadraticAlgebra R a b) :
    mk z.re z.im = z := rfl

variable {S T R : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

instance [Subsingleton R] : Subsingleton (QuadraticAlgebra R a b) := (equivProd a b).subsingleton

instance [Nontrivial R] : Nontrivial (QuadraticAlgebra R a b) := (equivProd a b).nontrivial

section Zero

variable [Zero R]

/-- Coercion `R → QuadraticAlgebra R a b`. -/
@[coe] def coe (x : R) : QuadraticAlgebra R a b := ⟨x, 0⟩

instance : Coe R (QuadraticAlgebra R a b) := ⟨coe⟩

@[simp, norm_cast]
theorem coe_re : (r : QuadraticAlgebra R a b).re = r := rfl

@[simp, norm_cast]
theorem coe_im : (r : QuadraticAlgebra R a b).im = 0 := rfl

theorem coe_injective : Function.Injective (coe : R → QuadraticAlgebra R a b) :=
  fun _ _ h => congr_arg re h

@[simp]
theorem coe_inj {x y : R} : (x : QuadraticAlgebra R a b) = y ↔ x = y :=
  coe_injective.eq_iff

instance : Zero (QuadraticAlgebra R a b) := ⟨⟨0, 0⟩⟩

@[simp] theorem zero_re : (0 : QuadraticAlgebra R a b).re = 0 := rfl

@[simp] theorem zero_im : (0 : QuadraticAlgebra R a b).im = 0 := rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : R) : QuadraticAlgebra R a b) = 0 := rfl

instance : Inhabited (QuadraticAlgebra R a b) := ⟨0⟩

section One
variable [One R]

instance : One (QuadraticAlgebra R a b) := ⟨⟨1, 0⟩⟩

@[scoped simp] theorem one_re : (1 : QuadraticAlgebra R a b).re = 1 := rfl

@[scoped simp] theorem one_im : (1 : QuadraticAlgebra R a b).im = 0 := rfl

@[simp, norm_cast]
theorem coe_one : ((1 : R) : QuadraticAlgebra R a b) = 1 := rfl

end One

end Zero

section Add

variable [Add R]

instance : Add (QuadraticAlgebra R a b) where
  add z w := ⟨z.re + w.re, z.im + w.im⟩

@[simp] theorem add_re (z w : QuadraticAlgebra R a b) :
    (z + w).re = z.re + w.re := rfl

@[simp] theorem add_im (z w : QuadraticAlgebra R a b) :
    (z + w).im = z.im + w.im := rfl

@[simp]
theorem mk_add_mk (z w : QuadraticAlgebra R a b) :
    mk z.re z.im + mk w.re w.im = (mk (z.re + w.re) (z.im + w.im) : QuadraticAlgebra R a b) := rfl

end Add

section AddZeroClass

variable [AddZeroClass R]

@[simp]
theorem coe_add (x y : R) : ((x + y : R) : QuadraticAlgebra R a b) = x + y := by ext <;> simp

end AddZeroClass

section Neg

variable [Neg R]

instance : Neg (QuadraticAlgebra R a b) where neg z := ⟨-z.re, -z.im⟩

@[simp] theorem neg_re (z : QuadraticAlgebra R a b) : (-z).re = -z.re := rfl

@[simp] theorem neg_im (z : QuadraticAlgebra R a b) : (-z).im = -z.im := rfl

@[simp]
theorem neg_mk (x y : R) :
    - (mk x y : QuadraticAlgebra R a b) = ⟨-x, -y⟩ := rfl

end Neg

section AddGroup

@[simp]
theorem coe_neg [NegZeroClass R] (x : R) :
    ((-x : R) : QuadraticAlgebra R a b) = -x := by ext <;> simp

instance [Sub R] : Sub (QuadraticAlgebra R a b) where
  sub z w := ⟨z.re - w.re, z.im - w.im⟩

@[simp] theorem sub_re [Sub R] (z w : QuadraticAlgebra R a b) :
    (z - w).re = z.re - w.re := rfl

@[simp] theorem sub_im [Sub R] (z w : QuadraticAlgebra R a b) :
    (z - w).im = z.im - w.im := rfl

@[simp]
theorem mk_sub_mk [Sub R] (x1 y1 x2 y2 : R) :
    (mk x1 y1 : QuadraticAlgebra R a b) - mk x2 y2 = mk (x1 - x2) (y1 - y2) := rfl

@[norm_cast, simp]
theorem coe_sub (r1 r2 : R) [SubNegZeroMonoid R] :
    ((r1 - r2 : R) : QuadraticAlgebra R a b) = r1 - r2 :=
  QuadraticAlgebra.ext rfl zero_sub_zero.symm

end AddGroup

section Mul

variable [Mul R] [Add R]

instance : Mul (QuadraticAlgebra R a b) :=
  ⟨fun z w => ⟨z.1 * w.1 + a * z.2 * w.2, z.1 * w.2 + z.2 * w.1 + b * z.2 * w.2⟩⟩

@[simp] theorem mul_re (z w : QuadraticAlgebra R a b) :
    (z * w).re = z.re * w.re + a * z.im * w.im := rfl

@[simp] theorem mul_im (z w : QuadraticAlgebra R a b) :
    (z * w).im = z.re * w.im + z.im * w.re + b * z.im * w.im := rfl

@[simp]
theorem mk_mul_mk (x1 y1 x2 y2 : R) :
    (mk x1 y1 : QuadraticAlgebra R a b) * mk x2 y2 =
    mk (x1 * x2 + a * y1 * y2) (x1 * y2 + y1 * x2 + b * y1 * y2) := rfl

end Mul

section SMul

variable [SMul S R] [SMul T R] (s : S)

instance : SMul S (QuadraticAlgebra R a b) where smul s z := ⟨s • z.re, s • z.im⟩

instance [SMul S T] [IsScalarTower S T R] : IsScalarTower S T (QuadraticAlgebra R a b) where
  smul_assoc s t z := by ext <;> exact smul_assoc _ _ _

instance [SMulCommClass S T R] : SMulCommClass S T (QuadraticAlgebra R a b) where
  smul_comm s t z := by ext <;> exact smul_comm _ _ _

@[simp] theorem smul_re (s : S) (z : QuadraticAlgebra R a b) : (s • z).re = s • z.re := rfl

@[simp] theorem smul_im (s : S) (z : QuadraticAlgebra R a b) : (s • z).im = s • z.im := rfl

@[simp]
theorem smul_mk (s : S) (x y : R) :
    s • (mk x y : QuadraticAlgebra R a b) = mk (s • x) (s • y) := rfl

end SMul

section MulAction

instance [Monoid S] [MulAction S R] : MulAction S (QuadraticAlgebra R a b) where
  one_smul _ := by ext <;> simp
  mul_smul _ _ _ := by ext <;> simp[mul_smul]

end MulAction

@[simp, norm_cast]
theorem coe_smul [Zero R] [SMulZeroClass S R] (s : S) (r : R) :
    (↑(s • r) : QuadraticAlgebra R a b) = s • (r : QuadraticAlgebra R a b) :=
  QuadraticAlgebra.ext rfl (smul_zero _).symm

instance [AddMonoid R] : AddMonoid (QuadraticAlgebra R a b) := by
  refine (equivProd a b).injective.addMonoid _ rfl ?_ ?_ <;> intros <;> rfl

instance [Monoid S] [AddMonoid R] [DistribMulAction S R] :
    DistribMulAction S (QuadraticAlgebra R a b) where
  smul_zero _ := by ext <;> simp
  smul_add _ _ _ := by ext <;> simp

instance [AddCommMonoid R] : AddCommMonoid (QuadraticAlgebra R a b) where
  __ := inferInstanceAs (AddMonoid (QuadraticAlgebra R a b))
  add_comm _ _ := by ext <;> simp [add_comm]

instance [Semiring S] [AddCommMonoid R] [Module S R] : Module S (QuadraticAlgebra R a b) where
  add_smul r s x := by ext <;> simp[add_smul]
  zero_smul x := by ext <;> simp

instance [AddGroup R] : AddGroup (QuadraticAlgebra R a b) := by
  refine (equivProd a b).injective.addGroup _ rfl ?_ ?_ ?_ ?_ ?_ <;> intros <;> rfl

instance [AddCommGroup R] : AddCommGroup (QuadraticAlgebra R a b) where
  __ := inferInstanceAs (AddGroup (QuadraticAlgebra R a b))
  __ := inferInstanceAs (AddCommMonoid (QuadraticAlgebra R a b))

section AddCommGroupWithOne

instance [AddCommMonoidWithOne R] : AddCommMonoidWithOne (QuadraticAlgebra R a b) where
  natCast n := ((n : R) : QuadraticAlgebra R a b)
  natCast_zero := by ext <;> simp
  natCast_succ n := by ext <;> simp

@[simp, norm_cast]
theorem coe_ofNat (n : ℕ) [n.AtLeastTwo] [AddCommMonoidWithOne R] :
    ((ofNat(n) : R) : QuadraticAlgebra R a b) = (ofNat(n) : QuadraticAlgebra R a b) := by
  ext <;> rfl

variable [AddCommGroupWithOne R]

instance : AddCommGroupWithOne (QuadraticAlgebra R a b) where
  intCast n := ((n : R) : QuadraticAlgebra R a b)
  intCast_ofNat n := by norm_cast
  intCast_negSucc n := by rw [Int.negSucc_eq, Int.cast_neg, coe_neg]; norm_cast

@[simp, norm_cast]
theorem natCast_re (n : ℕ) : (n : QuadraticAlgebra R a b).re = n := rfl

@[simp, norm_cast]
theorem natCast_im (n : ℕ) : (n : QuadraticAlgebra R a b).im = 0 := rfl

@[norm_cast]
theorem coe_natCast (n : ℕ) : ↑(n : R) = (n : QuadraticAlgebra R a b) := rfl

@[simp, norm_cast]
theorem intCast_re (n : ℤ) : (n : QuadraticAlgebra R a b).re = n := rfl

@[scoped simp]
theorem ofNat_re (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : QuadraticAlgebra R a b).re = ofNat(n) := rfl

@[scoped simp]
theorem ofNat_im (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : QuadraticAlgebra R a b).im = 0 := rfl

@[simp, norm_cast]
theorem intCast_im (n : ℤ) : (n : QuadraticAlgebra R a b).im = 0 := rfl

@[norm_cast]
theorem coe_intCast (n : ℤ) : ↑(n : R) = (n : QuadraticAlgebra R a b) := rfl

end AddCommGroupWithOne

section Semiring

variable (a b) [Semiring R]

/-- `QuadraticAlgebra.re` as a `LinearMap` -/
@[simps]
def reₗ : QuadraticAlgebra R a b →ₗ[R] R where
  toFun := re
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `QuadraticAlgebra.im` as a `LinearMap` -/
@[simps]
def imₗ : QuadraticAlgebra R a b →ₗ[R] R where
  toFun := im
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `QuadraticAlgebra.equivTuple` as a `LinearEquiv` -/
def linearEquivTuple : QuadraticAlgebra R a b ≃ₗ[R] (Fin 2 → R) where
  __ := equivProd a b |>.trans <| finTwoArrowEquiv _ |>.symm
  map_add' _ _ := funext <| Fin.forall_fin_two.2 ⟨rfl, rfl⟩
  map_smul' _ _ := funext <| Fin.forall_fin_two.2 ⟨rfl, rfl⟩

@[simp]
lemma linearEquivTuple_apply (z : QuadraticAlgebra R a b) :
    (linearEquivTuple a b) z = ![z.re, z.im] := rfl

@[simp]
lemma linearEquivTuple_symm_apply (x : Fin 2 → R) :
    (linearEquivTuple a b).symm x = ⟨x 0, x 1⟩ := rfl

/-- `QuadraticAlgebra R a b` has a basis over `R` given by `1` and `i` -/
noncomputable def basis : Module.Basis (Fin 2) R (QuadraticAlgebra R a b) :=
  .ofEquivFun <| linearEquivTuple a b

@[simp]
theorem coe_basis_repr (x : QuadraticAlgebra R a b) :
    (basis a b).repr x = ![x.re, x.im] := rfl

instance : Module.Finite R (QuadraticAlgebra R a b) := .of_basis (basis a b)

instance : Module.Free R (QuadraticAlgebra R a b) := .of_basis (basis a b)

theorem rank_eq_two [StrongRankCondition R] : Module.rank R (QuadraticAlgebra R a b) = 2 := by
  simp [rank_eq_card_basis (basis a b)]

theorem finrank_eq_two [StrongRankCondition R] : Module.finrank R (QuadraticAlgebra R a b) = 2 := by
  simp [Module.finrank, rank_eq_two]

@[simp, norm_cast]
theorem coe_mul (x y : R) : ((x * y : R) : QuadraticAlgebra R a b) = x * y := by ext <;> simp

end Semiring

section CommSemiring

variable [CommSemiring R]

instance instCommSemiring : CommSemiring (QuadraticAlgebra R a b) where
  __ := inferInstanceAs (AddCommMonoidWithOne (QuadraticAlgebra R a b))
  left_distrib _ _ _ := by ext <;> simpa using by ring
  right_distrib _ _ _ := by ext <;> simpa using by ring
  zero_mul _ := by ext <;> simp
  mul_zero _ := by ext <;> simp
  mul_assoc _ _ _ := by ext <;> simpa using by ring
  one_mul _ := by ext <;> simp
  mul_one _ := by ext <;> simp
  mul_comm _ _ := by ext <;> simpa using by ring

instance [CommSemiring S] [CommSemiring R] [Algebra S R] :
    Algebra S (QuadraticAlgebra R a b) where
  algebraMap.toFun s := coe (algebraMap S R s)
  algebraMap.map_one' := by ext <;> simp
  algebraMap.map_mul' x y:= by ext <;> simp
  algebraMap.map_zero' := by ext <;> simp
  algebraMap.map_add' x y:= by ext <;> simp
  commutes' s z := by ext <;> simp [Algebra.commutes]
  smul_def' s x := by ext <;> simp [Algebra.smul_def]

theorem algebraMap_eq (r : R) : algebraMap R (QuadraticAlgebra R a b) r = ⟨r, 0⟩ := rfl

theorem algebraMap_injective : (algebraMap R (QuadraticAlgebra R a b) : _ → _).Injective :=
  fun _ _ ↦ by simp [algebraMap_eq]

instance [NoZeroDivisors R] : NoZeroSMulDivisors R (QuadraticAlgebra R a b) :=
  ⟨by simp [QuadraticAlgebra.ext_iff, or_and_left]⟩

@[norm_cast, simp]
theorem coe_pow (n : ℕ) (r : R) : ((r ^ n : R) : QuadraticAlgebra R a b) =
    (r : QuadraticAlgebra R a b) ^ n :=
  (algebraMap R (QuadraticAlgebra R a b)).map_pow r n

theorem coe_mul_eq_smul (r : R) (x : QuadraticAlgebra R a b) :
    (r * x : QuadraticAlgebra R a b) = r • x := Algebra.smul_def r x |>.symm

theorem mul_coe_eq_smul (r : R) (x : QuadraticAlgebra R a b) :
    (x * r : QuadraticAlgebra R a b) = r • x := by
  rw [mul_comm, coe_mul_eq_smul r x]

@[norm_cast, simp]
theorem coe_algebraMap : ⇑(algebraMap R (QuadraticAlgebra R a b)) = coe := rfl

theorem smul_coe (r1 r2 : R) :
    r1 • (r2 : QuadraticAlgebra R a b) = ↑(r1 * r2) := by rw [coe_mul, coe_mul_eq_smul]

end CommSemiring

section CommRing

instance instCommRing [CommRing R] : CommRing (QuadraticAlgebra R a b) where
  __ := inferInstanceAs (AddCommGroupWithOne (QuadraticAlgebra R a b))
  __ := inferInstanceAs (CommSemiring (QuadraticAlgebra R a b))

end CommRing

section Star

variable [Add R] [Mul R] [Neg R]

instance quadraticStar : Star (QuadraticAlgebra R a b) where
  star z := ⟨z.1 + b * z.2, -z.2⟩

@[simp] theorem star_re (z : QuadraticAlgebra R a b) : (star z).re = z.re + b * z.im := rfl

@[simp] theorem star_im (z : QuadraticAlgebra R a b) : (star z).im = -z.im := rfl

@[simp] theorem star_mk (x y : R) : star (mk x y : QuadraticAlgebra R a b) = ⟨x + b * y, -y⟩ := rfl

end Star
section StarRing
variable [CommRing R]

instance : StarRing (QuadraticAlgebra R a b) where
  star_involutive _ := by ext <;> simp
  star_mul z w := by ext <;> simp <;> ring
  star_add z w := by ext <;> simp [add_comm] ; ring

theorem self_add_star' (z : QuadraticAlgebra R a b) : z + star z = ↑(2 * z.re + b * z.im) := by
  ext <;> simp [two_mul, add_assoc]

theorem self_add_star (z : QuadraticAlgebra R a b) :
    z + star z = 2 * z.re + b * z.im := by
  ext <;> simp [self_add_star']

theorem star_add_self' (z : QuadraticAlgebra R a b) :
    star z + z = ↑(2 * z.re + b * z.im) := by
  ext <;> simp [two_mul, add_comm, add_assoc]

theorem star_add_self (z : QuadraticAlgebra R a b) :
    star z + z = 2 * z.re + b * z.im := by
  ext <;> simp [star_add_self']

theorem star_eq_two_re_sub (z : QuadraticAlgebra R a b) :
    star z = ↑(2 * z.re + b * z.im) - z :=
  eq_sub_iff_add_eq.2 z.star_add_self'

instance (z : QuadraticAlgebra R a b) : IsStarNormal z :=
  ⟨by
    rw [commute_iff_eq, z.star_eq_two_re_sub];
    ext <;> simp <;> ring⟩

@[simp, norm_cast]
theorem star_coe (r : R) : star (r : QuadraticAlgebra R a b) = r := by ext <;> simp

@[simp]
theorem star_smul [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]
    (s : S) (z : QuadraticAlgebra R a b) : star (s • z) = s • star z :=
  QuadraticAlgebra.ext (by simp [mul_smul_comm]) (smul_neg _ _).symm

theorem star_smul' [Monoid S] [DistribMulAction S R] (s : S) (z : QuadraticAlgebra R a 0) :
    star (s • z) = s • star z :=
  QuadraticAlgebra.ext (by simp) (smul_neg _ _).symm

theorem eq_re_of_eq_coe {z : QuadraticAlgebra R a b} {x : R} (h : z = x) : z = z.re := by
  rw [h, coe_re]

theorem eq_re_iff_mem_range_coe {z : QuadraticAlgebra R a b} :
    z = z.re ↔ z ∈ Set.range coe := ⟨fun h ↦ ⟨z.re, h.symm⟩, fun ⟨_, h⟩ ↦ eq_re_of_eq_coe h.symm⟩

theorem star_mul_eq_coe {z : QuadraticAlgebra R a b} : star z * z = (star z * z).re := by
  ext <;> simp ; ring

theorem mul_star_eq_coe {z : QuadraticAlgebra R a b} : z * star z = (z * star z).re := by
  ext <;> simp ; ring

open MulOpposite in
def starAe : QuadraticAlgebra R a b ≃ₐ[R] (QuadraticAlgebra R a b)ᵐᵒᵖ :=
  { starAddEquiv.trans opAddEquiv with
    map_mul' _ _ := by simp [star_mul]
    commutes' _ := by simp}

@[simp]
lemma coe_starAe : ⇑starAe = MulOpposite.op ∘ (star (R := QuadraticAlgebra R a b)) := rfl

end StarRing

section Norm

variable [CommRing R]

def normSq : QuadraticAlgebra R a b →*₀ R where
  toFun z := (z * star z).re
  map_zero' := by simp
  map_one' := by simp
  map_mul' _ _ := by simpa using by ring

theorem normSq_def (z : QuadraticAlgebra R a b) : normSq z = (z * star z).re := rfl

theorem normSq_def' (z : QuadraticAlgebra R a b) :
    normSq z = z.re ^ 2 + b * z.im * z.re - a * z.im ^ 2 := by
  rw [normSq_def]; simp ; ring

theorem normSq_coe (r : R) : normSq (r : QuadraticAlgebra R a b) = r ^ 2 := by
  simp [normSq_def, pow_two]

@[simp]
theorem normSq_star (z : QuadraticAlgebra R a b) : normSq (star z) = normSq z := by
  simp [normSq_def']; ring

@[norm_cast]
theorem normSq_natCast (n : ℕ) : normSq (n : QuadraticAlgebra R a b) = n ^ 2 :=
  coe_natCast (R := R) n |>.symm ▸ normSq_coe _

@[norm_cast]
theorem normSq_intCast (n : ℤ) : normSq (n : QuadraticAlgebra R a b) = n ^ 2 :=
  coe_intCast (R := R) n |>.symm ▸ normSq_coe _

@[simp]
theorem normSq_neg (z : QuadraticAlgebra R a b) : normSq (-z) = normSq z := by
  simp [normSq_def]

theorem self_mul_star (z : QuadraticAlgebra R a b) :
    z * star z = normSq z := by rw [mul_star_eq_coe, normSq_def]

theorem star_self_mul (z : QuadraticAlgebra R a b) :
    star z * z = normSq z := by rw [star_mul_eq_coe, normSq_def, mul_comm]

end Norm

section Field

variable [Field R]

instance : NNRatCast (QuadraticAlgebra R a b) where nnratCast q := (q : R)

instance : RatCast (QuadraticAlgebra R a b) where ratCast q := (q : R)

@[simp, norm_cast] lemma re_nnratCast (q : ℚ≥0) : (q : QuadraticAlgebra R a b).re = q := rfl

@[simp, norm_cast] lemma im_nnratCast (q : ℚ≥0) : (q : QuadraticAlgebra R a b).im = 0 := rfl

@[simp, norm_cast] lemma re_ratCast (q : ℚ) : (q : QuadraticAlgebra R a b).re = q := rfl

@[simp, norm_cast] lemma im_ratCast (q : ℚ) : (q : QuadraticAlgebra R a b).im = 0 := rfl

@[norm_cast] lemma coe_nnratCast (q : ℚ≥0) : (q : R) = (q : QuadraticAlgebra R a b) := rfl

@[norm_cast] lemma coe_ratCast (q : ℚ) : (q : R) = (q : QuadraticAlgebra R a b) := rfl

@[simps -isSimp]
instance : Inv (QuadraticAlgebra R a b) where inv z := (normSq z)⁻¹ • star z

instance : GroupWithZero (QuadraticAlgebra R a b) where
  inv_zero := by simp [inv_def]
  mul_inv_cancel z hz := by
    rw [inv_def, mul_smul_comm, self_mul_star, smul_coe, inv_mul_cancel₀ (fun h ↦ by
      rw [normSq_def'] at h
      sorry), coe_one]

end Field

end QuadraticAlgebra
