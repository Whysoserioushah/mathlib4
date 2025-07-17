/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib

/-!

# R[X] / (X² − a • X − b)

TODO: Add module docstring

-/
-- a + b α
universe u

/-- `R[X]/(X^2−a*X−b)` -/
@[ext]
structure QuadraticAlgebra (R : Type u) (a b : R) : Type u where
  /-- TODO: Add docstring -/
  re : R
  /-- TODO: Add docstring -/
  im : R

namespace QuadraticAlgebra

/-- The equivalence between quadratic algebra over `R` and `R × R`. -/
@[simps]
def equivProd {R : Type*} (a b : R) : QuadraticAlgebra R a b ≃ R × R where
  toFun z := (z.re, z.im)
  invFun p := ⟨p.1, p.2⟩

/-- The equivalence between quadratic algebra over `R` and `Fin 2 → R`. -/
@[simps symm_apply]
def equivTuple {R : Type*} (a b : R) : QuadraticAlgebra R a b ≃ (Fin 2 → R) where
  toFun a := ![a.1, a.2]
  invFun f := ⟨f 0, f 1⟩
  right_inv _ := funext fun i ↦ by fin_cases i <;> simp

@[simp]
theorem equivTuple_apply {R : Type*} (a b : R) (z : QuadraticAlgebra R a b) :
    equivTuple a b z = ![z.re, z.im] := rfl

@[simp]
theorem mk_eta {R : Type*} {a b} (z : QuadraticAlgebra R a b) :
    mk z.re z.im = z := rfl

variable {S T R : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

instance [Subsingleton R] : Subsingleton (QuadraticAlgebra R a b) := (equivTuple a b).subsingleton

instance [Nontrivial R] : Nontrivial (QuadraticAlgebra R a b) := (equivTuple a b).nontrivial

section Zero

variable [Zero R]

/-- Coercion `R → ℍ[R,c₁,c₂,c₃]`. -/
@[coe] def coe (x : R) : QuadraticAlgebra R a b := ⟨x, 0⟩

instance : CoeTC R (QuadraticAlgebra R a b) := ⟨coe⟩

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

@[scoped simp] theorem zero_re : (0 : QuadraticAlgebra R a b).re = 0 := rfl

@[scoped simp] theorem zero_im : (0 : QuadraticAlgebra R a b).im = 0 := rfl

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

section SMul


variable {α} [SMul α R] {a b : R}

instance : SMul α (QuadraticAlgebra R a b) where
  smul a z := ⟨a • z.1, a • z.2⟩

@[simp]
theorem re_smul (r : α) (z : QuadraticAlgebra R a b) : (r • z).re = r • z.re := rfl

@[simp]
theorem im_smul (r : α) (z : QuadraticAlgebra R a b) : (r • z).im = r • z.im := rfl

end SMul

variable [CommSemiring R] {a b : R}

/-- TODO: Add docstring -/
def ofInt (n : R) : QuadraticAlgebra R a b :=
  ⟨n, 0⟩

theorem re_ofInt (n : R) : (ofInt n : QuadraticAlgebra R a b).re = n :=
  rfl

theorem im_ofInt (n : R) : (ofInt n : QuadraticAlgebra R a b).im = 0 :=
  rfl

/-- The zero of the ring -/
instance : Zero (QuadraticAlgebra R a b) :=
  ⟨ofInt 0⟩

@[simp]
theorem re_zero : (0 : QuadraticAlgebra R a b).re = 0 :=
  rfl

@[simp]
theorem im_zero : (0 : QuadraticAlgebra R a b).im = 0 :=
  rfl

/-- The one of the ring -/
instance : One (QuadraticAlgebra R a b) :=
  ⟨ofInt 1⟩

@[simp]
theorem re_one : (1 : QuadraticAlgebra R a b).re = 1 :=
  rfl

@[simp]
theorem im_one : (1 : QuadraticAlgebra R a b).im = 0 :=
  rfl

instance : Add (QuadraticAlgebra R a b) :=
  ⟨fun z w => ⟨z.1 + w.1, z.2 + w.2⟩⟩

@[simp]
theorem re_add (z w : QuadraticAlgebra R a b) : (z + w).re = z.re + w.re :=
  rfl

@[simp]
theorem im_add (z w : QuadraticAlgebra R a b) : (z + w).im = z.im + w.im :=
  rfl

instance : Mul (QuadraticAlgebra R a b) :=
  ⟨fun z w => ⟨z.1 * w.1 + b * z.2 * w.2, z.1 * w.2 + z.2 * w.1 + a * z.2 * w.2⟩⟩

@[simp]
theorem re_mul (z w : QuadraticAlgebra R a b) :
    (z * w).re = z.re * w.re + b * z.im * w.im :=
  rfl

@[simp]
theorem im_mul (z w : QuadraticAlgebra R a b) :
    (z * w).im = z.re * w.im + z.im * w.re + a * z.im * w.im :=
  rfl


instance addCommMonoid : AddCommMonoid (QuadraticAlgebra R a b) := by
  refine
  { add := (· + ·)
    zero := 0
    nsmul n z := n • z
    add_assoc := ?_
    zero_add := ?_
    add_zero := ?_
    add_comm := ?_
    nsmul_zero := ?_
    nsmul_succ := ?_ } <;>
  intros <;>
  ext <;>
  simp [add_comm, add_left_comm, add_mul]

instance addMonoidWithOne : AddMonoidWithOne (QuadraticAlgebra R a b) :=
  { QuadraticAlgebra.addCommMonoid with
    natCast := fun n => ofInt n
    natCast_zero := by ext <;> simp [re_ofInt, im_ofInt]
    natCast_succ := fun n => by
      ext <;> simp [re_ofInt, im_ofInt, Nat.succ_eq_add_one]
    one := 1 }

instance commSemiring : CommSemiring (QuadraticAlgebra R a b) := by
  refine
  { addMonoidWithOne with
    mul := (· * ·)
    npow := @npowRec (QuadraticAlgebra R a b) ⟨1⟩ ⟨(· * ·)⟩,
    add_comm := ?_
    left_distrib := ?_
    right_distrib := ?_
    zero_mul := ?_
    mul_zero := ?_
    mul_assoc := ?_
    one_mul := ?_
    mul_one := ?_
    mul_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp <;>
  ring

end QuadraticAlgebra
