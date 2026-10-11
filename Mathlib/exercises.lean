module

public import Mathlib

/-!

-/

namespace exercise1

@[ext]
structure InvPair (α : Type*) [Monoid α] where
  val : α
  inv : α
  inv_val : inv * val = 1

@[simps]
def oneInvPair (α : Type*) [Monoid α] : InvPair α where
  val := 1
  inv := 1
  inv_val := mul_one _

instance (α : Type*) [Monoid α] : Mul (InvPair α) where
  mul P Q := {
    val := P.val * Q.val
    inv := Q.inv * P.inv
    inv_val := by rw [← mul_assoc, mul_assoc Q.inv, P.inv_val, mul_one, Q.inv_val]
  }

lemma InvPair.mul_val {α : Type*} [Monoid α] (P Q : InvPair α) :
    (P * Q).val = P.val * Q.val := rfl

lemma InvPair.mul_inv {α : Type*} [Monoid α] (P Q : InvPair α) :
    (P * Q).inv = Q.inv * P.inv := rfl

@[simps]
def mulSwapped (α : Type*) [Monoid α] (P Q : InvPair α) : InvPair α where
  val := Q.val * P.val
  inv := P.inv * Q.inv
  inv_val := by rw [← mul_assoc, mul_assoc P.inv, Q.inv_val, mul_one, P.inv_val]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
lemma oneInvPair_mul_eq_mulSwapped (α : Type*) [Monoid α] (P : InvPair α) :
    HMul.hMul (self := @instHMul _ ⟨mulSwapped α⟩) P (oneInvPair α) =
      oneInvPair α * P := by
  ext <;> simp [InvPair.mul_val, InvPair.mul_inv]
  <;> unfold mulSwapped <;> sorry

end exercise1
