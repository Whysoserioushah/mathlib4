import Mathlib

variable (p : ℕ) [Fact p.Prime]

open Matrix.GeneralLinearGroup

section Mathlib

open Matrix in
def GL.scalar (F n : Type*) [Field F] [Fintype n] [DecidableEq n] : Fˣ →* GL n F where
  toFun a := ⟨Matrix.scalar n a, Matrix.scalar n a⁻¹, by
    ext; simp [diagonal_apply, one_apply], by ext; simp [diagonal_apply, one_apply]⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [diagonal_apply]

instance GL.scalarNormal (F n : Type*) [Field F] [Fintype n] [DecidableEq n] :
    Subgroup.Normal (GL.scalar F n).range := by sorry

end Mathlib

theorem Q5a : Fintype.card ((GL (Fin 2) (ZMod p)) ⧸ (GL.scalar (ZMod p) (Fin 2)).range) =
    p * (p ^ 2 - 1) := sorry
