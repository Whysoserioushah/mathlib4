import Mathlib

-- this is half of the `AKLB` setup so there might be extra conditions not needed
variable {A K L : Type*} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [Field K] [Algebra A K]
  [IsFractionRing A K] [AddCommGroup L] [Module A L] [Module.Free A L] [Module.Finite A L]
  (B : LinearMap.BilinForm A L) (hB : (B.baseChange K).Nondegenerate)

include hB in
theorem Q1a : ∃ d : A, (Ideal.span {d} : Set A) = Set.range B.coeFnAddMonoidHom.uncurry := sorry

theorem Q1b (hB' : B.IsAlt) (l l' : L) (hll' : B l l' = (Q1a B hB).choose) :
    LinearIndependent A (fun i ↦ match i with | 0 => l | 1 => l' : Fin 2 → L)
    ∧ ∃ f : L →ₗ[A] (Fin 2 → A), Function.LeftInverse (Fintype.linearCombination A
      (fun i ↦ match i with | 0 => l | 1 => l') : (Fin 2 → A) →ₗ[A] L) f := sorry
