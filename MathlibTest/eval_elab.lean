import Mathlib.Tactic.Eval
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Util.Qq

#guard_expr eval% 2^10 =ₛ 1024

#guard_expr (eval% 2^10 : Int) =ₛ (1024 : Int)

#guard_expr
  (eval% Multiset.powerset ({1, 2, 3} : Multiset ℕ)) =
    {0, {1}, {2}, {1, 2}, {3}, {1, 3}, {2, 3}, {1, 2, 3}}

-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/How.20to.20simplify.20this.20proof.20without.20using.20a.20have.20statement.3F/near/422294189
section from_zulip

/--
error: failed to synthesize
  Lean.ToExpr (Finset (Finset ℕ))

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#check eval% Finset.powerset ({1, 2, 3} : Finset ℕ)

open Lean Qq

/-- `HasInstance (Foo X)` means than an `inst : Foo X` exists. -/
class HasInstance (α : Type u) where
  /-- The reflected version of `inst`. -/
  expr : Expr

-- this obviously doesn't scale, which is why this is only in the test file
instance : HasInstance (DecidableEq ℕ) :=
  ⟨q(inferInstanceAs <| DecidableEq ℕ)⟩
instance : HasInstance (DecidableEq (Finset ℕ)) :=
  ⟨q(inferInstanceAs <| DecidableEq (Finset ℕ))⟩
instance : HasInstance (DecidableEq (Finset (Finset ℕ))) :=
  ⟨q(inferInstanceAs <| DecidableEq (Finset (Finset ℕ)))⟩

open Qq Lean
/-- `Finset α` can be converted to an expr only if there is some way to find `DecidableEq α`. -/
unsafe nonrec instance Finset.toExpr
    {α : Type u} [ToLevel.{u}] [ToExpr α] [HasInstance (DecidableEq α)] : ToExpr (Finset α) :=
  haveI u' : Level := Lean.toLevel.{u}
  haveI α' : Q(Type u') := Lean.toTypeExpr α
  letI : Q(DecidableEq $α') := HasInstance.expr (DecidableEq α)
  { toTypeExpr := q(Finset $α')
    toExpr x := show Q(Finset $α') from mkSetLiteralQ q(Finset $α') (x.val.unquot.map toExpr) }

#guard_expr
  (eval% Finset.powerset ({1, 2, 3} : Finset ℕ)) =
    {∅, {1}, {2}, {1, 2}, {3}, {1, 3}, {2, 3}, {1, 2, 3}}

end from_zulip
