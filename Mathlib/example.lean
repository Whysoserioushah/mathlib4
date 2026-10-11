module

public import Mathlib

/-!
## Understanding reducibilities and different ways to work with them

1. Irreducible
2. Semireducible
3. implicit reducible
4. instance reducible
5. reducible

-/

@[expose] public section

/-! ## Why are reducibilities important?

## How Lean processes a theorem

Lean source
    |
    v
Parser
    |
    v
Elaboration (including macros and tactic execution)
    |
    +--> Logical definitions and proof terms
    |        |
    |        v
    |      Kernel --> Accepted declarations
    |
    +--> Executable definitions
    |        |
    |        v
    |      Compiler --> Interpreter / native execution
    |
    +--> Expressions and goals
             |
             v
       Delaborator and pretty printer --> Display

  During elaboration               What defEq helps establish

1. Checking a term                  Its inferred type matches the expected type
2. Inferring omitted arguments      Assignments to unknowns make the surrounding expressions match
3. Typeclass synthesis              A candidate instance fits the requested instance type
4. Running tactics                  A lemma matches a target, or a proposed proof fits the goal

For more detailed information about this, please read https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/

-/

section examplesForElab

-- example for 1
/--
error: Type mismatch
  x
has type
  Fin n
but is expected to have type
  Fin (0 + n)
-/
#guard_msgs in
example (n : Nat) (x : Fin n) : Fin (0 + n) := x

-- example for 2
def makePair {α : Type} (x y : α) : α × α := (x, y)

/--
error: Application type mismatch: The argument
  false
has type
  Bool
but is expected to have type
  ℕ
in the application
  makePair 1 false
---
info: makePair 1 sorry : ℕ × ℕ
-/
#guard_msgs in
#check makePair (1 : ℕ) false

-- example for 3

/--
error: failed to synthesize instance of type class
  HAdd α α ?m.3

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
variable {α : Type*} (x y : α) in
#check x + y

-- example for 4: see below

end examplesForElab

-- # irreducible

def ordinary : Nat := 42

-- when doing `irreducible_def x := y`, it would give a non-penetrable def
-- and auto-generate a lemma `x_def` saying `x = y`.
irreducible_def hide : Nat := 42

/-- info: hide_def : hide = 42 -/
#guard_msgs in
#check hide_def

-- Ordinary definitions unfold automatically.
example : ordinary = 42 := rfl

/--
info: @[irreducible, expose] def hide : ℕ :=
wrapped✝.1
-/
#guard_msgs in
#print hide

/--
info: @[expose] def ordinary : ℕ :=
42
-/
#guard_msgs in
#print ordinary

/--
error: Tactic `rfl` failed: The left-hand side
  hide + 1
is not definitionally equal to the right-hand side
  43

⊢ hide + 1 = 43
-/
#guard_msgs in
example : hide + 1 = 43 := by rfl

/-- info: 42 -/
#guard_msgs in
#eval hide  -- 42: compiled evaluation still works.

set_option linter.style.native false in
example : hide = 42 := by decide +native -- dangerous tactic

/--
trace: ⊢ wrapped✝.1 = 42
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : hide = 42 := by
  unfold hide
  -- here `unfold` gives uncomprehensible results
  trace_state
  sorry

-- # semireducible (default) reducibility
/-!
Now this is where things get interesting: how to make good design decisions to semireducible defs
are one of the key factors that determines your code quality
-/

def myNat := Nat
deriving AddCommMonoid, NatCast

-- `erw [x]` is the same as `rw (transparency := default) [x]`
/--
info: Debugging `erw?`
---
info: ❌️ at reducible transparency,
  Zero.toOfNat0
and
  instOfNatNat 0
are not defeq, but they are at default transparency.
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : 0 + (2 : myNat) = (2 : ℕ) := by
  erw? [Nat.zero_add]
  sorry

-- ## Subsection : Implicit and explicit variables

-- 1. Both arguments are explicit.
def myIdExplicit (α : Type) (x : α) : α := x

#check myIdExplicit Nat 3       -- Nat
#check myIdExplicit String "hi" -- String

-- 2. The type argument is implicit: inferred from x.
def myIdImplicit {α : Type} (x : α) : α := x

#check myIdImplicit 3 -- Nat
#check myIdImplicit "hi"      -- String

-- You can still supply an implicit argument explicitly.
#check myIdImplicit (α := myNat) 3
-- note that the default type when you put in a natural number is ℕ

/- In this example we learn the first way to bypass this sort of issue, with this option turned off
  you promote the implicit argument defEq check to `.deault` level. -/
set_option backward.isDefEq.respectTransparency false in
example : 0 + (2 : myNat) = 2 := by
  rw [Nat.zero_add]

instance : Sub myNat := by
  -- `unfold` here gives actual outputs
  unfold myNat
  infer_instance

-- # implicit reducible level

section defEqAttrib

-- In real life this could be any structures, e.g `Submodule`, `Subgroup`, `LinearMap`, etc.
structure NatBox where
  val : Nat

@[simps]
def myBox : NatBox where
  val := 42

/--
info: @[backward_defeq] theorem myBox_val : myBox.val = 42 :=
Eq.refl myBox.val
-/
#guard_msgs in
#print myBox_val

/-!
The process goes like this

1. `simp` reaches `f myBox.val i`.
2. It notices that the type of `i` depends on the first argument.
3. It uses `dsimp` to simplify `myBox.val`.
4. With the option off, `dsimp` ignores the backward-only lemma `myBox_val`.
5. Nothing changes, so `simp` reports that it made no progress.

-/
example (f : (n : Nat) → Fin n → Nat) (i : Fin myBox.val)
    (h : f 42 i = 0) : f myBox.val i = 0 := by
  fail_if_success simp only [myBox_val]
  guard_target =ₛ f myBox.val i = 0
  exact h

/--
trace: f : (n : ℕ) → Fin n → ℕ
i : Fin myBox.val
h : f 42 i = 0
⊢ f 42 i = 0
-/
#guard_msgs in
set_option backward.defeqAttrib.useBackward true in
example (f : (n : Nat) → Fin n → Nat) (i : Fin myBox.val)
    (h : f 42 i = 0) : f myBox.val i = 0 := by
  simp only [myBox_val]
  trace_state
  exact h

end defEqAttrib

section implicit

-- ## implicit reducibility

/-!
This section is about implicit reducibility in lean, this is almost the most important part in this
lecture, the decision between semireducible and implicit reducible when we're making definitions
will almost always be important for us if our goal is to create high quality formalizations.


# What is implicit reducible?

Use this attribute for definitions that should unfold when checking implicit-argument
definitional equality (e.g. abbreviations in downstream libraries such as Mathlib functors),
without affecting type class search. When proof automation applies a lemma, implicit arguments
are checked with increased transparency so that type-level computations (e.g. `n + 0` vs `n`)
are resolved.

In short tagging a definition with `@[implicit_reducible]`just mean it would make all its implicit
arguments `reducible` when checking.

-/

@[implicit_reducible, simps]
def myBoxImp : NatBox where
  val := 42

-- And now we can see that tagging `myBoxImp` with `@[implicit_reducible]` changes the lemma
-- generated by `simps` from `backward_defeq` to `defeq`.
/--
info: @[defeq] theorem myBoxImp_val : myBoxImp.val = 42 :=
Eq.refl myBoxImp.val
-/
#guard_msgs in
#print myBoxImp_val

example (f : (n : Nat) → Fin n → Nat) (i : Fin myBoxImp.val)
    (h : f 42 i = 0) : f myBoxImp.val i = 0 := by
  -- now `simp` works
  simp [h]

-- another way to check if `a` and `b` are implicit reducibly equal is to use `with_implict rfl`:
example : myBoxImp.val = 42 := by with_implicit rfl

example : myBox.val = 42 := by
  fail_if_success with_implicit rfl -- this doesn't work because `myBox` is not implicit reducible
  rfl -- this works because `rfl` can penetrate semireducible level

@[implicit_reducible]
def myNatImp := Nat
  deriving AddCommMonoid, NatCast

example : 0 + (2 : myNatImp) = 2 := by
  -- this now works too because `implicit_reducible` on the type is carried over on its
  -- derived instance
  rw [Nat.zero_add]

/--
error: failed to synthesize instance of type class
  Sub myNatImp

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
instance : Sub myNatImp := by
  -- this still doesn't work because in the goal, `myNatImp` is not implicit variable, it's explicit!
  infer_instance

end implicit

section instanceReducible

/-!

## instance reducible

`@[instance_reducible]` allows Lean to unfold a definition at .instances transparency, which is used
when matching typeclass instances. An ordinary def is semireducible and generally stays folded at
that level. The `instance` command automatically marks its definition as instance-reducible.


-/

/-- info: 0 -/
#guard_msgs in
#eval (default : Nat)

-- Here we see instance depending on free variable is not allowed in lean, however it is allowed
-- (and sometimes very helpful!) to have them as `instance_reducible` definitions.

-- a good example (for those who understands a bit more) is
-- `Localization.AtPrime.algebraOfLiesOver`

#check Localization.AtPrime.algebraOfLiesOver

/--
error: This instance has 1 argument that cannot be inferred using typeclass synthesis. Specifically

  argument 1: `(n : ℕ)`

These arguments are not instance-implicit and appear neither in another instance-implicit argument nor the return type, so they cannot be inferred using typeclass synthesis.
-/
#guard_msgs in
instance (n : Nat) : Inhabited Nat := ⟨n⟩

@[instance_reducible]
def MyNat : Type := Nat

def mixedArithmetic : Nat × Nat :=
  -- Intended: multiplication on MyNat means addition.
  letI : Mul MyNat := ⟨Nat.add⟩
  ((3 : Nat) * 3, (3 : Nat) ^ 2)

/-- info: (6, 9) -/
#guard_msgs in
#eval mixedArithmetic

/-
This seems surprising, so what happened?

- To elaborate 3 * 3, Lean requests Mul Nat. The local Mul MyNat matches because instance search
  can unfold MyNat.
- Exponentiation still uses the existing natural-number power operation, whose definition uses
  the original Nat.mul.

Consequently, * means addition here, while ^ still means ordinary exponentiation (If you trace the
instance of the natural powers of naturals, you'll find `Nat.instMonoid.toNPow`).

This is the danger of allowing instance matching to unfold an alias intended to distinguish
different structures.

Removing @[instance_reducible] makes MyNat an ordinary semireducible alias. Then its local
multiplication does not match Mul Nat, and the first example returns `(9, 9)`.
-/

example : True := by
  let : Mul MyNat := ⟨Nat.add⟩
  -- The usual relationship between powers and multiplication fails.
  have : (3 : Nat) ^ 2 ≠ 3 * 3 := by decide
  -- In fact, that goal is false with the selected multiplication!
  have : (3 : Nat) * 0 ≠ 0 := by decide
  trivial

end instanceReducible

section reducible



end reducible

section tactic

/-!
## Tactics and their performing levels of transparency

In lean, different tactics performs at diferent levels of transparencies. In this section, we will
categorize them based on their "dangerous" level.

-/

-- `rw` :

end tactic
