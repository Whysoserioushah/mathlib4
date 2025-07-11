/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Yunzhou Xie, Sidharth Hariharan
-/
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Complex.Basic

/-!
## `norm_num` extension for complex numbers

This file provides a `norm_num` extension for complex numbers, allowing the computation of
additions, multiplications, inversions, conjugates, and powers of complex numbers.

-/

open Lean Meta Elab Qq Tactic Complex Mathlib.Tactic
open ComplexConjugate

namespace Mathlib.Meta
namespace NormNumI

structure IsComplex (z : ℂ) (re im : ℝ) : Prop where
  out : z = ⟨re, im⟩

theorem IsComplex.I : IsComplex I 0 1 := ⟨rfl⟩

theorem IsComplex.zero : IsComplex (0 : ℂ) 0 0 := ⟨rfl⟩

theorem IsComplex.one : IsComplex (1 : ℂ) 1 0 := ⟨rfl⟩

theorem IsComplex.add : ∀ {z₁ z₂ : ℂ} {a₁ a₂ b₁ b₂ : ℝ},
    IsComplex z₁ a₁ b₁ → IsComplex z₂ a₂ b₂ → IsComplex (z₁ + z₂) (a₁ + a₂) (b₁ + b₂)
  | _, _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩ => ⟨rfl⟩

theorem IsComplex.mul : ∀ {z₁ z₂ : ℂ} {a₁ a₂ b₁ b₂ : ℝ},
    IsComplex z₁ a₁ b₁ → IsComplex z₂ a₂ b₂ →
      IsComplex (z₁ * z₂) (a₁ * a₂ - b₁ * b₂) (a₁ * b₂ + b₁ * a₂)
  | _, _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩ => ⟨rfl⟩

theorem IsComplex.inv {z : ℂ} {x y : ℝ} (h : IsComplex z x y) :
    IsComplex z⁻¹ (x / (x * x + y * y)) (- y / (x * x + y * y)) := by
  constructor
  obtain ⟨rfl⟩ := h
  rw [inv_def]
  exact Complex.ext (by simp [normSq_apply]; rfl) (by simp [normSq_apply, neg_div]; rfl)

theorem IsComplex.neg : ∀ {z : ℂ} {a b : ℝ}, IsComplex z a b → IsComplex (-z) (-a) (-b)
  | _, _, _, ⟨rfl⟩ => ⟨rfl⟩

theorem IsComplex.conj : ∀ {z : ℂ} {a b : ℝ}, IsComplex z a b → IsComplex (conj z) a (-b)
  | _, _, _, ⟨rfl⟩ => ⟨rfl⟩

theorem IsComplex.ofNat (n : ℕ) [n.AtLeastTwo] :
    IsComplex (OfNat.ofNat (α := ℂ) n) (OfNat.ofNat n) 0 := ⟨rfl⟩

theorem IsComplex.scientific (m exp : ℕ) (x : Bool) :
    IsComplex (OfScientific.ofScientific m x exp : ℂ) (OfScientific.ofScientific m x exp : ℝ) 0 :=
  ⟨rfl⟩

theorem eq_eq {z : ℂ} {a b a' b' : ℝ} (pf : IsComplex z a b) (pf_a : a = a') (pf_b : b = b') :
  IsComplex z a' b' := by simp_all

theorem eq_of_eq_of_eq_of_eq {z w : ℂ} {az bz aw bw : ℝ}
    (hz : IsComplex z az bz) (hw : IsComplex w aw bw)
    (ha : az = aw) (hb : bz = bw) : z = w := by
  simp [hz.out, hw.out, ha, hb]

theorem ne_of_re_ne {z w : ℂ} {az bz aw bw : ℝ} (hz : IsComplex z az bz) (hw : IsComplex w aw bw)
    (ha : az ≠ aw) : z ≠ w := by
  simp [hz.out, hw.out, ha]

theorem ne_of_im_ne {z w : ℂ} {az bz aw bw : ℝ} (hz : IsComplex z az bz) (hw : IsComplex w aw bw)
    (hb : bz ≠ bw) : z ≠ w := by
  simp [hz.out, hw.out, hb]

theorem IsComplex.re_eq {z : ℂ} {a b : ℝ} (hz : IsComplex z a b) : Complex.re z = a := by
  simp [hz.out]

theorem IsComplex.im_eq {z : ℂ} {a b : ℝ} (hz : IsComplex z a b) : Complex.im z = b := by
  simp [hz.out]

theorem IsComplex.of_pow_negSucc {z w : ℂ} {a b : ℝ} {n : ℕ} {k k' : ℤ} (h : k = Int.negSucc n)
    (hk : NormNum.IsInt k' k)
    (hz : IsComplex (w ^ (n + 1))⁻¹ a b) (hz' : z = w ^ (k' : ℤ)) : IsComplex z a b := by
  obtain rfl : k' = k := by simpa using hk.out
  constructor
  simpa [h, hz'] using hz.out

theorem IsComplex.of_pow_ofNat {z w : ℂ} {k k' : ℤ} {n : ℕ} {a b : ℝ} (hz1 : z = w ^ k)
    (hw : IsComplex (w ^ n) a b) (hk' : k' = n) (hkk' : NormNum.IsInt k k') :
    IsComplex z a b := by
  obtain rfl : k = k' := by simpa using hkk'.out
  constructor
  simpa [hz1, hk'] using hw.out

/-- Parsing all the basic calculation in complex. -/
partial def parse (z : Q(ℂ)) : MetaM (Σ a b : Q(ℝ), Q(IsComplex $z $a $b)) := do
  match z with
  /- parse an addition: `z₁ + z₂` -/
  | ~q($z₁ + $z₂) =>
    let ⟨_a₁, _b₁, pf₁⟩ ← parse z₁
    let ⟨_a₂, _b₂, pf₂⟩ ← parse z₂
    pure ⟨_, _, q(.add $pf₁ $pf₂)⟩
  /- parse a multiplication: `z₁ * z₂` -/
  | ~q($z₁ * $z₂) =>
    let ⟨_a₁, _b₁, pf₁⟩ ← parse z₁
    let ⟨_a₂, _b₂, pf₂⟩ ← parse z₂
    pure ⟨_, _, q(.mul $pf₁ $pf₂)⟩
  /- parse an inversion: `z⁻¹` -/
  | ~q($z⁻¹) =>
    let ⟨_x, _y, pf⟩ ← parse z
    pure ⟨_, _, q(.inv $pf)⟩
  /- parse `z₁/z₂` -/
  | ~q($z₁ / $z₂) => do
    let ⟨_a, _b, pf⟩ ← parse q($z₁ * $z₂⁻¹)
    return ⟨_, _, q($pf)⟩
  /- parse `-z` -/
  | ~q(-$w) => do
    let ⟨_a, _b, pf⟩ ← parse w
    return ⟨_, _, q(.neg $pf)⟩
  /- parse a subtraction `z₁ - z₂` -/
  | ~q($z₁ - $z₂) => parse q($z₁ + -$z₂)
  /- parse conjugate `conj z` -/
  | ~q(conj $w) =>
    let ⟨_a, _b, pf⟩ ← parse w
    return ⟨_, _, q(.conj $pf)⟩
  /- parse natural number power -/
  | ~q($w ^ ($n' : ℕ)) =>
    let ⟨n, hn⟩ ← NormNum.deriveNat q($n') q(inferInstance)
    match n.natLit! with
    | 0 =>
      let _i : $n =Q 0 := ⟨⟩
      return ⟨q(1), q(0), q(⟨show $w ^ $n' = _ from $(hn).out ▸ pow_zero _⟩)⟩
    | n + 1 =>
      parse q($w^$n * $w)
  /- parse integer power -/
  | ~q($w ^ ($k : ℤ)) =>
    let ⟨k', hm⟩ ← NormNum.deriveInt q($k) q(inferInstance)
    match k'.intLit! with
    | Int.ofNat n =>
      let ⟨a, b, pf⟩ ← parse q(@HPow.hPow ℂ ℕ ℂ instHPow $w $n)
      let _i : $k' =Q $n := ⟨⟩
      return ⟨a, b, q(.of_pow_ofNat rfl $pf rfl $hm)⟩
    | Int.negSucc n =>
      let ⟨a, b, pf⟩ ← parse q(($w ^ ($n + 1))⁻¹)
      let _i : $k' =Q Int.negSucc $n := ⟨⟩
      return ⟨a, b, q(.of_pow_negSucc rfl $hm $pf rfl)⟩
  /- parse `(I:ℂ)` -/
  | ~q(Complex.I) =>
    pure ⟨_, _, q(.I)⟩
  /- parse `(0:ℂ)` -/
  | ~q(0) =>
    pure ⟨_, _, q(.zero)⟩
  /- parse `(1:ℂ)` -/
  | ~q(1) =>
    pure ⟨_, _, q(.one)⟩
  /- anything else needs to be on the list of atoms -/
  | ~q(OfNat.ofNat $en (self := @instOfNatAtLeastTwo ℂ _ _ $inst)) =>
    return ⟨_, _, q(.ofNat $en)⟩
  | ~q(OfScientific.ofScientific $m $x $exp) =>
    return ⟨_, _, q(.scientific _ _ _)⟩
  | _ => throwError "found the atom {z} which is not a numeral"

/-- Using `norm_num` to normalise expressions -/
def normalize (z : Q(ℂ)) : MetaM (Σ a b : Q(ℝ), Q(IsComplex $z $a $b)) := do
  let ⟨a, b, pf⟩ ← parse z
  let ra ← Mathlib.Meta.NormNum.derive (α := q(ℝ)) a
  let rb ← Mathlib.Meta.NormNum.derive (α := q(ℝ)) b
  let { expr := (a' : Q(ℝ)), proof? := (pf_a : Q($a = $a')) } ← ra.toSimpResult | unreachable!
  let { expr := (b' : Q(ℝ)), proof? := (pf_b : Q($b = $b')) } ← rb.toSimpResult | unreachable!
  return ⟨a', b', q(eq_eq $pf $pf_a $pf_b)⟩

/-- Create the `NormNumI` tactic in `conv` mode. -/
elab "norm_numI" : conv => do
  let z ← Conv.getLhs
  let ⟨1, ~q(ℂ), z⟩ ← inferTypeQ z | throwError "{z} is not a complex number"
  let ⟨_, _, pf⟩ ← normalize z
  let r : Simp.ResultQ q($z) := .mk _ <| .some q(($pf).out)
  Conv.applySimpResult r

end NormNumI
namespace NormNum

/-- The `norm_num` extension which identifies expressions of the form `(z : ℂ) = (w : ℂ)`,
such that `norm_num` successfully recognises both the real and imaginary parts of both `z` and `w`.
-/
@[norm_num (_ : ℂ) = _] def evalComplexEq : NormNumExt where eval {v β} e := do
  haveI' : v =QL 0 := ⟨⟩; haveI' : $β =Q Prop := ⟨⟩
  let .app (.app f z) w ← whnfR e | failure
  guard <| ← withNewMCtxDepth <| isDefEq f q(Eq (α := ℂ))
  have z : Q(ℂ) := z
  have w : Q(ℂ) := w
  haveI' : $e =Q ($z = $w) := ⟨⟩
  let ⟨az, bz, pfz⟩ ← NormNumI.parse z
  let ⟨aw, bw, pfw⟩ ← NormNumI.parse w
  let ⟨ba, ra⟩ ← withTraceNode `debug (fun x =>
    return m!"{exceptEmoji x} norm_numI.evalComplexEq: z = {az} + {bz}i {q($az = $aw)}") do
    deriveBool q($az = $aw)
  trace[debug] "norm_numI.evalComplexEq output: {ba} {ra}"
  match ba with
  | true =>
    let ⟨bb, rb⟩ ← deriveBool q($bz = $bw)
    match bb with
    | true => return Result'.isBool true q(NormNumI.eq_of_eq_of_eq_of_eq $pfz $pfw $ra $rb)
    | false => return Result'.isBool false q(NormNumI.ne_of_im_ne $pfz $pfw $rb)
  | false => return Result'.isBool false q(NormNumI.ne_of_re_ne $pfz $pfw $ra)

/-- The `norm_num` extension which identifies expressions of the form `Complex.re (z : ℂ)`,
such that `norm_num` successfully recognises the real part of `z`.
-/
@[norm_num Complex.re _] def evalRe : NormNumExt where eval {v β} e := do
  haveI' : v =QL 0 := ⟨⟩; haveI' : $β =Q ℝ := ⟨⟩
  let .proj ``Complex 0 z ← whnfR e | failure
  have z : Q(ℂ) := z
  haveI' : $e =Q (Complex.re $z) := ⟨⟩
  let ⟨a, _, pf⟩ ← NormNumI.parse z
  let r ← derive q($a)
  return r.eqTrans q(($pf).re_eq)

/-- The `norm_num` extension which identifies expressions of the form `Complex.im (z : ℂ)`,
such that `norm_num` successfully recognises the imaginary part of `z`.
-/
@[norm_num Complex.im _] def evalIm : NormNumExt where eval {v β} e := do
  haveI' : v =QL 0 := ⟨⟩; haveI' : $β =Q ℝ := ⟨⟩
  let .proj ``Complex 1 z ← whnfR e | failure
  have z : Q(ℂ) := z
  haveI' : $e =Q (Complex.im $z) := ⟨⟩
  let ⟨_, b, pf⟩ ← NormNumI.parse z
  let r ← derive q($b)
  return r.eqTrans q(($pf).im_eq)

end NormNum

end Mathlib.Meta
