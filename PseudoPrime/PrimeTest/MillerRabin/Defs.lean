/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.ZMod.Basic
public import PseudoPrime.PrimeTest.Precheck

/-!
# Strong Miller–Rabin definitions

The exponent `n - 1` is represented as `d * 2^s`, with `d` odd.  The
finite-range formulation makes the executable Boolean test total for every
natural input; input prechecking is supplied by the surrounding interface.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Compute the residue a^r in ZMod n by binary exponentiation, for any natural n,a,r.
This is the executable power operation underlying the Miller-Rabin test.
-/
def zmodPowFast (n a : ℕ) (r : ℕ) : ZMod n :=
  npowBinRec r (a : ZMod n)

/--
Executable wrapper around zmodPowFast, returning a^r modulo n.
Proofs rewrite it to ordinary power while runtime tests retain binary exponentiation.
-/
def zmodPow (n a : ℕ) (r : ℕ) : ZMod n :=
  zmodPowFast n a r

/-- The proof-side definition of `ZMod` exponentiation.

This is deliberately noncomputable: all executable code goes through
`zmodPow`, while proofs can use the ordinary power notation directly. -/
noncomputable def zmodPowProof (n a : ℕ) (r : ℕ) : ZMod n :=
  (a : ZMod n) ^ r

/--
For any n,a,r, the proof-side exponentiation is ordinary ZMod power by definition.
This unfolding lemma connects the specification with standard power identities.
-/
theorem zmodPowProof_eq_pow (n a r : ℕ) : zmodPowProof n a r = (a : ZMod n) ^ r := by rfl

/--
For any n,a,r, executable binary exponentiation equals ordinary ZMod power.
Induction on r uses the zero and successor equations for npowBinRec.
This is the correctness bridge from runtime residues to algebraic proofs.
-/
theorem zmodPow_eq_pow (n a r : ℕ) : zmodPow n a r = (a : ZMod n) ^ r := by
  unfold zmodPow zmodPowFast
  induction r with
  | zero => rw [npowBinRec_zero, pow_zero]
  | succ r ih => rw [npowBinRec_succ, pow_succ, ih]

/--
For any n,a,r, executable and proof-side exponentiation agree.
Rewrite both to ordinary power; this transfers the finite Miller-Rabin condition.
-/
theorem zmodPow_eq_zmodPowProof (n a r : ℕ) : zmodPow n a r = zmodPowProof n a r := by
  rw [zmodPow_eq_pow, zmodPowProof_eq_pow]

/--
For every m, 2^(padicValNat 2 m) times Nat.divMaxPow m 2 equals m.
Apply the natural factorization theorem, including m=0.
Nonzero-input oddness is supplied separately when decomposing Miller-Rabin exponents.
-/
theorem twoAdicPart_mul_oddPart (m : ℕ) : 2 ^ padicValNat 2 m * Nat.divMaxPow m 2 = m := by
  exact Nat.pow_padicValNat_mul_divMaxPow 2 m

/-- For nonzero m, removing its maximal power of two leaves an odd quotient.
Use coprimality with two and the maximal-power nondivisibility theorem.
This establishes the odd-part premise used in Miller-Rabin exponent decompositions. -/
theorem oddPart_odd {m : ℕ} (hm : m ≠ 0) : Odd (Nat.divMaxPow m 2) := by
  apply Nat.coprime_two_left.mp
  apply Nat.prime_two.coprime_iff_not_dvd.mpr
  exact Nat.not_dvd_divMaxPow (by decide) hm

/--
Proof-side finite strong probable-prime condition at natural base a and modulus n.
Write n-1 = 2^s d and require a^d=1 or a^(d*2^r)=n-1 in ZMod n for some r<s.
The definition is total and performs no input precheck; prime soundness uses separate hypotheses.
-/
def IsStrongMillerRabinProbablePrime (n a : ℕ) : Prop :=
  let s := padicValNat 2 (n - 1)
  let d := Nat.divMaxPow (n - 1) 2
  zmodPowProof n a d = 1 ∨ ∃ r ∈ List.range s, zmodPowProof n a (d * 2 ^ r) = n - 1

/--
Executable finite strong condition using zmodPow in place of proof-side power.
The alternatives are a^d=1 or a^(d*2^r)=n-1 for r in List.range s, where n-1=2^s d.
No small-input guard is included; the equivalence lemma connects this to the specification.
-/
def IsStrongMillerRabinProbablePrimeFast (n a : ℕ) : Prop :=
  let s := padicValNat 2 (n - 1)
  let d := Nat.divMaxPow (n - 1) 2
  zmodPow n a d = 1 ∨ ∃ r ∈ List.range s, zmodPow n a (d * 2 ^ r) = n - 1

/--
Decide the finite strong Miller-Rabin condition for the explicit natural base a.
Binary modular powers test a^d=1 or a^(d*2^r)=n-1 over r<s in n-1=2^s d.
A true result is a probable-prime pass; small-input classification is provided by wrappers.
-/
def strongMillerRabinWithBase (n a : ℕ) : Bool :=
  let s := padicValNat 2 (n - 1)
  let d := Nat.divMaxPow (n - 1) 2
  decide (zmodPow n a d = 1 ∨ ∃ r ∈ List.range s, zmodPow n a (d * 2 ^ r) = n - 1)

/--
For any n and a, fast and proof-side finite strong conditions are equivalent.
Rewrite every executable power with its correctness theorem.
This permits the executable Boolean contract to use the algebraic specification.
-/
theorem isStrongMillerRabinProbablePrimeFast_iff {n a : ℕ} :
    IsStrongMillerRabinProbablePrimeFast n a ↔ IsStrongMillerRabinProbablePrime n a := by
  simp only [IsStrongMillerRabinProbablePrimeFast, IsStrongMillerRabinProbablePrime,
    zmodPow_eq_zmodPowProof]

/--
Specialize the unguarded strong Miller-Rabin Boolean condition to base two.
This component is used by BPSW; its prechecked wrapper handles exceptional small inputs.
-/
def strongMillerRabinBase2 (n : ℕ) : Bool :=
  strongMillerRabinWithBase n 2

/--
Apply the common primality precheck, then run base-two Miller-Rabin only on none.
A precheck result is returned directly; otherwise a probable-prime pass remains uncertified.
The wrapper supplies the one-sided primality-test interface.
-/
def strongMillerRabinBase2WithPrecheck (n : ℕ) : Bool :=
  match primalityPrecheck n with
  | some result => result
  | none => strongMillerRabinBase2 n

end PseudoPrime.PrimeTest
