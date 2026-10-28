/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.BPSW.EulerBaseTwo

/-! # Certified conditional Euler omission in Wheel30 BPSW

The optional entries omit Euler after base-two Strong MR for every signed power of two,
when n is odd and greater than one. All-input equalities preserve the established
specifications. Performance assessment remains separate from arithmetic correctness.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest.EulerRedundancy

/-- An integer whose absolute value has odd part one is a signed power of two.
The two-adic factorization identifies the exponent; the absolute-value alternatives
supply the sign. This certifies the executable eligibility test, including Q = 1 and -1. -/
theorem signed_two_power_of_oddPart_one (Q : ℤ) (h : Nat.divMaxPow Q.natAbs 2 = 1) :
    Q = (2 : ℤ) ^ padicValNat 2 Q.natAbs ∨ Q = -(2 : ℤ) ^ padicValNat 2 Q.natAbs := by
  have hf := Nat.pow_padicValNat_mul_divMaxPow 2 Q.natAbs
  rw [h, mul_one] at hf
  have hi : ((2 : ℕ) ^ padicValNat 2 Q.natAbs : ℤ) = (Q.natAbs : ℤ) :=
    congrArg (fun x : ℕ ↦ (x : ℤ)) hf
  rcases Int.natAbs_eq Q with he | he
  · exact Or.inl (he.trans hi.symm)
  · exact Or.inr (he.trans (congrArg Neg.neg hi.symm))

/-- Shared Strong and terminal-V evaluation for an integer Lucas parameter record.
Initialize one Lucas state and return its Strong flag conjoined with V = 2Q.
For odd moduli with Jacobi discriminant minus one, this equals the two existing tests.
The function performs no Euler comparison. -/
def strongVShared (n : ℕ) (param : LucasParams) : Bool :=
  let x := lucasStrengthenedState n param.D param.P param.Q
  x.strongOk && (x.v == 2 * (param.Q : ZMod n))

/-- For an odd modulus and Jacobi discriminant minus one, the shared evaluator equals
Strong Lucas conjoined with Lucas-V. The state invariants identify the flag and terminal V;
Boolean extensionality matches the modular comparison to the existing decision. -/
theorem strongVShared_eq {n : ℕ} (param : LucasParams) (hn : Odd n)
    (hD : jacobiSym param.D n = -1) :
    strongVShared n param =
      (strongLucasWithParams n param.D param.P param.Q &&
        lucasVWithParams n param.D param.P param.Q) := by
  simp only [strongVShared, lucasStrengthenedState_strong n hn, lucasStrengthenedState_v n hn,
    lucasProbablePrimeIndex_of_jacobi_eq_neg_one hD]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [lucasVWithParams, hD, true_and, lucasVZModFast_eq_lucasVZMod, beq_iff_eq,
    decide_eq_true_eq]

/-- Strengthened Lucas evaluator after a certified base-two Strong MR pass.
For odd n greater than one and Q with absolute odd part one, evaluate only shared
Strong and terminal V. Every signed power of two is eligible, including exponent zero.
Other inputs use the existing strengthened evaluator.
The erased MR and discriminant evidence justify the omission without repeating MR. -/
def strengthenedAfterMR (n : ℕ) (param : LucasParams) (_hMR : IsStrongMillerRabinProbablePrime n 2)
    (_hD : jacobiSym param.D n = -1) : Bool :=
  if 1 < n ∧ n % 2 = 1 ∧ Nat.divMaxPow param.Q.natAbs 2 = 1 then strongVShared n param
  else strengthenedLucasSharedEulerValid n param

/-- After a base-two MR pass and a selected Jacobi-minus-one discriminant, conditional
Euler omission preserves the strengthened result on every input.
The eligibility test supplies a signed-power witness and the general base-two theorem
makes Euler redundant. The shared state supplies the two remaining conditions. -/
theorem strengthenedAfterMR_eq (n : ℕ) (param : LucasParams)
    (hMR : IsStrongMillerRabinProbablePrime n 2) (hD : jacobiSym param.D n = -1) :
    strengthenedAfterMR n param hMR hD = strengthenedLucasSharedEulerValid n param := by
  unfold strengthenedAfterMR
  split
  · next h =>
      have ho := Nat.odd_iff.mpr h.2.1
      rw [strongVShared_eq param ho hD]
      exact
        (strengthened_without_euler_all h.1 ho hMR param (padicValNat 2 param.Q.natAbs)
            (signed_two_power_of_oddPart_one param.Q h.2.2)).symm
  · rfl

end PseudoPrime.PrimeTest.EulerRedundancy
