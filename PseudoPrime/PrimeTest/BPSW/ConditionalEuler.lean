/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.BPSW.EulerBaseTwo

/-! # Certified conditional Euler omission in Wheel30 BPSW

The optional entries omit Euler after base-two Strong MR for every signed power of two,
when n is odd and greater than one. All-input equalities preserve the established
specifications. Performance assessment remains separate from arithmetic correctness.
-/

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

namespace PseudoPrime.PrimeTest

/-- Consume a finite Selfridge outcome after a certified base-two MR pass.
Factors and exhaustion return false; selected parameters use ordinary Strong Lucas
or conditional strengthened evaluation. Only unconditional-budget wrappers treat
exhaustion as Boolean rejection; finite decision consumers must retain unknown. -/
def SelfridgeScanResult.acceptedAfterMR {n : ℕ} (strengthened : Bool)
    (hMR : IsStrongMillerRabinProbablePrime n 2) : SelfridgeScanResult n → Bool
  | .exhausted => false
  | .factor _ _ _ _ => false
  | .selected param hj =>
    if strengthened then EulerRedundancy.strengthenedAfterMR n param hMR hj
    else strongLucasWithParamsFast n param.D param.P param.Q

/-- The MR-certified outcome evaluator agrees with the existing acceptance flag.
Outcome cases preserve factors and exhaustion; the selected case uses conditional
Euler equivalence. This transfers the proof-carrying search consumer to the new entry. -/
theorem SelfridgeScanResult.acceptedAfterMR_eq {n : ℕ} (strengthened : Bool)
    (hMR : IsStrongMillerRabinProbablePrime n 2) (result : SelfridgeScanResult n) :
    result.acceptedAfterMR strengthened hMR = result.accepted strengthened := by
  cases result with
  | exhausted => rfl
  | factor g hl hu hd => rfl
  | selected param hj =>
    simp only [acceptedAfterMR, accepted, EulerRedundancy.strengthenedAfterMR_eq]

/-- Optional Wheel30 BPSW entry with certified conditional Euler omission.
Keep small-input, even-input, MR-first, square, and unconditional Selfridge stages.
Pass the already computed MR evidence to the selected Lucas consumer; strengthened
mode omits Euler only on the certified three-modulo-four signed-power branch. -/
def bpswWheel30ReducedEuler (n : ℕ) (strengthened : Bool) : Bool :=
  if n < 2 then false
  else
    if n = 2 then true
    else
      if Even n then false
      else
        if hm : strongMillerRabinWithBaseLoop n 2 = true then
          if natIsSquare n then false
          else
            (selfridgeNeOneResult n (2 * n)).acceptedAfterMR strengthened
              (strongMillerRabinWithBase_eq_true_iff.mp
                ((strongMillerRabinWithBaseLoop_eq n 2).symm.trans hm))
        else false

/-- For every natural input and both modes, the conditional entry equals bpswWheel30.
Outcome equivalence removes the MR proof argument, and a constant dependent if
becomes the original Boolean branch. This is an all-input equality contract. -/
theorem bpswWheel30ReducedEuler_eq (n : ℕ) (strengthened : Bool) :
    bpswWheel30ReducedEuler n strengthened = bpswWheel30 n strengthened := by
  simp only [bpswWheel30ReducedEuler, SelfridgeScanResult.acceptedAfterMR_eq, dite_eq_ite,
    bpswWheel30]

/-- Every prime passes the conditional Wheel30 entry in either mode.
Transport the existing unconditional prime-completeness theorem through Boolean equality. -/
theorem bpswWheel30ReducedEuler_of_prime {n : ℕ} (hp : n.Prime) (strengthened : Bool) :
    bpswWheel30ReducedEuler n strengthened = true := by
  rw [bpswWheel30ReducedEuler_eq]
  exact bpswWheel30_of_prime hp strengthened

/-- Certified decision from the unconditional conditional-Euler Wheel30 entry.
Boolean rejection proves non-primality; acceptance remains unknown.
Prime completeness justifies rejection and leaves later certificate searches available. -/
def BPSW.decideWheel30ReducedEuler (n : ℕ) (strengthened : Bool := false) : Decision n :=
  decideByPrimePass n (bpswWheel30ReducedEuler n strengthened)
    (fun hp ↦ bpswWheel30ReducedEuler_of_prime hp strengthened)

/-- The conditional entry preserves the existing natural certified decision on every input.
Boolean equality and proof irrelevance identify the rejection evidence and unknown outcome. -/
theorem BPSW.decideWheel30ReducedEuler_eq (n : ℕ) (strengthened : Bool) :
    decideWheel30ReducedEuler n strengthened = decideWheel30 n strengthened := by
  simp only [decideWheel30ReducedEuler, bpswWheel30ReducedEuler_eq, decideWheel30,
    decideByPrimePass, decideByTest]

/-- The conditional Wheel30 entry satisfies the public primality-test specification.
Function extensionality transports all small-input and prime-completeness fields
from the existing unconditional Wheel30 specification. -/
theorem bpswWheel30ReducedEuler_spec (strengthened : Bool) :
    PrimalityTestSpec (fun n ↦ bpswWheel30ReducedEuler n strengthened) := by
  rw [show (fun n ↦ bpswWheel30ReducedEuler n strengthened) = (fun n ↦ bpswWheel30 n strengthened)
      from funext (fun n ↦ bpswWheel30ReducedEuler_eq n _)]
  exact bpswWheel30_spec strengthened

/-- In strengthened mode, the conditional entry equals the independent paper specification.
Compose the all-input Wheel30 equality with the existing BFW specification theorem.
This checks the optimized procedure against the same five mathematical conditions. -/
theorem bpswWheel30ReducedEuler_eq_bfw (n : ℕ) :
    bpswWheel30ReducedEuler n true = bfwEnhancedBPSW n := by
  rw [bpswWheel30ReducedEuler_eq]
  exact strengthenedBPSWWheel30_eq_bfw n

/-- Signed wrapper for the conditional Wheel30 entry.
Negative integers return false before conversion; nonnegative integers use toNat.
This retains the signed-input behavior of the existing Wheel30 interface. -/
def bpswWheel30ReducedEulerInt (z : ℤ) (strengthened : Bool) : Bool :=
  if z < 0 then false else bpswWheel30ReducedEuler z.toNat strengthened

/-- For every integer and both modes, the conditional signed entry equals the existing one.
Rewrite the natural Boolean equality under the unchanged negative-input guard. -/
theorem bpswWheel30ReducedEulerInt_eq (z : ℤ) (strengthened : Bool) :
    bpswWheel30ReducedEulerInt z strengthened = bpswWheel30Int z strengthened := by
  simp only [bpswWheel30ReducedEulerInt, bpswWheel30ReducedEuler_eq, bpswWheel30Int]

/-- Certified conditional Wheel30 decision for a signed input, indexed by toNat.
Negative inputs are rejected; probable-prime acceptance remains unknown.
The existing signed prime-completeness contract transfers through Boolean equality. -/
def BPSW.decideWheel30ReducedEulerInt (z : ℤ) (strengthened : Bool := false) : Decision z.toNat :=
  decideByPrimePass z.toNat (bpswWheel30ReducedEulerInt z strengthened)
    (fun hp ↦
      (bpswWheel30ReducedEulerInt_eq z strengthened).trans
        (bpswWheel30Int_of_prime z strengthened hp))

/-- The conditional signed decision equals the existing signed decision for all inputs.
Boolean equality preserves both classification and the proof-carrying result index. -/
theorem BPSW.decideWheel30ReducedEulerInt_eq (z : ℤ) (strengthened : Bool) :
    decideWheel30ReducedEulerInt z strengthened = decideWheel30Int z strengthened := by
  simp only [decideWheel30ReducedEulerInt, bpswWheel30ReducedEulerInt_eq, decideWheel30Int,
    decideByPrimePass]

end PseudoPrime.PrimeTest
