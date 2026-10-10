/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.Selfridge.Scan
public import PseudoPrime.PrimeTest.StrongLucas.Fast

/-! # Unconditional factor-detecting BPSW execution

The new entries consume certified finite Selfridge search outcomes.
The existing classical Boolean APIs retain their all-input equality contracts.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/-- Evaluate selected Lucas parameters; factors and exhausted search return false.
The strengthened flag chooses the shared Strong, V, and Euler conditions.
Only the unconditional-budget wrapper uses exhaustion as a Boolean rejection. -/
def SelfridgeScanResult.accepted {n : ℕ} (strengthened : Bool) : SelfridgeScanResult n → Bool
  | .exhausted => false
  | .factor _ _ _ _ => false
  | .selected param _ =>
    if strengthened then strengthenedLucasSharedEulerValid n param
    else strongLucasWithParamsFast n param.D param.P param.Q

/-- Evaluate certified selected parameters at an odd modulus without retesting Jacobi of D.
The strengthened flag chooses the unguarded shared Euler core; ordinary execution uses PQ.
Factors and exhausted searches remain false. -/
def SelfridgeScanResult.acceptedOdd {n : ℕ} (_hn : Odd n) (strengthened : Bool) :
    SelfridgeScanResult n → Bool
  | .exhausted => false
  | .factor _ _ _ _ => false
  | .selected param _ =>
    if strengthened then strengthenedLucasSharedEulerCore n param
    else strongLucasWithPQ n param.P param.Q

/-- Odd-input acceptance agrees with the total selected-parameter evaluator.
The stored Jacobi evidence identifies both raw-core branches with their guarded versions. -/
theorem SelfridgeScanResult.acceptedOdd_eq {n : ℕ} (hn : Odd n) (strengthened : Bool)
    (result : SelfridgeScanResult n) :
    result.acceptedOdd hn strengthened = result.accepted strengthened := by
  cases result with
  | exhausted => rfl
  | factor g hl hu hd => rfl
  | selected param hj =>
    cases strengthened
    · simp only [SelfridgeScanResult.acceptedOdd, SelfridgeScanResult.accepted, Bool.false_eq_true,
        ↓reduceIte, strongLucasWithParamsFast, ite_eq_left (And.intro hn hj)]
    · simp only [SelfridgeScanResult.acceptedOdd, SelfridgeScanResult.accepted, ↓reduceIte,
        strengthenedLucasSharedEulerCore_eq n hn param hj]

/-- A completed search outcome accepts every prime input.
A proper factor contradicts primality.
Selected parameters use the corresponding prime-pass theorem. -/
theorem SelfridgeScanResult.accepted_of_prime {n : ℕ} (hp : n.Prime) (strengthened : Bool)
    (result : SelfridgeScanResult n) (h : result.hasStop = true) :
    result.accepted strengthened = true := by
  cases result with
  | exhausted => exact False.elim (Bool.false_ne_true h)
  | factor g hl hu hd => exact False.elim (Nat.not_prime_of_dvd_of_lt hd hl hu hp)
  | selected param hj =>
    cases strengthened
    · exact strongLucasWithParamsFast_of_prime hp _ _ _ param.discr hj
    · exact strengthenedLucasSharedEulerValid_of_prime hp param hj

/-- Run MR first, then square checking and factor-detecting Wheel30-filtered search.
Small and even inputs retain the conventional Boolean answers.
The unconditional budget completes every odd nonsquare search; no GRH is used. -/
def bpswWheel30 (n : ℕ) (strengthened : Bool) : Bool :=
  if n < 2 then false
  else
    if n = 2 then true
    else
      if he : Even n then false
      else
        if strongMillerRabinWithBaseLoop n 2 then
          if natIsSquare n then false
          else
            (selfridgeNeOneResult n (2 * n)).acceptedOdd (Nat.not_even_iff_odd.mp he) strengthened
        else false

/-- Every prime passes the finite MR-first factor-detecting composition.
The unconditional stop theorem prevents budget exhaustion in the odd-prime branch. -/
theorem bpswWheel30_of_prime {n : ℕ} (hp : n.Prime) (strengthened : Bool) :
    bpswWheel30 n strengthened = true := by
  by_cases ht : n = 2
  · subst n
    rfl
  · have ho : Odd n := hp.odd_of_ne_two ht
    have hl : ¬n < 2 := Nat.not_lt_of_ge hp.two_le
    have he : ¬Even n := Nat.not_even_iff_odd.mpr ho
    have hm : strongMillerRabinWithBaseLoop n 2 = true :=
      (strongMillerRabinWithBaseLoop_eq _ _).trans
        (strongMillerRabinWithBase_of_prime hp (Nat.coprime_two_left.mpr ho))
    simp only [bpswWheel30, hl, ht, he, hm, ↓reduceIte,
      natIsSquare_false_of_not_isSquare hp.not_isSquare, Bool.false_eq_true,
      SelfridgeScanResult.acceptedOdd_eq]
    exact
      SelfridgeScanResult.accepted_of_prime hp strengthened _
        (selfridgeNeOneResult_total ho hp.not_isSquare)

/-- The new finite factor-detecting composition satisfies the public primality-test contract.
Small and even cases reduce directly, and prime acceptance uses unconditional search termination. -/
theorem bpswWheel30_spec (strengthened : Bool) :
    PrimalityTestSpec (fun n ↦ bpswWheel30 n strengthened) := by
  constructor
  · rfl
  · rfl
  · rfl
  · intro n ht he
    by_cases hl : n < 2
    · simp only [bpswWheel30, hl, ↓reduceIte]
    · simp only [bpswWheel30, hl, ht, he, ↓reduceIte, ↓reduceDIte]
  · exact fun hp ↦ bpswWheel30_of_prime hp strengthened

/-- Ordinary MR-first BPSW with finite factor-detecting Wheel30-filtered search.
The selected Method A* parameters use the three-component Strong Lucas evaluator. -/
def bailliePSWWheel30 (n : ℕ) : Bool :=
  bpswWheel30 n false

/--
Strengthened MR-first BPSW with an unconditional 2*n magnitude budget for the
factor-detecting Wheel30 Selfridge search. Selected Method A* parameters use shared
Strong, terminal V and the gcd-free multiplied Euler comparison on odd Jacobi -1 inputs;
the total evaluator retains its fallback elsewhere. A Boolean pass remains probable primality.
-/
def strengthenedBPSWWheel30 (n : ℕ) : Bool :=
  bpswWheel30 n true

/-- Ordinary factor-detecting BPSW satisfies the unconditional primality-test contract.
This is prime completeness, rather than equality with the classical pure-minus-one test. -/
theorem bailliePSWWheel30_spec : PrimalityTestSpec bailliePSWWheel30 :=
  bpswWheel30_spec false

/-- Strengthened factor-detecting BPSW satisfies the unconditional primality-test contract.
The shared Euler fallback retains the selected-parameter semantics for all inputs. -/
theorem strengthenedBPSWWheel30_spec : PrimalityTestSpec strengthenedBPSWWheel30 :=
  bpswWheel30_spec true

/-- Convert the unconditional ordinary or strengthened Wheel30 test into a certified decision.
Boolean rejection proves non-primality; acceptance remains unknown.
Use decideWheel30Within when a caller supplies a possibly insufficient search budget. -/
def BPSW.decideWheel30 (n : ℕ) (strengthened : Bool := false) : Decision n :=
  decideByTest (fun n ↦ bpswWheel30 n strengthened) (bpswWheel30_spec strengthened) n

/-- Ordinary or strengthened BPSW for signed inputs. Negative values return false
before conversion; nonnegative values use the unconditional Wheel30 evaluator. -/
def bpswWheel30Int (z : ℤ) (strengthened : Bool) : Bool :=
  if z < 0 then false else bpswWheel30 z.toNat strengthened

/-- The signed wrapper agrees with evaluation at toNat on every integer.
For negative inputs, toNat is zero and the natural evaluator rejects zero. -/
theorem bpswWheel30Int_eq (z : ℤ) (strengthened : Bool) :
    bpswWheel30Int z strengthened = bpswWheel30 z.toNat strengthened := by
  by_cases h : z < 0
  · rw [bpswWheel30Int, ite_eq_left h, Int.toNat_of_nonpos (Int.le_of_lt h)]
    rfl
  · rw [bpswWheel30Int, ite_eq_right h]

/-- Negative signed inputs are rejected directly, without running the natural test. -/
theorem bpswWheel30Int_negative (z : ℤ) (strengthened : Bool) (h : z < 0) :
    bpswWheel30Int z strengthened = false := by rw [bpswWheel30Int, ite_eq_left h]

/-- Natural inputs embedded in the integers retain their original Boolean result. -/
theorem bpswWheel30Int_nat (n : ℕ) (strengthened : Bool) :
    bpswWheel30Int (n : ℤ) strengthened = bpswWheel30 n strengthened := by
  rw [bpswWheel30Int_eq, Int.toNat_natCast]

/-- A prime represented by the signed input passes either BPSW variant.
The all-input wrapper equality transports natural prime completeness. -/
theorem bpswWheel30Int_of_prime (z : ℤ) (strengthened : Bool) (hp : z.toNat.Prime) :
    bpswWheel30Int z strengthened = true := by
  rw [bpswWheel30Int_eq]
  exact bpswWheel30_of_prime hp strengthened

/-- Rejection certifies that the nonnegative interpretation is not prime.
Acceptance remains a probable-prime result and supplies no primality proof. -/
theorem bpswWheel30Int_not_prime_of_false (z : ℤ) (strengthened : Bool)
    (h : bpswWheel30Int z strengthened = false) : ¬z.toNat.Prime := by
  rw [bpswWheel30Int_eq] at h
  exact (bpswWheel30_spec strengthened).not_prime_of_false h

/-- Produce a certified one-sided decision for a signed input, indexed by toNat.
Negative inputs are rejected; acceptance remains unknown for downstream searches. -/
def BPSW.decideWheel30Int (z : ℤ) (strengthened : Bool := false) : Decision z.toNat :=
  decideByPrimePass z.toNat (bpswWheel30Int z strengthened) (bpswWheel30Int_of_prime z strengthened)

/-- The signed decision preserves the natural decision at toNat, including unknown.
Proof irrelevance identifies the rejection evidence after Boolean equality. -/
theorem BPSW.decideWheel30Int_eq (z : ℤ) (strengthened : Bool) :
    decideWheel30Int z strengthened = decideWheel30 z.toNat strengthened := by
  simp only [decideWheel30Int, bpswWheel30Int_eq, decideWheel30, decideByPrimePass, decideByTest]

/-- Run the common small-input, parity, and square precheck before MR and Wheel30 search.
The selected-parameter computation and unconditional search budget match bpswWheel30.
Squares are rejected before modular exponentiation; other odd inputs pay for sqrt first. -/
def bpswWheel30WithPrecheck (n : ℕ) (strengthened : Bool) : Bool :=
  match primalityPrecheck n with
  | some result => result
  | none =>
    if strongMillerRabinWithBaseLoop n 2 then (selfridgeNeOneResult n (2 * n)).accepted strengthened
    else false

/-- Moving the common precheck ahead of MR preserves both Boolean modes on every input.
Case analysis on the guards shows that only the order of rejection changes. -/
theorem bpswWheel30WithPrecheck_eq (n : ℕ) (strengthened : Bool) :
    bpswWheel30WithPrecheck n strengthened = bpswWheel30 n strengthened := by
  simp only [bpswWheel30WithPrecheck, primalityPrecheck, bpswWheel30,
    SelfridgeScanResult.acceptedOdd_eq]
  split_ifs <;> rfl

/-- The precheck-first Wheel30 test inherits unconditional prime completeness and small answers.
The all-input equality transfers the existing specification without new number theory. -/
theorem bpswWheel30WithPrecheck_spec (strengthened : Bool) :
    PrimalityTestSpec (fun n ↦ bpswWheel30WithPrecheck n strengthened) :=
  Eq.mpr (congrArg PrimalityTestSpec (funext (fun n ↦ bpswWheel30WithPrecheck_eq n strengthened)))
    (bpswWheel30_spec strengthened)

/-- Ordinary BPSW with the common precheck before MR and factor-detecting Wheel30 search. -/
def bailliePSWWheel30WithPrecheck (n : ℕ) : Bool :=
  bpswWheel30WithPrecheck n false

/-- Strengthened BPSW with the common precheck before MR and shared Lucas evaluation. -/
def strengthenedBPSWWheel30WithPrecheck (n : ℕ) : Bool :=
  bpswWheel30WithPrecheck n true

/-- Ordinary precheck-first Wheel30 BPSW satisfies the public primality-test contract. -/
theorem bailliePSWWheel30WithPrecheck_spec : PrimalityTestSpec bailliePSWWheel30WithPrecheck :=
  bpswWheel30WithPrecheck_spec false

/-- Strengthened precheck-first Wheel30 BPSW satisfies the public primality-test contract. -/
theorem strengthenedBPSWWheel30WithPrecheck_spec :
    PrimalityTestSpec strengthenedBPSWWheel30WithPrecheck :=
  bpswWheel30WithPrecheck_spec true

/-- Produce a certified decision using the common precheck before Wheel30 execution.
Rejection certifies non-primality, while acceptance remains unknown. -/
def BPSW.decideWheel30WithPrecheck (n : ℕ) (strengthened : Bool := false) : Decision n :=
  decideByTest (fun n ↦ bpswWheel30WithPrecheck n strengthened)
    (bpswWheel30WithPrecheck_spec strengthened) n

/-- Reordering the square check preserves every certified natural-input decision. -/
theorem BPSW.decideWheel30WithPrecheck_eq (n : ℕ) (strengthened : Bool) :
    decideWheel30WithPrecheck n strengthened = decideWheel30 n strengthened :=
  decideByTest_congr (bpswWheel30WithPrecheck_spec strengthened) (bpswWheel30_spec strengthened)
    (funext (fun n ↦ bpswWheel30WithPrecheck_eq n strengthened)) n

end PseudoPrime.PrimeTest
