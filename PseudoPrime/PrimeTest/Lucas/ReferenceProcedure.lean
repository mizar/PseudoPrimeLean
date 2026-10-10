/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.StrongLucas.NoGcd

/-! # Signed halving and leading-one reference Lucas procedure -/

@[expose] public section

namespace PseudoPrime.PrimeTest

/-- Halve a signed numerator by parity adjustment before reducing modulo n.
For odd n, x + (x mod 2)*n is even, including negative x; the result feeds reference increments. -/
def lucasSignedHalf (n : ℕ) (x : ℤ) : ZMod n :=
  (((x + (x % 2) * (n : ℤ)) / 2 : ℤ) : ZMod n)

/-- An odd modulus makes the raw parity-adjusted numerator exactly divisible by two.
The quotient/remainder decomposition of x provides an explicit integer factor. -/
theorem signedAdjusted_even (n : ℕ) (hn : Odd n) (x : ℤ) : 2 ∣ x + (x % 2) * (n : ℤ) := by
  obtain ⟨k, hk⟩ := hn
  refine ⟨x / 2 + (x % 2) * (k + 1 : ℤ), ?_⟩
  rw [hk, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  calc
    _ = (x / 2 * 2 + x % 2) + (x % 2) * (2 * (k : ℤ) + 1) :=
      congrArg (fun y ↦ y + (x % 2) * (2 * (k : ℤ) + 1)) (Int.ediv_mul_add_emod x 2).symm
    _ = _ := by ring

/-- Truncating and Euclidean division agree on the adjusted numerator.
Exact divisibility covers negative numerators, connecting C++ division to the Python half. -/
theorem signedHalf_division_modes (n : ℕ) (hn : Odd n) (x : ℤ) :
    (x + (x % 2) * (n : ℤ)).tdiv 2 = (x + (x % 2) * (n : ℤ)) / 2 :=
  Int.tdiv_eq_ediv_of_dvd (signedAdjusted_even n hn x)

/-- Twice the raw signed half recovers the original residue at every odd modulus.
Cast exact integer division and discard the multiple of the modulus; n=1 is included. -/
theorem signedHalf_twice (n : ℕ) (hn : Odd n) (x : ℤ) : 2 * lucasSignedHalf n x = (x : ZMod n) := by
  have hc := congrArg (fun y : ℤ ↦ (y : ZMod n)) (Int.mul_ediv_cancel' (signedAdjusted_even n hn x))
  simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_add, Int.cast_natCast, ZMod.natCast_self,
    mul_zero, add_zero] at hc
  exact hc

/-- Raw signed halving and the production residue-first half agree for odd moduli.
Cancel multiplication by two to transport the exact numerator identity. -/
theorem signedHalf_eq (n : ℕ) (hn : Odd n) (x : ℤ) :
    lucasSignedHalf n x = lucasModHalfExec n (x : ZMod n) := by
  rw [lucasModHalfExec_eq]
  have h := congrArg (lucasModHalf n) (signedHalf_twice n hn x)
  rw [lucasModHalf_twice n hn] at h
  exact h

/-- Increment U, V, and Q using raw signed numerators from canonical state residues.
Both half formulas use the old state and signed P, Q; normalization follows halving. -/
def lucasSignedIncrement (n : ℕ) (P Q : ℤ) (x : LucasUVQState n) : LucasUVQState n :=
  ⟨lucasSignedHalf n (P * (x.u.val : ℤ) + x.v.val),
    lucasSignedHalf n ((P * P - 4 * Q) * (x.u.val : ℤ) + P * (x.v.val : ℤ)), x.qk * (Q : ZMod n)⟩

/-- The raw signed increment equals the production triple increment for odd n.
The half bridge and canonical-residue cast identities identify all components. -/
theorem signedIncrement_eq (n : ℕ) (hn : Odd n) (P Q : ℤ) (x : LucasUVQState n) :
    lucasSignedIncrement n P Q x = lucasUVQIncrement n P Q x := by
  let : NeZero n := ⟨Nat.ne_of_gt hn.pos⟩
  apply LucasUVQState.ext
  · simp only [lucasSignedIncrement, lucasUVQIncrement, signedHalf_eq n hn, Int.cast_add,
      Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  · simp only [lucasSignedIncrement, lucasUVQIncrement, signedHalf_eq n hn, Int.cast_add,
      Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_sub, Int.cast_ofNat]
  · rfl

/-- Process one remaining binary digit after initializing the leading one.
Double the triple, then use the raw signed increment only for a one digit. -/
def lucasLeadingBit (n : ℕ) (P Q : ℤ) (b : Bool) (x : LucasUVQState n) : LucasUVQState n :=
  let y := lucasUVQDouble n x
  if b then lucasSignedIncrement n P Q y else y

/-- The reference digit step agrees with the production digit step on odd moduli.
The signed increment bridge identifies the only operational difference. -/
theorem leadingBit_eq (n : ℕ) (hn : Odd n) (P Q : ℤ) (b : Bool) (x : LucasUVQState n) :
    lucasLeadingBit n P Q b x = lucasUVQBit n P Q b x := by
  simp only [lucasLeadingBit, lucasUVQBit, signedIncrement_eq n hn]

/-- Evaluate Lucas triples from the leading-one state (1,P,Q).
Exponent zero returns (0,2,1); positive exponents process only the remaining binary digits.
This executable reference model supports correspondence with the C++/Python procedure. -/
def lucasUVQLeading (n : ℕ) (P Q : ℤ) (k : ℕ) : LucasUVQState n :=
  Nat.binaryRecFromOne (motive := fun _ ↦ LucasUVQState n) ⟨0, 2, 1⟩ ⟨1, P, Q⟩
    (fun b _ _ x ↦ lucasLeadingBit n P Q b x) k

/-- The explicit leading-one state represents U_1, V_1, Q^1 at every modulus.
The Lucas initial values identify the triple without performing a digit update. -/
theorem leadingOne_spec (n : ℕ) (P Q : ℤ) :
    (⟨1, P, Q⟩ : LucasUVQState n) = lucasUVQSpec n P Q 1 := by
  simp only [lucasUVQSpec, lucasUZMod, lucasVZMod, lucasU_one, lucasV_one, lucasQPow, pow_one,
    Int.cast_one]

/-- Leading-one and zero-prefix initialization agree for all exponents at odd moduli.
Binary induction separates exponents zero and one before transporting the remaining digits. -/
theorem leading_eq (n : ℕ) (hn : Odd n) (P Q : ℤ) (k : ℕ) :
    lucasUVQLeading n P Q k = lucasUVQ n P Q k := by
  rw [lucasUVQ_eq n hn]
  induction k using Nat.binaryRec' with
  | zero =>
    rw [lucasUVQLeading, Nat.binaryRecFromOne_zero, ← lucasUVQ_zero]; rfl
  | bit b k hk ih =>
    by_cases hz : k = 0
    · subst k
      have hb := hk rfl
      subst b
      rw [Nat.bit_true_apply, Nat.mul_zero, Nat.zero_add, lucasUVQLeading, Nat.binaryRecFromOne_one,
        leadingOne_spec]
    · rw [lucasUVQLeading, Nat.binaryRecFromOne_eq b k hz]
      change lucasLeadingBit n P Q b (lucasUVQLeading n P Q k) = _
      rw [ih, leadingBit_eq n hn, lucasUVQBit_spec n hn]

/-- Run the ordinary Strong scan with the leading-one reference initializer.
Odd inputs use the triple model; other inputs retain the existing total fallback. -/
def strongLucasLeading (n : ℕ) (D P Q : ℤ) : Bool :=
  if Odd n then
    let x := lucasUVQLeading n P Q (strongLucasOddPart n D)
    (x.u == 0) || lucasVScan n x.v x.qk (strongLucasTwoAdicExponent n D)
  else strongLucasWithParamsLoop n D P Q

/-- Reference initialization preserves the production ordinary Strong Boolean for all inputs.
The odd branch uses the triple equality and the other branch is unchanged. -/
theorem strongLucasLeading_eq (n : ℕ) (D P Q : ℤ) :
    strongLucasLeading n D P Q = strongLucasWithParamsUVQ n D P Q := by
  by_cases hn : Odd n
  · simp only [strongLucasLeading, strongLucasWithParamsUVQ, ite_eq_left hn, leading_eq n hn]
  · simp only [strongLucasLeading, strongLucasWithParamsUVQ, ite_eq_right hn]

/-- Obtain the shared Strong flag, terminal V, and half-index Q from the reference initializer.
The production terminal scan consumes the leading-one triple and preserves its index conventions. -/
def lucasStrengthenedLeadingState (n : ℕ) (D P Q : ℤ) : LucasStrengthenedState n :=
  let x := lucasUVQLeading n P Q (strongLucasOddPart n D)
  lucasStrengthenedScan n x.v x.qk (x.u == 0) (strongLucasTwoAdicExponent n D)

/-- On odd moduli, reference initialization preserves the complete shared terminal state.
Triple equality transports all three downstream fields simultaneously. -/
theorem strengthenedLeadingState_eq (n : ℕ) (hn : Odd n) (D P Q : ℤ) :
    lucasStrengthenedLeadingState n D P Q = lucasStrengthenedState n D P Q := by
  simp only [lucasStrengthenedLeadingState, lucasStrengthenedState, leading_eq n hn]

/-- Reference strengthened evaluation for proof-carrying Lucas parameters.
Odd Jacobi -1 inputs compare Strong, terminal V, and multiplied Euler; other inputs use fallback. -/
def strengthenedLucasLeadingValid (n : ℕ) (param : LucasParams) : Bool :=
  if Odd n ∧ jacobiSym param.D n = -1 then
    let x := lucasStrengthenedLeadingState n param.D param.P param.Q
    x.strongOk &&
      ((x.v == 2 * (param.Q : ZMod n)) &&
        (x.qk == (param.Q : ZMod n) * (jacobiSym param.Q n : ZMod n)))
  else strengthenedLucasSharedEuler n param.D param.P param.Q

/-- The reference valid-parameter evaluator equals the gcd-free production evaluator on all inputs.
Eligible inputs use the full terminal-state equality; ineligible inputs share their fallback. -/
theorem strengthenedLucasLeadingValid_eq (n : ℕ) (param : LucasParams) :
    strengthenedLucasLeadingValid n param = strengthenedLucasSharedEulerValid n param := by
  by_cases hg : Odd n ∧ jacobiSym param.D n = -1
  · simp only [strengthenedLucasLeadingValid, strengthenedLucasSharedEulerValid, ite_eq_left hg,
      strengthenedLeadingState_eq n hg.1]
  · simp only [strengthenedLucasLeadingValid, strengthenedLucasSharedEulerValid, ite_eq_right hg]

/-- Arithmetic right shift of the adjusted integer equals the raw half at every modulus.
The shift/division identity models Python's shift before residue normalization. -/
theorem signedHalf_shift (n : ℕ) (x : ℤ) :
    (((x + (x % 2) * (n : ℤ)) >>> 1 : ℤ) : ZMod n) = lucasSignedHalf n x := by
  simp only [Int.shiftRight_eq_div_pow, pow_one, Nat.cast_ofNat, lucasSignedHalf]

/-- Adding the modulus exactly for an odd numerator equals multiplication by its parity residue.
The integer remainder modulo two is zero or one, including negative inputs. -/
theorem signedParity_adjust (n : ℕ) (x : ℤ) :
    x + (if x % 2 = 0 then 0 else (n : ℤ)) = x + (x % 2) * (n : ℤ) := by
  rcases Int.emod_two_eq_zero_or_one x with h | h
  · simp only [h, ↓reduceIte, zero_mul]
  · simp only [h, Int.one_ne_zero, ↓reduceIte, one_mul]

/-- The ordinary reference procedure agrees with the original fixed-parameter Strong test.
Compose the initializer bridge with the existing production correctness contract. -/
theorem strongLucasLeading_eq_original (n : ℕ) (D P Q : ℤ) :
    strongLucasLeading n D P Q = strongLucasWithParams n D P Q :=
  (strongLucasLeading_eq n D P Q).trans (strongLucasWithParamsUVQ_eq n D P Q)

/-- The strengthened reference procedure agrees with the original guarded shared evaluator.
Compose the reference-state and valid-parameter gcd-removal bridges for downstream consumers. -/
theorem strengthenedLucasLeadingValid_eq_original (n : ℕ) (param : LucasParams) :
    strengthenedLucasLeadingValid n param =
      strengthenedLucasSharedEuler n param.D param.P param.Q :=
  (strengthenedLucasLeadingValid_eq n param).trans (strengthenedLucasSharedEulerValid_eq n param)

end PseudoPrime.PrimeTest
