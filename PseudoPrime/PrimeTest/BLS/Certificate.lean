/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PrimeTest.BLS.CubeCertificate
import PseudoPrime.PrimeTest.BLS.Extended
import PseudoPrime.PrimeTest.BLS.Result

/-!
# External BLS certificate verification
-/

namespace PseudoPrime.PrimeTest.BLS

/-- Untrusted BLS certificate data for a small prime or one of the three arithmetic methods.
Each constructor stores its own input. No primality proof is supplied by the caller;
the external verifier checks that input and every method-specific condition again. -/
inductive InputCertificate where
  | small (n : ℕ)
  | square (data : SquareCertificate)
  | cube (data : CubeCertificate)
  | bls5 (data : BLS5Certificate)

/-- Read the integer certified by the payload, before binding it to the caller's input. -/
def InputCertificate.input : InputCertificate → ℕ
  | .small n => n
  | .square c => c.n
  | .cube c => c.n
  | .bls5 c => c.n

/-- Recheck a certificate using the corresponding arithmetic verifier.
The small-input branch accepts exactly 2 and 3, without factor or witness searches. -/
def InputCertificate.check : InputCertificate → Bool
  | .small n => decide (n = 2 ∨ n = 3)
  | .square c => verifySquareCertificate c
  | .cube c => checkCubeCertificate c
  | .bls5 c => checkBLS5Certificate c

/-- A successful payload check proves its embedded input prime, by the existing
three BLS soundness theorems or the direct proofs for 2 and 3. -/
theorem InputCertificate.check_sound (c : InputCertificate) (h : c.check = true) :
    Nat.Prime c.input := by
  cases c with
  | small n =>
    obtain h | h := of_decide_eq_true h
    · exact h ▸ (by decide : Nat.Prime 2)
    · exact h ▸ (by decide : Nat.Prime 3)
  | square c => exact prime_of_valid_square_certificate c h
  | cube c => exact prime_of_valid_cube_certificate c h
  | bls5 c => exact prime_of_valid_bls5_certificate c h

/-- Verify an external certificate for the requested input.
Acceptance requires both input equality and the complete payload check. -/
def verifyInputCertificate (n : ℕ) (c : InputCertificate) : Bool :=
  decide (c.input = n) && c.check

/-- Acceptance is exactly input equality and successful payload verification. -/
theorem verifyInputCertificate_iff (n : ℕ) (c : InputCertificate) :
    verifyInputCertificate n c = true ↔ c.input = n ∧ c.check = true := by
  simp only [verifyInputCertificate, Bool.and_eq_true, decide_eq_true_eq]

/-- Every accepted external certificate proves the caller's requested integer prime. -/
theorem verifyInputCertificate_sound {n : ℕ} (c : InputCertificate)
    (h : verifyInputCertificate n c = true) : Nat.Prime n := by
  obtain ⟨hinput, hcheck⟩ := (verifyInputCertificate_iff n c).mp h
  exact hinput ▸ c.check_sound hcheck

/-- Return a proof-carrying result from an external certificate.
Inputs below 2 are invalid; a rejected or mismatched certificate gives only unknown. -/
def resultOfInputCertificate (n : ℕ) (c : InputCertificate) : BLSResult n :=
  if hinput : 1 < n then
    if h : verifyInputCertificate n c = true then .prime (verifyInputCertificate_sound c h)
    else .unknown
  else .invalidInput (Nat.not_lt.mp hinput)

/-- An accepted certificate reaches the prime branch of the public result consumer. -/
theorem resultOfInputCertificate_of_checked {n : ℕ} (c : InputCertificate)
    (h : verifyInputCertificate n c = true) :
    resultOfInputCertificate n c = .prime (verifyInputCertificate_sound c h) := by
  rw [resultOfInputCertificate, dite_eq_left (verifyInputCertificate_sound c h).one_lt,
    dite_eq_left h]

/-- Rejected certificates for inputs above 1 yield unknown rather than compositeness. -/
theorem resultOfInputCertificate_of_rejected {n : ℕ} (c : InputCertificate) (hn : 1 < n)
    (h : verifyInputCertificate n c = false) : resultOfInputCertificate n c = .unknown := by
  have hnot : verifyInputCertificate n c ≠ true := by
    intro ht
    exact Bool.noConfusion (h.symm.trans ht)
  rw [resultOfInputCertificate, dite_eq_left hn, dite_eq_right hnot]

/-- Inputs below the primality domain are reported separately from rejected certificates. -/
theorem resultOfInputCertificate_invalid {n : ℕ} (c : InputCertificate) (hn : n ≤ 1) :
    resultOfInputCertificate n c = .invalidInput hn := by
  rw [resultOfInputCertificate, dite_eq_right (Nat.not_lt.mpr hn)]

end PseudoPrime.PrimeTest.BLS
