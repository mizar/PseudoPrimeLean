/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PrimeTest.BLS.Certificate
import PseudoPrime.PrimeTest.BLS.Search

/-!
# External BLS certificate generation
-/

namespace PseudoPrime.PrimeTest.BLS

/-- Select one of the three BLS size and arithmetic criteria for bounded generation. -/
inductive CertificateMethod where
  | square | cube | bls5
/-- Generate a candidate using retained-factor supply and the requested method.
Inputs below 2 return none; 2 and 3 bypass both factor and witness searches.
The fuel bounds the existing factor search, not total execution time. -/
def proposeInputCertificate (n : ℕ) (method : CertificateMethod)
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ) :
    Option InputCertificate :=
  if n < 2 then none
  else if n = 2 ∨ n = 3 then some (.small n)
  else match method with
    | .square => (findSquareCertificateFromRetainedSupply n params fuel bases).map .square
    | .cube => (findCubeCertificate n params fuel bases).map .cube
    | .bls5 => (findBLS5Certificate n params fuel bases).map .bls5
/-- Generate and recheck a certificate for the requested input and finite search data.
Failure returns none and does not establish non-primality. -/
def generateInputCertificate (n : ℕ) (method : CertificateMethod)
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ) :
    Option InputCertificate :=
  (proposeInputCertificate n method params fuel bases).filter (verifyInputCertificate n)
/-- Every generated certificate passes the external verifier, including input equality. -/
theorem generateInputCertificate_checked {n : ℕ} {method : CertificateMethod}
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ} {bases : List ℕ}
    {c : InputCertificate} (h : generateInputCertificate n method params fuel bases = some c) :
    verifyInputCertificate n c = true := by
  exact (Option.filter_eq_some_iff.mp h).2
/-- Successful bounded generation proves the original input prime. -/
theorem generateInputCertificate_sound {n : ℕ} {method : CertificateMethod}
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ} {bases : List ℕ}
    {c : InputCertificate} (h : generateInputCertificate n method params fuel bases = some c) :
    Nat.Prime n := by
  exact verifyInputCertificate_sound c (generateInputCertificate_checked h)
/-- The prime 2 has a direct certificate for every method, even with no search budget. -/
theorem generateInputCertificate_two (method : CertificateMethod)
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ) :
    generateInputCertificate 2 method params fuel bases = some (.small 2) := by
  rfl
/-- The prime 3 has a direct certificate for every method, even with no search budget. -/
theorem generateInputCertificate_three (method : CertificateMethod)
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ) :
    generateInputCertificate 3 method params fuel bases = some (.small 3) := by
  rfl
/-- Successful generation feeds its certificate to the public proof-carrying prime result. -/
theorem generateInputCertificate_result {n : ℕ} {method : CertificateMethod}
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ} {bases : List ℕ}
    {c : InputCertificate} (h : generateInputCertificate n method params fuel bases = some c) :
    resultOfInputCertificate n c = .prime (generateInputCertificate_sound h) := by
  exact resultOfInputCertificate_of_checked c (generateInputCertificate_checked h)

/-- Inputs 0 and 1 do not enter the factor or witness searches. -/
theorem generateInputCertificate_invalid {n : ℕ} (method : CertificateMethod)
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ) (hn : n < 2)
        :
    generateInputCertificate n method params fuel bases = none := by
  rw [generateInputCertificate, proposeInputCertificate.eq_def, ite_eq_left hn]
  rfl

end PseudoPrime.PrimeTest.BLS
