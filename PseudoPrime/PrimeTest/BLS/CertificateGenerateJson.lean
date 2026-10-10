/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.BLS.CertificateJson
public import PseudoPrime.PrimeTest.BLS.CertificateGenerate

/-! # JSON encoding of generated BLS certificates -/

@[expose] public section

namespace PseudoPrime.PrimeTest.BLS

/-- Generate, encode, and independently recheck a bounded BLS candidate.
Return none on any failure; this makes no unconditional search-completeness claim. -/
def generateCertificateJson (n : ℕ) (method : CertificateMethod)
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) (bases : List ℕ) :
    Option Lean.Json :=
  ((generateInputCertificate n method params fuel bases).map encodeInputCertificate).filter
    (verifyCertificateJson n)

/-- Every generated JSON payload passes the same public JSON verifier. -/
theorem generateCertificateJson_checked {n : ℕ} {method : CertificateMethod}
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ} {bases : List ℕ}
    {j : Lean.Json} (h : generateCertificateJson n method params fuel bases = some j) :
    verifyCertificateJson n j = true := by exact (Option.filter_eq_some_iff.mp h).2

/-- Successful JSON certificate generation proves the original input prime. -/
theorem generateCertificateJson_sound {n : ℕ} {method : CertificateMethod}
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ} {bases : List ℕ}
    {j : Lean.Json} (h : generateCertificateJson n method params fuel bases = some j) :
    Nat.Prime n := by exact verifyCertificateJson_sound j (generateCertificateJson_checked h)

end PseudoPrime.PrimeTest.BLS
