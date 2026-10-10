/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.SmallInputJson

/-!
# Small-input certificate regressions
Test proof-carrying decisions, corruption and independently chosen verifier limits.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest.SmallInput.JsonTests

/-- Exercise accepted prime/nonprime claims and rejected mutations. -/
def run : IO Unit := do
  for n in List.range 101 do
    match h : generateCertificateText n 100 1024 with
    | none =>
      throw (IO.userError "in-range generation failed")
    | some text =>
      unless verifyCertificateText n 100 1024 text do
        throw (IO.userError "text replay failed")
      let checked :=
        resultOfVerifiedCertificateText n 100 1024 text (generateCertificateText_checked h)
      unless checked.toOption == (resultOfCertificateText n 100 1024 text).toOption do
        throw (IO.userError "verified decision differs from replay")
      match checked with
      | .unknown =>
        throw (IO.userError "accepted decision lost")
      | .prime _ =>
        unless decide (Nat.Prime n) do
          throw (IO.userError "prime decision mismatch")
      | .notPrime _ =>
        if decide (Nat.Prime n) then
          throw (IO.userError "nonprime decision mismatch")
  let valid := (encodeCertificate ⟨7, true⟩).compress
  for bad in
    [valid.replace "true" "false", valid.replace "\"7\"" "\"9\"", valid.replace "\"7\"" "7", "{}",
      "{"] do
    if verifyCertificateText 7 100 1024 bad then
      throw (IO.userError "tampered certificate accepted")
  unless verifyCertificateText 7 7 valid.utf8ByteSize valid do
    throw (IO.userError "exact boundaries rejected")
  if
      verifyCertificateText 7 6 1024 valid ||
        verifyCertificateText 7 100 (valid.utf8ByteSize - 1) valid then
    throw (IO.userError "limits bypassed")
  unless
    (generateCertificateText 101 100 1024).isNone && (generateCertificateText 7 100 0).isNone do
    throw (IO.userError "generation limit bypassed")

end PseudoPrime.PrimeTest.SmallInput.JsonTests

/-- Run the small-input JSON regressions. -/
def main : IO Unit :=
  PseudoPrime.PrimeTest.SmallInput.JsonTests.run
