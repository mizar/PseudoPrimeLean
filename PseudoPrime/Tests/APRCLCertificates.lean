/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.APRCL.Certificate

/-!
# APR-CL certificate replay regressions
Finite acceptance is tested without asserting the unproved local mathematical kernel.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest.APRCL.CertificateTests

/-- Small replay limits and a two-proposal search prefix. -/
def limits : CertificateLimits :=
  ⟨⟨32, 4, 16, 8⟩, 12, 2⟩

/-- Required low two-adic row for t=2. -/
def mainRows : List RawPairData :=
  [⟨2, 0, 3, 0⟩]

/-- A proposal whose required row alone need not establish the flag. -/
def plain : CertificateCandidate :=
  ⟨2, mainRows, []⟩

/-- An additional q=7 flag witness for n=13, outside the t=2 modulus. -/
def extended : CertificateCandidate :=
  ⟨2, mainRows, [⟨2, 0, 7, 0⟩]⟩

/-- Exercise full replay, malformed roles, input agreement and bounded generation. -/
def run : IO Unit := do
  unless verifyRawCertificate 5 limits (plain.bind 5) do
    throw (IO.userError "plain certificate rejected")
  unless verifyRawCertificate 13 limits (extended.bind 13) do
    throw (IO.userError "extra flag certificate rejected")
  for c in
    ([⟨5, 2, mainRows, []⟩, ⟨13, 2, [], extended.extra⟩, ⟨13, 2, mainRows, []⟩,
        ⟨13, 2, mainRows, [⟨2, 0, 3, 0⟩]⟩, ⟨13, 2, mainRows, [⟨2, 0, 7, 0⟩, ⟨2, 0, 11, 0⟩]⟩,
        ⟨13, 2, mainRows, [⟨3, 0, 7, 3⟩]⟩, ⟨13, 2, mainRows, [⟨2, 0, 23, 0⟩]⟩,
        ⟨13, 2, mainRows ++ extended.extra, []⟩, ⟨13, 0, mainRows, []⟩, ⟨13, 3, mainRows, []⟩,
        ⟨13, 1000000000, mainRows, []⟩] :
      List RawCertificate) do
    if verifyRawCertificate 13 limits c then
      throw (IO.userError "invalid certificate accepted")
  for n in [0, 1, 2, 3, 4, 7, 9, 25, 325, 577] do
    if verifyRawCertificate n limits (plain.bind n) then
      throw (IO.userError s!"unexpected acceptance: {n}")
  unless (powerDivisorScanLoopEarly 325 (modulus 2) 2).isSome do
    throw (IO.userError "proper divisor scan missed")
  if verifyRawCertificate 13 { limits with pairs := ⟨32, 4, 16, 1⟩ } (extended.bind 13) then
    throw (IO.userError "combined row count bypassed")
  let some c := generateRawCertificate 13 limits [plain, extended]
    | throw (IO.userError "bounded generation failed")
  unless c.n == 13 && c.t == 2 && verifyRawCertificate 13 limits c do
    throw (IO.userError "generation not bound to input")
  for cap in [0, 1] do
    unless
      (generateRawCertificate 13 { limits with maxCandidates := cap } [plain, extended]).isNone do
      throw (IO.userError "candidate prefix bypassed")
  unless (generateRawCertificate 13 limits []).isNone do
    throw (IO.userError "empty search succeeded")

end PseudoPrime.PrimeTest.APRCL.CertificateTests

/-- Run all certificate replay regressions. -/
def main : IO Unit :=
  PseudoPrime.PrimeTest.APRCL.CertificateTests.run
