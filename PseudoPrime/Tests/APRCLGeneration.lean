/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.APRCL.Generate

/-!
# Automatic APR-CL generation regressions
These tests check finite construction and replay, not the missing local kernel.
-/

namespace PseudoPrime.PrimeTest.APRCL.GenerationTests

/-- Limits for small bounded generation tests. -/
def limits : CertificateLimits :=
  ⟨⟨32, 4, 16, 8⟩, 12, 2⟩

/-- Exercise successful generation, root search and independent budget failures. -/
def run : IO Unit := do
  for key in ([(2, 0, 3), (3, 0, 7), (2, 1, 5), (2, 3, 17)] : List (ℕ × ℕ × ℕ)) do
    let some row := constructRawRow 19 limits.pairs 32 key
      | throw (IO.userError "automatic root construction failed")
    unless (row.p, row.k, row.q) == key && (decodePairInput 19 limits.pairs row).isSome do
      throw (IO.userError "constructed row changed key or failed replay")
  unless (constructRawRow 19 limits.pairs 2 (2, 1, 5)).isNone do
    throw (IO.userError "root prefix ignored")
  unless (constructRawRow 19 limits.pairs 3 (2, 1, 5)).isSome do
    throw (IO.userError "root prefix boundary rejected")
  unless (constructRawRow 19 limits.pairs 0 (2, 0, 3)).isSome do
    throw (IO.userError "scalar branch unnecessarily searched roots")
  for n in [5, 13] do
    let some c := generateAutomaticCertificate n limits ⟨32, 2⟩ [2, 12] [3, 7]
      | throw (IO.userError "automatic certificate generation failed")
    unless c.n == n && c.t == 2 && verifyRawCertificate n limits c do
      throw (IO.userError "automatic certificate replay failed")
    unless c.extra.length == (if n == 13 then 1 else 0) do
      throw (IO.userError "missing-flag search mismatch")
  unless (generateAutomaticCertificate 5 limits ⟨0, 0⟩ [0, 2] []).isSome do
    throw (IO.userError "failed parameter prevented subsequent success")
  for budget in ([⟨32, 0⟩, ⟨32, 1⟩] : List GenerationBudget) do
    unless (generateAutomaticCertificate 13 limits budget [2] [3, 7]).isNone do
      throw (IO.userError "auxiliary prefix ignored")
  unless
    (generateAutomaticCertificate 5 { limits with maxCandidates := 1 } ⟨32, 2⟩ [0, 2]
        [3, 7]).isNone do
    throw (IO.userError "parameter prefix ignored")
  for n in [0, 1, 2, 3, 4, 25] do
    unless (generateAutomaticCertificate n limits ⟨32, 2⟩ [2] [3, 7]).isNone do
      throw (IO.userError "unexpected general-path acceptance")
  unless (generateAutomaticCertificate 5 limits ⟨32, 2⟩ [1000000000] [3, 7]).isNone do
    throw (IO.userError "parameter bound ignored")
  unless
    (generateAutomaticCertificate 13 { limits with pairs := ⟨32, 4, 16, 1⟩ } ⟨32, 2⟩ [2]
        [3, 7]).isNone do
    throw (IO.userError "combined row bound ignored")

end PseudoPrime.PrimeTest.APRCL.GenerationTests

/-- Run automatic construction regressions. -/
def main : IO Unit :=
  PseudoPrime.PrimeTest.APRCL.GenerationTests.run
