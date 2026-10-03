/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.Tools.CertificateIO
import PseudoPrime.PrimeTest.APRCL.CertificateJson

/-!
# APR-CL raw certificate file interface
All successful messages describe finite replay, not an unconditional primality proof.
-/

namespace PseudoPrime.Tools.APRCLCertificate

/-- Configure replay from explicit parameter, prime and degree caps.
The row cap is maxQ, index cap is log2(maxQ), and one parameter is tried. -/
def limits (maxT maxQ maxDegree : ℕ) : PrimeTest.APRCL.CertificateLimits :=
  ⟨⟨maxQ, maxQ.log2, maxDegree, maxQ⟩, maxT, 1⟩

/-- Generate or replay a file with explicit resource bounds.
Codes: 0 finite acceptance, 1 rejection, 2 input/I/O error, 3 no generated certificate.
The byte cap is enforced during file reading, before JSON parsing. -/
def run (args : List String) : IO UInt32 := do
  match args with
  | [command, n, t, maxQ, maxDegree, maxBytes, path] =>
    match [n, t, maxQ, maxDegree, maxBytes].mapM CertificateIO.readNat with
    | .error message =>
      IO.eprintln message;
      return 2
    | .ok [n, t, maxQ, maxDegree, maxBytes] =>
      let caps := limits t maxQ maxDegree
      if command == "generate" then
        let auxiliary := List.range (maxQ + 1)
        match
          PrimeTest.APRCL.generateCertificateText n caps ⟨maxQ + 1, maxQ + 1⟩ [t] auxiliary
            maxBytes with
        | none =>
          IO.println "unknown: no certificate generated";
          return 3
        | some text =>
          IO.FS.writeFile path text
          IO.println "finite_checks_passed=true; local_kernel=pending"
          return 0
      else if command == "verify" then
        let some text ← CertificateIO.readFileBounded path maxBytes |
          do
            IO.println "finite_checks_passed=false"
            return 1
        let ok := PrimeTest.APRCL.verifyCertificateText n caps maxBytes text
        IO.println
            (if ok then "finite_checks_passed=true; local_kernel=pending"
            else "finite_checks_passed=false")
        return if ok then 0 else 1
      else
        IO.eprintln "expected generate or verify";
        return 2
    | .ok _ =>
      IO.eprintln "invalid arguments";
      return 2
  | _ =>
    IO.eprintln "generate|verify N T_OR_MAX_T MAX_Q MAX_DEGREE MAX_BYTES FILE"
    return 2

end PseudoPrime.Tools.APRCLCertificate

/-- Catch file errors without reporting a primality conclusion. -/
def main (args : List String) : IO UInt32 := do
  try
    PseudoPrime.Tools.APRCLCertificate.run args
  catch error =>
    IO.eprintln error.toString;
    return 2
