/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.Tools.CertificateIO
import PseudoPrime.PrimeTest.BLS.CertificateGenerateJson

/-!
# BLS certificate file command

Run with lake env lean --run PseudoPrime/Tools/BLSCertificate.lean.
Generation uses fixed rho parameters and may return unknown even on primes.
The byte limit is enforced during file reading, before UTF-8 decoding and JSON parsing.
-/

namespace PseudoPrime.Tools.BLSCertificate

/-- Select the square, cube, or BLS5 criterion from its external name. -/
def readMethod : String → Except String PrimeTest.BLS.CertificateMethod
  | "square" => .ok .square
  | "cube" => .ok .cube
  | "bls5" => .ok .bls5
  | _ => .error "expected square, cube, or bls5"

/-- Validate the method, input, factor fuel and witness-base limit. -/
def generateArgs (method n fuel maxBase : String) :
    Except String (PrimeTest.BLS.CertificateMethod × ℕ × ℕ × ℕ) := do
  return (← readMethod method, ← CertificateIO.readNat n, ← CertificateIO.readNat fuel,
      ← CertificateIO.readNat maxBase)

/-- Generate a rechecked certificate file, or verify a file against an explicit input.
Codes are 0 for success, 1 for rejection, 2 for input or I/O errors and 3 for failed generation. -/
def run (args : List String) : IO UInt32 := do
  match args with
  | ["generate", method, n, fuel, maxBase, path] =>
    match generateArgs method n fuel maxBase with
    | .error message =>
      IO.eprintln message;
      return 2
    | .ok (method, n, fuel, maxBase) =>
      if n < 2 then
        IO.eprintln "input must be at least 2"
        return 2
      let bases := (List.range (min (maxBase + 1) (n - 1))).drop 2
      match PrimeTest.BLS.generateCertificateJson n method ⟨2, 1⟩ fuel bases with
      | none =>
        IO.println "unknown: no certificate generated";
        return 3
      | some j =>
        IO.FS.writeFile path (j.pretty ++ "\n")
        IO.println "prime: certificate generated and rechecked"
        return 0
  | ["verify", n, maxBytes, path] =>
    match
      (do
        return (← CertificateIO.readNat n, ← CertificateIO.readNat maxBytes) :
        Except String (ℕ × ℕ)) with
    | .error message =>
      IO.eprintln message;
      return 2
    | .ok (n, maxBytes) =>
      let some text ← CertificateIO.readFileBounded path maxBytes |
        do
          IO.println "certificate_valid=false"
          return 1
      let accepted := PrimeTest.BLS.verifyCertificateText n maxBytes text
      IO.println (if accepted then "certificate_valid=true" else "certificate_valid=false")
      return if accepted then 0 else 1
  | _ =>
    IO.eprintln "generate METHOD N FUEL MAX_BASE FILE | verify N MAX_BYTES FILE"
    return 2

end PseudoPrime.Tools.BLSCertificate

/-- Run the file interface and report I/O failures without a primality verdict. -/
def main (args : List String) : IO UInt32 := do
  try
    PseudoPrime.Tools.BLSCertificate.run args
  catch error =>
    IO.eprintln error.toString
    return 2
