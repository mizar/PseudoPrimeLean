/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Tools.CertificateIO
public import PseudoPrime.PrimeTest.SmallInputJson

/-!
# Small-input certificate file command
Generation and verification recheck both prime and nonprime claims by bounded trial division.
-/

@[expose] public section

namespace PseudoPrime.Tools.SmallInputCertificate

/-- Print the proved decision; unknown includes invalid data and exceeded limits. -/
def report {n : ℕ} (result : PrimeTest.Decision n) : IO UInt32 :=
  match result with
  | .prime _ => do
    IO.println "prime";
    return 0
  | .notPrime _ => do
    IO.println "not_prime";
    return 0
  | .unknown => do
    IO.println "unknown_or_rejected";
    return 1

/-- Generate or verify bounded small-input JSON, with code 3 for no generated text.
Code 0 accepts either proved decision, code 1 rejects, code 2 reports arguments or I/O errors. -/
def run (args : List String) : IO UInt32 := do
  match args with
  | [command, n, limit, maxBytes, path] =>
    match [n, limit, maxBytes].mapM CertificateIO.readNat with
    | .ok [n, limit, maxBytes] =>
      if command == "generate" then
        match PrimeTest.SmallInput.generateCertificateText n limit maxBytes with
        | none =>
          IO.println "unknown: no certificate generated";
          return 3
        | some text =>
          IO.FS.writeFile path text
          report (PrimeTest.SmallInput.resultOfCertificateText n limit maxBytes text)
      else if command == "verify" then
        let some text ← CertificateIO.readFileBounded path maxBytes |
          do
            IO.println "unknown_or_rejected"
            return 1
        report (PrimeTest.SmallInput.resultOfCertificateText n limit maxBytes text)
      else
        IO.eprintln "expected generate or verify";
        return 2
    | .error message =>
      IO.eprintln message;
      return 2
    | .ok _ =>
      IO.eprintln "invalid arguments";
      return 2
  | _ =>
    IO.eprintln "generate|verify N LIMIT MAX_BYTES FILE";
    return 2

end PseudoPrime.Tools.SmallInputCertificate

/-- Report file errors without a mathematical conclusion. -/
def main (args : List String) : IO UInt32 := do
  try
    PseudoPrime.Tools.SmallInputCertificate.run args
  catch error =>
    IO.eprintln error.toString;
    return 2
