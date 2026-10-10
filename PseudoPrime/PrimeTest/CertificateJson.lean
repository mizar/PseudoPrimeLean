/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Lean.Data.Json

/-! # Exact decimal fields shared by primality certificate formats -/

@[expose] public section

namespace PseudoPrime.PrimeTest.CertificateJson

/--
Read an exact natural number from a JSON string containing its decimal representation.
Non-string JSON values return the error from `getStr?`; strings not accepted by `toNat?`
return the explicit decimal-string error. Successful decoding returns an unbounded `Nat`
without passing through floating point. Certificate parsers share this reader for large fields.
-/
def readNat (j : Lean.Json) : Except String Nat := do
  let s ← j.getStr?
  match s.toNat? with
  | some n =>
    return n
  | none =>
    throw "expected a natural-number decimal string"

end PseudoPrime.PrimeTest.CertificateJson
