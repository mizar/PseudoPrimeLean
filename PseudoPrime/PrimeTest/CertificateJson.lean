/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Lean.Data.Json
/-! # Exact decimal fields shared by primality certificate formats -/
namespace PseudoPrime.PrimeTest.CertificateJson
/-- Decode a decimal-string natural without a floating-point conversion. -/
def readNat (j : Lean.Json) : Except String Nat := do
  let s ← j.getStr?
  match s.toNat? with
  | some n => return n
  | none => throw "expected a natural-number decimal string"
end PseudoPrime.PrimeTest.CertificateJson
