/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.SmallInput
import PseudoPrime.PrimeTest.CertificateJson

/-!
# Small-input decision certificates in JSON

Bounded trial division verifies both positive and negative decisions unconditionally.
-/

namespace PseudoPrime.PrimeTest.SmallInput

structure Certificate where
  /-- Claimed target, checked against the caller's input. -/
  n : ℕ
  /-- Claimed primality; false includes zero and one. -/
  isPrime : Bool

/-- Recheck target agreement and the claimed decision under the caller's input limit.
False means rejected or out of range, not necessarily composite. -/
def verifyCertificate (n limit : ℕ) (c : Certificate) : Bool :=
  decide (c.n = n) && decide (isPrimeUpTo limit n = some c.isPrime)

/-- Acceptance binds the claim to the target and the exact bounded decision. -/
theorem verifyCertificate_spec {n limit : ℕ} {c : Certificate}
    (h : verifyCertificate n limit c = true) : c.n = n ∧ isPrimeUpTo limit n = some c.isPrime := by
  obtain ⟨hn, hp⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨of_decide_eq_true hn, of_decide_eq_true hp⟩

/-- Turn an accepted claim into a proved prime or notPrime result.
Invalid and out-of-range claims return unknown; zero and one are notPrime. -/
def resultOfCertificate (n limit : ℕ) (c : Certificate) : Decision n :=
  if h : verifyCertificate n limit c = true then
    match hb : c.isPrime with
    | true => .prime (isPrimeUpTo_true (by simpa only [hb] using (verifyCertificate_spec h).2))
    | false => .notPrime (isPrimeUpTo_false (by simpa only [hb] using (verifyCertificate_spec h).2))
  else .unknown

/-- Parse the three-field small-input-v1 format with a decimal-string target.
The Boolean remains untrusted until arithmetic replay. -/
def decodeCertificate (j : Lean.Json) : Except String Certificate := do
  let obj ← j.getObj?
  if obj.foldl (fun count _ _ ↦ count + 1) 0 != 3 then
    throw "invalid fields"
  if (← (← j.getObjVal? "format").getStr?) != "small-input-v1" then
    throw "unsupported certificate format"
  let n ← CertificateJson.readNat (← j.getObjVal? "n")
  return ⟨n, ← (← j.getObjVal? "is_prime").getBool?⟩

/-- Encode the target exactly as decimal text and retain the claimed Boolean decision. -/
def encodeCertificate (c : Certificate) : Lean.Json :=
  Lean.Json.mkObj
    [("format", .str "small-input-v1"), ("n", .str (toString c.n)), ("is_prime", .bool c.isPrime)]

/-- Reject excessive UTF-8 input before standard JSON parsing.
The byte bound does not cover memory already used to read the string. -/
def decodeCertificateText (maxBytes : ℕ) (text : String) : Except String Certificate := do
  if maxBytes < text.utf8ByteSize then
    throw "text exceeds byte limit"
  decodeCertificate (← Lean.Json.parse text)

/-- Parse and recheck text against an explicit target and trial-division limit. -/
def verifyCertificateText (n limit maxBytes : ℕ) (text : String) : Bool :=
  match decodeCertificateText maxBytes text with
  | .error _ => false
  | .ok c => verifyCertificate n limit c

/-- Connect external JSON directly to proof-carrying primality results.
This small-input path has no APR-CL local-kernel assumption. -/
def resultOfCertificateText (n limit maxBytes : ℕ) (text : String) : Decision n :=
  match decodeCertificateText maxBytes text with
  | .error _ => .unknown
  | .ok c => resultOfCertificate n limit c

/-- Accepted text supplies its actual decoded and arithmetically rechecked claim. -/
theorem verifyCertificateText_spec {n limit maxBytes : ℕ} {text : String}
    (h : verifyCertificateText n limit maxBytes text = true) :
    ∃ c,
      decodeCertificateText maxBytes text = .ok c ∧
        c.n = n ∧ isPrimeUpTo limit n = some c.isPrime := by
  cases hd : decodeCertificateText maxBytes text with
  | error message => simp only [verifyCertificateText, hd, Bool.false_eq_true] at h
  | ok c =>
    exact ⟨c, rfl, verifyCertificate_spec (by simpa only [verifyCertificateText, hd] using h)⟩

/-- Generate an in-range decision, serialize it, then parse and recheck the exact text.
Return none on excessive input or output size. -/
def generateCertificateText (n limit maxBytes : ℕ) : Option String :=
  ((isPrimeUpTo limit n).map (fun b ↦ (encodeCertificate ⟨n, b⟩).compress)).filter
    (verifyCertificateText n limit maxBytes)

/-- Every generated text passes the same external text verifier. -/
theorem generateCertificateText_checked {n limit maxBytes : ℕ} {text : String}
    (h : generateCertificateText n limit maxBytes = some text) :
    verifyCertificateText n limit maxBytes text = true := by
  exact (Option.filter_eq_some_iff.mp h).2

end PseudoPrime.PrimeTest.SmallInput
