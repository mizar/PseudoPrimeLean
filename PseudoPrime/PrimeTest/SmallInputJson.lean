/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.SmallInput
public import PseudoPrime.PrimeTest.CertificateJson

/-!
# Small-input decision certificates in JSON

Bounded trial division verifies both positive and negative decisions unconditionally.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest.SmallInput

/--
Untrusted small-input primality claim for a target n and a Boolean isPrime.
The target must agree with the caller and the claim must match bounded trial division.
No invariant is stored as a proof; resultOfCertificate supplies a certified Decision after replay.
-/
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

/-- Construct a certified decision from an already verified claim.
The acceptance proof supplies the bounded arithmetic result without repeating trial division.
Zero and one yield notPrime; generation can reuse its verification evidence. -/
def resultOfVerifiedCertificate (n limit : ℕ) (c : Certificate)
    (h : verifyCertificate n limit c = true) : Decision n :=
  match hb : c.isPrime with
  | true =>
    .prime
      (isPrimeUpTo_true (limit := limit) (n := n)
        (by simpa only [hb] using (verifyCertificate_spec h).2))
  | false =>
    .notPrime
      (isPrimeUpTo_false (limit := limit) (n := n)
        (by simpa only [hb] using (verifyCertificate_spec h).2))

/-- Verify an untrusted claim and construct its certified decision.
Invalid and out-of-range claims return unknown; zero and one are notPrime. -/
def resultOfCertificate (n limit : ℕ) (c : Certificate) : Decision n :=
  if h : verifyCertificate n limit c = true then resultOfVerifiedCertificate n limit c h
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

/-- Decode accepted text and reuse its verification proof to construct a decision.
The caller supplies acceptance for the same target, limit, and text; this path parses the text
but performs no additional trial division. The generator CLI uses it after generation. -/
def resultOfVerifiedCertificateText (n limit maxBytes : ℕ) (text : String)
    (h : verifyCertificateText n limit maxBytes text = true) : Decision n :=
  match hd : decodeCertificateText maxBytes text with
  | .error _ => .unknown
  | .ok c =>
    resultOfVerifiedCertificate n limit c (by simpa only [verifyCertificateText, hd] using h)

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

/-- Generate an in-range decision once, serialize it, and parse the exact text again.
Check the decoded target and Boolean against the computed decision; return none on excessive
input or output size. The public verifier independently replays trial division. -/
def generateCertificateText (n limit maxBytes : ℕ) : Option String :=
  let expected := isPrimeUpTo limit n
  (expected.map (fun b ↦ (encodeCertificate ⟨n, b⟩).compress)).filter
    (fun text ↦
      match decodeCertificateText maxBytes text with
      | .error _ => false
      | .ok c => decide (c.n = n) && decide (expected = some c.isPrime))

/-- Every generated text passes the same external text verifier. -/
theorem generateCertificateText_checked {n limit maxBytes : ℕ} {text : String}
    (h : generateCertificateText n limit maxBytes = some text) :
    verifyCertificateText n limit maxBytes text = true := by
  exact (Option.filter_eq_some_iff.mp h).2

end PseudoPrime.PrimeTest.SmallInput
