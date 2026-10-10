/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.BLS.Certificate
public import PseudoPrime.PrimeTest.CertificateJson

/-!
# JSON interchange for external BLS certificates

The parser accepts untrusted data. The mathematical verifier supplies the primality guarantee.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest.BLS

/-- Decode exactly two decimal-string naturals for a factor or witness entry. -/
def certificateJsonPair (j : Lean.Json) : Except String (ℕ × ℕ) := do
  let a ← j.getArr?
  if a.size != 2 then
    throw "expected a pair"
  return (← CertificateJson.readNat (← j.getArrVal? 0),
      ← CertificateJson.readNat (← j.getArrVal? 1))

/-- Decode the versioned Python BLS payload into untrusted method data.
Exactly five fields and a supported method are required. Small-prime payloads must be empty.
Factor bases and exponents are bounded by the input before computing their powers.
The cofactor is reconstructed; primality requires verifyInputCertificate afterward. -/
def decodeInputCertificate (j : Lean.Json) : Except String InputCertificate := do
  let obj ← j.getObj?
  if obj.foldl (fun count _ _ => count + 1) 0 != 5 then
    throw "invalid fields"
  let format ← (← j.getObjVal? "format").getStr?
  if format != "bls-reference-v1" then
    throw "unsupported certificate format"
  let method ← (← j.getObjVal? "method").getStr?
  if !(method == "square" || method == "cube" || method == "bls5") then
    throw "unsupported method"
  let n ← CertificateJson.readNat (← j.getObjVal? "n")
  let factors ← (← (← j.getObjVal? "factors").getArr?).toList.mapM certificateJsonPair
  let witnesses ← (← (← j.getObjVal? "witnesses").getArr?).toList.mapM certificateJsonPair
  if n = 2 ∨ n = 3 then
    if factors.isEmpty && witnesses.isEmpty then
      return .small n
    else
      throw "small-prime certificate must be empty"
  if
      !(factors.all
          (fun qe => decide (2 ≤ qe.1 ∧ qe.1 ≤ n - 1 ∧ 0 < qe.2 ∧ qe.2 ≤ (n - 1).log2 + 1))) then
    throw "factor outside input bounds"
  let data : PartialFactorizationData := ⟨factors, (n - 1) / factorProduct factors⟩
  if method == "square" then
    return .square ⟨n, data, witnesses⟩
  else if method == "cube" then
    return .cube ⟨n, data, witnesses⟩
  else
    return .bls5 ⟨n, data, witnesses, data.cofactor⟩

/-- Decode and mathematically recheck a JSON certificate for the requested input.
Malformed data and mathematical rejection both return false, never a composite verdict. -/
def verifyCertificateJson (n : ℕ) (j : Lean.Json) : Bool :=
  match decodeInputCertificate j with
  | .error _ => false
  | .ok c => verifyInputCertificate n c

/-- JSON acceptance proves the requested input prime through the external BLS verifier.
No trust in the producer or its result flags is required. -/
theorem verifyCertificateJson_sound {n : ℕ} (j : Lean.Json) (h : verifyCertificateJson n j = true) :
    Nat.Prime n := by
  cases hd : decodeInputCertificate j with
  | error message => simp only [verifyCertificateJson, hd, Bool.false_eq_true] at h
  | ok c => exact verifyInputCertificate_sound c (by simpa only [verifyCertificateJson, hd] using h)

/-- Encode factor or witness pairs as arrays of decimal strings. -/
def certificatePairsToJson (pairs : List (ℕ × ℕ)) : Lean.Json :=
  .arr (pairs.map (fun qe => Lean.Json.arr #[.str (toString qe.1), .str (toString qe.2)])).toArray

/-- Encode BLS data in the Python bls-reference-v1 format.
The cofactor is omitted and reconstructed on decode. Small primes use the square tag.
This encoder alone does not certify validity or assert round-trip equality for invalid data. -/
def encodeInputCertificate (c : InputCertificate) : Lean.Json :=
  let (n, method, factors, witnesses) : ℕ × String × List (ℕ × ℕ) × List (ℕ × ℕ) :=
    match c with
    | .small n => (n, "square", [], [])
    | .square c => (c.n, "square", c.factorization.factors, c.witnesses)
    | .cube c => (c.n, "cube", c.factorization.factors, c.witnesses)
    | .bls5 c => (c.n, "bls5", c.factorization.factors, c.witnesses)
  Lean.Json.mkObj
    [("format", .str "bls-reference-v1"), ("n", .str (toString n)), ("method", .str method),
      ("factors", certificatePairsToJson factors), ("witnesses", certificatePairsToJson witnesses)]

/-- Reject text exceeding maxBytes before JSON parsing, then recheck the decoded certificate.
This bounds the supplied text length, not the time or memory of the full verifier. -/
def verifyCertificateText (n maxBytes : ℕ) (text : String) : Bool :=
  if maxBytes < text.utf8ByteSize then false
  else
    match Lean.Json.parse text with
    | .error _ => false
    | .ok j => verifyCertificateJson n j

/-- Acceptance of bounded JSON text proves the requested input prime. -/
theorem verifyCertificateText_sound {n maxBytes : ℕ} (text : String)
    (h : verifyCertificateText n maxBytes text = true) : Nat.Prime n := by
  unfold verifyCertificateText at h
  split at h
  · exact Bool.noConfusion h
  · cases hp : Lean.Json.parse text with
    | error message => simp only [hp, Bool.false_eq_true] at h
    | ok j => exact verifyCertificateJson_sound j (by simpa only [hp] using h)

end PseudoPrime.PrimeTest.BLS
