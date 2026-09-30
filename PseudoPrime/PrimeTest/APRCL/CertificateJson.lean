import PseudoPrime.PrimeTest.APRCL.Generate
import PseudoPrime.PrimeTest.CertificateJson

/-!
# APR-CL raw JSON certificate interchange

The format preserves exact integers and separates finite replay from the local kernel.
-/

namespace PseudoPrime.PrimeTest.APRCL

/-- Decode exactly four decimal strings p,k,q,g; k is the zero-based Lean index.
Arithmetic validity is checked later by the raw certificate verifier. -/
def jsonRow (j : Lean.Json) : Except String RawPairData := do
  let a ← j.getArr?
  if a.size != 4 then
    throw "expected [p,k,q,g]"
  return ⟨← CertificateJson.readNat (← j.getArrVal? 0),
      ← CertificateJson.readNat (← j.getArrVal? 1), ← CertificateJson.readNat (← j.getArrVal? 2),
      ← CertificateJson.readNat (← j.getArrVal? 3)⟩

/-- Decode the versioned Lean raw format with exactly five object fields.
Reject oversized combined row arrays before converting their elements.
This differs from the Python compact format, which omits main rows and primitive roots. -/
def decodeRawCertificate (limits : CertificateLimits) (j : Lean.Json) :
    Except String RawCertificate := do
  let obj ← j.getObj?
  if obj.foldl (fun count _ _ ↦ count + 1) 0 != 5 then
    throw "invalid fields"
  if (← (← j.getObjVal? "format").getStr?) != "aprcl-lean-raw-v1" then
    throw "unsupported certificate format"
  let n ← CertificateJson.readNat (← j.getObjVal? "n")
  let t ← CertificateJson.readNat (← j.getObjVal? "t")
  let main ← (← j.getObjVal? "main").getArr?
  let extra ← (← j.getObjVal? "extra").getArr?
  if main.size + extra.size > limits.pairs.maxPairs then
    throw "too many rows"
  return ⟨n, t, ← main.toList.mapM jsonRow, ← extra.toList.mapM jsonRow⟩

/-- Encode one raw row as four exact decimal strings in p,k,q,g order. -/
def rowToJson (row : RawPairData) : Lean.Json :=
  .arr
    #[.str (toString row.p), .str (toString row.k), .str (toString row.q),
      .str (toString row.generator)]

/-- Serialize raw data without asserting validity or a general round-trip theorem.
The generator reparses and rechecks the serialized text before returning it. -/
def encodeRawCertificate (c : RawCertificate) : Lean.Json :=
  Lean.Json.mkObj
    [("format", .str "aprcl-lean-raw-v1"), ("n", .str (toString c.n)), ("t", .str (toString c.t)),
      ("main", .arr (c.main.map rowToJson).toArray),
      ("extra", .arr (c.extra.map rowToJson).toArray)]

/-- Decode and replay for the caller's target and limits.
Acceptance means finite-check success and still requires the local kernel for primality. -/
def verifyCertificateJson (n : ℕ) (limits : CertificateLimits) (j : Lean.Json) : Bool :=
  match decodeRawCertificate limits j with
  | .error _ => false
  | .ok c => verifyRawCertificate n limits c

/-- JSON acceptance provides the actual decoded certificate and its successful replay. -/
theorem verifyCertificateJson_spec {n : ℕ} {limits : CertificateLimits} {j : Lean.Json}
    (h : verifyCertificateJson n limits j = true) :
    ∃ c, decodeRawCertificate limits j = .ok c ∧ verifyRawCertificate n limits c = true := by
  cases hd : decodeRawCertificate limits j with
  | error message => simp only [verifyCertificateJson, hd, Bool.false_eq_true] at h
  | ok c => exact ⟨c, rfl, by simpa only [verifyCertificateJson, hd] using h⟩

/-- Check UTF-8 byte length before parsing text and decoding bounded rows.
The limit does not bound memory already used to read the input string. -/
def decodeCertificateText (limits : CertificateLimits) (maxBytes : ℕ) (text : String) :
    Except String RawCertificate := do
  if maxBytes < text.utf8ByteSize then
    throw "text exceeds byte limit"
  let j ← Lean.Json.parse text
  decodeRawCertificate limits j

/-- Replay bounded JSON text for an explicit target; false is not a composite verdict. -/
def verifyCertificateText (n : ℕ) (limits : CertificateLimits) (maxBytes : ℕ) (text : String) :
    Bool :=
  match decodeCertificateText limits maxBytes text with
  | .error _ => false
  | .ok c => verifyRawCertificate n limits c

/-- Text acceptance supplies a parsed certificate that passes complete arithmetic replay. -/
theorem verifyCertificateText_spec {n maxBytes : ℕ} {limits : CertificateLimits} {text : String}
    (h : verifyCertificateText n limits maxBytes text = true) :
    ∃ c,
      decodeCertificateText limits maxBytes text = .ok c ∧
        verifyRawCertificate n limits c = true := by
  cases hd : decodeCertificateText limits maxBytes text with
  | error message => simp only [verifyCertificateText, hd, Bool.false_eq_true] at h
  | ok c => exact ⟨c, rfl, by simpa only [verifyCertificateText, hd] using h⟩

/-- Text acceptance implies primality only with the explicit local block implication.
The decoded certificate is passed through the existing conditional raw verifier theorem. -/
theorem prime_of_verifyCertificateText {n maxBytes : ℕ} {limits : CertificateLimits} {text : String}
    (h : verifyCertificateText n limits maxBytes text = true) (a : ℕ → ℕ → ℕ)
    (hlocal :
      ∀ c,
        decodeCertificateText limits maxBytes text = .ok c →
          ∀ entries,
            decodePairInputs n limits.pairs (c.main ++ c.extra) = some entries →
              RawCertificateLocal n c.t entries a) :
    Nat.Prime n := by
  obtain ⟨c, hd, hc⟩ := verifyCertificateText_spec h
  exact prime_of_verifyRawCertificate hc a (hlocal c hd)

/-- Construct, serialize, parse and recheck an automatic certificate under a byte limit.
None means generation, serialization replay or a resource limit failed. -/
def generateCertificateText (n : ℕ) (limits : CertificateLimits) (budget : GenerationBudget)
    (parameters auxiliary : List ℕ) (maxBytes : ℕ) : Option String :=
  ((generateAutomaticCertificate n limits budget parameters auxiliary).map
        (fun c ↦ (encodeRawCertificate c).compress)).filter
    (verifyCertificateText n limits maxBytes)

/-- Every returned text passes the public bounded text verifier for the same target. -/
theorem generateCertificateText_checked {n maxBytes : ℕ} {limits : CertificateLimits}
    {budget : GenerationBudget} {parameters auxiliary : List ℕ} {text : String}
    (h : generateCertificateText n limits budget parameters auxiliary maxBytes = some text) :
    verifyCertificateText n limits maxBytes text = true := by
  exact (Option.filter_eq_some_iff.mp h).2

/-- Generated text feeds the final primality criterion with its local kernel still explicit. -/
theorem generateCertificateText_prime {n maxBytes : ℕ} {limits : CertificateLimits}
    {budget : GenerationBudget} {parameters auxiliary : List ℕ} {text : String}
    (h : generateCertificateText n limits budget parameters auxiliary maxBytes = some text)
    (a : ℕ → ℕ → ℕ)
    (hlocal :
      ∀ c,
        decodeCertificateText limits maxBytes text = .ok c →
          ∀ entries,
            decodePairInputs n limits.pairs (c.main ++ c.extra) = some entries →
              RawCertificateLocal n c.t entries a) :
    Nat.Prime n := by
  exact prime_of_verifyCertificateText (generateCertificateText_checked h) a hlocal

end PseudoPrime.PrimeTest.APRCL
