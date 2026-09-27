import PseudoPrime.PrimeTest.APRCL.CertificateJson
/-!
# APR-CL JSON replay regressions
Round-trip examples, tampering and resource limits are checked by compiled execution.
-/
namespace PseudoPrime.PrimeTest.APRCL.JsonTests
/-- Small limits for serialization and replay. -/
def limits : CertificateLimits := ⟨⟨32,4,16,8⟩,2,1⟩
/-- A valid raw certificate using an additional flag witness. -/
def sample : RawCertificate := ⟨13,2,[⟨2,0,3,0⟩],[⟨2,0,7,0⟩]⟩
/-- Check serialization, generated text, tampered inputs and byte/row caps. -/
def run : IO Unit := do
  let text := (encodeRawCertificate sample).compress
  unless verifyCertificateText 13 limits text.utf8ByteSize text do
    throw (IO.userError "round-trip rejected")
  if verifyCertificateText 13 limits (text.utf8ByteSize - 1) text then
    throw (IO.userError "byte cap ignored")
  if verifyCertificateText 5 limits 4096 text then
    throw (IO.userError "target mismatch accepted")
  if verifyCertificateText 13 {limits with pairs := ⟨32,4,16,1⟩} 4096 text then
    throw (IO.userError "row cap ignored")
  for bad in ["{", "{}", text.replace "aprcl-lean-raw-v1" "aprcl-reference-v1",
      text.replace "\"13\"" "13", text.replace "\"13\"" "\"-13\"",
      text.replace "[\"2\",\"0\",\"7\",\"0\"]" "[\"2\",\"0\",\"3\",\"0\"]"] do
    if verifyCertificateText 13 limits 4096 bad then
      throw (IO.userError "malformed or tampered JSON accepted")
  if verifyCertificateJson 13 limits
      (encodeRawCertificate {sample with extra := [⟨2,0,23,0⟩]}) then
    throw (IO.userError "false flag accepted")
  let huge := 100000000000000000000000000000000000001
  match decodeRawCertificate limits (encodeRawCertificate {sample with n := huge}) with
  | .error _ => throw (IO.userError "large natural decode failed")
  | .ok c =>
    unless c.n == huge do throw (IO.userError "large natural lost precision")
  let some generated := generateCertificateText 13 limits ⟨32,2⟩ [2] [3,7] 4096
    | throw (IO.userError "JSON generation failed")
  unless verifyCertificateText 13 limits 4096 generated do
    throw (IO.userError "generated JSON rejected")
  unless (generateCertificateText 13 limits ⟨32,2⟩ [2] [3,7] 0).isNone do
    throw (IO.userError "generation byte cap ignored")
end PseudoPrime.PrimeTest.APRCL.JsonTests
/-- Run JSON replay regressions. -/
def main : IO Unit := PseudoPrime.PrimeTest.APRCL.JsonTests.run
