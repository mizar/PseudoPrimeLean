import PseudoPrime.Tools.CertificateIO

/-! # Bounded certificate input regressions -/

namespace PseudoPrime.Tests.CertificateIO

/-- Check exact byte boundaries, multi-chunk input, UTF-8 and zero-byte limits. -/
def run : IO Unit := do
  for text in ["", "a", "あ", String.ofList (List.replicate 70000 'x')] do
    IO.FS.withTempFile fun handle path => do
        handle.write text.toUTF8
        handle.flush
        let exact ← Tools.CertificateIO.readFileBounded path text.utf8ByteSize
        unless exact == some text do
          throw (IO.userError "exact byte boundary failed")
        if text.utf8ByteSize > 0 then
          let tooSmall ← Tools.CertificateIO.readFileBounded path (text.utf8ByteSize - 1)
          unless tooSmall == none do
            throw (IO.userError "oversized input accepted")
  IO.FS.withTempFile fun handle path => do
      handle.write ⟨#[255]⟩
      handle.flush
      let rejected ←
        try
          let _ ← Tools.CertificateIO.readFileBounded path 1
          pure false
        catch _ =>
          pure true
      unless rejected do
        throw (IO.userError "invalid UTF-8 accepted")

end PseudoPrime.Tests.CertificateIO

/-- Execute the bounded input regressions without exporting them. -/
def main : IO Unit :=
  PseudoPrime.Tests.CertificateIO.run
