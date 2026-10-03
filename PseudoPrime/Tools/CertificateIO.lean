/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import Lean

/-! # Shared certificate command parsing and bounded UTF-8 input -/

namespace PseudoPrime.Tools.CertificateIO

/-- Parse an unsigned decimal command argument. -/
def readNat (s : String) : Except String Nat :=
  match s.toNat? with
  | some n => .ok n
  | none => .error "expected a natural-number decimal argument"

/-- Read at most maxBytes payload bytes, probing one extra byte to reject larger files.
An oversized file returns none; invalid UTF-8 and I/O failures raise an I/O error.
Each read is capped at 64 KiB, including on growing files. Decode UTF-8 only after the cap check.
The cap bounds payload storage, not total allocator overhead or parsing cost. -/
def readFileBounded (path : System.FilePath) (maxBytes : Nat) : IO (Option String) :=
  IO.FS.withFile path .read fun handle => do
    let rec loop (remaining : Nat) (data : ByteArray) : IO (Option ByteArray) := do
      let chunk ← handle.read (USize.ofNat (min 65536 remaining))
      if chunk.isEmpty then
        return some data
      if chunk.size > remaining then
        return none
      let data := data ++ chunk
      if data.size > maxBytes then
        return none
      if _h : remaining - chunk.size < remaining then
        loop (remaining - chunk.size) data
      else
        return some data
    termination_by remaining
    let some data ← loop (maxBytes + 1) ByteArray.empty | return none
    match String.fromUTF8? data with
    | some text =>
      return some text
    | none =>
      throw (IO.userError "certificate is not valid UTF-8")

end PseudoPrime.Tools.CertificateIO
