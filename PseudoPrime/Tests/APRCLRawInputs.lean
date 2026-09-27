import PseudoPrime.PrimeTest.APRCL.RawInput
/-!
# APR-CL raw input regressions

Execute all four constructors and reject malformed data and exceeded resource bounds.
-/
namespace PseudoPrime.PrimeTest.APRCL.RawInputTests
/-- Small explicit limits for the regression suite. -/
def limits : PairInputLimits := ⟨32, 4, 16, 8⟩
/-- One raw input for each branch. -/
def rows : List RawPairData := [⟨2, 0, 3, 0⟩, ⟨3, 0, 7, 3⟩, ⟨2, 1, 5, 2⟩, ⟨2, 3, 17, 3⟩]
/-- Exercise construction, fail-closed decoding, and finite-check acceptance. -/
def run : IO Unit := do
  for row in rows do
    let some input := decodePairInput 19 limits row
      | throw (IO.userError s!"branch rejected: {repr row}")
    unless input.key == (row.p, row.k, row.q) do
      throw (IO.userError "key mismatch")
  for row in ([⟨4, 0, 5, 2⟩, ⟨3, 0, 9, 2⟩, ⟨2, 1, 17, 3⟩,
      ⟨3, 0, 7, 1⟩, ⟨3, 0, 7, 7⟩, ⟨2, 1000000000, 3, 0⟩] : List RawPairData) do
    unless (decodePairInput 19 limits row).isNone do
      throw (IO.userError s!"invalid row accepted: {repr row}")
  for n in [0, 1, 2, 3] do
    unless (decodePairInput n limits ⟨2, 0, 3, 0⟩).isNone do
      throw (IO.userError "input guard bypassed")
  for cap in ([⟨2, 4, 16, 8⟩, ⟨32, 0, 16, 8⟩, ⟨32, 4, 1, 8⟩] :
      List PairInputLimits) do
    unless (decodePairInput 19 cap ⟨2, 1, 5, 2⟩).isNone do
      throw (IO.userError "resource guard bypassed")
  unless (decodePairInputs 19 ⟨32, 4, 16, 3⟩ rows).isNone do
    throw (IO.userError "row count guard bypassed")
  unless (decodePairInputs 19 limits [⟨2, 0, 3, 0⟩, ⟨3, 0, 7, 1⟩]).isNone do
    throw (IO.userError "invalid row silently dropped")
  unless checkRawPairs 5 2 limits 2 [⟨2, 0, 3, 0⟩] do
    throw (IO.userError "valid finite check rejected")
  for args in [(7, 2, 2), (5, 0, 2), (5, 1, 2), (5, 2, 1)] do
    if checkRawPairs args.1 args.2.1 limits args.2.2 [⟨2, 0, 3, 0⟩] then
      throw (IO.userError "flag or parameter guard bypassed")
end PseudoPrime.PrimeTest.APRCL.RawInputTests
/-- Run the raw APR-CL input regressions. -/
def main : IO Unit := PseudoPrime.PrimeTest.APRCL.RawInputTests.run
