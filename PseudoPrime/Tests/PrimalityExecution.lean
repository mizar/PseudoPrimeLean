import PseudoPrime.PrimeTest.Execution
/-! # Cross-method primality execution regressions -/
namespace PseudoPrime.PrimeTest.Execution.Tests
/-- Small replay bounds shared with the APR-CL boundary regressions. -/
def limits : PrimeTest.APRCL.CertificateLimits := ⟨⟨32,4,16,8⟩,12,2⟩
/-- Cross-method result semantics, input boundaries, exhaustion and pending preservation. -/
def runTests : IO Unit := do
  for n in List.range 51 do
    let exactResult := PrimeTest.SmallInput.classify 50 n
    let filtered := decideByTest bailliePSW bailliePSW_spec_unconditional n
    if filtered.toOption == some false then
      unless exactResult.toOption == some false do
        throw (IO.userError "filter contradicted trial division")
    let combined := runBPSW 50 n [] (fun _ ↦ .unknown)
      (limits := limits) (fun _ ↦ .unknown)
    unless combined.toDecision.toOption == exactResult.toOption do
      throw (IO.userError "small-input integration mismatch")
  for n in [0,1,2] do
    let combined := runBPSW 0 n [] (fun _ ↦ .unknown)
      (limits := limits) (fun _ ↦ .unknown)
    unless combined.toDecision.toOption ==
        (PrimeTest.SmallInput.classify 2 n).toOption do
      throw (IO.userError "zero-budget domain boundary mismatch")
  unless (FactorWitness.decideMany 15
      [⟨⟨2,1⟩,10⟩]).toOption == some false do
    throw (IO.userError "rho factor did not refute primality")
  for n in [0,1,2,15,17] do
    unless (FactorWitness.decideMany n
        [⟨⟨2,1⟩,0⟩]).toOption == none do
      throw (IO.userError "zero rho fuel produced a decision")
  unless (decideByTest bailliePSW bailliePSW_spec_unconditional 13).toOption == none do
    throw (IO.userError "probable-prime acceptance promoted to proof")
  for n in [0,1,2,3,4,13] do
    let result := PrimeTest.BLS.resultOfInputCertificate n (.small n)
    let expected := if n < 2 then some false else if n ≤ 3 then some true else none
    unless result.toDecision.toOption == expected do
      throw (IO.userError "BLS result conversion mismatch")
  let blsPrime := runBPSW 2 3 []
    (fun _ ↦ PrimeTest.BLS.resultOfInputCertificate 3 (.small 3))
    (limits := limits) (fun _ ↦ .unknown)
  unless blsPrime.toDecision.toOption == some true do
    throw (IO.userError "BLS stage did not retain prime proof")
  let exhausted := runBPSW 2 13 []
    (fun _ ↦ PrimeTest.BLS.resultOfInputCertificate 13 (.small 3))
    (limits := limits) (fun _ ↦ .unknown)
  unless exhausted.toDecision.toOption == none do
    throw (IO.userError "rejected certificate became a negative conclusion")
  let pending := runBPSW 2 13 [] (fun _ ↦ .unknown)
    (fun _ ↦ PrimeTest.APRCL.runWithKnownDivisors
      2 13 limits ⟨32,2⟩ [2] [3,7])
  match pending with
  | .pending c _ =>
    unless PrimeTest.APRCL.verifyRawCertificate 13 limits c do
      throw (IO.userError "pending certificate lost")
    unless pending.toDecision.toOption == none do
      throw (IO.userError "pending acceptance promoted to proof")
  | _ => throw (IO.userError "APRCL fallback not reached")
end PseudoPrime.PrimeTest.Execution.Tests
/-- Run integration regressions without exporting them from a library root. -/
def main : IO Unit := PseudoPrime.PrimeTest.Execution.Tests.runTests
