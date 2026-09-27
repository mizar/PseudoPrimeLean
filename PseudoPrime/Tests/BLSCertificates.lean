/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PrimeTest.BLS.CertificateGenerateJson

/-!
# BLS external-certificate regressions

Theorems check the arithmetic payloads in the kernel. The executable main checks
JSON replay and generation using the compiled runtime, without adding proof axioms.
-/

namespace PseudoPrime.PrimeTest.BLS.CertificateTests
/-- Regression for mismatched small input. -/
theorem mismatched_small_input : verifyInputCertificate 3 (.small 2) = false := by
  decide
/-- Regression for mismatched result unknown. -/
theorem mismatched_result_unknown : resultOfInputCertificate 3 (.small 2) = .unknown := by
  exact resultOfInputCertificate_of_rejected _ (by decide) (by decide)
/-- Regression for zero generation none. -/
theorem zero_generation_none : generateInputCertificate 0 .square ⟨2, 1⟩ 0 [] = none := by
  rfl
/-- Regression for one generation none. -/
theorem one_generation_none : generateInputCertificate 1 .bls5 ⟨2, 1⟩ 0 [] = none := by
  rfl
/-- A square-bound certificate for 13. -/
def testSquare : InputCertificate := .square ⟨13, ⟨[(2, 2)], 3⟩, [(2, 2)]⟩
/-- A cube certificate for 17 with F squared below the input. -/
def testCube : InputCertificate := .cube ⟨17, ⟨[(2, 2)], 4⟩, [(2, 3)]⟩
/-- A BLS5 certificate for 101 beyond the square and cube bounds. -/
def testBLS5 : InputCertificate := .bls5 ⟨101, ⟨[(2, 2)], 25⟩, [(2, 2)], 25⟩
/-- Regression for square payload accepts. -/
theorem square_payload_accepts : verifyInputCertificate 13 testSquare = true := by
  decide
/-- Regression for cube payload accepts. -/
theorem cube_payload_accepts : verifyInputCertificate 17 testCube = true := by
  decide
set_option maxRecDepth 4096 in
/-- Regression for bls5 payload accepts. -/
theorem bls5_payload_accepts : verifyInputCertificate 101 testBLS5 = true := by
  decide

/-- Check generation, JSON replay, input binding, size limits and tamper rejection at runtime. -/
def runInputCertificateRegression : IO Unit := do
  for method in [CertificateMethod.square, .cube, .bls5] do
    match generateCertificateJson 13 method ⟨2, 1⟩ 4 (List.range 13) with
    | none => throw (IO.userError "BLS JSON generation failed")
    | some j =>
      unless verifyCertificateText 13 4096 j.compress do
        throw (IO.userError "BLS JSON replay failed")
      if verifyCertificateText 17 4096 j.compress then
        throw (IO.userError "mismatched input accepted")
      if verifyCertificateText 13 0 j.compress then
        throw (IO.userError "text bound ignored")
  for c in [testSquare, testCube, testBLS5, .small 2, .small 3] do
    unless verifyCertificateText c.input 4096 (encodeInputCertificate c).compress do
      throw (IO.userError "method certificate replay failed")
  for text in ["{}", "not JSON",
      "{\"format\":\"bls-reference-v1\",\"n\":\"13\",\"method\":\"square\"," ++
        "\"factors\":[[\"2\",\"2\"]],\"witnesses\":[[\"2\",\"1\"]]}"] do
    if verifyCertificateText 13 4096 text then
      throw (IO.userError "invalid certificate accepted")


end PseudoPrime.PrimeTest.BLS.CertificateTests
/-- Run the compiled JSON and bounded-generation regressions. -/
def main : IO Unit :=
  PseudoPrime.PrimeTest.BLS.CertificateTests.runInputCertificateRegression
