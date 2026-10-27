/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SmallPart1.Block18

/-! # Finite original LLS Part 1 product checks for one 128-modulus block -/

@[expose] public section

namespace PseudoPrime.LLS.SmallPart1

/-- Exact integer product codes for this block.
Zero padding lies outside the target range. Every eligible code is checked below. -/
def block22Codes : Array ℕ :=
  #[26731977903874, 34907139, 34925314, 9277164247043, 67668995, 102508293, 34160643,
    10101797964547, 9139724512775, 35425539, 36523266, 2540039741879622917, 181253, 204217093,
    9689549773570, 34386193, 181506, 9689481622661, 34950147, 2540039741879624451, 35449986,
    236197123, 181890, 9552109769605, 67669507, 91011, 9277331214853, 9552142800387, 9002353437954,
    9552042667277, 182402, 9277164245635, 36498690, 91269, 37035267, 750858918902543965490181,
    182795, 91403, 34139653, 2648126545286926083, 183042, 36467973, 101475851, 9277164247299,
    9689481633538, 91651, 34953474, 9552042670981, 101216387, 10101830983179, 9277164251394,
    9277164247427, 67673091, 36992901, 35459842, 36483971, 9964358231557, 92039, 184199,
    2612097473390054411, 104100738, 172236935, 34138251, 9552109246851, 67670023, 9552210430213,
    184709, 9277164246403, 35450498, 70009859, 34418818, 9689481100295, 34948994, 92547,
    9277197004817, 9139759361283, 185347, 10101867155589, 101478146, 9552076219139, 34926978, 92807,
    185733, 2648126270375467909, 9689480592130, 92957, 9277230556165, 34387333, 186114,
    9552079362055, 169625091, 2612097336084792835, 34140805, 34909315, 9002320412930, 35420549,
    186629, 93315, 9552109249154, 2540039467034219019, 34953859, 35420555, 101479682, 9552042152963,
    9277335146242, 9689548199555, 187269, 2612097473390055173, 68988674, 70011139, 34141189,
    34387719, 34421122, 101984391, 34415874, 9689481108363, 9139724512775, 68441091, 188034,
    2648126270376514833, 67677187, 94087, 309598987, 9552042153987, 9277230820610, 35420805,
    102000898, 9139724767879]

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block22_check_0 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2821 block22Codes) 4 0 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block22_check_1 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2821 block22Codes) 4 16 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block22_check_2 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2821 block22Codes) 4 32 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block22_check_3 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2821 block22Codes) 4 48 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block22_check_4 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2821 block22Codes) 4 64 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block22_check_5 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2821 block22Codes) 4 80 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block22_check_6 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2821 block22Codes) 4 96 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block22_check_7 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2821 block22Codes) 4 112 = true := by
  decide +kernel

/-- Input: a window index. Claim: that window passes all finite checks.
Proof: select one of the eight kernel proofs. Role: the generic block soundness input. -/
theorem block22_check (j : Fin 8) :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2821 block22Codes) 4 (16 * j.val) =
      true := by
  fin_cases j
  · exact block22_check_0
  · exact block22_check_1
  · exact block22_check_2
  · exact block22_check_3
  · exact block22_check_4
  · exact block22_check_5
  · exact block22_check_6
  · exact block22_check_7

end PseudoPrime.LLS.SmallPart1
