/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SmallPart1.Block19

/-! # Finite original LLS Part 1 product checks for one 128-modulus block -/

@[expose] public section

namespace PseudoPrime.LLS.SmallPart1

/-- Exact integer product codes for this block.
Zero padding lies outside the target range. Every eligible code is checked below. -/
def block23Codes : Array ℕ :=
  #[34928002, 36475139, 35476226, 2648126270374944263, 188941, 101987459, 9689515176194, 36485251,
    189186, 9277199358981, 34426626, 2504019878426183939, 9552109249154, 94723, 189570,
    2828270118098438405, 67671043, 94851, 9277163467653, 2540039741879101187, 189955,
    10101801102599, 190091, 34912643, 35452802, 95109, 9552074914819, 2540039467001191947,
    202651906, 95261, 102519429, 9552076219651, 171197314, 9964359005323, 101479682, 9277163724037,
    9552042681090, 95491, 34432258, 9552042671493, 101476610, 9964393079043, 34142471,
    2720183314691134467, 135027205, 35421317, 35465986, 9552042151811, 304880386, 95883, 191889, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block23_check_0 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2949 block23Codes) 4 0 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block23_check_1 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2949 block23Codes) 4 16 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block23_check_2 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2949 block23Codes) 4 32 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block23_check_3 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2949 block23Codes) 4 48 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block23_check_4 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2949 block23Codes) 4 64 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block23_check_5 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2949 block23Codes) 4 80 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block23_check_6 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2949 block23Codes) 4 96 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block23_check_7 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2949 block23Codes) 4 112 = true := by
  decide +kernel

/-- Input: a window index. Claim: that window passes all finite checks.
Proof: select one of the eight kernel proofs. Role: the generic block soundness input. -/
theorem block23_check (j : Fin 8) :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2949 block23Codes) 4 (16 * j.val) =
      true := by
  fin_cases j
  · exact block23_check_0
  · exact block23_check_1
  · exact block23_check_2
  · exact block23_check_3
  · exact block23_check_4
  · exact block23_check_5
  · exact block23_check_6
  · exact block23_check_7

end PseudoPrime.LLS.SmallPart1
