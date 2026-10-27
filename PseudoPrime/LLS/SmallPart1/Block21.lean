/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SmallPart1.Block17

/-! # Finite original LLS Part 1 product checks for one 128-modulus block -/

@[expose] public section

namespace PseudoPrime.LLS.SmallPart1

/-- Exact integer product codes for this block.
Zero padding lies outside the target range. Every eligible code is checked below. -/
def block21Codes : Array ℕ :=
  #[172290, 34893837, 9689480587522, 9139724768275, 9139724511499, 35429763, 172674, 9552042667277,
    605819397, 101462021, 9552074912773, 9552075695875, 67929858, 11751199607303, 173186, 34908419,
    27144295287426, 34375431, 173447, 2540039741879622661, 173573, 36478853, 9277199887618,
    9552108722181, 9002353437954, 102507909, 173955, 2648134929130193923, 35447426, 87043, 34415362,
    9552042670213, 67667715, 34906371, 34922754, 2972385031362971523, 174595, 2720184276900643595,
    174723, 34384517, 35447685, 87429, 37032194, 2612097473423608069, 9552042165251, 85253,
    9689481111170, 9552076218883, 175362, 34894349, 103573762, 9552042150275, 9277333573378, 87811,
    34163207, 9552042146055, 175885, 169613571, 9552042156418, 9277164246019, 176131, 35417093,
    9552076226306, 10101831509763, 35448197, 36475651, 35473923, 741414149908007656098567,
    168312455, 88331, 103566469, 35433603, 9689547679490, 34894599, 177027, 9139759360771,
    9552042682626, 70010115, 34161667, 2648126545322051461, 34950530, 302780933, 9552076221698,
    9689481107075, 177667, 35419013, 101212933, 9552042673411, 103566466, 36478727, 370416514,
    2540039467036315141, 68979458, 101986691, 34138119, 9689581229061, 178434, 9689549770503,
    34430151, 9139724769031, 9139793960834, 35429763, 9964526245122, 10376676391429, 178946, 89485,
    36497538, 2648126270410067715, 179203, 38040709, 179330, 35434243, 2648126270407709703,
    34907399, 34941955, 2612097335984654597, 176386, 68961795, 34138629, 9002555279621, 67676165,
    9689549770885, 34412802, 9277164244995, 101207559, 90115, 180354, 2612097473357551367]

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block21_check_0 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2693 block21Codes) 4 0 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block21_check_1 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2693 block21Codes) 4 16 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block21_check_2 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2693 block21Codes) 4 32 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block21_check_3 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2693 block21Codes) 4 48 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block21_check_4 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2693 block21Codes) 4 64 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block21_check_5 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2693 block21Codes) 4 80 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block21_check_6 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2693 block21Codes) 4 96 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block21_check_7 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2693 block21Codes) 4 112 = true := by
  decide +kernel

/-- Input: a window index. Claim: that window passes all finite checks.
Proof: select one of the eight kernel proofs. Role: the generic block soundness input. -/
theorem block21_check (j : Fin 8) :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2693 block21Codes) 4 (16 * j.val) =
      true := by
  fin_cases j
  · exact block21_check_0
  · exact block21_check_1
  · exact block21_check_2
  · exact block21_check_3
  · exact block21_check_4
  · exact block21_check_5
  · exact block21_check_6
  · exact block21_check_7

end PseudoPrime.LLS.SmallPart1
