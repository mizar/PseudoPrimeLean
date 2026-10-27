/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SmallPart1.Block06

/-! # Finite original LLS Part 1 product checks for one 128-modulus block -/

@[expose] public section

namespace PseudoPrime.LLS.SmallPart1

/-- Exact integer product codes for this block.
Zero padding lies outside the target range. Every eligible code is checked below. -/
def block10Codes : Array ℕ :=
  #[67649539, 41099, 9277231337218, 2540039741879095427, 82443, 9552042661133, 82562, 9277164233731,
    35416965, 41349, 9689652529410, 9689481616133, 82961, 36980871, 34106373, 9552076214019, 83202,
    9964426102667, 83335, 9277164234883, 10101832029442, 41731, 83586, 9277164231435, 9689480313859,
    38027523, 9277164237186, 9689581226501, 67914498, 102502917, 35422978, 9964359000707, 38038917,
    42119, 84365, 713079987039861682210055, 84493, 42263, 101982082, 36983427, 68960514,
    9139762498567, 84867, 9277164235011, 35417730, 10376749254915, 77442, 9552109766917, 101987459,
    34884867, 9552074905095, 9277164235139, 36474499, 36976517, 101462786, 9689482666247, 34893570,
    171183879, 34905091, 2612097473357548549, 70533890, 43013, 34107405, 34362387, 35429762,
    36449549, 101462021, 9552041617159, 9139858704903, 43267, 34375426, 9552042662917, 34905986,
    101455877, 102507909, 2648134929063085059, 87043, 36452485, 34906370, 11338883270531,
    2720184139460117250, 43653, 87429, 2612097473423606917, 85250, 68952579, 34107917, 34883971,
    87810, 34879751, 168564994, 9277164235267, 34106373, 68429571, 34378498, 2612097473357548295,
    88322, 44163, 34894594, 9277164235523, 67650819, 9964428199813, 302518789, 34887299, 34894722,
    35407107, 36478722, 2540039467036313349, 101986691, 135009285, 9552109768450, 34363143,
    34119043, 39598597, 89485, 2648126270376513283, 38040706, 44803, 34907394, 9552109766917,
    67651075, 305400069, 9689548198018, 9277164234755, 90115, 9689482663687, 34120707, 34887683]

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block10_check_0 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1285 block10Codes) 4 0 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block10_check_1 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1285 block10Codes) 4 16 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block10_check_2 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1285 block10Codes) 4 32 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block10_check_3 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1285 block10Codes) 4 48 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block10_check_4 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1285 block10Codes) 4 64 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block10_check_5 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1285 block10Codes) 4 80 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block10_check_6 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1285 block10Codes) 4 96 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block10_check_7 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1285 block10Codes) 4 112 = true := by
  decide +kernel

/-- Input: a window index. Claim: that window passes all finite checks.
Proof: select one of the eight kernel proofs. Role: the generic block soundness input. -/
theorem block10_check (j : Fin 8) :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1285 block10Codes) 4 (16 * j.val) =
      true := by
  fin_cases j
  · exact block10_check_0
  · exact block10_check_1
  · exact block10_check_2
  · exact block10_check_3
  · exact block10_check_4
  · exact block10_check_5
  · exact block10_check_6
  · exact block10_check_7

end PseudoPrime.LLS.SmallPart1
