/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SmallPart1.Block05

/-! # Finite original LLS Part 1 product checks for one 128-modulus block -/

@[expose] public section

namespace PseudoPrime.LLS.SmallPart1

/-- Exact integer product codes for this block.
Zero padding lies outside the target range. Every eligible code is checked below. -/
def block09Codes : Array ℕ :=
  #[67650051, 36974597, 101461250, 2540039741913171715, 102506370, 34880899, 74373, 9689481615365,
    67648003, 35406083, 34889986, 9552075166213, 34897027, 10101967291143, 74882, 34883843,
    10101797170181, 37509, 36467458, 2612097473357548165, 34899074, 103552643, 34890114,
    9964360572163, 75527, 36974853, 101459714, 9277197783555, 9552042665730, 37891, 75906,
    9689481614981, 67651079, 10101833075715, 35414789, 9277164233987, 76291, 36450711, 35419906,
    9964358476039, 27144295285890, 38279, 35424013, 2612097473390052619, 76811, 38407, 34104333,
    9689548196483, 67648519, 102502533, 35425283, 9552041616773, 9552109768450, 34354951, 34373890,
    10101797951751, 77570, 38787, 35410178, 9277164233731, 77827, 9689481090315, 34901762,
    9552075165447, 9689481096450, 34882823, 78213, 2540039741879618565, 34367746, 39173, 34104861,
    34360453, 78594, 9964394121735, 78723, 2612097473355976451, 34104837, 39427, 9277333571842,
    9964359522693, 79106, 39563, 10101797956482, 2612097335917547267, 135013381, 35402117, 34114563,
    36457859, 9552042666242, 34882051, 236197123, 2612096923634238987, 79879, 32003, 105652866,
    34360849, 34375042, 9689481614981, 34110723, 9689480570629, 34891906, 68428803, 80514,
    2648126545321526029, 201857029, 40323, 34892034, 9552042141443, 9277163714306, 34878599,
    101985538, 34885379, 34891650, 36978435, 169614851, 2540039741879618821, 101986690, 101455109,
    9689513858059, 9689481618179, 81666, 34878599, 81795, 9552076214275, 9139794480898, 40963,
    82050, 10101798476421]

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block09_check_0 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1157 block09Codes) 4 0 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block09_check_1 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1157 block09Codes) 4 16 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block09_check_2 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1157 block09Codes) 4 32 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block09_check_3 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1157 block09Codes) 4 48 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block09_check_4 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1157 block09Codes) 4 64 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block09_check_5 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1157 block09Codes) 4 80 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block09_check_6 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1157 block09Codes) 4 96 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block09_check_7 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1157 block09Codes) 4 112 = true := by
  decide +kernel

/-- Input: a window index. Claim: that window passes all finite checks.
Proof: select one of the eight kernel proofs. Role: the generic block soundness input. -/
theorem block09_check (j : Fin 8) :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1157 block09Codes) 4 (16 * j.val) =
      true := by
  fin_cases j
  · exact block09_check_0
  · exact block09_check_1
  · exact block09_check_2
  · exact block09_check_3
  · exact block09_check_4
  · exact block09_check_5
  · exact block09_check_6
  · exact block09_check_7

end PseudoPrime.LLS.SmallPart1
