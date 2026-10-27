/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SmallPart1.Block02

/-! # Finite original LLS Part 1 product checks for one 128-modulus block -/

@[expose] public section

namespace PseudoPrime.LLS.SmallPart1

/-- Exact integer product codes for this block.
Zero padding lies outside the target range. Every eligible code is checked below. -/
def block06Codes : Array ℕ :=
  #[49410, 103549573, 168300291, 9964358473733, 9552109242626, 24835, 34101773, 2720184276764852999,
    169611650, 34876419, 34881282, 9552042136835, 67643139, 38019205, 50306, 34877699, 34881922,
    36972291, 36983811, 2648126270375462789, 202641154, 25349, 9552076213506, 35402115, 50946,
    9689549767813, 34888707, 9552076212739, 34095623, 25603, 34101765, 9552042135687, 9552041615618,
    101453575, 34882306, 10101797951747, 51715, 36444935, 51843, 9964358997251, 36979586, 35400965,
    36458754, 2540039741913170949, 101982082, 26141, 27556612145922, 9689516214791, 52482, 36446725,
    52611, 9689480567173, 10101932688642, 36449155, 52866, 9552042659973, 52994, 36972803, 39601413,
    9552075688963, 36459523, 38019717, 36983554, 9964359521923, 103552642, 26763, 53643,
    713079987039586803778321, 51970, 26903, 34096651, 36451459, 67905282, 36971141, 34361986,
    9139760401667, 36456069, 69997571, 34890498, 9689481089415, 54530, 101453585, 9552109766914,
    9689481091715, 54787, 10376675856135, 54914, 9689482663171, 9139724492299, 27527, 55173,
    9689481613829, 70003458, 27653, 34096133, 9689549768579, 34365826, 10101833074439, 101458178,
    9139724753675, 101193733, 34877827, 34360066, 9552042660357, 56066, 28049, 35408130,
    2612097473390052611, 56323, 104073861, 56450, 9277197782019, 9689481616642, 28293, 56709,
    2540039741879617797, 104079235, 71570947, 34882434, 34879363, 34891650, 34874635, 34363650,
    9552042137603, 9277164232962, 28675, 34105603, 9552042659597]

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block06_check_0 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 773 block06Codes) 4 0 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block06_check_1 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 773 block06Codes) 4 16 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block06_check_2 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 773 block06Codes) 4 32 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block06_check_3 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 773 block06Codes) 4 48 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block06_check_4 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 773 block06Codes) 4 64 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block06_check_5 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 773 block06Codes) 4 80 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block06_check_6 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 773 block06Codes) 4 96 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block06_check_7 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 773 block06Codes) 4 112 = true := by
  decide +kernel

/-- Input: a window index. Claim: that window passes all finite checks.
Proof: select one of the eight kernel proofs. Role: the generic block soundness input. -/
theorem block06_check (j : Fin 8) :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 773 block06Codes) 4 (16 * j.val) =
      true := by
  fin_cases j
  · exact block06_check_0
  · exact block06_check_1
  · exact block06_check_2
  · exact block06_check_3
  · exact block06_check_4
  · exact block06_check_5
  · exact block06_check_6
  · exact block06_check_7

end PseudoPrime.LLS.SmallPart1
