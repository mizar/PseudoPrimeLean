/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SmallPart1.Block09

/-! # Finite original LLS Part 1 product checks for one 128-modulus block -/

@[expose] public section

namespace PseudoPrime.LLS.SmallPart1

/-- Exact integer product codes for this block.
Zero padding lies outside the target range. Every eligible code is checked below. -/
def block13Codes : Array ℕ :=
  #[106754, 36983555, 36997890, 2612097061039117955, 37008003, 101979787, 36480258, 36464771,
    9552109769986, 53643, 37012997, 713079987039861715763979, 104967, 51971, 9689480313861,
    34367767, 67654675, 34883083, 101465101, 9552042144899, 36473986, 68953859, 34129411,
    9689481618053, 108290, 36983429, 9277196999697, 9139760404995, 108547, 36456069, 108675,
    10101833077763, 101984386, 35414789, 34915074, 2720183864412868999, 9689614520067, 54539,
    34115083, 9139791859473, 109315, 9552109766925, 34392834, 9689481098499, 34115205, 54787,
    34378498, 2720184139290775303, 67658755, 54915, 35425922, 2540039741879620867, 110083,
    9964358999563, 110211, 34368391, 9689481623298, 55173, 34128645, 9689481618437, 27144294762754,
    70003459, 34115589, 34368517, 110850, 35406853, 34385154, 2540039329630914435, 101199877,
    35414403, 34918146, 2648126270410065671, 111362, 101458183, 9552042147202, 9139760405251,
    67917570, 102504453, 111746, 9277164237187, 9964359008514, 38554371, 35441669,
    2540039741879620101, 112135, 56069, 9277335144706, 34368907, 34126723, 35408133, 112519,
    2612097473390053891, 36999810, 56323, 34132493, 9552111340165, 67655683, 56459, 9552109246082,
    2504010670015777795, 67922178, 9689482665223, 9139724767874, 34893443, 36999938, 56709,
    169616130, 2540039467036313861, 113669, 104079235, 34116613, 9552078837251, 67659267, 35406725,
    114059, 10101797959555, 2648126270407707659, 34891651, 114306, 9277164233995, 114451, 35412227,
    103559554, 9552042143747, 34392706, 9964359000327, 35435266, 35418115]

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block13_check_0 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1669 block13Codes) 4 0 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block13_check_1 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1669 block13Codes) 4 16 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block13_check_2 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1669 block13Codes) 4 32 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block13_check_3 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1669 block13Codes) 4 48 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block13_check_4 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1669 block13Codes) 4 64 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block13_check_5 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1669 block13Codes) 4 80 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block13_check_6 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1669 block13Codes) 4 96 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block13_check_7 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1669 block13Codes) 4 112 = true := by
  decide +kernel

/-- Input: a window index. Claim: that window passes all finite checks.
Proof: select one of the eight kernel proofs. Role: the generic block soundness input. -/
theorem block13_check (j : Fin 8) :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1669 block13Codes) 4 (16 * j.val) =
      true := by
  fin_cases j
  · exact block13_check_0
  · exact block13_check_1
  · exact block13_check_2
  · exact block13_check_3
  · exact block13_check_4
  · exact block13_check_5
  · exact block13_check_6
  · exact block13_check_7

end PseudoPrime.LLS.SmallPart1
