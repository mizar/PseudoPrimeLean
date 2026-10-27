/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SmallPart1.Block03

/-! # Finite original LLS Part 1 product checks for one 128-modulus block -/

@[expose] public section

namespace PseudoPrime.LLS.SmallPart1

/-- Exact integer product codes for this block.
Zero padding lies outside the target range. Every eligible code is checked below. -/
def block07Codes : Array ℕ :=
  #[67646467, 169609731, 9552109243010, 9552042138627, 67906818, 35399045, 57986, 34879619,
    34884354, 9552216720131, 58257, 2612097473356499205, 34891394, 29197, 9277199355650, 34355463,
    34365826, 35398661, 58759, 2828270118031330051, 36457605, 29443, 35416322, 2648126545254942597,
    67906818, 29571, 103553410, 9277197782531, 59395, 9689482661639, 101457794, 34880003, 36457858,
    29829, 9277196997635, 2612097335984653061, 59909, 103551107, 34098705, 9964360570627, 60162,
    35399429, 34369031, 9552042138883, 9689549768962, 35402883, 60546, 9552042660741, 201855493,
    35400963, 36458242, 2540039741879094275, 60931, 36448005, 35413762, 35404675, 9277164233474,
    30605, 38036995, 2612097473390052363, 59523, 203163909, 35409794, 34356231, 67645457,
    10101799522437, 61829, 9277163707269, 9277163447301, 67901447, 62091, 35399813, 101982850,
    31107, 9277199355650, 9002320400133, 62467, 34875527, 34106883, 10101799523587, 108272395,
    31367, 62853, 2648126270374939143, 68956418, 68426755, 9552042140290, 9277230811397, 34894723,
    10101801094919, 63367, 9277164232195, 34099845, 36451459, 34366210, 9552042660997, 63751, 31879,
    304875778, 9552042662147, 9139791859458, 36448645, 34108419, 36454019, 9552042664194, 32133,
    34895106, 2612097335986225925, 64523, 69998851, 34100243, 9277164231555, 64771, 34875143,
    9002321450242, 9277164232579, 34100229, 32515, 65154, 2648126270410064903, 65311, 101454341,
    9689614518149, 34881539, 336071171, 305398917, 105129730, 34881539]

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block07_check_0 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 901 block07Codes) 4 0 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block07_check_1 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 901 block07Codes) 4 16 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block07_check_2 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 901 block07Codes) 4 32 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block07_check_3 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 901 block07Codes) 4 48 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block07_check_4 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 901 block07Codes) 4 64 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block07_check_5 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 901 block07Codes) 4 80 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block07_check_6 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 901 block07Codes) 4 96 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block07_check_7 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 901 block07Codes) 4 112 = true := by
  decide +kernel

/-- Input: a window index. Claim: that window passes all finite checks.
Proof: select one of the eight kernel proofs. Role: the generic block soundness input. -/
theorem block07_check (j : Fin 8) :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 901 block07Codes) 4 (16 * j.val) =
      true := by
  fin_cases j
  · exact block07_check_0
  · exact block07_check_1
  · exact block07_check_2
  · exact block07_check_3
  · exact block07_check_4
  · exact block07_check_5
  · exact block07_check_6
  · exact block07_check_7

end PseudoPrime.LLS.SmallPart1
