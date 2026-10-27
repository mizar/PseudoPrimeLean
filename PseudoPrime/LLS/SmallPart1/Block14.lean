/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SmallPart1.Block10

/-! # Finite original LLS Part 1 product checks for one 128-modulus block -/

@[expose] public section

namespace PseudoPrime.LLS.SmallPart1

/-- Exact integer product codes for this block.
Zero padding lies outside the target range. Every eligible code is checked below. -/
def block14Codes : Array ℕ :=
  #[35427714, 36989187, 37011459, 2612097335917547277, 115211, 68957187, 34117127, 9689615829507,
    35433218, 9689549769349, 101467394, 9139760405507, 102510978, 68955395, 115881, 9552042665349,
    101990146, 57987, 10101798483714, 9277164238979, 34920067, 34884359, 34132995,
    2612097336091607811, 34903938, 58257, 116613, 2612097473356501509, 67656203, 35415685,
    9689548199170, 34370061, 34134403, 9689516216071, 117123, 9139724761351, 9277164242178,
    38035843, 34387714, 9552042664965, 34918274, 58759, 37001474, 2828270118064884483, 34915459,
    36457605, 104089605, 36991747, 9964391767559, 34892039, 118149, 713079987039861682210693,
    115587, 70528259, 34118149, 34894723, 67660803, 105126277, 9002321979138, 9277197786115,
    34904706, 59395, 34915074, 2648126270376513287, 119042, 101982083, 34903170, 9689481099779,
    67919106, 36457861, 119426, 34894979, 9139724501523, 9277199881219, 119699, 2612097336085316357,
    119845, 59909, 35421442, 9139793956995, 120066, 35409425, 120203, 2612097335917549315,
    9277231339138, 60163, 34392322, 9964359526149, 18073290282242, 34369031, 9552074908677,
    9552042146307, 120835, 10101866629389, 504106754, 9277164237955, 34119047, 60549, 36486402,
    2540039741879620485, 101467025, 205787653, 101987458, 9552042667267, 121602, 36458245, 34395906,
    2504010532578921475, 9552041361159, 60931, 121986, 9552042665733, 34922882, 35413763,
    9964426106114, 9277164239747, 122371, 9277164233491, 36486914, 36992899, 35429762, 38036995,
    35447042, 2612097473390053387, 270277635, 59523, 34119697, 9002454616325]

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block14_check_0 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1797 block14Codes) 4 0 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block14_check_1 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1797 block14Codes) 4 16 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block14_check_2 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1797 block14Codes) 4 32 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block14_check_3 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1797 block14Codes) 4 48 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block14_check_4 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1797 block14Codes) 4 64 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block14_check_5 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1797 block14Codes) 4 80 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block14_check_6 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1797 block14Codes) 4 96 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block14_check_7 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1797 block14Codes) 4 112 = true := by
  decide +kernel

/-- Input: a window index. Claim: that window passes all finite checks.
Proof: select one of the eight kernel proofs. Role: the generic block soundness input. -/
theorem block14_check (j : Fin 8) :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1797 block14Codes) 4 (16 * j.val) =
      true := by
  fin_cases j
  · exact block14_check_0
  · exact block14_check_1
  · exact block14_check_2
  · exact block14_check_3
  · exact block14_check_4
  · exact block14_check_5
  · exact block14_check_6
  · exact block14_check_7

end PseudoPrime.LLS.SmallPart1
