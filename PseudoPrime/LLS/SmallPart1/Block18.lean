/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SmallPart1.Block14

/-! # Finite original LLS Part 1 product checks for one 128-modulus block -/

@[expose] public section

namespace PseudoPrime.LLS.SmallPart1

/-- Exact integer product codes for this block.
Zero padding lies outside the target range. Every eligible code is checked below. -/
def block18Codes : Array ℕ :=
  #[147714, 2828270667788717841, 147843, 9277164241923, 34127877, 68436483, 34400002, 9689481621509,
    101208707, 101461265, 35438850, 2504019878426183427, 171193474, 103554949, 34935554,
    9552042147203, 9552175566599, 74373, 34933506, 2612097473356503045, 136070147, 68958723,
    27144295287042, 9277164241155, 149250, 34890007, 34400514, 9552142275077, 9139724507661,
    34897027, 149634, 2720184276899070727, 149767, 74917, 9277298446722, 9277164243203,
    9552108724482, 10101798480901, 150147, 34902659, 34913538, 36467459, 150413,
    2612097473357550853, 204221698, 35423365, 9277197002513, 9552109770371, 150786, 38035845,
    101471237, 2612097335917550851, 36488322, 75527, 34149379, 9689481621765, 9689480325379,
    101459717, 34915458, 9277197788163, 34412677, 9689482667783, 151682, 34903043, 9689480320005,
    75909, 35447042, 2648126270375466629, 152069, 67913223, 9277332000514, 2720184276764855299,
    152323, 35414789, 152453, 9277197788419, 9552076220162, 76291, 9140194510722, 9552042144135,
    152834, 35419907, 35440386, 2612097335916503303, 153091, 27281735812229, 37023490, 35427715,
    9277163461637, 35424013, 153483, 2612097473390053899, 131715, 76811, 34129415, 34379271,
    18073424496898, 34890765, 34414338, 2540039741946202755, 9964358228485, 67910663, 154257,
    9552109768837, 302784386, 35425283, 2828270255471337730, 9552041626373, 154627, 9552109244167,
    34152967, 9689480574727, 34916610, 36471043, 155013, 2648126270374942983, 67663885, 77573,
    34130443, 34903939, 34407298, 36458759, 9139758054403, 9277164242947, 34130565, 77827, 34403074,
    2612097473355977995]

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block18_check_0 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2309 block18Codes) 4 0 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block18_check_1 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2309 block18Codes) 4 16 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block18_check_2 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2309 block18Codes) 4 32 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block18_check_3 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2309 block18Codes) 4 48 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block18_check_4 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2309 block18Codes) 4 64 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block18_check_5 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2309 block18Codes) 4 80 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block18_check_6 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2309 block18Codes) 4 96 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block18_check_7 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2309 block18Codes) 4 112 = true := by
  decide +kernel

/-- Input: a window index. Claim: that window passes all finite checks.
Proof: select one of the eight kernel proofs. Role: the generic block soundness input. -/
theorem block18_check (j : Fin 8) :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2309 block18Codes) 4 (16 * j.val) =
      true := by
  fin_cases j
  · exact block18_check_0
  · exact block18_check_1
  · exact block18_check_2
  · exact block18_check_3
  · exact block18_check_4
  · exact block18_check_5
  · exact block18_check_6
  · exact block18_check_7

end PseudoPrime.LLS.SmallPart1
