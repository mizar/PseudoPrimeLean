/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SmallPart1.Block13

/-! # Finite original LLS Part 1 product checks for one 128-modulus block -/

@[expose] public section

namespace PseudoPrime.LLS.SmallPart1

/-- Exact integer product codes for this block.
Zero padding lies outside the target range. Every eligible code is checked below. -/
def block17Codes : Array ℕ :=
  #[34125189, 69777, 34931970, 750859099046804005323525, 9552042681090, 69893, 93314, 34375813,
    34404226, 9964393075211, 101469713, 9139760407043, 9277163459589, 70147, 34396941,
    9964426104583, 129794, 101459717, 34125575, 2612097473490715907, 169620611, 38558603, 140933,
    9552042671875, 9689549772034, 70533, 141189, 2540039741879621125, 138373, 18348169235459,
    9277164245634, 9139793957763, 141570, 34888199, 34397442, 9277163717893, 34125959, 70915,
    34401538, 2612097335952673031, 142082, 169613571, 27968929007874, 9277164242179, 67661315,
    9689482667781, 34145283, 34900739, 34912642, 35417859, 36505605, 2540039329630914439,
    9139724773634, 71441, 9689515173122, 9277230814469, 143106, 38034693, 143235,
    2648126270410066947, 36485250, 36471427, 143490, 2648126270375465989, 67661827, 71811,
    9552042151810, 9277164242435, 67928322, 36457229, 144007, 34901123, 35437442, 34894723,
    9277465430531, 2720183864413394693, 202648834, 72203, 34913163, 9552076217347, 9552108463107,
    9139760403719, 101472779, 9552042149507, 9552041364231, 35422085, 145026, 9552111340933, 145154,
    36991235, 36486402, 9277164242435, 145411, 34889351, 9552209383170, 35425795, 9689481106050,
    36996103, 35459331, 713079951010652344813837, 145927, 106702979, 34127367, 36474499, 67662349,
    101982087, 146323, 2648125858091634435, 9964428204811, 68958467, 34410754, 10376676388753,
    146690, 101461261, 9689513862151, 2540039329561714187, 146949, 36986757, 34404226,
    9552042669827, 9277164246786, 73617, 34926979, 9689481621509, 70021890, 73733, 34127883,
    34377733]

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block17_check_0 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2181 block17Codes) 4 0 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block17_check_1 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2181 block17Codes) 4 16 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block17_check_2 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2181 block17Codes) 4 32 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block17_check_3 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2181 block17Codes) 4 48 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block17_check_4 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2181 block17Codes) 4 64 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block17_check_5 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2181 block17Codes) 4 80 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block17_check_6 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2181 block17Codes) 4 96 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block17_check_7 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2181 block17Codes) 4 112 = true := by
  decide +kernel

/-- Input: a window index. Claim: that window passes all finite checks.
Proof: select one of the eight kernel proofs. Role: the generic block soundness input. -/
theorem block17_check (j : Fin 8) :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2181 block17Codes) 4 (16 * j.val) =
      true := by
  fin_cases j
  · exact block17_check_0
  · exact block17_check_1
  · exact block17_check_2
  · exact block17_check_3
  · exact block17_check_4
  · exact block17_check_5
  · exact block17_check_6
  · exact block17_check_7

end PseudoPrime.LLS.SmallPart1
