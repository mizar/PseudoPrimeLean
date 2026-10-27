/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SmallPart1.Block04

/-! # Finite original LLS Part 1 product checks for one 128-modulus block -/

@[expose] public section

namespace PseudoPrime.LLS.SmallPart1

/-- Exact integer product codes for this block.
Zero padding lies outside the target range. Every eligible code is checked below. -/
def block08Codes : Array ℕ :=
  #[34883970, 34353927, 65957, 2612097473356499589, 66053, 35404165, 9689481617666, 9552108718341,
    67648517, 35400453, 66435, 2504020153304089347, 35411586, 33283, 34369282, 9277164229899,
    9277163711746, 33413, 34887426, 9964359000195, 67075, 10101799522065, 67207, 34881923,
    102505218, 34880515, 36989186, 2648126270375463429, 101983619, 32389, 34101253, 9552076213507,
    67842, 36449157, 67971, 2540039741946201219, 9964359525122, 67902983, 34109445, 9552042137095,
    68359, 35403011, 9552108456965, 9277164232971, 67911426, 35400837, 36989187, 36455171, 35412354,
    36975747, 35420930, 2612097473357547783, 35421829, 34573, 34887042, 34358151, 9552108719874,
    34876695, 69507, 9139960677379, 34886274, 69999363, 69762, 2828270530416345861, 69893, 34949,
    9964391764491, 9552042140163, 70147, 101977863, 101459714, 9689615828227, 34888578, 36454147,
    70533, 2540039741879618309, 18073290017795, 104076163, 34101767, 34358533, 70914, 9552077785351,
    168564994, 9277164233347, 9552042141442, 35587, 34107139, 9139793954695, 71426, 101455109,
    38034690, 2648126270410065411, 34374274, 9689481614341, 71810, 35407363, 35408642, 35973,
    34894723, 2720183864413391749, 72203, 68951043, 9277197784322, 34883203, 34373506, 104074629,
    34369794, 9277164233475, 34889346, 36355, 34112519, 2720183726974437645, 101984386, 36483,
    101195655, 2648125720618602247, 67647747, 35401617, 101461250, 9689480568331, 34889602,
    35403523, 73617, 9689481615365, 73733, 36869, 2648126545254944514, 34882563]

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block08_check_0 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1029 block08Codes) 4 0 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block08_check_1 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1029 block08Codes) 4 16 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block08_check_2 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1029 block08Codes) 4 32 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block08_check_3 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1029 block08Codes) 4 48 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block08_check_4 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1029 block08Codes) 4 64 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block08_check_5 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1029 block08Codes) 4 80 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block08_check_6 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1029 block08Codes) 4 96 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block08_check_7 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1029 block08Codes) 4 112 = true := by
  decide +kernel

/-- Input: a window index. Claim: that window passes all finite checks.
Proof: select one of the eight kernel proofs. Role: the generic block soundness input. -/
theorem block08_check (j : Fin 8) :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1029 block08Codes) 4 (16 * j.val) =
      true := by
  fin_cases j
  · exact block08_check_0
  · exact block08_check_1
  · exact block08_check_2
  · exact block08_check_3
  · exact block08_check_4
  · exact block08_check_5
  · exact block08_check_6
  · exact block08_check_7

end PseudoPrime.LLS.SmallPart1
