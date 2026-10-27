/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SmallPart1.Block12

/-! # Finite original LLS Part 1 product checks for one 128-modulus block -/

@[expose] public section

namespace PseudoPrime.LLS.SmallPart1

/-- Exact integer product codes for this block.
Zero padding lies outside the target range. Every eligible code is checked below. -/
def block16Codes : Array ℕ :=
  #[131330, 101459717, 9277197001229, 9277164240899, 34135045, 36456837, 236724994, 9552041620231,
    101988610, 65957, 131973, 2612097473356502277, 9552041629442, 66053, 9552076220162,
    9277164239235, 132354, 9689482666247, 302521099, 2612097335983606021, 34122893, 68959237,
    34393346, 9552042666757, 101470850, 66435, 9964426106498, 2504020153304090115, 133123, 35411589,
    133250, 36471299, 9552042673410, 34893571, 133509, 2540039467001189643, 133639, 9689481620739,
    8933668033541, 34374277, 9139791864066, 34887431, 34394370, 9964359008515, 34123269, 67075,
    134274, 2648126270376513297, 169619330, 67207, 34909954, 9689481101699, 67922178, 102505221,
    705432194, 9277164239875, 9552310569218, 36989187, 135047, 2648126270375465989, 135173,
    101983619, 9552042673410, 34897539, 67665413, 35411973, 101470466, 2612097335951101187,
    9689481104130, 67843, 34140165, 9552042666885, 67658755, 67971, 34910466, 2540039741946202371,
    136195, 9964360573703, 136322, 9964392029703, 102513282, 35420165, 9552209383170,
    2540039741879096839, 136727, 68359, 9552041366151, 9552042669315, 136962, 10926500875269,
    137091, 9277164241419, 2648125858094780162, 68435715, 34143235, 10101798481029, 101207173,
    36989187, 35435138, 9552042148611, 137731, 35412357, 34133767, 9689481098371, 36483970,
    34896647, 36502531, 2612097473391102215, 138263, 35421829, 9552109246850, 34375437, 67660807,
    36984197, 34403586, 9139724764039, 101989383, 10101866630915, 34928898, 9552042142999, 67666439,
    69507, 10101832033026, 9139960678403, 36497539, 35410565, 139399, 10376710986499]

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block16_check_0 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2053 block16Codes) 4 0 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block16_check_1 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2053 block16Codes) 4 16 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block16_check_2 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2053 block16Codes) 4 32 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block16_check_3 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2053 block16Codes) 4 48 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block16_check_4 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2053 block16Codes) 4 64 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block16_check_5 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2053 block16Codes) 4 80 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block16_check_6 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2053 block16Codes) 4 96 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block16_check_7 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2053 block16Codes) 4 112 = true := by
  decide +kernel

/-- Input: a window index. Claim: that window passes all finite checks.
Proof: select one of the eight kernel proofs. Role: the generic block soundness input. -/
theorem block16_check (j : Fin 8) :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2053 block16Codes) 4 (16 * j.val) =
      true := by
  fin_cases j
  · exact block16_check_0
  · exact block16_check_1
  · exact block16_check_2
  · exact block16_check_3
  · exact block16_check_4
  · exact block16_check_5
  · exact block16_check_6
  · exact block16_check_7

end PseudoPrime.LLS.SmallPart1
