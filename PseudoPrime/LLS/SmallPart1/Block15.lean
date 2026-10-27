/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SmallPart1.Block11

/-! # Finite original LLS Part 1 product checks for one 128-modulus block -/

@[expose] public section

namespace PseudoPrime.LLS.SmallPart1

/-- Exact integer product codes for this block.
Zero padding lies outside the target range. Every eligible code is checked below. -/
def block15Codes : Array ℕ :=
  #[9689614782210, 35409797, 34924039, 9139724762119, 37003403, 67907601, 123522,
    2648126270376513669, 123653, 61829, 9689548723458, 9277163714309, 67923714, 9689481618437,
    101467394, 9552075167751, 34906498, 62091, 34924290, 9689481619589, 68968706, 101982851,
    9277164243074, 34896259, 124674, 10101832027915, 124803, 9002320403973, 27144295286658, 62467,
    9277197003779, 9552042141831, 101469314, 35417603, 36479746, 2648126270376514819, 67925250,
    108272395, 101468933, 34372231, 9552042672386, 62853, 34918915, 2648126270408493575, 37019266,
    68956419, 303829509, 9277197786115, 126210, 9689482666629, 34390786, 2504010670048807173,
    34907266, 34894723, 126594, 2648126545254944519, 101467778, 63367, 34907394, 9277164239875,
    67658499, 35410565, 127106, 9552042144899, 9277331213317, 35414787, 171191554,
    2540039741879620741, 127493, 63751, 2612097473424656642, 36994183, 127746, 304875781, 127875,
    9552076216579, 9277164244226, 9964425580293, 128133, 9552042666373, 67658755, 36467715,
    101988226, 9552042147459, 34394635, 10788994294023, 128643, 34897283, 9689615306498, 34895107,
    10101965197058, 2612097335986226693, 129029, 64523, 34121733, 10101833079043, 34926979,
    34886675, 36490243, 2540039467001191299, 35424002, 64771, 129666, 9552042141447, 129794,
    10101833078019, 35432706, 9277164240643, 34401922, 36459525, 9277197266178, 36470531,
    10376745064453, 65159, 130439, 741414185936804708615175, 204220162, 65311, 36481410,
    10376742441477, 67659293, 9689615828869, 370415107, 34897923, 35433093, 338430467, 34396930,
    9689750045829]

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block15_check_0 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1925 block15Codes) 4 0 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block15_check_1 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1925 block15Codes) 4 16 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block15_check_2 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1925 block15Codes) 4 32 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block15_check_3 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1925 block15Codes) 4 48 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block15_check_4 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1925 block15Codes) 4 64 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block15_check_5 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1925 block15Codes) 4 80 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block15_check_6 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1925 block15Codes) 4 96 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block15_check_7 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1925 block15Codes) 4 112 = true := by
  decide +kernel

/-- Input: a window index. Claim: that window passes all finite checks.
Proof: select one of the eight kernel proofs. Role: the generic block soundness input. -/
theorem block15_check (j : Fin 8) :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1925 block15Codes) 4 (16 * j.val) =
      true := by
  fin_cases j
  · exact block15_check_0
  · exact block15_check_1
  · exact block15_check_2
  · exact block15_check_3
  · exact block15_check_4
  · exact block15_check_5
  · exact block15_check_6
  · exact block15_check_7

end PseudoPrime.LLS.SmallPart1
