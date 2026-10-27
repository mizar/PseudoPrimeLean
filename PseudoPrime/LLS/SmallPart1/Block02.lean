/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Part1ProductCertificates

/-! # Finite original LLS Part 1 product checks for one 128-modulus block -/

@[expose] public section

namespace PseudoPrime.LLS.SmallPart1

/-- Exact integer product codes for this block.
Zero padding lies outside the target range. Every eligible code is checked below. -/
def block02Codes : Array ℕ :=
  #[34870530, 8337, 16773, 2648126270375461509, 68947202, 101975171, 34084359, 34869383, 17154,
    36440327, 34349506, 9139759350787, 9964426101506, 8707, 168559874, 9552042657157, 17669, 8835,
    103548802, 2648126270376510211, 17923, 36965253, 18051, 35393923, 9552042658050, 34868999,
    34348555, 9689481610757, 17411, 68945667, 34084869, 34345477, 18690, 36440709, 34348290,
    9277163702533, 34870914, 9475, 34873602, 9552042657037, 101452418, 9607, 34871554,
    9277164226819, 67899138, 35392517, 19589, 9689481086851, 34871682, 35393283, 19857,
    2612097335917019911, 19985, 9989, 9689549767426, 36443011, 20226, 36441349, 34349826,
    9552076211203, 35396226, 34869379, 34087939, 35392901, 67899138, 10371, 34872075, 9689480563207,
    34873987, 10101801092359, 21123, 34870403, 103549186, 10629, 36446466, 2612097473357546245,
    21523, 9991, 34085893, 10101833073667, 168298371, 104072325, 18819, 9277164227203,
    9689481612034, 11011, 22146, 9277164226315, 22274, 38539011, 102500610, 9277164227075, 22531,
    36441733, 35398402, 36443651, 9552041348101, 11399, 22919, 2612097473357546247, 21890, 35395211,
    34872194, 9964425577221, 67637771, 34868999, 23435, 9552042134275, 34086407, 70519043, 34350850,
    9552042133383, 23810, 35394563, 35395842, 9277164227459, 67900674, 104072325, 24194,
    9552042658051, 34086791, 12179, 24453, 9689481611269, 9689480564482, 12293, 102500994, 34347013]

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block02_check_0 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 261 block02Codes) 4 0 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block02_check_1 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 261 block02Codes) 4 16 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block02_check_2 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 261 block02Codes) 4 32 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block02_check_3 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 261 block02Codes) 4 48 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block02_check_4 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 261 block02Codes) 4 64 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block02_check_5 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 261 block02Codes) 4 80 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block02_check_6 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 261 block02Codes) 4 96 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block02_check_7 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 261 block02Codes) 4 112 = true := by
  decide +kernel

/-- Input: a window index. Claim: that window passes all finite checks.
Proof: select one of the eight kernel proofs. Role: the generic block soundness input. -/
theorem block02_check (j : Fin 8) :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 261 block02Codes) 4 (16 * j.val) =
      true := by
  fin_cases j
  · exact block02_check_0
  · exact block02_check_1
  · exact block02_check_2
  · exact block02_check_3
  · exact block02_check_4
  · exact block02_check_5
  · exact block02_check_6
  · exact block02_check_7

end PseudoPrime.LLS.SmallPart1
