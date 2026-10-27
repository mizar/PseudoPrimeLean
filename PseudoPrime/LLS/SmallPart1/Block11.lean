/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SmallPart1.Block07

/-! # Finite original LLS Part 1 product checks for one 128-modulus block -/

@[expose] public section

namespace PseudoPrime.LLS.SmallPart1

/-- Exact integer product codes for this block.
Zero padding lies outside the target range. Every eligible code is checked below. -/
def block11Codes : Array ℕ :=
  #[103556866, 34884355, 35425539, 2540039741879619205, 201857797, 45329, 9277163451525,
    9552042664707, 235672834, 102503301, 91011, 9552075691523, 9552042667266, 34886275, 91266,
    2864299052490296325, 91403, 9964393074435, 36467970, 9277164235907, 91651, 35404677,
    9002319093259, 35412355, 36992898, 45963, 92039, 2612097473390052875, 169615490, 103553411,
    9277333571842, 35411331, 67650563, 34880519, 92547, 9139724758295, 9552109244546, 68952835,
    92802, 9689481616261, 92930, 46469, 9552074905607, 2612097336084792067, 34909315, 31109, 93315,
    9277197259275, 34896258, 36459523, 9139791861378, 2612097473355976455, 70011138, 46855,
    104081538, 34888587, 67654659, 10101799523601, 94087, 9552042142723, 34896514, 34361991,
    34377986, 9689481092615, 101463170, 47235, 9277196999685, 2504010670017874179, 94723,
    10789060348165, 94850, 9689481094915, 10101798481154, 47493, 95109, 2540039467001188107, 95261,
    68953347, 9552042144898, 34364677, 95490, 36453765, 9277197263106, 2720183452096009219,
    34110597, 34885507, 95874, 9552042662157, 102513282, 48003, 34897026, 9277164236291,
    9689547674882, 34881163, 34122243, 9277197784323, 34897282, 38030087, 96651,
    2612097335986226309, 135539715, 48389, 9277199358210, 36986499, 67656199, 9689481616261,
    103560323, 2540039741913172227, 102508290, 48647, 97410, 9964358999943, 336334594, 101456651,
    34897666, 9277164236675, 34385026, 9689516215303, 97922, 34889603, 9552108458501, 36460295,
    34117895, 9689481617413, 68442882, 49163, 303304066, 2828270667788717827]

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block11_check_0 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1413 block11Codes) 4 0 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block11_check_1 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1413 block11Codes) 4 16 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block11_check_2 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1413 block11Codes) 4 32 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block11_check_3 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1413 block11Codes) 4 48 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block11_check_4 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1413 block11Codes) 4 64 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block11_check_5 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1413 block11Codes) 4 80 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block11_check_6 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1413 block11Codes) 4 96 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block11_check_7 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1413 block11Codes) 4 112 = true := by
  decide +kernel

/-- Input: a window index. Claim: that window passes all finite checks.
Proof: select one of the eight kernel proofs. Role: the generic block soundness input. -/
theorem block11_check (j : Fin 8) :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1413 block11Codes) 4 (16 * j.val) =
      true := by
  fin_cases j
  · exact block11_check_0
  · exact block11_check_1
  · exact block11_check_2
  · exact block11_check_3
  · exact block11_check_4
  · exact block11_check_5
  · exact block11_check_6
  · exact block11_check_7

end PseudoPrime.LLS.SmallPart1
