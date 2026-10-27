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
def block00Codes : Array ℕ :=
  #[258, 133, 387, 34865283, 386, 259, 642, 35389573, 770, 387, 35389698, 34865411, 1027, 389, 1154,
    36438275, 34865538, 647, 1413, 9689481609349, 1282, 775, 1154, 34865539, 1794, 36438279, 1923,
    34865667, 34865794, 1027, 34341634, 35389829, 2306, 1155, 35390210, 9552042656003, 2567,
    36438405, 2691, 35390083, 35390210, 1413, 2949, 9689481609477, 2691, 1283, 34079749, 34341639,
    3330, 1157, 34342146, 9552042131843, 34866306, 1795, 3714, 9689482658055, 3842, 1923, 101974402,
    34866179, 67896066, 35390085, 4226, 34866179, 34866562, 38535939, 4487, 9689481609605, 4613,
    2309, 35390722, 35390595, 34342786, 34865927, 4995, 9552076210435, 3458, 2567, 5250,
    9689482658181, 67634179, 2691, 34866946, 9277164225155, 5635, 36438791, 101450498, 34866563,
    34080651, 2949, 35391746, 9689481609733, 6149, 2691, 34867074, 36439299, 6402, 35390469, 6533,
    9552041607943, 9689482658562, 3331, 6786, 35390597, 6923, 35390723, 36440322, 9552042132227,
    7171, 36963461, 35392258, 35391235, 102499074, 3723, 36441091, 2612097473357545735, 7042, 3847,
    34081287, 35391363, 6402, 104071557, 8067, 34867203, 35392133, 68944643, 8322, 9689481609861]

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block00_check_0 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 5 block00Codes) 4 0 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block00_check_1 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 5 block00Codes) 4 16 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block00_check_2 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 5 block00Codes) 4 32 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block00_check_3 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 5 block00Codes) 4 48 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block00_check_4 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 5 block00Codes) 4 64 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block00_check_5 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 5 block00Codes) 4 80 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block00_check_6 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 5 block00Codes) 4 96 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block00_check_7 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 5 block00Codes) 4 112 = true := by
  decide +kernel

/-- Input: a window index. Claim: that window passes all finite checks.
Proof: select one of the eight kernel proofs. Role: the generic block soundness input. -/
theorem block00_check (j : Fin 8) :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 5 block00Codes) 4 (16 * j.val) =
      true := by
  fin_cases j
  · exact block00_check_0
  · exact block00_check_1
  · exact block00_check_2
  · exact block00_check_3
  · exact block00_check_4
  · exact block00_check_5
  · exact block00_check_6
  · exact block00_check_7

end PseudoPrime.LLS.SmallPart1
