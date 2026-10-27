/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SmallPart1.Block08

/-! # Finite original LLS Part 1 product checks for one 128-modulus block -/

@[expose] public section

namespace PseudoPrime.LLS.SmallPart1

/-- Exact integer product codes for this block.
Zero padding lies outside the target range. Every eligible code is checked below. -/
def block12Codes : Array ℕ :=
  #[370413698, 35405829, 98693, 9277163712517, 9552042668802, 49411, 9552209120259, 9964427676293,
    99074, 169611011, 9277164239234, 9964392028165, 99331, 10376744536325, 36477698, 35414275,
    35422466, 35412493, 99731, 713079987039861715239687, 103561091, 172757383, 34112007,
    9277164235779, 67653137, 34881291, 100227, 9552042142211, 36471426, 68953859, 100482,
    9964359524485, 34907394, 50309, 9689549770498, 9964359004419, 34388098, 35406213, 100995,
    9689482667779, 9552041360391, 36983811, 101253, 2648126270375464709, 68964098, 203165445,
    34897538, 34366213, 34384258, 9552079359239, 101465858, 9277164237187, 34898562, 50947,
    9002320405250, 2864299052557403269, 102155, 34888707, 9552074907143, 9552076215299, 102403,
    34882055, 101464322, 35415043, 9689481622786, 35412485, 102789, 2540039741879095431, 102919,
    10101799526659, 34899330, 9139791859463, 103171, 34882311, 9277197001731, 10101831506179,
    9964359005314, 51715, 103554, 9689482664711, 103682, 51843, 34899714, 2612097335917024515,
    67914498, 36979595, 104067, 9277163711749, 101985538, 36458755, 36482563, 2540039741980279813,
    34914439, 102506371, 9689513859847, 34367005, 104706, 27556613718789, 34388226,
    2540039192158407175, 35424386, 52483, 34128643, 9552042664453, 9552041624834, 52611, 101985538,
    9689480573701, 269228037, 10101935310087, 101203719, 9552042142595, 9552042147586, 52871,
    36480259, 2540039741879619717, 105995, 53011, 9964426105730, 9689482668291, 168306055, 39601413,
    106371, 9552075692035, 9552210430210, 36459523, 106626, 9964359524997]

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block12_check_0 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1541 block12Codes) 4 0 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block12_check_1 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1541 block12Codes) 4 16 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block12_check_2 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1541 block12Codes) 4 32 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block12_check_3 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1541 block12Codes) 4 48 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block12_check_4 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1541 block12Codes) 4 64 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block12_check_5 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1541 block12Codes) 4 80 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block12_check_6 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1541 block12Codes) 4 96 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block12_check_7 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1541 block12Codes) 4 112 = true := by
  decide +kernel

/-- Input: a window index. Claim: that window passes all finite checks.
Proof: select one of the eight kernel proofs. Role: the generic block soundness input. -/
theorem block12_check (j : Fin 8) :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 1541 block12Codes) 4 (16 * j.val) =
      true := by
  fin_cases j
  · exact block12_check_0
  · exact block12_check_1
  · exact block12_check_2
  · exact block12_check_3
  · exact block12_check_4
  · exact block12_check_5
  · exact block12_check_6
  · exact block12_check_7

end PseudoPrime.LLS.SmallPart1
