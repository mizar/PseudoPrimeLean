/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SmallPart1.Block15

/-! # Finite original LLS Part 1 product checks for one 128-modulus block -/

@[expose] public section

namespace PseudoPrime.LLS.SmallPart1

/-- Exact integer product codes for this block.
Zero padding lies outside the target range. Every eligible code is checked below. -/
def block19Codes : Array ℕ :=
  #[155906, 34901763, 104088450, 2648126132969017095, 156171, 9689481620741, 101996290,
    9139724764423, 9552042676482, 78213, 156549, 2540039741913172997, 102523267, 38562051,
    9277231341442, 34380037, 34149763, 34891293, 34403586, 9552041626757, 27556612147458, 78595,
    157314, 2612097473391102471, 34939778, 78723, 34917634, 2612097473355980291, 18073290021891,
    36464133, 157826, 34904579, 34917762, 9552210430211, 38078467, 2612097473356503429, 158213,
    79109, 10101932691202, 34380423, 158466, 10101799529349, 101475074, 2612097335951101699,
    35442306, 135013381, 35462402, 9552042668421, 9552041634050, 35425283, 34918146, 9552042151299,
    34415746, 9689482668295, 34941698, 9552042148355, 106710274, 236197123, 36501767,
    2612096923634240523, 34937474, 79879, 9552041366533, 36470019, 336338439, 105128581, 160131,
    9139724766737, 9689481630466, 36472195, 34154763, 2612097473356502661, 201863173, 36470019,
    103564162, 9689514649347, 37031043, 36464773, 38075138, 9689514648579, 36491650, 80523,
    38083847, 713079987039861748794125, 161297, 204216325, 34917122, 37002627, 338434306, 34892055,
    101471618, 9552042151427, 34132491, 9689481623299, 161922, 9552042144903, 67671043, 101461271,
    9277199361794, 9552042151683, 34156675, 36988805, 162434, 9689482673923, 9964359012994,
    169614851, 162693, 2540039467036314885, 71597826, 102510979, 103564930, 9964425581829, 163074,
    9689515168779, 163219, 2540039467001193219, 9552042156802, 81667, 8933734093323, 9689481098375,
    163586, 81795, 35443970, 9552076218371, 67932930, 9139793956625, 34152963, 35430403]

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block19_check_0 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2437 block19Codes) 4 0 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block19_check_1 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2437 block19Codes) 4 16 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block19_check_2 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2437 block19Codes) 4 32 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block19_check_3 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2437 block19Codes) 4 48 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block19_check_4 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2437 block19Codes) 4 64 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block19_check_5 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2437 block19Codes) 4 80 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block19_check_6 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2437 block19Codes) 4 96 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block19_check_7 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2437 block19Codes) 4 112 = true := by
  decide +kernel

/-- Input: a window index. Claim: that window passes all finite checks.
Proof: select one of the eight kernel proofs. Role: the generic block soundness input. -/
theorem block19_check (j : Fin 8) :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2437 block19Codes) 4 (16 * j.val) =
      true := by
  fin_cases j
  · exact block19_check_0
  · exact block19_check_1
  · exact block19_check_2
  · exact block19_check_3
  · exact block19_check_4
  · exact block19_check_5
  · exact block19_check_6
  · exact block19_check_7

end PseudoPrime.LLS.SmallPart1
