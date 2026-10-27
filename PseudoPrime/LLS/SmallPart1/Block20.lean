/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SmallPart1.Block16

/-! # Finite original LLS Part 1 product checks for one 128-modulus block -/

@[expose] public section

namespace PseudoPrime.LLS.SmallPart1

/-- Exact integer product codes for this block.
Zero padding lies outside the target range. Every eligible code is checked below. -/
def block20Codes : Array ℕ :=
  #[9552311093506, 82053, 34417669, 2648126270375467653, 103570307, 70533123, 34133509, 34381959,
    34157443, 10376743489285, 34406146, 2540039741879099651, 34920066, 82443, 164994,
    2612097335917548813, 67672579, 82563, 9139791601163, 2504010669982229507, 9689480590082,
    35416965, 103572226, 34906499, 34920322, 10101967816963, 165767, 9689481623045, 165895, 82961,
    9277199362818, 9689481627779, 34410754, 35417093, 34944003, 2612097335951101699, 34130949,
    83203, 34157059, 2612097473423083403, 67666435, 83335, 9277164249474, 9277164245251, 166915,
    10101833078023, 101473538, 34906883, 10101868208386, 83589, 35456258, 2540039467001191179,
    167429, 10376677964803, 101206021, 9964360581379, 167682, 9689481621893, 101476610,
    9689581229061, 9689482676994, 68438787, 35470082, 9552109769221, 35465602, 35422979, 37018370,
    2612097335917027971, 168451, 38038917, 9277197007875, 35431555, 35445506, 84365, 10101965198594,
    713079987039861715764487, 104097666, 84493, 34135057, 34383127, 35454210, 104079237, 169347,
    9689481106051, 35445890, 68960515, 168311815, 2504010532580494343, 101998210, 84867,
    9689481631490, 9277164245507, 169987, 35417733, 170114, 2720184139359455491, 34921858, 77447,
    170373, 2540039741946726661, 17798412115463, 101987459, 9689548201867, 9277164244227, 67673091,
    9552078837255, 170887, 9277164245763, 34916994, 36474499, 34408706, 9689481623429, 171266,
    101462789, 9964359018370, 2540039741878575367, 34938499, 34893579, 171650, 9002422636295,
    9552042678530, 34905091, 171909, 2612097473357551621, 172051, 70533891, 9277231341826, 34383877]

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block20_check_0 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2565 block20Codes) 4 0 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block20_check_1 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2565 block20Codes) 4 16 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block20_check_2 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2565 block20Codes) 4 32 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block20_check_3 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2565 block20Codes) 4 48 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block20_check_4 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2565 block20Codes) 4 64 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block20_check_5 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2565 block20Codes) 4 80 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block20_check_6 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2565 block20Codes) 4 96 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block20_check_7 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2565 block20Codes) 4 112 = true := by
  decide +kernel

/-- Input: a window index. Claim: that window passes all finite checks.
Proof: select one of the eight kernel proofs. Role: the generic block soundness input. -/
theorem block20_check (j : Fin 8) :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 2565 block20Codes) 4 (16 * j.val) =
      true := by
  fin_cases j
  · exact block20_check_0
  · exact block20_check_1
  · exact block20_check_2
  · exact block20_check_3
  · exact block20_check_4
  · exact block20_check_5
  · exact block20_check_6
  · exact block20_check_7

end PseudoPrime.LLS.SmallPart1
