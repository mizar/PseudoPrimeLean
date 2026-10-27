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
def block01Codes : Array ℕ :=
  #[101450882, 4231, 35391746, 9277164225539, 8707, 35390853, 8834, 10101799518979, 34868098, 4487,
    34868994, 9689481609989, 68945666, 4613, 34867842, 34343173, 9474, 36439309, 9607,
    9277164225667, 34081797, 36964227, 34082563, 9552042132231, 9989, 4995, 36441346, 9552076210691,
    34869379, 3461, 10370, 36964871, 10101798470914, 5253, 10629, 2612097473357545861, 9986,
    69993475, 101975170, 34867843, 11010, 34866955, 34344706, 9277164225795, 34868866, 5635, 11394,
    9689482658567, 11522, 101450501, 34868994, 9552042132867, 67897602, 34867083, 34083843,
    34868099, 101975170, 35391747, 12179, 9689481610245, 12293, 6149, 9277199352578, 34867843,
    12546, 35391365, 12675, 9552042657027, 35393666, 6403, 34346242, 9552042656773, 67635719, 6533,
    34869378, 9552075686659, 34346626, 10101799518993, 13442, 34868483, 35393922, 6789, 36967683,
    9689481610373, 103548803, 6923, 34083333, 9689481610499, 67636227, 36440325, 14211,
    9552042132995, 35393282, 7171, 14466, 9689481610373, 14599, 35392259, 9964358993794,
    9277164226307, 14851, 102499077, 36443906, 36441731, 35394434, 36441091, 15239,
    2612097473391100167, 15367, 7047, 10370, 34344711, 34346242, 34867719, 101976322, 9277164226435,
    36443266, 6403, 16011, 9552111337861, 34872194, 8067, 9689513853959, 34869251, 16387, 35392133,
    101976322, 9552076210947]

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block01_check_0 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 133 block01Codes) 4 0 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block01_check_1 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 133 block01Codes) 4 16 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block01_check_2 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 133 block01Codes) 4 32 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block01_check_3 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 133 block01Codes) 4 48 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block01_check_4 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 133 block01Codes) 4 64 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block01_check_5 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 133 block01Codes) 4 80 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block01_check_6 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 133 block01Codes) 4 96 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block01_check_7 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 133 block01Codes) 4 112 = true := by
  decide +kernel

/-- Input: a window index. Claim: that window passes all finite checks.
Proof: select one of the eight kernel proofs. Role: the generic block soundness input. -/
theorem block01_check (j : Fin 8) :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 133 block01Codes) 4 (16 * j.val) =
      true := by
  fin_cases j
  · exact block01_check_0
  · exact block01_check_1
  · exact block01_check_2
  · exact block01_check_3
  · exact block01_check_4
  · exact block01_check_5
  · exact block01_check_6
  · exact block01_check_7

end PseudoPrime.LLS.SmallPart1
