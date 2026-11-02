/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Part1ProductCheck

/-! # Independent finite LLS Part 1 coverage certificates

This block checks 128 positions using compact product and divisor codes. Each sixteen-position
window is checked in the kernel; positions at or above 3000 are padding. Integer data is
untrusted until these checks succeed. Blocks depend only on the computational entry and not on
one another, the catalog, soundness proofs, or analytic bounds.

Keep unrelated declarations and imports out of this file. Changing a computational dependency
can invalidate these expensive proofs even when the certificate arrays are unchanged.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- Exact product codes for the 128 positions starting at 133.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1ProductCodes01 : Array ℕ :=
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

/-- Exact divisor codes for the 128 positions starting at 133.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1DivisorCodes01 : Array ℕ :=
  #[1613123591, 545681410, 2685034499, 1612869634, 137, 211504591171586, 139, 351966665011202,
    1079926787, 546205698, 2149203979, 3221647362, 1614434309, 546467842, 2685296643, 1078620162,
    149, 351932841881602, 151, 1613131778, 2149736451, 281666640572418, 1614696453, 281701536657410,
    157, 547254274, 1080713219, 2685038594, 1613647879, 3221647362, 163, 1079144450,
    281667177177091, 547778562, 167, 351967201619970, 16397, 281770256396290, 2149998595,
    1079406594, 173, 211607670386690, 2685296645, 2148954114, 1081499651, 548564994, 179,
    422301586059266, 181, 281701000310786, 1081761795, 1613656066, 1615486981, 211642030125058,
    2149732363, 1079930882, 2685296643, 281804616134658, 191, 3221647362, 193, 549613570,
    281701536919555, 2685300738, 197, 352036457967618, 199, 3221909506, 1082552323, 550137858,
    1614434311, 281770793005058, 1616011269, 550400002, 2150526979, 2149216258, 2149994507,
    46133045085092605954, 211, 1080717314, 1083076611, 550924290, 1616273413, 3758518274,
    1614696455, 551186434, 1083338755, 352035921358850, 2149732365, 211745646211074, 223,
    2685300738, 3221909507, 551710722, 227, 281805152743426, 229, 281873335611394, 352035921620995,
    1614442498, 233, 352070817705986, 1616797701, 1081503746, 1084125187, 281770256658434, 239,
    422302122930178, 241, 2685825026, 28675, 1081765890, 3222167557, 211814365687810, 2149994509,
    1614704642, 1084649475, 3221909506, 251, 422336482668546, 2150518795, 553545730,
    281770256396291, 28674, 257, 211848725430274, 1615486983, 352070281101314]

/-- Claim: the sixteen positions starting at local index 0 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product01_window0 :
    unitGenerationAll (part1ProductLeaf 133 part1ProductCodes01 part1DivisorCodes01) 4 0 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 16 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product01_window1 :
    unitGenerationAll (part1ProductLeaf 133 part1ProductCodes01 part1DivisorCodes01) 4 16 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 32 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product01_window2 :
    unitGenerationAll (part1ProductLeaf 133 part1ProductCodes01 part1DivisorCodes01) 4 32 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 48 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product01_window3 :
    unitGenerationAll (part1ProductLeaf 133 part1ProductCodes01 part1DivisorCodes01) 4 48 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 64 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product01_window4 :
    unitGenerationAll (part1ProductLeaf 133 part1ProductCodes01 part1DivisorCodes01) 4 64 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 80 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product01_window5 :
    unitGenerationAll (part1ProductLeaf 133 part1ProductCodes01 part1DivisorCodes01) 4 80 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 96 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product01_window6 :
    unitGenerationAll (part1ProductLeaf 133 part1ProductCodes01 part1DivisorCodes01) 4 96 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 112 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product01_window7 :
    unitGenerationAll (part1ProductLeaf 133 part1ProductCodes01 part1DivisorCodes01) 4 112 =
      true := by
  decide +kernel

/-- Input: a window index below eight. Claim: its sixteen-position check succeeds.
Proof: select the corresponding kernel certificate. Role: the catalog's block interface. -/
theorem part1Product01_checks (j : Fin 8) :
    unitGenerationAll (part1ProductLeaf 133 part1ProductCodes01 part1DivisorCodes01) 4
        (16 * j.val) =
      true :=
  match j with
  | ⟨0, _⟩ => part1Product01_window0
  | ⟨1, _⟩ => part1Product01_window1
  | ⟨2, _⟩ => part1Product01_window2
  | ⟨3, _⟩ => part1Product01_window3
  | ⟨4, _⟩ => part1Product01_window4
  | ⟨5, _⟩ => part1Product01_window5
  | ⟨6, _⟩ => part1Product01_window6
  | ⟨7, _⟩ => part1Product01_window7

end PseudoPrime.LLS
