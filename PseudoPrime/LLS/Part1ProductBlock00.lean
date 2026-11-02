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

/-- Exact product codes for the 128 positions starting at 5.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1ProductCodes00 : Array ℕ :=
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

/-- Exact divisor codes for the 128 positions starting at 5.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1DivisorCodes00 : Array ℕ :=
  #[5, 537272322, 7, 8194, 8195, 537538562, 11, 1074147330, 13, 537800706, 1074409475, 12290, 17,
    1611022338, 19, 1074413570, 1074671619, 538329090, 23, 1611022338, 12293, 538591234, 16387,
    1074675714, 29, 211194279772162, 31, 16386, 1075200003, 539119618, 1611542533, 2147897346, 37,
    539381762, 1075462147, 1611288578, 41, 211228639514626, 43, 1075204098, 2148155395, 539906050,
    47, 2147897346, 12295, 2148159490, 1075990531, 1075466242, 53, 2684768258, 1612070917,
    1611550722, 1076252675, 540692482, 59, 281563560824834, 61, 540954626, 2148421635, 20482,
    1612333061, 211297895866370, 67, 1075994626, 1076776963, 281597383958530, 71, 2684772354, 73,
    541745154, 2148159491, 1076256770, 1612070919, 211332255604738, 79, 2148163586, 20483,
    542269442, 83, 281597920567298, 1612861445, 542531586, 1077563395, 1612079106, 89,
    351932305006594, 1612333063, 1076781058, 1077825539, 543055874, 1613123589, 2684772354, 97,
    2148425730, 2148950019, 2685034498, 101, 211401511952386, 103, 1612341250, 281597920829443,
    543842306, 107, 3221643266, 109, 281666640306178, 1078616067, 2148425730, 113, 211435871690754,
    1613647877, 1077567490, 2149212163, 544628738, 1612861447, 351932841877506, 16395, 544890882,
    1079140355, 1077829634, 20485, 351967201615874, 127, 24578, 1079402499, 281701000048642, 131,
    281667176919042]

/-- Claim: the sixteen positions starting at local index 0 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product00_window0 :
    unitGenerationAll (part1ProductLeaf 5 part1ProductCodes00 part1DivisorCodes00) 4 0 = true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 16 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product00_window1 :
    unitGenerationAll (part1ProductLeaf 5 part1ProductCodes00 part1DivisorCodes00) 4 16 = true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 32 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product00_window2 :
    unitGenerationAll (part1ProductLeaf 5 part1ProductCodes00 part1DivisorCodes00) 4 32 = true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 48 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product00_window3 :
    unitGenerationAll (part1ProductLeaf 5 part1ProductCodes00 part1DivisorCodes00) 4 48 = true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 64 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product00_window4 :
    unitGenerationAll (part1ProductLeaf 5 part1ProductCodes00 part1DivisorCodes00) 4 64 = true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 80 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product00_window5 :
    unitGenerationAll (part1ProductLeaf 5 part1ProductCodes00 part1DivisorCodes00) 4 80 = true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 96 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product00_window6 :
    unitGenerationAll (part1ProductLeaf 5 part1ProductCodes00 part1DivisorCodes00) 4 96 = true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 112 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product00_window7 :
    unitGenerationAll (part1ProductLeaf 5 part1ProductCodes00 part1DivisorCodes00) 4 112 =
      true := by
  decide +kernel

/-- Input: a window index below eight. Claim: its sixteen-position check succeeds.
Proof: select the corresponding kernel certificate. Role: the catalog's block interface. -/
theorem part1Product00_checks (j : Fin 8) :
    unitGenerationAll (part1ProductLeaf 5 part1ProductCodes00 part1DivisorCodes00) 4 (16 * j.val) =
      true :=
  match j with
  | ⟨0, _⟩ => part1Product00_window0
  | ⟨1, _⟩ => part1Product00_window1
  | ⟨2, _⟩ => part1Product00_window2
  | ⟨3, _⟩ => part1Product00_window3
  | ⟨4, _⟩ => part1Product00_window4
  | ⟨5, _⟩ => part1Product00_window5
  | ⟨6, _⟩ => part1Product00_window6
  | ⟨7, _⟩ => part1Product00_window7

end PseudoPrime.LLS
