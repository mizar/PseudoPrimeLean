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

/-- Exact product codes for the 128 positions starting at 1797.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1ProductCodes14 : Array ℕ :=
  #[35427714, 36989187, 37011459, 2612097335917547277, 115211, 68957187, 34117127, 9689615829507,
    35433218, 9689549769349, 101467394, 9139760405507, 102510978, 68955395, 115881, 9552042665349,
    101990146, 57987, 10101798483714, 9277164238979, 34920067, 34884359, 34132995,
    2612097336091607811, 34903938, 58257, 116613, 2612097473356501509, 67656203, 35415685,
    9689548199170, 34370061, 34134403, 9689516216071, 117123, 9139724761351, 9277164242178,
    38035843, 34387714, 9552042664965, 34918274, 58759, 37001474, 2828270118064884483, 34915459,
    36457605, 104089605, 36991747, 9964391767559, 34892039, 118149, 713079987039861682210693,
    115587, 70528259, 34118149, 34894723, 67660803, 105126277, 9002321979138, 9277197786115,
    34904706, 59395, 34915074, 2648126270376513287, 119042, 101982083, 34903170, 9689481099779,
    67919106, 36457861, 119426, 34894979, 9139724501523, 9277199881219, 119699, 2612097336085316357,
    119845, 59909, 35421442, 9139793956995, 120066, 35409425, 120203, 2612097335917549315,
    9277231339138, 60163, 34392322, 9964359526149, 18073290282242, 34369031, 9552074908677,
    9552042146307, 120835, 10101866629389, 504106754, 9277164237955, 34119047, 60549, 36486402,
    2540039741879620485, 101467025, 205787653, 101987458, 9552042667267, 121602, 36458245, 34395906,
    2504010532578921475, 9552041361159, 60931, 121986, 9552042665733, 34922882, 35413763,
    9964426106114, 9277164239747, 122371, 9277164233491, 36486914, 36992899, 35429762, 38036995,
    35447042, 2612097473390053387, 270277635, 59523, 34119697, 9002454616325]

/-- Exact divisor codes for the 128 positions starting at 1797.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1DivisorCodes14 : Array ℕ :=
  #[1152294915, 422748266078210, 1644335111, 633409966088194, 1801, 423126758498306, 1152557059,
    422921136152578, 3760623621, 55437693057442947074, 2165735437, 2162335746, 2693177347,
    284589365567490, 1811, 284074506100738, 3226112007, 655794178, 563143764516867, 1640407042,
    2694737943, 353584256819202, 2698407953, 73816883136205332482, 1153343491, 656318466, 1823,
    492912995901442, 2693959685, 353273946480642, 422715514068995, 1133682690, 2692112415,
    46254853382874767362, 1831, 1640669186, 423024215629827, 283730372370434, 1658753029,
    492878636163074, 2169405451, 657367042, 1154129923, 492981178769410, 1645121543,
    216385821515778, 2697097235, 1134206978, 422921672237059, 353067788312578, 1847,
    73812379537114570754, 24619, 422852952760322, 1154654211, 1134469122, 2698670097,
    353618616557570, 423127830925317, 3225067522, 1154916355, 658677762, 4296704011,
    55410671425318985730, 1861, 492912459554818, 3761152003, 1641193474, 1659539461,
    216454540992514, 1867, 1134993410, 353377562042371, 64602447998580596738, 1871, 563178660864002,
    1873, 659726338, 4832534531, 352999604920322, 1877, 216488900730882, 1879, 423024751452162,
    492911923208195, 660250626, 1645907975, 284177585315842, 493083722158085, 422920600854530,
    422851880591363, 2692128770, 1889, 83026744340354867202, 2692374559, 422955495890946,
    1156489219, 661037058, 1660325893, 353206299697154, 1646170119, 353102148050946, 2175180803,
    492912459292674, 1901, 216557620207618, 2170191883, 492878099816450, 283661652631555, 661823490,
    1907, 423128367276034, 2695262231, 284761164259330, 563178124517379, 1641979906, 1913,
    64629469596881428482, 1660850181, 1136566274, 2693701635, 283833451585538, 2697621523,
    633409966088194, 2699194385, 3225329666, 1157799939, 422852416937986]

/-- Claim: the sixteen positions starting at local index 0 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product14_window0 :
    unitGenerationAll (part1ProductLeaf 1797 part1ProductCodes14 part1DivisorCodes14) 4 0 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 16 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product14_window1 :
    unitGenerationAll (part1ProductLeaf 1797 part1ProductCodes14 part1DivisorCodes14) 4 16 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 32 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product14_window2 :
    unitGenerationAll (part1ProductLeaf 1797 part1ProductCodes14 part1DivisorCodes14) 4 32 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 48 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product14_window3 :
    unitGenerationAll (part1ProductLeaf 1797 part1ProductCodes14 part1DivisorCodes14) 4 48 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 64 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product14_window4 :
    unitGenerationAll (part1ProductLeaf 1797 part1ProductCodes14 part1DivisorCodes14) 4 64 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 80 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product14_window5 :
    unitGenerationAll (part1ProductLeaf 1797 part1ProductCodes14 part1DivisorCodes14) 4 80 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 96 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product14_window6 :
    unitGenerationAll (part1ProductLeaf 1797 part1ProductCodes14 part1DivisorCodes14) 4 96 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 112 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product14_window7 :
    unitGenerationAll (part1ProductLeaf 1797 part1ProductCodes14 part1DivisorCodes14) 4 112 =
      true := by
  decide +kernel

/-- Input: a window index below eight. Claim: its sixteen-position check succeeds.
Proof: select the corresponding kernel certificate. Role: the catalog's block interface. -/
theorem part1Product14_checks (j : Fin 8) :
    unitGenerationAll (part1ProductLeaf 1797 part1ProductCodes14 part1DivisorCodes14) 4
        (16 * j.val) =
      true :=
  match j with
  | ⟨0, _⟩ => part1Product14_window0
  | ⟨1, _⟩ => part1Product14_window1
  | ⟨2, _⟩ => part1Product14_window2
  | ⟨3, _⟩ => part1Product14_window3
  | ⟨4, _⟩ => part1Product14_window4
  | ⟨5, _⟩ => part1Product14_window5
  | ⟨6, _⟩ => part1Product14_window6
  | ⟨7, _⟩ => part1Product14_window7

end PseudoPrime.LLS
