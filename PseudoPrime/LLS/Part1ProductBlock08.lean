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

/-- Exact product codes for the 128 positions starting at 1029.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1ProductCodes08 : Array ℕ :=
  #[34883970, 34353927, 65957, 2612097473356499589, 66053, 35404165, 9689481617666, 9552108718341,
    67648517, 35400453, 66435, 2504020153304089347, 35411586, 33283, 34369282, 9277164229899,
    9277163711746, 33413, 34887426, 9964359000195, 67075, 10101799522065, 67207, 34881923,
    102505218, 34880515, 36989186, 2648126270375463429, 101983619, 32389, 34101253, 9552076213507,
    67842, 36449157, 67971, 2540039741946201219, 9964359525122, 67902983, 34109445, 9552042137095,
    68359, 35403011, 9552108456965, 9277164232971, 67911426, 35400837, 36989187, 36455171, 35412354,
    36975747, 35420930, 2612097473357547783, 35421829, 34573, 34887042, 34358151, 9552108719874,
    34876695, 69507, 9139960677379, 34886274, 69999363, 69762, 2828270530416345861, 69893, 34949,
    9964391764491, 9552042140163, 70147, 101977863, 101459714, 9689615828227, 34888578, 36454147,
    70533, 2540039741879618309, 18073290017795, 104076163, 34101767, 34358533, 70914, 9552077785351,
    168564994, 9277164233347, 9552042141442, 35587, 34107139, 9139793954695, 71426, 101455109,
    38034690, 2648126270410065411, 34374274, 9689481614341, 71810, 35407363, 35408642, 35973,
    34894723, 2720183864413391749, 72203, 68951043, 9277197784322, 34883203, 34373506, 104074629,
    34369794, 9277164233475, 34889346, 36355, 34112519, 2720183726974437645, 101984386, 36483,
    101195655, 2648125720618602247, 67647747, 35401617, 101461250, 9689480568331, 34889602,
    35403523, 73617, 9689481615365, 73733, 36869, 2648126545254944514, 34882563]

/-- Exact divisor codes for the 128 positions starting at 1029.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1DivisorCodes08 : Array ℕ :=
  #[4295921667, 283248798900226, 1031, 352587287535618, 1033, 352654934319106, 422611897716739,
    352483671973890, 2692374545, 214083182174210, 1039, 492808843206658, 1119260675, 605200386,
    1630175239, 422715513544706, 422542642151429, 605462530, 1119522819, 1627824130, 1049,
    73803301934219042818, 1051, 1108254722, 3759837187, 422748264505346, 1638301701,
    492775020077058, 1630437383, 3224281090, 1120047107, 352758549618690, 1061, 352862165442562,
    1063, 422543178506242, 282699043082243, 352551855366146, 2160226315, 283008817340418, 1069,
    283317518376962, 422508818763779, 2156306434, 2689228829, 214186261389314, 2690023429,
    1109041154, 1120833539, 492774483730434, 2158391309, 563040685039618, 2690539543, 607821826,
    3223752707, 1109303298, 422749336928261, 214220621127682, 1087, 3223494658, 3759575043,
    283351878115330, 1091, 64593440730606116866, 1093, 608608258, 282733402820611, 1628610562, 1097,
    352896525180930, 1631223815, 492774483468290, 1121882115, 422713905029122, 1103,
    422612434329602, 492877026852869, 282836482301954, 2689765379, 1110089730, 1109,
    46200739818065272834, 2160750603, 1628872706, 352758549876739, 609918978, 1639874565,
    422749873283074, 1117, 352586215104514, 1122668547, 563074508169218, 2692112403,
    64602377629836156930, 1123, 1110614018, 4295659523, 610705410, 3224272903, 352656007012354,
    1129, 283420597592066, 422714441109507, 1110876162, 2161012747, 563075044777986, 1640398853,
    2156830722, 1123454979, 611491842, 2693165073, 55383579458273714178, 1632010247, 611753986,
    2164166659, 492808307122178, 1640660997, 214392419819522, 2689228831, 352552391450626,
    1123979267, 422611897720834, 1151, 4832272386, 1153, 612540418, 64588937130442133507,
    3760365570]

/-- Claim: the sixteen positions starting at local index 0 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product08_window0 :
    unitGenerationAll (part1ProductLeaf 1029 part1ProductCodes08 part1DivisorCodes08) 4 0 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 16 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product08_window1 :
    unitGenerationAll (part1ProductLeaf 1029 part1ProductCodes08 part1DivisorCodes08) 4 16 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 32 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product08_window2 :
    unitGenerationAll (part1ProductLeaf 1029 part1ProductCodes08 part1DivisorCodes08) 4 32 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 48 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product08_window3 :
    unitGenerationAll (part1ProductLeaf 1029 part1ProductCodes08 part1DivisorCodes08) 4 48 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 64 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product08_window4 :
    unitGenerationAll (part1ProductLeaf 1029 part1ProductCodes08 part1DivisorCodes08) 4 64 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 80 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product08_window5 :
    unitGenerationAll (part1ProductLeaf 1029 part1ProductCodes08 part1DivisorCodes08) 4 80 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 96 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product08_window6 :
    unitGenerationAll (part1ProductLeaf 1029 part1ProductCodes08 part1DivisorCodes08) 4 96 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 112 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product08_window7 :
    unitGenerationAll (part1ProductLeaf 1029 part1ProductCodes08 part1DivisorCodes08) 4 112 =
      true := by
  decide +kernel

/-- Input: a window index below eight. Claim: its sixteen-position check succeeds.
Proof: select the corresponding kernel certificate. Role: the catalog's block interface. -/
theorem part1Product08_checks (j : Fin 8) :
    unitGenerationAll (part1ProductLeaf 1029 part1ProductCodes08 part1DivisorCodes08) 4
        (16 * j.val) =
      true :=
  match j with
  | ⟨0, _⟩ => part1Product08_window0
  | ⟨1, _⟩ => part1Product08_window1
  | ⟨2, _⟩ => part1Product08_window2
  | ⟨3, _⟩ => part1Product08_window3
  | ⟨4, _⟩ => part1Product08_window4
  | ⟨5, _⟩ => part1Product08_window5
  | ⟨6, _⟩ => part1Product08_window6
  | ⟨7, _⟩ => part1Product08_window7

end PseudoPrime.LLS
