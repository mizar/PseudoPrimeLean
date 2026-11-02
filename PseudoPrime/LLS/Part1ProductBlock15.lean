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

/-- Exact product codes for the 128 positions starting at 1925.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1ProductCodes15 : Array ℕ :=
  #[9689614782210, 35409797, 34924039, 9139724762119, 37003403, 67907601, 123522,
    2648126270376513669, 123653, 61829, 9689548723458, 9277163714309, 67923714, 9689481618437,
    101467394, 9552075167751, 34906498, 62091, 34924290, 9689481619589, 68968706, 101982851,
    9277164243074, 34896259, 124674, 10101832027915, 124803, 9002320403973, 27144295286658, 62467,
    9277197003779, 9552042141831, 101469314, 35417603, 36479746, 2648126270376514819, 67925250,
    108272395, 101468933, 34372231, 9552042672386, 62853, 34918915, 2648126270408493575, 37019266,
    68956419, 303829509, 9277197786115, 126210, 9689482666629, 34390786, 2504010670048807173,
    34907266, 34894723, 126594, 2648126545254944519, 101467778, 63367, 34907394, 9277164239875,
    67658499, 35410565, 127106, 9552042144899, 9277331213317, 35414787, 171191554,
    2540039741879620741, 127493, 63751, 2612097473424656642, 36994183, 127746, 304875781, 127875,
    9552076216579, 9277164244226, 9964425580293, 128133, 9552042666373, 67658755, 36467715,
    101988226, 9552042147459, 34394635, 10788994294023, 128643, 34897283, 9689615306498, 34895107,
    10101965197058, 2612097335986226693, 129029, 64523, 34121733, 10101833079043, 34926979,
    34886675, 36490243, 2540039467001191299, 35424002, 64771, 129666, 9552042141447, 129794,
    10101833078019, 35432706, 9277164240643, 34401922, 36459525, 9277197266178, 36470531,
    10376745064453, 65159, 130439, 741414185936804708615175, 204220162, 65311, 36481410,
    10376742441477, 67659293, 9689615828869, 370415107, 34897923, 35433093, 338430467, 34396930,
    9689750045829]

/-- Exact divisor codes for the 128 positions starting at 1925.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1DivisorCodes15 : Array ℕ :=
  #[563143764774917, 353687336034306, 3227410473, 1642242050, 1158062083, 284795523997698, 1931,
    64616029098024017922, 1933, 663658498, 422956031975427, 4296450050, 2167046157,
    64606881333079613442, 1646956551, 353515000733698, 1158586371, 664182786, 2693165085,
    5369143298, 1661636613, 283867811323906, 423230373797891, 1137614850, 1949,
    73816883102382202882, 1951, 2692390914, 422749873807363, 664969218, 492980106596357,
    284280664530946, 2697883667, 353377025695746, 1159372803, 633443789217794, 3228196901,
    353721695772674, 2167308301, 1138139138, 283730372108291, 665755650, 1647480839,
    422922208845826, 2170978315, 284864243474434, 2693963779, 493083185815554, 1973,
    55446700256697688066, 2694746117, 492911923470338, 1160159235, 422954960592898, 1979,
    73812379502754832386, 1647742983, 666804226, 1160421379, 3225329666, 1662685189,
    216798138376194, 1987, 353068324397058, 492877563731971, 284898603212802, 2171240459,
    353275019173890, 1993, 667590658, 64607021898232668163, 1139187714, 1997, 422853489369090, 1999,
    4832534530, 493083186601987, 73816812836180893698, 2003, 284349384007682, 1663209477,
    423229837713410, 2176753667, 1643552770, 3226636295, 46268364181756878850, 2011, 1139712002,
    423264733536259, 423126758760450, 493118081896453, 633444325826562, 2017, 669163522, 1161994243,
    353583720210434, 3227410475, 216901217591298, 3760361479, 492980642684930, 4832534531,
    669687810, 2027, 563178660864002, 2029, 64629539896369520642, 1162518531, 2164170754,
    2698407955, 353790415249410, 422852416671749, 1140498434, 353515000995843, 670474242, 2039,
    64602518264782168066, 2168094733, 670736386, 2177277955, 353102684135426, 1664258053,
    64633973196508798978, 2696048663, 40962, 1163304963, 422921672241154, 1649053703,
    492912995905538]

/-- Claim: the sixteen positions starting at local index 0 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product15_window0 :
    unitGenerationAll (part1ProductLeaf 1925 part1ProductCodes15 part1DivisorCodes15) 4 0 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 16 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product15_window1 :
    unitGenerationAll (part1ProductLeaf 1925 part1ProductCodes15 part1DivisorCodes15) 4 16 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 32 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product15_window2 :
    unitGenerationAll (part1ProductLeaf 1925 part1ProductCodes15 part1DivisorCodes15) 4 32 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 48 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product15_window3 :
    unitGenerationAll (part1ProductLeaf 1925 part1ProductCodes15 part1DivisorCodes15) 4 48 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 64 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product15_window4 :
    unitGenerationAll (part1ProductLeaf 1925 part1ProductCodes15 part1DivisorCodes15) 4 64 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 80 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product15_window5 :
    unitGenerationAll (part1ProductLeaf 1925 part1ProductCodes15 part1DivisorCodes15) 4 80 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 96 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product15_window6 :
    unitGenerationAll (part1ProductLeaf 1925 part1ProductCodes15 part1DivisorCodes15) 4 96 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 112 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product15_window7 :
    unitGenerationAll (part1ProductLeaf 1925 part1ProductCodes15 part1DivisorCodes15) 4 112 =
      true := by
  decide +kernel

/-- Input: a window index below eight. Claim: its sixteen-position check succeeds.
Proof: select the corresponding kernel certificate. Role: the catalog's block interface. -/
theorem part1Product15_checks (j : Fin 8) :
    unitGenerationAll (part1ProductLeaf 1925 part1ProductCodes15 part1DivisorCodes15) 4
        (16 * j.val) =
      true :=
  match j with
  | ⟨0, _⟩ => part1Product15_window0
  | ⟨1, _⟩ => part1Product15_window1
  | ⟨2, _⟩ => part1Product15_window2
  | ⟨3, _⟩ => part1Product15_window3
  | ⟨4, _⟩ => part1Product15_window4
  | ⟨5, _⟩ => part1Product15_window5
  | ⟨6, _⟩ => part1Product15_window6
  | ⟨7, _⟩ => part1Product15_window7

end PseudoPrime.LLS
