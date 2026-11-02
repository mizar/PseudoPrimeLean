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

/-- Exact product codes for the 128 positions starting at 1157.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1ProductCodes09 : Array ℕ :=
  #[67650051, 36974597, 101461250, 2540039741913171715, 102506370, 34880899, 74373, 9689481615365,
    67648003, 35406083, 34889986, 9552075166213, 34897027, 10101967291143, 74882, 34883843,
    10101797170181, 37509, 36467458, 2612097473357548165, 34899074, 103552643, 34890114,
    9964360572163, 75527, 36974853, 101459714, 9277197783555, 9552042665730, 37891, 75906,
    9689481614981, 67651079, 10101833075715, 35414789, 9277164233987, 76291, 36450711, 35419906,
    9964358476039, 27144295285890, 38279, 35424013, 2612097473390052619, 76811, 38407, 34104333,
    9689548196483, 67648519, 102502533, 35425283, 9552041616773, 9552109768450, 34354951, 34373890,
    10101797951751, 77570, 38787, 35410178, 9277164233731, 77827, 9689481090315, 34901762,
    9552075165447, 9689481096450, 34882823, 78213, 2540039741879618565, 34367746, 39173, 34104861,
    34360453, 78594, 9964394121735, 78723, 2612097473355976451, 34104837, 39427, 9277333571842,
    9964359522693, 79106, 39563, 10101797956482, 2612097335917547267, 135013381, 35402117, 34114563,
    36457859, 9552042666242, 34882051, 236197123, 2612096923634238987, 79879, 32003, 105652866,
    34360849, 34375042, 9689481614981, 34110723, 9689480570629, 34891906, 68428803, 80514,
    2648126545321526029, 201857029, 40323, 34892034, 9552042141443, 9277163714306, 34878599,
    101985538, 34885379, 34891650, 36978435, 169614851, 2540039741879618821, 101986690, 101455109,
    9689513858059, 9689481618179, 81666, 34878599, 81795, 9552076214275, 9139794480898, 40963,
    82050, 10101798476421]

/-- Exact divisor codes for the 128 positions starting at 1157.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1DivisorCodes09 : Array ℕ :=
  #[2159177741, 214426779557890, 2692374547, 422714976935938, 2690027523, 282905201778690, 1163,
    283146256293890, 1641185285, 352758013534210, 1124765699, 2157092866, 1632534535,
    64593440696246378498, 1171, 1112186882, 422611362418691, 613851138, 2690547717, 563075044777986,
    2161537035, 422748264767490, 2164690947, 352861628833794, 1181, 214495499034626, 3759833095,
    2689245186, 282836482035715, 614637570, 1187, 492775020077058, 2689753117, 64602447929324249090,
    1125814275, 1630183426, 1193, 214529858772994, 1641971717, 422611361898498, 422543178502147,
    615424002, 2161799179, 563040685039618, 1201, 615686146, 1126338563, 352586751188994,
    1642233861, 352999604396034, 2693689361, 1630445570, 422748800847875, 492774483468290,
    1633320967, 283214975770626, 1213, 616472578, 4295659523, 3223756802, 1217,
    55406097490770305026, 2691325975, 352895988572162, 422851879800835, 352654934581250, 1223,
    492878099292162, 4295917573, 617259010, 1127387139, 1114021890, 1229, 46209747017320013826,
    1231, 492774483730434, 2165477379, 617783298, 492911386591237, 283249335508994, 1237, 618045442,
    352861629091843, 422749336674306, 2693951505, 422612434329602, 2162323467, 1114546178,
    282905201512451, 283008280993794, 2690015261, 492809379815426, 1249, 4295663618, 2165739523,
    1114808322, 1634107399, 64606881229463527426, 1643544581, 1631232002, 1128697859,
    422851880591362, 1259, 73803301934219042818, 2160226317, 619618306, 1128960003, 2157879298,
    422611361628165, 214736017203202, 1634369543, 1115332610, 2690551811, 283661115760642,
    2689753119, 352759086227458, 2693165075, 492808843468802, 492877562679299, 422714440851458,
    1277, 353068323872770, 1279, 4295663618, 352895988830211, 620929026, 1283, 283318054985730]

/-- Claim: the sixteen positions starting at local index 0 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product09_window0 :
    unitGenerationAll (part1ProductLeaf 1157 part1ProductCodes09 part1DivisorCodes09) 4 0 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 16 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product09_window1 :
    unitGenerationAll (part1ProductLeaf 1157 part1ProductCodes09 part1DivisorCodes09) 4 16 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 32 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product09_window2 :
    unitGenerationAll (part1ProductLeaf 1157 part1ProductCodes09 part1DivisorCodes09) 4 32 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 48 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product09_window3 :
    unitGenerationAll (part1ProductLeaf 1157 part1ProductCodes09 part1DivisorCodes09) 4 48 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 64 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product09_window4 :
    unitGenerationAll (part1ProductLeaf 1157 part1ProductCodes09 part1DivisorCodes09) 4 64 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 80 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product09_window5 :
    unitGenerationAll (part1ProductLeaf 1157 part1ProductCodes09 part1DivisorCodes09) 4 80 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 96 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product09_window6 :
    unitGenerationAll (part1ProductLeaf 1157 part1ProductCodes09 part1DivisorCodes09) 4 96 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 112 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product09_window7 :
    unitGenerationAll (part1ProductLeaf 1157 part1ProductCodes09 part1DivisorCodes09) 4 112 =
      true := by
  decide +kernel

/-- Input: a window index below eight. Claim: its sixteen-position check succeeds.
Proof: select the corresponding kernel certificate. Role: the catalog's block interface. -/
theorem part1Product09_checks (j : Fin 8) :
    unitGenerationAll (part1ProductLeaf 1157 part1ProductCodes09 part1DivisorCodes09) 4
        (16 * j.val) =
      true :=
  match j with
  | ⟨0, _⟩ => part1Product09_window0
  | ⟨1, _⟩ => part1Product09_window1
  | ⟨2, _⟩ => part1Product09_window2
  | ⟨3, _⟩ => part1Product09_window3
  | ⟨4, _⟩ => part1Product09_window4
  | ⟨5, _⟩ => part1Product09_window5
  | ⟨6, _⟩ => part1Product09_window6
  | ⟨7, _⟩ => part1Product09_window7

end PseudoPrime.LLS
