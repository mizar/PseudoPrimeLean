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

/-- Exact product codes for the 128 positions starting at 901.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1ProductCodes07 : Array ℕ :=
  #[67646467, 169609731, 9552109243010, 9552042138627, 67906818, 35399045, 57986, 34879619,
    34884354, 9552216720131, 58257, 2612097473356499205, 34891394, 29197, 9277199355650, 34355463,
    34365826, 35398661, 58759, 2828270118031330051, 36457605, 29443, 35416322, 2648126545254942597,
    67906818, 29571, 103553410, 9277197782531, 59395, 9689482661639, 101457794, 34880003, 36457858,
    29829, 9277196997635, 2612097335984653061, 59909, 103551107, 34098705, 9964360570627, 60162,
    35399429, 34369031, 9552042138883, 9689549768962, 35402883, 60546, 9552042660741, 201855493,
    35400963, 36458242, 2540039741879094275, 60931, 36448005, 35413762, 35404675, 9277164233474,
    30605, 38036995, 2612097473390052363, 59523, 203163909, 35409794, 34356231, 67645457,
    10101799522437, 61829, 9277163707269, 9277163447301, 67901447, 62091, 35399813, 101982850,
    31107, 9277199355650, 9002320400133, 62467, 34875527, 34106883, 10101799523587, 108272395,
    31367, 62853, 2648126270374939143, 68956418, 68426755, 9552042140290, 9277230811397, 34894723,
    10101801094919, 63367, 9277164232195, 34099845, 36451459, 34366210, 9552042660997, 63751, 31879,
    304875778, 9552042662147, 9139791859458, 36448645, 34108419, 36454019, 9552042664194, 32133,
    34895106, 2612097335986225925, 64523, 69998851, 34100243, 9277164231555, 64771, 34875143,
    9002321450242, 9277164232579, 34100229, 32515, 65154, 2648126270410064903, 65311, 101454341,
    9689614518149, 34881539, 336071171, 305398917, 105129730, 34881539]

/-- Exact divisor codes for the 128 positions starting at 901.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1DivisorCodes07 : Array ℕ :=
  #[2691325969, 352551855099906, 352586751184899, 1625460738, 1634369541, 213705225048066, 907,
    1103532034, 2160758787, 64593440730069504002, 911, 422543714848770, 2158391307, 596807682,
    282527244390403, 1103794178, 1627815943, 422509355110402, 919, 422611897716738, 1114017795,
    597331970, 2156818445, 64588937130978742274, 2689236997, 597594114, 2161020931, 2688192514, 929,
    46187229019183157250, 3223748615, 1104318466, 1114542083, 598118402, 422508282413061,
    492809379811330, 937, 282630323867650, 1114804227, 352655470399490, 941, 213808304263170,
    2689753111, 2155253762, 563074508165123, 352586214838274, 947, 282837018644482, 2157080589,
    422543178240002, 1115328515, 422508818763778, 953, 352759086223362, 1635680261, 1105104898,
    422714440847363, 599691266, 1628602375, 563040685035522, 20511, 352483135885314, 2161545219,
    1105367042, 1635942405, 55392586691888189442, 967, 3759575042, 422542106071043, 283145719681026,
    971, 4832268290, 1628864519, 600739842, 492808843202563, 2155515906, 977, 213911383478274,
    2159177739, 563074508165122, 2161807363, 601264130, 983, 352552927793154, 1636466693,
    422713904762882, 352655470661635, 422542642417666, 2690015255, 64588937096619003906, 991,
    2688454658, 1117163523, 282699043344386, 1636728837, 282905738121218, 997, 602312706,
    2689241091, 4295659522, 492808307113991, 213980102955010, 2692112401, 1106677762,
    282630323605507, 602836994, 2691325971, 563075044773890, 1009, 283214439157762, 1117949955,
    422611361632258, 1013, 492809379811330, 422714977189893, 1627295746, 2162331651, 603623426,
    1019, 55379075858646339586, 1021, 282733403082754, 422748800585731, 36866, 2689761285,
    422543714852866, 2157867021, 1107468290]

/-- Claim: the sixteen positions starting at local index 0 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product07_window0 :
    unitGenerationAll (part1ProductLeaf 901 part1ProductCodes07 part1DivisorCodes07) 4 0 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 16 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product07_window1 :
    unitGenerationAll (part1ProductLeaf 901 part1ProductCodes07 part1DivisorCodes07) 4 16 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 32 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product07_window2 :
    unitGenerationAll (part1ProductLeaf 901 part1ProductCodes07 part1DivisorCodes07) 4 32 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 48 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product07_window3 :
    unitGenerationAll (part1ProductLeaf 901 part1ProductCodes07 part1DivisorCodes07) 4 48 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 64 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product07_window4 :
    unitGenerationAll (part1ProductLeaf 901 part1ProductCodes07 part1DivisorCodes07) 4 64 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 80 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product07_window5 :
    unitGenerationAll (part1ProductLeaf 901 part1ProductCodes07 part1DivisorCodes07) 4 80 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 96 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product07_window6 :
    unitGenerationAll (part1ProductLeaf 901 part1ProductCodes07 part1DivisorCodes07) 4 96 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 112 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product07_window7 :
    unitGenerationAll (part1ProductLeaf 901 part1ProductCodes07 part1DivisorCodes07) 4 112 =
      true := by
  decide +kernel

/-- Input: a window index below eight. Claim: its sixteen-position check succeeds.
Proof: select the corresponding kernel certificate. Role: the catalog's block interface. -/
theorem part1Product07_checks (j : Fin 8) :
    unitGenerationAll (part1ProductLeaf 901 part1ProductCodes07 part1DivisorCodes07) 4
        (16 * j.val) =
      true :=
  match j with
  | ⟨0, _⟩ => part1Product07_window0
  | ⟨1, _⟩ => part1Product07_window1
  | ⟨2, _⟩ => part1Product07_window2
  | ⟨3, _⟩ => part1Product07_window3
  | ⟨4, _⟩ => part1Product07_window4
  | ⟨5, _⟩ => part1Product07_window5
  | ⟨6, _⟩ => part1Product07_window6
  | ⟨7, _⟩ => part1Product07_window7

end PseudoPrime.LLS
