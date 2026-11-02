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

/-- Exact product codes for the 128 positions starting at 2309.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1ProductCodes18 : Array ℕ :=
  #[147714, 2828270667788717841, 147843, 9277164241923, 34127877, 68436483, 34400002, 9689481621509,
    101208707, 101461265, 35438850, 2504019878426183427, 171193474, 103554949, 34935554,
    9552042147203, 9552175566599, 74373, 34933506, 2612097473356503045, 136070147, 68958723,
    27144295287042, 9277164241155, 149250, 34890007, 34400514, 9552142275077, 9139724507661,
    34897027, 149634, 2720184276899070727, 149767, 74917, 9277298446722, 9277164243203,
    9552108724482, 10101798480901, 150147, 34902659, 34913538, 36467459, 150413,
    2612097473357550853, 204221698, 35423365, 9277197002513, 9552109770371, 150786, 38035845,
    101471237, 2612097335917550851, 36488322, 75527, 34149379, 9689481621765, 9689480325379,
    101459717, 34915458, 9277197788163, 34412677, 9689482667783, 151682, 34903043, 9689480320005,
    75909, 35447042, 2648126270375466629, 152069, 67913223, 9277332000514, 2720184276764855299,
    152323, 35414789, 152453, 9277197788419, 9552076220162, 76291, 9140194510722, 9552042144135,
    152834, 35419907, 35440386, 2612097335916503303, 153091, 27281735812229, 37023490, 35427715,
    9277163461637, 35424013, 153483, 2612097473390053899, 131715, 76811, 34129415, 34379271,
    18073424496898, 34890765, 34414338, 2540039741946202755, 9964358228485, 67910663, 154257,
    9552109768837, 302784386, 35425283, 2828270255471337730, 9552041626373, 154627, 9552109244167,
    34152967, 9689480574727, 34916610, 36471043, 155013, 2648126270374942983, 67663885, 77573,
    34130443, 34903939, 34407298, 36458759, 9139758054403, 9277164242947, 34130565, 77827, 34403074,
    2612097473355977995]

/-- Exact divisor codes for the 128 positions starting at 2309.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1DivisorCodes18 : Array ℕ :=
  #[2309, 9674736210618346633605122, 2311, 4297240578, 2181210115, 353377025961986, 1671335941,
    284796060610562, 1654034439, 423264197718018, 1175101443, 493084257988610, 2175172619,
    422956568588290, 2697621527, 353274482831362, 493118617722883, 689352706, 2170978317,
    353515537346562, 2702344209, 285482718769154, 422852953022467, 423127294586882, 2333,
    217794570792962, 1671860229, 2693967874, 422920600330243, 284348847665154, 2339,
    73816883102382206978, 2341, 690401282, 423436532228099, 1649061890, 423368349093893,
    64615958901078536194, 2347, 1150726146, 3761938435, 423024751456258, 2351, 633444325830658,
    2171240461, 353686263345154, 284177048707075, 493117545820162, 2357, 354099652898818,
    1654820871, 423230909886466, 1176936451, 691712002, 2702606353, 284864780087298,
    422955495886853, 563178124521474, 2181996547, 3226120194, 2697883671, 46295385779521105922,
    2371, 1151512578, 353789878902787, 692498434, 3760623621, 563144301129730, 2377,
    422920601645058, 423264733798403, 73825890335460077570, 2381, 217932009746434, 2383, 2167058434,
    423127830667267, 693284866, 493118081634311, 284899139825666, 2389, 285585797984258, 1178247171,
    492980642951170, 2393, 64607021898769281026, 1673433093, 1152299010, 423024216154115,
    353720623083522, 2399, 633409966092290, 36871, 694333442, 2696060931, 1152561154,
    493221161111557, 218000729223170, 2695262237, 422956032241666, 423470891966467, 285620157722626,
    2411, 423368885448706, 2701029395, 423436533018626, 64616029097487409155, 2167320578, 2417,
    64633973230868541442, 3228983337, 563143764520962, 2182782979, 284451926880258, 2423,
    353584256823298, 2697105413, 695906306, 1179820035, 1153347586, 1656131591, 633409966092290,
    563246307901451, 3760631810, 1180082179, 696430594, 1674481669, 64629539896906133506]

/-- Claim: the sixteen positions starting at local index 0 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product18_window0 :
    unitGenerationAll (part1ProductLeaf 2309 part1ProductCodes18 part1DivisorCodes18) 4 0 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 16 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product18_window1 :
    unitGenerationAll (part1ProductLeaf 2309 part1ProductCodes18 part1DivisorCodes18) 4 16 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 32 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product18_window2 :
    unitGenerationAll (part1ProductLeaf 2309 part1ProductCodes18 part1DivisorCodes18) 4 32 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 48 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product18_window3 :
    unitGenerationAll (part1ProductLeaf 2309 part1ProductCodes18 part1DivisorCodes18) 4 48 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 64 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product18_window4 :
    unitGenerationAll (part1ProductLeaf 2309 part1ProductCodes18 part1DivisorCodes18) 4 64 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 80 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product18_window5 :
    unitGenerationAll (part1ProductLeaf 2309 part1ProductCodes18 part1DivisorCodes18) 4 80 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 96 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product18_window6 :
    unitGenerationAll (part1ProductLeaf 2309 part1ProductCodes18 part1DivisorCodes18) 4 96 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 112 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product18_window7 :
    unitGenerationAll (part1ProductLeaf 2309 part1ProductCodes18 part1DivisorCodes18) 4 112 =
      true := by
  decide +kernel

/-- Input: a window index below eight. Claim: its sixteen-position check succeeds.
Proof: select the corresponding kernel certificate. Role: the catalog's block interface. -/
theorem part1Product18_checks (j : Fin 8) :
    unitGenerationAll (part1ProductLeaf 2309 part1ProductCodes18 part1DivisorCodes18) 4
        (16 * j.val) =
      true :=
  match j with
  | ⟨0, _⟩ => part1Product18_window0
  | ⟨1, _⟩ => part1Product18_window1
  | ⟨2, _⟩ => part1Product18_window2
  | ⟨3, _⟩ => part1Product18_window3
  | ⟨4, _⟩ => part1Product18_window4
  | ⟨5, _⟩ => part1Product18_window5
  | ⟨6, _⟩ => part1Product18_window6
  | ⟨7, _⟩ => part1Product18_window7

end PseudoPrime.LLS
