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

/-- Exact product codes for the 128 positions starting at 389.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1ProductCodes03 : Array ℕ :=
  #[24834, 10101833073415, 34876419, 9552042134147, 34873474, 12547, 34350850, 9689481611141, 25349,
    12675, 9139793953922, 9552076211459, 25603, 34869383, 101453570, 38541571, 35396354, 34870531,
    34876674, 2540039741879616517, 35402498, 69995015, 34087429, 34347397, 34352002, 35393669,
    34351362, 9552075687427, 34873986, 35395203, 26754, 2648126270376510225, 26882, 13443, 34873986,
    9552042134787, 67638275, 34869639, 101453570, 34871939, 9277164228354, 36967683, 27527,
    9689481611525, 27653, 103548803, 10101832025858, 34347787, 34877826, 35394053, 28049,
    2612097473356498179, 101976706, 68422659, 28290, 9552042658053, 67638787, 14211, 34874626,
    9552042134531, 28675, 36441869, 168299011, 34872323, 35399045, 14469, 9552209380098,
    2612097473356498053, 29197, 14599, 34087941, 9552042658563, 29442, 9964361090949, 29571,
    9277197780739, 9552041348871, 14851, 29826, 9552109765381, 101453954, 36443907, 35399429,
    9552042135171, 34092163, 35394437, 35400962, 9552042134531, 36448002, 15239, 30605,
    2612097473390051851, 204212482, 15367, 9552042135682, 34347911, 67639303, 10373, 31107,
    9139724750599, 35399810, 38540547, 31362, 9689481087495, 67640323, 101452037, 10101798473474,
    9277164228355, 36451459, 36443269, 31879, 36444419, 34875778, 16011, 32133, 2612097335986225541,
    69998850, 35396485, 35399426, 34873219, 32514, 9689516213255, 101454341, 34873347, 303301762,
    16387, 34353922, 9964359518853]

/-- Exact divisor codes for the 128 positions starting at 389.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1DivisorCodes03 : Array ℕ :=
  #[389, 46146626253255770114, 2687389713, 3222175746, 1090945027, 562724866, 1620996101,
    422405739020290, 397, 562987010, 352173360578563, 3758784514, 401, 212261579161602, 2151567373,
    1087012866, 3758784515, 281976415092738, 2152357899, 352140074057730, 409, 282183110131714,
    1091731459, 1087275010, 1618370567, 352243153272834, 1621520389, 2686091266, 1091993603,
    352173361102850, 419, 55356487491228434434, 421, 564559874, 2153676803, 1617592322, 2686611461,
    212330298638338, 1618632711, 1087799298, 422439026065411, 282217469870082, 431, 4295393282, 433,
    282010774831106, 281976951701507, 1088061442, 2687389715, 212364658376706, 439, 422405202411522,
    3222175747, 352139001626626, 443, 282114927263746, 1622306821, 566132738, 1093304323,
    3222175746, 449, 492671403982850, 2152882187, 1088585730, 1093566467, 566657026,
    422439562407941, 352174433796098, 457, 566919170, 2686615555, 352242616664066, 461,
    55365494724842913794, 463, 2151317506, 282011311439875, 567443458, 467, 422440098758658,
    1619423239, 282286189346818, 1094352899, 1618378754, 2153144331, 212467737591810, 2686873605,
    352139537711106, 2154463235, 568229890, 479, 492671403982850, 2152357901, 568492034,
    352242616926211, 3222700034, 1623355397, 4295393282, 487, 1618640898, 1095139331,
    492705227112450, 491, 282183646740482, 2688176145, 352173361364994, 422405202411523, 2151579650,
    1619947527, 212536457068546, 499, 3758784514, 1095663619, 569802754, 503, 492705763721218,
    1623879685, 352242080579586, 3222962179, 1090420738, 509, 46155633452510511106, 1620209671,
    32770, 2686877699, 570593282, 1624141829, 282218006482946]

/-- Claim: the sixteen positions starting at local index 0 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product03_window0 :
    unitGenerationAll (part1ProductLeaf 389 part1ProductCodes03 part1DivisorCodes03) 4 0 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 16 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product03_window1 :
    unitGenerationAll (part1ProductLeaf 389 part1ProductCodes03 part1DivisorCodes03) 4 16 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 32 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product03_window2 :
    unitGenerationAll (part1ProductLeaf 389 part1ProductCodes03 part1DivisorCodes03) 4 32 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 48 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product03_window3 :
    unitGenerationAll (part1ProductLeaf 389 part1ProductCodes03 part1DivisorCodes03) 4 48 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 64 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product03_window4 :
    unitGenerationAll (part1ProductLeaf 389 part1ProductCodes03 part1DivisorCodes03) 4 64 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 80 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product03_window5 :
    unitGenerationAll (part1ProductLeaf 389 part1ProductCodes03 part1DivisorCodes03) 4 80 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 96 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product03_window6 :
    unitGenerationAll (part1ProductLeaf 389 part1ProductCodes03 part1DivisorCodes03) 4 96 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 112 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product03_window7 :
    unitGenerationAll (part1ProductLeaf 389 part1ProductCodes03 part1DivisorCodes03) 4 112 =
      true := by
  decide +kernel

/-- Input: a window index below eight. Claim: its sixteen-position check succeeds.
Proof: select the corresponding kernel certificate. Role: the catalog's block interface. -/
theorem part1Product03_checks (j : Fin 8) :
    unitGenerationAll (part1ProductLeaf 389 part1ProductCodes03 part1DivisorCodes03) 4
        (16 * j.val) =
      true :=
  match j with
  | ⟨0, _⟩ => part1Product03_window0
  | ⟨1, _⟩ => part1Product03_window1
  | ⟨2, _⟩ => part1Product03_window2
  | ⟨3, _⟩ => part1Product03_window3
  | ⟨4, _⟩ => part1Product03_window4
  | ⟨5, _⟩ => part1Product03_window5
  | ⟨6, _⟩ => part1Product03_window6
  | ⟨7, _⟩ => part1Product03_window7

end PseudoPrime.LLS
