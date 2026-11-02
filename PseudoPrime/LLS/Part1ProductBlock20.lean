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

/-- Exact product codes for the 128 positions starting at 2565.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1ProductCodes20 : Array ℕ :=
  #[9552311093506, 82053, 34417669, 2648126270375467653, 103570307, 70533123, 34133509, 34381959,
    34157443, 10376743489285, 34406146, 2540039741879099651, 34920066, 82443, 164994,
    2612097335917548813, 67672579, 82563, 9139791601163, 2504010669982229507, 9689480590082,
    35416965, 103572226, 34906499, 34920322, 10101967816963, 165767, 9689481623045, 165895, 82961,
    9277199362818, 9689481627779, 34410754, 35417093, 34944003, 2612097335951101699, 34130949,
    83203, 34157059, 2612097473423083403, 67666435, 83335, 9277164249474, 9277164245251, 166915,
    10101833078023, 101473538, 34906883, 10101868208386, 83589, 35456258, 2540039467001191179,
    167429, 10376677964803, 101206021, 9964360581379, 167682, 9689481621893, 101476610,
    9689581229061, 9689482676994, 68438787, 35470082, 9552109769221, 35465602, 35422979, 37018370,
    2612097335917027971, 168451, 38038917, 9277197007875, 35431555, 35445506, 84365, 10101965198594,
    713079987039861715764487, 104097666, 84493, 34135057, 34383127, 35454210, 104079237, 169347,
    9689481106051, 35445890, 68960515, 168311815, 2504010532580494343, 101998210, 84867,
    9689481631490, 9277164245507, 169987, 35417733, 170114, 2720184139359455491, 34921858, 77447,
    170373, 2540039741946726661, 17798412115463, 101987459, 9689548201867, 9277164244227, 67673091,
    9552078837255, 170887, 9277164245763, 34916994, 36474499, 34408706, 9689481623429, 171266,
    101462789, 9964359018370, 2540039741878575367, 34938499, 34893579, 171650, 9002422636295,
    9552042678530, 34905091, 171909, 2612097473357551621, 172051, 70533891, 9277231341826, 34383877]

/-- Exact divisor codes for the 128 positions starting at 2565.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1DivisorCodes20 : Array ℕ :=
  #[563281740341251, 705081346, 2704179217, 353687336038402, 1658753031, 285895572500482,
    1186111491, 1158066178, 2695262239, 73816812836717244418, 2697895941, 492981179035650,
    1186373635, 705867778, 2579, 55437763391827390466, 2696048669, 706129922, 422921672499203,
    563280668176386, 423024215367685, 218516125298690, 2173599757, 1158590466, 1186897923,
    64647554295415877634, 2591, 5369147394, 2593, 706916354, 284452463484931, 423230373801986,
    3228209159, 218550485037058, 2699194391, 563178661130242, 4297236483, 707440642, 2702344211,
    64634043496533504002, 1678942213, 707702786, 423573971181571, 2168893442, 2609,
    64629610231290572802, 1659539463, 1159376898, 423367813013507, 708227074, 1679204357,
    353721695776770, 2617, 73825820035435638786, 2697109507, 354099653160962, 2621,
    64615958935438274562, 3229245483, 3226644482, 633444326088707, 353583184392194, 3230560293,
    423471964663810, 2178842635, 285998651715586, 1188732931, 423024751718402, 2633,
    218653564252162, 493118082424837, 1160163330, 2185928707, 709799938, 493083722158087,
    73812449871499014146, 2702606355, 710062082, 1189257219, 1160425474, 3761152005,
    633444325830658, 2647, 1654042626, 1189519363, 423128367542274, 2179104779,
    73825820070331723778, 1660325895, 710848514, 423231446753283, 2695278594, 2657, 218722283728898,
    2659, 73830393935624318978, 1190043651, 4296454146, 2663, 493222233550850, 493289880592389,
    422954961645570, 354030397071363, 493083186606082, 2704965649, 46317974146402136066, 2671,
    2169417730, 4296450051, 284761164525570, 2698420229, 285311456686082, 2677, 353617544130562,
    423024216416259, 423368885710850, 1660850183, 354408890544130, 2683, 423264733540354,
    284555542700035, 423573971972098, 2687, 633444325830658, 2689, 286101730930690, 492980642947075,
    1161998338]

/-- Claim: the sixteen positions starting at local index 0 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product20_window0 :
    unitGenerationAll (part1ProductLeaf 2565 part1ProductCodes20 part1DivisorCodes20) 4 0 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 16 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product20_window1 :
    unitGenerationAll (part1ProductLeaf 2565 part1ProductCodes20 part1DivisorCodes20) 4 16 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 32 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product20_window2 :
    unitGenerationAll (part1ProductLeaf 2565 part1ProductCodes20 part1DivisorCodes20) 4 32 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 48 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product20_window3 :
    unitGenerationAll (part1ProductLeaf 2565 part1ProductCodes20 part1DivisorCodes20) 4 48 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 64 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product20_window4 :
    unitGenerationAll (part1ProductLeaf 2565 part1ProductCodes20 part1DivisorCodes20) 4 64 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 80 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product20_window5 :
    unitGenerationAll (part1ProductLeaf 2565 part1ProductCodes20 part1DivisorCodes20) 4 80 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 96 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product20_window6 :
    unitGenerationAll (part1ProductLeaf 2565 part1ProductCodes20 part1DivisorCodes20) 4 96 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 112 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product20_window7 :
    unitGenerationAll (part1ProductLeaf 2565 part1ProductCodes20 part1DivisorCodes20) 4 112 =
      true := by
  decide +kernel

/-- Input: a window index below eight. Claim: its sixteen-position check succeeds.
Proof: select the corresponding kernel certificate. Role: the catalog's block interface. -/
theorem part1Product20_checks (j : Fin 8) :
    unitGenerationAll (part1ProductLeaf 2565 part1ProductCodes20 part1DivisorCodes20) 4
        (16 * j.val) =
      true :=
  match j with
  | ⟨0, _⟩ => part1Product20_window0
  | ⟨1, _⟩ => part1Product20_window1
  | ⟨2, _⟩ => part1Product20_window2
  | ⟨3, _⟩ => part1Product20_window3
  | ⟨4, _⟩ => part1Product20_window4
  | ⟨5, _⟩ => part1Product20_window5
  | ⟨6, _⟩ => part1Product20_window6
  | ⟨7, _⟩ => part1Product20_window7

end PseudoPrime.LLS
