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

/-- Exact product codes for the 128 positions starting at 773.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1ProductCodes06 : Array ℕ :=
  #[49410, 103549573, 168300291, 9964358473733, 9552109242626, 24835, 34101773, 2720184276764852999,
    169611650, 34876419, 34881282, 9552042136835, 67643139, 38019205, 50306, 34877699, 34881922,
    36972291, 36983811, 2648126270375462789, 202641154, 25349, 9552076213506, 35402115, 50946,
    9689549767813, 34888707, 9552076212739, 34095623, 25603, 34101765, 9552042135687, 9552041615618,
    101453575, 34882306, 10101797951747, 51715, 36444935, 51843, 9964358997251, 36979586, 35400965,
    36458754, 2540039741913170949, 101982082, 26141, 27556612145922, 9689516214791, 52482, 36446725,
    52611, 9689480567173, 10101932688642, 36449155, 52866, 9552042659973, 52994, 36972803, 39601413,
    9552075688963, 36459523, 38019717, 36983554, 9964359521923, 103552642, 26763, 53643,
    713079987039586803778321, 51970, 26903, 34096651, 36451459, 67905282, 36971141, 34361986,
    9139760401667, 36456069, 69997571, 34890498, 9689481089415, 54530, 101453585, 9552109766914,
    9689481091715, 54787, 10376675856135, 54914, 9689482663171, 9139724492299, 27527, 55173,
    9689481613829, 70003458, 27653, 34096133, 9689549768579, 34365826, 10101833074439, 101458178,
    9139724753675, 101193733, 34877827, 34360066, 9552042660357, 56066, 28049, 35408130,
    2612097473390052611, 56323, 104073861, 56450, 9277197782019, 9689481616642, 28293, 56709,
    2540039741879617797, 104079235, 71570947, 34882434, 34879363, 34891650, 34874635, 34363650,
    9552042137603, 9277164232962, 28675, 34105603, 9552042659597]

/-- Exact divisor codes for the 128 positions starting at 773.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1DivisorCodes06 : Array ℕ :=
  #[773, 352587287531522, 2688450565, 1623363586, 352483135098883, 587894786, 2689753107,
    55370068659391598594, 2156818443, 422610825547778, 2688192515, 3759050754, 1631223813,
    213361627664386, 787, 1099599874, 1108250627, 282836482035714, 1625452551, 492775020072962,
    2155503629, 588943362, 282389805436931, 1099862018, 797, 55383509123889270786, 2690539537,
    4295659522, 2159185923, 589467650, 2157080587, 282630860214274, 422611361103877,
    352379519799298, 1109037059, 1623887874, 809, 563040685035522, 811, 352345696145410, 1109299203,
    352483135623170, 1632010245, 422509355110402, 2690015251, 590516226, 422439562416131,
    352552391184386, 821, 213464706879490, 823, 1624150018, 492774483464195, 282492348043266, 827,
    422612434325506, 829, 282905201512450, 1110085635, 3222966274, 3223482375, 213499066617858,
    1632534533, 422542642155522, 2688454659, 591826946, 839, 64579929897364262914, 20509, 592089090,
    1110609923, 1101434882, 3759833093, 352656007008258, 3759566855, 2154467330, 1110872067,
    422508818501634, 2689228823, 282699579691010, 853, 282526707781634, 422543178240003, 1624674306,
    857, 64593370430581411842, 859, 352586750922754, 352551854575619, 593399810, 863, 4832268290,
    1633320965, 593661954, 3223490563, 352380055883778, 2157867019, 46182725419555786754,
    2156294157, 1624936450, 2160234499, 422610825809922, 3759046661, 282733939429378, 877,
    594448386, 1112182787, 492774483464194, 881, 492706300596226, 883, 422508282679298,
    282492884652035, 594972674, 887, 352484208316418, 1627287559, 283008280727554, 3759575043,
    1103007746, 2690539539, 213670865309698, 1634107397, 3759050754, 422611361894403, 595759106,
    2688438301, 563040685035522]

/-- Claim: the sixteen positions starting at local index 0 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product06_window0 :
    unitGenerationAll (part1ProductLeaf 773 part1ProductCodes06 part1DivisorCodes06) 4 0 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 16 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product06_window1 :
    unitGenerationAll (part1ProductLeaf 773 part1ProductCodes06 part1DivisorCodes06) 4 16 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 32 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product06_window2 :
    unitGenerationAll (part1ProductLeaf 773 part1ProductCodes06 part1DivisorCodes06) 4 32 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 48 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product06_window3 :
    unitGenerationAll (part1ProductLeaf 773 part1ProductCodes06 part1DivisorCodes06) 4 48 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 64 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product06_window4 :
    unitGenerationAll (part1ProductLeaf 773 part1ProductCodes06 part1DivisorCodes06) 4 64 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 80 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product06_window5 :
    unitGenerationAll (part1ProductLeaf 773 part1ProductCodes06 part1DivisorCodes06) 4 80 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 96 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product06_window6 :
    unitGenerationAll (part1ProductLeaf 773 part1ProductCodes06 part1DivisorCodes06) 4 96 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 112 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product06_window7 :
    unitGenerationAll (part1ProductLeaf 773 part1ProductCodes06 part1DivisorCodes06) 4 112 =
      true := by
  decide +kernel

/-- Input: a window index below eight. Claim: its sixteen-position check succeeds.
Proof: select the corresponding kernel certificate. Role: the catalog's block interface. -/
theorem part1Product06_checks (j : Fin 8) :
    unitGenerationAll (part1ProductLeaf 773 part1ProductCodes06 part1DivisorCodes06) 4
        (16 * j.val) =
      true :=
  match j with
  | ⟨0, _⟩ => part1Product06_window0
  | ⟨1, _⟩ => part1Product06_window1
  | ⟨2, _⟩ => part1Product06_window2
  | ⟨3, _⟩ => part1Product06_window3
  | ⟨4, _⟩ => part1Product06_window4
  | ⟨5, _⟩ => part1Product06_window5
  | ⟨6, _⟩ => part1Product06_window6
  | ⟨7, _⟩ => part1Product06_window7

end PseudoPrime.LLS
