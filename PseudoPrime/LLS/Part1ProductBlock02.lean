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

/-- Exact product codes for the 128 positions starting at 261.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1ProductCodes02 : Array ℕ :=
  #[34870530, 8337, 16773, 2648126270375461509, 68947202, 101975171, 34084359, 34869383, 17154,
    36440327, 34349506, 9139759350787, 9964426101506, 8707, 168559874, 9552042657157, 17669, 8835,
    103548802, 2648126270376510211, 17923, 36965253, 18051, 35393923, 9552042658050, 34868999,
    34348555, 9689481610757, 17411, 68945667, 34084869, 34345477, 18690, 36440709, 34348290,
    9277163702533, 34870914, 9475, 34873602, 9552042657037, 101452418, 9607, 34871554,
    9277164226819, 67899138, 35392517, 19589, 9689481086851, 34871682, 35393283, 19857,
    2612097335917019911, 19985, 9989, 9689549767426, 36443011, 20226, 36441349, 34349826,
    9552076211203, 35396226, 34869379, 34087939, 35392901, 67899138, 10371, 34872075, 9689480563207,
    34873987, 10101801092359, 21123, 34870403, 103549186, 10629, 36446466, 2612097473357546245,
    21523, 9991, 34085893, 10101833073667, 168298371, 104072325, 18819, 9277164227203,
    9689481612034, 11011, 22146, 9277164226315, 22274, 38539011, 102500610, 9277164227075, 22531,
    36441733, 35398402, 36443651, 9552041348101, 11399, 22919, 2612097473357546247, 21890, 35395211,
    34872194, 9964425577221, 67637771, 34868999, 23435, 9552042134275, 34086407, 70519043, 34350850,
    9552042133383, 23810, 35394563, 35395842, 9277164227459, 67900674, 104072325, 24194,
    9552042658051, 34086791, 12179, 24453, 9689481611269, 9689480564482, 12293, 102500994, 34347013]

/-- Exact divisor codes for the 128 positions starting at 261.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1DivisorCodes02 : Array ℕ :=
  #[2151313411, 554074114, 263, 352036457971714, 1617584133, 281804616400898, 1085435907,
    1082556418, 269, 422302122934274, 271, 2149744642, 352070281359363, 554860546, 2685820933,
    281873872224258, 277, 555122690, 2151575555, 422335946063874, 281, 211917444907010, 283,
    1083080706, 281804616134659, 352069745016834, 1616011271, 3758522370, 20497, 281976414830594,
    1086484483, 1083342850, 293, 422336482672642, 1618370565, 1615495170, 2685825027, 556433410,
    2150518797, 422302122934274, 1616273415, 556695554, 1087008771, 2150006786, 1618632709,
    352139537186818, 307, 352035921625090, 1087270915, 282010774568962, 311, 352070817710082, 313,
    557481986, 422335946059779, 1084129282, 317, 212020524122114, 2151305227, 3221913602,
    1087795203, 281873335877634, 2686865425, 3758522370, 2686087173, 558268418, 1088057347,
    1616019458, 1616797703, 46142122653091528706, 331, 1084653570, 2152361987, 558792706,
    1619423237, 422336482672642, 337, 2686091266, 1088581635, 352139537448962, 2151567371,
    352173896925186, 24583, 1616281602, 281873872482307, 559579138, 347, 281976951439362, 349,
    422336482934786, 2686087171, 2685829122, 353, 212123603337218, 1619947525, 1085440002,
    352139000836099, 560365570, 359, 492670867111938, 20499, 560627714, 3222695939, 352070281363458,
    1620209669, 212157963075586, 367, 2150531074, 2152886275, 282114390654978, 1617584135,
    282011311177730, 373, 352139001364482, 3758780419, 1616805890, 2151305229, 422336482672642, 379,
    352173897187330, 1090416643, 561938434, 383, 3758522370, 422404665798661, 562200578, 2153152515,
    1086488578]

/-- Claim: the sixteen positions starting at local index 0 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product02_window0 :
    unitGenerationAll (part1ProductLeaf 261 part1ProductCodes02 part1DivisorCodes02) 4 0 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 16 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product02_window1 :
    unitGenerationAll (part1ProductLeaf 261 part1ProductCodes02 part1DivisorCodes02) 4 16 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 32 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product02_window2 :
    unitGenerationAll (part1ProductLeaf 261 part1ProductCodes02 part1DivisorCodes02) 4 32 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 48 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product02_window3 :
    unitGenerationAll (part1ProductLeaf 261 part1ProductCodes02 part1DivisorCodes02) 4 48 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 64 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product02_window4 :
    unitGenerationAll (part1ProductLeaf 261 part1ProductCodes02 part1DivisorCodes02) 4 64 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 80 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product02_window5 :
    unitGenerationAll (part1ProductLeaf 261 part1ProductCodes02 part1DivisorCodes02) 4 80 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 96 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product02_window6 :
    unitGenerationAll (part1ProductLeaf 261 part1ProductCodes02 part1DivisorCodes02) 4 96 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 112 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product02_window7 :
    unitGenerationAll (part1ProductLeaf 261 part1ProductCodes02 part1DivisorCodes02) 4 112 =
      true := by
  decide +kernel

/-- Input: a window index below eight. Claim: its sixteen-position check succeeds.
Proof: select the corresponding kernel certificate. Role: the catalog's block interface. -/
theorem part1Product02_checks (j : Fin 8) :
    unitGenerationAll (part1ProductLeaf 261 part1ProductCodes02 part1DivisorCodes02) 4
        (16 * j.val) =
      true :=
  match j with
  | ⟨0, _⟩ => part1Product02_window0
  | ⟨1, _⟩ => part1Product02_window1
  | ⟨2, _⟩ => part1Product02_window2
  | ⟨3, _⟩ => part1Product02_window3
  | ⟨4, _⟩ => part1Product02_window4
  | ⟨5, _⟩ => part1Product02_window5
  | ⟨6, _⟩ => part1Product02_window6
  | ⟨7, _⟩ => part1Product02_window7

end PseudoPrime.LLS
