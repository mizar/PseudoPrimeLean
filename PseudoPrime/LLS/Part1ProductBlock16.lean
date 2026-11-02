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

/-- Exact product codes for the 128 positions starting at 2053.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1ProductCodes16 : Array ℕ :=
  #[131330, 101459717, 9277197001229, 9277164240899, 34135045, 36456837, 236724994, 9552041620231,
    101988610, 65957, 131973, 2612097473356502277, 9552041629442, 66053, 9552076220162,
    9277164239235, 132354, 9689482666247, 302521099, 2612097335983606021, 34122893, 68959237,
    34393346, 9552042666757, 101470850, 66435, 9964426106498, 2504020153304090115, 133123, 35411589,
    133250, 36471299, 9552042673410, 34893571, 133509, 2540039467001189643, 133639, 9689481620739,
    8933668033541, 34374277, 9139791864066, 34887431, 34394370, 9964359008515, 34123269, 67075,
    134274, 2648126270376513297, 169619330, 67207, 34909954, 9689481101699, 67922178, 102505221,
    705432194, 9277164239875, 9552310569218, 36989187, 135047, 2648126270375465989, 135173,
    101983619, 9552042673410, 34897539, 67665413, 35411973, 101470466, 2612097335951101187,
    9689481104130, 67843, 34140165, 9552042666885, 67658755, 67971, 34910466, 2540039741946202371,
    136195, 9964360573703, 136322, 9964392029703, 102513282, 35420165, 9552209383170,
    2540039741879096839, 136727, 68359, 9552041366151, 9552042669315, 136962, 10926500875269,
    137091, 9277164241419, 2648125858094780162, 68435715, 34143235, 10101798481029, 101207173,
    36989187, 35435138, 9552042148611, 137731, 35412357, 34133767, 9689481098371, 36483970,
    34896647, 36502531, 2612097473391102215, 138263, 35421829, 9552109246850, 34375437, 67660807,
    36984197, 34403586, 9139724764039, 101989383, 10101866630915, 34928898, 9552042142999, 67666439,
    69507, 10101832033026, 9139960678403, 36497539, 35410565, 139399, 10376710986499]

/-- Exact divisor codes for the 128 positions starting at 2053.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1DivisorCodes16 : Array ℕ :=
  #[2053, 353205227270146, 283833451323395, 1644343298, 3760357387, 633444325830658, 2693689373,
    353618079952898, 2177540099, 672051202, 2063, 422956568588290, 423230910140421, 672313346,
    423127294844931, 423024215371778, 2069, 64616029063664283650, 2698670099, 422852953026562,
    1164353539, 423264197455874, 2695270405, 284452463226882, 2693165087, 673099778,
    563143764779011, 563178124259330, 2081, 217073016287234, 2083, 1142075394, 283867811061763,
    284039610019842, 2087, 493084794597378, 2089, 64606951598207971330, 422920600068099, 1142337538,
    492980642942983, 217107376025602, 1665568773, 2164699138, 2178064387, 674410498, 2099,
    83026744340354871298, 2172551179, 674672642, 1165664259, 1645129730, 1665830917,
    563178660868098, 3226898439, 493117545558018, 422851880853507, 285104761647106, 2111,
    563144301129730, 2113, 284073969758210, 423024751452163, 3761156098, 2693951517,
    217176095502338, 2168881165, 423127830671362, 353583720472579, 675983362, 2172813323,
    423231446495234, 3760361477, 676245506, 1166712835, 492912459558914, 2129, 46277371381011623938,
    2131, 422921136418818, 2694750211, 353514464653314, 423265269878789, 353378098393090, 2137,
    677031938, 493117546340355, 353686799429634, 2141, 64602518299141910530, 2143, 2693181442,
    73816812836180631555, 422851882168322, 2699194387, 284555542441986, 1650888711, 422956031979522,
    2178850819, 1645916162, 2153, 217279174717442, 1667141637, 563143764783106, 1168023555,
    353273946746882, 2701029393, 633409966092290, 2161, 423023680073730, 353618080210947,
    1144696834, 1667403781, 492912995905538, 2173337611, 1646178306, 2179112963,
    64634043495996895234, 2169405453, 284589902180354, 3228196905, 679391234, 493084257984515,
    3760369666, 1651412999, 563144301129730, 2179, 353721159168002]

/-- Claim: the sixteen positions starting at local index 0 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product16_window0 :
    unitGenerationAll (part1ProductLeaf 2053 part1ProductCodes16 part1DivisorCodes16) 4 0 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 16 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product16_window1 :
    unitGenerationAll (part1ProductLeaf 2053 part1ProductCodes16 part1DivisorCodes16) 4 16 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 32 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product16_window2 :
    unitGenerationAll (part1ProductLeaf 2053 part1ProductCodes16 part1DivisorCodes16) 4 32 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 48 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product16_window3 :
    unitGenerationAll (part1ProductLeaf 2053 part1ProductCodes16 part1DivisorCodes16) 4 48 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 64 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product16_window4 :
    unitGenerationAll (part1ProductLeaf 2053 part1ProductCodes16 part1DivisorCodes16) 4 64 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 80 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product16_window5 :
    unitGenerationAll (part1ProductLeaf 2053 part1ProductCodes16 part1DivisorCodes16) 4 80 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 96 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product16_window6 :
    unitGenerationAll (part1ProductLeaf 2053 part1ProductCodes16 part1DivisorCodes16) 4 96 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 112 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product16_window7 :
    unitGenerationAll (part1ProductLeaf 2053 part1ProductCodes16 part1DivisorCodes16) 4 112 =
      true := by
  decide +kernel

/-- Input: a window index below eight. Claim: its sixteen-position check succeeds.
Proof: select the corresponding kernel certificate. Role: the catalog's block interface. -/
theorem part1Product16_checks (j : Fin 8) :
    unitGenerationAll (part1ProductLeaf 2053 part1ProductCodes16 part1DivisorCodes16) 4
        (16 * j.val) =
      true :=
  match j with
  | ⟨0, _⟩ => part1Product16_window0
  | ⟨1, _⟩ => part1Product16_window1
  | ⟨2, _⟩ => part1Product16_window2
  | ⟨3, _⟩ => part1Product16_window3
  | ⟨4, _⟩ => part1Product16_window4
  | ⟨5, _⟩ => part1Product16_window5
  | ⟨6, _⟩ => part1Product16_window6
  | ⟨7, _⟩ => part1Product16_window7

end PseudoPrime.LLS
