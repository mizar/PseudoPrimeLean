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

/-- Exact product codes for the 128 positions starting at 1413.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1ProductCodes11 : Array ℕ :=
  #[103556866, 34884355, 35425539, 2540039741879619205, 201857797, 45329, 9277163451525,
    9552042664707, 235672834, 102503301, 91011, 9552075691523, 9552042667266, 34886275, 91266,
    2864299052490296325, 91403, 9964393074435, 36467970, 9277164235907, 91651, 35404677,
    9002319093259, 35412355, 36992898, 45963, 92039, 2612097473390052875, 169615490, 103553411,
    9277333571842, 35411331, 67650563, 34880519, 92547, 9139724758295, 9552109244546, 68952835,
    92802, 9689481616261, 92930, 46469, 9552074905607, 2612097336084792067, 34909315, 31109, 93315,
    9277197259275, 34896258, 36459523, 9139791861378, 2612097473355976455, 70011138, 46855,
    104081538, 34888587, 67654659, 10101799523601, 94087, 9552042142723, 34896514, 34361991,
    34377986, 9689481092615, 101463170, 47235, 9277196999685, 2504010670017874179, 94723,
    10789060348165, 94850, 9689481094915, 10101798481154, 47493, 95109, 2540039467001188107, 95261,
    68953347, 9552042144898, 34364677, 95490, 36453765, 9277197263106, 2720183452096009219,
    34110597, 34885507, 95874, 9552042662157, 102513282, 48003, 34897026, 9277164236291,
    9689547674882, 34881163, 34122243, 9277197784323, 34897282, 38030087, 96651,
    2612097335986226309, 135539715, 48389, 9277199358210, 36986499, 67656199, 9689481616261,
    103560323, 2540039741913172227, 102508290, 48647, 97410, 9964358999943, 336334594, 101456651,
    34897666, 9277164236675, 34385026, 9689516215303, 97922, 34889603, 9552108458501, 36460295,
    34117895, 9689481617413, 68442882, 49163, 303304066, 2828270667788717827]

/-- Exact divisor codes for the 128 positions starting at 1413.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1DivisorCodes11 : Array ℕ :=
  #[2168098819, 283214439424002, 1647742981, 352862165442562, 2161799181, 629841922,
    422955495886851, 353068324134914, 3225059335, 353205762826242, 1423, 2159190018,
    492912459288579, 422748265291778, 1427, 64602447929860857858, 1429, 64593440799325855746,
    2691338243, 1634115586, 1433, 215217053540354, 422921135624197, 1120837634, 1136562179,
    631152642, 1439, 633409429217282, 2164686859, 283248799162370, 422851880062979, 3760627714,
    3760361477, 215251413278722, 1447, 1634377730, 422611897978883, 422715513806850, 1451,
    563143764254722, 1453, 632201218, 283146256551939, 492808843468802, 2690539551, 4832272386,
    1459, 353102683873282, 1137610755, 422954959806466, 492911923200007, 352896525180930,
    1649053701, 632987650, 2168885251, 1121886210, 2162323469, 73803372302963220482, 1471,
    3224281090, 1138135043, 352999068573698, 2692124677, 422921671974914, 1638301703, 633774082,
    422714441633795, 422852952760322, 1481, 64606881263823265794, 1483, 352758549880834,
    563143764512771, 634298370, 1487, 422749873283074, 1489, 284039609753602, 353067787522051,
    1122672642, 1493, 353274482302978, 492980106072069, 492877563469826, 1139183619,
    283317518639106, 1499, 633409429217282, 2694737939, 635346946, 2169409539, 2690555906,
    422955495362565, 215423211970562, 2165473291, 422714441113602, 1139707907, 284073969491970,
    1511, 563075044777986, 2696048657, 636133378, 283214976028675, 1123459074, 3226624037,
    64615958797462446082, 3225321479, 492912459292674, 3759837187, 636657666, 1523, 283661652369410,
    2692386821, 283351878377474, 1140494339, 1635688450, 2165735435, 64602518264245297154, 1531,
    1123983362, 353102147260419, 352861093011458, 1650888709, 4832272386, 2691325981, 637706242,
    3760627715, 73812309167833784322]

/-- Claim: the sixteen positions starting at local index 0 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product11_window0 :
    unitGenerationAll (part1ProductLeaf 1413 part1ProductCodes11 part1DivisorCodes11) 4 0 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 16 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product11_window1 :
    unitGenerationAll (part1ProductLeaf 1413 part1ProductCodes11 part1DivisorCodes11) 4 16 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 32 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product11_window2 :
    unitGenerationAll (part1ProductLeaf 1413 part1ProductCodes11 part1DivisorCodes11) 4 32 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 48 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product11_window3 :
    unitGenerationAll (part1ProductLeaf 1413 part1ProductCodes11 part1DivisorCodes11) 4 48 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 64 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product11_window4 :
    unitGenerationAll (part1ProductLeaf 1413 part1ProductCodes11 part1DivisorCodes11) 4 64 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 80 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product11_window5 :
    unitGenerationAll (part1ProductLeaf 1413 part1ProductCodes11 part1DivisorCodes11) 4 80 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 96 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product11_window6 :
    unitGenerationAll (part1ProductLeaf 1413 part1ProductCodes11 part1DivisorCodes11) 4 96 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 112 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product11_window7 :
    unitGenerationAll (part1ProductLeaf 1413 part1ProductCodes11 part1DivisorCodes11) 4 112 =
      true := by
  decide +kernel

/-- Input: a window index below eight. Claim: its sixteen-position check succeeds.
Proof: select the corresponding kernel certificate. Role: the catalog's block interface. -/
theorem part1Product11_checks (j : Fin 8) :
    unitGenerationAll (part1ProductLeaf 1413 part1ProductCodes11 part1DivisorCodes11) 4
        (16 * j.val) =
      true :=
  match j with
  | ⟨0, _⟩ => part1Product11_window0
  | ⟨1, _⟩ => part1Product11_window1
  | ⟨2, _⟩ => part1Product11_window2
  | ⟨3, _⟩ => part1Product11_window3
  | ⟨4, _⟩ => part1Product11_window4
  | ⟨5, _⟩ => part1Product11_window5
  | ⟨6, _⟩ => part1Product11_window6
  | ⟨7, _⟩ => part1Product11_window7

end PseudoPrime.LLS
