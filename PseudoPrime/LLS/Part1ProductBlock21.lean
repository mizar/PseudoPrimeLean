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

/-- Exact product codes for the 128 positions starting at 2693.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1ProductCodes21 : Array ℕ :=
  #[172290, 34893837, 9689480587522, 9139724768275, 9139724511499, 35429763, 172674, 9552042667277,
    605819397, 101462021, 9552074912773, 9552075695875, 67929858, 11751199607303, 173186, 34908419,
    27144295287426, 34375431, 173447, 2540039741879622661, 173573, 36478853, 9277199887618,
    9552108722181, 9002353437954, 102507909, 173955, 2648134929130193923, 35447426, 87043, 34415362,
    9552042670213, 67667715, 34906371, 34922754, 2972385031362971523, 174595, 2720184276900643595,
    174723, 34384517, 35447685, 87429, 37032194, 2612097473423608069, 9552042165251, 85253,
    9689481111170, 9552076218883, 175362, 34894349, 103573762, 9552042150275, 9277333573378, 87811,
    34163207, 9552042146055, 175885, 169613571, 9552042156418, 9277164246019, 176131, 35417093,
    9552076226306, 10101831509763, 35448197, 36475651, 35473923, 741414149908007656098567,
    168312455, 88331, 103566469, 35433603, 9689547679490, 34894599, 177027, 9139759360771,
    9552042682626, 70010115, 34161667, 2648126545322051461, 34950530, 302780933, 9552076221698,
    9689481107075, 177667, 35419013, 101212933, 9552042673411, 103566466, 36478727, 370416514,
    2540039467036315141, 68979458, 101986691, 34138119, 9689581229061, 178434, 9689549770503,
    34430151, 9139724769031, 9139793960834, 35429763, 9964526245122, 10376676391429, 178946, 89485,
    36497538, 2648126270410067715, 179203, 38040709, 179330, 35434243, 2648126270407709703,
    34907399, 34941955, 2612097335984654597, 176386, 68961795, 34138629, 9002555279621, 67676165,
    9689549770885, 34412802, 9277164244995, 101207559, 90115, 180354, 2612097473357551367]

/-- Exact divisor codes for the 128 positions starting at 2693.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1DivisorCodes21 : Array ℕ :=
  #[2693, 218825362944002, 563143764779013, 1654829058, 493117547126787, 423436533280770, 2699,
    703778710269954, 3230822437, 284795524263938, 423127295369219, 4296716290, 1681563653,
    64656491194645655554, 2707, 1162522626, 422956032237571, 286136090669058, 2711, 353790415253506,
    2713, 423229838503938, 284589902438403, 353515000999938, 563280667639819, 354443250282498, 2719,
    563247380606978, 1192665091, 715304962, 1661636615, 285380176162818, 2698682373,
    423023680860162, 2697633795, 493118081642498, 2729, 9675326506499074083434498, 2731, 1163309058,
    1193189379, 716091394, 1682350085, 563281740083202, 492980643467271, 3762991106,
    423642690658307, 354202732376066, 2741, 218962801897474, 2175172621, 4832800770,
    423265806491651, 716877826, 3230036009, 285414535901186, 2749, 563144301391874, 354099116548099,
    3226906626, 2753, 563247380344834, 493083722948613, 423127294849026, 1194237955,
    284864243740674, 2696048671, 64616099432408461314, 2180415499, 717926402, 2187763715,
    1164357634, 423574507528197, 219031521374210, 2767, 2170204162, 423436532490243,
    286239169884162, 2705752081, 73812379537114574850, 3228983343, 423470893019138, 493222233808899,
    1656139778, 2777, 219065881112578, 1662685191, 354237092114434, 2697895939, 353686263607298,
    3761143819, 493084794597378, 1683660805, 284898603479042, 1195548675, 493289881120770, 2789,
    64634113830917943298, 2791, 1656401922, 563281203732483, 354029860728834, 493324240330757,
    285483255377922, 2797, 720285698, 2188288003, 633444326092802, 2801, 219134600589314, 2803,
    1165668354, 73825820035972243459, 423264198242306, 1663209479, 563178660868098, 24629,
    286307889360898, 1196597251, 493221161906178, 2697097245, 55491736252971397122, 1684447237,
    4296454146, 2188550147, 721596418, 2819, 55446770591082131458]

/-- Claim: the sixteen positions starting at local index 0 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product21_window0 :
    unitGenerationAll (part1ProductLeaf 2693 part1ProductCodes21 part1DivisorCodes21) 4 0 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 16 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product21_window1 :
    unitGenerationAll (part1ProductLeaf 2693 part1ProductCodes21 part1DivisorCodes21) 4 16 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 32 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product21_window2 :
    unitGenerationAll (part1ProductLeaf 2693 part1ProductCodes21 part1DivisorCodes21) 4 32 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 48 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product21_window3 :
    unitGenerationAll (part1ProductLeaf 2693 part1ProductCodes21 part1DivisorCodes21) 4 48 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 64 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product21_window4 :
    unitGenerationAll (part1ProductLeaf 2693 part1ProductCodes21 part1DivisorCodes21) 4 64 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 80 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product21_window5 :
    unitGenerationAll (part1ProductLeaf 2693 part1ProductCodes21 part1DivisorCodes21) 4 80 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 96 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product21_window6 :
    unitGenerationAll (part1ProductLeaf 2693 part1ProductCodes21 part1DivisorCodes21) 4 96 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 112 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product21_window7 :
    unitGenerationAll (part1ProductLeaf 2693 part1ProductCodes21 part1DivisorCodes21) 4 112 =
      true := by
  decide +kernel

/-- Input: a window index below eight. Claim: its sixteen-position check succeeds.
Proof: select the corresponding kernel certificate. Role: the catalog's block interface. -/
theorem part1Product21_checks (j : Fin 8) :
    unitGenerationAll (part1ProductLeaf 2693 part1ProductCodes21 part1DivisorCodes21) 4
        (16 * j.val) =
      true :=
  match j with
  | ⟨0, _⟩ => part1Product21_window0
  | ⟨1, _⟩ => part1Product21_window1
  | ⟨2, _⟩ => part1Product21_window2
  | ⟨3, _⟩ => part1Product21_window3
  | ⟨4, _⟩ => part1Product21_window4
  | ⟨5, _⟩ => part1Product21_window5
  | ⟨6, _⟩ => part1Product21_window6
  | ⟨7, _⟩ => part1Product21_window7

end PseudoPrime.LLS
