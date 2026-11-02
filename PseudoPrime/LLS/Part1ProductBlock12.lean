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

/-- Exact product codes for the 128 positions starting at 1541.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1ProductCodes12 : Array ℕ :=
  #[370413698, 35405829, 98693, 9277163712517, 9552042668802, 49411, 9552209120259, 9964427676293,
    99074, 169611011, 9277164239234, 9964392028165, 99331, 10376744536325, 36477698, 35414275,
    35422466, 35412493, 99731, 713079987039861715239687, 103561091, 172757383, 34112007,
    9277164235779, 67653137, 34881291, 100227, 9552042142211, 36471426, 68953859, 100482,
    9964359524485, 34907394, 50309, 9689549770498, 9964359004419, 34388098, 35406213, 100995,
    9689482667779, 9552041360391, 36983811, 101253, 2648126270375464709, 68964098, 203165445,
    34897538, 34366213, 34384258, 9552079359239, 101465858, 9277164237187, 34898562, 50947,
    9002320405250, 2864299052557403269, 102155, 34888707, 9552074907143, 9552076215299, 102403,
    34882055, 101464322, 35415043, 9689481622786, 35412485, 102789, 2540039741879095431, 102919,
    10101799526659, 34899330, 9139791859463, 103171, 34882311, 9277197001731, 10101831506179,
    9964359005314, 51715, 103554, 9689482664711, 103682, 51843, 34899714, 2612097335917024515,
    67914498, 36979595, 104067, 9277163711749, 101985538, 36458755, 36482563, 2540039741980279813,
    34914439, 102506371, 9689513859847, 34367005, 104706, 27556613718789, 34388226,
    2540039192158407175, 35424386, 52483, 34128643, 9552042664453, 9552041624834, 52611, 101985538,
    9689480573701, 269228037, 10101935310087, 101203719, 9552042142595, 9552042147586, 52871,
    36480259, 2540039741879619717, 105995, 53011, 9964426105730, 9689482668291, 168306055, 39601413,
    106371, 9552075692035, 9552210430210, 36459523, 106626, 9964359524997]

/-- Exact divisor codes for the 128 positions starting at 1541.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1DivisorCodes12 : Array ℕ :=
  #[2693165079, 215526828056578, 1543, 1635950594, 283249335771139, 638230530, 492877026852871,
    422956568584194, 1549, 422749873545218, 423024215367683, 2160238594, 1553, 55424111889816657922,
    1651412997, 1124769794, 2170200067, 422920600330242, 1559, 64593511065527427074, 1639874567,
    353067788050434, 1142071299, 492980106600450, 1651675141, 422716050415618, 1567, 4295925762,
    1142333443, 284177048707074, 1571, 283730908717058, 3759833099, 640065538, 563075045040131,
    1636474882, 2695262227, 215629907271682, 1579, 353205763088386, 422748801376259,
    283420597854210, 1583, 563144301125634, 1652199429, 352895452749826, 3761152003, 1125818370,
    1640398855, 46236838984365285378, 3226886181, 1636737026, 2692128771, 641376258,
    422714977718277, 64606951530025099266, 1597, 423023679283202, 422920599543811, 4832534530, 1601,
    353378098388994, 1640660999, 1126342658, 283318055247875, 353102147788802, 1607,
    353000141266946, 1609, 64615958728743231490, 2170986499, 422748800851970, 1613, 215732986486786,
    492911387119621, 2160762882, 563143227908099, 642949122, 1619, 633409966088194, 1621, 643211266,
    1144692739, 422714977198082, 3759837189, 215767346225154, 1627, 422852416675842, 2171248643,
    284280127922178, 1641185287, 492878636163074, 2693689367, 422954960068610, 283352414986243,
    1127391234, 1637, 64593440731142987778, 2167046155, 422921672237058, 1145479171, 644521986,
    2691325983, 283833987932162, 423024214839301, 644784130, 2692390915, 2161025026, 2697097233,
    73812379502754832386, 2164158477, 352861629095938, 422714441900035, 645308418, 1654034437,
    492981715378178, 1657, 645570562, 353205226479619, 353274482565122, 2167308299, 215870425440258,
    1663, 3759841282, 422852952760323, 492877562945538, 1667, 283868347670530]

/-- Claim: the sixteen positions starting at local index 0 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product12_window0 :
    unitGenerationAll (part1ProductLeaf 1541 part1ProductCodes12 part1DivisorCodes12) 4 0 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 16 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product12_window1 :
    unitGenerationAll (part1ProductLeaf 1541 part1ProductCodes12 part1DivisorCodes12) 4 16 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 32 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product12_window2 :
    unitGenerationAll (part1ProductLeaf 1541 part1ProductCodes12 part1DivisorCodes12) 4 32 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 48 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product12_window3 :
    unitGenerationAll (part1ProductLeaf 1541 part1ProductCodes12 part1DivisorCodes12) 4 48 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 64 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product12_window4 :
    unitGenerationAll (part1ProductLeaf 1541 part1ProductCodes12 part1DivisorCodes12) 4 64 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 80 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product12_window5 :
    unitGenerationAll (part1ProductLeaf 1541 part1ProductCodes12 part1DivisorCodes12) 4 80 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 96 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product12_window6 :
    unitGenerationAll (part1ProductLeaf 1541 part1ProductCodes12 part1DivisorCodes12) 4 96 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 112 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product12_window7 :
    unitGenerationAll (part1ProductLeaf 1541 part1ProductCodes12 part1DivisorCodes12) 4 112 =
      true := by
  decide +kernel

/-- Input: a window index below eight. Claim: its sixteen-position check succeeds.
Proof: select the corresponding kernel certificate. Role: the catalog's block interface. -/
theorem part1Product12_checks (j : Fin 8) :
    unitGenerationAll (part1ProductLeaf 1541 part1ProductCodes12 part1DivisorCodes12) 4
        (16 * j.val) =
      true :=
  match j with
  | ⟨0, _⟩ => part1Product12_window0
  | ⟨1, _⟩ => part1Product12_window1
  | ⟨2, _⟩ => part1Product12_window2
  | ⟨3, _⟩ => part1Product12_window3
  | ⟨4, _⟩ => part1Product12_window4
  | ⟨5, _⟩ => part1Product12_window5
  | ⟨6, _⟩ => part1Product12_window6
  | ⟨7, _⟩ => part1Product12_window7

end PseudoPrime.LLS
