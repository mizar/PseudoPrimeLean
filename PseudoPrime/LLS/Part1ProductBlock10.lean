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

/-- Exact product codes for the 128 positions starting at 1285.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1ProductCodes10 : Array ℕ :=
  #[67649539, 41099, 9277231337218, 2540039741879095427, 82443, 9552042661133, 82562, 9277164233731,
    35416965, 41349, 9689652529410, 9689481616133, 82961, 36980871, 34106373, 9552076214019, 83202,
    9964426102667, 83335, 9277164234883, 10101832029442, 41731, 83586, 9277164231435, 9689480313859,
    38027523, 9277164237186, 9689581226501, 67914498, 102502917, 35422978, 9964359000707, 38038917,
    42119, 84365, 713079987039861682210055, 84493, 42263, 101982082, 36983427, 68960514,
    9139762498567, 84867, 9277164235011, 35417730, 10376749254915, 77442, 9552109766917, 101987459,
    34884867, 9552074905095, 9277164235139, 36474499, 36976517, 101462786, 9689482666247, 34893570,
    171183879, 34905091, 2612097473357548549, 70533890, 43013, 34107405, 34362387, 35429762,
    36449549, 101462021, 9552041617159, 9139858704903, 43267, 34375426, 9552042662917, 34905986,
    101455877, 102507909, 2648134929063085059, 87043, 36452485, 34906370, 11338883270531,
    2720184139460117250, 43653, 87429, 2612097473423606917, 85250, 68952579, 34107917, 34883971,
    87810, 34879751, 168564994, 9277164235267, 34106373, 68429571, 34378498, 2612097473357548295,
    88322, 44163, 34894594, 9277164235523, 67650819, 9964428199813, 302518789, 34887299, 34894722,
    35407107, 36478722, 2540039467036313349, 101986691, 135009285, 9552109768450, 34363143,
    34119043, 39598597, 89485, 2648126270376513283, 38040706, 44803, 34907394, 9552109766917,
    67651075, 305400069, 9689548198018, 9277164234755, 90115, 9689482663687, 34120707, 34887683]

/-- Exact divisor codes for the 128 positions starting at 1285.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1DivisorCodes10 : Array ℕ :=
  #[1644335109, 621191170, 492808307118083, 422611897982978, 1289, 46214320985691561986, 1291,
    492911387123714, 1130270723, 621715458, 422852416147461, 4832272386, 1297, 352861092749314,
    1130532867, 492809380077570, 1301, 55410601090397675522, 1303, 1632018434, 422715513802755,
    622501890, 1307, 283352414724098, 492877026590727, 283730372108290, 422611362680835, 2689769474,
    2160750605, 353102683611138, 1645121541, 352655470665730, 1131319299, 623288322, 1319,
    64589007465363185666, 1321, 623550466, 4295921667, 1117167618, 2691338245, 64602377664195895298,
    1327, 2158403586, 1131843587, 64606951529488490498, 28683, 422852952498178, 2690015263,
    422713905553410, 283008817598467, 1632542722, 1635680263, 214942175633410, 2161012749,
    352999604658178, 2167050243, 352895452487682, 2694737937, 563075044777986, 1645907973,
    625123330, 1132630019, 1117954050, 2693689363, 633409429217282, 1635942407, 3759841282,
    422920599277571, 625647618, 1646170117, 283421134200834, 2692112407, 283145719947266,
    2167312387, 492878099554306, 1361, 215010895110146, 2690539549, 422748800589826,
    64593440730606374915, 626434050, 1367, 492912459030530, 24613, 283833451323394, 1133678595,
    4295925762, 1373, 215045254848514, 3759575045, 2690031618, 3760361475, 352758013796354,
    1636466695, 55392657026272632834, 1381, 627482626, 1134202883, 1633329154, 1646956549,
    64588937130978746370, 2693951507, 1119264770, 1134465027, 283867811061762, 2161537037,
    422715513544706, 1636728839, 422920600068098, 422749873541123, 1119526914, 2164158475,
    215113974325250, 1399, 563075045040130, 1134989315, 628793346, 2692374551, 492809379815426,
    1647480837, 422851880853506, 352999068045315, 3759579138, 1409, 46223328184946302978,
    2695262225, 1120051202]

/-- Claim: the sixteen positions starting at local index 0 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product10_window0 :
    unitGenerationAll (part1ProductLeaf 1285 part1ProductCodes10 part1DivisorCodes10) 4 0 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 16 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product10_window1 :
    unitGenerationAll (part1ProductLeaf 1285 part1ProductCodes10 part1DivisorCodes10) 4 16 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 32 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product10_window2 :
    unitGenerationAll (part1ProductLeaf 1285 part1ProductCodes10 part1DivisorCodes10) 4 32 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 48 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product10_window3 :
    unitGenerationAll (part1ProductLeaf 1285 part1ProductCodes10 part1DivisorCodes10) 4 48 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 64 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product10_window4 :
    unitGenerationAll (part1ProductLeaf 1285 part1ProductCodes10 part1DivisorCodes10) 4 64 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 80 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product10_window5 :
    unitGenerationAll (part1ProductLeaf 1285 part1ProductCodes10 part1DivisorCodes10) 4 80 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 96 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product10_window6 :
    unitGenerationAll (part1ProductLeaf 1285 part1ProductCodes10 part1DivisorCodes10) 4 96 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 112 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product10_window7 :
    unitGenerationAll (part1ProductLeaf 1285 part1ProductCodes10 part1DivisorCodes10) 4 112 =
      true := by
  decide +kernel

/-- Input: a window index below eight. Claim: its sixteen-position check succeeds.
Proof: select the corresponding kernel certificate. Role: the catalog's block interface. -/
theorem part1Product10_checks (j : Fin 8) :
    unitGenerationAll (part1ProductLeaf 1285 part1ProductCodes10 part1DivisorCodes10) 4
        (16 * j.val) =
      true :=
  match j with
  | ⟨0, _⟩ => part1Product10_window0
  | ⟨1, _⟩ => part1Product10_window1
  | ⟨2, _⟩ => part1Product10_window2
  | ⟨3, _⟩ => part1Product10_window3
  | ⟨4, _⟩ => part1Product10_window4
  | ⟨5, _⟩ => part1Product10_window5
  | ⟨6, _⟩ => part1Product10_window6
  | ⟨7, _⟩ => part1Product10_window7

end PseudoPrime.LLS
