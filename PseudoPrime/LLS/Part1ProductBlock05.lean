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

/-- Exact product codes for the 128 positions starting at 645.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1ProductCodes05 : Array ℕ :=
  #[9277163443469, 34874371, 41349, 9689481612677, 35408002, 68947715, 9552109242242, 34875523,
    41730, 34872075, 34357506, 9689514117639, 102502917, 34873987, 42114, 2648126545254941959,
    42242, 21123, 9139758042119, 9277164229763, 9964425578754, 103549189, 34884866, 34875779,
    34092933, 36446471, 171183874, 2612097473357547013, 43013, 21523, 35400962, 34350855, 43266,
    36445189, 101455877, 2648125858093204483, 36452482, 169609091, 43653, 9689548719237, 67641859,
    18819, 34093319, 9277164229891, 67905282, 9689482660615, 44163, 34876163, 9964426102658, 22149,
    35407106, 2540039467001186059, 135009285, 22279, 34093573, 10101799522051, 44802, 102500613,
    302778626, 9277164229635, 9552042661634, 22531, 34360066, 9552042659461, 45314, 35398403,
    102503298, 9552042137091, 34886275, 10926433242117, 9964392025858, 35400835, 35404674, 22919,
    45963, 2612097473391100679, 103553411, 21891, 34094087, 34352407, 68952834, 35396485, 46469,
    2612097335983604485, 31106, 67899915, 34100227, 9964358995719, 46855, 23435, 9689482663170,
    9552042137091, 34361986, 34872839, 47235, 9552077785347, 9277231335682, 36972291, 47493,
    2540039741879093127, 68953346, 23813, 36453762, 9277164229635, 34361218, 36444429, 48003,
    9277164230403, 34881163, 68424963, 34097927, 9552111338629, 48386, 24195, 9689481091970,
    2540039741879617795, 48647, 34873223, 101456651, 35401603, 9689513856007, 24453, 34887426,
    9689481613317, 49163, 10101800046339, 34095109, 34353157]

/-- Exact divisor codes for the 128 positions starting at 645.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1DivisorCodes05 : Array ℕ :=
  #[282218006740995, 422542106071042, 647, 4295397378, 2155241483, 422440099024898, 352380055879683,
    1095143426, 653, 212983133671426, 1627815941, 2152894466, 2157084675, 282286189613058, 659,
    55365565059227357186, 661, 580292610, 422507745804291, 1621528578, 422542641627141,
    352483671445506, 2688176151, 1095667714, 1103003651, 282630323605506, 2155503627,
    492705763725314, 673, 581079042, 4295655427, 3222966274, 677, 213051853148162, 1623355399,
    422508818501634, 1103527939, 352379519537154, 683, 422543177977858, 1628602373, 3759050754,
    1103790083, 2153156610, 2154455053, 46169214620136804354, 691, 1096454146, 422405202673667,
    582389762, 1628864517, 352346232492034, 2689753105, 582651906, 1104314371, 492705763987458, 701,
    422440098762754, 2689228819, 3222704130, 282286726217731, 583176194, 1623879687,
    282492884389890, 709, 282699043082242, 2157871107, 1622315010, 2688438295, 55379005523725029378,
    422439562936325, 1097240578, 1105100803, 583962626, 719, 563040148164610, 1624141831,
    3223752706, 1105362947, 1097502722, 2688188421, 492774483202050, 727, 422439562416130, 32771,
    282733402820610, 2690015249, 282527244128258, 733, 585011202, 492705763983363, 2687406082,
    2156294155, 352552390922242, 739, 352483671707650, 422542105542659, 282389268828162, 743,
    352380592230402, 1630175237, 585797634, 2158395395, 422508282417154, 1624666119,
    563040148164610, 751, 2153680898, 1106673667, 352345160060930, 1630437381, 492705763725314, 757,
    586584066, 422611361628163, 422543178240002, 761, 213292371316738, 1624928263, 1098813442,
    422508818497539, 587108354, 2155241485, 4295397378, 769, 64588866761697955842, 1107464195,
    1099075586]

/-- Claim: the sixteen positions starting at local index 0 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product05_window0 :
    unitGenerationAll (part1ProductLeaf 645 part1ProductCodes05 part1DivisorCodes05) 4 0 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 16 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product05_window1 :
    unitGenerationAll (part1ProductLeaf 645 part1ProductCodes05 part1DivisorCodes05) 4 16 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 32 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product05_window2 :
    unitGenerationAll (part1ProductLeaf 645 part1ProductCodes05 part1DivisorCodes05) 4 32 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 48 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product05_window3 :
    unitGenerationAll (part1ProductLeaf 645 part1ProductCodes05 part1DivisorCodes05) 4 48 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 64 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product05_window4 :
    unitGenerationAll (part1ProductLeaf 645 part1ProductCodes05 part1DivisorCodes05) 4 64 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 80 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product05_window5 :
    unitGenerationAll (part1ProductLeaf 645 part1ProductCodes05 part1DivisorCodes05) 4 80 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 96 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product05_window6 :
    unitGenerationAll (part1ProductLeaf 645 part1ProductCodes05 part1DivisorCodes05) 4 96 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 112 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product05_window7 :
    unitGenerationAll (part1ProductLeaf 645 part1ProductCodes05 part1DivisorCodes05) 4 112 =
      true := by
  decide +kernel

/-- Input: a window index below eight. Claim: its sixteen-position check succeeds.
Proof: select the corresponding kernel certificate. Role: the catalog's block interface. -/
theorem part1Product05_checks (j : Fin 8) :
    unitGenerationAll (part1ProductLeaf 645 part1ProductCodes05 part1DivisorCodes05) 4
        (16 * j.val) =
      true :=
  match j with
  | ⟨0, _⟩ => part1Product05_window0
  | ⟨1, _⟩ => part1Product05_window1
  | ⟨2, _⟩ => part1Product05_window2
  | ⟨3, _⟩ => part1Product05_window3
  | ⟨4, _⟩ => part1Product05_window4
  | ⟨5, _⟩ => part1Product05_window5
  | ⟨6, _⟩ => part1Product05_window6
  | ⟨7, _⟩ => part1Product05_window7

end PseudoPrime.LLS
