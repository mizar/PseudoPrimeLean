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

/-- Exact product codes for the 128 positions starting at 517.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1ProductCodes04 : Array ℕ :=
  #[34879874, 101452037, 35400450, 2612097335951098627, 33283, 34870539, 33410, 38019203,
    9689482661634, 16773, 34880515, 2648126270375462149, 32389, 68947203, 34876290, 9552109241475,
    67640839, 34870791, 34354434, 9139724750983, 34876546, 17155, 34354306, 9689482660103, 34562,
    34349511, 34876674, 9139826459651, 67640067, 9964427674373, 34946, 34873859, 101977858,
    169608451, 36454146, 2540039741879616901, 104076163, 17669, 9552076212482, 35398275, 35586,
    101975947, 101455106, 2648126270410064643, 9689480303621, 17923, 35970, 9689481612165, 67640323,
    18051, 101977474, 9277164228995, 36355, 9552042658061, 36483, 9139724750599, 35401602, 34348555,
    35403522, 9689481612293, 36869, 17411, 34091013, 9552076211971, 34356610, 35395589, 34357506,
    9552041611781, 9277335143170, 18691, 37506, 9689482660485, 101455490, 36445443, 36974850,
    9277197781251, 37891, 35395205, 9552074902531, 35398915, 36450690, 38019335, 38279,
    2612097335917544717, 38407, 104073859, 102502530, 36447623, 34354946, 34871559, 38787,
    9277164229123, 9689481090306, 67899143, 34882818, 9552042658821, 39170, 19589, 9964391762439,
    2612097473355974531, 39427, 38017413, 39554, 9552042659587, 34877826, 19857, 34882051,
    2612097335950574343, 32002, 19985, 9277164230274, 34350853, 67642371, 10101866627853, 40323,
    9552042136451, 34878594, 20227, 34094851, 9552042659077, 101455106, 35398403, 35402882,
    9552076212227, 40963, 35396229, 41099, 9689481089155]

/-- Exact divisor codes for the 128 positions starting at 517.
Definition: the displayed integer array, with zero padding beyond the finite target range.
Output: untrusted codes indexed by local position. Role: the checked windows below. -/
def part1DivisorCodes04 : Array ℕ :=
  #[2153668619, 282114390921218, 1096450051, 422439562153986, 521, 352346232492034, 523, 1090949122,
    492705227112451, 571379714, 2688438289, 422405739024386, 20503, 282389268566018, 2155249667,
    352173897453570, 2152882189, 212639536287746, 1624666117, 1619431426, 1097236483, 572166146,
    3222695943, 492671403986946, 541, 572428290, 1097498627, 2686619650, 1624928261,
    55369998324470288386, 547, 1091735554, 2155511811, 422405202415618, 2688176147, 352243153276930,
    1620996103, 573214722, 282114390654979, 1091997698, 557, 352380592230402, 2153144333,
    492705227116546, 422507745542147, 573739010, 563, 282286725959682, 1625452549, 574001154,
    3759046659, 1619955714, 569, 46160137052137885698, 571, 422439026069506, 1098809347,
    282183110397954, 2687397893, 4295397378, 577, 3223490562, 1099071491, 352345695883266,
    1621520391, 212776975241218, 2154455051, 1620217858, 422439562149891, 575311874, 587,
    492705763725314, 2688438291, 282492347781122, 1099595779, 2152370178, 593, 422405739024386,
    422508281884677, 1093308418, 1099857923, 352242080845826, 599, 492671403986946, 601,
    282217470136322, 2156298243, 1093570562, 3222695941, 212845694717954, 607, 2686881794,
    352345696141315, 282526707519490, 2153668621, 422508818239490, 613, 577146882, 282183110131715,
    422405202677762, 617, 212880054456322, 619, 352380055621634, 2687401987, 577671170, 1622306823,
    422440098762754, 28677, 577933314, 422542105280515, 1094356994, 2689228817,
    64579859528083214338, 631, 1621004290, 1101430787, 578457602, 1627287557, 282389805174786,
    3222958087, 352345159798786, 2156822531, 3758788610, 641, 212948773933058, 643, 352242616930306]

/-- Claim: the sixteen positions starting at local index 0 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product04_window0 :
    unitGenerationAll (part1ProductLeaf 517 part1ProductCodes04 part1DivisorCodes04) 4 0 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 16 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product04_window1 :
    unitGenerationAll (part1ProductLeaf 517 part1ProductCodes04 part1DivisorCodes04) 4 16 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 32 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product04_window2 :
    unitGenerationAll (part1ProductLeaf 517 part1ProductCodes04 part1DivisorCodes04) 4 32 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 48 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product04_window3 :
    unitGenerationAll (part1ProductLeaf 517 part1ProductCodes04 part1DivisorCodes04) 4 48 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 64 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product04_window4 :
    unitGenerationAll (part1ProductLeaf 517 part1ProductCodes04 part1DivisorCodes04) 4 64 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 80 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product04_window5 :
    unitGenerationAll (part1ProductLeaf 517 part1ProductCodes04 part1DivisorCodes04) 4 80 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 96 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product04_window6 :
    unitGenerationAll (part1ProductLeaf 517 part1ProductCodes04 part1DivisorCodes04) 4 96 =
      true := by
  decide +kernel

/-- Claim: the sixteen positions starting at local index 112 pass coverage.
Proof: kernel computation with default resources. Role: one independent certificate window. -/
private theorem part1Product04_window7 :
    unitGenerationAll (part1ProductLeaf 517 part1ProductCodes04 part1DivisorCodes04) 4 112 =
      true := by
  decide +kernel

/-- Input: a window index below eight. Claim: its sixteen-position check succeeds.
Proof: select the corresponding kernel certificate. Role: the catalog's block interface. -/
theorem part1Product04_checks (j : Fin 8) :
    unitGenerationAll (part1ProductLeaf 517 part1ProductCodes04 part1DivisorCodes04) 4
        (16 * j.val) =
      true :=
  match j with
  | ⟨0, _⟩ => part1Product04_window0
  | ⟨1, _⟩ => part1Product04_window1
  | ⟨2, _⟩ => part1Product04_window2
  | ⟨3, _⟩ => part1Product04_window3
  | ⟨4, _⟩ => part1Product04_window4
  | ⟨5, _⟩ => part1Product04_window5
  | ⟨6, _⟩ => part1Product04_window6
  | ⟨7, _⟩ => part1Product04_window7

end PseudoPrime.LLS
