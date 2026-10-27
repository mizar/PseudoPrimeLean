/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SmallPart1.Block00

/-! # Finite original LLS Part 1 product checks for one 128-modulus block -/

@[expose] public section

namespace PseudoPrime.LLS.SmallPart1

/-- Exact integer product codes for this block.
Zero padding lies outside the target range. Every eligible code is checked below. -/
def block04Codes : Array ℕ :=
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

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block04_check_0 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 517 block04Codes) 4 0 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block04_check_1 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 517 block04Codes) 4 16 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block04_check_2 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 517 block04Codes) 4 32 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block04_check_3 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 517 block04Codes) 4 48 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block04_check_4 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 517 block04Codes) 4 64 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block04_check_5 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 517 block04Codes) 4 80 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block04_check_6 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 517 block04Codes) 4 96 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block04_check_7 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 517 block04Codes) 4 112 = true := by
  decide +kernel

/-- Input: a window index. Claim: that window passes all finite checks.
Proof: select one of the eight kernel proofs. Role: the generic block soundness input. -/
theorem block04_check (j : Fin 8) :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 517 block04Codes) 4 (16 * j.val) =
      true := by
  fin_cases j
  · exact block04_check_0
  · exact block04_check_1
  · exact block04_check_2
  · exact block04_check_3
  · exact block04_check_4
  · exact block04_check_5
  · exact block04_check_6
  · exact block04_check_7

end PseudoPrime.LLS.SmallPart1
