/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SmallPart1.Block01

/-! # Finite original LLS Part 1 product checks for one 128-modulus block -/

@[expose] public section

namespace PseudoPrime.LLS.SmallPart1

/-- Exact integer product codes for this block.
Zero padding lies outside the target range. Every eligible code is checked below. -/
def block05Codes : Array ℕ :=
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

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block05_check_0 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 645 block05Codes) 4 0 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block05_check_1 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 645 block05Codes) 4 16 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block05_check_2 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 645 block05Codes) 4 32 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block05_check_3 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 645 block05Codes) 4 48 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block05_check_4 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 645 block05Codes) 4 64 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block05_check_5 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 645 block05Codes) 4 80 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block05_check_6 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 645 block05Codes) 4 96 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block05_check_7 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 645 block05Codes) 4 112 = true := by
  decide +kernel

/-- Input: a window index. Claim: that window passes all finite checks.
Proof: select one of the eight kernel proofs. Role: the generic block soundness input. -/
theorem block05_check (j : Fin 8) :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 645 block05Codes) 4 (16 * j.val) =
      true := by
  fin_cases j
  · exact block05_check_0
  · exact block05_check_1
  · exact block05_check_2
  · exact block05_check_3
  · exact block05_check_4
  · exact block05_check_5
  · exact block05_check_6
  · exact block05_check_7

end PseudoPrime.LLS.SmallPart1
