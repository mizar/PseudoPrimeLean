/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Part1ProductCertificates

/-! # Finite original LLS Part 1 product checks for one 128-modulus block -/

@[expose] public section

namespace PseudoPrime.LLS.SmallPart1

/-- Exact integer product codes for this block.
Zero padding lies outside the target range. Every eligible code is checked below. -/
def block03Codes : Array ℕ :=
  #[24834, 10101833073415, 34876419, 9552042134147, 34873474, 12547, 34350850, 9689481611141, 25349,
    12675, 9139793953922, 9552076211459, 25603, 34869383, 101453570, 38541571, 35396354, 34870531,
    34876674, 2540039741879616517, 35402498, 69995015, 34087429, 34347397, 34352002, 35393669,
    34351362, 9552075687427, 34873986, 35395203, 26754, 2648126270376510225, 26882, 13443, 34873986,
    9552042134787, 67638275, 34869639, 101453570, 34871939, 9277164228354, 36967683, 27527,
    9689481611525, 27653, 103548803, 10101832025858, 34347787, 34877826, 35394053, 28049,
    2612097473356498179, 101976706, 68422659, 28290, 9552042658053, 67638787, 14211, 34874626,
    9552042134531, 28675, 36441869, 168299011, 34872323, 35399045, 14469, 9552209380098,
    2612097473356498053, 29197, 14599, 34087941, 9552042658563, 29442, 9964361090949, 29571,
    9277197780739, 9552041348871, 14851, 29826, 9552109765381, 101453954, 36443907, 35399429,
    9552042135171, 34092163, 35394437, 35400962, 9552042134531, 36448002, 15239, 30605,
    2612097473390051851, 204212482, 15367, 9552042135682, 34347911, 67639303, 10373, 31107,
    9139724750599, 35399810, 38540547, 31362, 9689481087495, 67640323, 101452037, 10101798473474,
    9277164228355, 36451459, 36443269, 31879, 36444419, 34875778, 16011, 32133, 2612097335986225541,
    69998850, 35396485, 35399426, 34873219, 32514, 9689516213255, 101454341, 34873347, 303301762,
    16387, 34353922, 9964359518853]

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block03_check_0 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 389 block03Codes) 4 0 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block03_check_1 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 389 block03Codes) 4 16 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block03_check_2 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 389 block03Codes) 4 32 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block03_check_3 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 389 block03Codes) 4 48 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block03_check_4 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 389 block03Codes) 4 64 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block03_check_5 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 389 block03Codes) 4 80 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block03_check_6 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 389 block03Codes) 4 96 = true := by
  decide +kernel

/-- Claim: all sixteen local product checks pass.
Proof: kernel computation with default resources. Role: a bounded certificate window. -/
private theorem block03_check_7 :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 389 block03Codes) 4 112 = true := by
  decide +kernel

/-- Input: a window index. Claim: that window passes all finite checks.
Proof: select one of the eight kernel proofs. Role: the generic block soundness input. -/
theorem block03_check (j : Fin 8) :
    NumberTheory.generationBalancedAll (llsPart1ProductLeaf 389 block03Codes) 4 (16 * j.val) =
      true := by
  fin_cases j
  · exact block03_check_0
  · exact block03_check_1
  · exact block03_check_2
  · exact block03_check_3
  · exact block03_check_4
  · exact block03_check_5
  · exact block03_check_6
  · exact block03_check_7

end PseudoPrime.LLS.SmallPart1
