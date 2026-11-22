/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.DyadicEM8Intervals

/-! # Independent checks for factor-product blocks -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A fixed binary tree of saved rectangles. A leaf contains one rectangle and a branch holds
two disjoint subtrees. Certificate data can use a balanced tree to share the same saved inputs
among independent block checks without storing a linear update history. -/
inductive BoxTree where
  | leaf (box : Analysis.IntegerInterval × Analysis.IntegerInterval)
  | node (left right : BoxTree)

/-- Select a rectangle by consuming one direction per branch. A path ending at a branch or
continuing beyond a leaf returns `none`; no list element is selected by a numeric index. -/
def BoxTree.lookup :
    BoxTree → List Bool → Option (Analysis.IntegerInterval × Analysis.IntegerInterval)
  | .leaf box, [] => some box
  | .node left _, false :: path => left.lookup path
  | .node _ right, true :: path => right.lookup path
  | _, _ => none

/-- Produce `depth` binary directions, most significant bit first, for a natural key.
For depth eight and keys below 256 this gives one path to each leaf of a complete tree. -/
def boxTreeBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | depth + 1, key => key.testBit depth :: boxTreeBits depth key

/-- Read a saved odd-base rectangle from a fixed tree using the key `n / 2`.
The fallback is used only for absent paths; a consumer proves the required block checks for
the actual tree. The function does not construct or re-evaluate earlier factor rows. -/
def oddBoxTreeFamily (tree : BoxTree) (depth : ℕ)
    (fallback : Analysis.IntegerInterval × Analysis.IntegerInterval) (n : ℕ) :
    Analysis.IntegerInterval × Analysis.IntegerInterval :=
  (tree.lookup (boxTreeBits depth (n / 2))).getD fallback

/-- Check the rounded product equalities for a supplied block of factor triples.
The scale and rectangle family are shared inputs; the list is traversed directly, and no
other block or prefix is evaluated. A consumer can check disjoint blocks independently. -/
def boxBlockCheck [DecidableEq Analysis.IntegerInterval] (G : ℤ)
    (B : ℕ → Analysis.IntegerInterval × Analysis.IntegerInterval) (rows : List (ℕ × ℕ × ℕ)) :
    Bool :=
  rows.all fun (n, a, b) ↦ decide (B n = Analysis.roundedComplexProduct G (B a) (B b))

/-- A successful block check proves the product equality for every triple in that block.
The membership proof selects a checked proposition without accessing a list by index.
This theorem lets a parent proof consume separately verified block results. -/
theorem boxBlockCheck_sound [DecidableEq Analysis.IntegerInterval] (G : ℤ)
    (B : ℕ → Analysis.IntegerInterval × Analysis.IntegerInterval) (rows : List (ℕ × ℕ × ℕ))
    (h : boxBlockCheck G B rows = true) (n a b : ℕ) (hm : (n, a, b) ∈ rows) :
    B n = Analysis.roundedComplexProduct G (B a) (B b) := by
  exact of_decide_eq_true ((List.all_eq_true.mp h) (n, a, b) hm)

/-- A checked row and certified parent rectangles enclose the corresponding composite term.
The row's factor identity and positivity are supplied separately, so each independently
verified block can be combined with the common factor-family induction without rechecking it. -/
theorem boxBlock_term [DecidableEq Analysis.IntegerInterval] (G : ℤ)
    (B : ℕ → Analysis.IntegerInterval × Analysis.IntegerInterval) (rows : List (ℕ × ℕ × ℕ))
    (h : boxBlockCheck G B rows = true) (s : ℂ) (n a b : ℕ) (hm : (n, a, b) ∈ rows) (hG : 0 < G)
    (ha : 0 < a) (hb : 0 < b) (hab : a * b = n)
    (hA : Analysis.complexIntervalContains (B a).1 (B a).2 G (dyadicPowerTerm s a))
    (hB : Analysis.complexIntervalContains (B b).1 (B b).2 G (dyadicPowerTerm s b)) :
    Analysis.complexIntervalContains (B n).1 (B n).2 G (dyadicPowerTerm s n) := by
  rw [boxBlockCheck_sound G B rows h n a b hm]
  exact factoredTerm_contains G (B a) (B b) s a b n hG ha hb hab hA hB

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
