/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaScaledRampBlocks

/-! # Balanced evaluation of exact scaled prefix moments -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The integer kth moment of rows with natural index at most bound.
Only integer weights, natural comparisons and integer powers are evaluated.
Dividing by the common positive scale later recovers the rational moment. -/
def gammaScaledIntegerPrefix (rows : List (GammaFiniteRampRow × ℤ)) (bound k : ℕ) : ℤ :=
  ((rows.filter (fun rz ↦ decide (rz.1.index ≤ bound))).map
      (fun rz ↦ rz.2 * (rz.1.index : ℤ) ^ k)).sum

/-- Input: any two finite row lists, prefix bound and moment index.
Claim: integer prefix moments add over concatenation.
Proof: distribute filter, map and sum over the append.
This permits balanced evaluation without a long flat-list recursion. -/
theorem gamma_scaled_integer_prefix_append (l r : List (GammaFiniteRampRow × ℤ)) (bound k : ℕ) :
    gammaScaledIntegerPrefix (l ++ r) bound k =
      gammaScaledIntegerPrefix l bound k + gammaScaledIntegerPrefix r bound k := by
  simp only [gammaScaledIntegerPrefix, List.filter_append, List.map_append, List.sum_append]

/-- Input: exact scaled integer weights for every row.
Claim: the integer prefix moment is D times the exact rational moment.
Proof: cast the finite sum and use the checked weight equality row by row.
No rounding or subtraction of analytic bounds occurs in this identity. -/
theorem gamma_scaled_integer_prefix_cast (rows : List (GammaFiniteRampRow × ℤ)) (D : ℕ)
    (hweights : ∀ rz ∈ rows, (rz.2 : ℚ) = (D : ℚ) * (rz.1.logLower * rz.1.rampLower ^ 2))
    (bound k : ℕ) :
    (gammaScaledIntegerPrefix rows bound k : ℚ) =
      (D : ℚ) *
        gammaRationalListMoment ((rows.map Prod.fst).filter (fun r ↦ decide (r.index ≤ bound)))
          (fun r ↦ r.logLower * r.rampLower ^ 2) (fun r ↦ (r.index : ℚ)) k := by
  simp only [gammaScaledIntegerPrefix, Int.cast_list_sum, List.map_map, List.filter_map,
    gammaRationalListMoment, Function.comp_def, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro rz hz
  rw [hweights rz (List.mem_filter.mp hz).1]
  ring

/-- A balanced tree of checked blocks on adjacent intervals.
Leaves retain their checked rational and integer data. Nodes certify adjacency
by their indices. The tree supplies both a reusable certificate and a shallow
integer-prefix evaluator for arbitrarily many rows. -/
inductive GammaScaledRampTree (a : ℚ) (D : ℕ) : ℕ → ℕ → Type where
  /-- One already checked finite row block. -/
  | leaf {lo hi : ℕ} (b : GammaScaledRampBlock a D lo hi) : GammaScaledRampTree a D lo hi
  /-- Two subtrees on adjacent natural intervals. -/
  |
  node {lo mid hi : ℕ} (l : GammaScaledRampTree a D lo mid) (r : GammaScaledRampTree a D mid hi) :
    GammaScaledRampTree a D lo hi

/-- The checked block represented by a balanced tree.
Merge only proof-carrying blocks; all leaf checks are reused. This gives access
to the existing rational ramp-certificate and witness interfaces. -/
def GammaScaledRampTree.block {a : ℚ} {D lo hi : ℕ} (t : GammaScaledRampTree a D lo hi) :
    GammaScaledRampBlock a D lo hi :=
  match t with
  | .leaf b => b
  | .node l r => l.block.append r.block

/-- The exact integer prefix moment evaluated through the tree.
At each leaf evaluate its short row list, and at each node add two integers.
The natural prefix bound and moment index remain arbitrary parameters. -/
def GammaScaledRampTree.prefixMoment {a : ℚ} {D lo hi : ℕ} (t : GammaScaledRampTree a D lo hi)
    (bound k : ℕ) : ℤ :=
  match t with
  | .leaf b => gammaScaledIntegerPrefix b.rows bound k
  | .node l r => l.prefixMoment bound k + r.prefixMoment bound k

/-- Input: any checked block tree, bound and moment index.
Claim: balanced evaluation equals the flat integer prefix sum.
Proof: induct on the tree and use additivity over concatenation.
This identifies the efficient evaluator with the exact row data. -/
theorem GammaScaledRampTree.prefixMoment_eq {a : ℚ} {D lo hi : ℕ}
    (t : GammaScaledRampTree a D lo hi) (bound k : ℕ) :
    t.prefixMoment bound k = gammaScaledIntegerPrefix t.block.rows bound k := by
  induction t with
  | leaf b => rfl
  | node l r il
    ir =>
    change
      l.prefixMoment bound k + r.prefixMoment bound k =
        gammaScaledIntegerPrefix (l.block.rows ++ r.block.rows) bound k
    rw [gamma_scaled_integer_prefix_append, il, ir]

/-- Input: any checked tree, natural bound and moment index.
Claim: its integer evaluator casts to D times the actual rational prefix moment.
Proof: use the flat evaluator identity and the block's exact weight facts.
This is the common soundness theorem for generated integer moment tables. -/
theorem GammaScaledRampTree.prefixMoment_cast {a : ℚ} {D lo hi : ℕ}
    (t : GammaScaledRampTree a D lo hi) (bound k : ℕ) :
    (t.prefixMoment bound k : ℚ) =
      (D : ℚ) *
        gammaRationalListMoment
          ((t.block.rows.map Prod.fst).filter (fun r ↦ decide (r.index ≤ bound)))
          (fun r ↦ r.logLower * r.rampLower ^ 2) (fun r ↦ (r.index : ℚ)) k := by
  rw [t.prefixMoment_eq]
  exact
    gamma_scaled_integer_prefix_cast t.block.rows D
      (fun rz hz ↦ (List.forall_iff_forall_mem.mp t.block.facts.2.1 rz hz).2.1) bound k

end PseudoPrime.Analysis
