/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianGammaCutoffExecution

/-! # Bounded-memory partition of the Gaussian midpoint certificate -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Partition a finite sum into n adjacent blocks of length m.
Induction and the range-add identity avoid expanding the large full range.
This permits bounded-memory kernel verification of integer certificates. -/
theorem sum_range_blocks {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n m : ℕ) :
    (∑ k ∈ Finset.range (n * m), f k) =
      ∑ b ∈ Finset.range n, ∑ k ∈ Finset.range m, f (b * m + k) := by
  induction n with
  | zero => simp only [zero_mul, Finset.sum_range_zero]
  | succ n ih => rw [Nat.succ_mul, Finset.sum_range_add f (n * m) m, ih, Finset.sum_range_succ]

/-- One block of 250 consecutive midpoint integer contributions.
The block index chooses its starting node. This bounds the size of each kernel computation. -/
def gaussianCutoffMidpointBlock (b : ℕ) : ℕ :=
  ∑ k ∈ Finset.range 250,
    gaussianCutoffNodeLowerFast (((2 * (b * 250 + k) + 1 : ℕ) : ℤ) - 16000) / 2000

/-- The 16,000-node execution sum is the sum of 64 blocks of 250 nodes.
Use the generic block partition identity. Exact block values can be verified separately. -/
theorem gaussianCutoffMidpointLowerFast_eq_blocks :
    gaussianCutoffMidpointLowerFast = ∑ b ∈ Finset.range 64, gaussianCutoffMidpointBlock b := by
  exact
    sum_range_blocks (fun k ↦ gaussianCutoffNodeLowerFast (((2 * k + 1 : ℕ) : ℤ) - 16000) / 2000) 64
      250

end PseudoPrime.Analysis
