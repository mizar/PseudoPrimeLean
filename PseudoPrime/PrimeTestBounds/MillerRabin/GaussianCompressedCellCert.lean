/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompressedMoment
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompressedMoment

/-! # Independent certificates for compressed high Gaussian cells -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Number of cells in one compressed correction plan. -/
public def highCompressedCellCount (K : HighGaussianKernel) (j : Fin 3) : ℕ :=
  planCount K j

/-- The sign check of a single compressed cell, including the trivial mixed case. -/
public def highCompressedCellCheck (K : HighGaussianKernel) (j : Fin 3) (i : ℕ) : Bool :=
  planSignCheck K j i

/-- The rational charge of one compressed cell. -/
public def highCompressedCellCharge (K : HighGaussianKernel) (j : Fin 3) (i : ℕ) : ℚ :=
  planCharge K j i

/-- Independently checked cell signs certify the full compressed plan. -/
public theorem high_compressed_sign_of_cells (K : HighGaussianKernel) (j : Fin 3)
    (h : ∀ i : Fin (highCompressedCellCount K j), highCompressedCellCheck K j i = true) :
    highCompressedSignCheck K j = true := by
  apply List.all_eq_true.mpr
  intro i hi
  exact h ⟨i, List.mem_range.mp hi⟩

/-- Independent cell charge bounds can be added before comparing with the cap. -/
public theorem high_compressed_charge_of_cells (K : HighGaussianKernel) (j : Fin 3) (b : ℕ → ℚ)
    (h : ∀ i : Fin (highCompressedCellCount K j), highCompressedCellCharge K j i ≤ b i) :
    highCompressedMomentCharge K j ≤ ∑ i ∈ Finset.range (highCompressedCellCount K j), b i := by
  apply Finset.sum_le_sum
  intro i hi
  exact h ⟨i, Finset.mem_range.mp hi⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
