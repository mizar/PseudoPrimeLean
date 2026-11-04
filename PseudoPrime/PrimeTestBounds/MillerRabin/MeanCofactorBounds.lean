/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.MeanCofactorGap
public import PseudoPrime.PrimeTestBounds.MillerRabin.MeanFloorNumerics

/-! # Large-cofactor witnesses with the floor budgets discharged -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For `n = m * q` with an odd prime `q`, the stated scale, theta and scalar-gap
hypotheses give an MR-rejecting prime at most `b ^ 2`. The uniform factor, floor and
logarithmic bounds discharge the floor parameters in the mean-gap criterion. This reduces
the large-cofactor branch to its three explicit theta and scalar cells. -/
theorem large_cofactor_of_mean_cells {n m q b : ℕ} (hn : 1 < n) (ho : Odd n) (hm : 1 < m)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = m * q) {α P a η : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hP : 1 ≤ P) (hP2 : P ≤ 2) (ha : (99 / 100 : ℝ) ≤ a) (ha1 : a ≤ 1) (hη : 0 ≤ 15 * η / 16)
    (hη1 : 15 * η / 16 ≤ 1) (hb : 52000 ≤ b) (hL : 0 < Real.log n) (hLU : Real.log n ≤ 40000000000)
    (hfloor : α * Real.log n ≤ (b : ℝ) + 1) (hτ : 50000 ≤ α * Real.log n)
    (hqL : α * Real.log n < Real.log q) (hu : 20 ≤ Real.log (b ^ 2 : ℕ))
    (huU : Real.log (b ^ 2 : ℕ) ≤ 48) (hθB : a * (b : ℝ) ^ 2 ≤ Chebyshev.theta (b ^ 2 : ℕ))
    (hθ : ∀ t ∈ Set.Icc ((b : ℝ) ^ 2 / 16) ((b : ℝ) ^ 2), η * t ≤ Chebyshev.theta t)
    (hupper : Chebyshev.theta (b ^ 2 : ℕ) ≤ P * (b : ℝ) ^ 2)
    (hgap :
      (1 - α) * Real.log n + 120 <
        (α / P) *
          (a / 2 + ((999 / 1000) * a + (15 * η / 16) / 2) / Real.log (b ^ 2 : ℕ) +
            ((999 / 1000) * (15 * η / 16)) / Real.log (b ^ 2 : ℕ) ^ 2) *
          Real.log n) :
    ∃ r : ℕ, r.Prime ∧ r ≤ b ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let B : ℝ := (b : ℝ) ^ 2
  let f : ℝ := a / Real.log (b ^ 2 : ℕ) + (15 * η / 16) / Real.log (b ^ 2 : ℕ) ^ 2
  let τ := α * Real.log n
  let M := ⌊B * f⌋₊
  let k := ⌊(τ - 4) * M / (P * B)⌋₊
  have hB : 0 < B := pow_pos (Nat.cast_pos.mpr (by linarith only [hb])) 2
  have hp0 : 0 < P := by linarith only [hP]
  have ⟨hf, hf2⟩ := mean_supply_factor_bounds ha ha1 hη hη1 hu huU
  have ⟨hsize, hpos, hround⟩ :=
    mean_floor_size_budgets (show (52000 : ℝ) ≤ b by exact_mod_cast hb) hτ hfloor hP hP2 hf hf2
  have hτ4 : 4 ≤ τ := by linarith only [hτ]
  have ⟨hk0, hkM, hM, hmean, _⟩ :=
    mean_floor_parameters hB hp0 (by linarith only [hf]) hτ4 hsize hpos hround
  have hkτ : (k : ℝ) ≤ τ := mean_selected_size_le hB (by linarith only [hf2]) hP hτ4 hM hmean
  have hτU : τ ≤ 40000000000 := by
    have h := mul_le_mul_of_nonneg_right hα1 hL.le
    dsimp only [τ]
    linarith only [h, hLU]
  have hloss := mean_log_loss_le (mul_pos hα hL) hτU hk0 hkτ huU
  exact
    large_cofactor_of_mean_floors hn ho hm hq hq2 hprod hα hP (by linarith only [hb]) hL hfloor hτ4
      hqL hθB hθ hupper (by linarith only [hf]) hsize hpos hround hgap hloss

end PseudoPrime.PrimeTestBounds.MillerRabin
