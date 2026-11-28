/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassExact
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleConductors
import all PseudoPrime.LLS.PaperStatements.ShiftedPoleKernel
import Mathlib.Tactic.Ring

/-! # Critical-line mass and the high Gaussian conductor contribution -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Multiplication by the Mellin phase at positive cutoff `x` leaves the absolute
mass of the combined shifted-pole kernel unchanged on the imaginary axis. -/
public theorem high_gaussian_weighted_mass (K : HighGaussianKernel) {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ,
        ‖(∑ j ∈ Finset.range (2 * K.degree + 1),
              (K.expandedCoeff j : ℂ) *
                (LLS.PaperStatements.shiftedPoleKernel (K.logPower j) K.pole 5
                      (Nat.le_of_succ_le_succ
                        ((by decide : 2 ≤ 4).trans (high_gaussian_order_ge_four K j)))
                      (high_gaussian_pole_gt K)).function
                  (Complex.I * (t : ℂ))) *
            (x : ℂ) ^ (Complex.I * (t : ℂ))‖) =
      3 * Real.pi / 8 := by
  convert high_gaussian_mass_exact K using 1
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_im, zero_mul, mul_zero, sub_self,
    Real.rpow_zero, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  change _ * (Complex.exp ((↑(5 : ℝ) : ℂ) * (Complex.I * (t : ℂ))) / _) = _
  simp only [Complex.ofReal_ofNat, Complex.ofReal_ratCast, mul_div_assoc]

/-- For three nonzero factors of `n`, the conductor-density part of the high
Gaussian zero bound is its normalized absolute mass times the paired log sum. -/
public theorem high_gaussian_pair_conductor (K : HighGaussianKernel) {n p q r : ℕ} [NeZero p]
    [NeZero q] [NeZero r] (hn : n = p * q * r) :
    (Real.log (p * q : ℕ) + Real.log (p * r : ℕ) + Real.log (q * r : ℕ)) / (2 * Real.pi) *
        (∫ t : ℝ,
          ‖∑ j ∈ Finset.range (2 * K.degree + 1),
              (K.expandedCoeff j : ℂ) * Complex.exp (5 * (Complex.I * (t : ℂ))) /
                (Complex.I * (t : ℂ) + (K.pole : ℂ)) ^ (K.logPower j + 1)‖) =
      3 * Real.log n / 8 := by
  rw [pair_level_log_sum hn, high_gaussian_mass_exact]
  have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
  calc
    _ = (3 * Real.log n / 8) * (Real.pi / Real.pi) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [div_self hπ, mul_one]

end PseudoPrime.PrimeTestBounds.MillerRabin
