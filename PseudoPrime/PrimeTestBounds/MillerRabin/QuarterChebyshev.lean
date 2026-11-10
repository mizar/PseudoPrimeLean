/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RealLog
public import PseudoPrime.Analysis.LogTaylorBounds
public import Mathlib.NumberTheory.Chebyshev

/-! # Chebyshev upper bound for the quarter-bound principal sums -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For `t ≥ 1`, the Chebyshev function satisfies `ψ(t) ≤ 3t` without RH.
Chebyshev's elementary upper estimate, certified bounds for `log 4` and
`log (5/2)`, and a tangent bound for `log t` give the coefficient three.
This supplies the upper principal-sum estimates in the high-index proof. -/
theorem quarter_psi_le_three {t : ℝ} (ht : 1 ≤ t) : Chebyshev.psi t ≤ 3 * t := by
  have h4 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 4 2 16 1 (7 / 5) = true from by decide +kernel)).2
  have h25 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck (5 / 2) 2 16 (9 / 10) 1 = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h4 h25
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have htangent :=
    Analysis.log_le_log_add_sub_div (a := (5 / 2 : ℝ)) (y := Real.sqrt t) (by norm_num only) hs
  have he := Real.log_sqrt ht0.le
  have hlog : Real.log t ≤ (4 / 5 : ℝ) * Real.sqrt t := by linarith only [htangent, h25, he]
  have hroot := Real.sq_sqrt ht0.le
  have hprod := mul_le_mul_of_nonneg_left hlog (le_of_lt hs)
  have hmain := mul_le_mul_of_nonneg_right h4 ht0.le
  have hpsi := Chebyshev.psi_le ht
  nlinarith only [hpsi, hmain, hprod, hroot]

/-- A real weight bounded above by `c ≥ 0` on natural indices through
`floor X`, with `X ≥ 1`, gives a weighted Mangoldt sum at most `3cX`.
Termwise comparison and the Chebyshev estimate supply a finite-sum upper
bound for truncations in the high-index principal-cost calculation. -/
theorem quarter_mangoldt_weight_le {X c : ℝ} (hX : 1 ≤ X) (hc : 0 ≤ c) (w : ℕ → ℝ)
    (hw : ∀ n ∈ Finset.Icc 0 ⌊X⌋₊, w n ≤ c) :
    (∑ n ∈ Finset.Icc 0 ⌊X⌋₊, w n * ArithmeticFunction.vonMangoldt n) ≤ c * (3 * X) := by
  calc
    _ ≤ c * ∑ n ∈ Finset.Icc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n := by
      rw [Finset.mul_sum]
      exact
        Finset.sum_le_sum
          (fun n hn ↦ mul_le_mul_of_nonneg_right (hw n hn) ArithmeticFunction.vonMangoldt_nonneg)
    _ = c * Chebyshev.psi X := by rw [Chebyshev.psi_eq_sum_Icc]
    _ ≤ c * (3 * X) := mul_le_mul_of_nonneg_left (quarter_psi_le_three hX) hc

end PseudoPrime.PrimeTestBounds.MillerRabin
