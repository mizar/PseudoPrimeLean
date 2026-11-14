/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadPhase
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiMidpointBracketsRH

/-! # ψ error from bounds on a finite critical-line phase sum -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, ordered low-zero brackets and a count bound reduce the ψ error
estimate to upper bounds for the finite phase sum at both smoothing
midpoints. The distance-sum and higher-zero budgets are already included. -/
theorem psi_error_phase_brackets (hRH : RiemannHypothesis) (g : Fin 29 → ℝ) (hmono : StrictMono g)
    (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hl : LowZero100LowerBounds g) (hu : LowZero100UpperBounds g)
    {T x h D K : ℝ} (hT : 100 ≤ T) (hh : 0 < h) (hx : 1 < x - h) (hD : 0 ≤ D)
    (hsqrt : Real.sqrt (x + h) ≤ D) (htail : ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h ≤ D * T)
    (hlo : |zeroHeadPhase g (Real.log ((x - h + x) / 2))| ≤ K)
    (hhi : |zeroHeadPhase g (Real.log ((x + (x + h)) / 2))| ≤ K) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        (Real.sqrt (x + h) * K + 3640 * (x - h) ^ (-(3 / 2 : ℝ)) * h ^ 2 / 24) +
        D *
          (((Real.log (T / (2 * Real.pi))) ^ 2 + 2 * Real.log (T / (2 * Real.pi)) + 2) /
                (2 * Real.pi) -
              143 / 125 -
              (3 / 8 : ℝ) / T +
            1 / (15 * T ^ 2)) +
        1 / h := by
  have hc : zeroCount 100 ≤ 2 * (29 : ℕ) := by
    norm_num only [Nat.cast_ofNat]
    exact hcount
  have hk : 0 ≤ K := (abs_nonneg _).trans hlo
  have htlo : 0 < (x - h + x) / 2 := by linarith only [hx, hh]
  have hthi : 0 < (x + (x + h)) / 2 := by linarith only [hx, hh]
  have hslo : Real.sqrt ((x - h + x) / 2) ≤ Real.sqrt (x + h) :=
    Real.sqrt_le_sqrt (by linarith only [hh])
  have hshi : Real.sqrt ((x + (x + h)) / 2) ≤ Real.sqrt (x + h) :=
    Real.sqrt_le_sqrt (by linarith only [hh])
  have hzlo :=
    zero_head_phase_of_count hRH (show (0 : ℝ) ≤ 100 by norm_num only) htlo g hmono.injective hpos
      hheight hzero hc
  have hzhi :=
    zero_head_phase_of_count hRH (show (0 : ℝ) ≤ 100 by norm_num only) hthi g hmono.injective hpos
      hheight hzero hc
  apply
    psi_error_midpoint_brackets hRH g hmono hpos hheight hzero hcount hl hu hT hh hx hD hsqrt htail
  · rw [hzlo, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact
      (mul_le_mul_of_nonneg_left hlo (Real.sqrt_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hslo hk)
  · rw [hzhi, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact
      (mul_le_mul_of_nonneg_left hhi (Real.sqrt_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hshi hk)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
