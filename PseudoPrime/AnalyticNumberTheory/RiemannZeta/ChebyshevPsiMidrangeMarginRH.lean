/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiMidrangeSigned
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiMidrangeTailNumerics

/-! # A Lee–Nosal margin on the initial midrange -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Canonical smoothing writes the cutoff logarithm in terms of `log x`. -/
theorem midrange_cutoff_log {x : ℝ} (hx : 0 < x) (hL : 0 < Real.log x) :
    let δ := (5 * Real.log x / (6 * Real.pi)) / Real.sqrt x
    Real.log ((2 / δ) / (2 * Real.pi)) = Real.log x / 2 - Real.log (5 * Real.log x / 6) := by
  dsimp only
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have hq : (5 * Real.log x / 6 : ℝ) ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num only) hL.ne') (by norm_num only)
  have hp := mul_inv_cancel₀ Real.pi_ne_zero
  have he :
    (2 / ((5 * Real.log x / (6 * Real.pi)) / Real.sqrt x)) / (2 * Real.pi) =
      Real.sqrt x / (5 * Real.log x / 6) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    linear_combination (Real.sqrt x * (6 / 5) * (Real.log x)⁻¹) * hp
  rw [he, Real.log_div hs hq, Real.log_sqrt hx.le]

/-- The signed initial envelope splits into its main term and the remainder
controlled by `midrange_remainder_arithmetic`. -/
theorem midrange_signed_decomposition (L δ s c x : ℝ) (hsq : s * δ = 5 * L / (6 * Real.pi))
    (hlog : Real.log ((2 / δ) / (2 * Real.pi)) = L / 2 - Real.log (5 * L / 6)) :
    let B :=
      ((L / 2 - Real.log (5 * L / 6)) ^ 2 + 2 * (L / 2 - Real.log (5 * L / 6)) + 2) /
          (2 * Real.pi) -
        143 / 125
    s * δ / 2 + c / s + ((1 + δ / 4) * (127 / 250) + 527 / 250000) +
            (1 + δ) *
              (((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 + 2 * Real.log ((2 / δ) / (2 * Real.pi)) +
                      2) /
                    (2 * Real.pi) -
                  143 / 125 +
                1 / (15 * (2 / δ) ^ 2)) -
          21 / 32000 +
        1 / (x * δ * s) =
      midrangePhaseMain L +
        (c / s + δ * (127 / 250) / 4 + 527 / 250000 + δ * B - 21 / 32000 + (1 + δ) * δ ^ 2 / 60 +
          1 / (x * δ * s)) := by
  dsimp only [midrangePhaseMain]
  rw [hlog]
  have he : 1 / (15 * (2 / δ) ^ 2) = δ ^ 2 / 60 := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring_nf
    simp only [inv_inv]
  rw [he]
  rw [hsq]
  ring

/-- Under RH and the stated height-100 zero hypotheses, the normalized ψ
error is below the Lee–Nosal envelope by 1/40 for `10^6 ≤ x` and
`log x ≤ 13.86`. The proof retains the cutoff gain and bounds all remainders. -/
theorem psi_midrange_margin_start (hRH : RiemannHypothesis) (g : Fin 29 → ℝ) (hmono : StrictMono g)
    (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hl : LowZero100LowerBounds g) (hu : LowZero100UpperBounds g)
    {x : ℝ} (ha : 1000000 ≤ x) (hL : Real.log x ≤ (1386 / 100 : ℝ)) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ leeNosalPsiLog (Real.log x) - 1 / 40 := by
  let L := Real.log x
  let s := Real.sqrt x
  let δ := (5 * L / (6 * Real.pi)) / s
  let B :=
    ((L / 2 - Real.log (5 * L / 6)) ^ 2 + 2 * (L / 2 - Real.log (5 * L / 6)) + 2) / (2 * Real.pi) -
      143 / 125
  have hx : 0 < x := by linarith only [ha]
  have hs : 0 < s := Real.sqrt_pos.2 hx
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx.le
  have hs1000 : 1000 ≤ s := by nlinarith only [hs, hs2, ha]
  have hll : (13815 / 1000 : ℝ) ≤ L := log_million_lower ha
  have hL0 : 0 < L := by linarith only [hll]
  have hd : (7 / 2000 : ℝ) ≤ δ := midrange_delta_lower ha hL
  have hdu : δ ≤ 37 / 10000 := midrange_delta_sharp ha hL
  have hB : B ≤ 191 / 50 := midrange_tail_coefficient hll hL
  have hc := midrange_log_two_pi_le
  have hrem := midrange_remainder_arithmetic hd hdu hB hc hs1000 ha
  have hmain := midrange_main_gap hll
  have hlog : Real.log ((2 / δ) / (2 * Real.pi)) = L / 2 - Real.log (5 * L / 6) :=
    midrange_cutoff_log hx hL0
  have hsq : s * δ = 5 * L / (6 * Real.pi) := by
    dsimp only [δ]
    simp only [div_eq_mul_inv]
    linear_combination (5 * L / (6 * Real.pi)) * (mul_inv_cancel₀ hs.ne')
  have he := midrange_signed_decomposition L δ s (Real.log (2 * Real.pi)) x hsq hlog
  have hp := psi_midrange_signed hRH g hmono hpos hheight hzero hcount hl hu ha hL
  change
    |Chebyshev.psi x - x| / s ≤
      s * δ / 2 + Real.log (2 * Real.pi) / s + ((1 + δ / 4) * (127 / 250) + 527 / 250000) +
            (1 + δ) *
              (((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 + 2 * Real.log ((2 / δ) / (2 * Real.pi)) +
                      2) /
                    (2 * Real.pi) -
                  143 / 125 +
                1 / (15 * (2 / δ) ^ 2)) -
          21 / 32000 +
        1 / (x * δ * s) at hp
  rw [he] at hp
  change |Chebyshev.psi x - x| / s ≤ leeNosalPsiLog L - 1 / 40
  dsimp only [B] at hrem
  linarith only [hp, hrem, hmain]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
