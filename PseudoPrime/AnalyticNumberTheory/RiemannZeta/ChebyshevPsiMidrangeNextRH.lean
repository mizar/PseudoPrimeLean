/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiMidrangeNextNumerics

/-! # Lee–Nosal margin on the next midrange interval -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The next-block envelope splits into the sharper main term, the difference
between the phase constants, and the nonnegative smoothing remainder. -/
theorem midrange_next_decomposition (L δ s c x : ℝ) (hsq : s * δ = 5 * L / (6 * Real.pi))
    (hlog : Real.log ((2 / δ) / (2 * Real.pi)) = L / 2 - Real.log (5 * L / 6)) :
    let B :=
      ((L / 2 - Real.log (5 * L / 6)) ^ 2 + 2 * (L / 2 - Real.log (5 * L / 6)) + 2) /
          (2 * Real.pi) -
        143 / 125
    s * δ / 2 + c / s + ((1 + δ / 4) * (51 / 100) + 527 / 250000) +
        (1 + δ) *
          (((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 + 2 * Real.log ((2 / δ) / (2 * Real.pi)) + 2) /
                (2 * Real.pi) -
              143 / 125 +
            1 / (15 * (2 / δ) ^ 2)) +
        1 / (x * δ * s) =
      midrangePhaseMain L + 1 / 500 +
        (c / s + δ * (51 / 100) / 4 + 527 / 250000 + δ * B + (1 + δ) * δ ^ 2 / 60 +
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
error is at most the Lee–Nosal envelope minus 1/40 between log heights
13.86 and 14.23. The five phase blocks and rational remainder bounds suffice. -/
theorem psi_midrange_margin_next (hRH : RiemannHypothesis) (g : Fin 29 → ℝ) (hmono : StrictMono g)
    (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hl : LowZero100LowerBounds g) (hu : LowZero100UpperBounds g)
    {x : ℝ} (ha : 1000000 ≤ x) (hlo : (1386 / 100 : ℝ) ≤ Real.log x)
    (hhi : Real.log x ≤ (1423 / 100 : ℝ)) :
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
  have hL0 : 0 < L := by linarith only [hlo]
  have hd : (1 / 500 : ℝ) ≤ δ := midrange_next_delta_lower ha hhi
  have hdu : δ ≤ 37 / 10000 := midrange_next_delta_upper hlo hhi hx
  have hB : B ≤ 83 / 20 := midrange_next_tail_coefficient hlo hhi
  have hc := midrange_log_two_pi_le
  have hrem := midrange_next_remainder hd hdu hB hc hs1000 ha
  have hmonoGap :=
    midrange_main_gap_mono.monotoneOn
      (Set.mem_Ici.mpr (by norm_num only : (13815 / 1000 : ℝ) ≤ 1386 / 100))
      (Set.mem_Ici.mpr
        (show (13815 / 1000 : ℝ) ≤ L by
          dsimp only [L]; linarith only [hlo]))
      hlo
  have hmain : (117 / 2500 : ℝ) < leeNosalPsiLog L - midrangePhaseMain L :=
    midrange_main_gap_at_1386.trans_le hmonoGap
  have hlog : Real.log ((2 / δ) / (2 * Real.pi)) = L / 2 - Real.log (5 * L / 6) :=
    midrange_cutoff_log hx hL0
  have hsq : s * δ = 5 * L / (6 * Real.pi) := by
    dsimp only [δ]
    simp only [div_eq_mul_inv]
    linear_combination (5 * L / (6 * Real.pi)) * (mul_inv_cancel₀ hs.ne')
  have he := midrange_next_decomposition L δ s (Real.log (2 * Real.pi)) x hsq hlog
  have hp := psi_midrange_canonical hRH g hmono hpos hheight hzero hcount hl hu ha hhi
  have hcurv := midrange_curvature_sharp (show 0 ≤ δ by linarith only [hd]) hdu
  have hcut : 0 ≤ (1 + δ) * ((3 / 8 : ℝ) / (2 / δ)) := by
    apply mul_nonneg (by linarith only [hd])
    exact div_nonneg (by norm_num only) (div_nonneg (by norm_num only) (by linarith only [hd]))
  change
    |Chebyshev.psi x - x| / s ≤
      s * δ / 2 + Real.log (2 * Real.pi) / s +
        ((1 + δ / 4) * (51 / 100) + 3640 * δ ^ 2 * (1 - δ) ^ (-(3 / 2 : ℝ)) / 24) +
        (1 + δ) *
          (((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 + 2 * Real.log ((2 / δ) / (2 * Real.pi)) + 2) /
                (2 * Real.pi) -
              143 / 125 -
              (3 / 8 : ℝ) / (2 / δ) +
            1 / (15 * (2 / δ) ^ 2)) +
        1 / (x * δ * s) at hp
  have hp' :
    |Chebyshev.psi x - x| / s ≤
      s * δ / 2 + Real.log (2 * Real.pi) / s + ((1 + δ / 4) * (51 / 100) + 527 / 250000) +
        (1 + δ) *
          (((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 + 2 * Real.log ((2 / δ) / (2 * Real.pi)) + 2) /
                (2 * Real.pi) -
              143 / 125 +
            1 / (15 * (2 / δ) ^ 2)) +
        1 / (x * δ * s) := by
    nlinarith only [hp, hcurv, hcut]
  rw [he] at hp'
  change |Chebyshev.psi x - x| / s ≤ leeNosalPsiLog L - 1 / 40
  dsimp only [B] at hrem
  linarith only [hp', hrem, hmain]

/-- Under RH and the stated height-100 zero hypotheses, the Lee–Nosal margin
1/40 holds from one million through log height 14.23. The first two blocks use
the sharper phase bound and the remaining three blocks use 51/100. -/
theorem psi_midrange_margin_five (hRH : RiemannHypothesis) (g : Fin 29 → ℝ) (hmono : StrictMono g)
    (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hl : LowZero100LowerBounds g) (hu : LowZero100UpperBounds g)
    {x : ℝ} (ha : 1000000 ≤ x) (hhi : Real.log x ≤ (1423 / 100 : ℝ)) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ leeNosalPsiLog (Real.log x) - 1 / 40 := by
  by_cases h : Real.log x ≤ 1386 / 100
  · exact psi_midrange_margin_start hRH g hmono hpos hheight hzero hcount hl hu ha h
  · exact
      psi_midrange_margin_next hRH g hmono hpos hheight hzero hcount hl hu ha (le_of_not_ge h) hhi

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
