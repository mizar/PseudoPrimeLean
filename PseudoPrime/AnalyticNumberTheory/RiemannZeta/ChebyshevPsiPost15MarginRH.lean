/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiPost15Numerics
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiMidrangeTo15RH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevIntegratedMargin20RH

/-! # The 9/100 margin just above log height 15 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- In the stated range, both smoothing midpoint logarithms lie in the first
twelve certified phase blocks. -/
theorem midrange_post15_midpoints {x δ : ℝ} (hx : 0 < x) (hd : 0 ≤ δ) (hu : δ ≤ 1 / 200)
    (hl : (13815 / 1000 : ℝ) ≤ Real.log x) (hh : Real.log x ≤ (151 / 10 : ℝ)) :
    Real.log ((x - x * δ + x) / 2) ∈ Set.Icc (1381 / 100 : ℝ) (7553 / 500 : ℝ) ∧
      Real.log ((x + (x + x * δ)) / 2) ∈ Set.Icc (1381 / 100 : ℝ) (7553 / 500 : ℝ) := by
  have hlog := midpoint_log_bounds hd hu
  have hm : 0 < 1 - δ / 2 := by linarith only [hu]
  have hp : 0 < 1 + δ / 2 := by linarith only [hd]
  have hm0 : Real.log (1 - δ / 2) ≤ 0 := Real.log_nonpos hm.le (by linarith only [hd])
  have hp0 : 0 ≤ Real.log (1 + δ / 2) := Real.log_nonneg (by linarith only [hd])
  have he1 : (x - x * δ + x) / 2 = x * (1 - δ / 2) := by ring
  have he2 : (x + (x + x * δ)) / 2 = x * (1 + δ / 2) := by ring
  rw [he1, he2, Real.log_mul hx.ne' hm.ne', Real.log_mul hx.ne' hp.ne']
  constructor <;> constructor <;> linarith only [hl, hh, hlog.1, hlog.2, hm0, hp0]

/-- Under RH and the stated height-100 zero hypotheses, the normalized ψ
error is at most the Lee–Nosal envelope minus 9/100 between log heights 15
and 15.1. The twelve certified phase blocks control the zero head. -/
theorem psi_midrange_margin_post15 (hRH : RiemannHypothesis) (g : Fin 29 → ℝ) (hmono : StrictMono g)
    (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hl : LowZero100LowerBounds g) (hu : LowZero100UpperBounds g)
    {x : ℝ} (ha : 1000000 ≤ x) (hlo : (15 : ℝ) ≤ Real.log x) (hhi : Real.log x ≤ (151 / 10 : ℝ)) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ leeNosalPsiLog (Real.log x) - 9 / 100 := by
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
  have hd : (1 / 1000 : ℝ) ≤ δ := midrange_post15_delta_lower ha hhi
  have hlo' : (1423 / 100 : ℝ) ≤ Real.log x := by linarith only [hlo]
  have hdu : δ ≤ 1 / 250 := midrange_post15_delta_upper hlo' hhi hx
  have hB : B ≤ 5 := midrange_post15_tail_coefficient hlo' hhi
  have hc := midrange_log_two_pi_le
  have hrem := midrange_later_remainder hd hdu hB hc hs1000 ha
  have hmonoGap :=
    midrange_main_gap_mono.monotoneOn (Set.mem_Ici.mpr (by norm_num only : (13815 / 1000 : ℝ) ≤ 15))
      (Set.mem_Ici.mpr
        (show (13815 / 1000 : ℝ) ≤ L by
          dsimp only [L]; linarith only [hlo]))
      hlo
  have hmain : (7 / 50 : ℝ) < leeNosalPsiLog L - midrangePhaseMain L :=
    midrange_main_gap_at_15.trans_le hmonoGap
  have hlog : Real.log ((2 / δ) / (2 * Real.pi)) = L / 2 - Real.log (5 * L / 6) :=
    midrange_cutoff_log hx hL0
  have hsq : s * δ = 5 * L / (6 * Real.pi) := by
    dsimp only [δ]
    simp only [div_eq_mul_inv]
    linear_combination (5 * L / (6 * Real.pi)) * (mul_inv_cancel₀ hs.ne')
  have he := midrange_later_decomposition L δ s (Real.log (2 * Real.pi)) x hsq hlog
  have hδ0 : 0 < δ := by linarith only [hd]
  have hm := midrange_post15_midpoints hx hδ0.le (by linarith only [hdu]) (log_million_lower ha) hhi
  have hmul := mul_le_mul_of_nonneg_left hdu hx.le
  have hleft : 1 < x - x * δ := by nlinarith only [hmul, ha]
  have hcut : 100 ≤ 2 / δ := by
    apply (le_div_iff₀ hδ0).2
    linarith only [hdu]
  have hp :=
    psi_error_first_twelve_blocks_scale hRH g hmono hpos hheight hzero hcount hl hu hx hδ0
      (by linarith only [hdu]) hleft hcut hm.1 hm.2
  have hcurv := midrange_curvature_le hδ0.le hdu
  have hcutpos : 0 ≤ (1 + δ) * ((3 / 8 : ℝ) / (2 / δ)) := by
    apply mul_nonneg (by linarith only [hd])
    exact div_nonneg (by norm_num only) (div_nonneg (by norm_num only) hδ0.le)
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
      s * δ / 2 + Real.log (2 * Real.pi) / s + ((1 + δ / 4) * (51 / 100) + 613 / 250000) +
        (1 + δ) *
          (((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 + 2 * Real.log ((2 / δ) / (2 * Real.pi)) + 2) /
                (2 * Real.pi) -
              143 / 125 +
            1 / (15 * (2 / δ) ^ 2)) +
        1 / (x * δ * s) := by
    nlinarith only [hp, hcurv, hcutpos]
  rw [he] at hp'
  change |Chebyshev.psi x - x| / s ≤ leeNosalPsiLog L - 9 / 100
  dsimp only [B] at hrem
  linarith only [hp', hrem, hmain]

/-- Under RH and the stated height-100 zero hypotheses, the normalized ψ
error has margin 9/100 for positive `x` with `15 ≤ log x ≤ 15.1`. The lower
bound `x ≥ 10^6` follows from the logarithmic hypothesis. -/
theorem psi_post15_margin_of_brackets (hRH : RiemannHypothesis) (g : Fin 29 → ℝ)
    (hmono : StrictMono g) (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hl : LowZero100LowerBounds g) (hu : LowZero100UpperBounds g)
    {x : ℝ} (hx : 0 < x) (hlo : (15 : ℝ) ≤ Real.log x) (hhi : Real.log x ≤ (151 / 10 : ℝ)) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ leeNosalPsiLog (Real.log x) - 9 / 100 := by
  exact
    psi_midrange_margin_post15 hRH g hmono hpos hheight hzero hcount hl hu
      (million_le_of_log_fifteen hx hlo) hlo hhi

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
