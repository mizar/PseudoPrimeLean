/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaAnalytic100
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed260Combined1

/-! # First analytic Gamma cell and witness -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The first analytic scale has the displayed positive square-root lower bound. -/
theorem gamma_analytic100_root_lower : (402693 / 10000 : ℝ) ≤ Real.sqrt (60000 / 37 : ℝ) := by
  apply Real.le_sqrt_of_sq_le
  norm_num only

/-- Under RH, the signed-variation principal sum is at most 40.65 at the
first analytic scale. -/
theorem gamma_analytic100_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (60000 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (60000 / 37 : ℝ)) ≤
      813 / 20 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 402693 / 10000) (T := 201347 / 5000) (Z := 9239 / 1250)
      (by norm_num only) (by norm_num only) gamma_analytic100_root_lower gamma_analytic100_roots.1
      gamma_analytic100_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power at this scale. -/
theorem gamma_analytic100_power : (60000 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 313 / 20000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- The finite Euler prefix through 3000 exceeds 4.7. -/
theorem gamma_analytic100_euler :
    (47 / 10 : ℝ) ≤ ∑ n ∈ Finset.Ioc (0 : ℕ) 3000, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (47 / 10 : ℚ) ≤
      ((centerRowsBelow 3000).map
          (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 3000 ≤ 50000) (47 / 10) hc

/-- Under RH, the first analytic cell has a strict Gamma gap through 100.1. -/
theorem gamma_analytic100_gap (hRH : RiemannHypothesis) {L : ℝ} (hL : L ≤ 1001 / 10) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (60000 / 37)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (60000 / 37 : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 3000, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (60000 / 37 : ℝ) +
        (105 / 2 : ℝ) * (60000 / 37 : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((60000 / 37 : ℝ) * Real.sqrt (60000 / 37 : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 3000,
          Real.exp (-(k : ℝ) / (60000 / 37)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (60000 / 37 : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 3000) (60000 / 37 : ℝ) L (1001 / 10) (402693 / 10000)
      (313 / 20000) (32711 / 1000) (813 / 20) (47 / 10) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) hL gamma_analytic100_power (gamma_analytic100_main hRH)
      (gamma_analytic100_principal hRH) gamma_analytic100_euler (euler_mass_le_12372 hRH)
  norm_num only

/-- Under GRH, the first analytic cell extends the `3/10` rejecting-prime
bound for odd composites from logarithmic scale eight through 100.1. -/
theorem exists_reject_03_analytic100 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ (1001 / 10 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases hu : UniformKorseltTriple n
  · by_cases hprev : Real.log n ≤ (100 : ℝ)
    · apply exists_reject_03_fixed260_block1 hn ho hc hGRH hL
      simpa only [gammaFixed260Cell335Right, Rat.cast_ofNat] using hprev
    · have hlo : (100 : ℝ) ≤ Real.log n := le_of_not_ge hprev
      have hcut : (3000 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
        nlinarith only [hlo, sq_nonneg (Real.log n - 100)]
      obtain ⟨l, hl, hb, hf⟩ :=
        uniformKorselt_reject_gamma hn ho hu hGRH (X := (3000 : ℝ)) (x := (60000 / 37 : ℝ))
          (by norm_num only) (Finset.Ioc 0 3000)
          (by
            intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
          (by norm_num only) (gamma_analytic100_gap hGRH.riemann hU)
      exact ⟨l, hl, hb.trans hcut, hf⟩
  · exact exists_prime_reject_03_nonuniform_log8 hn ho hc hu hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
