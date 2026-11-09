/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighVariableScalars
public import PseudoPrime.PrimeTestBounds.MillerRabin.HighVariableCofactor

/-! # Coefficient for the variable-radius paired-prime bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, the variable paired coefficient gives an MR witness in the large-prime-cofactor
branch for `log n ≥ 70000`. The radius and its logarithmic budget are derived from the selected
coefficient, and the paired count is transferred to the local Fermat kernel. -/
theorem large_cofactor_witness_paired {n m q : ℕ} (hn : 1 < n) (ho : Odd n) (hm : 1 < m)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = m * q) (hRH : RiemannHypothesis)
    (hL : (70000 : ℝ) ≤ Real.log n)
    (hqLarge : pairedAlpha (2 * Real.log (Real.log n)) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (pairedAlpha (2 * Real.log (Real.log n))) ^ 2 * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let L := Real.log n
  let U := 2 * Real.log L
  let α := pairedAlpha U
  let b := ⌊α * L⌋₊
  have hU : 22 ≤ U := high_log_twice_ge_22 hL
  have hα := pairedAlpha_bounds hU
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hα0 : 0 ≤ α := by linarith only [hα.1]
  have hb : 5000 ≤ b := high_floor_radius_ge_5000 hL hα.1
  have hb1 : 1 ≤ (b : ℝ) := by
    have hbr : (5000 : ℝ) ≤ b := Nat.cast_le.mpr hb
    linarith only [hbr]
  have hbf := Nat.floor_le (mul_nonneg hα0 hL0)
  have hbL : (b : ℝ) ≤ L := by
    have hh := mul_le_mul_of_nonneg_right hα.2 hL0
    linarith only [hbf, hh]
  have hmargin := high_variable_log_margin hL hb1 hbL
  have hv0 : 0 ≤ 2 * Real.log (b : ℝ) := mul_nonneg (by norm_num only) (Real.log_nonneg hb1)
  have hweak : (2 * Real.log (b : ℝ)) ^ 2 + (29 / 25) * (2 * Real.log (b : ℝ)) ≤ L / 100 := by
    linarith only [hmargin, hv0]
  have hlinear := highCoeff_semiprime_log_linear hL hv0 hweak
  have hlog := Real.log_le_log (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) hb1) hbL
  have huU : 2 * Real.log (b : ℝ) ≤ U := by linarith only [hlog]
  have hgap : (3 / 2 * α - 1) * U + (339 / 500) * α ≥ 1 / 100 := (pairedAlpha_gap hU).ge
  exact
    large_cofactor_witness_selected hn ho hm hq hq2 hprod hRH hL hα.1 hα.2 hlinear huU hgap hmargin
      hqLarge

/-- Under GRH, an odd product of distinct primes `p < q` with `log n ≥ 70000` has a rejecting
prime within the variable paired-coefficient bound. The local non-Korselt estimate handles a
small `log q`; the prime-product count handles the complementary large-cofactor branch. -/
theorem distinct_semiprime_witness_paired {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (70000 : ℝ) ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (pairedAlpha (2 * Real.log (Real.log n))) ^ 2 * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hdiv : q ∣ n := by
    rw [hprod]
    exact dvd_mul_left q p
  have hq2 : q ≠ 2 := ho.ne_two_of_dvd_nat hdiv
  by_cases hsmall : Real.log q ≤ pairedAlpha (2 * Real.log (Real.log n)) * Real.log n
  · have hbad : ¬q - 1 ∣ n - 1 := by
      rw [hprod]
      exact NumberTheory.not_sub_one_dvd_prime_mul_sub_one_of_lt hp hq hpq
    obtain ⟨r, hr, hb, hf⟩ :=
      exists_prime_witness_le_nonKorselt_factor_log_sq hn ho hq hdiv hbad hGRH
    have hsq := pow_le_pow_left₀ (Real.log_natCast_nonneg q) hsmall 2
    have hbound :
      (Real.log q) ^ 2 ≤ (pairedAlpha (2 * Real.log (Real.log n))) ^ 2 * (Real.log n) ^ 2 := by
      nlinarith only [hsq]
    exact ⟨r, hr, hb.trans hbound, hf⟩
  · exact
      large_cofactor_witness_paired hn ho hp.one_lt hq hq2 hprod hGRH.riemann hL
        (lt_of_not_ge hsmall)

end PseudoPrime.PrimeTestBounds.MillerRabin
