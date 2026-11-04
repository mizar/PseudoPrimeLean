/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.VariableRepeatedBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.MeanCofactorWitness

/-! # Fixed-coefficient witnesses for repeated prime factors -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, an odd `n > 1` with `log n ≥ 80000` and a prime-power divisor whose
logarithm lies between one third of `log n` and `log n` has a rejecting prime within
`(427 / 1000) * log n ^ 2`. Apply the variable-radius divisor theorem at
`α = 13069 / 20000` and round `α ^ 2). This handles the large repeated divisor branch. -/
theorem primePow_divisor_witness_427 {n p a : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 2 ≤ a) (hdiv : p ^ a ∣ n) (hRH : RiemannHypothesis)
    (hL : (80000 : ℝ) ≤ Real.log n) (hlower : Real.log n / 3 ≤ Real.log (p ^ a : ℕ))
    (hupper : Real.log (p ^ a : ℕ) ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (427 / 1000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨r, hr, hrbound, hrnot⟩ :=
    variable_primePow_divisor hn ho hp hp2 ha hdiv hRH (α := 13069 / 20000) (by norm_num only)
      (by norm_num only) (by linarith only [hL]) hlower hupper
  have hc : (13069 / 20000 : ℝ) ^ 2 ≤ 427 / 1000 := by norm_num only
  exact ⟨r, hr, hrbound.trans (mul_le_mul_of_nonneg_right hc (sq_nonneg _)), hrnot⟩

/-- Under RH, an odd input `n = p ^ 2 * q` with prime factors and
`80000 ≤ log n ≤ 4 * 10 ^ 10` has a rejecting prime within
`(427 / 1000) * log n ^ 2`. Split on the logarithmic size of `q): use the
large-cofactor theorem or the prime-power divisor theorem. This covers the repeated
three-factor branch. -/
theorem squareTimesPrime_witness_427 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hprod : n = p ^ 2 * q) (hRH : RiemannHypothesis) (hL : (80000 : ℝ) ≤ Real.log n)
    (hLU : Real.log n ≤ 40000000000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (427 / 1000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpsq : 1 < p ^ 2 := by nlinarith only [hp.one_lt]
  have hpdiv : p ∣ n := hprod ▸ dvd_mul_of_dvd_left (dvd_pow_self p (by norm_num only)) q
  have hqdiv : q ∣ n := hprod ▸ dvd_mul_left q (p ^ 2)
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpdiv
  have hq2 : q ≠ 2 := ho.ne_two_of_dvd_nat hqdiv
  have hdiv : p ^ 2 ∣ n := hprod ▸ dvd_mul_right (p ^ 2) q
  have hlog : Real.log n = Real.log (p ^ 2 : ℕ) + Real.log q := by
    rw [hprod, Nat.cast_mul,
      Real.log_mul (Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt (zero_lt_one.trans hpsq)))
        (Nat.cast_ne_zero.mpr hq.ne_zero)]
  have hupper : Real.log (p ^ 2 : ℕ) ≤ Real.log n := by
    have hqlog := Real.log_natCast_nonneg q
    linarith only [hlog, hqlog]
  by_cases hqLarge : (13069 / 20000 : ℝ) * Real.log n < Real.log q
  · exact large_cofactor_witness_427 hRH hn ho hpsq hq hq2 hprod hL hLU hqLarge
  · have hlower : Real.log n / 3 ≤ Real.log (p ^ 2 : ℕ) := by
      have hqsmall := le_of_not_gt hqLarge
      linarith only [hlog, hqsmall, hL]
    exact
      primePow_divisor_witness_427 hn ho hp hp2 (by norm_num only : 2 ≤ 2) hdiv hRH hL hlower hupper

end PseudoPrime.PrimeTestBounds.MillerRabin
