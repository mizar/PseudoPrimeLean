/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.DualMeanCofactor
public import PseudoPrime.PrimeTestBounds.MillerRabin.VariableRepeatedBounds
/-! # Repeated-factor witnesses for the two-cell mean bridge -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin
/-- Under RH, the variable-radius divisor theorem bounds a rejecting prime for an
odd modulus with a sufficiently large prime-power divisor. -/
theorem dualMean_primePow {n p a : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 2 ≤ a) (hdiv : p ^ a ∣ n) (hRH : RiemannHypothesis)
    (hL : (81000 : ℝ) ≤ Real.log n) (hlower : Real.log n / 3 ≤ Real.log (p ^ a : ℕ))
    (hupper : Real.log (p ^ a : ℕ) ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4187 / 10000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨r, hr, hrbound, hrnot⟩ :=
    variable_primePow_divisor hn ho hp hp2 ha hdiv hRH (α := 647 / 1000) (by norm_num only)
      (by norm_num only) (by linarith only [hL]) hlower hupper
  have hc : (647 / 1000 : ℝ) ^ 2 ≤ 4187 / 10000 := by norm_num only
  exact ⟨r, hr, hrbound.trans (mul_le_mul_of_nonneg_right hc (sq_nonneg _)), hrnot⟩

/-- Under RH, an odd product of a prime square and a prime has a witness below
the new coefficient. Split on the logarithmic size of the prime cofactor. -/
theorem dualMean_squarePrime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hprod : n = p ^ 2 * q) (hRH : RiemannHypothesis) (hL : (81000 : ℝ) ≤ Real.log n)
    (hLU : Real.log n ≤ 5000000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4187 / 10000 : ℝ) * (Real.log n) ^ 2 ∧
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
  by_cases hqLarge : (647 / 1000 : ℝ) * Real.log n < Real.log q
  · exact dualMean_cofactor hRH hn ho hpsq hq hq2 hprod hL hLU hqLarge
  · have hlower : Real.log n / 3 ≤ Real.log (p ^ 2 : ℕ) := by
      have hqsmall := le_of_not_gt hqLarge
      linarith only [hlog, hqsmall, hL]
    exact
      dualMean_primePow hn ho hp hp2 (by norm_num only : 2 ≤ 2) hdiv hRH hL hlower hupper




end PseudoPrime.PrimeTestBounds.MillerRabin
