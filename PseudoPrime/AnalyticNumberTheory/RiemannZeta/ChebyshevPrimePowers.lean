/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevGap43

/-! # Separating the prime-square contribution -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Above logarithmic scale 43, `exp (L/6)` is at least `20L`. Split the
exponential at seven and use the lower bound `exp 1 > 8/3`. -/
theorem exp_sixth_lower {L : ℝ} (hL : 43 ≤ L) : 20 * L ≤ Real.exp (L / 6) := by
  have he : (8 / 3 : ℝ) ≤ Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    norm_num only at h ⊢
    linarith only [h]
  have he7 : (840 : ℝ) ≤ Real.exp 7 := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 8 / 3 by norm_num only) he 7
    rw [← Real.exp_nat_mul] at h
    norm_num only at h ⊢
    linarith only [h]
  have ht := Real.add_one_le_exp (L / 6 - 7)
  have hm := mul_le_mul he7 ht (by linarith only [hL]) (Real.exp_pos 7).le
  have heq : Real.exp (L / 6) = Real.exp 7 * Real.exp (L / 6 - 7) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq]
  nlinarith only [hm, hL]

/-- For `x ≥ 4`, the difference between Chebyshev's `ψ` and `θ` is at most
`log 4 * sqrt x + 2 log x * x^(1/3)`. Separate the prime-square term from
the higher powers in the finite theta decomposition, then count the latter. -/
theorem psi_sub_theta_prime_powers {x : ℝ} (hx : 4 ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x ≤
      Real.log 4 * Real.sqrt x + 2 * Real.log x * x ^ (1 / 3 : ℝ) := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hx2 : 2 ≤ x := by linarith only [hx]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have hfloor : 2 ≤ ⌊Real.log x / Real.log 2⌋₊ := by
    apply Nat.le_floor
    norm_num only [Nat.cast_ofNat]
    apply (le_div_iff₀ hl2).2
    rw [← hlog4]
    exact Real.log_le_log (by norm_num only) hx
  have hs := Chebyshev.psi_eq_theta_add_sum_theta hx2
  rw [← Finset.add_sum_Ioc_eq_sum_Icc hfloor] at hs
  have htwo : Chebyshev.theta (x ^ ((1 : ℝ) / (2 : ℕ))) ≤ Real.log 4 * Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    exact Chebyshev.theta_le_log4_mul_x (Real.rpow_nonneg hx0 _)
  have hsum :
    (∑ n ∈ Finset.Ioc 2 ⌊Real.log x / Real.log 2⌋₊, Chebyshev.theta (x ^ ((1 : ℝ) / n))) ≤
      (⌊Real.log x / Real.log 2⌋₊ : ℝ) * (Real.log 4 * x ^ (1 / 3 : ℝ)) := by
    calc
      _ ≤ (Finset.Ioc 2 ⌊Real.log x / Real.log 2⌋₊).card • (Real.log 4 * x ^ (1 / 3 : ℝ)) := by
        apply Finset.sum_le_card_nsmul
        intro n hn
        have hn3 : (3 : ℝ) ≤ n := by
          have hn' := (Finset.mem_Ioc.mp hn).1
          exact_mod_cast hn'
        have hn0 : 0 < (n : ℝ) := by linarith only [hn3]
        have hexp : (1 : ℝ) / n ≤ 1 / 3 := by
          apply (div_le_div_iff₀ hn0 (by norm_num only : (0 : ℝ) < 3)).2
          linarith only [hn3]
        have hpow := Real.rpow_le_rpow_of_exponent_le hx1 hexp
        have htheta := Chebyshev.theta_le_log4_mul_x (Real.rpow_nonneg hx0 ((1 : ℝ) / n))
        exact htheta.trans (mul_le_mul_of_nonneg_left hpow (Real.log_nonneg (by norm_num only)))
      _ ≤ (⌊Real.log x / Real.log 2⌋₊ : ℝ) * (Real.log 4 * x ^ (1 / 3 : ℝ)) := by
        simp only [Nat.card_Ioc, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast Nat.sub_le _ _
        · exact mul_nonneg (Real.log_nonneg (by norm_num only)) (Real.rpow_nonneg hx0 _)
  have hfloorle : (⌊Real.log x / Real.log 2⌋₊ : ℝ) ≤ Real.log x / Real.log 2 :=
    Nat.floor_le (div_nonneg hlx hl2.le)
  have hm :=
    mul_le_mul_of_nonneg_right hfloorle
      (mul_nonneg (Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 4))
        (Real.rpow_nonneg hx0 (1 / 3 : ℝ)))
  have heq :
    (Real.log x / Real.log 2) * (Real.log 4 * x ^ (1 / 3 : ℝ)) =
      2 * Real.log x * x ^ (1 / 3 : ℝ) := by
    rw [hlog4]
    have h2ne : Real.log 2 ≠ 0 := hl2.ne'
    field_simp
  rw [heq] at hm
  linarith only [hs, htwo, hsum, hm]

/-- For positive `x` with `log x ≥ 43`, the nonnegative prime-power excess
`ψ(x) - θ(x)` is at most `3/2 * sqrt x`. Bound the square contribution by
`log 4 * sqrt x` and absorb the remaining powers using exponential growth. -/
theorem psi_sub_theta_43 {x : ℝ} (hx : 0 < x) (hL : 43 ≤ Real.log x) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (3 / 2 : ℝ) * Real.sqrt x := by
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have hlog4lt : Real.log 4 < (7 / 5 : ℝ) := by
    rw [hlog4]
    linarith only [Real.log_two_lt_d9]
  have hx4 : 4 ≤ x := by
    by_contra hn
    have hh := Real.log_le_log hx (le_of_not_ge hn)
    linarith only [hh, hlog4lt, hL]
  have hxpow : x ^ (1 / 3 : ℝ) = Real.exp (Real.log x / 3) := by
    rw [Real.rpow_def_of_pos hx]
    congr 1
    ring
  have hxsqrt : Real.sqrt x = Real.exp (Real.log x / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
    congr 1
    ring
  have hexp :
    Real.exp (Real.log x / 2) = Real.exp (Real.log x / 3) * Real.exp (Real.log x / 6) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he := exp_sixth_lower hL
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (Real.log x / 3)).le
  have htail : 2 * Real.log x * x ^ (1 / 3 : ℝ) ≤ (1 / 10 : ℝ) * Real.sqrt x := by
    rw [hxpow, hxsqrt, hexp]
    nlinarith only [hm]
  have hfirst := mul_le_mul_of_nonneg_right hlog4lt.le (Real.sqrt_nonneg x)
  have hprime := psi_sub_theta_prime_powers hx4
  linarith only [hprime, hfirst, htail]

/-- Under RH and the stated Rosser-type positive zero-count bound, the
Chebyshev `θ` error for positive `x` with `log x ≥ 43` is bounded by the
target envelope minus `5/4 * sqrt x`. Combine the `ψ` bound with the
prime-power excess; the zero-count estimate remains a hypothesis. -/
theorem theta_error_envelope_of_log (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x)
    (hL : 43 ≤ Real.log x)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t)) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x *
        (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) - 5 / 4) := by
  have hp := abs_le.mp (psi_error_envelope_of_log hRH hx hL hQ)
  have hd := psi_sub_theta_43 hx hL
  have hd0 := sub_nonneg.mpr (Chebyshev.theta_le_psi x)
  have hs := Real.sqrt_nonneg x
  apply abs_le.mpr
  constructor
  · nlinarith only [hp.1, hd]
  · nlinarith only [hp.2, hd0, hs]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
