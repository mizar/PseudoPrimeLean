/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Arithmetic bounds for logarithmic Euler coefficients

Local roots bounded by their prime base give the coefficient bound
norm(a n)<=d*n*log n and a uniform L-series bound on Re s=3.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- The norm of the logarithm-weighted constant L-series term at 2 equals
log(n)/n^2, including the totalized zero term. Convert the natural logarithm
to its real cast and use the real exponent norm formula. This identifies
the scalar majorant used on the line Re s=3. -/
theorem norm_log_series_term (n : ℕ) :
    ‖LSeries.term (LSeries.logMul 1) (2 : ℂ) n‖ = Real.log n / (n : ℝ) ^ 2 := by
  by_cases hn : n = 0
  · simp only [hn, LSeries.term_zero, norm_zero, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0),
      div_zero]
  · rw [LSeries.norm_term_eq, ite_eq_right hn]
    simp only [LSeries.logMul, Pi.one_apply, mul_one, ← Complex.natCast_log, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg n)]
    rw [show (2 : ℂ).re = ((2 : ℕ) : ℝ) from rfl, Real.rpow_natCast]

/-- A coefficient bound norm(a n)<=d*n*log n dominates each L-series term
on Re s=3 by d times the logarithm-weighted constant-series term at 2.
Cancel one power of n at nonzero indices and treat n=0 separately.
This converts the local-root coefficient estimate into absolute convergence. -/
theorem norm_series_term_le_log_majorant {a : ℕ → ℂ} {d : ℝ} (ha : ∀ n, ‖a n‖ ≤ d * n * Real.log n)
    {s : ℂ} (hs : s.re = 3) (n : ℕ) :
    ‖LSeries.term a s n‖ ≤ d * ‖LSeries.term (LSeries.logMul 1) (2 : ℂ) n‖ := by
  by_cases hn : n = 0
  · simp only [hn, LSeries.term_zero, norm_zero, mul_zero, le_refl]
  · rw [LSeries.norm_term_eq, ite_eq_right hn, hs, show (3 : ℝ) = ((3 : ℕ) : ℝ) from rfl,
      Real.rpow_natCast, norm_log_series_term]
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    calc
      _ ≤ (d * n * Real.log n) / (n : ℝ) ^ 3 :=
        div_le_div_of_nonneg_right (ha n) (pow_nonneg (Nat.cast_nonneg n) 3)
      _ = _ := by
        rw [show d * (n : ℝ) * Real.log n = (n : ℝ) * (d * Real.log n) from by ring, pow_succ',
          mul_div_mul_left _ _ hnR, mul_div_assoc]

/-- The scalar series log(n)/n^2 is summable over natural n. Apply mathlib's
logarithm-weighted L-series convergence above the abscissa of the constant
sequence and take norms. This gives a finite universal arithmetic constant. -/
theorem summable_log_series_majorant : Summable (fun n : ℕ ↦ Real.log n / (n : ℝ) ^ 2) := by
  have hlt : LSeries.abscissaOfAbsConv 1 < ((2 : ℂ).re : EReal) := by
    rw [LSeries.abscissaOfAbsConv_one]
    change ((1 : ℝ) : EReal) < ((2 : ℝ) : EReal)
    exact EReal.coe_lt_coe_iff.mpr (by norm_num only : (1 : ℝ) < 2)
  have hs := (LSeriesSummable_logMul_of_lt_re hlt).norm
  exact hs.congr (fun n ↦ norm_log_series_term n)

/-- Coefficients bounded by d*n*log n give an absolutely convergent L-series
at each point of real part 3, with norm at most d*sum(log n/n^2).
Dominate norms termwise by the summable scalar majorant and compare tsums.
This supplies the arithmetic contribution in equation (5.31). -/
theorem summable_series_and_norm_le_log_majorant {a : ℕ → ℂ} {d : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ d * n * Real.log n) {s : ℂ} (hs : s.re = 3) :
    LSeriesSummable a s ∧ ‖LSeries a s‖ ≤ d * ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2 := by
  have hbound : ∀ n, ‖LSeries.term a s n‖ ≤ d * (Real.log n / (n : ℝ) ^ 2) := by
    intro n
    simpa only [norm_log_series_term] using norm_series_term_le_log_majorant ha hs n
  have hmajor := summable_log_series_majorant.mul_left d
  have hn : Summable (fun n ↦ ‖LSeries.term a s n‖) :=
    hmajor.of_nonneg_of_le (fun n ↦ norm_nonneg _) hbound
  refine ⟨summable_norm_iff.mp hn, ?_⟩
  calc
    _ ≤ ∑' n : ℕ, ‖LSeries.term a s n‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n : ℕ, d * (Real.log n / (n : ℝ) ^ 2) := hn.tsum_le_tsum hbound hmajor
    _ = _ := tsum_mul_left

/-- If d local roots have norm at most p, the sum of their k-th powers times
log p has norm at most d*p^k*log p. Apply the triangle inequality and the
norm bound to each power. No Ramanujan bound is needed; this is the local
coefficient estimate for general Euler factors. -/
theorem norm_primePowerLogCoefficient_le {d : ℕ} (α : Fin d → ℂ) {p : ℕ} (hα : ∀ j, ‖α j‖ ≤ p)
    (k : ℕ) : ‖∑ j : Fin d, α j ^ k * Complex.log p‖ ≤ (d : ℝ) * (p : ℝ) ^ k * Real.log p := by
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
  have hterm : ∀ j : Fin d, ‖α j ^ k * Complex.log p‖ ≤ (p : ℝ) ^ k * Real.log p := by
    intro j
    rw [norm_mul, norm_pow, ← Complex.natCast_log, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlog]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hα j) k) hlog
  calc
    _ ≤ ∑ j : Fin d, ‖α j ^ k * Complex.log p‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin d, (p : ℝ) ^ k * Real.log p := Finset.sum_le_sum (fun j _ ↦ hterm j)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- For a positive exponent k, the local-root logarithmic coefficient is
bounded by d*p^k*log(p^k). Use log(p^k)=k*log p and k>=1 after the local-root
estimate. This expresses the majorant in the Dirichlet-series index. -/
theorem norm_primePowerLogCoefficient_le_log_power {d : ℕ} (α : Fin d → ℂ) {p : ℕ}
    (hα : ∀ j, ‖α j‖ ≤ p) {k : ℕ} (hk : 1 ≤ k) :
    ‖∑ j : Fin d, α j ^ k * Complex.log p‖ ≤ (d : ℝ) * (p : ℝ) ^ k * Real.log ((p : ℝ) ^ k) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog := Real.log_natCast_nonneg p
  have hm : Real.log (p : ℝ) ≤ Real.log ((p : ℝ) ^ k) := by
    rw [Real.log_pow]
    exact le_mul_of_one_le_left hlog hkR
  exact
    (norm_primePowerLogCoefficient_le α hα k).trans
      (mul_le_mul_of_nonneg_left hm
        (mul_nonneg (Nat.cast_nonneg d) (pow_nonneg (Nat.cast_nonneg p) k)))

/-- Suppose each nonzero coefficient is a positive-power local-root sum,
with d roots of norm at most its base p. Then norm(a n)<=d*n*log n at every
natural index. Apply the prime-power estimate and use zero at the other
indices. This derives the global bound from local-root data. -/
theorem norm_logCoefficient_le_of_localRoots {d : ℕ} {a : ℕ → ℂ}
    (ha :
      ∀ n,
        a n ≠ 0 →
          ∃ (p k : ℕ) (α : Fin d → ℂ),
            1 ≤ k ∧ n = p ^ k ∧ a n = ∑ j : Fin d, α j ^ k * Complex.log p ∧ ∀ j, ‖α j‖ ≤ p)
    (n : ℕ) : ‖a n‖ ≤ (d : ℝ) * n * Real.log n := by
  by_cases hz : a n = 0
  · rw [hz, norm_zero]
    exact
      mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg n)) (Real.log_natCast_nonneg n)
  · obtain ⟨p, k, α, hk, hn, hval, hα⟩ := ha n hz
    rw [hval, hn, Nat.cast_pow]
    exact norm_primePowerLogCoefficient_le_log_power α hα hk

/-- If the negative logarithmic derivative is represented by the L-series
of these local-root coefficients, its norm on Re s=3 is bounded by the
finite constant d*sum(log n/n^2). Use absolute convergence and the preceding
series norm estimate. The logarithmic-derivative series identity remains an
explicit premise; this theorem supplies its quantitative bound, not the
identity itself. -/
theorem norm_logDeriv_at_three_le_of_localRoots {d : ℕ} {a : ℕ → ℂ} {L : ℂ → ℂ}
    (ha :
      ∀ n,
        a n ≠ 0 →
          ∃ (p k : ℕ) (α : Fin d → ℂ),
            1 ≤ k ∧ n = p ^ k ∧ a n = ∑ j : Fin d, α j ^ k * Complex.log p ∧ ∀ j, ‖α j‖ ≤ p)
    {s : ℂ} (hs : s.re = 3) (hlog : logDeriv L s = -LSeries a s) :
    ‖logDeriv L s‖ ≤ (d : ℝ) * ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2 := by
  rw [hlog, norm_neg]
  exact (summable_series_and_norm_le_log_majorant (norm_logCoefficient_le_of_localRoots ha) hs).2

end PseudoPrime.AnalyticNumberTheory.General
