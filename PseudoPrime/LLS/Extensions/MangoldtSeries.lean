/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.EulerLogSeries
public import PseudoPrime.LLS.Extensions.ArithmeticCoefficients
public import PseudoPrime.LLS.Extensions.ShiftedFormulaIntegration

/-!
# Mangoldt series and shifted Mellin inversion

Prime-power reindexing identifies the Euler logarithmic derivative with its arithmetic series.
Mellin inversion supplies the shifted finite sum on the right vertical line.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- Define the complex coefficient a_f(n) Lambda(n) for any Euler data f and natural index n.
It vanishes outside positive prime powers. For admissible data, its L-series converges on
Re s > 1 and represents -L'/L; it supplies the coefficients of shifted arithmetic sums. -/
noncomputable def mangoldtSeriesCoefficient (f : GeneralLFunction) (n : ℕ) : ℂ :=
  f.mangoldtCoefficient n * (ArithmeticFunction.vonMangoldt n : ℂ)

/-- For admissible data and Re s > 1, the Mangoldt coefficient series converges absolutely.
Compare with the log-weighted constant-coefficient L-series using the degree bound. -/
theorem LSeriesSummable_mangoldtSeriesCoefficient (f : GeneralLFunction) (hf : f.IsAdmissible)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable f.mangoldtSeriesCoefficient s := by
  have hb : LSeries.abscissaOfAbsConv (fun _ : ℕ ↦ (1 : ℂ)) ≤ 1 :=
    LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun _ _ ↦ by rw [norm_one]⟩
  have ht : LSeries.abscissaOfAbsConv (fun _ : ℕ ↦ (1 : ℂ)) < s.re :=
    hb.trans_lt (by exact_mod_cast hs)
  have hn := (LSeriesSummable_logMul_of_lt_re ht).norm.mul_left (f.degree : ℝ)
  apply Summable.of_norm_bounded hn
  intro n
  rcases eq_or_ne n 0 with rfl | hn0
  · rw [LSeries.term_zero, norm_zero, LSeries.term_zero, norm_zero, mul_zero]
  · rw [LSeries.term_def, ite_eq_right hn0, norm_div, mangoldtSeriesCoefficient, norm_mul,
      Complex.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, LSeries.term_def,
      ite_eq_right hn0, LSeries.logMul, mul_one, norm_div]
    calc
      ‖f.mangoldtCoefficient n‖ * ArithmeticFunction.vonMangoldt n / ‖(n : ℂ) ^ s‖ ≤
          f.degree * ‖Complex.log (n : ℕ)‖ / ‖(n : ℂ) ^ s‖ :=
        by
        apply div_le_div_of_nonneg_right _ (norm_nonneg _)
        apply
          mul_le_mul (norm_mangoldtCoefficient_le f hf n) _ ArithmeticFunction.vonMangoldt_nonneg
            (Nat.cast_nonneg _)
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _),
          Complex.norm_of_nonneg
            (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0))]
        exact ArithmeticFunction.vonMangoldt_le_log
      _ = _ := mul_div_assoc _ _ _

/-- Positive powers of distinct primes give distinct natural indices.
Uniqueness of prime-power representations recovers both the prime and the exponent. -/
private theorem primePowerIndex_injective :
    Function.Injective (fun pk : Nat.Primes × ℕ ↦ (pk.1 : ℕ) ^ (pk.2 + 1)) := by
  intro a b hab
  obtain ⟨hp, hk⟩ := a.1.property.pow_inj b.1.property hab
  exact Prod.ext (Subtype.ext hp) hk

/-- For any Euler data, prime p, natural k and complex s, rewrite the series term at p^(k+1)
as log(p) times the sum of (root(p,j)/p^s)^(k+1) over the roots.
The identity is algebraic: canonical prime-power coefficients and complex powers give the
rewrite without admissibility or convergence assumptions. It enables prime-power reindexing. -/
theorem mangoldtSeries_term_prime_pow (f : GeneralLFunction) (p : Nat.Primes) (k : ℕ) (s : ℂ) :
    LSeries.term f.mangoldtSeriesCoefficient s ((p : ℕ) ^ (k + 1)) =
      Complex.log (p : ℕ) * ∑ j : Fin f.degree, (f.root p j / (p : ℂ) ^ s) ^ (k + 1) := by
  rw [LSeries.term_def, ite_eq_right (pow_ne_zero _ p.property.ne_zero), mangoldtSeriesCoefficient,
    mangoldtCoefficient_prime_pow f p.property (Nat.succ_ne_zero _),
    ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero _),
    ArithmeticFunction.vonMangoldt_apply_prime p.property, Complex.ofReal_log (Nat.cast_nonneg _),
    primePowerCoefficient, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul,
    Finset.sum_mul, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.ofReal_natCast]
  rw [div_pow, pow_succ]
  ring

/-- For admissible data on Re s > 1, reindex the Mangoldt series by primes and positive powers.
The coefficients vanish outside prime powers; absolute convergence permits iterated summation. -/
theorem LSeries_mangoldt_eq_prime_powers (f : GeneralLFunction) (hf : f.IsAdmissible) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries f.mangoldtSeriesCoefficient s =
      ∑' p : Nat.Primes,
        ∑' k : ℕ,
          Complex.log (p : ℕ) * ∑ j : Fin f.degree, (f.root p j / (p : ℂ) ^ s) ^ (k + 1) := by
  have hrange :
    Function.support (LSeries.term f.mangoldtSeriesCoefficient s) ⊆
      Set.range (fun pk : Nat.Primes × ℕ ↦ (pk.1 : ℕ) ^ (pk.2 + 1)) := by
    intro n hn
    have hpp : IsPrimePow n := by
      by_contra h
      apply hn
      rw [LSeries.term_def, mangoldtSeriesCoefficient, mangoldtCoefficient, ite_eq_right h,
        zero_mul]
      split_ifs <;> simp only [zero_div]
    obtain ⟨p, k, hp, hk, he⟩ := (isPrimePow_nat_iff n).mp hpp
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    exact ⟨(⟨p, hp⟩, k), he⟩
  have he := primePowerIndex_injective.tsum_eq hrange
  have hsum :=
    (LSeriesSummable_mangoldtSeriesCoefficient f hf hs).comp_injective primePowerIndex_injective
  change
    Summable
      (fun pk : Nat.Primes × ℕ ↦
        LSeries.term f.mangoldtSeriesCoefficient s ((pk.1 : ℕ) ^ (pk.2 + 1))) at hsum
  rw [LSeries, ← he, hsum.tsum_prod]
  exact tsum_congr (fun p ↦ tsum_congr (fun k ↦ mangoldtSeries_term_prime_pow f p k s))

/-- For admissible Euler data and Re s > 1, identify the ordinary logarithmic derivative
with the negative L-series of a_f(n) Lambda(n).
Reindex by positive prime powers and exchange the finite root sum with absolutely convergent
geometric series. This connects the Euler product to the arithmetic input of Mellin inversion. -/
theorem logDeriv_ordinary_eq_neg_mangoldtSeries (f : GeneralLFunction) (hf : f.IsAdmissible) {s : ℂ}
    (hs : 1 < s.re) : logDeriv f.L s = -LSeries f.mangoldtSeriesCoefficient s := by
  rw [LSeries_mangoldt_eq_prime_powers f hf hs, logDeriv_ordinary_eq_prime_geometric_series f hf hs,
    ← tsum_neg]
  apply tsum_congr
  intro p
  have hgeo : ∀ j : Fin f.degree, Summable (fun k : ℕ ↦ (f.root p j / (p : ℂ) ^ s) ^ (k + 1)) := by
    intro j
    simpa only [pow_succ'] using
      (summable_geometric_of_norm_lt_one
            (norm_root_div_prime_cpow_lt_one f hf p j (zero_lt_one.trans hs))).mul_left
        (f.root p j / (p : ℂ) ^ s)
  rw [tsum_mul_left, Summable.tsum_finsetSum (fun j _ ↦ hgeo j), Finset.mul_sum, ←
    Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun j _ ↦ by rw [neg_mul])

/-- For admissible Euler data, sigma > 1, x > 0 and tau > 0, express the shifted arithmetic
sum as (2 pi)^(-1) times the vertical integral of -L'/L on Re s = sigma + tau, with kernel
x^(tau+iy)/(tau+iy)^2.
Absolute convergence on this line and the negative Mangoldt-series identity justify logarithmic
Mellin inversion. The result supplies the initial right-line formula for contour shifting. -/
theorem shiftedArithmeticSum_eq_integral_logDeriv (f : GeneralLFunction) (hf : f.IsAdmissible)
    {σ x τ : ℝ} (hσ : 1 < σ) (hx : 0 < x) (hτ : 0 < τ) :
    f.shiftedArithmeticSum x σ =
      (2 * Real.pi : ℝ)⁻¹ •
        ∫ y : ℝ,
          -logDeriv f.L (((σ + τ : ℝ) : ℂ) + y * Complex.I) * (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
            ((τ : ℂ) + y * Complex.I) ^ 2 := by
  have hστ : 1 < σ + τ := lt_trans hσ (lt_add_of_pos_right σ hτ)
  have hzero : f.mangoldtSeriesCoefficient 0 = 0 := by
    rw [mangoldtSeriesCoefficient, ArithmeticFunction.map_zero, Complex.ofReal_zero, mul_zero]
  change
    AnalyticNumberTheory.General.logarithmicWeightedSum
        (AnalyticNumberTheory.General.shiftedLSeriesCoefficient f.mangoldtSeriesCoefficient σ) x =
      _
  rw [AnalyticNumberTheory.General.logarithmicWeightedSum_shifted_eq_integral_LSeries
      f.mangoldtSeriesCoefficient hzero σ hx hτ
      (LSeriesSummable_mangoldtSeriesCoefficient f hf
        (by simpa only [Complex.ofReal_re] using hστ))]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  have hr : 1 < (((σ + τ : ℝ) : ℂ) + y * Complex.I).re := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero] using hστ
  rw [logDeriv_ordinary_eq_neg_mangoldtSeries f hf hr, neg_neg]

end PseudoPrime.LLS.Extensions.GeneralLFunction
