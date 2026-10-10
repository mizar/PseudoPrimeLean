/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.EulerLogDerivative
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.NumberTheory.EulerProduct.ExpLog

/-!
# Differentiation of the logarithmic Euler series

Absolute convergence and a uniform derivative bound on smaller half-planes identify the
ordinary logarithmic derivative with the sum of its local Euler derivatives.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- For admissible roots and Re s > 1, the root-to-prime-power ratios are summable over primes.
Compare their norms with the real p-series using the Ramanujan bound. -/
theorem summable_root_div_prime_cpow (f : GeneralLFunction) (hf : f.IsAdmissible) (j : Fin f.degree)
    {s : ℂ} (hs : 1 < s.re) : Summable (fun p : Nat.Primes ↦ f.root p j / (p : ℂ) ^ s) := by
  have hb := (Real.summable_nat_rpow_inv.mpr hs).subtype Nat.Prime
  apply Summable.of_norm_bounded hb
  intro p
  rw [norm_div, Complex.norm_natCast_cpow_of_pos p.property.pos]
  exact
    (div_le_div_of_nonneg_right (hf.2.2.2.2.1 p p.property j)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans_eq
      (one_div _)

/-- For any Euler data, prime p and complex s, sum -log(1 - root(p,j)/p^s) over the roots.
The logarithm is the principal complex logarithm. For admissible data and Re s > 0,
exponentiating this sum gives the Euler factor; it need not be the principal logarithm
of the product. Summing these local logarithms gives the Euler representation on Re s > 1. -/
noncomputable def localEulerLog (f : GeneralLFunction) (p : Nat.Primes) (s : ℂ) : ℂ :=
  ∑ j : Fin f.degree, -Complex.log (1 - f.root p j / (p : ℂ) ^ s)

/-- For admissible data and Re s > 1, the local Euler logarithms are summable.
Apply logarithmic summability to each root series and sum over the finite degree. -/
theorem summable_localEulerLog (f : GeneralLFunction) (hf : f.IsAdmissible) {s : ℂ}
    (hs : 1 < s.re) : Summable (fun p : Nat.Primes ↦ localEulerLog f p s) := by
  exact summable_sum (fun j _ ↦ (summable_root_div_prime_cpow f hf j hs).clog_one_sub.neg)

/-- For admissible data on Re s > 0, exponentiating the local logarithm recovers the Euler factor.
The root norm bound makes every denominator nonzero. -/
theorem exp_localEulerLog (f : GeneralLFunction) (hf : f.IsAdmissible) (p : Nat.Primes) {s : ℂ}
    (hs : 0 < s.re) : Complex.exp (localEulerLog f p s) = f.eulerFactor p s := by
  unfold localEulerLog eulerFactor
  rw [Complex.exp_sum]
  exact
    Finset.prod_congr rfl
      (fun j _ ↦ by
        rw [Complex.exp_neg, Complex.exp_log (one_sub_root_div_prime_cpow_ne_zero f hf p j hs)])

/-- For admissible data and Re s > 1, L(s) is the exponential of the summed local logarithms.
Exponentiate their convergent series, identify each exponential with its Euler factor,
and apply the admissible Euler product identity. This representation permits termwise
differentiation without choosing a logarithm of the ordinary L-function. -/
theorem ordinary_eq_exp_tsum_localEulerLog (f : GeneralLFunction) (hf : f.IsAdmissible) {s : ℂ}
    (hs : 1 < s.re) : f.L s = Complex.exp (∑' p : Nat.Primes, localEulerLog f p s) := by
  have he := (summable_localEulerLog f hf hs).hasSum.cexp.tprod_eq
  have hprod := (hf.2.2.2.2.2.1 s hs).2.2.2.2
  rw [hprod]
  simpa only [Function.comp_apply, exp_localEulerLog f hf _ (zero_lt_one.trans hs)] using he

/-- For admissible data, a prime p and Re s > 0, the derivative of localEulerLog is
logDeriv of the Euler factor at s. The root norm bound places each denominator in the
principal logarithm's slit plane, so the finite logarithmic sum can be differentiated.
This supplies the individual derivatives for the global logarithmic series. -/
theorem hasDerivAt_localEulerLog (f : GeneralLFunction) (hf : f.IsAdmissible) (p : Nat.Primes)
    {s : ℂ} (hs : 0 < s.re) : HasDerivAt (localEulerLog f p) (logDeriv (f.eulerFactor p) s) s := by
  rw [logDeriv_eulerFactor f hf p hs]
  apply HasDerivAt.fun_sum
  intro j _
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  have hpow := (hasDerivAt_id s).const_cpow (Or.inl hp)
  simp only [id_eq, mul_one] at hpow
  have hd :=
    ((hasDerivAt_const s (f.root p j)).div hpow
          (Complex.cpow_ne_zero_iff.mpr (Or.inl hp))).const_sub
      1
  have hslit : 1 - f.root p j / (p : ℂ) ^ s ∈ Complex.slitPlane := by
    have h :=
      Complex.mem_slitPlane_of_norm_lt_one
        (show ‖-(f.root p j / (p : ℂ) ^ s)‖ < 1 by
          rw [norm_neg]
          exact norm_root_div_prime_cpow_lt_one f hf p j hs)
    simpa only [sub_eq_add_neg] using h
  simp only [Pi.div_apply] at hd
  convert (hd.clog hslit).neg using 1
  field_simp [Complex.cpow_ne_zero_iff.mpr (Or.inl hp)]
  ring

/-- For admissible roots and any real a <= Re s, the root ratio has norm at most p^(-a).
The exponent a need not be positive. Combine the Ramanujan bound with monotonicity of
real powers of p > 1 to obtain a bound uniform on the corresponding half-plane. -/
theorem norm_root_div_prime_cpow_le (f : GeneralLFunction) (hf : f.IsAdmissible) (p : Nat.Primes)
    (j : Fin f.degree) {a : ℝ} {s : ℂ} (has : a ≤ s.re) :
    ‖f.root p j / (p : ℂ) ^ s‖ ≤ ((p : ℕ) : ℝ) ^ (-a) := by
  have hp : (1 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.property.one_lt.le
  rw [norm_div, Complex.norm_natCast_cpow_of_pos p.property.pos]
  calc
    ‖f.root p j‖ / (p : ℝ) ^ s.re ≤ 1 / (p : ℝ) ^ s.re :=
      div_le_div_of_nonneg_right (hf.2.2.2.2.1 p p.property j)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = (p : ℝ) ^ (-s.re) := by rw [Real.rpow_neg (zero_lt_one.trans_le hp).le, one_div]
    _ ≤ (p : ℝ) ^ (-a) := Real.rpow_le_rpow_of_exponent_le hp (neg_le_neg has)

/-- For admissible data and Re s > a > 1, bound the local logarithmic derivative by
2 * degree * log(p) * p^(-a). Each root ratio has norm at most one half, so each
complementary denominator has norm at least one half. Summing over the roots gives
the uniform derivative majorant used to differentiate the prime series. -/
theorem norm_logDeriv_eulerFactor_le (f : GeneralLFunction) (hf : f.IsAdmissible) (p : Nat.Primes)
    {a : ℝ} (ha : 1 < a) {s : ℂ} (hs : a < s.re) :
    ‖logDeriv (f.eulerFactor p) s‖ ≤ 2 * f.degree * Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ (-a) := by
  have hp : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.one_lt
  have hhalf : ((p : ℕ) : ℝ) ^ (-a) ≤ 1 / 2 := by
    have htwo : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.property.two_le
    calc
      (p : ℝ) ^ (-a) ≤ (p : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hp.le (neg_le_neg ha.le)
      _ = 1 / (p : ℝ) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num only) htwo
  have hlog : ‖Complex.log (p : ℕ)‖ = Real.log (p : ℕ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _),
      Complex.norm_of_nonneg (Real.log_nonneg hp.le)]
  rw [logDeriv_eulerFactor f hf p (zero_lt_one.trans (ha.trans hs))]
  calc
    ‖∑ j : Fin f.degree,
            -(f.root p j / (p : ℂ) ^ s) * Complex.log (p : ℕ) / (1 - f.root p j / (p : ℂ) ^ s)‖ ≤
        ∑ j : Fin f.degree, 2 * Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ (-a) :=
      by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      have hu := norm_root_div_prime_cpow_le f hf p j hs.le
      have hd : 1 / 2 ≤ ‖1 - f.root p j / (p : ℂ) ^ s‖ := by
        have h := norm_sub_norm_le (1 : ℂ) (f.root p j / (p : ℂ) ^ s)
        rw [norm_one] at h
        linarith only [h, hu, hhalf]
      rw [norm_div, norm_mul, norm_neg, hlog]
      apply
        (div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) (Real.log_nonneg hp.le))
            (by norm_num only) hd).trans
      nlinarith only [hu, Real.log_nonneg hp.le]
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- For a > 1, the prime majorant log(p) p^(-a) is summable.
Restrict the norm-summable log-weighted constant-coefficient L-series to the prime subtype. -/
private theorem summable_prime_log_majorant {a : ℝ} (ha : 1 < a) :
    Summable (fun p : Nat.Primes ↦ Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ (-a)) := by
  have hbound : LSeries.abscissaOfAbsConv (fun _ : ℕ ↦ (1 : ℂ)) ≤ 1 :=
    LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun _ _ ↦ by rw [norm_one]⟩
  have hs :=
    LSeriesSummable_logMul_of_lt_re
      (hbound.trans_lt
        (show (1 : EReal) < (a : ℂ).re by
          simpa only [Complex.ofReal_re, ← EReal.coe_one, EReal.coe_lt_coe_iff] using ha))
  have hn := hs.norm.comp_injective (i := fun p : Nat.Primes ↦ (p : ℕ)) Subtype.val_injective
  apply hn.congr
  intro p
  rw [Function.comp_apply, LSeries.term_def, ite_eq_right p.property.ne_zero, LSeries.logMul,
    mul_one, norm_div, Complex.norm_natCast_cpow_of_pos p.property.pos, ← Complex.ofReal_natCast, ←
    Complex.ofReal_log (Nat.cast_nonneg _),
    Complex.norm_of_nonneg
      (Real.log_nonneg (show (1 : ℝ) ≤ (p : ℕ) by exact_mod_cast p.property.one_lt.le)),
    Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]

/-- For admissible data and Re s > 1, the derivative of the summed local logarithms is
the prime sum of the local Euler logarithmic derivatives. Choose 1 < a < Re s;
the summable bound 2 * degree * log(p) * p^(-a) is uniform on Re z > a.
Apply termwise differentiation there to differentiate the exponential Euler representation. -/
theorem hasDerivAt_tsum_localEulerLog (f : GeneralLFunction) (hf : f.IsAdmissible) {s : ℂ}
    (hs : 1 < s.re) :
    HasDerivAt (fun z ↦ ∑' p : Nat.Primes, localEulerLog f p z)
      (∑' p : Nat.Primes, logDeriv (f.eulerFactor p) s) s := by
  obtain ⟨a, ha, has⟩ := exists_between hs
  have hu :
    Summable (fun p : Nat.Primes ↦ 2 * f.degree * Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ (-a)) := by
    simpa only [mul_assoc] using (summable_prime_log_majorant ha).mul_left (2 * (f.degree : ℝ))
  have hc : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_gt ⟨Complex.add_re, Complex.smul_re⟩ a
  exact
    hasDerivAt_tsum_of_isPreconnected hu (isOpen_lt continuous_const Complex.continuous_re)
      hc.isPreconnected
      (fun p z hz ↦ hasDerivAt_localEulerLog f hf p (zero_lt_one.trans (ha.trans hz)))
      (fun p z hz ↦ norm_logDeriv_eulerFactor_le f hf p ha hz) has (summable_localEulerLog f hf hs)
      has

/-- For admissible data on Re s > 1, the logarithmic derivative is the sum of the local derivatives.
Differentiate the exponential Euler representation locally and cancel its nonzero exponential. -/
theorem logDeriv_ordinary_eq_tsum_localEuler (f : GeneralLFunction) (hf : f.IsAdmissible) {s : ℂ}
    (hs : 1 < s.re) : logDeriv f.L s = ∑' p : Nat.Primes, logDeriv (f.eulerFactor p) s := by
  have he := (hasDerivAt_tsum_localEulerLog f hf hs).cexp
  have hnear : f.L =ᶠ[nhds s] (fun z ↦ Complex.exp (∑' p : Nat.Primes, localEulerLog f p z)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact ordinary_eq_exp_tsum_localEulerLog f hf hz
  have hd := he.congr_of_eventuallyEq hnear
  rw [logDeriv_apply, hd.deriv, ordinary_eq_exp_tsum_localEulerLog f hf hs]
  exact mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)

/-- For admissible data on Re s > 1, the local logarithmic derivatives are summable.
An intermediate exponent gives a summable prime logarithmic majorant. -/
theorem summable_logDeriv_eulerFactor (f : GeneralLFunction) (hf : f.IsAdmissible) {s : ℂ}
    (hs : 1 < s.re) : Summable (fun p : Nat.Primes ↦ logDeriv (f.eulerFactor p) s) := by
  obtain ⟨a, ha, has⟩ := exists_between hs
  apply Summable.of_norm_bounded ((summable_prime_log_majorant ha).mul_left (2 * (f.degree : ℝ)))
  intro p
  simpa only [mul_assoc] using norm_logDeriv_eulerFactor_le f hf p ha has

/-- For admissible data and Re s > 1, express L'(s)/L(s) as a prime sum of root geometric
series, with terms -log(p) * (root(p,j)/p^s)^(k+1). The local expansions require Re s > 0;
the global identity uses convergence on Re s > 1. Combine the differentiated Euler
representation with those expansions to prepare the Mangoldt-series reindexing. -/
theorem logDeriv_ordinary_eq_prime_geometric_series (f : GeneralLFunction) (hf : f.IsAdmissible)
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv f.L s =
      ∑' p : Nat.Primes,
        ∑ j : Fin f.degree,
          -Complex.log (p : ℕ) * ∑' k : ℕ, (f.root p j / (p : ℂ) ^ s) ^ (k + 1) := by
  rw [logDeriv_ordinary_eq_tsum_localEuler f hf hs]
  exact tsum_congr (fun p ↦ logDeriv_eulerFactor_eq_geometric_series f hf p (zero_lt_one.trans hs))

end PseudoPrime.LLS.Extensions.GeneralLFunction
