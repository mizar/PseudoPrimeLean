/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEuler570

/-! # Zeta moments for the section 94 Euler constant -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At 38/25 the positive sixth-pole Euler mass is the zeta logarithmic
derivative combined with its first two derivatives. The level-one character
is one at every integer, so no character factor remains in the Euler series. -/
private theorem quarter_euler_zeta_operator :
    8 * (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) =
      -3 * (logDeriv riemannZeta (38 / 25 : ℂ)).re +
          (153 / 50 : ℝ) * (deriv (logDeriv riemannZeta) (38 / 25 : ℂ)).re -
        (2601 / 2500 : ℝ) * (deriv (deriv (logDeriv riemannZeta)) (38 / 25 : ℂ)).re := by
  have h := quarter_euler_operator_570 (1 : DirichletCharacter ℂ 1)
  simp only [DirichletCharacter.LFunction_modOne_eq, MulChar.one_apply (isUnit_of_subsingleton _),
    Complex.one_re, one_mul] at h
  linarith only [h]

/-- The derivative of a logarithmic derivative is the second logarithmic
jet wherever the underlying holomorphic function is nonzero. -/
private theorem logDeriv_first_jet {f : ℂ → ℂ} {s : ℂ} (hf : AnalyticAt ℂ f s) (hn : f s ≠ 0) :
    deriv (logDeriv f) s = deriv (deriv f) s / f s - (deriv f s / f s) ^ 2 := by
  rw [show logDeriv f = deriv f / f from rfl,
    (hf.deriv.differentiableAt.hasDerivAt.div hf.differentiableAt.hasDerivAt hn).deriv]
  field_simp [hn]

/-- Three derivatives of a holomorphic nonvanishing function determine
the second derivative of its logarithmic derivative. Differentiate the
local first-jet identity before evaluating the rational expression. -/
private theorem logDeriv_second_jet {f : ℂ → ℂ} {s : ℂ} (hf : AnalyticAt ℂ f s) (hn : f s ≠ 0) :
    deriv (deriv (logDeriv f)) s =
      deriv (deriv (deriv f)) s / f s - 3 * (deriv f s / f s) * (deriv (deriv f) s / f s) +
        2 * (deriv f s / f s) ^ 3 := by
  have he :
    deriv (logDeriv f) =ᶠ[nhds s] (fun z ↦ deriv (deriv f) z / f z - (deriv f z / f z) ^ 2) := by
    filter_upwards [hf.eventually_analyticAt, hf.continuousAt.eventually_ne hn] with z hz hz₀
    exact logDeriv_first_jet hz hz₀
  have d := hf.differentiableAt.hasDerivAt
  have d₁ := hf.deriv.differentiableAt.hasDerivAt
  have d₂ := hf.deriv.deriv.differentiableAt.hasDerivAt
  rw [he.deriv_eq]
  change deriv (deriv (deriv f) / f - (deriv f / f) ^ 2) s = _
  rw [((d₂.div d hn).sub ((d₁.div d hn).pow 2)).deriv]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.div_apply]
  field_simp [hn]
  ring

/-- Real values of zeta and its first three derivatives at 38/25 determine
the section 94 Euler constant by an explicit rational function. The odd
derivatives use their negatives, so all four inputs are positive moments. -/
private theorem quarter_euler_zeta_jet {z a b c : ℝ} (hz : 0 < z)
    (h₀ : riemannZeta (38 / 25 : ℂ) = (z : ℂ)) (h₁ : deriv riemannZeta (38 / 25 : ℂ) = (-a : ℝ))
    (h₂ : deriv (deriv riemannZeta) (38 / 25 : ℂ) = (b : ℂ))
    (h₃ : deriv (deriv (deriv riemannZeta)) (38 / 25 : ℂ) = (-c : ℝ)) :
    8 * (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) =
      3 * (a / z) + (153 / 50 : ℝ) * (b / z - (a / z) ^ 2) +
        (2601 / 2500 : ℝ) * (c / z - 3 * (a / z) * (b / z) + 2 * (a / z) ^ 3) := by
  let s : ℂ := 38 / 25
  have hs : s ≠ 1 := by norm_num only [s]
  have hA : AnalyticAt ℂ riemannZeta s :=
    (show DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) from fun _ ht ↦
          (differentiableAt_riemannZeta ht).differentiableWithinAt).analyticAt
      (isClosed_singleton.isOpen_compl.mem_nhds hs)
  have hn : riemannZeta s ≠ 0 := by
    rw [show riemannZeta s = (z : ℂ) from h₀]
    exact Complex.ofReal_ne_zero.mpr hz.ne'
  rw [quarter_euler_zeta_operator, logDeriv_first_jet hA hn, logDeriv_second_jet hA hn]
  rw [logDeriv_apply, h₀, h₁, h₂, h₃]
  simp only [← Complex.ofReal_div, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_add,
    ← Complex.ofReal_sub, ← Complex.ofReal_ofNat, Complex.ofReal_re]
  ring

/-- Positive denominator bounds turn numerator endpoints into quotient
endpoints by cross multiplication. -/
private theorem euler_quotient_box {x z l u L U p q : ℝ} (hz : 0 < z) (hl : l ≤ x) (hu : x ≤ u)
    (hL : L ≤ z) (hU : z ≤ U) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpl : p * U ≤ l) (huq : u ≤ q * L) :
    p ≤ x / z ∧ x / z ≤ q := by
  exact
    ⟨(le_div_iff₀ hz).mpr ((mul_le_mul_of_nonneg_left hU hp).trans (hpl.trans hl)),
      (div_le_iff₀ hz).mpr (hu.trans (huq.trans (mul_le_mul_of_nonneg_left hL hq)))⟩

/-- Rational enclosures for the four signed zeta derivatives at 38/25 suffice
for the Euler lower bound 3.7372. The interval products keep the signs of the
quadratic and cubic contributions in the logarithmic derivatives. -/
private theorem quarter_euler_lower_of_zeta_box {z a b c : ℝ}
    (h₀ : riemannZeta (38 / 25 : ℂ) = (z : ℂ)) (h₁ : deriv riemannZeta (38 / 25 : ℂ) = (-a : ℝ))
    (h₂ : deriv (deriv riemannZeta) (38 / 25 : ℂ) = (b : ℂ))
    (h₃ : deriv (deriv (deriv riemannZeta)) (38 / 25 : ℂ) = (-c : ℝ))
    (hz : z ∈ Set.Icc 2.53680538 2.53680540) (ha : a ∈ Set.Icc 3.63067364 3.63067368)
    (hb : b ∈ Set.Icc 14.21347859 14.21347864) (hc : c ∈ Set.Icc 82.06215830 82.06215838) :
    3.7372 ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n := by
  have hz₀ := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2.53680538) hz.1
  have hu :=
    euler_quotient_box (p := 1.43119910) (q := 1.43119916) hz₀ ha.1 ha.2 hz.1 hz.2
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
  have hv :=
    euler_quotient_box (p := 5.60290456) (q := 5.60290467) hz₀ hb.1 hb.2 hz.1 hz.2
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
  have hw : (32.34862172 : ℝ) ≤ c / z :=
    (le_div_iff₀ hz₀).mpr
      ((mul_le_mul_of_nonneg_left hz.2 (by norm_num only)).trans
        ((by norm_num only : (32.34862172 : ℝ) * 2.53680540 ≤ 82.06215830).trans hc.1))
  have hp := (show (0 : ℝ) ≤ 1.43119910 by norm_num only).trans hu.1
  have hsq := pow_le_pow_left₀ hp hu.2 2
  have hcu := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 1.43119910) hu.1 3
  have huv :=
    mul_le_mul hu.2 hv.2 ((show (0 : ℝ) ≤ 5.60290456 by norm_num only).trans hv.1)
      (by norm_num only)
  linarith only [quarter_euler_zeta_jet hz₀ h₀ h₁ h₂ h₃, hu.1, hv.1, hw, hsq, hcu, huv]

/-- The positive Dirichlet moments for the zeta jet at 38/25.
The index zero contributes zero, matching the convention for L-series. -/
noncomputable def quarterZetaMoment (j : ℕ) : ℝ :=
  ∑' n : ℕ, if n = 0 then 0 else (Real.log n) ^ j / (n : ℝ) ^ (38 / 25 : ℝ)

/-- Applying the logarithmic coefficient operator to the constant sequence
raises the complex logarithm to the corresponding power. -/
private theorem zeta_log_mul (j n : ℕ) :
    (LSeries.logMul^[j] (1 : ℕ → ℂ)) n = Complex.log (n : ℂ) ^ j := by
  induction j with
  | zero => simp only [Function.iterate_zero, id_eq, Pi.one_apply, pow_zero]
  | succ k ih => rw [Function.iterate_succ_apply', LSeries.logMul, ih, pow_succ']

/-- The real logarithmic Dirichlet moments converge at 38/25. Use the
invariance of the absolute-convergence abscissa under logarithmic weights. -/
theorem quarter_zeta_moment_summable (j : ℕ) :
    Summable (fun n : ℕ ↦ if n = 0 then 0 else (Real.log n) ^ j / (n : ℝ) ^ (38 / 25 : ℝ)) := by
  have hA : LSeries.abscissaOfAbsConv (LSeries.logMul^[j] (1 : ℕ → ℂ)) = 1 := by
    induction j with
    | zero => exact LSeries.abscissaOfAbsConv_one
    | succ k ih => rw [Function.iterate_succ_apply', LSeries.abscissaOfAbsConv_logMul, ih]
  have hs : LSeriesSummable (LSeries.logMul^[j] (1 : ℕ → ℂ)) (38 / 25) := by
    apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
    rw [hA]
    have hσ : (1 : ℝ) < (38 / 25 : ℂ).re := by
      norm_num only [Complex.div_re, Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_ofNat]
    exact_mod_cast hσ
  apply (Complex.reCLM.summable hs).congr
  intro n
  by_cases hn : n = 0
  · subst n
    rw [LSeries.term_zero, ite_eq_left rfl, Complex.reCLM_apply, Complex.zero_re]
  rw [LSeries.term_of_ne_zero hn, zeta_log_mul, ite_eq_right hn, Complex.reCLM_apply]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _), ← Complex.ofReal_pow,
    show (38 / 25 : ℂ) = ((38 / 25 : ℝ) : ℂ) by
      norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat],
    ← Complex.ofReal_cpow (Nat.cast_nonneg _), ← Complex.ofReal_div, Complex.ofReal_re]

/-- Once the correction starts at an integer N ≥ 1, the positive moment is
a finite prefix plus a unit-step series of the real power-logarithm weight. -/
theorem quarter_zeta_moment_split (j N : ℕ) (hN : 0 < N) :
    quarterZetaMoment j =
      (∑ n ∈ Finset.range N, if n = 0 then 0 else (Real.log n) ^ j / (n : ℝ) ^ (38 / 25 : ℝ)) +
        ∑' n : ℕ, (Real.log ((N : ℝ) + n)) ^ j / ((N : ℝ) + n) ^ (38 / 25 : ℝ) := by
  unfold quarterZetaMoment
  rw [← (quarter_zeta_moment_summable j).sum_add_tsum_nat_add N]
  congr 1
  apply tsum_congr
  intro n
  rw [ite_eq_right ((Nat.lt_add_of_pos_right hN).ne_zero), Nat.cast_add, add_comm]

/-- In the half-plane of absolute convergence the zeta derivatives at the
real point 38/25 are real and equal to the alternating Dirichlet moments. -/
private theorem quarter_zeta_deriv_eq_moment (j : ℕ) :
    iteratedDeriv j riemannZeta (38 / 25 : ℂ) = (-1 : ℂ) ^ j * (quarterZetaMoment j : ℂ) := by
  let s : ℂ := 38 / 25
  let U : Set ℂ := {w | (1 : ℝ) < w.re}
  have hs : 1 < s.re := by
    norm_num only [s, Complex.div_re, Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_ofNat]
  have hU : IsOpen U := Complex.continuous_re.isOpen_preimage (Set.Ioi (1 : ℝ)) isOpen_Ioi
  have he : U.EqOn riemannZeta (LSeries (1 : ℕ → ℂ)) := fun _ hx ↦
    (LSeries_one_eq_riemannZeta hx).symm
  change iteratedDeriv j riemannZeta s = _
  rw [he.iteratedDeriv_of_isOpen hU j (show s ∈ U from hs),
    LSeries_iteratedDeriv j (LSeries.abscissaOfAbsConv_one.symm ▸ (by exact_mod_cast hs))]
  unfold quarterZetaMoment LSeries
  rw [Complex.ofReal_tsum]
  congr 1
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    rw [LSeries.term_zero, ite_eq_left rfl, Complex.ofReal_zero]
  rw [LSeries.term_of_ne_zero hn, zeta_log_mul, ite_eq_right hn, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_log (Nat.cast_nonneg _),
    Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast]
  norm_num only [s, Complex.ofReal_div, Complex.ofReal_ofNat]

/-- The four real Dirichlet moments suffice for the Euler recovery bound.
Only the rational enclosures of these moments remain as input. -/
theorem quarter_euler_lower_of_moments (h₀ : quarterZetaMoment 0 ∈ Set.Icc 2.53680538 2.53680540)
    (h₁ : quarterZetaMoment 1 ∈ Set.Icc 3.63067364 3.63067368)
    (h₂ : quarterZetaMoment 2 ∈ Set.Icc 14.21347859 14.21347864)
    (h₃ : quarterZetaMoment 3 ∈ Set.Icc 82.06215830 82.06215838) :
    3.7372 ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n := by
  apply quarter_euler_lower_of_zeta_box _ _ _ _ h₀ h₁ h₂ h₃
  · simpa only [iteratedDeriv_zero, pow_zero, one_mul] using quarter_zeta_deriv_eq_moment 0
  · simpa only [iteratedDeriv_succ, iteratedDeriv_zero, pow_one, neg_one_mul,
      Complex.ofReal_neg] using quarter_zeta_deriv_eq_moment 1
  · simpa only [iteratedDeriv_succ, iteratedDeriv_zero, neg_one_sq, one_mul] using
      quarter_zeta_deriv_eq_moment 2
  · simpa only [iteratedDeriv_succ, iteratedDeriv_zero, pow_succ, pow_zero, one_mul, neg_one_mul,
      neg_neg, Complex.ofReal_neg] using quarter_zeta_deriv_eq_moment 3

end PseudoPrime.PrimeTestBounds.MillerRabin
