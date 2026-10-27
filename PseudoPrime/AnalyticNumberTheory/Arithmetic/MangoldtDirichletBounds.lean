/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogPowerIntegralBounds
public import PseudoPrime.Analysis.LogDirichletNumericalBounds
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-! # Explicit real bounds for the von Mangoldt Dirichlet series

The logarithmic-power integral comparison gives a bound using only the real part's
distance from one. No prime number theorem or Riemann hypothesis is needed.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For any real exponent and natural n, the von Mangoldt term divided by n^sigma
is bounded by (log n+1)n^(-sigma). Use von Mangoldt at most log n and the
nonnegative reciprocal power. This is the termwise input for the integral comparison. -/
theorem vonMangoldt_div_rpow_le_envelope {σ : ℝ} (n : ℕ) :
    ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ ≤ (Real.log n + 1) * (n : ℝ) ^ (-σ) := by
  have hn :=
    div_le_div_of_nonneg_right (ArithmeticFunction.vonMangoldt_le_log (n := n))
      (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
  rw [Real.rpow_neg (Nat.cast_nonneg n)]
  exact
    hn.trans
      (by
        rw [div_eq_mul_inv]
        exact
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
            (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) σ)))

/-- For sigma greater than one, the real von Mangoldt Dirichlet series is summable.
Dominate its nonnegative terms by the summable logarithmic-power envelope.
This justifies infinite-sum comparisons and removal of the zero terms at zero and one. -/
theorem summable_vonMangoldt_div_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ) := by
  have hr : 0 < σ - 1 := sub_pos.mpr hσ
  have he : -(σ - 1) - 1 = -σ := by ring
  have hs := Analysis.summable_logPower_envelope hr
  rw [he] at hs
  exact
    hs.of_nonneg_of_le
      (fun n ↦
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ))
      (vonMangoldt_div_rpow_le_envelope)

/-- For sigma greater than one, the von Mangoldt Dirichlet series is at most
(sigma-1)^(-2)+(sigma-1)^(-1). Remove the zero terms at zero and one, then
compare with the decreasing logarithmic-power envelope and its exact integral.
This provides an unconditional numerical bound for ordinary L-function logarithmic derivatives. -/
theorem tsum_vonMangoldt_div_rpow_le {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ) ≤ (σ - 1)⁻¹ ^ 2 + (σ - 1)⁻¹ := by
  have hr : 0 < σ - 1 := sub_pos.mpr hσ
  have he : -(σ - 1) - 1 = -σ := by ring
  have henv := Analysis.summable_logPower_envelope hr
  have htail :=
    henv.comp_injective
      (fun a b h ↦ Nat.add_right_cancel h : Function.Injective (fun n : ℕ ↦ n + 2))
  have hsum := summable_vonMangoldt_div_rpow hσ
  have hshift := hsum.sum_add_tsum_nat_add 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
    ArithmeticFunction.map_zero, ArithmeticFunction.vonMangoldt_apply_one, zero_div,
    zero_add] at hshift
  rw [← hshift]
  have ht :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt (n + 2) / (n + 2 : ℕ) ^ σ) ≤
      ∑' n : ℕ, (Real.log (n + 2 : ℕ) + 1) * (n + 2 : ℕ) ^ (-(σ - 1) - 1) := by
    apply
      Summable.tsum_le_tsum (fun n ↦ ?_) (hsum.comp_injective (fun a b h ↦ Nat.add_right_cancel h))
        htail
    rw [he]
    exact vonMangoldt_div_rpow_le_envelope (n + 2)
  exact ht.trans (Analysis.tsum_logPower_envelope_le hr)

/-- For real coefficients and positive real exponent, the complex L-series is the
real embedding of the real-power Dirichlet sum. Compare terms, including the
zero index, and commute the real embedding with the infinite sum. -/
theorem lSeries_ofReal_eq_tsum_div_rpow (f : ℕ → ℝ) {σ : ℝ} (hσ : 0 < σ) :
    LSeries (fun n ↦ (f n : ℂ)) (σ : ℂ) = (((∑' n : ℕ, f n / (n : ℝ) ^ σ) : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero, Nat.cast_zero, Real.zero_rpow hσ.ne', div_zero,
      Complex.ofReal_zero]
  · rw [LSeries.term_of_ne_zero hn, ← Complex.ofReal_natCast, ←
      Complex.ofReal_cpow (Nat.cast_nonneg n), ← Complex.ofReal_div]

/-- For sigma greater than one, the von Mangoldt Dirichlet sum equals the
logarithmic Dirichlet sum divided by the power Dirichlet sum. Use the Euler
logarithmic-derivative identity and termwise differentiation of the constant-one
L-series. This keeps the denominator instead of bounding it by one. -/
theorem tsum_vonMangoldt_eq_log_ratio {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ) =
      (∑' n : ℕ, Real.log n / (n : ℝ) ^ σ) / (∑' n : ℕ, 1 / (n : ℝ) ^ σ) := by
  have he := ArithmeticFunction.LSeries_vonMangoldt_eq (s := (σ : ℂ)) hσ
  have ha : LSeries.abscissaOfAbsConv (1 : ℕ → ℂ) < (σ : ℂ).re := by
    rw [LSeries.abscissaOfAbsConv_one]
    exact_mod_cast hσ
  rw [LSeries_deriv ha, neg_neg] at he
  have hlog : LSeries.logMul (1 : ℕ → ℂ) = (fun n : ℕ ↦ (Real.log n : ℂ)) := by
    funext n
    simp only [LSeries.logMul, Pi.one_apply, mul_one, ← Complex.ofReal_natCast,
      Complex.ofReal_log (Nat.cast_nonneg n)]
  have hone : (1 : ℕ → ℂ) = (fun _ ↦ ((1 : ℝ) : ℂ)) := rfl
  rw [hlog, hone, lSeries_ofReal_eq_tsum_div_rpow _ (zero_lt_one.trans hσ),
    lSeries_ofReal_eq_tsum_div_rpow _ (zero_lt_one.trans hσ),
    lSeries_ofReal_eq_tsum_div_rpow _ (zero_lt_one.trans hσ), ← Complex.ofReal_div] at he
  exact Complex.ofReal_injective he

/-- For positive r, the von Mangoldt series at 1+r is at most
(r^(-2)+1/(r+1))/(1+2^(-r)/r). Bound the logarithmic numerator by its integral
plus two initial terms, and keep an integral lower bound for the power denominator.
The estimate is unconditional and supplies a sharper ordinary L-function allowance. -/
theorem tsum_vonMangoldt_le_euler_ratio {r : ℝ} (hr : 0 < r) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r)) ≤
      (r⁻¹ ^ 2 + (r + 1)⁻¹) / (1 + (2 : ℝ) ^ (-r) / r) := by
  have hs : 1 < 1 + r := by linarith only [hr]
  rw [tsum_vonMangoldt_eq_log_ratio hs]
  have hp : -(1 + r) = -r - 1 := by ring
  have hd : (∑' n : ℕ, 1 / (n : ℝ) ^ (1 + r)) = ∑' n : ℕ, (n : ℝ) ^ (-r - 1) := by
    apply tsum_congr
    intro n
    rw [one_div, ← Real.rpow_neg (Nat.cast_nonneg n), hp]
  have hn :
    (∑' n : ℕ, Real.log n / (n : ℝ) ^ (1 + r)) = ∑' n : ℕ, Real.log n * (n : ℝ) ^ (-r - 1) := by
    apply tsum_congr
    intro n
    rw [div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg n), hp]
  rw [hd, hn]
  have hlo := Analysis.one_add_two_rpow_div_le_tsum hr
  have hpos : 0 < 1 + (2 : ℝ) ^ (-r) / r :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (div_nonneg (Real.rpow_nonneg (by norm_num only : (0 : ℝ) ≤ 2) _) hr.le)
  have hnumer :=
    add_nonneg (sq_nonneg r⁻¹) (inv_nonneg.mpr (by linarith only [hr] : (0 : ℝ) ≤ r + 1))
  exact
    (div_le_div_of_nonneg_right (Analysis.tsum_logPower_le hr) (hpos.le.trans hlo)).trans
      (div_le_div_of_nonneg_left hnumer hpos hlo)

/--
Input: a scale `η` with `0 < η ≤ 1`.
Claim: multiplying the von Mangoldt Dirichlet series at `1 + η` by `η` gives an absolute bound
of four.
Proof: use the Euler-ratio estimate, compare its denominator with `1 / (2η)`, and simplify the
resulting numerator using `η ≤ 1`.
Role: gives a uniform mass bound for finite low-prime contributions in the zero detector.
-/
theorem eta_mul_tsum_vonMangoldt_le_four {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    η * (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + η)) ≤ 4 := by
  have hbase : (1 : ℝ) ≤ 2 := by norm_num only
  have hexp : -1 ≤ -η := by linarith only [hη1]
  have hpow : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-η) := by
    calc
      (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by norm_num only [Real.rpow_neg]
      _ ≤ (2 : ℝ) ^ (-η) := Real.rpow_le_rpow_of_exponent_le hbase hexp
  have hden : 1 / (2 * η) ≤ 1 + (2 : ℝ) ^ (-η) / η := by
    have hdiv := div_le_div_of_nonneg_right hpow hη.le
    have hrewrite : (1 / 2 : ℝ) / η = 1 / (2 * η) := by ring
    rw [hrewrite] at hdiv
    linarith only [hdiv]
  have hdenpos : 0 < 1 + (2 : ℝ) ^ (-η) / η := by positivity
  have hbound := tsum_vonMangoldt_le_euler_ratio hη
  have hrecip : (η + 1)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity : 0 < η + 1)]
    linarith only [hη]
  have hnum : η * (η⁻¹ ^ 2 + (η + 1)⁻¹) ≤ η⁻¹ + η := by
    have hηinv : η * η⁻¹ = 1 := by rw [mul_inv_cancel₀ hη.ne']
    have hfirst : η * η⁻¹ ^ 2 = η⁻¹ := by
      calc
        η * η⁻¹ ^ 2 = (η * η⁻¹) * η⁻¹ := by ring
        _ = η⁻¹ := by
          rw [hηinv]; ring
    calc
      η * (η⁻¹ ^ 2 + (η + 1)⁻¹) = η⁻¹ + η * (η + 1)⁻¹ := by rw [mul_add, hfirst]
      _ ≤ η⁻¹ + η := by
        simpa only [mul_one] using (add_le_add_right (mul_le_mul_of_nonneg_left hrecip hη.le) η⁻¹)
  have hηinv : η * η⁻¹ = 1 := by rw [mul_inv_cancel₀ hη.ne']
  have hηinvpos : 0 < η⁻¹ := by positivity
  have hsquare : η ^ 2 ≤ 1 := by nlinarith only [hη, hη1]
  have hsmall : η ≤ η⁻¹ := by
    have hmul := mul_le_mul_of_nonneg_right hsquare hηinvpos.le
    have hleft : η ^ 2 * η⁻¹ = η := by
      calc
        η ^ 2 * η⁻¹ = η * (η * η⁻¹) := by ring
        _ = η := by
          rw [hηinv]; ring
    have hright : 1 * η⁻¹ = η⁻¹ := by ring
    rw [hleft, hright] at hmul
    exact hmul
  have hnumsmall : η⁻¹ + η ≤ 2 * η⁻¹ := by linarith only [hsmall]
  have hdenlarge : 2 * η⁻¹ ≤ 4 * (1 + (2 : ℝ) ^ (-η) / η) := by
    have hmul := mul_le_mul_of_nonneg_left hden (by norm_num : (0 : ℝ) ≤ 4)
    have hrewrite : 4 * (1 / (2 * η)) = 2 * η⁻¹ := by
      field_simp; ring
    rw [hrewrite] at hmul
    exact hmul
  have hratio : η * ((η⁻¹ ^ 2 + (η + 1)⁻¹) / (1 + (2 : ℝ) ^ (-η) / η)) ≤ 4 := by
    rw [show
        η * ((η⁻¹ ^ 2 + (η + 1)⁻¹) / (1 + (2 : ℝ) ^ (-η) / η)) =
          (η * (η⁻¹ ^ 2 + (η + 1)⁻¹)) / (1 + (2 : ℝ) ^ (-η) / η)
        by ring]
    apply (div_le_iff₀ hdenpos).2
    exact le_trans hnum (le_trans hnumsmall hdenlarge)
  exact le_trans (mul_le_mul_of_nonneg_left hbound hη.le) (by simpa only using hratio)

/--
Inputs: a finite cutoff and a scale `η` with `0 < η ≤ 1`.
Claim: the von Mangoldt Dirichlet mass through the cutoff, multiplied by `η`, is at most four.
Proof: dominate the finite sum by its nonnegative summable series and apply
`eta_mul_tsum_vonMangoldt_le_four`.
Role: bounds finite low-prime mass uniformly in the Euler cutoff.
-/
theorem eta_mul_finite_vonMangoldt_sum_le_four (N : ℕ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    η * (∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + η)) ≤ 4 := by
  let f : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + η)
  have hsummable : Summable f := by
    apply summable_vonMangoldt_div_rpow
    linarith only [hη]
  have hnonneg : ∀ i ∉ Finset.range (N + 1), 0 ≤ f i := by
    intro i hi
    dsimp only [f]
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg i) _)
  have hfinite : (∑ n ∈ Finset.range (N + 1), f n) ≤ ∑' n, f n :=
    hsummable.sum_le_tsum (Finset.range (N + 1)) hnonneg
  have hratio := eta_mul_tsum_vonMangoldt_le_four hη hη1
  have hscaled := mul_le_mul_of_nonneg_left hfinite hη.le
  calc
    η * (∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + η)) =
        η * ∑ n ∈ Finset.range (N + 1), f n :=
      by simp only [f]
    _ ≤ η * ∑' n, f n := by simpa only [Finset.sum_attach] using hscaled
    _ ≤ 4 := by
      have hseries :
        (∑' n, f n) = ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + η) := by
        apply tsum_congr
        intro n
        rfl
      rw [hseries] at hratio
      exact le_trans (mul_le_mul_of_nonneg_left (le_of_eq hseries) hη.le) hratio

end PseudoPrime.AnalyticNumberTheory.Arithmetic
