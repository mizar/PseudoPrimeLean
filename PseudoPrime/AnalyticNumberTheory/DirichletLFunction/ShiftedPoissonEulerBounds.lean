/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PoissonNumericalBounds

/-!
# Euler error bounds for shifted Poisson zero tests

Extend Euler-ratio estimates to every height and retain exact Gamma contributions
when combining shifted Poisson centers with signed finite coefficients.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For every character, positive r and real height, the ordinary logarithmic
derivative at 1+r+it obeys the explicit Euler-ratio bound. Dominate its twisted
Mangoldt series by the untwisted series. This extends the real-axis error budget
to shifted Poisson centers without imposing RH. -/
theorem norm_logDeriv_vertical_le_euler_ratio {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    ‖logDeriv χ.LFunction (((1 + r : ℝ) : ℂ) + t * Complex.I)‖ ≤
      (r⁻¹ ^ 2 + (r + 1)⁻¹) / (1 + (2 : ℝ) ^ (-r) / r) := by
  have hs : 1 < 1 + r := by linarith only [hr]
  have hn := norm_neg_deriv_div_dirichletLFunction_le_vonMangoldt_tsum χ hs t
  simp only [neg_div, norm_neg] at hn
  exact hn.trans (Arithmetic.tsum_vonMangoldt_le_euler_ratio hr)

/-- For a shift at most one, the Euler-ratio majorant is at most four divided by the shift.
Use the lower bound `2 ^ (-r) ≥ 1 / 2` and the elementary reciprocal inequalities. -/
theorem euler_ratio_le_four_div_gap {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (r⁻¹ ^ 2 + (r + 1)⁻¹) / (1 + (2 : ℝ) ^ (-r) / r) ≤ 4 / r := by
  have hx : 1 ≤ r⁻¹ := by
    rw [one_le_inv₀ hr]
    exact hr1
  have hp : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-r) := by
    calc
      (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by norm_num [Real.rpow_neg, Real.rpow_one]
      _ ≤ (2 : ℝ) ^ (-r) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num only) (by linarith only [hr1])
  have hden : 1 / (2 * r) ≤ 1 + (2 : ℝ) ^ (-r) / r := by
    have hdiv : 1 / (2 * r) ≤ (2 : ℝ) ^ (-r) / r := by
      rw [show 1 / (2 * r) = (1 / 2) / r by ring]
      apply (div_le_div_iff₀ hr hr).2
      exact mul_le_mul_of_nonneg_right hp hr.le
    linarith only [hdiv]
  have hrecip : (r + 1)⁻¹ ≤ r⁻¹ := by
    apply (inv_le_inv₀ (by positivity) hr).2
    linarith only [hr]
  have hA : r⁻¹ ^ 2 + (r + 1)⁻¹ ≤ 2 * r⁻¹ ^ 2 := by
    calc
      r⁻¹ ^ 2 + (r + 1)⁻¹ = (r + 1)⁻¹ + r⁻¹ ^ 2 := by ring
      _ ≤ r⁻¹ + r⁻¹ ^ 2 := by simpa only [add_comm] using add_le_add_right hrecip (r⁻¹ ^ 2)
      _ ≤ 2 * r⁻¹ ^ 2 := by nlinarith only [hx]
  apply (div_le_iff₀ (by positivity)).2
  have hmul := mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ 4 / r)
  have htarget : 2 * r⁻¹ ^ 2 ≤ (4 / r) * (1 / (2 * r)) := by
    field_simp
    ring_nf
    nlinarith only [hr]
  calc
    r⁻¹ ^ 2 + (r + 1)⁻¹ ≤ 2 * r⁻¹ ^ 2 := hA
    _ ≤ (4 / r) * (1 / (2 * r)) := htarget
    _ ≤ (4 / r) * (1 + (2 : ℝ) ^ (-r) / r) := hmul

/-- The ordinary logarithmic derivative on the line `1 + r + it` is at most `4 / r`
when `0 < r ≤ 1`. Combine the uniform Euler-ratio estimate with its elementary simplification. -/
theorem norm_logDeriv_vertical_le_four_div_gap {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (t : ℝ) :
    ‖logDeriv χ.LFunction (((1 + r : ℝ) : ℂ) + t * Complex.I)‖ ≤ 4 / r := by
  exact (norm_logDeriv_vertical_le_euler_ratio χ hr t).trans (euler_ratio_le_four_div_gap hr hr1)

/-- For each fixed shift `0 < r ≤ 1`, the completed logarithmic derivative is bounded by the
Euler term `4 / r` plus a logarithmic-height gamma term, uniformly in the modulus and character.
The gamma constant may depend on `r`; a constant uniform in the shift is needed for log-free use. -/
theorem exists_norm_completed_logDeriv_small_shift_bound {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ A : ℝ,
      0 < A ∧
        ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
          χ ≠ 1 →
            ∀ t : ℝ,
              ‖logDeriv χ.completedLFunction (((1 + r : ℝ) : ℂ) + Complex.I * t)‖ ≤
                4 / r + A * (Real.log (4 + |t|) + 1) := by
  have hσ : 0 < (1 + r : ℝ) := by linarith only [hr]
  have hσ' : (1 + r : ℝ) ≤ 2 := by linarith only [hr1]
  obtain ⟨A, hA, hgamma⟩ := exists_uniform_norm_logDeriv_gammaFactor_vertical_le_log hσ hσ'
  refine ⟨A, hA, ?_⟩
  intro q _ χ hne t
  let s : ℂ := ((1 + r : ℝ) : ℂ) + Complex.I * t
  have hsre : s.re = 1 + r := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hs1 : 1 ≤ s.re := by
    rw [hsre]; linarith only [hr]
  have hspos : 0 < s.re := zero_lt_one.trans_le hs1
  have hF : DirichletCharacter.completedLFunction χ s ≠ 0 :=
    completedLFunction_ne_zero_of_one_le_re hne hs1
  have hG : DirichletCharacter.gammaFactor χ s ≠ 0 := gammaFactor_ne_zero_of_re_pos χ hspos
  have hderivG := (analyticAt_gammaFactor_of_re_pos χ hspos).differentiableAt
  have hidentity :=
    logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne hF hG hderivG
  have hsum :
    logDeriv χ.completedLFunction s = logDeriv χ.LFunction s + logDeriv χ.gammaFactor s := by
    rw [hidentity]
    ring
  have hordinary : ‖logDeriv χ.LFunction s‖ ≤ 4 / r := by
    have h := norm_logDeriv_vertical_le_four_div_gap χ hr hr1 t
    have hsEq : s = (((1 + r : ℝ) : ℂ) + t * Complex.I) := by
      dsimp [s]
      rw [mul_comm (Complex.I : ℂ) (t : ℂ)]
    rw [hsEq]
    exact h
  rw [hsum]
  calc
    ‖logDeriv χ.LFunction s + logDeriv χ.gammaFactor s‖ ≤
        ‖logDeriv χ.LFunction s‖ + ‖logDeriv χ.gammaFactor s‖ :=
      norm_add_le _ _
    _ ≤ 4 / r + A * (Real.log (4 + |t|) + 1) := by
      apply add_le_add hordinary
      simpa only [s] using hgamma q χ t

/-- For shifts at most one half, the completed logarithmic derivative has a bound whose
constant is uniform in the shift, modulus, and nonprincipal character. Combine the uniform
gamma estimate on `3/4 ≤ Re(s) ≤ 3/2` with the Euler bound for the ordinary logarithmic
derivative. This gives the shift-uniform input needed for a local multiplicity estimate. -/
theorem exists_uniform_norm_completed_logDeriv_small_shift_bound :
    ∃ A : ℝ,
      0 < A ∧
        ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
          χ ≠ 1 →
            ∀ {r : ℝ},
              0 < r →
                r ≤ 1 / 2 →
                ∀ t : ℝ,
                  ‖logDeriv χ.completedLFunction (((1 + r : ℝ) : ℂ) + Complex.I * t)‖ ≤
                    4 / r + A * (Real.log (4 + |t|) + 1) := by
  obtain ⟨C, hC, hstrip⟩ := exists_uniform_norm_logDeriv_gammaFactor_on_strip
  let A : ℝ := 2 * C + 1
  have hA : 0 < A := by
    dsimp only [A]
    linarith only [hC]
  refine ⟨A, hA, ?_⟩
  intro q _ χ hne r hr hr1 t
  let s : ℂ := ((1 + r : ℝ) : ℂ) + Complex.I * t
  have hsre : s.re = 1 + r := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hsim : s.im = t := by
    simp only [s, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      mul_zero, one_mul, zero_add]
    exact Complex.ofReal_re t
  have hslo : 3 / 4 ≤ s.re := by
    rw [hsre]
    linarith only [hr]
  have hshi : s.re ≤ 3 / 2 := by
    rw [hsre]
    linarith only [hr1]
  have hs1 : 1 ≤ s.re := by
    rw [hsre]
    linarith only [hr]
  have hspos : 0 < s.re := zero_lt_one.trans_le hs1
  have hF : DirichletCharacter.completedLFunction χ s ≠ 0 :=
    completedLFunction_ne_zero_of_one_le_re hne hs1
  have hG : DirichletCharacter.gammaFactor χ s ≠ 0 := gammaFactor_ne_zero_of_re_pos χ hspos
  have hderivG := (analyticAt_gammaFactor_of_re_pos χ hspos).differentiableAt
  have hidentity :=
    logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne hF hG hderivG
  have hsum :
    logDeriv χ.completedLFunction s = logDeriv χ.LFunction s + logDeriv χ.gammaFactor s := by
    rw [hidentity]
    ring
  have hordinary : ‖logDeriv χ.LFunction s‖ ≤ 4 / r := by
    have h := norm_logDeriv_vertical_le_four_div_gap χ hr (by linarith only [hr1]) t
    have hsEq : s = (((1 + r : ℝ) : ℂ) + t * Complex.I) := by
      dsimp [s]
      rw [mul_comm (Complex.I : ℂ) (t : ℂ)]
    rw [hsEq]
    exact h
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have htarg : 0 < 4 + |t| := by positivity
  have hlog4 : 0 ≤ Real.log (4 + |t|) :=
    Real.log_nonneg
      (by
        have := abs_nonneg t; linarith)
  have harg : 2 * |t| + 2 ≤ 2 * (4 + |t|) := by nlinarith only [abs_nonneg t]
  have hlog : Real.log (2 * |t| + 2) ≤ Real.log (4 + |t|) + 1 := by
    calc
      Real.log (2 * |t| + 2) ≤ Real.log (2 * (4 + |t|)) := Real.log_le_log (by positivity) harg
      _ = Real.log 2 + Real.log (4 + |t|) := by
        rw [Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) (ne_of_gt htarg)]
      _ ≤ Real.log (4 + |t|) + 1 := by linarith only [hlog2]
  have hLnonneg : 0 ≤ Real.log (4 + |t|) + 1 := by linarith only [hlog4]
  have hfactor : Real.log (2 * |s.im| + 2) + 1 ≤ 2 * (Real.log (4 + |t|) + 1) := by
    rw [hsim]
    linarith only [hlog, hlog4]
  have hgamma : ‖logDeriv χ.gammaFactor s‖ ≤ A * (Real.log (4 + |t|) + 1) := by
    have hbound := hstrip χ hslo hshi
    have hbound' : ‖logDeriv χ.gammaFactor s‖ ≤ C * (2 * (Real.log (4 + |t|) + 1)) := by
      calc
        ‖logDeriv χ.gammaFactor s‖ ≤ C * (Real.log (2 * |s.im| + 2) + 1) := hbound
        _ ≤ C * (2 * (Real.log (4 + |t|) + 1)) := mul_le_mul_of_nonneg_left hfactor hC
    calc
      ‖logDeriv χ.gammaFactor s‖ ≤ C * (2 * (Real.log (4 + |t|) + 1)) := hbound'
      _ ≤ A * (Real.log (4 + |t|) + 1) := by
        dsimp only [A]
        nlinarith only [hC, hLnonneg]
  rw [hsum]
  calc
    ‖logDeriv χ.LFunction s + logDeriv χ.gammaFactor s‖ ≤
        ‖logDeriv χ.LFunction s‖ + ‖logDeriv χ.gammaFactor s‖ :=
      norm_add_le _ _
    _ ≤ 4 / r + A * (Real.log (4 + |t|) + 1) := add_le_add hordinary hgamma

/-- The real divisor-weighted Poisson sum centered at 1+r+it, with horizontal
distance r+1/2 from the critical line. It is defined with total real arithmetic
for all r and t; convergence and positivity follow under the later RH hypotheses.
This is the value used in signed shifted-center zero certificates. -/
noncomputable def shiftedCompletedPoissonSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (r t : ℝ) : ℝ :=
  ∑' ρ : ℂ,
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
      ((1 / 2 + r) / Complex.normSq ((((1 + r : ℝ) : ℂ) + t * Complex.I) - ρ))

/-- For primitive nonprincipal individual-RH data and positive r, subtracting
the conductor term and the exact real Gamma derivative from the shifted Poisson sum
leaves an error bounded by the Euler ratio. Use the completed Poisson identity and
the ordinary/completed derivative decomposition. Gamma signs are retained. -/
theorem shifted_poissonSum_centered_sub_gamma_le_euler_ratio {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    |shiftedCompletedPoissonSum χ r t - Real.log q / 2 -
          (logDeriv χ.gammaFactor (((1 + r : ℝ) : ℂ) + t * Complex.I)).re| ≤
      (r⁻¹ ^ 2 + (r + 1)⁻¹) / (1 + (2 : ℝ) ^ (-r) / r) := by
  let s := (((1 + r : ℝ) : ℂ) + t * Complex.I)
  have hs : s.re = 1 + r := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hs1 : 1 ≤ s.re := by
    rw [hs]; linarith only [hr]
  have hspos : 0 < s.re := zero_lt_one.trans_le hs1
  have he :=
    completed_poissonSum_eq_logDeriv_re hq hRH hp hne hinv (s := s)
      (by
        rw [hs]; linarith only [hr])
  rw [hs, show 1 + r - 1 / 2 = 1 / 2 + r by ring] at he
  have hd :=
    logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne
      (completedLFunction_ne_zero_of_one_le_re hne hs1) (gammaFactor_ne_zero_of_re_pos χ hspos)
      (analyticAt_gammaFactor_of_re_pos χ hspos).differentiableAt
  unfold shiftedCompletedPoissonSum
  change |(∑' ρ : ℂ, _) - Real.log q / 2 - (logDeriv χ.gammaFactor s).re| ≤ _
  rw [he, add_sub_cancel_right, ← Complex.sub_re, ← hd]
  exact (Complex.abs_re_le_norm _).trans (norm_logDeriv_vertical_le_euler_ratio χ hr t)

/-- For primitive nonprincipal individual-RH data and a finite collection of
positive horizontal gaps, heights and signed weights, the absolute weighted sum of
the conductor-and-Gamma-subtracted Poisson errors is bounded by the absolute-weighted
Euler ratios. Apply the shifted estimate termwise. This supplies a certificate
interface that does not replace the signed Gamma combination by separate norms. -/
theorem shifted_poisson_signed_combination_error_le {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {ι : Type*} (S : Finset ι) (r t w : ι → ℝ)
    (hr : ∀ i ∈ S, 0 < r i) :
    |∑ i ∈ S,
          w i *
            (shiftedCompletedPoissonSum χ (r i) (t i) - Real.log q / 2 -
              (logDeriv χ.gammaFactor ((((1 + r i : ℝ) : ℂ) + t i * Complex.I))).re)| ≤
      ∑ i ∈ S, |w i| * (((r i)⁻¹ ^ 2 + (r i + 1)⁻¹) / (1 + (2 : ℝ) ^ (-r i) / r i)) := by
  apply (Finset.abs_sum_le_sum_abs _ S).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul]
  exact
    mul_le_mul_of_nonneg_left
      (shifted_poissonSum_centered_sub_gamma_le_euler_ratio hq hRH hp hne hinv (hr i hi) (t i))
      (abs_nonneg (w i))

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
