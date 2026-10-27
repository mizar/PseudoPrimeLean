/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PairedEulerDifferences
public import PseudoPrime.Analysis.TwoPoleGammaMajorant
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorPrefixBounds

/-! # Gamma zero mass from a positive signed two-pole majorant -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For primitive nonprincipal individual-RH data and ordered nodes right of one,
a critical-line Gamma majorant by a signed Poisson pair gives convergence and
a retained-prefix upper bound for the actual Gamma zero mass. RH places each
nonzero-divisor zero on the critical line. Transfer the height-kernel result
without changing the multiplicity or taking separate endpoint norms. -/
theorem gamma_zeroMass_le_of_poissonDifferenceWeight_majorant {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {σ τ u v : ℝ} (hs : 1 < σ) (hst : σ ≤ τ) (hv : 0 ≤ v)
    (hvu : v ≤ u) (A B : Finset ℕ)
    (hmajorant :
      ∀ t : ℝ,
        ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ ≤
          Analysis.poissonDifferenceWeight (σ - 1 / 2) (τ - 1 / 2) u v t) :
    Summable
        (fun ρ : ℂ ↦
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖Complex.Gamma ρ‖) ∧
      (∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖Complex.Gamma ρ‖) ≤
        (u - v) *
            (Real.log q / 2 + (logDeriv χ.gammaFactor (σ : ℂ)).re -
              (logDeriv (1 : DirichletCharacter ℂ 1).LFunction (σ : ℂ)).re -
              ∑ m ∈ A, realPairedEulerTerm χ σ m) +
          v *
            ((logDeriv χ.gammaFactor (σ : ℂ)).re - (logDeriv χ.gammaFactor (τ : ℂ)).re +
                (logDeriv (1 : DirichletCharacter ℂ 1).LFunction (τ : ℂ)).re -
              (logDeriv (1 : DirichletCharacter ℂ 1).LFunction (σ : ℂ)).re -
              (τ - σ) * (∑ m ∈ B, Real.log m * realPairedEulerTerm χ τ m)) := by
  have h :=
    zeroMass_le_of_poissonDifferenceWeight_majorant hq hRH hp hne hinv hs hst hv hvu A B
      (fun t ↦ ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖) (fun _ ↦ norm_nonneg _) hmajorant
  have he (ρ : ℂ) :
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖Complex.Gamma ρ‖ =
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * ρ.im)‖ := by
    by_cases hD : MeromorphicOn.divisor χ.completedLFunction Set.univ ρ = 0
    · simp only [hD, Int.cast_zero, zero_mul]
    · have hr :=
        completedLFunction_zero_re_eq_half_of_dirichletRH hRH hp hinv
          (dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD)
      have hρ : ρ = (1 / 2 : ℂ) + Complex.I * ρ.im := by
        calc
          ρ = (ρ.re : ℂ) + (ρ.im : ℂ) * Complex.I := (Complex.re_add_im ρ).symm
          _ = _ := by
            rw [hr]
            norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
            ring
      exact
        congrArg
          (fun z : ℂ ↦
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖Complex.Gamma z‖)
          hρ
  exact ⟨h.1.congr (fun ρ ↦ (he ρ).symm), (tsum_congr he).trans_le h.2⟩

/-- The conductor-independent remainder for the two-pole Gamma profile.
The two Gamma derivatives and principal logarithmic derivatives retain their signs.
This remainder is bounded rationally below in the zero-mass interface. -/
noncomputable def twoPoleGammaConstant {q : ℕ} (χ : DirichletCharacter ℂ q) : ℝ :=
  (3 / 2 : ℝ) * (logDeriv χ.gammaFactor ((5 / 4 : ℝ) : ℂ)).re -
      (1 / 2 : ℝ) * (logDeriv χ.gammaFactor ((11 / 4 : ℝ) : ℂ)).re -
      (3 / 2 : ℝ) * (logDeriv (1 : DirichletCharacter ℂ 1).LFunction ((5 / 4 : ℝ) : ℂ)).re +
    (1 / 2 : ℝ) * (logDeriv (1 : DirichletCharacter ℂ 1).LFunction ((11 / 4 : ℝ) : ℂ)).re

/-- For primitive nonprincipal individual-RH data, the two-pole profile bounds the
Gamma zero mass, including convergence. Specialize the signed Poisson theorem and
retain both finite Euler prefixes for later witness-absence comparisons. -/
theorem gamma_zeroMass_le_twoPole_retained_prefixes {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (A B : Finset ℕ) :
    Summable
        (fun ρ : ℂ ↦
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖Complex.Gamma ρ‖) ∧
      (∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖Complex.Gamma ρ‖) ≤
        Real.log q / 2 + twoPoleGammaConstant χ - (∑ m ∈ A, realPairedEulerTerm χ (5 / 4) m) -
          (3 / 4 : ℝ) * (∑ m ∈ B, Real.log m * realPairedEulerTerm χ (11 / 4) m) := by
  have h :=
    gamma_zeroMass_le_of_poissonDifferenceWeight_majorant hq hRH hp hne hinv (σ := 5 / 4) (τ :=
      11 / 4) (u := 3 / 2) (v := 1 / 2) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) A B
      (by
        intro t
        norm_num only
        exact Analysis.norm_Gamma_half_add_I_le_twoPole t)
  refine ⟨h.1, ?_⟩
  unfold twoPoleGammaConstant
  convert h.2 using 1
  ring

/-- The principal logarithmic derivative at five fourths has norm at most four.
Use the Euler-ratio estimate and the rational quarter-power lower bound.
This bounds the principal contribution to the two-pole remainder. -/
theorem norm_principal_logDeriv_five_fourths_le_four :
    ‖logDeriv (1 : DirichletCharacter ℂ 1).LFunction ((5 / 4 : ℝ) : ℂ)‖ ≤ 4 := by
  have h :=
    norm_logDeriv_real_le_euler_ratio (1 : DirichletCharacter ℂ 1) (r := 1 / 4) (by norm_num only)
  norm_num only at h
  have hd : 0 < 1 + (2 : ℝ) ^ (-(1 / 4 : ℝ)) / (1 / 4) :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (div_nonneg (Real.rpow_nonneg (by norm_num only : (0 : ℝ) ≤ 2) _) (by norm_num only))
  have hb : ((1 / 4 : ℝ)⁻¹ ^ 2 + (1 / 4 + 1)⁻¹) / (1 + (2 : ℝ) ^ (-(1 / 4 : ℝ)) / (1 / 4)) ≤ 4 := by
    apply (div_le_iff₀ hd).mpr
    have hp := Analysis.two_neg_quarter_ge_four_fifths
    norm_num only
    nlinarith only [hp]
  norm_num only at hb
  exact h.trans hb

/-- Right of one, the principal logarithmic derivative has nonpositive real part.
The signed Mangoldt series has nonnegative terms. This preserves its favorable sign. -/
theorem re_principal_logDeriv_nonpos {σ : ℝ} (hs : 1 < σ) :
    (logDeriv (1 : DirichletCharacter ℂ 1).LFunction (σ : ℂ)).re ≤ 0 := by
  rw [re_logDeriv_eq_signed_Mangoldt_tsum _ hs]
  simp only [MulChar.one_apply (isUnit_of_subsingleton (_ : ZMod 1)), Complex.one_re, one_mul]
  exact
    neg_nonpos.mpr
      (tsum_nonneg
        (fun n ↦
          div_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (Real.rpow_nonneg (Nat.cast_nonneg n) σ)))

/-- For every complex Dirichlet character, bound the Gamma derivative at five fourths.
Evaluate eight reciprocal-prefix terms rationally; use the result in the two-pole mass. -/
theorem abs_re_gammaFactor_five_fourths_le {q : ℕ} (χ : DirichletCharacter ℂ q) :
    |(logDeriv χ.gammaFactor ((5 / 4 : ℝ) : ℂ)).re| ≤ 27 / 20 := by
  have h :=
    abs_re_logDeriv_gammaFactor_le_prefix χ (σ := 5 / 4) (R := 5 / 8) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) 8
  have hb : Gamma.gammaPrefixAllowance (5 / 8) 8 ≤ (27 / 20 : ℝ) := by
    norm_num only [Gamma.gammaPrefixAllowance, Finset.sum_range_succ, Finset.sum_range_zero,
      max_def, ite_true, ite_false]
  exact h.trans hb

/-- For every complex Dirichlet character, bound the Gamma derivative at eleven fourths.
Evaluate eight reciprocal-prefix terms rationally; use the result in the two-pole mass. -/
theorem abs_re_gammaFactor_eleven_fourths_le {q : ℕ} (χ : DirichletCharacter ℂ q) :
    |(logDeriv χ.gammaFactor ((11 / 4 : ℝ) : ℂ)).re| ≤ 71 / 100 := by
  have h :=
    abs_re_logDeriv_gammaFactor_le_prefix χ (σ := 11 / 4) (R := 11 / 8) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) 8
  have hb : Gamma.gammaPrefixAllowance (11 / 8) 8 ≤ (71 / 100 : ℝ) := by
    norm_num only [Gamma.gammaPrefixAllowance, Finset.sum_range_succ, Finset.sum_range_zero,
      max_def, ite_true, ite_false]
  exact h.trans hb

/-- For every character, the two-pole remainder is at most 419/50.
Combine the signed principal bound with both Gamma-derivative estimates.
No Riemann hypothesis is needed for this constant estimate. -/
theorem twoPoleGammaConstant_le {q : ℕ} (χ : DirichletCharacter ℂ q) :
    twoPoleGammaConstant χ ≤ 419 / 50 := by
  have hA := abs_re_gammaFactor_five_fourths_le χ
  have hB := abs_re_gammaFactor_eleven_fourths_le χ
  have hZ := re_principal_logDeriv_nonpos (σ := 11 / 4) (by norm_num only)
  have hlow :=
    (abs_le.mp
        ((Complex.abs_re_le_norm
              (logDeriv (1 : DirichletCharacter ℂ 1).LFunction ((5 / 4 : ℝ) : ℂ))).trans
          norm_principal_logDeriv_five_fourths_le_four)).1
  unfold twoPoleGammaConstant
  linarith only [(abs_le.mp hA).2, (abs_le.mp hB).1, hZ, hlow]

/-- For primitive nonprincipal individual-RH data, bound the convergent Gamma zero
mass by half the conductor logarithm plus 419/50, retaining both Euler prefixes.
Insert the rational remainder estimate into the signed-profile inequality. -/
theorem gamma_zeroMass_le_twoPole_rational_retained {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (A B : Finset ℕ) :
    Summable
        (fun ρ : ℂ ↦
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖Complex.Gamma ρ‖) ∧
      (∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖Complex.Gamma ρ‖) ≤
        Real.log q / 2 + 419 / 50 - (∑ m ∈ A, realPairedEulerTerm χ (5 / 4) m) -
          (3 / 4 : ℝ) * (∑ m ∈ B, Real.log m * realPairedEulerTerm χ (11 / 4) m) := by
  have h := gamma_zeroMass_le_twoPole_retained_prefixes hq hRH hp hne hinv A B
  have hc := twoPoleGammaConstant_le χ
  refine ⟨h.1, ?_⟩
  linarith only [h.2, hc]

/-- For primitive nonprincipal individual-RH data, the Gamma zero mass converges and
is at most half the conductor logarithm plus 419/50. Choose empty Euler prefixes.
This supplies a finite-scale alternative to the existing prefix mass estimate. -/
theorem gamma_zeroMass_le_half_log_add_419_fiftieths {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    Summable
        (fun ρ : ℂ ↦
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖Complex.Gamma ρ‖) ∧
      (∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖Complex.Gamma ρ‖) ≤
        Real.log q / 2 + 419 / 50 := by
  have h := gamma_zeroMass_le_twoPole_rational_retained hq hRH hp hne hinv ∅ ∅
  simpa only [Finset.sum_empty, mul_zero, sub_zero] using h

/-- Below the stated logarithmic threshold, the two-pole rational mass bound is
strictly smaller than the earlier prefix mass bound. Rational arithmetic proves
the comparison; this statement compares zero-mass bounds, not witness bounds. -/
theorem twoPole_rational_upper_lt_prefix_upper {L : ℝ} (hL : L < 288000000 / 716577) :
    L / 2 + 419 / 50 < (11783423 / 25000000 : ℝ) * L + 199 / 10 := by linarith only [hL]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
