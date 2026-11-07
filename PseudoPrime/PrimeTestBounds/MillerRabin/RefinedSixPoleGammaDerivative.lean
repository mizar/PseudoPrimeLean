/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleGammaBounds
public import PseudoPrime.AnalyticNumberTheory.Gamma.TrigammaSpecialValues
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # First derivative of the refined even Gamma correction -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The real part of digamma restricted to the real line. Its derivative at
positive points enters the first derivative of the even Gamma term. -/
noncomputable def digammaReal (x : ℝ) : ℝ :=
  (Complex.digamma (x : ℂ)).re

/-- Digamma plus the first `m` reciprocal terms. Its increase on the positive
axis records the nonnegative tail of the digamma difference series, providing
lower bounds for the digamma derivative. -/
noncomputable def digammaPrefixRemainder (m : ℕ) (x : ℝ) : ℝ :=
  digammaReal x + ∑ k ∈ Finset.range m, (x + k)⁻¹

/-- Every finite digamma-prefix remainder is monotone on the positive axis.
The positive residual in the convergent reciprocal-difference series proves
monotonicity. This yields a lower bound for the derivative of digamma. -/
theorem digamma_prefix_remainder_mono (m : ℕ) :
    MonotoneOn (digammaPrefixRemainder m) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have h := AnalyticNumberTheory.Gamma.real_digamma_difference_ge_prefix hx hxy m
  unfold digammaPrefixRemainder digammaReal
  simp only [one_div, Finset.sum_sub_distrib] at h
  linarith only [h]

/-- At a positive point where real digamma has derivative `d`, each finite
reciprocal-square prefix is at most `d`. Differentiate the monotone prefix
remainder and use nonnegativity of its derivative. This avoids differentiating
an infinite series to obtain a rigorous one-sided bound. -/
theorem digamma_deriv_ge_prefix {x d : ℝ} (hx : 0 < x) (hd : HasDerivAt digammaReal d x) (m : ℕ) :
    (∑ k ∈ Finset.range m, (x + k)⁻¹ ^ 2) ≤ d := by
  have hsum :
    HasDerivAt (fun t : ℝ ↦ ∑ k ∈ Finset.range m, (t + k)⁻¹)
      (∑ k ∈ Finset.range m, -((x + k)⁻¹ ^ 2)) x := by
    apply HasDerivAt.fun_sum
    intro k hk
    have hkx : x + (k : ℝ) ≠ 0 := (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg k)).ne'
    have h := ((hasDerivAt_id x).add_const (k : ℝ)).inv hkx
    convert h using 1
    · funext t; rfl
    · simp only [id_eq, inv_pow, one_div, neg_div]
  have htotal := hd.add hsum
  change HasDerivAt (digammaPrefixRemainder m) _ x at htotal
  have hnon := (digamma_prefix_remainder_mono m).derivWithin_nonneg (x := x)
  have hn : Set.Ioi (0 : ℝ) ∈ nhds x := Ioi_mem_nhds hx
  rw [derivWithin_of_mem_nhds hn, htotal.deriv] at hnon
  simp only [Finset.sum_neg_distrib] at hnon
  linarith only [hnon]

/-- The real part of the complex digamma derivative at `79/100` exceeds
`556/250`. The first eight reciprocal squares give the rational bound, and
Gamma analyticity supplies the required derivative. This controls the first
weighted derivative in the refined Gamma correction. -/
theorem refined_digamma_deriv_lower :
    (556 / 250 : ℝ) < (deriv Complex.digamma ((79 / 100 : ℝ) : ℂ)).re := by
  have hz : (0 : ℝ) < 79 / 100 := by norm_num only
  have hb :=
    AnalyticNumberTheory.Gamma.ball_avoids_nonpos_int (c := 79 / 100) (r := 1 / 2)
      (by norm_num only) (by norm_num only)
  have hΓ :=
    AnalyticNumberTheory.Gamma.analyticAt_Gamma_of_ball (s := ((79 / 100 : ℝ) : ℂ)) (r := 1 / 2)
      (by norm_num only) hb
  have hne : Complex.Gamma (((79 / 100 : ℝ)) : ℂ) ≠ 0 :=
    Complex.Gamma_ne_zero
      (AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos
        (by simpa only [Complex.ofReal_re] using hz))
  have hd :=
    (AnalyticNumberTheory.Gamma.analyticAt_digamma hΓ
          hne).differentiableAt |>.hasDerivAt.real_of_complex
  change HasDerivAt digammaReal _ (79 / 100 : ℝ) at hd
  have h := digamma_deriv_ge_prefix hz hd 8
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one] at h
  linarith only [h]

/-- For an even character, the first derivative of the shifted real Gamma
logarithmic derivative at `27/25` exceeds `139/250`. The even Gamma formula
holds in a neighborhood, and the chain rule transfers the certified digamma
derivative bound. This supplies the first derivative term of the correction. -/
theorem refined_gamma_even_deriv_lower {q : ℕ} {χ : DirichletCharacter ℂ q} (he : χ.Even) :
    (139 / 250 : ℝ) <
      deriv (fun u : ℝ ↦ (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re) (27 / 25) := by
  have hz : (0 : ℝ) < 79 / 100 := by norm_num only
  have hb :=
    AnalyticNumberTheory.Gamma.ball_avoids_nonpos_int (c := 79 / 100) (r := 1 / 2)
      (by norm_num only) (by norm_num only)
  have hΓ :=
    AnalyticNumberTheory.Gamma.analyticAt_Gamma_of_ball (s := ((79 / 100 : ℝ) : ℂ)) (r := 1 / 2)
      (by norm_num only) hb
  have hne : Complex.Gamma (((79 / 100 : ℝ)) : ℂ) ≠ 0 :=
    Complex.Gamma_ne_zero
      (AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos
        (by simpa only [Complex.ofReal_re] using hz))
  have hd :=
    (AnalyticNumberTheory.Gamma.analyticAt_digamma hΓ
          hne).differentiableAt |>.hasDerivAt.real_of_complex
  change HasDerivAt digammaReal _ (79 / 100 : ℝ) at hd
  have hc : (((1 / 2 : ℝ) + 27 / 25) / 2 : ℝ) = 79 / 100 := by norm_num only
  rw [← hc] at hd
  have hd' :=
    (hd.comp (27 / 25 : ℝ)
          (((hasDerivAt_id (27 / 25 : ℝ)).const_add (1 / 2 : ℝ)).div_const 2)).sub_const
      (Real.log Real.pi)
  have hd'' := hd'.div_const 2
  simp only [Function.comp_def, id_eq, hc] at hd''
  have heq :
    (fun u : ℝ ↦ (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re) =ᶠ[nhds (27 / 25 : ℝ)]
      (fun u : ℝ ↦ (digammaReal (((1 / 2 : ℝ) + u) / 2) - Real.log Real.pi) / 2) := by
    have ha : (0 : ℝ) < 1 / 2 + 27 / 25 := by norm_num only
    filter_upwards [(isOpen_lt continuous_const (continuous_const.add continuous_id)).mem_nhds
        ha] with
      u hu
    exact AnalyticNumberTheory.DirichletLFunction.re_gammaFactor_even he hu
  rw [heq.deriv_eq, hd''.deriv]
  have hl := refined_digamma_deriv_lower
  linarith only [hl]

end PseudoPrime.PrimeTestBounds.MillerRabin
