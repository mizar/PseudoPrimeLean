/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleSharpError

/-! # Full principal series for the refined sixth-pole kernel -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The normalized kernel weight vanishes beyond its positive support. Specialize
the inverse Mellin profile and use its support theorem. -/
theorem refinedKernelWeight_zero_of_lt {u : ℝ} (hu : Real.exp (21 / 8 : ℝ) < u) :
    refinedKernelWeight u = 0 := by
  have hp : 0 < u := (Real.exp_pos _).trans hu
  rw [refinedKernelWeight, refinedSixPoleKernel,
    LLS.PaperStatements.rationalPole_transform (m := 3) (a := 25 / 54) (c := 21 / 16) (u := u)
      (by norm_num only) (by norm_num only) (by norm_num only) hp,
    Complex.ofReal_re, refined_six_pole_profile_zero hu, zero_div]

/-- For positive scale, the real principal series is its finite sum through the exact
support cutoff. Terms past the cutoff and the zero index vanish. -/
theorem refined_principal_sum_finite {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) =
      ∑ n ∈ Finset.Ioc 0 ⌊x * Real.exp (21 / 8 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re := by
  apply tsum_eq_sum
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp only [LLS.PaperStatements.MellinKernel.summand, ite_true, Complex.zero_re]
  · have hlt : ⌊x * Real.exp (21 / 8 : ℝ)⌋₊ < n := by
      by_contra h
      exact hn (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0, le_of_not_gt h⟩)
    have hnr : x * Real.exp (21 / 8 : ℝ) < (n : ℝ) := Nat.lt_of_floor_lt hlt
    rw [refined_principal_summand_eq hx hn0]
    dsimp only [refinedScaledWeight]
    rw [refinedKernelWeight_zero_of_lt ((lt_div_iff₀ hx).mpr (by linarith only [hnr])), zero_div,
      mul_zero]

/-- At positive scale, the full principal series equals the supported double Abel
integral with no boundary terms. The weight and derivative vanish at the support endpoint. -/
theorem refined_full_double_abel {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re =
      (∫ u : ℝ in (0 : ℝ)..Real.exp (21 / 8 : ℝ),
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) * refinedSecondDensity u) /
        Real.sqrt x := by
  have hc : refinedCoord (Real.exp (21 / 8 : ℝ)) = 0 := by
    norm_num only [refinedCoord, Real.log_exp]
  have hw : refinedWeight (Real.exp (21 / 8 : ℝ)) = 0 := by
    norm_num only [refinedWeight, hc, zero_pow, zero_mul, zero_div]
  have hd : refinedWeightDeriv (Real.exp (21 / 8 : ℝ)) = 0 := by
    norm_num only [refinedWeightDeriv, hc, zero_pow, mul_zero, sub_zero]
  have h := refined_principal_double_abel hx (Real.exp_pos (21 / 8 : ℝ)).le le_rfl
  simp only [hw, hd, mul_zero, zero_mul, sub_zero, add_zero] at h
  have hs :=
    LLS.PaperStatements.MellinKernel.summable_summand refinedSixPoleKernel
      (1 : DirichletCharacter ℂ 1) hx
  change Complex.reCLM (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n) = _
  rw [Complex.reCLM.map_tsum hs]
  change (∑' n : ℕ, (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) = _
  rw [refined_principal_sum_finite hx]
  exact h

/-- The linear moment of the second density is integrable and equals the kernel
half-point value. Evaluate its three logarithmic moments and combine exponentials. -/
theorem refined_second_main_full :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ u * refinedSecondDensity u)
        (Set.Ioc 0 (Real.exp (21 / 8 : ℝ))) ∧
      (∫ u : ℝ in Set.Ioc 0 (Real.exp (21 / 8 : ℝ)), u * refinedSecondDensity u) =
        (22958251200 / 243087455521 : ℝ) * Real.exp (21 / 16 : ℝ) := by
  have h3 := refined_density_moment 3 1 (by norm_num only)
  have h4 := refined_density_moment 4 1 (by norm_num only)
  have h5 := refined_density_moment 5 1 (by norm_num only)
  simp only [Real.rpow_one] at h3 h4 h5
  have he :
    (fun u : ℝ ↦ u * refinedSecondDensity u) =
      (fun u : ℝ ↦
        (29 / 50 : ℝ) ^ 2 *
              (u * Real.exp (-refinedCoord u) / (120 * u * Real.sqrt u) * refinedCoord u ^ 5) -
            (10 * (29 / 50 : ℝ) * (27 / 25 : ℝ)) *
              (u * Real.exp (-refinedCoord u) / (120 * u * Real.sqrt u) * refinedCoord u ^ 4) +
          (20 * (27 / 25 : ℝ) ^ 2) *
            (u * Real.exp (-refinedCoord u) / (120 * u * Real.sqrt u) * refinedCoord u ^ 3)) := by
    funext u
    dsimp only [refinedSecondDensity]
    ring
  rw [he]
  have hi5 := h5.1.const_mul ((29 / 50 : ℝ) ^ 2)
  have hi4 := h4.1.const_mul (10 * (29 / 50 : ℝ) * (27 / 25 : ℝ))
  have hi3 := h3.1.const_mul (20 * (27 / 25 : ℝ) ^ 2)
  refine ⟨(hi5.sub hi4).add hi3, ?_⟩
  have hsum := MeasureTheory.integral_add (hi5.sub hi4) hi3
  have hsum2 := MeasureTheory.integral_sub hi5 hi4
  simp only [Pi.sub_apply] at hsum hsum2
  rw [hsum, hsum2, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, h5.2, h4.2, h3.2]
  norm_num only [Nat.factorial, Nat.reduceAdd, Nat.cast_ofNat]
  have hexp : Real.exp (-(567 / 200 : ℝ)) * Real.exp (1659 / 400 : ℝ) = Real.exp (21 / 16 : ℝ) := by
    rw [← Real.exp_add]
    norm_num only
  nlinarith only [hexp]

/-- At positive scale, the full principal series minus the kernel half-point main term
is exactly the normalized logarithmic Mangoldt error integral. Split the full integral. -/
theorem refined_full_error_identity {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re -
        Real.sqrt x * (refinedSixPoleKernel.function (1 / 2)).re =
      (∫ u : ℝ in (0 : ℝ)..Real.exp (21 / 8 : ℝ),
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
            refinedSecondDensity u) /
        Real.sqrt x := by
  rw [refined_full_double_abel hx,
    refined_log_integral_split hx (Real.exp_pos (21 / 8 : ℝ)).le le_rfl,
    intervalIntegral.integral_of_le (Real.exp_pos _).le, refined_second_main_full.2, ←
    refined_six_pole_half]
  have hs := (Real.sqrt_pos.mpr hx).ne'
  field_simp (disch :=
    first
    | exact hs
    | norm_num only)
  rw [Real.sq_sqrt hx.le]
  ring

/-- Under RH and at scale at least one, the full principal series differs from its
half-point main term by at most the explicit sharp error. Apply the integral bound and
normalize by the positive square root of the scale. -/
theorem refined_full_sharp_error (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    |(∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re -
          Real.sqrt x * (refinedSixPoleKernel.function (1 / 2)).re| ≤
      (231 / 5000 : ℝ) * (6889 / 2700) +
        ((1839 / 1000 : ℝ) * (Real.log x + 21 / 8) + 2) *
            ((918330048 / 17682025 : ℝ) * Real.exp (-(21 / 16 : ℝ))) /
          Real.sqrt x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  rw [refined_full_error_identity hx0, abs_div, abs_of_pos hs]
  apply (div_le_iff₀ hs).mpr
  have h := refined_sharp_integral_explicit hRH hx (Real.exp_pos (21 / 8 : ℝ)).le le_rfl
  convert h using 1
  field_simp (disch :=
    first
    | exact hs.ne'
    | norm_num only)

end PseudoPrime.PrimeTestBounds.MillerRabin
