/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorGrowth

/-!
# Vertical gamma-factor regularity and logarithmic growth

Positive real part avoids all gamma poles. Continuity controls a bounded height interval;
the central-strip logarithmic estimate controls its complement.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Positive real part and a nonnegative real shift exclude nonpositive integral
half-arguments. Compare real parts of a purported equality. This verifies the gamma
regularity conditions for both character parities. -/
theorem half_add_ne_neg_nat_of_re_pos {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 ≤ a) (m : ℕ) :
    (s + (a : ℂ)) / 2 ≠ -(m : ℂ) := by
  intro he
  have hr := congrArg Complex.re he
  simp only [Complex.div_ofNat_re, Complex.add_re, Complex.ofReal_re, Complex.neg_re,
    Complex.natCast_re] at hr
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith only [hr, hs, ha, hm]

/-- For any character and a point with positive real part, the gamma factor is analytic
there. Both parity half-arguments avoid nonpositive integers; differentiability on the
open half-plane gives analyticity. This supports local logarithmic derivatives. -/
theorem analyticAt_gammaFactor_of_re_pos {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 0 < s.re) : AnalyticAt ℂ χ.gammaFactor s := by
  have hd : DifferentiableOn ℂ χ.gammaFactor {z : ℂ | 0 < z.re} := by
    intro z hz
    have h0 : ∀ m : ℕ, z / 2 ≠ -(m : ℂ) := by
      simpa only [Complex.ofReal_zero, add_zero] using
        half_add_ne_neg_nat_of_re_pos hz (a := 0) le_rfl
    rcases χ.even_or_odd with he | ho
    · exact (differentiableAt_gammaFactor_of_even_of_half_ne_neg_nat he h0).differentiableWithinAt
    · exact
        (differentiableAt_gammaFactor_of_odd_of_half_ne_neg_nat ho
            (by
              simpa only [Complex.ofReal_one] using
                half_add_ne_neg_nat_of_re_pos hz (a := 1) zero_le_one)).differentiableWithinAt
  exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)

/-- At a point with positive real part, either parity gamma factor is nonzero. Apply the
regular half-argument formulas. This permits analytic division in the gamma-factor
logarithmic derivative. -/
theorem gammaFactor_ne_zero_of_re_pos {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    χ.gammaFactor s ≠ 0 := by
  rcases χ.even_or_odd with he | ho
  · apply gammaFactor_ne_zero_of_even_of_half_ne_neg_nat he
    simpa only [Complex.ofReal_zero, add_zero] using
      half_add_ne_neg_nat_of_re_pos hs (a := 0) le_rfl
  · apply gammaFactor_ne_zero_of_odd_of_half_ne_neg_nat ho
    simpa only [Complex.ofReal_one] using half_add_ne_neg_nat_of_re_pos hs (a := 1) zero_le_one

/-- For a fixed positive real part, the gamma-factor logarithmic derivative is continuous on
the entire vertical line. Analyticity and nonvanishing give an analytic quotient; compose
with the vertical parametrization. This controls bounded height intervals. -/
theorem continuous_logDeriv_gammaFactor_vertical {N : ℕ} (χ : DirichletCharacter ℂ N) {σ : ℝ}
    (hσ : 0 < σ) : Continuous (fun t : ℝ => logDeriv χ.gammaFactor ((σ : ℂ) + Complex.I * t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hs : 0 < ((σ : ℂ) + Complex.I * t).re := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] using hσ
  have hg := analyticAt_gammaFactor_of_re_pos χ hs
  have hl : AnalyticAt ℂ (logDeriv χ.gammaFactor) ((σ : ℂ) + Complex.I * t) :=
    hg.deriv.div hg (gammaFactor_ne_zero_of_re_pos χ hs)
  exact
    hl.continuousAt.comp (f := fun t : ℝ => (σ : ℂ) + Complex.I * t)
      ((continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousAt)

/-- For a fixed real part in (0,2], the gamma-factor logarithmic derivative on its vertical
line is bounded by A times log(4+abs t)+1 for some positive A. Use compact continuity
near height zero and the logarithmic strip estimate elsewhere. This supplies full-line
Mellin integrability. -/
theorem exists_norm_logDeriv_gammaFactor_vertical_le_log {N : ℕ} (χ : DirichletCharacter ℂ N)
    {σ : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 2) :
    ∃ A : ℝ,
      0 < A ∧
        ∀ t : ℝ,
          ‖logDeriv χ.gammaFactor ((σ : ℂ) + Complex.I * t)‖ ≤ A * (Real.log (4 + |t|) + 1) := by
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn
      (continuous_logDeriv_gammaFactor_vertical χ hσ).continuousOn
  let D : ℝ := ‖Complex.log (Real.pi : ℂ)‖ + Real.pi + Gamma.digammaLogErrorBound + 4
  let A : ℝ := 1 + |D| + max M 0
  have hA1 : 1 ≤ A := by
    dsimp only [A]; linarith only [abs_nonneg D, le_max_right M 0]
  have hDM : D ≤ |D| := le_abs_self D
  refine ⟨A, zero_lt_one.trans_le hA1, fun t => ?_⟩
  have hL : 0 ≤ Real.log (4 + |t|) := Real.log_nonneg (by linarith only [abs_nonneg t])
  by_cases ht : 1 ≤ |t|
  · have hsr : |((σ : ℂ) + Complex.I * t).re| ≤ 2 := by
      simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, abs_of_pos hσ] using hσ'
    have hsi : 1 ≤ |((σ : ℂ) + Complex.I * t).im| := by
      simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, one_mul, zero_mul, zero_add] using ht
    have hb := norm_logDeriv_gammaFactor_le_log χ hsr hsi
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, one_mul, zero_mul, zero_add] at hb
    have hD : D ≤ A := by
      dsimp only [A]; linarith only [hDM, le_max_right M 0]
    change ‖logDeriv χ.gammaFactor ((σ : ℂ) + Complex.I * t)‖ ≤ A * _
    dsimp only [D] at hD
    nlinarith only [hb, hD, hA1, hL]
  · have htb : |t| ≤ 1 := (lt_of_not_ge ht).le
    have hm := hM t (abs_le.mp htb)
    have hMA : M ≤ A := by
      dsimp only [A]
      linarith only [le_max_left M 0, abs_nonneg D]
    nlinarith only [hm, hMA, hA1, hL]

/-- The principal character of modulus one is even. Its gamma factor is `Gammaℝ`,
so it supplies a fixed reference function independent of the modulus. -/
theorem principal_modulus_one_even : (1 : DirichletCharacter ℂ 1).Even := by
  rw [DirichletCharacter.Even, Subsingleton.elim (-1 : ZMod 1) 1, map_one]

/-- At a point with positive real part, any character gamma logarithmic derivative equals
the modulus-one reference derivative either at that point or translated by one.
Parity identifies the gamma factors and the translation chain rule has derivative one.
This reduces bounds uniform in characters to two fixed functions. -/
theorem logDeriv_gammaFactor_eq_one_or_one_shift {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 0 < s.re) :
    logDeriv χ.gammaFactor s = logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor s ∨
      logDeriv χ.gammaFactor s = logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor (s + 1) := by
  classical
  have h1 : (1 : DirichletCharacter ℂ 1).Even := by
    rw [DirichletCharacter.Even, Subsingleton.elim (-1 : ZMod 1) 1, map_one]
  rcases χ.even_or_odd with he | ho
  · left
    have hfun : χ.gammaFactor = (1 : DirichletCharacter ℂ 1).gammaFactor := by
      funext z
      rw [he.gammaFactor_def, h1.gammaFactor_def]
    rw [hfun]
  · right
    have hfun :
      χ.gammaFactor = (1 : DirichletCharacter ℂ 1).gammaFactor ∘ (fun z : ℂ => z + 1) := by
      funext z
      rw [ho.gammaFactor_def, Function.comp_apply, h1.gammaFactor_def]
    rw [hfun,
      logDeriv_comp (g := fun z : ℂ => z + 1) (x := s)
        (analyticAt_gammaFactor_of_re_pos (1 : DirichletCharacter ℂ 1)
            (by
              simp only [Complex.add_re, Complex.one_re]; linarith only [hs])).differentiableAt
        (differentiableAt_id.add_const 1)]
    simp only [deriv_add_const, deriv_id'', mul_one]

/-- For a fixed positive real part, the gamma logarithmic derivatives of all characters
are uniformly bounded for heights of absolute value at most one. Reduce parity to the
modulus-one gamma factor at two real parts, and use continuity on the compact interval.
This supplies a modulus-independent bound near height zero. -/
theorem exists_uniform_norm_logDeriv_gammaFactor_compact_le {σ : ℝ} (hσ : 0 < σ) :
    ∃ M : ℝ,
      ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (t : ℝ),
        |t| ≤ 1 → ‖logDeriv χ.gammaFactor ((σ : ℂ) + Complex.I * t)‖ ≤ M := by
  obtain ⟨M0, hb0⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn
      (continuous_logDeriv_gammaFactor_vertical (1 : DirichletCharacter ℂ 1) hσ).continuousOn
  obtain ⟨M1, hb1⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn
      (continuous_logDeriv_gammaFactor_vertical (1 : DirichletCharacter ℂ 1) (σ := σ + 1)
          (by linarith only [hσ])).continuousOn
  refine ⟨max M0 M1, fun N χ t ht => ?_⟩
  have hs : 0 < ((σ : ℂ) + Complex.I * t).re := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] using hσ
  rcases logDeriv_gammaFactor_eq_one_or_one_shift χ hs with he | he
  · rw [he]
    exact (hb0 t (abs_le.mp ht)).trans (le_max_left M0 M1)
  · rw [he]
    have hh : (((σ + 1 : ℝ) : ℂ) + Complex.I * t) = ((σ : ℂ) + Complex.I * t) + 1 := by
      rw [Complex.ofReal_add, Complex.ofReal_one]
      ring
    rw [← hh]
    exact (hb1 t (abs_le.mp ht)).trans (le_max_right M0 M1)

/-- For a fixed real part in (0,2], a positive logarithmic growth constant works for every
modulus and character. Combine the uniform compact-height bound with the gamma strip
estimate outside that interval. This controls both the central Mellin line and reflected
right lines in the primitive functional equation. -/
theorem exists_uniform_norm_logDeriv_gammaFactor_vertical_le_log {σ : ℝ} (hσ : 0 < σ)
    (hσ' : σ ≤ 2) :
    ∃ A : ℝ,
      0 < A ∧
        ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (t : ℝ),
          ‖logDeriv χ.gammaFactor ((σ : ℂ) + Complex.I * t)‖ ≤ A * (Real.log (4 + |t|) + 1) := by
  obtain ⟨M, hM⟩ := exists_uniform_norm_logDeriv_gammaFactor_compact_le hσ
  let D : ℝ := ‖Complex.log (Real.pi : ℂ)‖ + Real.pi + Gamma.digammaLogErrorBound + 4
  let A : ℝ := 1 + |D| + max M 0
  have hA1 : 1 ≤ A := by
    dsimp only [A]; linarith only [abs_nonneg D, le_max_right M 0]
  have hDM : D ≤ |D| := le_abs_self D
  refine ⟨A, zero_lt_one.trans_le hA1, fun N χ t => ?_⟩
  have hL : 0 ≤ Real.log (4 + |t|) := Real.log_nonneg (by linarith only [abs_nonneg t])
  by_cases ht : 1 ≤ |t|
  · have hsr : |((σ : ℂ) + Complex.I * t).re| ≤ 2 := by
      simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, abs_of_pos hσ] using hσ'
    have hsi : 1 ≤ |((σ : ℂ) + Complex.I * t).im| := by
      simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, one_mul, zero_mul, zero_add] using ht
    have hb := norm_logDeriv_gammaFactor_le_log χ hsr hsi
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, one_mul, zero_mul, zero_add] at hb
    have hD : D ≤ A := by
      dsimp only [A]; linarith only [hDM, le_max_right M 0]
    change ‖logDeriv χ.gammaFactor ((σ : ℂ) + Complex.I * t)‖ ≤ A * _
    dsimp only [D] at hD
    nlinarith only [hb, hD, hA1, hL]
  · have htb : |t| ≤ 1 := (lt_of_not_ge ht).le
    have hm := hM N χ t htb
    have hMA : M ≤ A := by
      dsimp only [A]
      linarith only [le_max_left M 0, abs_nonneg D]
    nlinarith only [hm, hMA, hA1, hL]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
