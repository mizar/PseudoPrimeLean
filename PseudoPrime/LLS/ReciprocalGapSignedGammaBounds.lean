/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapScalarResolvent
public import PseudoPrime.Analysis.ClampedExponentialDifference

/-! # Decaying one-sided Gamma bounds for adjustable reciprocal witnesses -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For positive scale, express the compact profile using exp(-h*log(x)).
Apply the real-power logarithm formula. This exposes one-sided logarithmic differences. -/
theorem reciprocalGapProfile_eq_log_clamped {h x : ℝ} (hx : 0 < x) :
    reciprocalGapProfile h x = Real.sqrt x⁻¹ * max (1 - Real.exp (-h * Real.log x)) 0 / h := by
  have hp : x⁻¹ ^ h = Real.exp (-h * Real.log x) := by
    rw [Real.rpow_def_of_pos (inv_pos.mpr hx), Real.log_inv]
    congr 1
    ring
  rw [reciprocalGapProfile, hp]

/-- For h>0, x>=1 and r>=0, the difference between exp(-c*r) times the baseline profile
and the shifted density is at most sqrt(1/x)*r*exp(-c*r)/2.
Apply the clamped exponential drop and retain the increased square-root shift factor.
This is a signed estimate; no absolute value is taken. -/
theorem reciprocalGap_density_difference_le {h x : ℝ} (hh : 0 < h) (hx : 1 ≤ x) (c r : ℝ)
    (hr : 0 ≤ r) :
    Real.exp (-c * r) * reciprocalGapProfile h x - reciprocalGapResolventDensity h c x r ≤
      (Real.sqrt x⁻¹ / 2) * (r * Real.exp (-c * r)) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  let A := max (1 - Real.exp (-h * Real.log x)) 0
  let B := max (1 - Real.exp (-h * (Real.log x - r / 2))) 0
  let Q := (Real.sqrt x⁻¹ / h) * Real.exp (-c * r)
  have hQ : 0 ≤ Q := mul_nonneg (div_nonneg (Real.sqrt_nonneg _) hh.le) (Real.exp_pos _).le
  have hd : A - B ≤ h * (r / 2) :=
    Analysis.clamped_exponential_drop_le hh (Real.log_nonneg hx) (by linarith only [hr])
  have he : 1 ≤ Real.exp (r / 4) := Real.one_le_exp_iff.mpr (by linarith only [hr])
  have hB : B ≤ Real.exp (r / 4) * B := le_mul_of_one_le_left (le_max_right _ _) he
  have hpow : x⁻¹ ^ h * Real.exp (h * r / 2) = Real.exp (-h * (Real.log x - r / 2)) := by
    rw [Real.rpow_def_of_pos (inv_pos.mpr hx0), Real.log_inv, ← Real.exp_add]
    congr 1
    ring
  have hexp : Real.exp (-(c - 1 / 4) * r) = Real.exp (-c * r) * Real.exp (r / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [reciprocalGapProfile_eq_log_clamped hx0, reciprocalGapResolventDensity_eq_exp_clamped hx0,
    hpow, hexp]
  calc
    _ = Q * (A - Real.exp (r / 4) * B) := by
      dsimp only [Q, A, B]; ring
    _ ≤ Q * (A - B) := mul_le_mul_of_nonneg_left (sub_le_sub_left hB A) hQ
    _ ≤ Q * (h * (r / 2)) := mul_le_mul_of_nonneg_left hd hQ
    _ = _ := by
      dsimp only [Q]; field_simp [hh.ne']

/-- For positive gap and coordinate and scale at least one, the signed scalar resolvent
difference is at most sqrt(1/x)/(2*c^2). Integrate the one-sided density estimate,
using the zeroth and first exponential moments. This gives a summable Gamma-series bound. -/
theorem reciprocalGap_scalar_difference_le_inv_square {h c x : ℝ} (hh : 0 < h) (hc : 0 < c)
    (hx : 1 ≤ x) :
    reciprocalGapProfile h x / c - (∫ r : ℝ in Set.Ioi 0, reciprocalGapResolventDensity h c x r) ≤
      Real.sqrt x⁻¹ / (2 * c ^ 2) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hE := integrableOn_exp_mul_Ioi (neg_neg_of_pos hc) (0 : ℝ)
  have hM :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := c) (by norm_num only)
      (by norm_num only) hc
  simp only [Real.rpow_one] at hM
  have hD := integrableOn_reciprocalGapResolventDensity hh hc hx0
  have hΓ : Real.Gamma 2 = 1 := by
    have h := Real.Gamma_nat_eq_factorial 1
    norm_num only at h
    exact h
  have hIM := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := c) (by norm_num only) hc
  norm_num only [Real.rpow_one, Real.rpow_two, hΓ] at hIM
  have hIE := integral_exp_mul_Ioi (neg_neg_of_pos hc) (0 : ℝ)
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq] at hIE
  have hi :=
    MeasureTheory.setIntegral_mono_on ((hE.mul_const (reciprocalGapProfile h x)).sub hD)
      (hM.const_mul (Real.sqrt x⁻¹ / 2)) measurableSet_Ioi
      (fun r hr ↦ reciprocalGap_density_difference_le hh hx c r hr.le)
  simp only [Pi.sub_apply] at hi
  simp only [← neg_mul, mul_one] at hIM
  rw [MeasureTheory.integral_sub (hE.mul_const _) hD, MeasureTheory.integral_mul_const,
    MeasureTheory.integral_const_mul, hIE, hIM] at hi
  convert hi using 1 <;> ring

/-- The one-sided real Gamma budget is (9/2)*sqrt(1/x)-(3/4)*k_h(x).
For positive gap and scale at least one it bounds the Gamma integral uniformly in character.
The negative compact-profile contribution is retained for finite-scale witness comparisons. -/
noncomputable def reciprocalGapSignedGammaBudget (h x : ℝ) : ℝ :=
  (9 / 2 : ℝ) * Real.sqrt x⁻¹ - (3 / 4 : ℝ) * reciprocalGapProfile h x

/-- For all characters, h>0 and x>=1, the real central Gamma integral is bounded above by
the signed Gamma budget. Compare each scalar term with sqrt(1/x)/(2*(b+n)^2), sum the
inverse-square bound eighteen and use the negative baseline coefficient at most -3/4.
This improves the previous constant real upper bound without asserting a norm bound. -/
theorem reciprocalGap_gamma_re_le_signed_budget {h x : ℝ} (hh : 0 < h) (hx : 1 ≤ x) {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * reciprocalGapCentralWeight h x t)).re ≤
      reciprocalGapSignedGammaBudget h x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  obtain ⟨b, hb, hb1, hseries⟩ := reciprocalGap_central_gammaIntegral_re_eq_scalar_series χ
  have hb0 : 0 < b := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1 / 4) hb
  let F := fun n : ℕ ↦
    reciprocalGapProfile h x / (b + n) -
      ∫ r : ℝ in Set.Ioi 0, reciprocalGapResolventDensity h (b + n) x r
  let U := fun n : ℕ ↦ (Real.sqrt x⁻¹ / 2) * ((b + n) ^ 2)⁻¹
  have hsF : Summable F := summable_reciprocalGap_scalar_resolvent_difference hh hb0 hx0
  have hsU : Summable U := (Analysis.summable_shifted_inverse_squares hb0).mul_left _
  have hterm (n : ℕ) : F n ≤ U n := by
    have h :=
      reciprocalGap_scalar_difference_le_inv_square hh
        (add_pos_of_pos_of_nonneg hb0 (Nat.cast_nonneg n)) hx
    dsimp only [F, U]
    exact
      h.trans_eq
        (by
          simp only [div_eq_mul_inv, mul_inv_rev]; ring)
  have hsum := hsF.tsum_le_tsum hterm hsU
  dsimp only [U] at hsum
  rw [tsum_mul_left] at hsum
  have hI :=
    mul_le_mul_of_nonneg_left (Analysis.shifted_inverse_square_sum_le_eighteen hb)
      (div_nonneg (Real.sqrt_nonneg x⁻¹) (by norm_num only : (0 : ℝ) ≤ 2))
  have hβ : ((-Complex.log Real.pi + Complex.digamma (b : ℂ)) / 2).re ≤ -3 / 4 := by
    rw [Complex.div_ofNat_re, Complex.add_re, Complex.neg_re, ← Complex.ofReal_log Real.pi_pos.le,
      Complex.ofReal_re]
    exact gamma_real_baseline_le_neg_three_quarters hb0 hb1
  have hm := mul_le_mul_of_nonneg_right hβ (reciprocalGapProfile_nonneg hh x)
  rw [hseries hh hx0]
  change _ ≤ (9 / 2 : ℝ) * Real.sqrt x⁻¹ - (3 / 4 : ℝ) * reciprocalGapProfile h x
  dsimp only [F] at hsum
  linarith only [hsum, hI, hm]

/-- For nonzero level, positive gap and scale at least one, the real completed remainder
minus pole and left contributions is bounded by the signed Gamma budget.
Use its exact central-Gamma identity. This connects the signed estimate to the contour formula. -/
theorem reciprocalGap_remainder_gamma_re_le_signed_budget {h x : ℝ} (hh : 0 < h) (hx : 1 ≤ x)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (reciprocalGapCompletedRemainder h hh χ x -
          MellinKernel.weightedResidue (reciprocalGapMellinKernel h hh)
            (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2) -
          reciprocalGapLeftIntegral h hh χ x).re ≤
      reciprocalGapSignedGammaBudget h x := by
  rw [reciprocalGap_remainder_sub_pole_left_eq_central_gamma hh χ hx]
  exact reciprocalGap_gamma_re_le_signed_budget hh hx χ

/-- For positive h with 6*h<=1-(1/x)^h, the signed Gamma budget is nonpositive.
The scale condition makes the compact profile at least 6*sqrt(1/x).
This gives an explicit sufficient condition for discarding the archimedean contribution. -/
theorem reciprocalGapSignedGammaBudget_nonpos {h x : ℝ} (hh : 0 < h)
    (hscale : 6 * h ≤ 1 - x⁻¹ ^ h) : reciprocalGapSignedGammaBudget h x ≤ 0 := by
  have hm := mul_le_mul_of_nonneg_left hscale (Real.sqrt_nonneg x⁻¹)
  have hk : 6 * Real.sqrt x⁻¹ ≤ reciprocalGapProfile h x := by
    rw [reciprocalGapProfile, max_eq_left (by linarith only [hscale, hh])]
    apply (le_div_iff₀ hh).mpr
    nlinarith only [hm]
  unfold reciprocalGapSignedGammaBudget
  linarith only [hk]

/-- For any character, h>0, x>=1 and 6*h<=1-(1/x)^h, the central Gamma integral has
nonpositive real part. Combine the signed budget and its explicit scale condition.
No GRH, primitivity or character nontriviality is required. -/
theorem reciprocalGap_gamma_re_nonpos_of_scale {h x : ℝ} (hh : 0 < h) (hx : 1 ≤ x)
    (hscale : 6 * h ≤ 1 - x⁻¹ ^ h) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * reciprocalGapCentralWeight h x t)).re ≤
      0 := by
  exact
    (reciprocalGap_gamma_re_le_signed_budget hh hx χ).trans
      (reciprocalGapSignedGammaBudget_nonpos hh hscale)

/-- For primitive nonprincipal GRH data with nonprincipal inverse and level at least eight,
bound the real completed remainder by the pole budget, numerical left budget and signed
Gamma budget at scales at least one. Use one-sided real bounds for all three components.
The negative Gamma saving remains in the actual witness remainder. -/
theorem reciprocalGap_remainder_re_le_signed_budget {h : ℝ} (hh : 0 < h) {q : ℕ} [NeZero q]
    (hq : 8 ≤ q) {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    (reciprocalGapCompletedRemainder h hh χ x).re ≤
      ((7 / 6 : ℝ) * Real.log q + 4) / (h * Real.sqrt x) + reciprocalGapNumericLeftBudget h hh q x +
        reciprocalGapSignedGammaBudget h x := by
  let P :=
    MellinKernel.weightedResidue (reciprocalGapMellinKernel h hh)
      (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2)
  let L := reciprocalGapLeftIntegral h hh χ x
  let R := reciprocalGapCompletedRemainder h hh χ x
  have hΓ : (R - P - L).re ≤ reciprocalGapSignedGammaBudget h x :=
    reciprocalGap_remainder_gamma_re_le_signed_budget hh hx χ
  have hP :=
    (Complex.re_le_norm P).trans
      (reciprocalGap_poleResidue_norm_le hh hq hp hne hGRH (zero_lt_one.trans_le hx))
  have hq1 : 1 ≤ q := (by norm_num only : 1 ≤ 8).trans hq
  have hL :=
    (Complex.re_le_norm L).trans
      ((reciprocalGap_leftIntegral_norm_le hh hq1 hp hne hinv (zero_lt_one.trans_le hx)).trans
        (reciprocalGapLeftBudget_le_numeric hh hq1 (zero_lt_one.trans_le hx)))
  simp only [Complex.sub_re] at hΓ
  change R.re ≤ _
  linarith only [hΓ, hP, hL]

/-- For primitive nonprincipal GRH data at level at least eight, separation using the zero
prefix, explicit pole and left budgets and the signed Gamma budget yields a prime
non-one witness below the scale. Apply exact prime separation with the real remainder bound.
This replaces the constant 176 in the earlier criterion; a new global cutoff is not assumed. -/
theorem exists_prime_not_one_of_reciprocalGap_signed_separation {h c : ℝ} (hh : 0 < h) {q : ℕ}
    [NeZero q] (hq : 8 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hc : (1 / 2 : ℝ) < c) (hbound : c ^ 2 ≤ 1 / 4 + h / 2) {x : ℝ}
    (hx : 1 ≤ x) (B : Finset ℕ)
    (hgap :
      (1 / c) *
            (Real.log q / 2 + (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + c) : ℂ)).re +
                (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) -
              ∑ n ∈ B, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) +
          (((7 / 6 : ℝ) * Real.log q + 4) / (h * Real.sqrt x) +
            reciprocalGapNumericLeftBudget h hh q x +
            reciprocalGapSignedGammaBudget h x) <
        (reciprocalGapCharacterSum h (1 : DirichletCharacter ℂ 1) x).re) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  apply
    exists_prime_not_one_of_reciprocalGap_separation hh ((by norm_num only : 2 ≤ 8).trans hq) hGRH
      hp hne hinv hc hbound hx B
  have hr := reciprocalGap_remainder_re_le_signed_budget hh hq hp hne hinv hGRH hx
  exact (add_le_add (le_refl _) hr).trans_lt hgap

end PseudoPrime.LLS.PaperStatements
