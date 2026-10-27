/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.TriangularDigammaCorrection
public import PseudoPrime.LLS.TriangularArchimedeanBounds
public import PseudoPrime.LLS.TriangularSignedZeroMass
public import PseudoPrime.LLS.TriangularScaledGammaBounds
public import PseudoPrime.LLS.TriangularFamilyZeroMass

/-! # Signed central Gamma bound for the alpha-18 triangular kernel

Retain the negative real-axis baseline and add the positive vertical correction.
The normalized real Gamma integral is at most minus eighteen for every character.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For positive b at most one, the real Gamma baseline is at most minus three quarters.
Use monotonicity of the real digamma value, its value at one, and log pi greater than one.
This supplies the negative constant retained in the signed integral bound. -/
theorem gamma_real_baseline_le_neg_three_quarters {b : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1) :
    (-Real.log Real.pi + (Complex.digamma (b : ℂ)).re) / 2 ≤ -3 / 4 := by
  have hd := AnalyticNumberTheory.Gamma.re_digamma_mono_of_pos hb0 hb1
  norm_num only [Complex.ofReal_one, Complex.digamma_one, Complex.neg_re, Complex.ofReal_re] at hd
  have hl := Real.log_le_log (Real.exp_pos 1) (Real.exp_one_lt_three.trans Real.pi_gt_three).le
  rw [Real.log_exp] at hl
  linarith only [hd, hl, Real.one_half_lt_eulerMascheroniConstant]

/-- For a complex number, division by two divides its real part by two.
Expand complex division and the real and imaginary parts of the denominator.
This supports the parity conversion of the central Gamma factor. -/
theorem complex_div_two_re (z : ℂ) : (z / 2).re = z.re / 2 := by
  norm_num only [Complex.div_re, show (2 : ℂ).re = (2 : ℝ) from rfl,
    show (2 : ℂ).im = (0 : ℝ) from rfl, Complex.normSq_ofNat, mul_zero, zero_div, add_zero]
  ring

open AnalyticNumberTheory.DirichletLFunction in
/-- For every Dirichlet character, a central Gamma argument b lies between one quarter and one.
The real logarithmic derivative equals half the digamma value minus log pi.
Split even and odd parity; positivity of the argument excludes Gamma poles.
This converts the Gamma factor into the positive vertical correction interface. -/
theorem gamma_central_re_eq_digamma {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ∃ b : ℝ,
      1 / 4 ≤ b ∧
        b ≤ 1 ∧
        ∀ t : ℝ,
          (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2)).re =
            (-Real.log Real.pi + (Complex.digamma ((b : ℂ) + Complex.I * (t / 2))).re) / 2 := by
  rcases χ.even_or_odd with hχ | hχ
  · refine ⟨1 / 4, le_refl _, by norm_num only, ?_⟩
    intro t
    have hz : (Complex.I * (t : ℂ) + 1 / 2) / 2 = ((1 / 4 : ℝ) : ℂ) + Complex.I * (t / 2) := by
      norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one]
      ring
    have hp : 0 < ((Complex.I * (t : ℂ) + 1 / 2) / 2).re := by
      simp only [complex_div_two_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
      norm_num only [Complex.one_re]
    have he :=
      logDeriv_gammaFactor_eq_of_even_of_half_ne_neg_nat hχ
        (fun n ↦ AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos hp n)
    rw [he, hz, ← Complex.ofReal_log Real.pi_pos.le]
    simp only [Complex.add_re, complex_div_two_re, Complex.neg_re, Complex.ofReal_re]
    ring
  · refine ⟨3 / 4, by norm_num only, by norm_num only, ?_⟩
    intro t
    have hz :
      ((Complex.I * (t : ℂ) + 1 / 2) + 1) / 2 = ((3 / 4 : ℝ) : ℂ) + Complex.I * (t / 2) := by
      norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one]
      ring
    have hp : 0 < (((Complex.I * (t : ℂ) + 1 / 2) + 1) / 2).re := by
      simp only [complex_div_two_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
      norm_num only [Complex.one_re]
    have he :=
      logDeriv_gammaFactor_eq_of_odd_of_half_ne_neg_nat hχ
        (fun n ↦ AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos hp n)
    rw [he, hz, ← Complex.ofReal_log Real.pi_pos.le]
    simp only [Complex.add_re, complex_div_two_re, Complex.neg_re, Complex.ofReal_re]
    ring

/-- For every character, the real alpha-18 central Gamma integrand is integrable.
Specialize the general vertical integrability theorem to line zero and scale one.
This permits real integral splitting without an additional convergence premise. -/
theorem triangular18_central_gamma_re_integrable {q : ℕ} (χ : DirichletCharacter ℂ q) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
            Analysis.triangularMellinFunction 18 (Complex.I * t)).re) := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have h :=
    MellinKernel.integrable_gammaFactor_power_line K χ (c := 0) (x := 1) (by norm_num only)
      (by
        change (0 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) zero_lt_one
  simp only [Complex.ofReal_zero, zero_add, Complex.ofReal_one, Complex.one_cpow, mul_one] at h
  exact Complex.reCLM.integrable_comp h

/-- For every character, the normalized real alpha-18 central Gamma integral
is at most minus eighteen.
Split it into its real-axis baseline and positive vertical correction.
The baseline is at most minus three quarters, the kernel mass is thirty-six,
and the correction is at most nine. No GRH assumption is needed.
This supplies the signed Gamma contribution in the absolute zero-mass formula. -/
theorem triangular18_central_gamma_re_integral_le_neg_eighteen {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    (∫ t : ℝ,
          (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
              Analysis.triangularMellinFunction 18 (Complex.I * t)).re) /
        (2 * Real.pi) ≤
      -18 := by
  obtain ⟨b, hb, hb1, he⟩ := gamma_central_re_eq_digamma χ
  let w := fun t : ℝ ↦ ‖Analysis.triangularMellinFunction 18 (Complex.I * t)‖
  let B := (-Real.log Real.pi + (Complex.digamma (b : ℂ)).re) / 2
  let C := fun t : ℝ ↦
    (1 / 2 : ℝ) *
      ((Complex.digamma ((b : ℂ) + Complex.I * (t / 2))).re - (Complex.digamma (b : ℂ)).re) *
      w t
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have hw : MeasureTheory.Integrable w := by
    have h :=
      MellinKernel.integrable_line_in_strip K (c := 0)
        (by
          change (-1 / 2 - 1 / 8 : ℝ) < 0; norm_num only)
        (by
          change (0 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
        (by norm_num only)
    simp only [Complex.ofReal_zero, zero_add] at h
    exact h.norm
  have hid (t : ℝ) :
    (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
          Analysis.triangularMellinFunction 18 (Complex.I * t)).re =
      B * w t + C t := by
    rw [Analysis.triangularMellinFunction_imaginary (by norm_num only : (18 : ℝ) ≠ 0)]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [he]
    dsimp only [B, C, w]
    rw [Analysis.norm_triangularMellinFunction_imaginary (by norm_num only : (18 : ℝ) ≠ 0)]
    ring
  have hr := triangular18_central_gamma_re_integrable χ
  have hc : MeasureTheory.Integrable C := by
    have h := hr.sub (hw.const_mul B)
    convert h using 1
    funext t
    change
      C t =
        (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
              Analysis.triangularMellinFunction 18 (Complex.I * t)).re -
          B * w t
    rw [hid]
    ring
  have hm : (∫ t : ℝ, w t) / (2 * Real.pi) = 36 := by
    have h := triangular_mass_of_function K (by norm_num only : (0 : ℝ) < 18) rfl
    norm_num only at h
    exact h
  have hi :
    (∫ t : ℝ,
        (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
            Analysis.triangularMellinFunction 18 (Complex.I * t)).re) =
      B * (∫ t : ℝ, w t) + ∫ t : ℝ, C t := by
    rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hid),
      MeasureTheory.integral_add (hw.const_mul B) hc, MeasureTheory.integral_const_mul]
  have hB :=
    gamma_real_baseline_le_neg_three_quarters
      (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1 / 4) hb) hb1
  have hC :=
    Analysis.triangular_digamma_correction_integral_le_nine (by norm_num only : (18 : ℝ) ≠ 0) hb
  rw [hi, add_div, mul_div_assoc, hm]
  change B * 36 + (∫ t : ℝ, C t) / (2 * Real.pi) ≤ -18
  change B ≤ -3 / 4 at hB
  change (∫ t : ℝ, C t) / (2 * Real.pi) ≤ 9 at hC
  linarith only [hB, hC]

/-- For every character and line between zero and five eighths, the normalized
scale-one Gamma integral has real part at most minus eighteen.
Shift to the central line and commute real part with the integrable complex integral.
This supplies the negative Gamma contribution in the right-line zero-mass formula. -/
theorem triangular18_gammaIntegral_re_le_neg_eighteen {q : ℕ} (χ : DirichletCharacter ℂ q) {b : ℝ}
    (hb : 0 ≤ b) (hbK : b ≤ 5 / 8) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor (((b : ℂ) + Complex.I * t) + 1 / 2) *
              K.function ((b : ℂ) + Complex.I * t))).re ≤
      -18 := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have he :=
    MellinKernel.gammaIntegral_eq_central K χ (x := 1) hb
      (by
        change b ≤ 1 / 2 + 1 / 8; linarith only [hbK])
      (by linarith only [hbK]) le_rfl
  simp only [Complex.ofReal_one, Complex.one_cpow, mul_one] at he
  change (((1 / (2 * Real.pi) : ℝ) : ℂ) * _).re ≤ -18
  rw [he]
  have hi :=
    MellinKernel.integrable_gammaFactor_power_line K χ (c := 0) (x := 1) (by norm_num only)
      (by
        change (0 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) zero_lt_one
  simp only [Complex.ofReal_zero, zero_add, Complex.ofReal_one, Complex.one_cpow, mul_one] at hi
  have hr := Complex.reCLM.integral_comp_comm hi
  change
    (∫ t : ℝ, (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * K.function (Complex.I * t)).re) =
      (∫ t : ℝ,
          logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * K.function (Complex.I * t)).re at hr
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [← hr]
  have h := triangular18_central_gamma_re_integral_le_neg_eighteen χ
  change (1 / (2 * Real.pi)) * _ ≤ -18
  rw [one_div_mul_eq_div]
  exact h

/-- For primitive nonprincipal GRH data of modulus at least two with nonprincipal inverse,
the absolute zero mass is bounded by the conductor term minus both arithmetic real parts
and thirty-six. Apply the exact signed formula and the negative scale-one Gamma bound
for the character and its inverse. This retains arithmetic cancellation across families. -/
theorem triangular18_absoluteMass_le_signed_arithmetic_sub_thirty_six {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) ≤
      36 * Real.log q - (∑' n : ℕ, K.summand χ 1 n).re - (∑' n : ℕ, K.summand χ⁻¹ 1 n).re - 36 := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let G := fun ψ : DirichletCharacter ℂ q ↦
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        logDeriv ψ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
          K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t))
  have hg (ψ : DirichletCharacter ℂ q) : (G ψ).re ≤ -18 :=
    triangular18_gammaIntegral_re_le_neg_eighteen ψ (b := 9 / 16) (by norm_num only)
      (by norm_num only)
  have he := triangular18_absoluteMass_signed_formula hq hGRH hp hne hinv
  change
    (∑' n : ℕ, K.summand χ 1 n) + (∑' n : ℕ, K.summand χ⁻¹ 1 n) +
        ((∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖ : ℝ) : ℂ) =
      36 * Complex.log q + G χ + G χ⁻¹ at he
  rw [← Complex.natCast_log, ← Complex.ofReal_ofNat 36, ← Complex.ofReal_mul] at he
  have hr := congrArg Complex.re he
  simp only [Complex.add_re, Complex.ofReal_re] at hr
  change (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) ≤ _
  linarith only [hr, hg χ, hg χ⁻¹]

/-- For primitive nonprincipal GRH data and scale at least one, bound the arithmetic norm
by the conductor term, both negative scale-one arithmetic real parts, and the remainder.
The fixed cost is 5964: combine the signed zero mass contribution minus thirty-six
with the existing scale-dependent Gamma norm cost 6000. This is an intermediate
bound; the scale-dependent Gamma integral is still estimated by its norm. -/
theorem triangular18_primitive_arithmetic_norm_le_signed_sharp {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    ‖∑' n : ℕ, K.summand χ x n‖ ≤
      36 * Real.log q - (∑' n : ℕ, K.summand χ 1 n).re - (∑' n : ℕ, K.summand χ⁻¹ 1 n).re + 5964 +
        4000000000000 * (Real.log q + 284) * x ^ (-9 / 16 : ℝ) := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let S := ∑' n : ℕ, K.summand χ x n
  let Z := ∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ
  have hR := triangular18_primitive_remainder_norm_le_scaled_gamma hq hGRH hp hne hinv hx
  have hs :=
    MellinKernel.summable_oscillatingZeroTerm K hq hGRH hp hne hinv (zero_lt_one.trans_le hx)
  have hZ : ‖Z‖ ≤ ∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖ := by
    have ht := norm_tsum_le_tsum_norm hs.norm
    have he : (∑' ρ : ℂ, ‖K.oscillatingZeroTerm χ x ρ‖) = ∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖ :=
      tsum_congr (MellinKernel.norm_oscillatingZeroTerm K χ (zero_lt_one.trans_le hx))
    exact ht.trans_eq he
  have hM := triangular18_absoluteMass_le_signed_arithmetic_sub_thirty_six hq hGRH hp hne hinv
  have ht := norm_sub_le (S + Z) Z
  have he : (S + Z) - Z = S := by ring
  rw [he] at ht
  change ‖S‖ ≤ _
  linarith only [ht, hR, hZ, hM]

/-- Under GRH and containment of eligible primes through X, the finite principal sum
is bounded by primitive annihilator budgets with fixed cost 5964 per nonprincipal member.
Apply the sharp primitive arithmetic norm bound after the signed primitivization comparison.
This passes the negative scale-one Gamma contribution to the subgroup average. -/
theorem triangular18_principal_sum_le_signed_sharp_budgets_of_noSmallPrimes {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x X : ℝ} (hx : 1 ≤ x)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) :
    letI := Classical.propDecidable
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    (H.index : ℝ) * (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ q) x n).re) ≤
      ∑ χ : NumberTheory.subgroupAnnihilator H,
        if χ.val = 1 then (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x n).re
        else
          36 * Real.log χ.val.conductor - (∑' n : ℕ, K.summand χ.val.primitiveCharacter 1 n).re -
              (∑' n : ℕ, K.summand (χ.val.primitiveCharacter)⁻¹ 1 n).re +
            5964 +
            4000000000000 * (Real.log χ.val.conductor + 284) * x ^ (-9 / 16 : ℝ) := by
  classical
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have hc :=
    MellinKernel.principal_sum_le_primitive_average_of_noSmallPrimes K H (zero_lt_one.trans_le hx)
      hsmall
  apply hc.trans
  apply Finset.sum_le_sum
  intro χ _
  by_cases hn : χ.val = 1
  · rw [ite_eq_left hn, hn, tsum_congr (MellinKernel.principal_primitive_summand_eq_level_one K x)]
  · rw [ite_eq_right hn]
    let : NeZero χ.val.conductor := ⟨χ.val.conductor_ne_zero⟩
    have hp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ.val hn
    have hq := NumberTheory.three_le_conductor_of_ne_one χ.val hn
    have hb :=
      triangular18_primitive_arithmetic_norm_le_signed_sharp ((by norm_num only : 2 ≤ 3).trans hq)
        hGRH (DirichletCharacter.primitiveCharacter_isPrimitive χ.val) hp (inv_ne_one.mpr hp) hx
    exact (Complex.re_le_norm _).trans hb

end PseudoPrime.LLS.PaperStatements
