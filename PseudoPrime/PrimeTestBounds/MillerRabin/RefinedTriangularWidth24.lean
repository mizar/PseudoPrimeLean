/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.TriangularDualScaleGeneral
public import PseudoPrime.LLS.PaperStatements.TriangularCreditedInterior
public import PseudoPrime.LLS.PaperStatements.TriangularJointSharp
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleLargeIndexScalar

/-! # Width-24 triangular dual-scale input for the refined bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, the primitive nonprincipal width-24 triangular kernel satisfies
the exact signed dual-scale formula with explicit Gamma weight series. Apply
the parameterized identity at width 24; this is the starting point for the
large-index comparison in the refined witness bound. -/
theorem refined_triangular24_dual_formula {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    ∃ β γ : ℝ,
      1 / 4 ≤ β ∧
        β ≤ 1 ∧
          1 / 4 ≤ γ ∧
            γ ≤ 1 ∧
              let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
              (∑' n : ℕ, K.summand χ x n) + (∑' n : ℕ, K.summand χ⁻¹ x⁻¹ n) +
                  (∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ) =
                Complex.log q * (LLS.PaperStatements.triangularKernelProfile 24 x : ℂ) +
                  (((-Complex.log Real.pi + Complex.digamma (β : ℂ)) / 2) *
                      (LLS.PaperStatements.triangularKernelProfile 24 x : ℂ) +
                    (1 / 2 : ℂ) *
                      ∑' n : ℕ, LLS.PaperStatements.triangularGammaReciprocalTerm 24 (β + n) x) +
                  (((-Complex.log Real.pi + Complex.digamma (γ : ℂ)) / 2) *
                      (LLS.PaperStatements.triangularKernelProfile 24 x⁻¹ : ℂ) +
                    (1 / 2 : ℂ) *
                      ∑' n : ℕ,
                        LLS.PaperStatements.triangularGammaReciprocalTerm 24 (γ + n) x⁻¹) := by
  exact
    LLS.PaperStatements.triangular_dual_weightSeries_GRH (a := 24) (by norm_num only) hq hGRH hp hne
      hinv hx

/-- For the width-24 kernel, the primitive scale-one character average retains
twice the finite level-one sum when every prime through the cutoff is coprime
to the modulus and lies in the subgroup. The general Mellin-kernel credit theorem
supplies this arithmetic input to the large-index comparison. -/
theorem refined_triangular24_scaleOne_credit {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) {X : ℝ}
    (hX : 0 ≤ X) (hlarge : ∀ p : ℕ, p.Prime → p ∣ q → X < (p : ℝ))
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → NumberTheory.residueInSubgroup q H p) :
    letI := Classical.propDecidable
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
    (2 : ℝ) * (H.index : ℝ) *
          (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) 1 n).re) -
        2 * (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) 1 n).re ≤
      ∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H),
        ((∑' n : ℕ, K.summand χ.val.primitiveCharacter 1 n).re +
          (∑' n : ℕ, K.summand (χ.val.primitiveCharacter)⁻¹ 1 n).re) := by
  exact
    LLS.PaperStatements.MellinKernel.scaleOne_pair_lower
      (LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)) H hX hlarge
      hsmall

/-- For a subgroup under GRH, the nonprincipal annihilator characters satisfy
the exact width-24 dual-scale formula. Their primitive conductors meet the
nonprincipal hypotheses, and the family identity keeps both arithmetic scales
and Gamma terms available for the large-index comparison. -/
theorem refined_triangular24_family {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    letI := Classical.propDecidable
    letI : ∀ i : NumberTheory.subgroupAnnihilator H, NeZero i.val.conductor := fun i ↦
      ⟨i.val.conductor_ne_zero⟩
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
    let G :=
      fun (i : NumberTheory.subgroupAnnihilator H) (ψ : DirichletCharacter ℂ (i.val.conductor))
        (y : ℝ) ↦
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv ψ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
            (K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (y : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t)))
    let S := Finset.univ.filter (fun i : NumberTheory.subgroupAnnihilator H ↦ i.val ≠ 1)
    (∑ i ∈ S,
        ((∑' n : ℕ, K.summand (i.val.primitiveCharacter) x n) +
            (∑' n : ℕ, K.summand (i.val.primitiveCharacter)⁻¹ x⁻¹ n) +
            (∑' ρ : ℂ, K.oscillatingZeroTerm (i.val.primitiveCharacter) x ρ)).re) =
      LLS.PaperStatements.triangularKernelProfile 24 x * (∑ i ∈ S, Real.log (i.val.conductor)) +
        ∑ i ∈ S, (G i (i.val.primitiveCharacter) x + G i (i.val.primitiveCharacter)⁻¹ x⁻¹).re := by
  classical
  let _ := Classical.propDecidable
  let A := NumberTheory.subgroupAnnihilator H
  let f := fun χ : A ↦ χ.val.conductor
  let : ∀ χ : A, NeZero (f χ) := fun χ ↦ ⟨χ.val.conductor_ne_zero⟩
  let S := Finset.univ.filter (fun χ : A ↦ χ.val ≠ 1)
  have hn (χ : A) (hχ : χ ∈ S) : χ.val ≠ 1 := (Finset.mem_filter.mp hχ).2
  have hp (χ : A) (hχ : χ ∈ S) : χ.val.primitiveCharacter ≠ 1 :=
    AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ.val (hn χ hχ)
  exact
    LLS.PaperStatements.triangular_dual_signed_family (a := 24) (by norm_num only) S f
      (fun χ ↦ χ.val.primitiveCharacter) hGRH
      (fun χ hχ ↦
        (by norm_num only : 2 ≤ 3).trans
          (NumberTheory.three_le_conductor_of_ne_one χ.val (hn χ hχ)))
      (fun χ _ ↦ DirichletCharacter.primitiveCharacter_isPrimitive χ.val) hp
      (fun χ hχ ↦ inv_ne_one.mpr (hp χ hχ)) hx

/-- For every Dirichlet character, the real central Gamma integrand of the
width-24 triangular kernel is integrable. Specialize the general admissible-kernel
line integrability theorem at scale one; this permits the signed Gamma estimate. -/
theorem refined_24_gamma_re_integrable {q : ℕ} (χ : DirichletCharacter ℂ q) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
            Analysis.triangularMellinFunction 24 (Complex.I * t)).re) := by
  let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
  have h :=
    LLS.PaperStatements.MellinKernel.integrable_gammaFactor_power_line K χ (c := 0) (x := 1)
      (by norm_num only)
      (by
        change (0 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) zero_lt_one
  simp only [Complex.ofReal_zero, zero_add, Complex.ofReal_one, Complex.one_cpow, mul_one] at h
  exact Complex.reCLM.integrable_comp h

/-- For every Dirichlet character, the normalized width-24 central Gamma
integral has real part at most minus 27. Its real-axis baseline is at most
minus three quarters, the kernel mass is 48, and the vertical correction is
at most nine. This gives the signed scale-one zero-mass budget. -/
theorem refined_24_gamma_re_le_neg27 {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (∫ t : ℝ,
          (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
              Analysis.triangularMellinFunction 24 (Complex.I * t)).re) /
        (2 * Real.pi) ≤
      -27 := by
  obtain ⟨b, hb, hb1, he⟩ := LLS.PaperStatements.gamma_central_re_eq_digamma χ
  let w := fun t : ℝ ↦ ‖Analysis.triangularMellinFunction 24 (Complex.I * t)‖
  let B := (-Real.log Real.pi + (Complex.digamma (b : ℂ)).re) / 2
  let C := fun t : ℝ ↦
    (1 / 2 : ℝ) *
      ((Complex.digamma ((b : ℂ) + Complex.I * (t / 2))).re - (Complex.digamma (b : ℂ)).re) *
      w t
  let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
  have hw : MeasureTheory.Integrable w := by
    have h :=
      LLS.PaperStatements.MellinKernel.integrable_line_in_strip K (c := 0)
        (by
          change (-1 / 2 - 1 / 8 : ℝ) < 0; norm_num only)
        (by
          change (0 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
        (by norm_num only)
    simp only [Complex.ofReal_zero, zero_add] at h
    exact h.norm
  have hid (t : ℝ) :
    (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
          Analysis.triangularMellinFunction 24 (Complex.I * t)).re =
      B * w t + C t := by
    rw [Analysis.triangularMellinFunction_imaginary (by norm_num only : (24 : ℝ) ≠ 0)]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [he]
    dsimp only [B, C, w]
    rw [Analysis.norm_triangularMellinFunction_imaginary (by norm_num only : (24 : ℝ) ≠ 0)]
    ring
  have hr := refined_24_gamma_re_integrable χ
  have hc : MeasureTheory.Integrable C := by
    have h := hr.sub (hw.const_mul B)
    convert h using 1
    funext t
    change
      C t =
        (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
              Analysis.triangularMellinFunction 24 (Complex.I * t)).re -
          B * w t
    rw [hid]
    ring
  have hm : (∫ t : ℝ, w t) / (2 * Real.pi) = 48 := by
    have h :=
      LLS.PaperStatements.triangular_mass_of_function K (by norm_num only : (0 : ℝ) < 24) rfl
    norm_num only at h
    exact h
  have hi :
    (∫ t : ℝ,
        (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
            Analysis.triangularMellinFunction 24 (Complex.I * t)).re) =
      B * (∫ t : ℝ, w t) + ∫ t : ℝ, C t := by
    rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hid),
      MeasureTheory.integral_add (hw.const_mul B) hc, MeasureTheory.integral_const_mul]
  have hB :=
    LLS.PaperStatements.gamma_real_baseline_le_neg_three_quarters
      (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1 / 4) hb) hb1
  have hC :=
    Analysis.triangular_digamma_correction_integral_le_nine (by norm_num only : (24 : ℝ) ≠ 0) hb
  rw [hi, add_div, mul_div_assoc, hm]
  change B * 48 + (∫ t : ℝ, C t) / (2 * Real.pi) ≤ -27
  change B ≤ -3 / 4 at hB
  change (∫ t : ℝ, C t) / (2 * Real.pi) ≤ 9 at hC
  linarith only [hB, hC]

/-- At scale one, the width-24 Gamma integral on any right line between zero
and five eighths has real part at most minus 27. Shift to the central line and
apply the certified negative central bound. -/
theorem refined_24_gamma_line_le_neg27 {q : ℕ} (χ : DirichletCharacter ℂ q) {b : ℝ} (hb : 0 ≤ b)
    (hbK : b ≤ 5 / 8) :
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor (((b : ℂ) + Complex.I * t) + 1 / 2) *
              K.function ((b : ℂ) + Complex.I * t))).re ≤
      -27 := by
  let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
  have he :=
    LLS.PaperStatements.MellinKernel.gammaIntegral_eq_central K χ (x := 1) hb
      (by
        change b ≤ 1 / 2 + 1 / 8; linarith only [hbK])
      (by linarith only [hbK]) le_rfl
  simp only [Complex.ofReal_one, Complex.one_cpow, mul_one] at he
  change (((1 / (2 * Real.pi) : ℝ) : ℂ) * _).re ≤ -27
  rw [he]
  have hi :=
    LLS.PaperStatements.MellinKernel.integrable_gammaFactor_power_line K χ (c := 0) (x := 1)
      (by norm_num only)
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
  have h := refined_24_gamma_re_le_neg27 χ
  change (1 / (2 * Real.pi)) * _ ≤ -27
  rw [one_div_mul_eq_div]
  exact h

/-- For primitive nonprincipal GRH data, the width-24 scale-one arithmetic
sums and absolute zero mass equal 48 times the conductor logarithm plus the
two Gamma integrals. Specialize the exact dual-scale formula at one and use
positivity of the triangular zero terms. -/
theorem refined_24_mass_signed_formula {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
    let G := fun ψ : DirichletCharacter ℂ q ↦
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv ψ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
            K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t))
    (∑' n : ℕ, K.summand χ 1 n) + (∑' n : ℕ, K.summand χ⁻¹ 1 n) +
        ((∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖ : ℝ) : ℂ) =
      48 * Complex.log q + G χ + G χ⁻¹ := by
  have h :=
    LLS.PaperStatements.triangular_dual_signed_formula (a := 24) (by norm_num only) hq hGRH hp hne
      hinv (x := 1) le_rfl
  simp only [inv_one, Complex.ofReal_one, Complex.one_cpow, mul_one] at h
  rw [LLS.PaperStatements.triangular_zeroSum_one_eq_absoluteMass (by norm_num only : (0 : ℝ) < 24)
      hne] at h
  norm_num only [LLS.PaperStatements.triangularKernelProfile, Real.log_one, abs_zero, sub_zero,
    max_eq_right (by norm_num only : (0 : ℝ) ≤ 48), Complex.ofReal_ofNat] at h
  dsimp only
  linear_combination h

/-- Under GRH, the width-24 absolute zero mass is at most 48 times the
conductor logarithm minus the two scale-one arithmetic sums and 54. Insert
the signed Gamma bounds for the character and its inverse into the exact
scale-one mass identity. -/
theorem refined_24_mass_signed_GRH {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
    (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) ≤
      48 * Real.log q - (∑' n : ℕ, K.summand χ 1 n).re - (∑' n : ℕ, K.summand χ⁻¹ 1 n).re - 54 := by
  let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
  let G := fun ψ : DirichletCharacter ℂ q ↦
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        logDeriv ψ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
          K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t))
  have hg (ψ : DirichletCharacter ℂ q) : (G ψ).re ≤ -27 :=
    refined_24_gamma_line_le_neg27 ψ (b := 9 / 16) (by norm_num only) (by norm_num only)
  have he := refined_24_mass_signed_formula hq hGRH hp hne hinv
  change
    (∑' n : ℕ, K.summand χ 1 n) + (∑' n : ℕ, K.summand χ⁻¹ 1 n) +
        ((∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖ : ℝ) : ℂ) =
      48 * Complex.log q + G χ + G χ⁻¹ at he
  rw [← Complex.natCast_log, ← Complex.ofReal_ofNat 48, ← Complex.ofReal_mul] at he
  have hr := congrArg Complex.re he
  simp only [Complex.add_re, Complex.ofReal_re] at hr
  change (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) ≤ _
  linarith only [hr, hg χ, hg χ⁻¹]

/-- Under GRH, the real part of the width-24 oscillating zero sum is bounded
below by minus 48 times the conductor logarithm plus both scale-one arithmetic
sums and 54. The triangle inequality and the signed mass estimate preserve
the arithmetic cancellation for subgroup averaging. -/
theorem refined_24_osc_zero_lower {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
    (-48 * Real.log q + (∑' n : ℕ, K.summand χ 1 n).re + (∑' n : ℕ, K.summand χ⁻¹ 1 n).re + 54 ≤
      (∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ).re) := by
  let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
  let Z := ∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ
  have hs := LLS.PaperStatements.MellinKernel.summable_oscillatingZeroTerm K hq hGRH hp hne hinv hx
  have ht := norm_tsum_le_tsum_norm hs.norm
  have he : (∑' ρ : ℂ, ‖K.oscillatingZeroTerm χ x ρ‖) = ∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖ :=
    tsum_congr (LLS.PaperStatements.MellinKernel.norm_oscillatingZeroTerm K χ hx)
  have hz : ‖Z‖ ≤ ∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖ := ht.trans_eq he
  have hm := refined_24_mass_signed_GRH hq hGRH hp hne hinv
  have hr := Complex.re_le_norm (-Z)
  rw [Complex.neg_re, norm_neg] at hr
  change -48 * Real.log q + _ + _ + 54 ≤ Z.re
  linarith only [hz, hm, hr]

/-- For positive scale, the nonprincipal width-24 inverse-scale primitive
character sum is bounded below by minus the level-one principal sum. Apply
nonnegativity to the complete primitive average and remove its principal member. -/
theorem refined_24_inverse_sum_lower {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) {x : ℝ}
    (hx : 0 < x) :
    letI := Classical.propDecidable
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24);
    -(∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x⁻¹ n).re ≤
      ∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H),
        (∑' n : ℕ, K.summand (χ.val.primitiveCharacter)⁻¹ x⁻¹ n).re := by
  classical
  let _ := Classical.propDecidable
  let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
  let A := NumberTheory.subgroupAnnihilator H
  let F := fun χ : A ↦ (∑' n : ℕ, K.summand χ.val.primitiveCharacter x⁻¹ n).re
  have hn := LLS.PaperStatements.MellinKernel.primitive_tsum_sum_re_nonneg K A (inv_pos.mpr hx)
  rw [Complex.re_sum] at hn
  have he := Finset.sum_erase_add (s := Finset.univ) F (Finset.mem_univ (1 : A))
  have hp : F (1 : A) = (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x⁻¹ n).re :=
    congrArg Complex.re
      (tsum_congr (LLS.PaperStatements.MellinKernel.principal_primitive_summand_eq_level_one K x⁻¹))
  have hr (χ : A) : (∑' n : ℕ, K.summand (χ.val.primitiveCharacter)⁻¹ x⁻¹ n).re = F χ := by
    let : NeZero χ.val.conductor := ⟨χ.val.conductor_ne_zero⟩
    exact
      LLS.PaperStatements.MellinKernel.tsum_summand_inv_re_eq K χ.val.primitiveCharacter
        (inv_pos.mpr hx)
  have hs := Finset.sum_congr (s₁ := Finset.univ.erase (1 : A)) rfl (fun χ _ ↦ hr χ)
  change -_ ≤ _
  rw [hs]
  rw [hp] at he
  change 0 ≤ ∑ χ : A, F χ at hn
  linarith only [hn, he]

/-- Under GRH and scale at least one, the nonprincipal width-24 primitive
arithmetic and zero aggregate is bounded by the conductor profile, signed Gamma
terms and the inverse-scale principal sum. Combine the family identity with
the nonnegative full inverse-character average. -/
theorem refined_24_family_dual_upper {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    letI := Classical.propDecidable
    letI : ∀ i : NumberTheory.subgroupAnnihilator H, NeZero i.val.conductor := fun i ↦
      ⟨i.val.conductor_ne_zero⟩
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
    let G :=
      fun (i : NumberTheory.subgroupAnnihilator H) (ψ : DirichletCharacter ℂ (i.val.conductor))
        (y : ℝ) ↦
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv ψ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
            (K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (y : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t)))
    let S := Finset.univ.filter (fun i : NumberTheory.subgroupAnnihilator H ↦ i.val ≠ 1)
    (∑ i ∈ S,
        ((∑' n : ℕ, K.summand (i.val.primitiveCharacter) x n) +
            (∑' ρ : ℂ, K.oscillatingZeroTerm (i.val.primitiveCharacter) x ρ)).re) ≤
      LLS.PaperStatements.triangularKernelProfile 24 x * (∑ i ∈ S, Real.log (i.val.conductor)) +
        ∑ i ∈ S, (G i (i.val.primitiveCharacter) x + G i (i.val.primitiveCharacter)⁻¹ x⁻¹).re +
        (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x⁻¹ n).re := by
  classical
  let _ := Classical.propDecidable
  let A := NumberTheory.subgroupAnnihilator H
  have hf : Finset.univ.filter (fun χ : A ↦ χ.val ≠ 1) = Finset.univ.erase (1 : A) := by
    have hn (χ : A) : χ.val = 1 ↔ χ = 1 := by
      constructor
      · intro h
        exact Subtype.ext h
      · intro h
        exact congrArg Subtype.val h
    apply Finset.ext
    intro χ
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true,
      not_congr (hn χ)]
  have he := refined_triangular24_family H hGRH hx
  have hd := refined_24_inverse_sum_lower H (zero_lt_one.trans_le hx)
  dsimp only at he hd ⊢
  rw [hf] at he ⊢
  simp only [Complex.add_re, Finset.sum_add_distrib] at he ⊢
  linarith only [he, hd]

/-- Under GRH, the width-24 nonprincipal primitive arithmetic aggregate is
bounded by the conductor profile, both Gamma terms and inverse-scale principal
sum, minus the scale-one arithmetic pairs and 54 per character. Sum the
signed oscillating-zero lower bound and combine it with the family upper bound. -/
theorem refined_24_family_arithmetic_upper {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    letI := Classical.propDecidable
    letI : ∀ i : NumberTheory.subgroupAnnihilator H, NeZero i.val.conductor := fun i ↦
      ⟨i.val.conductor_ne_zero⟩
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
    let G :=
      fun (i : NumberTheory.subgroupAnnihilator H) (ψ : DirichletCharacter ℂ (i.val.conductor))
        (y : ℝ) ↦
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv ψ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
            (K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (y : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t)))
    let S := Finset.univ.filter (fun i : NumberTheory.subgroupAnnihilator H ↦ i.val ≠ 1)
    (∑ i ∈ S, (∑' n : ℕ, K.summand (i.val.primitiveCharacter) x n).re) ≤
      LLS.PaperStatements.triangularKernelProfile 24 x * (∑ i ∈ S, Real.log (i.val.conductor)) +
          ∑ i ∈ S, (G i (i.val.primitiveCharacter) x + G i (i.val.primitiveCharacter)⁻¹ x⁻¹).re +
          (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x⁻¹ n).re +
          48 * (∑ i ∈ S, Real.log i.val.conductor) -
        (∑ i ∈ S,
          ((∑' n : ℕ, K.summand i.val.primitiveCharacter 1 n).re +
            (∑' n : ℕ, K.summand (i.val.primitiveCharacter)⁻¹ 1 n).re)) -
        54 * S.card := by
  classical
  let _ := Classical.propDecidable
  let A := NumberTheory.subgroupAnnihilator H
  let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
  let S := Finset.univ.filter (fun χ : A ↦ χ.val ≠ 1)
  have hn (χ : A) (hχ : χ ∈ S) : χ.val ≠ 1 := (Finset.mem_filter.mp hχ).2
  have hp (χ : A) (hχ : χ ∈ S) : χ.val.primitiveCharacter ≠ 1 :=
    AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ.val (hn χ hχ)
  let : ∀ χ : A, NeZero χ.val.conductor := fun χ ↦ ⟨χ.val.conductor_ne_zero⟩
  have hz (χ : A) (hχ : χ ∈ S) :
    -48 * Real.log χ.val.conductor + (∑' n : ℕ, K.summand χ.val.primitiveCharacter 1 n).re +
        (∑' n : ℕ, K.summand (χ.val.primitiveCharacter)⁻¹ 1 n).re +
        54 ≤
      (∑' ρ : ℂ, K.oscillatingZeroTerm χ.val.primitiveCharacter x ρ).re := by
    let : NeZero χ.val.conductor := ⟨χ.val.conductor_ne_zero⟩
    exact
      refined_24_osc_zero_lower
        ((by norm_num only : 2 ≤ 3).trans
          (NumberTheory.three_le_conductor_of_ne_one χ.val (hn χ hχ)))
        hGRH (DirichletCharacter.primitiveCharacter_isPrimitive χ.val) (hp χ hχ)
        (inv_ne_one.mpr (hp χ hχ)) (zero_lt_one.trans_le hx)
  have hsum := Finset.sum_le_sum (s := S) hz
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hsum
  have h := refined_24_family_dual_upper H hGRH hx
  dsimp only at h ⊢
  simp only [Complex.add_re, Finset.sum_add_distrib] at h
  simp only [Complex.add_re, Finset.sum_add_distrib]
  linarith only [h, hsum]

/-- Under GRH and eligible-prime containment through the cutoff, the finite
width-24 principal sum is bounded by the signed conductor, Gamma and arithmetic
terms plus the two exact level-one principal costs. Separate the principal
character from the primitive average and apply the family arithmetic bound. -/
theorem refined_24_finite_principal_bound {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x X : ℝ} (hx : 1 ≤ x)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → NumberTheory.residueInSubgroup q H p) :
    letI := Classical.propDecidable
    letI : ∀ i : NumberTheory.subgroupAnnihilator H, NeZero i.val.conductor := fun i ↦
      ⟨i.val.conductor_ne_zero⟩
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
    let G :=
      fun (i : NumberTheory.subgroupAnnihilator H) (ψ : DirichletCharacter ℂ (i.val.conductor))
        (y : ℝ) ↦
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv ψ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
            (K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (y : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t)))
    let S := Finset.univ.filter (fun i : NumberTheory.subgroupAnnihilator H ↦ i.val ≠ 1)
    (H.index : ℝ) * (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ q) x n).re) ≤
      LLS.PaperStatements.triangularKernelProfile 24 x * (∑ i ∈ S, Real.log (i.val.conductor)) +
            ∑ i ∈ S, (G i (i.val.primitiveCharacter) x + G i (i.val.primitiveCharacter)⁻¹ x⁻¹).re +
            (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x⁻¹ n).re +
            48 * (∑ i ∈ S, Real.log i.val.conductor) -
          (∑ i ∈ S,
            ((∑' n : ℕ, K.summand i.val.primitiveCharacter 1 n).re +
              (∑' n : ℕ, K.summand (i.val.primitiveCharacter)⁻¹ 1 n).re)) -
          54 * S.card +
        (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x n).re := by
  classical
  let _ := Classical.propDecidable
  let A := NumberTheory.subgroupAnnihilator H
  let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
  let F := fun χ : A ↦ (∑' n : ℕ, K.summand χ.val.primitiveCharacter x n).re
  have hf : Finset.univ.filter (fun χ : A ↦ χ.val ≠ 1) = Finset.univ.erase (1 : A) := by
    have hn (χ : A) : χ.val = 1 ↔ χ = 1 := by
      constructor
      · intro h
        exact Subtype.ext h
      · intro h
        exact congrArg Subtype.val h
    apply Finset.ext
    intro χ
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true,
      not_congr (hn χ)]
  have hs := Finset.sum_erase_add (s := Finset.univ) F (Finset.mem_univ (1 : A))
  have hp : F (1 : A) = (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x n).re :=
    congrArg Complex.re
      (tsum_congr (LLS.PaperStatements.MellinKernel.principal_primitive_summand_eq_level_one K x))
  rw [hp] at hs
  have hc :=
    LLS.PaperStatements.MellinKernel.principal_sum_le_primitive_of_noSmall K H
      (zero_lt_one.trans_le hx) hsmall
  have hb := refined_24_family_arithmetic_upper H hGRH hx
  dsimp only at hb ⊢
  rw [hf] at hb ⊢
  change (H.index : ℝ) * _ ≤ ∑ χ : A, F χ at hc
  linarith only [hc, hs, hb]

/-- Under GRH and the no-small-prime hypotheses, the width-24 finite principal
sum at scale `x` plus twice the finite scale-one sum is bounded by conductor,
Gamma and three exact level-one costs. Retain the scale-one arithmetic credit
and replace the finite principal sum by its level-one counterpart. -/
theorem refined_24_credited_principal {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x X : ℝ} (hx : 1 ≤ x)
    (hX : 0 ≤ X) (hlarge : ∀ p : ℕ, p.Prime → p ∣ q → X < (p : ℝ))
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → NumberTheory.residueInSubgroup q H p) :
    letI := Classical.propDecidable
    letI : ∀ i : NumberTheory.subgroupAnnihilator H, NeZero i.val.conductor := fun i ↦
      ⟨i.val.conductor_ne_zero⟩
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
    let G :=
      fun (i : NumberTheory.subgroupAnnihilator H) (ψ : DirichletCharacter ℂ (i.val.conductor))
        (y : ℝ) ↦
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv ψ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
            (K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (y : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t)))
    let S := Finset.univ.filter (fun i : NumberTheory.subgroupAnnihilator H ↦ i.val ≠ 1)
    (H.index : ℝ) *
        ((∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) x n).re) +
          2 * (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) 1 n).re)) ≤
      LLS.PaperStatements.triangularKernelProfile 24 x * (∑ i ∈ S, Real.log (i.val.conductor)) +
            ∑ i ∈ S, (G i (i.val.primitiveCharacter) x + G i (i.val.primitiveCharacter)⁻¹ x⁻¹).re +
            48 * (∑ i ∈ S, Real.log i.val.conductor) -
          54 * S.card +
        (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x⁻¹ n).re +
        (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x n).re +
        2 * (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) 1 n).re := by
  classical
  let _ := Classical.propDecidable
  let A := NumberTheory.subgroupAnnihilator H
  let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
  have hf : Finset.univ.filter (fun χ : A ↦ χ.val ≠ 1) = Finset.univ.erase (1 : A) := by
    have he (χ : A) : χ.val = 1 ↔ χ = 1 := by
      constructor
      · intro h
        exact Subtype.ext h
      · intro h
        exact congrArg Subtype.val h
    apply Finset.ext
    intro χ
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true,
      not_congr (he χ)]
  have heq := LLS.PaperStatements.finite_principal_eq_level_one K (q := q) (x := x) hX hlarge
  have hb := refined_24_finite_principal_bound H hGRH hx hsmall
  have ha := refined_triangular24_scaleOne_credit H hX hlarge hsmall
  dsimp only at hb ha ⊢
  rw [heq] at hb
  rw [hf] at hb ⊢
  linarith only [hb, ha]

/-- The width-24 imaginary-axis kernel has norm at most `4608/(1+(24t)²)`.
Combine the sinc bound with the height-square bound; the scaled denominator
gives a linear-in-width Gamma integral estimate. -/
theorem refined_24_central_decay (t : ℝ) :
    ‖Analysis.triangularMellinFunction 24 (Complex.I * t)‖ ≤ 4608 / (1 + (24 * t) ^ 2) := by
  have hn : ‖Analysis.triangularMellinFunction 24 (Complex.I * t)‖ ≤ (2304 : ℝ) := by
    rw [Analysis.norm_triangularMellinFunction_imaginary (by norm_num only : (24 : ℝ) ≠ 0)]
    have hs := Real.abs_sinc_le_one (24 * t)
    have ha := sq_abs (Real.sinc (24 * t))
    nlinarith only [hs, ha, abs_nonneg (Real.sinc (24 * t))]
  have ht :=
    Analysis.triangularMellinFunction_height_sq_norm_le_four (by norm_num only : (24 : ℝ) ≠ 0) t
  apply (le_div_iff₀ (by linarith only [sq_nonneg (24 * t)] : (0 : ℝ) < 1 + (24 * t) ^ 2)).mpr
  nlinarith only [hn, ht]

/-- The raw width-24 central Gamma integral has norm at most 46464 at every
positive scale. Use the scaled sinc bound, the logarithmic Gamma majorant and
the common logarithmic integral after changing the height by a factor of 24. -/
theorem refined_24_central_gamma_norm {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    ‖∫ t : ℝ,
          logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
            (Analysis.triangularMellinFunction 24 (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))‖ ≤
      46464 := by
  let f := fun t : ℝ ↦ (Real.log (4 + |t|) + 1) / (1 + t ^ 2)
  have hf :=
    (MeasureTheory.integrable_comp_mul_left_iff f (by norm_num only : (24 : ℝ) ≠ 0)).mpr
      Analysis.integrable_log_add_abs_div_one_add_sq
  have hi :=
    MeasureTheory.norm_integral_le_of_norm_le (f := fun t : ℝ ↦
      logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
        (Analysis.triangularMellinFunction 24 (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)))
      (hf.const_mul (11 * 4608 : ℝ))
      (MeasureTheory.ae_of_all _
        (fun t : ℝ ↦ by
          have hr : (Complex.I * (t : ℂ) + 1 / 2).re = (1 / 2 : ℝ) := by
            simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
              Complex.div_ofNat_re, Complex.one_re, zero_add]
          have hg := LLS.PaperStatements.triangular_gamma_central_log_bound χ hr
          have hlog :=
            Real.log_le_log (by linarith only [abs_nonneg t] : (0 : ℝ) < 4 + |t|)
              (by
                rw [abs_mul, abs_of_pos (by norm_num only : (0 : ℝ) < 24)]
                nlinarith only [abs_nonneg t] : 4 + |t| ≤ 4 + |24 * t|)
          have hp : 0 ≤ Real.log (4 + |24 * t|) :=
            Real.log_nonneg (by linarith only [abs_nonneg (24 * t)])
          simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
            Complex.ofReal_im, one_mul, zero_mul, zero_add, Complex.div_ofNat_im, Complex.one_im,
            zero_div, add_zero] at hg
          have hb :
            ‖logDeriv χ.gammaFactor (Complex.I * t + 1 / 2)‖ ≤
              11 * (Real.log (4 + |24 * t|) + 1) := by
            linarith only [hg, hlog, hp]
          rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
          simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Real.rpow_zero, mul_one]
          have h :=
            mul_le_mul hb (refined_24_central_decay t) (norm_nonneg _)
              (by linarith only [hp] : 0 ≤ 11 * (Real.log (4 + |24 * t|) + 1))
          exact
            h.trans_eq
              (by
                dsimp only [f]; ring)))
  rw [MeasureTheory.integral_const_mul, MeasureTheory.Measure.integral_comp_mul_left] at hi
  norm_num only [abs_of_pos (by norm_num only : (0 : ℝ) < (24 : ℝ)⁻¹), smul_eq_mul] at hi
  have hb := Analysis.logarithmic_inverseSquare_integral_le_twenty_two
  dsimp only [f] at hi
  linarith only [hi, hb]

/-- For every character and positive scale, the normalized width-24 Gamma
integral on the right contour has norm at most 8000. Shift to the central line
and normalize the explicit scaled-kernel integral bound. This applies to both
the scale and its reciprocal in the two-scale comparison. -/
theorem refined_24_gamma_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
              (K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t)))‖ ≤
      (8000 : ℝ) := by
  let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
  have he :=
    LLS.PaperStatements.MellinKernel.gammaIntegral_eq_central_of_pos K χ (b := 9 / 16)
      (by norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) hx
  change ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * _‖ ≤ _
  rw [he]
  have hraw := refined_24_central_gamma_norm χ hx
  have hn := LLS.PaperStatements.norm_mellinNormalization_mul_le_sixth hraw
  exact hn.trans (by norm_num only : (46464 : ℝ) / 6 ≤ 8000)

/-- For every character and positive scale, the real part of the two normalized
Gamma integrals at reciprocal scales is at most 16000. Bound each real part by
its norm and use the uniform width-24 estimate. -/
theorem refined_24_gamma_pair_le {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
    let G := fun (ψ : DirichletCharacter ℂ q) (y : ℝ) ↦
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv ψ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
            (K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (y : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t)))
    (G χ x + G χ⁻¹ x⁻¹).re ≤ 16000 := by
  dsimp only
  rw [Complex.add_re]
  have h₁ := refined_24_gamma_norm_le χ hx
  have h₂ := refined_24_gamma_norm_le χ⁻¹ (inv_pos.mpr hx)
  dsimp only at h₁ h₂
  have h₃ :=
    Complex.re_le_norm
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv χ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
            ((LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)).function
                (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t))))
  have h₄ :=
    Complex.re_le_norm
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv χ⁻¹.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
            ((LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)).function
                (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              ((x⁻¹ : ℝ) : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t))))
  linarith only [h₁, h₂, h₃, h₄]

/-- Under GRH and the stated cutoff hypotheses, the credited width-24 finite
principal sum is bounded by the three exact level-one costs and a conductor
budget. Sum the reciprocal-scale Gamma bound over nonprincipal characters and
bound their conductor logarithms by the modulus logarithm. -/
theorem refined_24_credited_conductor {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x X : ℝ} (hx : 1 ≤ x)
    (hX : 0 ≤ X) (hlarge : ∀ p : ℕ, p.Prime → p ∣ q → X < (p : ℝ))
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → NumberTheory.residueInSubgroup q H p) :
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
    (H.index : ℝ) *
        ((∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) x n).re) +
          2 * (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) 1 n).re)) ≤
      (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x⁻¹ n).re +
        (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x n).re +
        2 * (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) 1 n).re +
        ((H.index : ℝ) - 1) *
          ((48 + LLS.PaperStatements.triangularKernelProfile 24 x) * Real.log q + 15946) := by
  classical
  let _ := Classical.propDecidable
  let A := NumberTheory.subgroupAnnihilator H
  let S := Finset.univ.filter (fun χ : A ↦ χ.val ≠ 1)
  let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
  let G := fun (i : A) (ψ : DirichletCharacter ℂ i.val.conductor) (y : ℝ) ↦
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        logDeriv ψ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
          (K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (y : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t)))
  have hg :
    (∑ i ∈ S, (G i i.val.primitiveCharacter x + G i i.val.primitiveCharacter⁻¹ x⁻¹).re) ≤
      16000 * (S.card : ℝ) := by
    calc
      _ ≤ ∑ _i ∈ S, (16000 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact refined_24_gamma_pair_le i.val.primitiveCharacter (zero_lt_one.trans_le hx)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hf : S = Finset.univ.erase (1 : A) := by
    have he (χ : A) : χ.val = 1 ↔ χ = 1 := by
      constructor
      · intro h
        exact Subtype.ext h
      · intro h
        exact congrArg Subtype.val h
    apply Finset.ext
    intro χ
    simp only [S, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true,
      not_congr (he χ)]
  have hcard : (S.card : ℝ) = (H.index : ℝ) - 1 := by
    rw [hf, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨1⟩))),
      Nat.cast_one, NumberTheory.card_subgroupAnnihilator]
  have hcond :
    (∑ χ ∈ S, Real.log χ.val.conductor) = LLS.PaperStatements.subgroupConductorLogSum H := by
    rw [hf]
    unfold LLS.PaperStatements.subgroupConductorLogSum
    apply Finset.sum_congr
    · apply Finset.ext
      intro χ
      simp only [Finset.mem_erase, Finset.mem_univ]
    · intro χ _
      rfl
  have hcoef : 0 ≤ 48 + LLS.PaperStatements.triangularKernelProfile 24 x := by
    unfold LLS.PaperStatements.triangularKernelProfile
    have hp := le_max_left (0 : ℝ) (2 * 24 - |Real.log x|)
    linarith only [hp]
  have hc := mul_le_mul_of_nonneg_left (LLS.PaperStatements.subgroupConductorLogSum_le H) hcoef
  have hb := refined_24_credited_principal H hGRH hx hX hlarge hsmall
  dsimp only at hb ⊢
  dsimp only [G, K, S, A] at hg hcard hcond
  rw [hcard, hcond] at hb
  rw [hcard] at hg
  nlinarith only [hb, hg, hc]

/-- Under GRH, the width-24 credited principal comparison has the explicit
conductor budget from the large-index argument. For scales at least one, rewrite
the triangular profile and discard the negative scale-one Gamma credit. -/
theorem refined_24_paper_comparison {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x X : ℝ} (hx : 1 ≤ x)
    (hX : 0 ≤ X) (hlarge : ∀ p : ℕ, p.Prime → p ∣ q → X < (p : ℝ))
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → NumberTheory.residueInSubgroup q H p) :
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
    (H.index : ℝ) *
        ((∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) x n).re) +
          2 * (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) 1 n).re)) ≤
      (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x⁻¹ n).re +
        (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x n).re +
        2 * (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) 1 n).re +
        ((H.index : ℝ) - 1) * ((48 + max 0 (48 - Real.log x)) * Real.log q + 16000) := by
  have hp : LLS.PaperStatements.triangularKernelProfile 24 x = max 0 (48 - Real.log x) := by
    unfold LLS.PaperStatements.triangularKernelProfile
    rw [abs_of_nonneg (Real.log_nonneg hx)]
    norm_num only
  have hi : (1 : ℝ) ≤ H.index := by
    have hn : 0 < Fintype.card (NumberTheory.subgroupAnnihilator H) := Fintype.card_pos_iff.mpr ⟨1⟩
    rw [NumberTheory.card_subgroupAnnihilator] at hn
    exact_mod_cast hn
  have hb := refined_24_credited_conductor H hGRH hx hX hlarge hsmall
  dsimp only at hb ⊢
  rw [hp] at hb
  nlinarith only [hb, hi]

/-- A triangle of half-width 48 is bounded by two triangles of half-width 36
whose centers are shifted by 12. This pointwise majorant permits reuse of the
width-18 principal estimates at two positive rescaled arguments. -/
theorem refined_24_profile_cover (t : ℝ) :
    max 0 (48 - |t|) ≤ max 0 (36 - |t - 12|) + max 0 (36 - |t + 12|) := by
  have ha := le_max_right (0 : ℝ) (36 - |t - 12|)
  have hb := le_max_right (0 : ℝ) (36 - |t + 12|)
  have hc := le_max_left (0 : ℝ) (36 - |t - 12|)
  have hd := le_max_left (0 : ℝ) (36 - |t + 12|)
  apply max_le
  · linarith only [hc, hd]
  · by_cases h₁ : t ≤ -12
    · rw [abs_of_nonpos (by linarith only [h₁] : t ≤ 0),
        abs_of_nonpos (by linarith only [h₁] : t + 12 ≤ 0)] at *
      linarith only [hb, hc]
    · by_cases h₂ : 12 ≤ t
      · rw [abs_of_nonneg (by linarith only [h₂] : 0 ≤ t),
          abs_of_nonneg (by linarith only [h₂] : 0 ≤ t - 12)] at *
        linarith only [ha, hd]
      · rw [abs_of_nonpos (by linarith only [h₂] : t - 12 ≤ 0),
          abs_of_nonneg (by linarith only [h₁] : 0 ≤ t + 12)] at *
        have ht := abs_nonneg t
        linarith only [ha, hb, ht]

/-- At any positive argument, the width-24 triangular profile is bounded by
width-18 profiles with reciprocal exponential shifts. Apply the real-variable
triangle cover after taking logarithms. -/
theorem refined_24_profile_le_shifted {u : ℝ} (hu : 0 < u) :
    LLS.PaperStatements.triangularKernelProfile 24 u ≤
      LLS.PaperStatements.triangularKernelProfile 18 (u / Real.exp 12) +
        LLS.PaperStatements.triangularKernelProfile 18 (u * Real.exp 12) := by
  unfold LLS.PaperStatements.triangularKernelProfile
  rw [Real.log_div hu.ne' (Real.exp_ne_zero 12), Real.log_mul hu.ne' (Real.exp_ne_zero 12),
    Real.log_exp]
  norm_num only
  exact refined_24_profile_cover (Real.log u)

/-- For a positive scale and nonzero index, the width-24 level-one summand
is its triangular profile times the nonnegative Mangoldt weight. Evaluate the
Mellin transform at the positive rescaled index. -/
theorem refined_24_level_one_term {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    ((LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)).summand
          (1 : DirichletCharacter ℂ 1) x n).re =
      ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        LLS.PaperStatements.triangularKernelProfile 24 (n / x) := by
  have hp : 0 < (n : ℝ) / x := div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hx
  simp only [LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn,
    MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), mul_one, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [LLS.PaperStatements.triangular_transform_of_function _ (by norm_num only : (0 : ℝ) < 24) rfl
      hp]

/-- Each width-24 level-one arithmetic term is bounded by the two width-18
terms at exponentially shifted scales. The Mangoldt weight is nonnegative,
so the pointwise profile cover transfers to arithmetic terms. -/
theorem refined_24_summand_le_shifted {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ((LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)).summand
          (1 : DirichletCharacter ℂ 1) x n).re ≤
      ((LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
            (1 : DirichletCharacter ℂ 1) (x * Real.exp 12) n).re +
        ((LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
            (1 : DirichletCharacter ℂ 1) (x / Real.exp 12) n).re := by
  by_cases hn : n = 0
  · subst n
    simp only [LLS.PaperStatements.MellinKernel.summand, ↓reduceIte, Complex.zero_re, add_zero,
      le_refl]
  · rw [refined_24_level_one_term hx hn,
      LLS.PaperStatements.triangular18_level_one_term (mul_pos hx (Real.exp_pos 12)) hn,
      LLS.PaperStatements.triangular18_level_one_term (div_pos hx (Real.exp_pos 12)) hn]
    have hp := refined_24_profile_le_shifted (div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hx)
    have hm :=
      mul_le_mul_of_nonneg_left hp
        (div_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n)) (Real.sqrt_nonneg n))
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc, mul_left_comm, mul_comm] at hm ⊢
    nlinarith only [hm]

/-- The full width-24 level-one arithmetic sum at a positive scale is bounded
by the sum of two width-18 level-one arithmetic sums at shifted scales. Sum the
pointwise cover using the absolute convergence of all three Mellin sums. -/
theorem refined_24_principal_le_shifted {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ,
          (LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)).summand
            (1 : DirichletCharacter ℂ 1) x n).re ≤
      (∑' n : ℕ,
            (LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
              (1 : DirichletCharacter ℂ 1) (x * Real.exp 12) n).re +
        (∑' n : ℕ,
            (LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
              (1 : DirichletCharacter ℂ 1) (x / Real.exp 12) n).re := by
  let K24 := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
  let K18 := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have h24 := LLS.PaperStatements.MellinKernel.summable_summand K24 (1 : DirichletCharacter ℂ 1) hx
  have hp :=
    LLS.PaperStatements.MellinKernel.summable_summand K18 (1 : DirichletCharacter ℂ 1)
      (mul_pos hx (Real.exp_pos 12))
  have hm :=
    LLS.PaperStatements.MellinKernel.summable_summand K18 (1 : DirichletCharacter ℂ 1)
      (div_pos hx (Real.exp_pos 12))
  change
    Complex.reCLM (∑' n : ℕ, K24.summand (1 : DirichletCharacter ℂ 1) x n) ≤
      Complex.reCLM (∑' n : ℕ, K18.summand (1 : DirichletCharacter ℂ 1) (x * Real.exp 12) n) +
        Complex.reCLM (∑' n : ℕ, K18.summand (1 : DirichletCharacter ℂ 1) (x / Real.exp 12) n)
  rw [Complex.reCLM.map_tsum h24, Complex.reCLM.map_tsum hp, Complex.reCLM.map_tsum hm]
  have h :=
    Summable.tsum_le_tsum (fun n ↦ refined_24_summand_le_shifted hx n) (Complex.reCLM.summable h24)
      ((Complex.reCLM.summable hp).add (Complex.reCLM.summable hm))
  change
    (∑' n : ℕ, Complex.reCLM (K24.summand 1 x n)) ≤
      (∑' n : ℕ,
        (Complex.reCLM (K18.summand 1 (x * Real.exp 12) n) +
          Complex.reCLM (K18.summand 1 (x / Real.exp 12) n))) at h
  rw [(Complex.reCLM.summable hp).tsum_add (Complex.reCLM.summable hm)] at h
  exact h

/-- The two exponential shift coefficients have explicit rational budgets.
Bound the positive exponentials by powers of the rational upper bound for
`exp 1`, and bound their reciprocals by one. -/
theorem refined_24_shift_exp_bounds :
    Real.exp 6 + Real.exp (-6) ≤ 410 ∧ Real.exp 3 + Real.exp (-3) ≤ 22 := by
  have he : Real.exp 1 ≤ (68 / 25 : ℝ) := Real.exp_one_lt_d9.le.trans (by norm_num only)
  have h6 := pow_le_pow_left₀ (Real.exp_pos 1).le he 6
  have h3 := pow_le_pow_left₀ (Real.exp_pos 1).le he 3
  have e6 : Real.exp 1 ^ 6 = Real.exp 6 := by
    rw [← Real.exp_nat_mul]; norm_num only
  have e3 : Real.exp 1 ^ 3 = Real.exp 3 := by
    rw [← Real.exp_nat_mul]; norm_num only
  rw [e6] at h6
  rw [e3] at h3
  have hn6 : Real.exp (-6) ≤ 1 := (Real.exp_le_one_iff).mpr (by norm_num only)
  have hn3 : Real.exp (-3) ≤ 1 := (Real.exp_le_one_iff).mpr (by norm_num only)
  constructor <;> norm_num only at h6 h3 ⊢ <;> linarith only [h6, h3, hn6, hn3]

/-- Under RH, the full width-24 level-one arithmetic sum at a positive scale
has the explicit paper budget. Apply the two shifted width-18 bounds and
control their square-root and fourth-root exponential factors. -/
theorem refined_24_principal_upper (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ,
          (LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)).summand
            (1 : DirichletCharacter ℂ 1) x n).re ≤
      130000000000 * Real.sqrt x + 500000000 * x ^ (1 / 4 : ℝ) := by
  have hs := refined_24_principal_le_shifted hx
  have hp :=
    LLS.PaperStatements.triangular18_level_one_arithmetic_upper_of_rh hRH
      (mul_pos hx (Real.exp_pos 12))
  have hm :=
    LLS.PaperStatements.triangular18_level_one_arithmetic_upper_of_rh hRH
      (div_pos hx (Real.exp_pos 12))
  have he2 : Real.sqrt (Real.exp 12) = Real.exp 6 := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    norm_num only
  have he4 : Real.exp 12 ^ (1 / 4 : ℝ) = Real.exp 3 := by
    rw [← Real.exp_mul]
    norm_num only
  rw [Real.sqrt_mul hx.le, Real.mul_rpow hx.le (Real.exp_pos 12).le, he2, he4] at hp
  rw [Real.sqrt_div hx.le, Real.div_rpow hx.le (Real.exp_pos 12).le, he2, he4] at hm
  simp only [div_eq_mul_inv, ← Real.exp_neg] at hs hm
  have hsqrt := Real.sqrt_nonneg x
  have hpow := Real.rpow_nonneg hx.le (1 / 4)
  have h1 := mul_le_mul_of_nonneg_left refined_24_shift_exp_bounds.1 hsqrt
  have h2 := mul_le_mul_of_nonneg_left refined_24_shift_exp_bounds.2 hpow
  nlinarith only [hs, hp, hm, h1, h2, hsqrt, hpow]

/-- Under GRH and the cutoff hypotheses, the credited width-24 finite sum
satisfies the paper comparison with an explicit numerical principal cost.
Apply the positive-scale principal bound at the scale, its inverse and one. -/
theorem refined_24_numeric_comparison {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x X : ℝ} (hx : 1 ≤ x)
    (hX : 0 ≤ X) (hlarge : ∀ p : ℕ, p.Prime → p ∣ q → X < (p : ℝ))
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → NumberTheory.residueInSubgroup q H p) :
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
    (H.index : ℝ) *
        ((∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) x n).re) +
          2 * (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) 1 n).re)) ≤
      130000000000 * (Real.sqrt x + Real.sqrt x⁻¹) +
        500000000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
        2 * (130000000000 + 500000000) +
        ((H.index : ℝ) - 1) * ((48 + max 0 (48 - Real.log x)) * Real.log q + 16000) := by
  have hb := refined_24_paper_comparison H hGRH hx hX hlarge hsmall
  have hp := refined_24_principal_upper hGRH.riemann (zero_lt_one.trans_le hx)
  have hm := refined_24_principal_upper hGRH.riemann (inv_pos.mpr (zero_lt_one.trans_le hx))
  have h1 := refined_24_principal_upper hGRH.riemann (x := 1) (by norm_num only)
  simp only [Real.sqrt_one, Real.one_rpow, mul_one] at h1
  dsimp only at hb ⊢
  nlinarith only [hb, hp, hm, h1]

/-- On the width-24 inner support, combine the two finite level-one sums into
the explicit Mangoldt-weighted sum used in the inner large-index argument.
Both profiles retain the floor cutoff and the support endpoint. -/
theorem refined_24_joint_weight {x : ℝ} (hx : 1 ≤ x) (hu : x ≤ Real.exp 48) :
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) x n).re) +
        2 * (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) 1 n).re) =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * (144 - Real.log x - Real.log n) := by
  let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hlogx : Real.log x ≤ 48 := by
    have hh := Real.log_le_log hxp hu
    simpa only [Real.log_exp] using hh
  dsimp only
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' := Finset.mem_Icc.mp hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn'.1
  have hnp : 0 < (n : ℝ) := zero_lt_one.trans_le hn1
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.cast_pos.mp hnp)
  have hnx : (n : ℝ) ≤ x := (Nat.cast_le.mpr hn'.2).trans (Nat.floor_le hxp.le)
  have hln0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlnx := Real.log_le_log hnp hnx
  have hdiv : Real.log ((n : ℝ) / x) = Real.log n - Real.log x := Real.log_div hnp.ne' hxp.ne'
  have hprofilex :
    LLS.PaperStatements.triangularKernelProfile 24 ((n : ℝ) / x) =
      48 + Real.log n - Real.log x := by
    unfold LLS.PaperStatements.triangularKernelProfile
    rw [hdiv, abs_of_nonpos (by linarith only [hlnx] : Real.log n - Real.log x ≤ 0)]
    norm_num only
    rw [max_eq_right (by linarith only [hln0, hlogx])]
    ring
  have hprofile1 :
    LLS.PaperStatements.triangularKernelProfile 24 ((n : ℝ) / 1) = 48 - Real.log n := by
    rw [div_one]
    unfold LLS.PaperStatements.triangularKernelProfile
    rw [abs_of_nonneg hln0]
    norm_num only
    exact max_eq_right (by linarith only [hlnx, hlogx])
  have htermx := refined_24_level_one_term (x := x) hxp hn0
  have hterm1 := refined_24_level_one_term (x := 1) (by norm_num only) hn0
  change (K.summand (1 : DirichletCharacter ℂ 1) x n).re = _ at htermx
  change (K.summand (1 : DirichletCharacter ℂ 1) 1 n).re = _ at hterm1
  rw [htermx, hterm1, hprofilex, hprofile1]
  ring

/-- The derivative of the width-24 joint cutoff weight at positive inputs.
The cutoff is a fixed parameter; the formula feeds Abel summation for the
finite combined principal sum. -/
theorem refined_24_joint_deriv {x t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun z : ℝ ↦ (144 - Real.log x - Real.log z) * z ^ (-1 / 2 : ℝ))
      (t ^ (-3 / 2 : ℝ) * ((Real.log x + Real.log t) / 2 - 73)) t := by
  have h :=
    (((Real.hasDerivAt_log ht.ne').neg).const_add (144 - Real.log x)).mul
      (Real.hasDerivAt_rpow_const (p := -1 / 2) (Or.inl ht.ne'))
  have hp := Real.rpow_add ht (-1) (-1 / 2)
  norm_num only at hp
  rw [Real.rpow_neg_one] at hp
  apply h.congr_deriv
  norm_num only
  rw [neg_mul, ← hp]
  simp only [Pi.neg_apply]
  ring

/-- Abel summation for the joint width-24 Mangoldt weight at any cutoff at
least one. The lower endpoint contributes zero because the Chebyshev function
vanishes at one. This identity is used to bound the inner principal sum. -/
theorem refined_24_joint_abel {x : ℝ} (hx : 1 ≤ x) :
    (∑ k ∈ Finset.Ioc ⌊(1 : ℝ)⌋₊ ⌊x⌋₊,
        ((144 - Real.log x - Real.log k) * (k : ℝ) ^ (-1 / 2 : ℝ)) *
          ArithmeticFunction.vonMangoldt k) =
      ((144 - Real.log x - Real.log x) * x ^ (-1 / 2 : ℝ)) * Chebyshev.psi x -
        ∫ t in Set.Ioc 1 x,
          (t ^ (-3 / 2 : ℝ) * ((Real.log x + Real.log t) / 2 - 73)) * Chebyshev.psi t := by
  let f := fun t : ℝ ↦ (144 - Real.log x - Real.log t) * t ^ (-1 / 2 : ℝ)
  let d := fun t : ℝ ↦ t ^ (-3 / 2 : ℝ) * ((Real.log x + Real.log t) / 2 - 73)
  have hd (t : ℝ) (ht : t ∈ Set.Icc 1 x) :=
    refined_24_joint_deriv (x := x) (zero_lt_one.trans_le ht.1)
  have he : Set.EqOn (deriv f) d (Set.Icc 1 x) := fun t ht ↦ (hd t ht).deriv
  have hc : ContinuousOn d (Set.Icc 1 x) := by
    intro t ht
    have hp : 0 < t := zero_lt_one.trans_le ht.1
    exact
      ((Real.continuousAt_rpow_const t (-3 / 2) (Or.inl hp.ne')).mul
          (((continuousAt_const.add (Real.continuousAt_log hp.ne')).div_const 2).sub
            continuousAt_const)).continuousWithinAt
  have hi : MeasureTheory.IntegrableOn (deriv f) (Set.Icc 1 x) := (hc.congr he).integrableOn_Icc
  have h :=
    sum_mul_eq_sub_sub_integral_mul ArithmeticFunction.vonMangoldt (by norm_num only : (0 : ℝ) ≤ 1)
      hx (fun t ht ↦ (hd t ht).differentiableAt) hi
  simp only [← Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_one, mul_zero, sub_zero] at h
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      (fun t ht ↦ congrArg (fun z : ℝ ↦ z * Chebyshev.psi t) (he ⟨ht.1.le, ht.2⟩))] at h
  exact h

/-- On the inner support, the width-24 combined finite principal sum equals
its Abel endpoint minus the Chebyshev integral. The term at one vanishes and
the floor cutoff is unchanged. -/
theorem refined_24_joint_sum_abel {x : ℝ} (hx : 1 ≤ x) (hu : x ≤ Real.exp 48) :
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) x n).re) +
        2 * (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) 1 n).re) =
      ((144 - 2 * Real.log x) * x ^ (-1 / 2 : ℝ)) * Chebyshev.psi x -
        ∫ t in Set.Ioc 1 x,
          (t ^ (-3 / 2 : ℝ) * ((Real.log x + Real.log t) / 2 - 73)) * Chebyshev.psi t := by
  dsimp only
  rw [refined_24_joint_weight hx hu]
  have hfloor : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hz :
    ArithmeticFunction.vonMangoldt 1 / Real.sqrt (1 : ℕ) * (144 - Real.log x - Real.log (1 : ℕ)) =
      0 := by
    norm_num only [ArithmeticFunction.vonMangoldt_apply_one, zero_div, zero_mul]
  rw [Finset.Icc_eq_cons_Ioc hfloor, Finset.sum_cons, hz, zero_add]
  have hsum :
    (∑ n ∈ Finset.Ioc 1 ⌊x⌋₊,
        ArithmeticFunction.vonMangoldt n / Real.sqrt n * (144 - Real.log x - Real.log n)) =
      ∑ n ∈ Finset.Ioc ⌊(1 : ℝ)⌋₊ ⌊x⌋₊,
        ((144 - Real.log x - Real.log n) * (n : ℝ) ^ (-1 / 2 : ℝ)) *
          ArithmeticFunction.vonMangoldt n := by
    simp only [Nat.floor_one]
    apply Finset.sum_congr rfl
    intro n hn
    have hnp : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [neg_div, Real.rpow_neg hnp, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
    ring
  rw [hsum, refined_24_joint_abel hx]
  congr 2
  ring

/-- The explicit primitive for the width-24 joint Chebyshev estimate.
The cutoff parameter is shifted by `exp 36` in the width-18 primitive,
which changes its logarithmic coefficient from 108 to 144. It is used at
the lower integration boundary and at the cutoff. -/
noncomputable def refined_24_jointPrimitive (x t : ℝ) : ℝ :=
  LLS.PaperStatements.triangular18_jointPrimitive (x / Real.exp 36) t

/-- At positive cutoff and integration point, differentiate the width-24
joint primitive. Rewrite the logarithmic parameter of the existing primitive
and retain each Chebyshev error term for the endpoint estimate. -/
theorem refined_24_jointPrimitive_deriv {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    HasDerivAt (refined_24_jointPrimitive x)
      (t ^ (-1 / 2 : ℝ) * ((146 - Real.log x - Real.log t) / 2) -
          (19 / 30 : ℝ) * (t ^ (-3 / 4 : ℝ) * ((146 - Real.log x - Real.log t) / 2)) -
          (63 / 10 : ℝ) * (t ^ (-5 / 4 : ℝ) * ((146 - Real.log x - Real.log t) / 2)) +
        (1839 / 1000 : ℝ) * (t ^ (-3 / 2 : ℝ) * ((Real.log x + Real.log t) / 2 - 73)))
      t := by
  have h := LLS.PaperStatements.triangular18_jointPrimitive_deriv (x := x / Real.exp 36) ht
  rw [Real.log_div hx.ne' (Real.exp_ne_zero 36), Real.log_exp] at h
  apply h.congr_deriv
  ring

/-- Under RH, the width-24 joint Abel integrand on `[16,x]` is bounded by
the negative derivative of the explicit primitive. The support condition makes
the weight derivative nonpositive, so the lower Chebyshev bound applies. -/
theorem refined_24_integrand_le (hRH : RiemannHypothesis) {x t : ℝ} (hx : 1 ≤ x)
    (hu : x ≤ Real.exp 48) (ht : 16 ≤ t) (htx : t ≤ x) :
    t ^ (-3 / 2 : ℝ) * ((Real.log x + Real.log t) / 2 - 73) * Chebyshev.psi t ≤
      -(t ^ (-1 / 2 : ℝ) * ((146 - Real.log x - Real.log t) / 2) -
            (19 / 30 : ℝ) * (t ^ (-3 / 4 : ℝ) * ((146 - Real.log x - Real.log t) / 2)) -
            (63 / 10 : ℝ) * (t ^ (-5 / 4 : ℝ) * ((146 - Real.log x - Real.log t) / 2)) +
          (1839 / 1000 : ℝ) * (t ^ (-3 / 2 : ℝ) * ((Real.log x + Real.log t) / 2 - 73))) := by
  have hp : 0 < t := by linarith only [ht]
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hlx := Real.log_le_log hxp hu
  rw [Real.log_exp] at hlx
  have hlt := Real.log_le_log hp htx
  have hd : t ^ (-3 / 2 : ℝ) * ((Real.log x + Real.log t) / 2 - 73) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hp.le _) (by linarith only [hlx, hlt])
  have hm := mul_le_mul_of_nonpos_left (LLS.PaperStatements.scaleOne_psi_lower hRH ht) hd
  have h1 : t ^ (-3 / 2 : ℝ) * t = t ^ (-1 / 2 : ℝ) := by
    have he := Real.rpow_add hp (-3 / 2) 1
    norm_num only [Real.rpow_one] at he
    simpa only [neg_div] using he.symm
  have h34 : t ^ (-3 / 2 : ℝ) * t ^ (3 / 4 : ℝ) = t ^ (-3 / 4 : ℝ) := by
    rw [← Real.rpow_add hp]
    congr 1
    norm_num only
  have h14 : t ^ (-3 / 2 : ℝ) * t ^ (1 / 4 : ℝ) = t ^ (-5 / 4 : ℝ) := by
    rw [← Real.rpow_add hp]
    congr 1
    norm_num only
  have he :
    (t ^ (-3 / 2 : ℝ) * ((Real.log x + Real.log t) / 2 - 73)) *
        (t - (19 / 30 : ℝ) * t ^ (3 / 4 : ℝ) - (63 / 10 : ℝ) * t ^ (1 / 4 : ℝ) - 1839 / 1000) =
      -(t ^ (-1 / 2 : ℝ) * ((146 - Real.log x - Real.log t) / 2) -
            (19 / 30 : ℝ) * (t ^ (-3 / 4 : ℝ) * ((146 - Real.log x - Real.log t) / 2)) -
            (63 / 10 : ℝ) * (t ^ (-5 / 4 : ℝ) * ((146 - Real.log x - Real.log t) / 2)) +
          (1839 / 1000 : ℝ) * (t ^ (-3 / 2 : ℝ) * ((Real.log x + Real.log t) / 2 - 73))) := by
    calc
      _ =
          -((t ^ (-3 / 2 : ℝ) * t) * ((146 - Real.log x - Real.log t) / 2) -
                (19 / 30 : ℝ) *
                  ((t ^ (-3 / 2 : ℝ) * t ^ (3 / 4 : ℝ)) * ((146 - Real.log x - Real.log t) / 2)) -
                (63 / 10 : ℝ) *
                  ((t ^ (-3 / 2 : ℝ) * t ^ (1 / 4 : ℝ)) * ((146 - Real.log x - Real.log t) / 2)) +
              (1839 / 1000 : ℝ) * (t ^ (-3 / 2 : ℝ) * ((Real.log x + Real.log t) / 2 - 73))) :=
        by ring
      _ = _ := by rw [h1, h34, h14]
  exact hm.trans_eq he

/-- Under RH, the width-24 joint Abel integral is bounded by the difference
of its explicit primitive at 16 and the cutoff. Below 16 use only positivity
of the Chebyshev function, and above 16 integrate the relative lower bound. -/
theorem refined_24_joint_integral_le (hRH : RiemannHypothesis) {x : ℝ} (hx : 16 ≤ x)
    (hu : x ≤ Real.exp 48) :
    (∫ t in (1 : ℝ)..x, t ^ (-3 / 2 : ℝ) * ((Real.log x + Real.log t) / 2 - 73) * Chebyshev.psi t) ≤
      refined_24_jointPrimitive x 16 - refined_24_jointPrimitive x x := by
  let d := fun t : ℝ ↦ t ^ (-3 / 2 : ℝ) * ((Real.log x + Real.log t) / 2 - 73)
  let p := fun t : ℝ ↦
    t ^ (-1 / 2 : ℝ) * ((146 - Real.log x - Real.log t) / 2) -
        (19 / 30 : ℝ) * (t ^ (-3 / 4 : ℝ) * ((146 - Real.log x - Real.log t) / 2)) -
        (63 / 10 : ℝ) * (t ^ (-5 / 4 : ℝ) * ((146 - Real.log x - Real.log t) / 2)) +
      (1839 / 1000 : ℝ) * d t
  have hx1 : (1 : ℝ) ≤ x := by linarith only [hx]
  have hxpos : 0 < x := by linarith only [hx]
  have hlogx : Real.log x ≤ 48 := by
    have h := Real.log_le_log hxpos hu
    simpa only [Real.log_exp] using h
  have hdcont {a b : ℝ} (ha : 1 ≤ a) : ContinuousOn d (Set.Icc a b) := by
    intro t ht
    have hp : 0 < t := by linarith only [ha, ht.1]
    exact
      ((Real.continuousAt_rpow_const t (-3 / 2) (Or.inl hp.ne')).mul
          (((continuousAt_const.add (Real.continuousAt_log hp.ne')).div_const 2).sub
            continuousAt_const)).continuousWithinAt
  have hint {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t ↦ d t * Chebyshev.psi t) MeasureTheory.volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    have h :=
      integrableOn_mul_sum_Icc ArithmeticFunction.vonMangoldt (m := 0) (by linarith only [ha])
        (hdcont (a := a) (b := b) ha).integrableOn_Icc
    simp only [← Chebyshev.psi_eq_sum_Icc] at h
    exact h.mono_set Set.Ioc_subset_Icc_self
  have hcont : ContinuousOn p (Set.Icc 16 x) := by
    intro t ht
    have hp : 0 < t := by linarith only [ht.1]
    have hr (r : ℝ) := Real.continuousAt_rpow_const t r (Or.inl hp.ne')
    have hl := Real.continuousAt_log hp.ne'
    have hk : ContinuousAt (fun z : ℝ ↦ (146 - Real.log x - Real.log z) / 2) t :=
      ((continuousAt_const.sub hl).div_const 2)
    have hdt : ContinuousAt d t :=
      (hr (-3 / 2)).mul (((continuousAt_const.add hl).div_const 2).sub continuousAt_const)
    exact
      ((((hr (-1 / 2)).mul hk).sub (((hr (-3 / 4)).mul hk).const_mul (19 / 30))).sub
            (((hr (-5 / 4)).mul hk).const_mul (63 / 10)) |>.add
          (hdt.const_mul (1839 / 1000))).continuousWithinAt
  have hpint : IntervalIntegrable p MeasureTheory.volume 16 x := hcont.intervalIntegrable_of_Icc hx
  have hprim :
    (∫ t in (16 : ℝ)..x, p t) = refined_24_jointPrimitive x x - refined_24_jointPrimitive x 16 := by
    apply
      intervalIntegral.integral_eq_sub_of_hasDerivAt (f := refined_24_jointPrimitive x) (f' := p)
    · intro t ht
      rw [Set.uIcc_of_le hx] at ht
      exact refined_24_jointPrimitive_deriv hxpos (by linarith only [ht.1])
    · exact hpint
  have hlo : (∫ t in (1 : ℝ)..16, d t * Chebyshev.psi t) ≤ 0 := by
    have hm :=
      intervalIntegral.integral_mono_on (by norm_num only : (1 : ℝ) ≤ 16)
        (hint (by norm_num only) (by norm_num only)) intervalIntegrable_const
        (fun t ht ↦
          show d t * Chebyshev.psi t ≤ (0 : ℝ)
            by
            have hp : 0 < t := by linarith only [ht.1]
            have hl := Real.log_le_log hp (ht.2.trans hx)
            have hd : d t ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hp.le _)
                (by linarith only [hlogx, hl])
            exact mul_nonpos_of_nonpos_of_nonneg hd (Chebyshev.psi_nonneg t))
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_zero] using hm
  have hhi : (∫ t in (16 : ℝ)..x, d t * Chebyshev.psi t) ≤ -(∫ t in (16 : ℝ)..x, p t) := by
    have hm :=
      intervalIntegral.integral_mono_on hx (hint (by norm_num only) hx) hpint.neg
        (fun t ht ↦ refined_24_integrand_le hRH hx1 hu ht.1 ht.2)
    change (∫ t in (16 : ℝ)..x, d t * Chebyshev.psi t) ≤ ∫ t in (16 : ℝ)..x, -p t at hm
    rw [intervalIntegral.integral_neg] at hm
    exact hm
  have hsum :=
    intervalIntegral.integral_add_adjacent_intervals
      (hint (by norm_num only) (by norm_num only : (1 : ℝ) ≤ 16)) (hint (by norm_num only) hx)
  rw [hprim] at hhi
  change (∫ t in (1 : ℝ)..x, d t * Chebyshev.psi t) ≤ _
  linarith only [hlo, hhi, hsum]

/-- At a positive cutoff, evaluate the upper Abel boundary together with the
width-24 primitive. The constant Chebyshev error cancels, leaving the main
square-root term and two explicit power corrections. -/
theorem refined_24_primitive_endpoint {x : ℝ} (hx : 0 < x) :
    ((144 - 2 * Real.log x) * x ^ (-1 / 2 : ℝ)) *
          (x - (19 / 30 : ℝ) * x ^ (3 / 4 : ℝ) - (63 / 10 : ℝ) * x ^ (1 / 4 : ℝ) - 1839 / 1000) +
        refined_24_jointPrimitive x x =
      (292 - 4 * Real.log x) * Real.sqrt x -
          (19 / 30 : ℝ) * (444 - 6 * Real.log x) * x ^ (1 / 4 : ℝ) +
        (63 / 10 : ℝ) * (140 - 2 * Real.log x) * x ^ (-1 / 4 : ℝ) := by
  have h1 : x ^ (-1 / 2 : ℝ) * x = Real.sqrt x := by
    have h := Real.rpow_add hx (-1 / 2) 1
    norm_num only [Real.rpow_one] at h
    simpa only [neg_div, Real.sqrt_eq_rpow] using h.symm
  have h2 : x ^ (-1 / 2 : ℝ) * x ^ (3 / 4 : ℝ) = x ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hx]
    congr 1
    norm_num only
  have h3 : x ^ (-1 / 2 : ℝ) * x ^ (1 / 4 : ℝ) = x ^ (-1 / 4 : ℝ) := by
    rw [← Real.rpow_add hx]
    congr 1
    norm_num only
  calc
    _ =
        (144 - 2 * Real.log x) * (x ^ (-1 / 2 : ℝ) * x) + (148 - 2 * Real.log x) * Real.sqrt x -
          (19 / 30 : ℝ) *
            ((144 - 2 * Real.log x) * (x ^ (-1 / 2 : ℝ) * x ^ (3 / 4 : ℝ)) +
              (300 - 4 * Real.log x) * x ^ (1 / 4 : ℝ)) -
          (63 / 10 : ℝ) *
            ((144 - 2 * Real.log x) * (x ^ (-1 / 2 : ℝ) * x ^ (1 / 4 : ℝ)) +
              (-284 + 4 * Real.log x) * x ^ (-1 / 4 : ℝ)) :=
      by
      dsimp only [refined_24_jointPrimitive, LLS.PaperStatements.triangular18_jointPrimitive]
      rw [Real.log_div hx.ne' (Real.exp_ne_zero 36), Real.log_exp, ← Real.sqrt_eq_rpow]
      ring
    _ = _ := by
      rw [h1, h2, h3]; ring

/-- The width-24 joint primitive at 16 is at most 1600 when the cutoff is at
least one. Evaluate the existing endpoint formula after the logarithmic
shift and use nonnegativity of both logarithms. -/
theorem refined_24_primitive_sixteen_le {x : ℝ} (hx : 1 ≤ x) :
    refined_24_jointPrimitive x 16 ≤ 1600 := by
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have h := LLS.PaperStatements.joint_primitive_sixteen (x / Real.exp 36)
  rw [Real.log_div hxp.ne' (Real.exp_ne_zero 36), Real.log_exp] at h
  have hlx := Real.log_nonneg hx
  have hl16 : 0 ≤ Real.log (16 : ℝ) := Real.log_nonneg (by norm_num only)
  change LLS.PaperStatements.triangular18_jointPrimitive (x / Real.exp 36) 16 ≤ _
  linarith only [h, hlx, hl16]

/-- Under RH, for cutoffs between 16 and `exp 48`, the combined width-24
finite principal sum has the explicit inner lower bound. Combine Abel
summation, the Chebyshev lower estimate and both primitive endpoints; discard
the remaining nonnegative inverse-fourth-root contribution. -/
theorem refined_24_joint_lower (hRH : RiemannHypothesis) {x : ℝ} (hx : 16 ≤ x)
    (hu : x ≤ Real.exp 48) :
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
    (292 - 4 * Real.log x) * Real.sqrt x -
        (19 / 30 : ℝ) * (444 - 6 * Real.log x) * x ^ (1 / 4 : ℝ) -
        1600 ≤
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) x n).re) +
        2 * (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) 1 n).re) := by
  have hx1 : (1 : ℝ) ≤ x := by linarith only [hx]
  have hxpos : 0 < x := by linarith only [hx]
  have hlog : Real.log x ≤ 48 := by
    have h := Real.log_le_log hxpos hu
    simpa only [Real.log_exp] using h
  have hw : 0 ≤ (144 - 2 * Real.log x) * x ^ (-1 / 2 : ℝ) :=
    mul_nonneg (by linarith only [hlog]) (Real.rpow_nonneg hxpos.le _)
  have hpsi := mul_le_mul_of_nonneg_left (LLS.PaperStatements.scaleOne_psi_lower hRH hx) hw
  have hint := refined_24_joint_integral_le hRH hx hu
  have he := refined_24_primitive_endpoint hxpos
  have he16 := refined_24_primitive_sixteen_le hx1
  have hrest : 0 ≤ (63 / 10 : ℝ) * (140 - 2 * Real.log x) * x ^ (-1 / 4 : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num only) (by linarith only [hlog]))
      (Real.rpow_nonneg hxpos.le _)
  dsimp only
  rw [refined_24_joint_sum_abel hx1 hu, ← intervalIntegral.integral_of_le hx1]
  nlinarith only [hpsi, hint, he, he16, hrest]

/-- Under GRH, a strict width-24 inner gap forces a prime at or below the
cutoff that either divides the modulus or lies outside the subgroup. Combine
the finite principal lower bound with the no-witness numerical comparison. -/
theorem refined_24_exists_prime_inner {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 16 ≤ x)
    (hu : x ≤ Real.exp 48)
    (hgap :
      130000000000 * (Real.sqrt x + Real.sqrt x⁻¹) +
          500000000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
          2 * (130000000000 + 500000000) +
          ((H.index : ℝ) - 1) * ((96 - Real.log x) * Real.log q + 16000) <
        (H.index : ℝ) *
          ((292 - 4 * Real.log x) * Real.sqrt x -
            (19 / 30 : ℝ) * (444 - 6 * Real.log x) * x ^ (1 / 4 : ℝ) -
            1600)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ (p ∣ q ∨ ¬NumberTheory.residueInSubgroup q H p) := by
  classical
  by_contra hnone
  have hlarge (p : ℕ) (hp : p.Prime) (hd : p ∣ q) : x < (p : ℝ) := by
    by_contra h
    exact hnone ⟨p, hp, le_of_not_gt h, Or.inl hd⟩
  have hsmall (p : ℕ) (hp : p.Prime) (_ : ¬p ∣ q) (hle : (p : ℝ) ≤ x) :
    NumberTheory.residueInSubgroup q H p := by
    by_contra hout
    exact hnone ⟨p, hp, hle, Or.inr hout⟩
  have hx1 : (1 : ℝ) ≤ x := by linarith only [hx]
  have hlog : Real.log x ≤ 48 := by
    have h := Real.log_le_log (by linarith only [hx]) hu
    simpa only [Real.log_exp] using h
  have hlower := refined_24_joint_lower hGRH.riemann hx hu
  have hl := mul_le_mul_of_nonneg_left hlower (Nat.cast_nonneg H.index)
  have hc := refined_24_numeric_comparison H hGRH hx1 (by linarith only [hx]) hlarge hsmall
  dsimp only at hl hc
  rw [max_eq_right (by linarith only [hlog] : 0 ≤ 48 - Real.log x)] at hc
  nlinarith only [hl, hc, hgap]

/-- Under GRH, a subgroup of index at least `10^16` has an excluded or
dividing prime below the paper cutoff whenever the cutoff lies in the inner
width-24 support. The certified scalar gap supplies the strict inequality. -/
theorem refined_24_prime_cutoff_inner {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {K : ℝ} (hL : 1000 ≤ Real.log q)
    (hK : 0 ≤ K) (hK3 : K ≤ 3) (hh : (10000000000000000 : ℝ) ≤ H.index)
    (hy : Real.log (refinedPaperBound (Real.log q) K) ≤ 48) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ refinedPaperBound (Real.log q) K ∧
        (p ∣ q ∨ ¬NumberTheory.residueInSubgroup q H p) := by
  let L := Real.log q
  let r := refinedPaperRoot L K
  let x := refinedPaperBound L K
  have hrlo := refined_root_lower (show 0 ≤ L by linarith only [hL]) hK
  have hr : 0 < r := refined_paper_root_positive L K
  have hx : x = r ^ 4 := rfl
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  have hx16 : 16 ≤ x := by
    have hs : (4 : ℝ) ≤ r ^ 2 := by
      dsimp only [r]; linarith only [hrlo, hL]
    have hp := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 4) hs 2
    rw [hx]
    nlinarith only [hp]
  have hroot : Real.sqrt x = r ^ 2 := by
    rw [hx]
    have he : r ^ 4 = (r ^ 2) ^ 2 := by ring
    rw [he, Real.sqrt_sq hr2]
  have hquarter : x ^ (1 / 4 : ℝ) = r := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    norm_num only [Real.rpow_one]
  have hrootInv : Real.sqrt x⁻¹ = (r ^ 2)⁻¹ := by rw [Real.sqrt_inv, hroot]
  have hquarterInv : (x⁻¹) ^ (1 / 4 : ℝ) = r⁻¹ := by
    rw [Real.inv_rpow (by linarith only [hx16] : 0 ≤ x), hquarter]
  have hu : x ≤ Real.exp 48 := (Real.log_le_iff_le_exp (by linarith only [hx16])).mp hy
  have hg := refined_cutoff_inner_index_all hL hK hK3 hh hy
  apply refined_24_exists_prime_inner H hGRH hx16 hu
  rw [hroot, hrootInv, hquarter, hquarterInv]
  exact hg

/-- Under GRH, an odd input with logarithm at least 1000, large Fermat index,
and paper cutoff inside the width-24 support has a rejecting prime within
the piecewise cutoff. A divisor cannot pass and a passing base belongs to
the Fermat subgroup. -/
theorem refined_24_inner_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hi : 10 ^ 16 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 1000 ≤ Real.log n)
    (hy : Real.log (refinedPaperBound (Real.log n) (refinedPaperAllowance (Real.log n))) ≤ 48) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ refinedPaperCoefficient (Real.log n) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  have hiR : (10000000000000000 : ℝ) ≤ ((PrimeTest.fermatSubgroup n).index : ℝ) := by
    exact_mod_cast hi
  have ha := refined_allowance_range (Real.log n)
  obtain ⟨p, hp, hb, hout⟩ :=
    refined_24_prime_cutoff_inner (PrimeTest.fermatSubgroup n) hGRH hL ha.1 ha.2 hiR hy
  refine ⟨p, hp, ?_, ?_⟩
  · rw [refined_piecewise_high hL]
    exact hb
  · intro hpass
    rcases hout with hd | hout
    · have hcop :=
        (ZMod.isUnit_iff_coprime p n).mp (PrimeTest.strongMillerRabinPass_isUnit hn ho hpass)
      exact (hp.coprime_iff_not_dvd.mp hcop) hd
    · exact hout (PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn ho hpass)

/-- Under GRH in the outer width-24 support, a finite principal lower bound
and a strict numerical gap force a prime dividing the modulus or outside the
subgroup. The scale-one principal sum is nonnegative and may be discarded. -/
theorem refined_24_exists_prime_outer {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x B : ℝ} (hx : 1 ≤ x)
    (hy : 48 ≤ Real.log x)
    (hlower :
      let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
      B ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) x n).re)
    (hgap :
      130000000000 * (Real.sqrt x + Real.sqrt x⁻¹) +
          500000000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
          2 * (130000000000 + 500000000) +
          ((H.index : ℝ) - 1) * (48 * Real.log q + 16000) <
        (H.index : ℝ) * B) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ (p ∣ q ∨ ¬NumberTheory.residueInSubgroup q H p) := by
  classical
  by_contra hnone
  have hlarge (p : ℕ) (hp : p.Prime) (hd : p ∣ q) : x < (p : ℝ) := by
    by_contra h
    exact hnone ⟨p, hp, le_of_not_gt h, Or.inl hd⟩
  have hsmall (p : ℕ) (hp : p.Prime) (_ : ¬p ∣ q) (hle : (p : ℝ) ≤ x) :
    NumberTheory.residueInSubgroup q H p := by
    by_contra hout
    exact hnone ⟨p, hp, hle, Or.inr hout⟩
  let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
  have hnonneg : 0 ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) 1 n).re := by
    apply Finset.sum_nonneg
    intro n hn
    exact LLS.PaperStatements.MellinKernel.principal_summand_re_nonneg K (by norm_num only) n
  have hl := mul_le_mul_of_nonneg_left hlower (Nat.cast_nonneg H.index)
  have hp := mul_nonneg (Nat.cast_nonneg H.index : (0 : ℝ) ≤ H.index) hnonneg
  have hc := refined_24_numeric_comparison H hGRH hx (by linarith only [hx]) hlarge hsmall
  dsimp only at hl hc
  rw [max_eq_left (by linarith only [hy] : 48 - Real.log x ≤ 0)] at hc
  nlinarith only [hl, hp, hc, hgap]

/-- On the logarithmic interval `[-36, 0]`, a width-24 triangular profile is
the sum of four thirds of the central width-18 profile and one third of the
width-18 profile shifted by 36. Both profiles retain their support endpoints. -/
theorem refined_24_outer_profile_split {u : ℝ} (hu : 0 < u) (hl : Real.exp (-36) ≤ u) (hr : u ≤ 1) :
    LLS.PaperStatements.triangularKernelProfile 24 u =
      (4 / 3 : ℝ) * LLS.PaperStatements.triangularKernelProfile 18 u +
        (1 / 3 : ℝ) * LLS.PaperStatements.triangularKernelProfile 18 (u * Real.exp 36) := by
  have hlogl : -36 ≤ Real.log u := by
    have h := Real.log_le_log (Real.exp_pos (-36)) hl
    simpa only [Real.log_exp] using h
  have hlogr : Real.log u ≤ 0 := Real.log_nonpos hu.le hr
  have hshift : Real.log (u * Real.exp 36) = Real.log u + 36 := by
    rw [Real.log_mul hu.ne' (Real.exp_ne_zero 36), Real.log_exp]
  unfold LLS.PaperStatements.triangularKernelProfile
  rw [hshift, abs_of_nonpos hlogr, abs_of_nonneg (by linarith only [hlogl])]
  norm_num only
  rw [max_eq_right (by linarith only [hlogl]), max_eq_right (by linarith only [hlogl]),
    max_eq_right (by linarith only [hlogr])]
  ring

/-- On the interval from `exp(-36)x` to `x`, the width-24 level-one
summand splits into two width-18 summands at scales `x` and `exp(-36)x`.
The pointwise profile identity preserves the finite cutoff. -/
theorem refined_24_outer_term_split {x : ℝ} (hx : 0 < x) {n : ℕ} (hl : Real.exp (-36) * x ≤ (n : ℝ))
    (hr : (n : ℝ) ≤ x) :
    let K24 := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
    let K18 := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    (K24.summand (1 : DirichletCharacter ℂ 1) x n).re =
      (4 / 3 : ℝ) * (K18.summand (1 : DirichletCharacter ℂ 1) x n).re +
        (1 / 3 : ℝ) * (K18.summand (1 : DirichletCharacter ℂ 1) (Real.exp (-36) * x) n).re := by
  have hn : (0 : ℝ) < n := (mul_pos (Real.exp_pos (-36)) hx).trans_le hl
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.cast_pos.mp hn)
  have hu : 0 < (n : ℝ) / x := div_pos hn hx
  have hul : Real.exp (-36) ≤ (n : ℝ) / x := (le_div_iff₀ hx).mpr hl
  have hur : (n : ℝ) / x ≤ 1 := (div_le_one hx).mpr hr
  have hp := refined_24_outer_profile_split hu hul hur
  have he : (n : ℝ) / (Real.exp (-36) * x) = (n : ℝ) / x * Real.exp 36 := by
    rw [Real.exp_neg]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc, mul_left_comm, mul_comm]
  dsimp only
  rw [refined_24_level_one_term hx hn0, LLS.PaperStatements.triangular18_level_one_term hx hn0,
    LLS.PaperStatements.triangular18_level_one_term (mul_pos (Real.exp_pos (-36)) hx) hn0, he, hp]
  ring

/-- Under RH, the width-18 level-one upper-support sum has its explicit Abel
main term and error lower bound at every positive scale. Take the lower side
of the existing absolute error estimate and normalize by the square root. -/
theorem refined_18_upper_support_lower (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x) :
    Real.sqrt x * (4 * Real.exp 18 - 76) - 13 * (12 * Real.exp 9 - 48) * x ^ (1 / 4 : ℝ) ≤
      ∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊Real.exp 36 * x⌋₊,
        ((LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
            (1 : DirichletCharacter ℂ 1) x k).re := by
  have he :=
    Analysis.triangular18_upper_mangoldt_error_le hx (fun t ht ↦ LLS.psi_error_le_thirteen hRH ht)
  rw [Analysis.triangular18_upper_scaled_main_integral hx] at he
  have hl := (abs_le.mp he).1
  have hmain :
    x * (4 * Real.exp 18 - 76) - 13 * (12 * Real.exp 9 - 48) * x ^ (3 / 4 : ℝ) ≤
      ∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊Real.exp 36 * x⌋₊,
        ((36 - Real.log ((k : ℝ) / x)) * ((k : ℝ) / x) ^ (-1 / 2 : ℝ)) *
          ArithmeticFunction.vonMangoldt k := by
    linarith only [hl]
  rw [LLS.PaperStatements.triangular18_level_one_upper_sum hx]
  have hs := Real.sqrt_pos.mpr hx
  have hp : x ^ (3 / 4 : ℝ) / Real.sqrt x = x ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hx]
    norm_num only
  have hd := div_le_div_of_nonneg_right hmain hs.le
  rw [sub_div, mul_div_assoc (13 * (12 * Real.exp 9 - 48)), hp] at hd
  have heq : x * (4 * Real.exp 18 - 76) / Real.sqrt x = Real.sqrt x * (4 * Real.exp 18 - 76) := by
    nth_rw 1 [← Real.sq_sqrt hx.le]
    field_simp [hs.ne']
  simpa only [heq] using hd

/-- At a positive cutoff, the finite width-24 principal sum dominates a
combination of the width-18 lower- and upper-support sums on the shared
interval. Nonnegative terms outside the interval can only increase it. -/
theorem refined_24_outer_sum_split {x : ℝ} (hx : 0 < x) :
    let K24 := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
    let K18 := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    let y := Real.exp (-36) * x
    (4 / 3 : ℝ) * (∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊x⌋₊, (K18.summand (1 : DirichletCharacter ℂ 1) x n).re) +
        (1 / 3 : ℝ) *
          (∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊x⌋₊, (K18.summand (1 : DirichletCharacter ℂ 1) y n).re) ≤
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (K24.summand (1 : DirichletCharacter ℂ 1) x n).re := by
  let K24 := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
  let K18 := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let y := Real.exp (-36) * x
  have hy : 0 < y := mul_pos (Real.exp_pos (-36)) hx
  have hsub : Finset.Ioc ⌊y⌋₊ ⌊x⌋₊ ⊆ Finset.Icc 1 ⌊x⌋₊ := by
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    exact
      Finset.mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hn'.1)), hn'.2⟩
  have hsum :
    (∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊x⌋₊, (K24.summand (1 : DirichletCharacter ℂ 1) x n).re) =
      (4 / 3 : ℝ) *
          (∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊x⌋₊, (K18.summand (1 : DirichletCharacter ℂ 1) x n).re) +
        (1 / 3 : ℝ) *
          (∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊x⌋₊, (K18.summand (1 : DirichletCharacter ℂ 1) y n).re) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hm := Finset.mem_Ioc.mp hn
    have hl : y ≤ (n : ℝ) := (Nat.floor_lt hy.le).mp hm.1 |>.le
    have hr : (n : ℝ) ≤ x := (Nat.cast_le.mpr hm.2).trans (Nat.floor_le hx.le)
    exact refined_24_outer_term_split hx hl hr
  have h :
    (∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊x⌋₊, (K24.summand (1 : DirichletCharacter ℂ 1) x n).re) ≤
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (K24.summand (1 : DirichletCharacter ℂ 1) x n).re :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n hn _ ↦ LLS.PaperStatements.MellinKernel.principal_summand_re_nonneg (q := 1) K24 hx n)
  dsimp only
  rw [← hsum]
  exact h

/-- Under RH, the width-24 finite principal sum has an explicit lower bound
at every positive cutoff. Combine the two width-18 support estimates after
rescaling and retain the exponentially small lower-endpoint correction. -/
theorem refined_24_outer_lower_precise (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x) :
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
    (92 - 20 * Real.exp (-18)) * Real.sqrt x - 2000 * x ^ (1 / 4 : ℝ) ≤
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) x n).re := by
  let y := Real.exp (-36) * x
  have hy : 0 < y := mul_pos (Real.exp_pos (-36)) hx
  have hscale : Real.exp 36 * y = x := by
    dsimp only [y]
    rw [← mul_assoc, ← Real.exp_add]
    norm_num only [Real.exp_zero, one_mul]
  have hsqrty : Real.sqrt y = Real.exp (-18) * Real.sqrt x := by
    dsimp only [y]
    rw [Real.sqrt_mul (Real.exp_pos (-36)).le, Real.sqrt_eq_rpow, ← Real.exp_mul]
    norm_num only
  have hpowy : y ^ (1 / 4 : ℝ) = Real.exp (-9) * x ^ (1 / 4 : ℝ) := by
    dsimp only [y]
    rw [Real.mul_rpow (Real.exp_pos (-36)).le hx.le, ← Real.exp_mul]
    norm_num only
  have he18 : Real.exp (-18) * Real.exp 18 = 1 := by
    rw [← Real.exp_add]
    norm_num only [Real.exp_zero]
  have he9 : Real.exp (-9) * Real.exp 9 = 1 := by
    rw [← Real.exp_add]
    norm_num only [Real.exp_zero]
  have hlo := LLS.PaperStatements.triangular18_level_one_cutoff_sum_lower_of_rh hRH hx
  have hhi := refined_18_upper_support_lower hRH hy
  rw [hscale, hsqrty, hpowy] at hhi
  have hsum := refined_24_outer_sum_split hx
  dsimp only at hsum ⊢
  have hm1 := mul_le_mul_of_nonneg_left hlo (by norm_num only : (0 : ℝ) ≤ 4 / 3)
  have hm2 := mul_le_mul_of_nonneg_left hhi (by norm_num only : (0 : ℝ) ≤ 1 / 3)
  dsimp only [y] at hm2
  have h18 := congrArg (fun z : ℝ ↦ z * Real.sqrt x) he18
  have h9 := congrArg (fun z : ℝ ↦ z * x ^ (1 / 4 : ℝ)) he9
  have hxpow := Real.rpow_nonneg hx.le (1 / 4)
  have hpos := mul_nonneg (Real.exp_pos (-9)).le hxpow
  nlinarith only [hsum, hm1, hm2, h18, h9, hxpow, hpos]

/-- A rational bound for the lower-endpoint correction in the width-24 outer
sum. A finite exponential series lower bound at 18 gives the required
reciprocal estimate. -/
theorem refined_24_exp_neg_eighteen : Real.exp (-18) ≤ (1 / 2000 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 18) 5
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_one, pow_zero, pow_succ, div_one, add_zero] at h
  have he : (2000 : ℝ) ≤ Real.exp 18 := by linarith only [h]
  rw [Real.exp_neg, one_div]
  exact (inv_le_inv₀ (Real.exp_pos 18) (by norm_num only : (0 : ℝ) < 2000)).mpr he

/-- Under RH, the width-24 finite principal sum has a rational explicit lower
bound at positive cutoff. Replace the exponential endpoint correction by
`1/100` in the previously proved precise estimate. -/
theorem refined_24_outer_lower (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x) :
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 24)
    (9199 / 100 : ℝ) * Real.sqrt x - 2000 * x ^ (1 / 4 : ℝ) ≤
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) x n).re := by
  have h := refined_24_outer_lower_precise hRH hx
  have he := mul_le_mul_of_nonneg_right refined_24_exp_neg_eighteen (Real.sqrt_nonneg x)
  dsimp only at h ⊢
  nlinarith only [h, he]

/-- At the paper cutoff outside width-24 support and index at least `10^16`,
the numerical cost is strictly below the rational finite-sum lower bound.
The small loss in the main coefficient is absorbed by the certified gap. -/
theorem refined_24_outer_index_gap {L K h : ℝ} (hL : 1000 ≤ L) (hK : 0 ≤ K) (hK3 : K ≤ 3)
    (hh : 10000000000000000 ≤ h) (hy : 48 ≤ Real.log (refinedPaperBound L K)) :
    (130000000000 : ℝ) * (refinedPaperRoot L K ^ 2 + (refinedPaperRoot L K ^ 2)⁻¹) +
        500000000 * (refinedPaperRoot L K + (refinedPaperRoot L K)⁻¹) +
        2 * (130000000000 + 500000000) +
        (h - 1) * (48 * L + 16000) <
      h * ((9199 / 100 : ℝ) * refinedPaperRoot L K ^ 2 - 2000 * refinedPaperRoot L K) := by
  have hbig := refined_cutoff_outer_scale hL hK hK3 hy
  have hL0 : 0 ≤ L := by linarith only [hbig]
  have hrlo := refined_root_lower hL0 hK
  have hrhi := refined_root_upper hL hK hK3
  have hcost := refined_large_index_cost hL hrlo hrhi hh
  rw [Real.sqrt_sq (refined_paper_root_positive L K).le] at hcost
  have hs : Real.sqrt L ≤ L / 100000 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith only [hbig, sq_nonneg (L - 10000000000)]
  have ht :=
    (refined_root_sqrt_cap hL hK hK3).trans
      (mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 151 / 200))
  have hgap :
    48 * L + 16000 + L / 1000 <
      (9199 / 100 : ℝ) * refinedPaperRoot L K ^ 2 - 2000 * refinedPaperRoot L K := by
    nlinarith only [hbig, hrlo, ht]
  have hmul := mul_lt_mul_of_pos_left hgap (show 0 < h by linarith only [hh])
  nlinarith only [hcost, hmul, hbig]

/-- Under GRH, a subgroup of index at least `10^16` has an excluded or
dividing prime below the paper cutoff in the outer width-24 support. Combine
the proved finite-sum lower bound with the certified rational scalar gap. -/
theorem refined_24_prime_cutoff_outer {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {K : ℝ} (hL : 1000 ≤ Real.log q)
    (hK : 0 ≤ K) (hK3 : K ≤ 3) (hh : (10000000000000000 : ℝ) ≤ H.index)
    (hy : 48 ≤ Real.log (refinedPaperBound (Real.log q) K)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ refinedPaperBound (Real.log q) K ∧
        (p ∣ q ∨ ¬NumberTheory.residueInSubgroup q H p) := by
  let L := Real.log q
  let r := refinedPaperRoot L K
  let x := refinedPaperBound L K
  have hrlo := refined_root_lower (show 0 ≤ L by linarith only [hL]) hK
  have hr : 0 < r := refined_paper_root_positive L K
  have hx : x = r ^ 4 := rfl
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  have hx1 : 1 ≤ x := by
    have hs : (1 : ℝ) ≤ r ^ 2 := by
      dsimp only [r]; linarith only [hrlo, hL]
    have hp := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 1) hs 2
    rw [hx]
    nlinarith only [hp]
  have hroot : Real.sqrt x = r ^ 2 := by
    rw [hx]
    have he : r ^ 4 = (r ^ 2) ^ 2 := by ring
    rw [he, Real.sqrt_sq hr2]
  have hquarter : x ^ (1 / 4 : ℝ) = r := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    norm_num only [Real.rpow_one]
  have hrootInv : Real.sqrt x⁻¹ = (r ^ 2)⁻¹ := by rw [Real.sqrt_inv, hroot]
  have hquarterInv : (x⁻¹) ^ (1 / 4 : ℝ) = r⁻¹ := by
    rw [Real.inv_rpow (by linarith only [hx1] : 0 ≤ x), hquarter]
  have hlower := refined_24_outer_lower hGRH.riemann (by linarith only [hx1] : 0 < x)
  have hg := refined_24_outer_index_gap hL hK hK3 hh hy
  apply refined_24_exists_prime_outer H hGRH hx1 hy hlower
  rw [hroot, hrootInv, hquarter, hquarterInv]
  exact hg

/-- Under GRH, an odd input with logarithm at least 1000, large Fermat index,
and paper cutoff outside the width-24 support has a rejecting prime within
the piecewise cutoff. Divisors and bases outside the Fermat subgroup reject. -/
theorem refined_24_outer_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hi : 10 ^ 16 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 1000 ≤ Real.log n)
    (hy : 48 ≤ Real.log (refinedPaperBound (Real.log n) (refinedPaperAllowance (Real.log n)))) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ refinedPaperCoefficient (Real.log n) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  have hiR : (10000000000000000 : ℝ) ≤ ((PrimeTest.fermatSubgroup n).index : ℝ) := by
    exact_mod_cast hi
  have ha := refined_allowance_range (Real.log n)
  obtain ⟨p, hp, hb, hout⟩ :=
    refined_24_prime_cutoff_outer (PrimeTest.fermatSubgroup n) hGRH hL ha.1 ha.2 hiR hy
  refine ⟨p, hp, ?_, ?_⟩
  · rw [refined_piecewise_high hL]
    exact hb
  · intro hpass
    rcases hout with hd | hout
    · have hcop :=
        (ZMod.isUnit_iff_coprime p n).mp (PrimeTest.strongMillerRabinPass_isUnit hn ho hpass)
      exact (hp.coprime_iff_not_dvd.mp hcop) hd
    · exact hout (PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn ho hpass)

/-- Under GRH, every odd composite with logarithm at least 1000 has a rejecting
prime bounded by the piecewise coefficient. Split by subgroup index and then use
the inner or outer width-24 witness. -/
theorem refined_piecewise_high_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (1000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ refinedPaperCoefficient (Real.log n) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 16
  · exact refined_index16_witness hn ho hc hi hGRH hL
  · have hlarge : 10 ^ 16 ≤ (PrimeTest.fermatSubgroup n).index := Nat.le_of_lt (lt_of_not_ge hi)
    by_cases hy :
      Real.log (refinedPaperBound (Real.log n) (refinedPaperAllowance (Real.log n))) ≤ 48
    · exact refined_24_inner_witness hn ho hlarge hGRH hL hy
    · exact refined_24_outer_witness hn ho hlarge hGRH hL (le_of_not_ge hy)

end PseudoPrime.PrimeTestBounds.MillerRabin
