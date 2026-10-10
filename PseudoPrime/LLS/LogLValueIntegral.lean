/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.LogarithmicShiftIntegral
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ShiftedLogMellinInversion
public import PseudoPrime.LLS.PaperDefinitions
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ShiftedMellin
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.MainIntegral

/-!
# Shifted Perron representation of logarithmic L-value sums

Shifted logarithmic-derivative integrals represent the finite arithmetic sums in
Lemmas 2.5 and 2.6. For zeta, evaluate the combined pole and origin terms and bound
the zero and gamma integrals to obtain the complete formula and its two real errors.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For any character and real x, the logarithmic L-value finite sum is the integral of the
n^(-sigma)-weighted logarithmic sum over sigma>1, divided by log x.
The Mangoldt coefficient at one vanishes, and integration supplies 1/(n log n).
This connects the shifted arithmetic formula to the sum in Lemma 2.5. -/
theorem characterLogLValueSum_eq_integrated_shift {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) :
    characterLogLValueSum χ x =
      (∫ σ : ℝ in Set.Ioi 1,
          AnalyticNumberTheory.General.logarithmicWeightedSum
            (AnalyticNumberTheory.General.shiftedLSeriesCoefficient
              (fun n ↦ χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) σ)
            x) /
        (Real.log x : ℂ) := by
  have ha : χ ((1 : ℕ) : ZMod q) * (ArithmeticFunction.vonMangoldt 1 : ℂ) = 0 := by
    rw [ArithmeticFunction.vonMangoldt_apply_one, Complex.ofReal_zero, mul_zero]
  rw [AnalyticNumberTheory.General.integral_logarithmicWeightedSum_shifted _ ha]
  rw [Finset.sum_div]
  unfold characterLogLValueSum
  apply Finset.sum_congr rfl
  intro n _
  rw [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_natCast]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- For x>0 and a positive vertical abscissa tau, the logarithmic L-value finite sum equals
the iterated shifted logarithmic-derivative integral, normalized by log x.
Apply shifted Mellin inversion for every sigma>1, then integrate the arithmetic identity.
This is the contour representation preceding zero and gamma residue evaluation in Lemma 2.5. -/
theorem characterLogLValueSum_eq_integrated_logContour {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x τ : ℝ} (hx : 0 < x) (hτ : 0 < τ) :
    characterLogLValueSum χ x =
      (∫ σ : ℝ in Set.Ioi 1,
          (2 * Real.pi : ℝ)⁻¹ •
            ∫ y : ℝ,
              AnalyticNumberTheory.DirichletLFunction.shiftedLogContourKernel χ x σ
                ((τ : ℂ) + y * Complex.I)) /
        (Real.log x : ℂ) := by
  rw [characterLogLValueSum_eq_integrated_shift]
  congr 1
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro σ hσ
  exact
    AnalyticNumberTheory.DirichletLFunction.shifted_logarithmic_sum_eq_integral χ hx (le_of_lt hσ)
      hτ

/-- For every real cutoff x, the unsigned logarithmic sum is the integral of the
shifted Mangoldt sum over sigma > 1, divided by log x, as an equality in complex numbers.
Integrate the finite coefficients; the term at one vanishes, and the other integrals
supply 1/(n log n). This is the arithmetic integral interface for Lemma 2.6,
before evaluating the pole at one, nontrivial zeros and gamma contributions. -/
theorem logLValueSum_eq_integrated_shift (x : ℝ) :
    (logLValueSum x : ℂ) =
      (∫ σ : ℝ in Set.Ioi 1,
          AnalyticNumberTheory.General.logarithmicWeightedSum
            (AnalyticNumberTheory.General.shiftedLSeriesCoefficient
              (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) σ)
            x) /
        (Real.log x : ℂ) := by
  have ha : (ArithmeticFunction.vonMangoldt 1 : ℂ) = 0 := by
    rw [ArithmeticFunction.vonMangoldt_apply_one, Complex.ofReal_zero]
  rw [AnalyticNumberTheory.General.integral_logarithmicWeightedSum_shifted _ ha, Finset.sum_div]
  unfold logLValueSum
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast]
  ring

/-- At modulus one, the character logarithmic sum is the complex embedding of the
unsigned real sum. Every residue class is one and its character value is one.
This identifies the zeta arithmetic sum when specializing shifted Mellin inversion. -/
theorem characterLogLValueSum_modOne_eq (x : ℝ) :
    characterLogLValueSum (1 : DirichletCharacter ℂ 1) x = (logLValueSum x : ℂ) := by
  unfold characterLogLValueSum logLValueSum
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [Subsingleton.elim (n : ZMod 1) 1, map_one, one_mul]

/-- For x > 0 and a positive vertical abscissa tau, express the unsigned logarithmic
sum as the iterated shifted zeta logarithmic-derivative integral divided by log x.
Specialize character Mellin inversion to modulus one and identify its L-function with zeta.
This contour representation is used to identify the shifted pole at 1-sigma,
the nontrivial-zero contribution, and the gamma contribution in Lemma 2.6. -/
theorem logLValueSum_eq_integrated_logContour {x τ : ℝ} (hx : 0 < x) (hτ : 0 < τ) :
    (logLValueSum x : ℂ) =
      (∫ σ : ℝ in Set.Ioi 1,
          (2 * Real.pi : ℝ)⁻¹ •
            ∫ y : ℝ,
              -deriv riemannZeta ((σ : ℂ) + ((τ : ℂ) + y * Complex.I)) /
                    riemannZeta ((σ : ℂ) + ((τ : ℂ) + y * Complex.I)) *
                  (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
                ((τ : ℂ) + y * Complex.I) ^ 2) /
        (Real.log x : ℂ) := by
  rw [← characterLogLValueSum_modOne_eq x, characterLogLValueSum_eq_integrated_logContour _ hx hτ]
  simp only [AnalyticNumberTheory.DirichletLFunction.shiftedLogContourKernel,
    DirichletCharacter.LFunction_modOne_eq]

/-- Under RH and x > 1, the unsigned logarithmic finite sum equals the integral,
over sigma > 1, of the complete shifted pole, logarithmic-derivative and zero-residue
formula, divided by log x. Apply the shifted explicit formula inside the finite-sum
integral. Keep the pole and logarithmic-derivative terms combined because their
separate integrals diverge at one. This is the endpoint interface for Lemma 2.6. -/
theorem logLValueSum_eq_integrated_residues (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    (logLValueSum x : ℂ) =
      (∫ σ : ℝ in Set.Ioi 1,
          (x : ℂ) ^ (1 - (σ : ℂ)) / ((σ : ℂ) - 1) ^ 2 -
            logDeriv riemannZeta (σ : ℂ) * (Real.log x : ℂ) -
            deriv (logDeriv riemannZeta) (σ : ℂ) -
            (∑' ρ : AnalyticNumberTheory.RiemannXi.Zero,
              (analyticOrderNatAt AnalyticNumberTheory.RiemannXi.riemannXi (ρ : ℂ) : ℂ) *
                  (x : ℂ) ^ ((ρ : ℂ) - (σ : ℂ)) /
                ((ρ : ℂ) - (σ : ℂ)) ^ 2) -
            AnalyticNumberTheory.General.gammaShiftSum x 2 σ) /
        (Real.log x : ℂ) := by
  rw [logLValueSum_eq_integrated_shift]
  congr 1
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro σ hσ
  exact AnalyticNumberTheory.RiemannZeta.shifted_logarithmicWeightedSum_eq_residues hRH hσ hx

/-- For a real cutoff x, integrate the combined zeta pole and logarithmic-derivative
terms over sigma > 1 and divide by log x. Keeping these terms together cancels the
endpoint singularities. Under RH and x > 1 the integral is well-defined and integrable;
evaluating it gives the explicit main term of Lemma 2.6. -/
noncomputable def zetaLogLValueMain (x : ℝ) : ℂ :=
  (∫ σ : ℝ in Set.Ioi 1, AnalyticNumberTheory.RiemannZeta.shiftedZetaMainKernel x σ) /
    (Real.log x : ℂ)

/-- Under RH and x > 1, split the unsigned logarithmic sum into its combined zeta
main integral minus the normalized nontrivial-zero and gamma residue integrals.
All three combined families are integrable, so the integrated shifted formula may
be separated. This isolates the two quantitative errors in Lemma 2.6. -/
theorem logLValueSum_eq_zetaMain_sub_zero_sub_gamma (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    (logLValueSum x : ℂ) =
      zetaLogLValueMain x -
        (∫ σ : ℝ in Set.Ioi 1,
            ∑' ρ : AnalyticNumberTheory.RiemannXi.Zero,
              (analyticOrderNatAt AnalyticNumberTheory.RiemannXi.riemannXi (ρ : ℂ) : ℂ) *
                  (x : ℂ) ^ ((ρ : ℂ) - (σ : ℂ)) /
                ((ρ : ℂ) - (σ : ℂ)) ^ 2) /
          (Real.log x : ℂ) -
        (∫ σ : ℝ in Set.Ioi 1, AnalyticNumberTheory.General.gammaShiftSum x 2 σ) /
          (Real.log x : ℂ) := by
  let Z := fun σ : ℝ ↦
    ∑' ρ : AnalyticNumberTheory.RiemannXi.Zero,
      (analyticOrderNatAt AnalyticNumberTheory.RiemannXi.riemannXi (ρ : ℂ) : ℂ) *
          (x : ℂ) ^ ((ρ : ℂ) - (σ : ℂ)) /
        ((ρ : ℂ) - (σ : ℂ)) ^ 2
  have hZ : MeasureTheory.IntegrableOn Z (Set.Ioi 1) := by
    simpa only [AnalyticNumberTheory.RiemannXi.riemannXiZeroMultiplicity] using
      AnalyticNumberTheory.RiemannXi.integrableOn_shifted_zero_sum hRH hx
  have hG :=
    AnalyticNumberTheory.General.integrableOn_gammaShiftSum hx
      (show (0 : ℝ) ≤ (2 : ℂ).re by norm_num only [Complex.re_ofNat])
  have hM := AnalyticNumberTheory.RiemannZeta.integrableOn_shiftedZetaMainKernel hRH hx
  rw [logLValueSum_eq_integrated_residues hRH hx]
  change
    (∫ σ : ℝ in Set.Ioi 1,
          AnalyticNumberTheory.RiemannZeta.shiftedZetaMainKernel x σ - Z σ -
            AnalyticNumberTheory.General.gammaShiftSum x 2 σ) /
        (Real.log x : ℂ) =
      _
  rw [MeasureTheory.integral_sub (f := fun σ ↦
      AnalyticNumberTheory.RiemannZeta.shiftedZetaMainKernel x σ - Z σ) (g :=
      AnalyticNumberTheory.General.gammaShiftSum x 2) (hM.sub hZ) hG,
    MeasureTheory.integral_sub (f := AnalyticNumberTheory.RiemannZeta.shiftedZetaMainKernel x) (g :=
      Z) hM hZ]
  dsimp only [zetaLogLValueMain, Z]
  ring

/-- Under RH and x > 1, the unsigned logarithmic sum differs from the combined
zeta main integral by at most 2 B/(sqrt x (log x)^2)+1/(3 x^3 (log x)^2).
Use the exact Riemann zero mass for the nontrivial zeros and the sharper gamma
bound for shifts of real part at least two. This proves the complete residue-error
bound of Lemma 2.6. Combine it with the evaluation of the main integral to bound
the error from the explicit logarithmic main term. -/
theorem norm_logLValueSum_sub_zetaMain_le (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    ‖(logLValueSum x : ℂ) - zetaLogLValueMain x‖ ≤
      2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass / (Real.sqrt x * (Real.log x) ^ 2) +
        1 / (3 * x ^ 3 * (Real.log x) ^ 2) := by
  let Z :=
    (∫ σ : ℝ in Set.Ioi 1,
        ∑' ρ : AnalyticNumberTheory.RiemannXi.Zero,
          (analyticOrderNatAt AnalyticNumberTheory.RiemannXi.riemannXi (ρ : ℂ) : ℂ) *
              (x : ℂ) ^ ((ρ : ℂ) - (σ : ℂ)) /
            ((ρ : ℂ) - (σ : ℂ)) ^ 2) /
      (Real.log x : ℂ)
  let G :=
    (∫ σ : ℝ in Set.Ioi 1, AnalyticNumberTheory.General.gammaShiftSum x 2 σ) / (Real.log x : ℂ)
  have hZ :
    ‖Z‖ ≤
      2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass / (Real.sqrt x * (Real.log x) ^ 2) := by
    simpa only [AnalyticNumberTheory.RiemannXi.riemannXiZeroMultiplicity] using
      AnalyticNumberTheory.RiemannXi.norm_integrated_shifted_zero_sum_div_log_le hRH hx
  have hG : ‖G‖ ≤ 1 / (3 * x ^ 3 * (Real.log x) ^ 2) :=
    AnalyticNumberTheory.General.norm_integrated_gammaShiftSum_div_log_le_of_two_le_re hx
      (show (2 : ℝ) ≤ (2 : ℂ).re by norm_num only [Complex.re_ofNat])
  have he : (logLValueSum x : ℂ) = zetaLogLValueMain x - Z - G :=
    logLValueSum_eq_zetaMain_sub_zero_sub_gamma hRH hx
  rw [he, show (zetaLogLValueMain x - Z - G) - zetaLogLValueMain x = -(Z + G) by ring, norm_neg]
  exact (norm_add_le Z G).trans (add_le_add hZ hG)

/-- Under RH and x > 1, the real normalized zeta main integral is
log log x+gamma-1+gamma/log x. Integrate the combined pole and logarithmic derivative
before dividing by log x; cancellation at one identifies the main term in Lemma 2.6. -/
theorem zetaLogLValueMain_re (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    (zetaLogLValueMain x).re =
      Real.log (Real.log x) + Real.eulerMascheroniConstant - 1 +
        Real.eulerMascheroniConstant / Real.log x := by
  have hi := AnalyticNumberTheory.RiemannZeta.integrableOn_shiftedZetaMainKernel hRH hx
  have he := Complex.reCLM.integral_comp_comm hi
  change
    (∫ σ : ℝ in Set.Ioi 1, (AnalyticNumberTheory.RiemannZeta.shiftedZetaMainKernel x σ).re) =
      (∫ σ : ℝ in Set.Ioi 1, AnalyticNumberTheory.RiemannZeta.shiftedZetaMainKernel x σ).re at he
  rw [zetaLogLValueMain, Complex.div_ofReal_re, ← he]
  rw [AnalyticNumberTheory.RiemannZeta.integral_shiftedZetaMainKernel_re hRH hx]
  field_simp [ne_of_gt (Real.log_pos hx)]

/-- Normalize an error bounded by the absolute value of a signed radius. The zero
radius gives zero error; otherwise divide by the radius. This retains the paper's signed
constant. -/
private theorem exists_theta_mul_of_abs_le_abs {y c : ℝ} (h : |y| ≤ |c|) :
    ∃ θ : ℝ, |θ| ≤ 1 ∧ y = θ * c := by
  by_cases hc : c = 0
  · have hy : y = 0 :=
      abs_eq_zero.mp (le_antisymm (by simpa only [hc, abs_zero] using h) (abs_nonneg y))
    exact ⟨0, by norm_num only [abs_zero], by rw [hy, zero_mul]⟩
  · refine ⟨y / c, ?_, (div_mul_cancel₀ y hc).symm⟩
    rw [abs_div]
    exact (div_le_one (abs_pos.mpr hc)).mpr h

/-- Under RH and x > 1, the logarithmic Mangoldt sum has the exact main term
log log x+gamma-1+gamma/log x and two independent bounded real errors. Take real parts of the
integrated residue identity, evaluate its combined main integral, and normalize the zero and
gamma errors separately. The signed zero constant agrees with the original Lemma 2.6. -/
theorem logLValueSum_eq_main_with_bounded_errors (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    ∃ θ₁ θ₂ : ℝ,
      |θ₁| ≤ 1 ∧
        |θ₂| ≤ 1 ∧
        logLValueSum x =
          Real.log (Real.log x) + Real.eulerMascheroniConstant - 1 +
            Real.eulerMascheroniConstant / Real.log x +
            2 * (Real.log (4 * Real.pi) / 2 - 1 - Real.eulerMascheroniConstant / 2) * θ₁ /
              (Real.sqrt x * (Real.log x) ^ 2) +
            θ₂ / (3 * x ^ 3 * (Real.log x) ^ 2) := by
  let Z :=
    (∫ σ : ℝ in Set.Ioi 1,
        ∑' ρ : AnalyticNumberTheory.RiemannXi.Zero,
          (analyticOrderNatAt AnalyticNumberTheory.RiemannXi.riemannXi (ρ : ℂ) : ℂ) *
              (x : ℂ) ^ ((ρ : ℂ) - (σ : ℂ)) /
            ((ρ : ℂ) - (σ : ℂ)) ^ 2) /
      (Real.log x : ℂ)
  let G :=
    (∫ σ : ℝ in Set.Ioi 1, AnalyticNumberTheory.General.gammaShiftSum x 2 σ) / (Real.log x : ℂ)
  have hd : 0 < Real.sqrt x * (Real.log x) ^ 2 :=
    mul_pos (Real.sqrt_pos.mpr (zero_lt_one.trans hx)) (sq_pos_of_pos (Real.log_pos hx))
  have hg : 0 < 3 * x ^ 3 * (Real.log x) ^ 2 :=
    mul_pos (mul_pos (by norm_num only) (pow_pos (zero_lt_one.trans hx) 3))
      (sq_pos_of_pos (Real.log_pos hx))
  have hZ :
    ‖Z‖ ≤
      2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass / (Real.sqrt x * (Real.log x) ^ 2) := by
    simpa only [AnalyticNumberTheory.RiemannXi.riemannXiZeroMultiplicity] using
      AnalyticNumberTheory.RiemannXi.norm_integrated_shifted_zero_sum_div_log_le hRH hx
  have hG : ‖G‖ ≤ 1 / (3 * x ^ 3 * (Real.log x) ^ 2) :=
    AnalyticNumberTheory.General.norm_integrated_gammaShiftSum_div_log_le_of_two_le_re hx
      (show (2 : ℝ) ≤ (2 : ℂ).re by norm_num only [Complex.re_ofNat])
  have hz :
    |-Z.re| ≤
      |2 * (Real.log (4 * Real.pi) / 2 - 1 - Real.eulerMascheroniConstant / 2) /
          (Real.sqrt x * (Real.log x) ^ 2)| := by
    rw [abs_neg, abs_div, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num only), abs_of_pos hd]
    exact (Complex.abs_re_le_norm Z).trans hZ
  have hgr : |-G.re| ≤ |1 / (3 * x ^ 3 * (Real.log x) ^ 2)| := by
    rw [abs_neg, abs_of_pos (one_div_pos.mpr hg)]
    exact (Complex.abs_re_le_norm G).trans hG
  obtain ⟨θ₁, hθ₁, he₁⟩ := exists_theta_mul_of_abs_le_abs hz
  obtain ⟨θ₂, hθ₂, he₂⟩ := exists_theta_mul_of_abs_le_abs hgr
  refine ⟨θ₁, θ₂, hθ₁, hθ₂, ?_⟩
  have he := congrArg Complex.re (logLValueSum_eq_zetaMain_sub_zero_sub_gamma hRH hx)
  change (logLValueSum x : ℂ).re = (zetaLogLValueMain x - Z - G).re at he
  simp only [Complex.ofReal_re, Complex.sub_re, zetaLogLValueMain_re hRH hx] at he
  rw [he]
  simp only [div_eq_mul_inv] at he₁ he₂ ⊢
  nlinarith only [he₁, he₂]

/-- Under RH and x > 1, the logarithmic Mangoldt sum differs from
log log x+gamma-1+gamma/log x by at most the sum of the zero and gamma error radii.
Take the real part of the integrated residue estimate and evaluate the main integral.
This two-sided bound is used in the upper and reciprocal bounds for L(1,chi). -/
theorem abs_logLValueSum_error_le (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    |logLValueSum x -
          (Real.log (Real.log x) + Real.eulerMascheroniConstant - 1 +
            Real.eulerMascheroniConstant / Real.log x)| ≤
      2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass / (Real.sqrt x * (Real.log x) ^ 2) +
        1 / (3 * x ^ 3 * (Real.log x) ^ 2) := by
  have h := Complex.abs_re_le_norm ((logLValueSum x : ℂ) - zetaLogLValueMain x)
  rw [Complex.sub_re, Complex.ofReal_re, zetaLogLValueMain_re hRH hx] at h
  exact h.trans (norm_logLValueSum_sub_zetaMain_le hRH hx)

end PseudoPrime.LLS.PaperStatements
