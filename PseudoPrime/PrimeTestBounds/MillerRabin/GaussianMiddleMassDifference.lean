/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassLeft
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassGammaCancel
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassContour
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassPoleShift
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosinePoles644
import PseudoPrime.LLS.PaperStatements.MellinKernelArithmeticMellin

/-! # Pole and Euler evaluations of the middle mass contour formula -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The normalized simple-pole integral of the combined middle Gaussian mass. -/
public noncomputable def middleMassPoleIntegral (Q : Polynomial ℚ) (a : ℚ) (d₀ : ℕ) (b p : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ,
      (1 / ((b : ℂ) + Complex.I * (t : ℂ) - (p : ℂ))) *
        middleMassExtension Q a (d₀ + 2) ((b : ℂ) + Complex.I * (t : ℂ))

/-- On either comparison line, the integral of the mass is the weighted sum
of the balanced simple-pole integrals. -/
private theorem middle_mass_pole_fold (Q : Polynomial ℚ) (a : ℚ) {d₀ : ℕ} (ha : 2 ≤ (a : ℝ))
    (hd₀ : 1 ≤ d₀) (hQ : Q.natDegree ≤ d₀) {b p : ℝ} (hb₁ : -(5 / 8 : ℝ) < b) (hb₂ : b ≤ 5 / 8)
    (hb : b ≠ -1 / 2) (hp : b ≠ p) :
    middleMassPoleIntegral Q a d₀ b p =
      ∑ j ∈ Finset.range (d₀ + 1),
        (((normSqPolynomial a Q).coeff j : ℂ)) *
          quarterCosinePole (balancedPoleKernel a ha (d₀ + 1 - j)) b p 1 := by
  let r := fun t : ℝ ↦ (b : ℂ) + Complex.I * (t : ℂ)
  let g := fun t ↦ 1 / (r t - (p : ℂ))
  let B := fun j ↦ balancedPoleKernel a ha (d₀ + 1 - j)
  let c := fun j ↦ ((normSqPolynomial a Q).coeff j : ℂ)
  let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hre (t : ℝ) : (r t).re = b := by
    simp only [r, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hl (t : ℝ) : -(a : ℝ) < (r t).re := by
    rw [hre]; linarith only [ha, hb₁]
  have hr (t : ℝ) : (r t).re < (a : ℝ) := by
    rw [hre]; linarith only [ha, hb₂]
  have hi (j : ℕ) : MeasureTheory.Integrable (fun t ↦ g t * (B j).function (r t)) := by
    have hd : (B j).delta = 1 / 8 := balanced_pole_delta _ _ _
    simpa only [g, r, Complex.ofReal_one, Complex.one_cpow, mul_one] using
      (B j).integrable_pole_power_line (x := 1) (c := b) (p := p)
        (by
          rw [hd]; linarith only [hb₁])
        (by
          rw [hd]; linarith only [hb₂])
        hb hp zero_lt_one
  change
    d * (∫ t : ℝ, g t * middleMassExtension Q a (d₀ + 2) (r t)) =
      ∑ j ∈ Finset.range (d₀ + 1), c j * quarterCosinePole (B j) b p 1
  rw [← fold_middle_mass_integrals Q a ha hd₀ hQ r hl hr g hi, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [quarterCosinePole, Complex.ofReal_one, Complex.one_cpow, mul_one]
  exact mul_left_comm _ _ _

/-- Moving an interior simple pole across the strip contributes the mass
function evaluated at the pole, by linearity of the balanced decomposition. -/
public theorem middle_mass_pole_shift (Q : Polynomial ℚ) (a : ℚ) {d₀ : ℕ} (ha : 2 ≤ (a : ℝ))
    (hd₀ : 1 ≤ d₀) (hQ : Q.natDegree ≤ d₀) {p : ℝ} (hl : -9 / 16 < p) (hr : p < 9 / 16) :
    middleMassPoleIntegral Q a d₀ (9 / 16) p - middleMassPoleIntegral Q a d₀ (-9 / 16) p =
      middleMassExtension Q a (d₀ + 2) (p : ℂ) := by
  rw [middle_mass_pole_fold Q a ha hd₀ hQ (by norm_num only) (by norm_num only) (by norm_num only)
      hr.ne',
    middle_mass_pole_fold Q a ha hd₀ hQ (by norm_num only) (by norm_num only) (by norm_num only)
      hl.ne]
  rw [← Finset.sum_sub_distrib]
  rw [middle_mass_balanced_sum Q a ha hd₀ hQ
      (by
        rw [Complex.ofReal_re]; linarith only [ha, hl])
      (by
        rw [Complex.ofReal_re]; linarith only [ha, hr])]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_sub,
    quarter_cosine_pole_diff _ (balanced_pole_delta _ _ _) (balanced_pole_analytic ha _) le_rfl hl
      hr]
  simp only [Complex.ofReal_one, Complex.one_cpow, mul_one]

/-- Reflection moves the left contour to the right contour for the even mass kernel. -/
public theorem middle_mass_reflect (Q : Polynomial ℚ) (a : ℚ) (d₀ : ℕ) (H : ℂ → ℂ) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    (∫ t : ℝ, H (-(l t)) * middleMassExtension Q a (d₀ + 2) (l t)) =
      ∫ t : ℝ, H (r t) * middleMassExtension Q a (d₀ + 2) (r t) := by
  intro l r
  let F := fun t ↦ H (r t) * middleMassExtension Q a (d₀ + 2) (r t)
  have hr (t : ℝ) : r (-t) = -(l t) := by
    dsimp only [r, l]
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat, mul_neg, neg_add_rev]
    ring
  have he (t : ℝ) : H (-(l t)) * middleMassExtension Q a (d₀ + 2) (l t) = F (-t) := by
    simp only [F, hr, middle_mass_extension_even]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall he)]
  exact MeasureTheory.integral_neg_eq_self F MeasureTheory.volume

/-- The ordinary logarithmic derivative on the right contour gives the unit-scale
Mangoldt series of the signed mass profile. -/
public theorem middle_mass_euler (Q : Polynomial ℚ) (a : ℚ) {d₀ : ℕ} (ha : 2 ≤ (a : ℝ))
    (hd₀ : 1 ≤ d₀) (hQ : Q.natDegree ≤ d₀) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    d * (∫ t : ℝ, -logDeriv χ.LFunction (r t + 1 / 2) * middleMassExtension Q a (d₀ + 2) (r t)) =
      ∑' n : ℕ,
        ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n *
          (middleMassProfile Q a d₀ n : ℂ) := by
  intro r d
  let B := fun j ↦ balancedPoleKernel a ha (d₀ + 1 - j)
  let c := fun j ↦ ((normSqPolynomial a Q).coeff j : ℂ)
  let G := fun j t ↦ -logDeriv χ.LFunction (r t + 1 / 2) * (B j).function (r t)
  have hb (j : ℕ) : (9 / 16 : ℝ) ≤ 1 / 2 + (B j).delta := by
    rw [show (B j).delta = 1 / 8 from balanced_pole_delta _ _ _]
    norm_num only
  have hre (t : ℝ) : (r t).re = 9 / 16 := by
    simp only [r, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hm (t : ℝ) :
    (∑ j ∈ Finset.range (d₀ + 1), c j * G j t) =
      -logDeriv χ.LFunction (r t + 1 / 2) * middleMassExtension Q a (d₀ + 2) (r t) := by
    rw [middle_mass_balanced_sum Q a ha hd₀ hQ
        (by
          rw [hre]; linarith only [ha])
        (by
          rw [hre]; linarith only [ha]),
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ mul_left_comm _ _ _
  have hi (j : ℕ) : MeasureTheory.Integrable (fun t ↦ c j * G j t) := by
    have h :=
      (B j).integrable_arithmeticMellin_logDeriv χ (x := 1) zero_lt_one
        (by norm_num only : (1 / 2 : ℝ) < 9 / 16) (hb j)
    simpa only [G, r, Complex.ofReal_one, Complex.one_cpow, mul_one] using h.const_mul (c j)
  have hA (j : ℕ) : d * (∫ t : ℝ, G j t) = ∑' n : ℕ, (B j).summand χ 1 n := by
    have h :=
      (B j).tsum_summand_eq_integral_logDeriv χ (x := 1) zero_lt_one
        (by norm_num only : (1 / 2 : ℝ) < 9 / 16) (hb j)
    simpa only [G, r, d, Complex.ofReal_one, Complex.one_cpow, mul_one] using h.symm
  simp_rw [← hm, MeasureTheory.integral_finsetSum _ (fun j _ ↦ hi j),
    MeasureTheory.integral_const_mul, Finset.mul_sum, mul_left_comm d, hA]
  rw [← LLS.PaperStatements.MellinKernel.tsum_kernel_finset_sum _ B c χ zero_lt_one]
  exact tsum_congr (middle_mass_mangoldt Q a d₀ ha χ)

/-- Reflection converts the ordinary derivative on the left into the same
signed Mangoldt series as the right contour at unit scale. -/
public theorem middle_reflected_mass_euler (Q : Polynomial ℚ) (a : ℚ) {d₀ : ℕ} (ha : 2 ≤ (a : ℝ))
    (hd₀ : 1 ≤ d₀) (hQ : Q.natDegree ≤ d₀) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    d * (∫ t : ℝ, -logDeriv χ.LFunction (-(l t) + 1 / 2) * middleMassExtension Q a (d₀ + 2) (l t)) =
      ∑' n : ℕ,
        ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n *
          (middleMassProfile Q a d₀ n : ℂ) := by
  intro l d
  have h := middle_mass_reflect Q a d₀ (fun z ↦ -logDeriv χ.LFunction (z + 1 / 2))
  dsimp only at h
  rw [h]
  exact middle_mass_euler Q a ha hd₀ hQ χ

/-- The mass difference for a primitive even self-dual character consists
of the conductor, two identical half-point residues and two Euler differences. -/
public theorem middle_mass_even_difference (Q : Polynomial ℚ) (a : ℚ) {d₀ : ℕ} (ha : 2 ≤ (a : ℝ))
    (hd₀ : 1 ≤ d₀) (hQ : Q.natDegree ≤ d₀) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even) :
    let F := middleMassExtension Q a (d₀ + 2)
    let E := fun {m : ℕ} (ψ : DirichletCharacter ℂ m) ↦
      ∑' n : ℕ,
        ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * ψ n *
          (middleMassProfile Q a d₀ n : ℂ)
    (∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) * F (Complex.I * ρ.im)) -
        middleXiMass Q a d₀ =
      Complex.log q * (middleMassProfile Q a d₀ 1 : ℂ) - 2 * F ((1 / 2 : ℝ) : ℂ) +
        2 * (E (1 : DirichletCharacter ℂ 1) - E χ) := by
  intro F E
  have h := middle_mass_reflected_difference Q a ha hd₀ hQ hq hGRH hp hne hi he
  have hc := middle_mass_conductor_integral Q a ha hd₀ hQ q
  have he₁ := middle_reflected_mass_euler Q a ha hd₀ hQ (1 : DirichletCharacter ℂ 1)
  have he₂ := middle_reflected_mass_euler Q a ha hd₀ hQ χ
  have hpos :=
    middle_mass_pole_shift Q a ha hd₀ hQ (p := 1 / 2) (by norm_num only) (by norm_num only)
  have hneg :=
    middle_mass_pole_shift Q a ha hd₀ hQ (p := -(1 / 2)) (by norm_num only) (by norm_num only)
  have hsym : F ((-(1 / 2) : ℝ) : ℂ) = F ((1 / 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_neg]
    exact middle_mass_extension_even Q a (d₀ + 2) _
  dsimp only [F, E] at h hc he₁ he₂ hpos hneg hsym ⊢
  simp only [middleMassPoleIntegral] at hpos hneg
  rw [hsym] at hneg
  have harg : (-1 / 2 : ℝ) = -(1 / 2) := by norm_num only
  simp only [harg] at h
  linear_combination h + hc + he₁ - he₂ - hpos - hneg

end PseudoPrime.PrimeTestBounds.MillerRabin
