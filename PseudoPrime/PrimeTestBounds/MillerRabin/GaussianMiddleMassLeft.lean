/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassGammaCancel
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassGammaCancel
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianBalancedPoleKernel
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftZeta
import PseudoPrime.LLS.PaperStatements.MellinKernelArithmeticMellin
import PseudoPrime.LLS.PaperStatements.MellinKernelVerticalIntegrability

/-! # Reflected left contour of the middle Gaussian absolute mass -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Integrability of the balanced components transfers to the combined contour mass. -/
private theorem integrable_middle_mass (Q : Polynomial ℚ) (a : ℚ) {d₀ : ℕ} (ha : 2 ≤ (a : ℝ))
    (hd₀ : 1 ≤ d₀) (hQ : Q.natDegree ≤ d₀) (b : ℝ) (g : ℝ → ℂ) (hb₁ : -1 ≤ b) (hb₂ : b ≤ 1)
    (h :
      ∀ j : ℕ,
        MeasureTheory.Integrable
          (fun t : ℝ ↦
            g t *
              (balancedPoleKernel a ha (d₀ + 1 - j)).function ((b : ℂ) + Complex.I * (t : ℂ)))) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ g t * middleMassExtension Q a (d₀ + 2) ((b : ℂ) + Complex.I * t)) := by
  let r := fun t : ℝ ↦ (b : ℂ) + Complex.I * (t : ℂ)
  let B := fun j ↦ balancedPoleKernel a ha (d₀ + 1 - j)
  let c := fun j ↦ ((normSqPolynomial a Q).coeff j : ℂ)
  have hre (t : ℝ) : (r t).re = b := by
    simp only [r, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hh (j : ℕ) : MeasureTheory.Integrable (fun t : ℝ ↦ c j * (g t * (B j).function (r t))) :=
    (h j).const_mul _
  apply (MeasureTheory.integrable_finsetSum (Finset.range (d₀ + 1)) (fun j _ ↦ hh j)).congr
  exact
    Filter.Eventually.of_forall fun t ↦ by
      dsimp only
      rw [middle_mass_balanced_sum Q a ha hd₀ hQ
          (by
            rw [hre]; linarith only [ha, hb₁])
          (by
            rw [hre]; linarith only [ha, hb₂]),
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ mul_left_comm _ _ _

/-- The reflected ordinary logarithmic derivative is integrable against the middle mass. -/
private theorem integrable_middle_reflected (Q : Polynomial ℚ) (a : ℚ) {d₀ : ℕ} (ha : 2 ≤ (a : ℝ))
    (hd₀ : 1 ≤ d₀) (hQ : Q.natDegree ≤ d₀) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        -logDeriv χ.LFunction (-(l t) + 1 / 2) * middleMassExtension Q a (d₀ + 2) (l t)) := by
  intro l
  let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
  have h :=
    integrable_middle_mass Q a ha hd₀ hQ (9 / 16) (fun t ↦ -logDeriv χ.LFunction (r t + 1 / 2))
      (by norm_num only) (by norm_num only) fun j ↦ by
      let B := balancedPoleKernel a ha (d₀ + 1 - j)
      have hb : (9 / 16 : ℝ) ≤ 1 / 2 + B.delta := by
        rw [show B.delta = 1 / 8 from balanced_pole_delta _ _ _]
        norm_num only
      simpa only [r, Complex.ofReal_one, Complex.one_cpow, mul_one] using
        B.integrable_arithmeticMellin_logDeriv χ (x := 1) zero_lt_one (by norm_num only) hb
  apply h.comp_neg.congr
  apply Filter.Eventually.of_forall
  intro t
  change -logDeriv χ.LFunction (r (-t) + 1 / 2) * middleMassExtension Q a (d₀ + 2) (r (-t)) = _
  have hr : r (-t) = -(l t) := by
    dsimp only [r, l]
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat, mul_neg, neg_add_rev]
    ring
  rw [hr, middle_mass_extension_even]

/-- The left contour difference is the conductor term, the reflected Euler
difference, and the two left simple-pole integrals. -/
public theorem middle_mass_left_split (Q : Polynomial ℚ) (a : ℚ) {d₀ : ℕ} (ha : 2 ≤ (a : ℝ))
    (hd₀ : 1 ≤ d₀) (hQ : Q.natDegree ≤ d₀) {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    d *
        ((∫ t : ℝ,
            -logDeriv χ.completedLFunction (l t + 1 / 2) * middleMassExtension Q a (d₀ + 2) (l t)) -
          ∫ t : ℝ,
            -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (l t + 1 / 2) *
              middleMassExtension Q a (d₀ + 2) (l t)) =
      d * (∫ t : ℝ, Complex.log q * middleMassExtension Q a (d₀ + 2) (l t)) +
        d *
          ((∫ t : ℝ,
              -logDeriv (1 : DirichletCharacter ℂ 1).LFunction (-(l t) + 1 / 2) *
                middleMassExtension Q a (d₀ + 2) (l t)) -
            ∫ t : ℝ,
              -logDeriv χ.LFunction (-(l t) + 1 / 2) * middleMassExtension Q a (d₀ + 2) (l t)) +
        d * (∫ t : ℝ, 1 / (l t - ((1 / 2 : ℝ) : ℂ)) * middleMassExtension Q a (d₀ + 2) (l t)) +
        d * (∫ t : ℝ, 1 / (l t - ((-1 / 2 : ℝ) : ℂ)) * middleMassExtension Q a (d₀ + 2) (l t)) := by
  intro l d
  let F := fun t ↦ -logDeriv χ.completedLFunction (l t + 1 / 2)
  let Z := fun t ↦ -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (l t + 1 / 2)
  let C := fun t ↦ Complex.log (q : ℂ) * middleMassExtension Q a (d₀ + 2) (l t)
  let A {m : ℕ} [NeZero m] (ψ : DirichletCharacter ℂ m) (t : ℝ) : ℂ :=
    -logDeriv ψ.LFunction (-(l t) + 1 / 2) * middleMassExtension Q a (d₀ + 2) (l t)
  let P := fun (p : ℝ) t ↦ 1 / (l t - (p : ℂ)) * middleMassExtension Q a (d₀ + 2) (l t)
  let B := fun j ↦ balancedPoleKernel a ha (d₀ + 1 - j)
  have hd (j : ℕ) : (B j).delta = 1 / 8 := balanced_pole_delta _ _ _
  have hb (j : ℕ) : -1 / 2 - (B j).delta < (-9 / 16 : ℝ) := by
    rw [hd]; norm_num only
  have hF :=
    integrable_middle_mass Q a ha hd₀ hQ (-9 / 16) F (by norm_num only) (by norm_num only) fun j ↦
      by
      simpa only [F, l, Complex.ofReal_one, Complex.one_cpow, mul_one] using
        (B j).integrable_completed_left_line hp hne (inv_ne_one.mpr hne) (x := 1) (hb j)
          (by norm_num only) (by norm_num only) zero_lt_one
  have hZ :=
    integrable_middle_mass Q a ha hd₀ hQ (-9 / 16) Z (by norm_num only) (by norm_num only) fun j ↦
      by
      simpa only [Z, l, Complex.ofReal_one, Complex.one_cpow, mul_one] using
        (B j).integrable_xi_left_line (x := 1) (hb j) (by norm_num only) (by norm_num only)
          zero_lt_one
  have hC : MeasureTheory.Integrable C := by
    apply
      integrable_middle_mass Q a ha hd₀ hQ (-9 / 16) (fun _ ↦ Complex.log q) (by norm_num only)
        (by norm_num only)
    intro j
    have h :=
      balanced_vertical (a := (a : ℝ)) (c := -9 / 16) (by linarith only [ha])
        (by linarith only [ha]) (d₀ + 1 - j)
    unfold Complex.VerticalIntegrable at h
    simpa only [balancedPoleKernel, mul_comm Complex.I] using h.const_mul (Complex.log q)
  have hA : MeasureTheory.Integrable (fun t ↦ A (1 : DirichletCharacter ℂ 1) t - A χ t) :=
    (integrable_middle_reflected Q a ha hd₀ hQ (1 : DirichletCharacter ℂ 1)).sub
      (integrable_middle_reflected Q a ha hd₀ hQ χ)
  have hP (p : ℝ) (hn : (-9 / 16 : ℝ) ≠ p) : MeasureTheory.Integrable (P p) := by
    apply
      integrable_middle_mass Q a ha hd₀ hQ (-9 / 16) (fun t ↦ 1 / (l t - (p : ℂ)))
        (by norm_num only) (by norm_num only)
    intro j
    simpa only [l, Complex.ofReal_one, Complex.one_cpow, mul_one] using
      (B j).integrable_pole_power_line (x := 1) (hb j)
        (by
          rw [hd]; norm_num only)
        (by norm_num only) hn zero_lt_one
  have hPp := hP (1 / 2) (by norm_num only)
  have hPm := hP (-1 / 2) (by norm_num only)
  have hpoint (t : ℝ) :
    F t * middleMassExtension Q a (d₀ + 2) (l t) - Z t * middleMassExtension Q a (d₀ + 2) (l t) =
      C t + (A (1 : DirichletCharacter ℂ 1) t - A χ t) + P (1 / 2) t + P (-1 / 2) t := by
    have h := twoShift_left_log_difference hp hne hi he t
    have hw : ((17 / 16 : ℝ) : ℂ) - Complex.I * t = -(l t) + 1 / 2 := by
      dsimp only [l]
      simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
      ring
    dsimp only at h
    rw [hw] at h
    have H :=
      twoShift_left_pole_split (l t) (middleMassExtension Q a (d₀ + 2) (l t)) (Complex.log q)
        (logDeriv χ.LFunction (-(l t) + 1 / 2)) (logDeriv riemannZeta (-(l t) + 1 / 2))
    dsimp only at H
    simpa only [F, Z, C, A, P, l, ← sub_mul, sub_neg_eq_add, DirichletCharacter.LFunction_modOne_eq,
      h] using H
  change
    d *
        ((∫ t : ℝ, F t * middleMassExtension Q a (d₀ + 2) (l t)) -
          ∫ t : ℝ, Z t * middleMassExtension Q a (d₀ + 2) (l t)) =
      _
  have hAdd := MeasureTheory.integral_add ((hC.add hA).add hPp) hPm
  have hAdd' := MeasureTheory.integral_add (hC.add hA) hPp
  have hSub :=
    MeasureTheory.integral_sub
      (show MeasureTheory.Integrable (A (1 : DirichletCharacter ℂ 1)) from
        integrable_middle_reflected Q a ha hd₀ hQ (1 : DirichletCharacter ℂ 1))
      (show MeasureTheory.Integrable (A χ) from integrable_middle_reflected Q a ha hd₀ hQ χ)
  simp only [Pi.add_apply] at hAdd hAdd'
  rw [← MeasureTheory.integral_sub hF hZ,
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint), hAdd, hAdd',
    MeasureTheory.integral_add hC hA, hSub]
  simp only [mul_add, mul_sub, C, A, P]

/-- The character-minus-Xi mass after Gamma cancellation and left reflection.
Only the conductor, ordinary Euler terms and the two contour jumps remain. -/
public theorem middle_mass_reflected_difference (Q : Polynomial ℚ) (a : ℚ) {d₀ : ℕ}
    (ha : 2 ≤ (a : ℝ)) (hd₀ : 1 ≤ d₀) (hQ : Q.natDegree ≤ d₀) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    let F := middleMassExtension Q a (d₀ + 2)
    let E := fun {m : ℕ} (ψ : DirichletCharacter ℂ m) ↦
      ∑' n : ℕ,
        ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * ψ n *
          (middleMassProfile Q a d₀ n : ℂ)
    let A := fun {m : ℕ} [NeZero m] (ψ : DirichletCharacter ℂ m) ↦
      ∫ t : ℝ, -logDeriv ψ.LFunction (-(l t) + 1 / 2) * F (l t)
    let P := fun (v : ℝ → ℂ) (p : ℝ) ↦ ∫ t : ℝ, 1 / (v t - (p : ℂ)) * F (v t)
    (∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) * F (Complex.I * ρ.im)) -
        middleXiMass Q a d₀ =
      d * (∫ t : ℝ, Complex.log q * F (l t)) + d * (A (1 : DirichletCharacter ℂ 1) - A χ) +
        d * (P l (1 / 2) + P l (-1 / 2) - P r (1 / 2) - P r (-1 / 2)) +
        (E (1 : DirichletCharacter ℂ 1) - E χ) := by
  intro l r d F E A P
  have h := middle_mass_gamma_cancel Q a ha hd₀ hQ hq hGRH hGRH.riemann hp hne he
  have hl := middle_mass_left_split Q a ha hd₀ hQ hp hne hi he
  dsimp only [l, r, d, F, E, A, P] at h hl ⊢
  linear_combination h + hl

/-- The normalized integral of the mass on the left line equals the central
Mellin profile value, which is the coefficient of the conductor logarithm. -/
public theorem middle_mass_conductor_integral (Q : Polynomial ℚ) (a : ℚ) {d : ℕ} (ha : 2 ≤ (a : ℝ))
    (hd : 1 ≤ d) (hQ : Q.natDegree ≤ d) (q : ℕ) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, Complex.log q * middleMassExtension Q a (d + 2) (l t)) =
      Complex.log q * (middleMassProfile Q a d 1 : ℂ) := by
  intro l
  let B := fun j ↦ balancedPoleKernel a ha (d + 1 - j)
  have hre (t : ℝ) : (l t).re = -9 / 16 := by
    simp only [l, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hl (t : ℝ) : -(a : ℝ) < (l t).re := by
    rw [hre]; linarith only [ha]
  have hr (t : ℝ) : (l t).re < (a : ℝ) := by
    rw [hre]; linarith only [ha]
  have hi (j : ℕ) : MeasureTheory.Integrable (fun t ↦ (B j).function (l t)) := by
    have h :=
      balanced_vertical (a := (a : ℝ)) (c := -9 / 16) (by linarith only [ha])
        (by linarith only [ha]) (d + 1 - j)
    simpa only [B, l, balancedPoleKernel, Complex.VerticalIntegrable, mul_comm Complex.I] using h
  rw [MeasureTheory.integral_const_mul, mul_left_comm _ (Complex.log q)]
  congr 1
  have h :=
    fold_middle_mass_integrals Q a ha hd hQ l hl hr (fun _ ↦ 1)
      (fun j ↦ by simpa only [one_mul] using hi j)
  simp only [one_mul] at h
  rw [← h, Finset.mul_sum]
  simp only [middleMassProfile, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hpow : d + 1 - j + 1 = d + 2 - j := (Nat.sub_add_comm (hj'.trans (Nat.le_succ d))).symm
  have hv :=
    balanced_pole_inverse ha (d + 1 - j) (c := -9 / 16) (by linarith only [ha])
      (by linarith only [ha]) (u := 1) zero_lt_one
  simp only [Analysis.inverseMellin, Complex.ofReal_one, Complex.one_cpow, mul_one, hpow] at hv
  rw [mul_left_comm,
    show
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, (B j).function (l t)) =
        ((1 / 2 * k131SymmetricProfile a (d + 2 - j) (d + 2 - j) 1 : ℝ) : ℂ)
      from hv]
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ratCast, Complex.ofReal_ofNat,
    Complex.ofReal_one]
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
