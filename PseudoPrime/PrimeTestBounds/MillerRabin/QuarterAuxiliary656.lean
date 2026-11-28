/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterKernel656
public import PseudoPrime.LLS.PaperStatements.MellinKernelZeros

/-! # Finite-frequency square completion for section 132 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Every pairwise cosine term in the finite-frequency quadratic form
is accounted for by the squares of the two trigonometric sums. -/
private theorem cosine_cross_sum {ι : Type*} [Fintype ι] (a c : ι → ℝ) :
    (∑ i, ∑ j, c i * c j * Real.cos (a i - a j)) =
      (∑ i, c i * Real.cos (a i)) ^ 2 + (∑ i, c i * Real.sin (a i)) ^ 2 := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.cos_sub]
  ring

/-- Completing two squares gives the phase inequality for any finite set
of angles and real coefficients, with all pairwise cosine terms retained. -/
theorem finite_frequency_phase_le {ι : Type*} [Fintype ι] (θ : ℝ) (a c : ι → ℝ) :
    (∑ i, c i * (Real.cos (a i) + Real.cos (θ - a i))) -
        (∑ i, ∑ j, c i * c j * Real.cos (a i - a j)) / 2 ≤
      1 + Real.cos θ := by
  let x := ∑ i, c i * Real.cos (a i)
  let y := ∑ i, c i * Real.sin (a i)
  have hlin :
    (∑ i, c i * (Real.cos (a i) + Real.cos (θ - a i))) = (1 + Real.cos θ) * x + Real.sin θ * y := by
    dsimp only [x, y]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.cos_sub]
    ring
  rw [hlin, cosine_cross_sum]
  change (1 + Real.cos θ) * x + Real.sin θ * y - (x ^ 2 + y ^ 2) / 2 ≤ _
  linear_combination
    sq_nonneg (1 + Real.cos θ - x) / 2 + sq_nonneg (Real.sin θ - y) / 2 +
      Real.sin_sq_add_cos_sq θ / 2

/-- Summing the finite-frequency inequality against nonnegative summable weights
retains every ordered pair of frequencies. The angles grow with the ordinates. -/
theorem finite_frequency_weighted_le {ι κ : Type*} [Fintype ι] (w θ g : κ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hs : Summable w) (a c : ι → ℝ) :
    let W := fun f : κ → ℝ ↦ ∑' k, w k * Real.cos (f k)
    (∑ i, c i * (W (fun k ↦ a i * g k) + W (fun k ↦ θ k - a i * g k))) -
        (∑ i, ∑ j, c i * c j * W (fun k ↦ (a i - a j) * g k)) / 2 ≤
      (∑' k, w k) + W θ := by
  intro W
  have hc (f : κ → ℝ) : Summable (fun k ↦ w k * Real.cos (f k)) := by
    apply hs.of_norm_bounded
    intro k
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw k)]
    exact mul_le_of_le_one_right (hw k) (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
  let f := fun i k ↦ c i * (w k * Real.cos (a i * g k) + w k * Real.cos (θ k - a i * g k))
  let v := fun i j k ↦ c i * c j * (w k * Real.cos ((a i - a j) * g k))
  have hf (i : ι) : Summable (f i) := ((hc _).add (hc _)).mul_left _
  have hv (i j : ι) : Summable (v i j) := (hc _).mul_left _
  have hF : Summable (fun k ↦ ∑ i, f i k) := summable_sum (fun i _ ↦ hf i)
  have hV (i : ι) : Summable (fun k ↦ ∑ j, v i j k) := summable_sum (fun j _ ↦ hv i j)
  have hVV : Summable (fun k ↦ ∑ i, ∑ j, v i j k) := summable_sum (fun i _ ↦ hV i)
  have h :=
    (hF.sub (hVV.div_const 2)).tsum_le_tsum (g := fun k ↦ w k + w k * Real.cos (θ k))
      (fun k ↦ by
        have hk :=
          mul_le_mul_of_nonneg_left (finite_frequency_phase_le (θ k) (fun i ↦ a i * g k) c) (hw k)
        simpa only [f, v, mul_sub, mul_add, ← mul_div_assoc, Finset.mul_sum, sub_mul, mul_left_comm,
          mul_assoc, mul_one] using hk)
      (hs.add (hc θ))
  rw [Summable.tsum_sub hF (hVV.div_const 2), tsum_div_const,
    Summable.tsum_finsetSum (fun i _ ↦ hf i), Summable.tsum_finsetSum (fun i _ ↦ hV i),
    Summable.tsum_add hs (hc θ)] at h
  simpa only [W, f, v, Summable.tsum_finsetSum (fun j _ ↦ hv _ j), tsum_mul_left,
    Summable.tsum_add (hc _) (hc _)] using h

/-- Multiplication of the scale by exp(-s) rotates each zero term by
minus s times its ordinate, including terms of zero multiplicity. -/
private theorem zero_term_shift {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x)
    (s : ℝ) (ρ : ℂ) :
    quarterKernel656.oscillatingZeroTerm χ (x * Real.exp (-s)) ρ =
      quarterKernel656.oscillatingZeroTerm χ x ρ * Complex.exp ((-(s * ρ.im) : ℝ) * Complex.I) := by
  unfold LLS.PaperStatements.MellinKernel.oscillatingZeroTerm
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos hx (Real.exp_pos _)).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), ←
    Complex.ofReal_log (mul_pos hx (Real.exp_pos _)).le, ← Complex.ofReal_log hx.le,
    Real.log_mul hx.ne' (Real.exp_pos _).ne', Real.log_exp, mul_assoc, ← Complex.exp_add]
  push_cast
  ring_nf

/-- The shifted phase cosine sum is exactly the real oscillating zero sum
at the rescaled cutoff. Absolute convergence at the positive new cutoff
justifies taking the real part term by term. -/
private theorem shifted_phase_eq {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    (hi : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (s : ℝ) :
    let Z := quarterKernel656.oscillatingZeroTerm χ x
    (∑' ρ : ℂ, ‖Z ρ‖ * Real.cos ((Z ρ).arg - s * ρ.im)) =
      (∑' ρ : ℂ, quarterKernel656.oscillatingZeroTerm χ (x * Real.exp (-s)) ρ).re := by
  intro Z
  rw [Complex.re_tsum
      (LLS.PaperStatements.MellinKernel.summable_oscillatingZeroTerm quarterKernel656 hq hG hp hn hi
        (mul_pos hx (Real.exp_pos _)))]
  apply tsum_congr
  intro ρ
  rw [zero_term_shift χ hx, Complex.mul_re, Complex.exp_re, Complex.exp_im, Real.cos_sub]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, mul_one, add_zero, Real.exp_zero, one_mul, Real.cos_neg,
    Real.sin_neg]
  change ‖Z ρ‖ * _ = (Z ρ).re * _ - (Z ρ).im * _
  rw [mul_add, ← mul_assoc, Complex.norm_mul_cos_arg, ← mul_assoc, Complex.norm_mul_sin_arg]
  ring

/-- For a primitive nonprincipal character under GRH, the seven-frequency
inequality bounds the main oscillating zero sum and its absolute mass.
Every cosine of a difference of auxiliary frequencies occurs in the bound. -/
theorem quarter_seven_frequency_656 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    {X : ℝ} (hX : 0 < X) :
    let Z := quarterKernel656.oscillatingZeroTerm χ X
    let B := fun t : ℝ ↦ ∑' ρ : ℂ, ‖Z ρ‖ * Real.cos (t * ρ.im)
    let T := fun t : ℝ ↦ (∑' ρ : ℂ, quarterKernel656.oscillatingZeroTerm χ (X * Real.exp (-t)) ρ).re
    (∑ i, quarterAuxCoeff656 i * (B (quarterAuxFrequency656 i) + T (quarterAuxFrequency656 i))) -
        (∑ i,
            ∑ j,
              quarterAuxCoeff656 i * quarterAuxCoeff656 j *
                B (quarterAuxFrequency656 i - quarterAuxFrequency656 j)) /
          2 ≤
      (∑' ρ : ℂ, ‖Z ρ‖) + (∑' ρ : ℂ, Z ρ).re := by
  intro Z B T
  have hi := inv_ne_one.mpr hn
  have hs :=
    LLS.PaperStatements.MellinKernel.summable_oscillatingZeroTerm quarterKernel656 hq hG hp hn hi hX
  have h :=
    finite_frequency_weighted_le (fun ρ ↦ ‖Z ρ‖) (fun ρ ↦ (Z ρ).arg) Complex.im
      (fun ρ ↦ norm_nonneg (Z ρ)) hs.norm quarterAuxFrequency656 quarterAuxCoeff656
  dsimp only at h
  have ht (t : ℝ) : (∑' ρ : ℂ, ‖Z ρ‖ * Real.cos ((Z ρ).arg - t * ρ.im)) = T t :=
    shifted_phase_eq hq hG hp hn hi hX t
  have hr : (∑' ρ : ℂ, ‖Z ρ‖ * Real.cos (Z ρ).arg) = (∑' ρ : ℂ, Z ρ).re := by
    rw [Complex.re_tsum hs]
    exact tsum_congr (fun ρ ↦ Complex.norm_mul_cos_arg (Z ρ))
  simpa only [ht, hr, B] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
