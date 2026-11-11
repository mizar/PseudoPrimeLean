/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundGammaFiniteLimit

/-! # Primitive for the Gamma Euler–Maclaurin cells -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For positive `a`, the complex Gamma kernel on the `k`th unit interval
equals the corresponding difference of Stirling main terms minus the
logarithm of the shifted argument. Translate the polynomial cell to `[0,1]`
and apply its explicit primitive. -/
theorem gamma_complex_integral_nat_cell {a y : ℝ} (ha : 0 < a) (k : ℕ) :
    (∫ t in (k : ℝ)..((k : ℝ) + 1), backlundGammaComplexKernel a y t) =
      AnalyticNumberTheory.Gamma.backlundStirlingMain
          (((a : ℂ) + (y : ℂ) * Complex.I) + (k + 1 : ℕ)) -
        AnalyticNumberTheory.Gamma.backlundStirlingMain (((a : ℂ) + (y : ℂ) * Complex.I) + k) -
        Complex.log (((a : ℂ) + (y : ℂ) * Complex.I) + k) := by
  let b : ℂ := ((a : ℂ) + (y : ℂ) * Complex.I) + k
  have hb : 0 < b.re := by
    simp only [b, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero, Complex.natCast_re]
    exact add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg k)
  have h := gamma_complex_integral_cell a y (k : ℤ)
  simp only [Int.cast_natCast] at h
  rw [h]
  have hs :=
    intervalIntegral.integral_comp_add_left
      (fun t : ℝ ↦
        ((((t - k) * (1 - (t - k)) : ℝ) : ℂ) / 2) *
          ((((a + t : ℝ) : ℂ) + (y : ℂ) * Complex.I)⁻¹ ^ 2))
      (k : ℝ) (a := 0) (b := 1)
  simp only [add_zero, add_sub_cancel_left] at hs
  rw [← hs]
  have he :
    (fun v : ℝ ↦
        ((((k + v - k) * (1 - (k + v - k)) : ℝ) : ℂ) / 2) *
          ((((a + (k + v) : ℝ) : ℂ) + (y : ℂ) * Complex.I)⁻¹ ^ 2)) =
      (fun v : ℝ ↦ ((v : ℂ) * (1 - v) / 2) * (b + v)⁻¹ ^ 2) := by
    funext v
    simp only [add_sub_cancel_left, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_add, Complex.ofReal_natCast]
    congr 2
    dsimp only [b]
    ring
  simp only [add_sub_cancel_left] at he
  rw [he, AnalyticNumberTheory.Gamma.gamma_quadratic_integral_cell b hb]
  dsimp only [b]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [add_assoc]

/-- At positive real part, the integral of the Gamma kernel over `[0,N]`
equals the shifted Stirling main-part difference minus the finite logarithm
sum. The unit-cell endpoint terms telescope for every natural `N`. -/
theorem gamma_complex_integral_nat {a y : ℝ} (ha : 0 < a) (N : ℕ) :
    (∫ t in (0 : ℝ)..(N : ℝ), backlundGammaComplexKernel a y t) =
      AnalyticNumberTheory.Gamma.backlundStirlingMain (((a : ℂ) + (y : ℂ) * Complex.I) + N) -
        AnalyticNumberTheory.Gamma.backlundStirlingMain ((a : ℂ) + (y : ℂ) * Complex.I) -
        ∑ k ∈ Finset.range N, Complex.log (((a : ℂ) + (y : ℂ) * Complex.I) + k) := by
  rw [← gamma_complex_integral_sum ha N]
  have he :
    (∑ k ∈ Finset.range N, ∫ t in (k : ℝ)..((k : ℝ) + 1), backlundGammaComplexKernel a y t) =
      ∑ k ∈ Finset.range N,
        (AnalyticNumberTheory.Gamma.backlundStirlingMain
            (((a : ℂ) + (y : ℂ) * Complex.I) + (k + 1 : ℕ)) -
          AnalyticNumberTheory.Gamma.backlundStirlingMain (((a : ℂ) + (y : ℂ) * Complex.I) + k) -
          Complex.log (((a : ℂ) + (y : ℂ) * Complex.I) + k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact gamma_complex_integral_nat_cell ha k
  rw [he, Finset.sum_sub_distrib,
    Finset.sum_range_sub
      (fun k : ℕ ↦
        AnalyticNumberTheory.Gamma.backlundStirlingMain (((a : ℂ) + (y : ℂ) * Complex.I) + k))
      N]
  simp only [Nat.cast_zero, add_zero]

/-- The finite Gamma Euler–Maclaurin identity holds at every required
height and cutoff. The cell integrals telescope, and the imaginary parts of
the Euler logarithmic corrections produce the harmonic contribution. -/
theorem backlund_gamma_finite_identity : BacklundGammaFiniteIdentity := by
  intro t ht N
  let z : ℂ := ((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I
  have hz : z.im = t / 2 := by
    simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  have hi := gamma_complex_integral_nat (a := 1 / 4) (y := t / 2) (by norm_num only) N
  change
    (AnalyticNumberTheory.Gamma.backlundGammaPartial z N -
          AnalyticNumberTheory.Gamma.backlundStirlingMain z -
          ∫ u in (0 : ℝ)..(N : ℝ), backlundGammaComplexKernel (1 / 4) (t / 2) u).im =
      _
  rw [hi]
  simp only [Complex.sub_im, Complex.im_sum, AnalyticNumberTheory.Gamma.gamma_partial_im, hz]
  have hcomm : (N : ℂ) + z = z + N := add_comm _ _
  rw [hcomm]
  ring

/-- The complex Gamma remainder identity follows without additional
assumptions from the finite cell formula and the proved limiting argument.
The real constant is chosen separately at each height. -/
theorem backlund_gamma_complex_identity : BacklundGammaComplexIdentity := by
  exact gamma_complex_identity_of_finite backlund_gamma_finite_identity

end PseudoPrime.PrimeTestBounds.MillerRabin
