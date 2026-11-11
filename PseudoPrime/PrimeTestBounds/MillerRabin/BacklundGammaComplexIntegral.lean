/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ThreeEleventhsGammaIntegral

/-! # Complex Euler–Maclaurin kernel for the Gamma remainder -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The complex Euler–Maclaurin kernel at `a + iy`, weighted by the periodic
quadratic function. Its integral is the candidate Gamma logarithm remainder
up to a real constant. -/
noncomputable def backlundGammaComplexKernel (a y x : ℝ) : ℂ :=
  ((backlundGammaWeight x : ℂ) / 2) * ((((a + x : ℝ) : ℂ) + (y : ℂ) * Complex.I)⁻¹ ^ 2)

private theorem inv_sq_im (a y x : ℝ) :
    ((((a + x : ℝ) : ℂ) + (y : ℂ) * Complex.I)⁻¹ ^ 2).im =
      -(2 * y * (a + x)) / (((a + x) ^ 2 + y ^ 2) ^ 2) := by
  rw [pow_two, Complex.mul_im, Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one,
    zero_add]
  simp only [pow_two, div_eq_mul_inv, mul_inv]
  ring

/-- The imaginary part of the complex kernel is the negative real kernel.
This algebraic identity is the bridge to the signed Gamma remainder. -/
theorem backlundGammaComplexKernel_im (a y x : ℝ) :
    (backlundGammaComplexKernel a y x).im =
      -(backlundGammaWeight x * backlundGammaKernel a y x) := by
  unfold backlundGammaComplexKernel
  rw [Complex.mul_im, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_div, zero_mul, add_zero, inv_sq_im]
  unfold backlundGammaKernel
  ring

private theorem complex_kernel_bound {a y x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    ‖backlundGammaComplexKernel a y x‖ ≤ (x + a)⁻¹ ^ 2 := by
  have hw := backlundGammaWeight_bounds x
  have hp : 0 < x + a := add_pos hx ha
  have hd : 0 < (x + a) ^ 2 := sq_pos_of_pos hp
  have hz : ‖((((a + x : ℝ) : ℂ) + (y : ℂ) * Complex.I))‖ ^ 2 = (x + a) ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one,
      zero_add]
    ring
  unfold backlundGammaComplexKernel
  rw [norm_mul, norm_div, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hw.1, norm_pow, norm_inv, inv_pow, hz]
  have hi : ((x + a) ^ 2 + y ^ 2)⁻¹ ≤ ((x + a) ^ 2)⁻¹ := by
    exact (inv_le_inv₀ (by positivity) hd).2 (by nlinarith only [sq_nonneg y])
  have hn : 0 ≤ ((x + a) ^ 2 + y ^ 2)⁻¹ := inv_nonneg.mpr (by positivity)
  have hh : backlundGammaWeight x / 2 ≤ 1 := by linarith only [hw.2]
  calc
    backlundGammaWeight x / 2 * ((x + a) ^ 2 + y ^ 2)⁻¹ ≤ 1 * ((x + a) ^ 2 + y ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right hh hn
    _ ≤ (x + a)⁻¹ ^ 2 := by simpa only [one_mul, inv_pow] using hi

/-- If `a > 0`, the weighted complex kernel is integrable on `(0,∞)` for
every real `y`. A shifted inverse square dominates its norm. -/
theorem backlundGammaComplexKernel_integrable {a y : ℝ} (ha : 0 < a) :
    MeasureTheory.IntegrableOn (backlundGammaComplexKernel a y) (Set.Ioi 0) := by
  have hg : MeasureTheory.IntegrableOn (fun x : ℝ ↦ (x + a) ^ (-2 : ℝ)) (Set.Ioi 0) :=
    integrableOn_add_rpow_Ioi_of_lt (by norm_num only) (by linarith only [ha])
  have hm : Measurable (backlundGammaComplexKernel a y) := by
    have hw : Measurable backlundGammaWeight := by
      exact measurable_fract.mul (measurable_const.sub measurable_fract)
    exact
      (hw.complex_ofReal.div_const 2).mul
        (((measurable_const.add measurable_id).complex_ofReal.add measurable_const).inv.pow_const 2)
  apply hg.mono' hm.aestronglyMeasurable
  filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Ioi] with
    x hx
  have hp : 0 ≤ x + a := le_of_lt (add_pos hx ha)
  rw [show (-2 : ℝ) = -(↑(2 : ℕ) : ℝ) by norm_num only, Real.rpow_neg hp, Real.rpow_natCast, ←
    inv_pow]
  exact complex_kernel_bound ha hx

/-- For positive `a`, the imaginary part of the complex kernel integral is
the negative of the real positive-kernel integral. Integrability is proved
above, so taking the imaginary part introduces no additional hypothesis. -/
theorem backlundGammaComplexKernel_integral_im {a y : ℝ} (ha : 0 < a) :
    (∫ x in Set.Ioi (0 : ℝ), backlundGammaComplexKernel a y x).im =
      -(∫ x in Set.Ioi (0 : ℝ), backlundGammaWeight x * backlundGammaKernel a y x) := by
  have hi := integral_im (backlundGammaComplexKernel_integrable (y := y) ha)
  simp only [RCLike.im_to_complex, backlundGammaComplexKernel_im, MeasureTheory.integral_neg] at hi
  exact hi.symm

/-- The complex Euler–Maclaurin representation of the Gamma logarithm at
the required heights, allowing an arbitrary real constant. This proposition
specifies the remaining identity and does not assert its proof. -/
def BacklundGammaComplexIdentity : Prop :=
  ∀ t : ℝ,
    2 * Real.pi * Real.exp 1 ≤ t →
      ∃ c : ℝ,
        let z : ℂ := ((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I
        AnalyticNumberTheory.Gamma.logGammaSeries z - ((z - (1 / 2 : ℂ)) * Complex.log z - z) =
          (c : ℂ) + ∫ x in Set.Ioi (0 : ℝ), backlundGammaComplexKernel (1 / 4) (t / 2) x

/-- The complex Gamma integral representation implies the signed real
remainder identity. The real constant vanishes when taking imaginary parts,
and the kernel integral is known to be integrable. -/
theorem gamma_remainder_identity_of_complex (h : BacklundGammaComplexIdentity) :
    BacklundGammaRemainderIdentity := by
  intro t ht
  obtain ⟨c, hc⟩ := h t ht
  unfold backlundGammaRemainder
  dsimp only at hc ⊢
  rw [hc, Complex.add_im, Complex.ofReal_im, zero_add]
  exact backlundGammaComplexKernel_integral_im (by norm_num only)

/-- Under GRH and the Euler-normalized zero-count identity, the complex
Gamma integral representation yields the least-prime `3/11` witness bound
for every odd composite. The integral estimates and classification are
discharged by the preceding bridge. -/
theorem three_eleven_least_of_gamma_complex {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hV : EulerRiemannVonMangoldt)
    (hI : BacklundGammaComplexIdentity) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  exact
    three_eleven_least_of_gamma_integral hn ho hc hGRH hV (gamma_remainder_identity_of_complex hI)

end PseudoPrime.PrimeTestBounds.MillerRabin
