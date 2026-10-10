/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelFiniteContour
public import PseudoPrime.LLS.MellinKernelZeros
public import PseudoPrime.LLS.MellinKernelArithmeticMellin
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.LogDerivZeta
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.ShiftedZeros

/-!
# Principal-character Mellin contour and xi zero terms

The zeta logarithmic derivative supplies the level-one arithmetic contour.
Quadratic kernel decay and xi inverse-square mass bound its oscillatory zero sum.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

open AnalyticNumberTheory.RiemannXi in
/-- The multiplicity of a xi zero times the kernel value at its imaginary height.
The zero subtype records nonvanishing multiplicity support and avoids the pole of zeta.
This is the unmodulated zero term for the principal-character Mellin formula. -/
noncomputable def zetaKernelZeroTerm (K : MellinKernel) (ρ : Zero) : ℂ :=
  (riemannXiZeroMultiplicity (ρ : ℂ) : ℂ) * K.function (Complex.I * (ρ : ℂ).im)

open AnalyticNumberTheory.RiemannXi in
/-- Under RH and a positive imaginary-axis decay bound, each xi zero term is bounded
by the decay constant times its inverse-square multiplicity mass. The critical-line
identity permits the kernel denominator comparison. This majorizes the zeta zero sum. -/
theorem norm_zetaKernelZeroTerm_le (K : MellinKernel) (hRH : RiemannHypothesis) {C : ℝ} (hC : 0 < C)
    (hb : ∀ t : ℝ, ‖K.function (Complex.I * t)‖ ≤ C / (1 + t ^ 2)) (ρ : Zero) :
    ‖K.zetaKernelZeroTerm ρ‖ ≤ C * ((riemannXiZeroMultiplicity (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2) := by
  have hr := riemannXi_zero_re_eq_half_of_riemannHypothesis hRH ρ.property
  have hk := norm_kernel_le_inv_normSq K hC hb hr
  rw [Complex.normSq_eq_norm_sq] at hk
  rw [zetaKernelZeroTerm, norm_mul, Complex.norm_natCast]
  calc
    _ ≤ (riemannXiZeroMultiplicity (ρ : ℂ) : ℝ) * (C / ‖(ρ : ℂ)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg _)
    _ = _ := by ring

open AnalyticNumberTheory.RiemannXi in
/-- Under RH, the xi zero kernel terms are absolutely summable for every Mellin kernel.
Compare with the existing inverse-square xi zero mass using quadratic kernel decay.
This permits the infinite zero sum in the principal-character explicit formula. -/
theorem summable_zetaKernelZeroTerm (K : MellinKernel) (hRH : RiemannHypothesis) :
    Summable K.zetaKernelZeroTerm := by
  obtain ⟨C, hC, hb⟩ := exists_vertical_decay_bound K
  have hs := summable_inverse_square_mass_of_riemannHypothesis hRH
  exact (hs.mul_left C).of_norm_bounded (norm_zetaKernelZeroTerm_le K hRH hC hb)

open AnalyticNumberTheory.RiemannXi in
/-- The xi zero kernel term multiplied by the phase `x^(i Im rho)`.
For positive scale the phase has norm one. These terms are the zero contribution
in the principal-character Mellin contour after shifting the critical line to zero. -/
noncomputable def zetaOscillatingZeroTerm (K : MellinKernel) (x : ℝ) (ρ : Zero) : ℂ :=
  K.zetaKernelZeroTerm ρ * (x : ℂ) ^ (Complex.I * (ρ : ℂ).im)

open AnalyticNumberTheory.RiemannXi in
/-- At positive scale, an oscillatory xi zero term has the unmodulated term's norm.
The phase exponent has zero real part, so its complex power has unit norm.
This transfers convergence and uniform bounds to the oscillating zero series. -/
theorem norm_zetaOscillatingZeroTerm (K : MellinKernel) {x : ℝ} (hx : 0 < x) (ρ : Zero) :
    ‖K.zetaOscillatingZeroTerm x ρ‖ = ‖K.zetaKernelZeroTerm ρ‖ := by
  rw [zetaOscillatingZeroTerm, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, Real.rpow_zero, mul_one]

/-- Under RH and at positive scale, the oscillatory xi zero series is absolutely
summable. Its term norms equal those of the proved summable unmodulated series.
This justifies the principal-character contour zero sum. -/
theorem summable_zetaOscillatingZeroTerm (K : MellinKernel) (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 0 < x) : Summable (K.zetaOscillatingZeroTerm x) := by
  exact
    (summable_zetaKernelZeroTerm K hRH).norm.of_norm_bounded
      (fun ρ => (norm_zetaOscillatingZeroTerm K hx ρ).le)

/-- Under RH, a positive constant bounds the norm of the oscillatory xi zero sum
at every positive scale. Absolute summability and the triangle inequality bound it
by the fixed unmodulated absolute mass. This supplies a bounded zero contribution
to the principal-character remainder in Lemma 6.1. -/
theorem exists_norm_tsum_zetaOscillatingZeroTerm_le (K : MellinKernel) (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ {x : ℝ}, 0 < x → ‖∑' ρ, K.zetaOscillatingZeroTerm x ρ‖ ≤ C := by
  let M := ∑' ρ, ‖K.zetaKernelZeroTerm ρ‖
  have hM : 0 ≤ M := tsum_nonneg (fun ρ => norm_nonneg _)
  refine ⟨M + 1, add_pos_of_nonneg_of_pos hM zero_lt_one, ?_⟩
  intro x hx
  have h : ‖∑' ρ, K.zetaOscillatingZeroTerm x ρ‖ ≤ M := by
    calc
      _ ≤ ∑' ρ, ‖K.zetaOscillatingZeroTerm x ρ‖ :=
        norm_tsum_le_tsum_norm (summable_zetaOscillatingZeroTerm K hRH hx).norm
      _ = M := tsum_congr (norm_zetaOscillatingZeroTerm K hx)
  exact h.trans (le_add_of_nonneg_right zero_le_one)

/-- To the right of one, the weighted negative zeta logarithmic derivative splits
into the xi part and the pole and shifted-gamma terms. Rewrite the existing xi
completion identity and distribute the weight. This identifies the principal contour. -/
theorem zeta_arithmetic_logDeriv_eq_xi_add_pole_gamma {s : ℂ} (hs : 1 < s.re) (w : ℂ) :
    -logDeriv riemannZeta s * w =
      -logDeriv PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXi s * w +
        (1 / (s - 1) - Complex.log (Real.pi : ℂ) / 2 + Complex.digamma (s / 2 + 1) / 2) * w := by
  rw [PseudoPrime.AnalyticNumberTheory.RiemannXi.logDeriv_eq_pole_gamma_zeta_of_one_lt_re hs]
  ring

/-- For a positive scale and a right strip line above one half, the level-one
principal arithmetic sum is the normalized weighted zeta logarithmic derivative
integral. Identify the level-one L-function with zeta in the general arithmetic
Mellin formula. This is the starting contour for the principal estimate. -/
theorem tsum_level_one_summand_eq_integral_zeta_logDeriv (K : MellinKernel) {x c : ℝ} (hx : 0 < x)
    (hc : 1 / 2 < c) (hc' : c ≤ 1 / 2 + K.delta) :
    (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x n) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ,
          -logDeriv riemannZeta (((c : ℂ) + Complex.I * t) + 1 / 2) *
            (K.function ((c : ℂ) + Complex.I * t) * (x : ℂ) ^ ((c : ℂ) + Complex.I * t)) := by
  simpa only [DirichletCharacter.LFunction_modOne_eq] using
    tsum_summand_eq_integral_logDeriv K (1 : DirichletCharacter ℂ 1) hx hc hc'

open AnalyticNumberTheory.RiemannXi in
/-- Under RH, the weighted residue at a shifted xi zero equals the negative
oscillatory zeta zero term for any real scale. Translation preserves analytic order,
and RH identifies the shifted zero with its imaginary height. This matches finite
xi contour residues to the absolutely convergent zeta zero series. -/
theorem weightedResidue_xi_zero_eq_neg_zetaOscillatingZeroTerm (K : MellinKernel)
    (hRH : RiemannHypothesis) (x : ℝ) (ρ : Zero) :
    weightedResidue K (fun z : ℂ => riemannXi (z + 1 / 2)) x ((ρ : ℂ) - 1 / 2) =
      -K.zetaOscillatingZeroTerm x ρ := by
  have hr := riemannXi_zero_re_eq_half_of_riemannHypothesis hRH ρ.property
  have he : (ρ : ℂ) - 1 / 2 = Complex.I * (ρ : ℂ).im := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re, hr, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
        sub_self]
    · simp only [Complex.sub_im, Complex.div_ofNat_im, Complex.one_im, zero_div, sub_zero,
        Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        one_mul, zero_add]
  have hne : (ρ : ℂ) - 1 / 2 ≠ -1 / 2 := by
    intro h
    have hz : (ρ : ℂ) = 0 := by linear_combination h
    have hzero := ρ.property
    rw [hz, riemannXi_zero] at hzero
    norm_num only at hzero
  have hm :
    analyticOrderNatAt (fun z : ℂ => riemannXi (z + 1 / 2)) ((ρ : ℂ) - 1 / 2) =
      riemannXiZeroMultiplicity (ρ : ℂ) := by
    rw [analyticOrderNatAt, shifted_analyticOrderAt, sub_add_cancel]
    rfl
  rw [weightedResidue, ite_eq_right hne, hm, he, zetaOscillatingZeroTerm, zetaKernelZeroTerm]
  ring

open AnalyticNumberTheory AnalyticNumberTheory.RiemannXi in
/-- For a positive scale and an ordered rectangle in the kernel strip, an interior
finite ledger covering shifted xi zeros and the kernel pole gives the xi weighted
contour identity. Entirety of xi and nonvanishing at zero discharge the analytic and
finite-order hypotheses; translation has derivative one. This is the finite stage
of the principal-character contour before the infinite zero sum is taken. -/
theorem xiFiniteContourIdentity (K : MellinKernel) {x : ℝ} (hx : 0 < x) {z w : ℂ}
    (hre : z.re < w.re) (him : z.im < w.im) (hregion : Rectangle.rectangleClosedBox z w ⊆ K.region)
    (S : Finset ℂ) (hclosed : ∀ s ∈ S, s ∈ Rectangle.rectangleClosedBox z w)
    (hopen : ∀ s ∈ S, s ∈ RectangleGeometry.rectangleOpenBox z w)
    (hcover :
      ∀ s ∈ Rectangle.rectangleClosedBox z w, s = -1 / 2 ∨ riemannXi (s + 1 / 2) = 0 → s ∈ S) :
    RectangleGeometry.rectangleBoundaryIntegral
        (fun s => -logDeriv riemannXi (s + 1 / 2) * (K.function s * (x : ℂ) ^ s)) z w =
      ∑ s ∈ S,
        2 * Real.pi * Complex.I * weightedResidue K (fun t : ℂ => riemannXi (t + 1 / 2)) x s := by
  have hF : AnalyticOnNhd ℂ (fun s : ℂ => riemannXi (s + 1 / 2)) K.region := fun s _ =>
    (differentiable_riemannXi.analyticAt (s + 1 / 2)).comp (f := fun t : ℂ => t + 1 / 2) (x := s)
      (analyticAt_id.add analyticAt_const)
  have hp : riemannXi ((-1 / 2 : ℂ) + 1 / 2) ≠ 0 := by
    rw [neg_div, neg_add_cancel, riemannXi_zero]
    norm_num only
  have hfinite : ∀ s ∈ S, analyticOrderAt (fun t : ℂ => riemannXi (t + 1 / 2)) s ≠ ⊤ := by
    intro s _
    exact shifted_analyticOrderAt_ne_top s
  have h := weightedFiniteContourIdentity K hx hre him hregion hF hp S hclosed hopen hcover hfinite
  simpa only [logDeriv_shifted] using h

end PseudoPrime.LLS.PaperStatements.MellinKernel
