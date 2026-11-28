/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMainXi656
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterZetaMass101
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMainXi656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxSlope656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMainGamma656

/-! # Absolute mass of the common zeta contribution in section 132 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem quarter_norm_transfer656 (t : ℝ) :
    ‖quarterKernel656.function (Complex.I * t)‖ ≤
      (3 / 2) * ‖quarterKernel570.function (Complex.I * t)‖ := by
  rw [quarter_zero_norm_656, quarter_zero_norm_570]
  have h : (51 / 50 : ℝ) ^ 2 + t ^ 2 ≤ (11 / 10 : ℝ) ^ 2 + t ^ 2 := by linarith only
  have hp : 0 < (51 / 50 : ℝ) ^ 2 + t ^ 2 :=
    add_pos_of_pos_of_nonneg (by norm_num only) (sq_nonneg t)
  have hd := pow_le_pow_left₀ hp.le h 3
  have h₁ :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ (11 / 10) ^ 5) (pow_pos hp 3) hd
  calc
    _ ≤ (11 / 10 : ℝ) ^ 5 / ((51 / 50 : ℝ) ^ 2 + t ^ 2) ^ 3 := h₁
    _ ≤ _ := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by norm_num only) (pow_nonneg hp.le 3)

/-- Under RH the zeta mass for the section 132 kernel is at most 1/2000000.
Pointwise comparison reuses the already certified section 101 zero sum. -/
theorem quarter_zeta_mass_656 (hRH : RiemannHypothesis) :
    (∑' ρ, ‖quarterKernel656.zetaKernelZeroTerm ρ‖) ≤ 1 / 2000000 := by
  have ha :=
    (LLS.PaperStatements.MellinKernel.summable_zetaKernelZeroTerm quarterKernel656 hRH).norm
  have hb :=
    (LLS.PaperStatements.MellinKernel.summable_zetaKernelZeroTerm quarterKernel570 hRH).norm
  have h :=
    ha.tsum_le_tsum
      (fun ρ ↦ by
        unfold LLS.PaperStatements.MellinKernel.zetaKernelZeroTerm
        rw [norm_mul, norm_mul, mul_left_comm (3 / 2 : ℝ)]
        exact mul_le_mul_of_nonneg_left (quarter_norm_transfer656 _) (norm_nonneg _))
      (hb.mul_left (3 / 2 : ℝ))
  rw [tsum_mul_left] at h
  linarith only [h, section101_zeta_mass hRH]

/-- Under RH the oscillating zeta zero sum at any scale at least one is
bounded in absolute value by the certified unmodulated zero mass. -/
theorem quarter_main_zero_abs_656 (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    |(∑' ρ, quarterKernel656.zetaOscillatingZeroTerm x ρ).re| ≤ 1 / 2000000 := by
  have hp := zero_lt_one.trans_le hx
  have hs :=
    LLS.PaperStatements.MellinKernel.summable_zetaOscillatingZeroTerm quarterKernel656 hRH hp
  refine (Complex.abs_re_le_norm _).trans ((norm_tsum_le_tsum_norm hs.norm).trans ?_)
  simpa only [LLS.PaperStatements.MellinKernel.norm_zetaOscillatingZeroTerm _ hp] using
    quarter_zeta_mass_656 hRH

/-- Under RH, for radius at least 322 the shifted scales are admissible.
The sum of the absolute weights is at most two, so three copies of the
shifted zeta zero sum cost at most three millionths. -/
theorem quarter_main_xi_mix_lower_656 (hRH : RiemannHypothesis) {r : ℝ} (hr : 322 ≤ r) :
    (-0.000003 : ℝ) ≤ 3 * quarterMainXiMix656 r := by
  have hX := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 322) hr 2
  have hc : (∑ i, |quarterAuxCoeff656 i|) ≤ 2 := by
    have h : (∑ i, |quarterAuxCoeffRat656 i|) ≤ 2 := by decide +kernel
    simpa only [quarterAuxCoeff656, Rat.cast_sum, Rat.cast_abs, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr h
  have h :=
    Finset.abs_sum_le_sum_abs (s := Finset.univ)
      (fun i ↦
        quarterAuxCoeff656 i *
          (∑' ρ,
              quarterKernel656.zetaOscillatingZeroTerm
                (r ^ 2 * Real.exp (-(quarterAuxFrequency656 i))) ρ).re)
  have hb :=
    Finset.sum_le_sum (s := Finset.univ)
      (fun i _ ↦
        mul_le_mul_of_nonneg_left
          (quarter_main_zero_abs_656 hRH (quarter_aux_scale_ge_one_656 hX i))
          (abs_nonneg (quarterAuxCoeff656 i)))
  simp only [abs_mul] at h
  rw [← Finset.sum_mul] at hb
  have hh : |quarterMainXiMix656 r| ≤ _ := h.trans hb
  linarith only [(abs_le.mp hh).1, hc]

/-- For the section 132 radius interval and three even pair characters
agreeing on the prime prefix, include the certified shifted conductor,
residue, reflected Euler and zeta terms in the forward-sum comparison. -/
theorem quarter_forward_aux_gain_656 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hs : 2 ≤ s)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc 322 328)
    (hL : Real.log p + Real.log q + Real.log s = 4 * r)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) :
    (∑' n, quarterKernel656.summand a (r ^ 2) n).re +
        (∑' n, quarterKernel656.summand b (r ^ 2) n).re +
        (∑' n, quarterKernel656.summand c (r ^ 2) n).re +
        quarterAuxTheta656 r +
        quarterAuxNegPole656 / r +
        3.670157088 +
        0.00022760 * r ≤
      quarterCosineContour656 a 0 + quarterCosineContour656 b 0 + quarterCosineContour656 c 0 +
        ((contourRemainder656 a (r ^ 2)).re + (contourRemainder656 b (r ^ 2)).re +
          (contourRemainder656 c (r ^ 2)).re) := by
  have hF := quarter_forward_linear_gain_656 ha hb hc hp hq hs hG hr.1 hL ht hpa hpb hpc
  have hR := quarter_corrected_shift_lower_656 ha hb hc hG.riemann hr hL ht hpa hpb hpc
  have hZ := quarter_main_xi_mix_lower_656 hG.riemann hr.1
  linarith only [hF, hR, hZ]

/-- On the section 132 interval, separate the unshifted conductor, Euler
and common Gamma contributions in the forward comparison. This leaves
the unshifted symmetric zero mass as the only contour term. -/
theorem quarter_forward_main_gain_656 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hs : 2 ≤ s)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc 322 328)
    (hL : Real.log p + Real.log q + Real.log s = 4 * r)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) :
    let x := r ^ 2
    (∑' n, quarterKernel656.summand a x n).re + (∑' n, quarterKernel656.summand b x n).re +
        (∑' n, quarterKernel656.summand c x n).re +
        quarterAuxTheta656 r +
        quarterAuxNegPole656 / r +
        3.670157088 +
        0.00022760 * r +
        (quarterMainEuler656 a x + quarterMainEuler656 b x + quarterMainEuler656 c x) ≤
      quarterCosineContour656 a 0 + quarterCosineContour656 b 0 + quarterCosineContour656 c 0 +
        4 * r * (quarterKernel656.transform x⁻¹).re +
        3 * (quarterLevelGamma656 x).re := by
  intro x
  have hx : 0 < x := pow_pos ((by norm_num only : (0 : ℝ) < 322).trans_le hr.1) 2
  have h := quarter_forward_aux_gain_656 ha hb hc hp hq hs hG hr hL ht hpa hpb hpc
  rw [quarter_main_arch_split_656 ha.1 ha.2.1 ha.2.2.1 hx,
    quarter_main_arch_split_656 hb.1 hb.2.1 hb.2.2.1 hx,
    quarter_main_arch_split_656 hc.1 hc.2.1 hc.2.2.1 hx,
    quarter_even_level_gamma_656 a ha.2.1 ha.2.2.2 x,
    quarter_even_level_gamma_656 b hb.2.1 hb.2.2.2 x,
    quarter_even_level_gamma_656 c hc.2.1 hc.2.2.2 x] at h
  have hP :
    (quarterKernel656.transform x⁻¹).re =
      Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) x⁻¹ := by
    rw [quarterKernel656, LLS.PaperStatements.rationalPole_transform _ _ _ _ (inv_pos.mpr hx),
      Complex.ofReal_re]
  rw [hP, ← hL, add_mul, add_mul]
  dsimp only [x] at h ⊢
  linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
