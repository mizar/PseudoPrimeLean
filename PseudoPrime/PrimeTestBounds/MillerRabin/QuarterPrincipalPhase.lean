/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalZeros
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiSign100RH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCount100RH
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAbel570
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.FiniteZeroSums
import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMassBounds
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Principal phase bound from the certified zeta zeros -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The certified height-100 zeros give the uniform lower bound for the
finite phase sum under RH, with the count and bracket conditions discharged. -/
theorem section104_phase_lower_of_RH (hRH : RiemannHypothesis) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) {X : ℝ} (hX : 0 < X) :
    -0.0217976 ≤
      ∑ ρ ∈ S,
        ((AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
            ((X : ℂ) ^ ρ / (Real.sqrt X : ℂ)) *
            section99PhaseKernel ρ).re := by
  obtain ⟨g, hm, hp, ht, hζ, hg, _⟩ := AnalyticNumberTheory.RiemannZeta.low_zero_100_exists
  have hc := AnalyticNumberTheory.RiemannZeta.count_100_eq_58_of_RH hRH
  have hh := AnalyticNumberTheory.RiemannZeta.critical_zeros_complete_simple hRH hc.le g hm hp ht hζ
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hh
  exact section104_finite_phase_lower (g := g) (X := X) hRH hc S hz hre hg hm hp hh.1 hh.2 hX

/-- Every rectangular truncation used in the logarithmic explicit formula
inherits the same phase lower bound under RH. -/
theorem section104_rect_phase_lower (hRH : RiemannHypothesis) (k : ℕ) {X : ℝ} (hX : 0 < X) :
    -0.0217976 ≤
      ∑
        ρ ∈
          (AnalyticNumberTheory.RiemannZeta.riemannZetaZerosInAnyRectangle
                (AnalyticNumberTheory.RiemannZeta.unifiedRectangleLower k)
                (AnalyticNumberTheory.RiemannZeta.unifiedTauRectangleUpper 2 k)).filter
            (fun ρ ↦ ¬ρ.re < 0),
        ((AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
            ((X : ℂ) ^ ρ / (Real.sqrt X : ℂ)) *
            section99PhaseKernel ρ).re := by
  apply section104_phase_lower_of_RH hRH _ _ _ hX
  · intro ρ hρ
    exact
      (AnalyticNumberTheory.RiemannZeta.mem_riemannZetaZerosInAnyRectangle_iff.mp
          (Finset.mem_filter.mp hρ).1).2
  · intro ρ hρ
    exact not_lt.mp (Finset.mem_filter.mp hρ).2

/-- Under RH a finite nontrivial-zero family has inverse-square ordinate
mass at most 0.0505. The low-zero gap controls the change of denominator. -/
private theorem section99_finite_ordinate_mass (hRH : RiemannHypothesis) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) :
    (∑ ρ ∈ S, (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) ≤
      0.0505 := by
  have h := AnalyticNumberTheory.RiemannZeta.sum_zetaZeroMultiplicity_invNormSq_le hRH S hz hre
  have hm := AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_one_fortieth
  calc
    _ ≤
        ∑ ρ ∈ S,
          (101 / 100 : ℝ) *
            ((AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) /
              Complex.normSq ρ) :=
      by
      apply Finset.sum_le_sum
      intro ρ hρ
      have hxi :=
        AnalyticNumberTheory.RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg (hz ρ hρ) (hre ρ hρ)
      have hr := AnalyticNumberTheory.RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hxi
      have ht := AnalyticNumberTheory.RiemannZeta.zero_height_gt_two_pi hRH (hz ρ hρ) (hre ρ hρ)
      have ht6 : 6 ≤ |ρ.im| := by linarith only [ht, Real.pi_gt_three]
      have hs := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 6) ht6 2
      have hn : 0 < Complex.normSq ρ := by
        rw [Complex.normSq_apply, hr]
        nlinarith only [sq_nonneg ρ.im]
      have hd : Complex.normSq ρ ≤ (101 / 100) * |ρ.im| ^ 2 := by
        rw [Complex.normSq_apply, hr, sq_abs]
        rw [sq_abs] at hs
        nlinarith only [hs]
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ (sq_pos_of_pos (by linarith only [ht6])) hn).2
      have hh :=
        mul_le_mul_of_nonneg_left hd
          (Nat.cast_nonneg (α := ℝ)
            (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ))
      simpa only [mul_left_comm, mul_assoc] using hh
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      linarith only [h, hm]

/-- At radius at least 292 the physical endpoint weight is bounded
by the existing uniform reflected-weight envelope. -/
private theorem section99_weight_one_le {r : ℝ} (hl : 292 ≤ r) :
    quarterWeight570 (r ^ 2) 1 ≤ 0.002861 := by
  have hr : 0 < r := by linarith only [hl]
  have hx := sq_pos_of_pos hr
  have hlog := Real.log_nonneg (one_le_pow₀ (show 1 ≤ r by linarith only [hl]) (n := 2))
  have hw : quarterWeight570 (r ^ 2) 1 = (quarterKernel570.transform (1 / r ^ 2)).re := by
    rw [quarterKernel570, LLS.PaperStatements.rationalPole_transform _ _ _ _ (one_div_pos.mpr hx),
      Complex.ofReal_re, Analysis.rationalPoleProfile,
      ite_eq_left
        ⟨one_div_pos.mpr hx, by
          rw [one_div, Real.log_inv]; linarith only [hlog]⟩]
    norm_num only [quarterWeight570, Real.sqrt_one, div_one, Nat.reduceMul, Nat.reduceSub,
      Nat.factorial, Nat.cast_ofNat, one_mul]
  rw [hw]
  linarith only [reflected_weight_upper_of_288 ((by norm_num only : (288 : ℝ) ≤ 292).trans hl)]

/-- An eventual lower bound on the truncated normalized phase sums gives
a lower bound on the physical Abel action with a uniform loss of 0.00045.
The loss bounds the two corrections at the physical lower cutoff. -/
theorem section99_nontrivial_of_phase (hRH : RiemannHypothesis) {r B : ℝ} (hl : 292 ≤ r)
    (hphase :
      ∀ᶠ k : ℕ in Filter.atTop,
        B ≤
          ∑
            ρ ∈
              (AnalyticNumberTheory.RiemannZeta.riemannZetaZerosInAnyRectangle
                    (AnalyticNumberTheory.RiemannZeta.unifiedRectangleLower k)
                    (AnalyticNumberTheory.RiemannZeta.unifiedTauRectangleUpper 2 k)).filter
                (fun ρ ↦ ¬ρ.re < 0),
            ((AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
                (((r ^ 2 : ℝ) : ℂ) ^ ρ / (Real.sqrt (r ^ 2) : ℂ)) *
                section99PhaseKernel ρ).re) :
    section99AbelAction (r ^ 2)
        (fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) ≥
      B - 0.00045 := by
  have hx : 1 ≤ r ^ 2 := one_le_pow₀ (by linarith only [hl]) (n := 2)
  have hb : 14 ≤ 14 / 5 + Real.log (r ^ 2) := by
    have h :=
      (Analysis.rationalLogIntervalCheck_sound (N := 292) (j := 8) (n := 20) (lo := 227 / 40) (hi :=
          6) (by decide +kernel)).1
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
    rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [h, Real.log_le_log (by norm_num only) hl]
  apply ge_of_tendsto (section99_zero_integral_limit hx)
  filter_upwards [hphase] with k hp
  let S :=
    (AnalyticNumberTheory.RiemannZeta.riemannZetaZerosInAnyRectangle
          (AnalyticNumberTheory.RiemannZeta.unifiedRectangleLower k)
          (AnalyticNumberTheory.RiemannZeta.unifiedTauRectangleUpper 2 k)).filter
      (fun ρ ↦ ¬ρ.re < 0)
  let F := fun ρ : ℂ ↦
    ((AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
        (((r ^ 2 : ℝ) : ℂ) ^ ρ / (Real.sqrt (r ^ 2) : ℂ)) *
        section99PhaseKernel ρ).re
  let M := fun ρ : ℂ ↦
    (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2
  have hz (ρ : ℂ) (hρ : ρ ∈ S) : riemannZeta ρ = 0 :=
    (AnalyticNumberTheory.RiemannZeta.mem_riemannZetaZerosInAnyRectangle_iff.mp
        (Finset.mem_filter.mp hρ).1).2
  have hre (ρ : ℂ) (hρ : ρ ∈ S) : 0 ≤ ρ.re := not_lt.mp (Finset.mem_filter.mp hρ).2
  have hterm (ρ : ℂ) (hρ : ρ ∈ S) :
    F ρ - (153 / 50) * 0.002861 * M ρ ≤ section99ZeroIntegral (r ^ 2) ρ := by
    have hi := AnalyticNumberTheory.RiemannZeta.zero_height_gt_two_pi hRH (hz ρ hρ) (hre ρ hρ)
    have hxi :=
      AnalyticNumberTheory.RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg (hz ρ hρ) (hre ρ hρ)
    have hR := AnalyticNumberTheory.RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hxi
    have h :=
      (abs_le.mp (section99_zero_lower_error hx hb (by linarith only [hi, Real.pi_gt_three]) hR)).1
    have hm : 0 ≤ M ρ := div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    have hw :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (section99_weight_one_le hl)
          (by norm_num only : (0 : ℝ) ≤ 153 / 50))
        hm
    change
      -((153 / 50) * quarterWeight570 (r ^ 2) 1 * M ρ) ≤ section99ZeroIntegral (r ^ 2) ρ - F ρ at h
    linarith only [h, hw]
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have hm : ∑ ρ ∈ S, M ρ ≤ 0.0505 := section99_finite_ordinate_mass hRH S hz hre
  change B - 0.00045 ≤ ∑ ρ ∈ S, section99ZeroIntegral (r ^ 2) ρ
  linarith only [hsum, hp, hm]

/-- The nontrivial-zero contribution to the physical Abel action is
bounded below by minus 0.02225 at all radii from 292 onward under RH. -/
theorem section99_nontrivial_lower (hRH : RiemannHypothesis) {r : ℝ} (hl : 292 ≤ r) :
    section99AbelAction (r ^ 2)
        (fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) ≥
      -0.02225 := by
  have hr : 0 < r := by linarith only [hl]
  have h :=
    section99_nontrivial_of_phase hRH hl
      (Filter.Eventually.of_forall (fun k ↦ section104_rect_phase_lower hRH k (sq_pos_of_pos hr)))
  linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
