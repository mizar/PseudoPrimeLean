/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseBoxes656
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhasePairs656
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMellinPhase656
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalLimit656
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalTail663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseRows644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalCorrection644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseBoxes656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseCertificate644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseTransfer656

/-! # Low-zero phase endpoints for the quarter-square bridge -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
-- Check the rotations and the rounded sum at 29 positive ordinates.
/-- The paired low-zero phase at radius 329 is at least 4500000/10^9. -/
theorem quarter_bridge_phase_329 {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) :
    4500000 / 1000000000 ≤
      pairedPhase g (fun i ↦ quarterPhaseKernel656 (g i)) (2 * Real.log (329)) := by
  have hx :=
    radius_log_box (r := 329) (lo := 5796057740765 / 1000000000000) (hi :=
      5796057760766 / 1000000000000) (a := 1159211548153000000000) (b := 1159211552153200000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [Rat.cast_ofNat] at hx
  have h :=
    endpoint_rational_lower656 hl hu hx (by decide +kernel) (B := 4500000 / 1000000000)
      (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
-- Check the rotations and the rounded sum at 29 positive ordinates.
/-- The paired low-zero phase at radius 330 is at least 4320000/10^9. -/
theorem quarter_bridge_phase_330 {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) :
    4320000 / 1000000000 ≤
      pairedPhase g (fun i ↦ quarterPhaseKernel656 (g i)) (2 * Real.log (330)) := by
  have hx :=
    radius_log_box (r := 330) (lo := 5799092644460 / 1000000000000) (hi :=
      5799092664461 / 1000000000000) (a := 1159818528892000000000) (b := 1159818532892200000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [Rat.cast_ofNat] at hx
  have h :=
    endpoint_rational_lower656 hl hu hx (by decide +kernel) (B := 4320000 / 1000000000)
      (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
-- Check the rotations and the rounded sum at 29 positive ordinates.
/-- The paired low-zero phase at radius 663 / 2 is at least 4020000/10^9. -/
theorem quarter_bridge_phase_33150 {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) :
    4020000 / 1000000000 ≤
      pairedPhase g (fun i ↦ quarterPhaseKernel656 (g i)) (2 * Real.log (663 / 2)) := by
  have hx :=
    radius_log_box (r := 663 / 2) (lo := 5803627799625 / 1000000000000) (hi :=
      5803627819626 / 1000000000000) (a := 1160725559925000000000) (b := 1160725563925200000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [Rat.cast_div, Rat.cast_ofNat] at hx
  have h :=
    endpoint_rational_lower656 hl hu hx (by decide +kernel) (B := 4020000 / 1000000000)
      (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

/-- The established curvature cap transfers two bounds on the paired low-zero
phase to every radius in the closed interval between them. -/
theorem quarter_bridge_phase_between {g : Fin 29 → ℝ}
    (hlo : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hhi : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) {l u r v : ℝ} (hl : 0 < l)
    (hr : r ∈ Set.Icc l u)
    (hleft : v ≤ pairedPhase g (fun i ↦ quarterPhaseKernel656 (g i)) (2 * Real.log l))
    (hright : v ≤ pairedPhase g (fun i ↦ quarterPhaseKernel656 (g i)) (2 * Real.log u)) :
    v - 29 * (u - l) ^ 2 / (2 * l ^ 2) ≤
      pairedPhase g (fun i ↦ quarterPhaseKernel656 (g i)) (2 * Real.log r) := by
  let C := fun i : Fin 29 ↦ quarterPhaseKernel656 (g i)
  let D := fun i ↦ ((g i : ℂ) * Complex.I) * C i
  let E := fun i ↦ ((g i : ℂ) * Complex.I) * D i
  have hC : 2 * (∑ i : Fin 29, (g i) ^ 2 * ‖C i‖) ≤ 29 :=
    (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum
            (fun i _ ↦ mul_le_mul_of_nonneg_left (phase_kernel_norm (g i)) (sq_nonneg _)))
          (by norm_num only : (0 : ℝ) ≤ 2)).trans
      (quarter_phase_curvature_656 hlo hhi)
  have h :=
    log_phase_lower_of_curvature (f := pairedPhase g C) (f' := pairedPhase g D) (f'' :=
      pairedPhase g E) hl hr (by norm_num only : (0 : ℝ) ≤ 29)
      (fun x _ ↦ (paired_phase_deriv g C x).continuousAt.continuousWithinAt)
      (fun x _ ↦ paired_phase_deriv g C x) (fun x _ ↦ paired_phase_deriv g D x)
      (fun x _ ↦
        (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ ↦ phase_term_upper x (g i) (C i)))
              (by norm_num only : (0 : ℝ) ≤ 2)).trans
          hC)
  exact (sub_le_sub_right (le_min hleft hright) _).trans h

/-- The three closed radius intervals share a lower bound for the
oscillating zero sum at every height at least 100. -/
theorem quarter_bridge_phase_trunc (hRH : RiemannHypothesis) {r T : ℝ}
    (hr : r ∈ Set.Icc 328 (663 / 2)) (hT : 100 ≤ T) :
    (-0.002883 : ℝ) ≤
      (∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo T,
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          (Complex.exp (Complex.I * ((2 * Real.log r * ρ.im : ℝ) : ℂ)) *
              quarterPhaseKernel656 ρ.im).re) := by
  obtain ⟨g, hm, hp, hu, hz, hlo, hhi⟩ := AnalyticNumberTheory.RiemannZeta.low_zero_100_exists
  let Z := fun t : ℝ ↦ pairedPhase g (fun i ↦ quarterPhaseKernel656 (g i)) (2 * Real.log t)
  have e₁ : (0.0045 : ℝ) ≤ Z 329 :=
    (by norm_num only : (0.0045 : ℝ) ≤ 4500000 / 1000000000).trans
      (quarter_bridge_phase_329 hlo hhi)
  have e₂ : (0.00432 : ℝ) ≤ Z 330 :=
    (by norm_num only : (0.00432 : ℝ) ≤ 4320000 / 1000000000).trans
      (quarter_bridge_phase_330 hlo hhi)
  have e₃ : (0.00402 : ℝ) ≤ Z (663 / 2) :=
    (by norm_num only : (0.00402 : ℝ) ≤ 4020000 / 1000000000).trans
      (quarter_bridge_phase_33150 hlo hhi)
  have hhead : (0.00371 : ℝ) ≤ Z r := by
    by_cases h₁ : r ≤ 329
    · have e₀ : (0.0045 : ℝ) ≤ Z 328 :=
        (by norm_num only : (0.0045 : ℝ) ≤ 4706101 / 1000000000).trans
          (quarter_phase_endpoint_656_328 hlo hhi)
      have h := quarter_bridge_phase_between hlo hhi (by norm_num only) ⟨hr.1, h₁⟩ e₀ e₁
      linarith only [h]
    by_cases h₂ : r ≤ 330
    · have h :=
        quarter_bridge_phase_between hlo hhi (by norm_num only) ⟨le_of_not_ge h₁, h₂⟩
          ((by norm_num only : (0.00432 : ℝ) ≤ 0.0045).trans e₁) e₂
      linarith only [h]
    · have h :=
        quarter_bridge_phase_between hlo hhi (by norm_num only) ⟨le_of_not_ge h₂, hr.2⟩
          ((by norm_num only : (0.00402 : ℝ) ≤ 0.00432).trans e₂) e₃
      linarith only [h]
  have ht := quarter_phase_truncation_lower_656 hRH hm hp hu hz hT (2 * Real.log r) (Z r) le_rfl
  linarith only [hhead, ht]

/-- The oscillating sum still has a uniform lower bound after charging
the scalar remainder over all three bridge intervals. -/
theorem quarter_bridge_phase_lower (hRH : RiemannHypothesis) {r T : ℝ}
    (hr : r ∈ Set.Icc 328 (663 / 2)) (hT : 100 ≤ T) :
    (-0.00555 : ℝ) ≤
      (∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo T,
          (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
            (Complex.exp (Complex.I * ((2 * Real.log r * ρ.im : ℝ) : ℂ)) *
                quarterPhaseKernel656 ρ.im).re) -
        quarterPhaseRem656 r := by
  have hrem := quarter_phase_rem_le_656 ((by norm_num only : (322 : ℝ) ≤ 328).trans hr.1)
  linarith only [quarter_bridge_phase_trunc hRH hr hT, hrem]

/-- Express the bridge lower bound in Mellin normalization, so it can
be used with the centered principal Abel formula. -/
theorem quarter_bridge_mellin_lower (hRH : RiemannHypothesis) {r T : ℝ}
    (hr : r ∈ Set.Icc 328 (663 / 2)) (hT : 100 ≤ T) :
    (-0.00555 : ℝ) ≤
      (∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo T,
          (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
            ((((r ^ 2 : ℝ) : ℂ) ^ ρ / (Real.sqrt (r ^ 2) : ℂ)) * quarterMellinPhase656 ρ).re) -
        quarterPhaseRem656 r := by
  apply (quarter_bridge_phase_lower hRH hr hT).trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hT₀ := (by norm_num only : (0 : ℝ) ≤ 100).trans hT
  have hzero := (AnalyticNumberTheory.RiemannZeta.mem_zerosUpTo hT₀).mp hρ
  have hxi := AnalyticNumberTheory.RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hzero.1 hzero.2.1
  rw [quarter_mellin_cutoff_phase_656 ((by norm_num only : (0 : ℝ) < 328).trans_le hr.1)
      (AnalyticNumberTheory.RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hxi)]

private theorem bridge_weight_one {r : ℝ} (hr : 328 ≤ r) : quarterWeight656 (r ^ 2) 1 ≤ 0.0014 := by
  have hr₀ := (by norm_num only : (0 : ℝ) < 328).trans_le hr
  have hx : 1 ≤ r ^ 2 := one_le_pow₀ ((by norm_num only : (1 : ℝ) ≤ 328).trans hr)
  have hu := inv_pos.mpr (sq_pos_of_pos hr₀)
  have hl : Real.log (r ^ 2)⁻¹ ≤ 21 / 8 := by
    rw [Real.log_inv]
    linarith only [Real.log_nonneg hx]
  have he : quarterWeight656 (r ^ 2) 1 = (quarterKernel656.transform (r ^ 2)⁻¹).re := by
    rw [quarter_transform_656 hu hl]
    unfold quarterWeight656
    simp only [Real.sqrt_one, div_one, one_mul, one_div]
  have h := quarter_main_conductor_box_663 hr
  have hb : 4 * r * quarterWeight656 (r ^ 2) 1 ≤ 1.659189 := by
    rw [he]
    split_ifs at h <;> linarith only [h]
  by_contra! hn
  have hm := mul_le_mul_of_nonneg_left hn.le (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hr₀.le)
  linarith only [hm, hb, hr]

private theorem bridge_correction_sum (hRH : RiemannHypothesis) {r : ℝ} (hr : 328 ≤ r)
    (S : Finset ℂ) (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) :
    (∑ ρ ∈ S, |quarterPhaseCorrection656 (r ^ 2) ρ|) ≤ 0.000234 := by
  have h1 := (by norm_num only : (1 : ℝ) ≤ 328).trans hr
  have hX : 1 ≤ r ^ 2 := one_le_pow₀ h1
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 27) (lo := 57 / 10) (hi := 6)
        (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlo
  have hb : 14 ≤ 21 / 8 + Real.log (r ^ 2) := by
    rw [Real.log_pow]
    linarith only [hlo, Real.log_le_log (by norm_num only : (0 : ℝ) < 328) hr]
  have h := finite_ordinate_mass hRH S hz hre
  calc
    _ ≤
        ∑ ρ ∈ S,
          (33 / 10) * 0.0014 *
            ((AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) :=
      by
      apply Finset.sum_le_sum
      intro ρ hρ
      have hξ :=
        AnalyticNumberTheory.RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg (hz ρ hρ) (hre ρ hρ)
      have ht := AnalyticNumberTheory.RiemannZeta.zero_height_gt_two_pi hRH (hz ρ hρ) (hre ρ hρ)
      have hl := AnalyticNumberTheory.RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hξ
      exact
        (quarter_correction_bound_656 hX hb (by linarith only [ht, Real.pi_gt_three]) hl).trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (bridge_weight_one hr) (by norm_num only)) (by positivity))
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      linarith only [h]

private theorem zero_abel_of_phase (hRH : RiemannHypothesis) {r B : ℝ} (hr : 328 ≤ r)
    (hphase :
      ∀ T : ℝ,
        100 ≤ T →
          B ≤
            ∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo T,
              (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
                (Complex.exp (Complex.I * ((2 * Real.log r * ρ.im : ℝ) : ℂ)) *
                    quarterPhaseKernel656 ρ.im).re) :
    B - 0.000234 ≤
      quarterAbelAction656 (r ^ 2)
        (fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) := by
  have h1 := (by norm_num only : (1 : ℝ) ≤ 328).trans hr
  apply ge_of_tendsto (quarter_zero_integral_limit_656 (one_le_pow₀ h1 (n := 2)))
  filter_upwards [Filter.tendsto_atTop.mp
      AnalyticNumberTheory.RiemannZeta.tendsto_unifiedContourHeightSeq_atTop 100] with
    k hk
  have hT := (by norm_num only : (0 : ℝ) ≤ 100).trans hk
  rw [unified_ledger_eq k hT]
  let S :=
    AnalyticNumberTheory.RiemannZeta.zerosUpTo
      (AnalyticNumberTheory.RiemannZeta.unifiedContourHeightSeq k)
  have hm {ρ : ℂ} (hρ : ρ ∈ S) := (AnalyticNumberTheory.RiemannZeta.mem_zerosUpTo hT).mp hρ
  have hc := bridge_correction_sum hRH hr S (fun _ hρ ↦ (hm hρ).1) (fun _ hρ ↦ (hm hρ).2.1)
  have hd :
    -(∑ ρ ∈ S, |quarterPhaseCorrection656 (r ^ 2) ρ|) ≤
      ∑ ρ ∈ S, quarterPhaseCorrection656 (r ^ 2) ρ := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun ρ _ ↦ neg_abs_le _)
  have he :=
    Finset.sum_congr (s₁ := S) rfl
      (fun ρ hρ ↦
        quarter_physical_phase_656 h1
          (AnalyticNumberTheory.RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH
            (AnalyticNumberTheory.RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg (hm hρ).1
              (hm hρ).2.1)))
  change _ ≤ ∑ ρ ∈ S, quarterZeroIntegral656 (r ^ 2) ρ
  rw [he, Finset.sum_add_distrib]
  rw [sub_eq_add_neg]
  exact add_le_add (hphase _ hk) (by linarith only [hc, hd])

/-- Include the physical lower-end correction and pass the three-interval
phase estimate to the complete nontrivial-zero part of the principal Abel action. -/
theorem quarter_bridge_zero_abel_lower (hRH : RiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc 328 (663 / 2)) :
    (-0.003117 : ℝ) ≤
      quarterAbelAction656 (r ^ 2)
        (fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) := by
  have h := zero_abel_of_phase hRH hr.1 (fun _ hT ↦ quarter_bridge_phase_trunc hRH hr hT)
  linarith only [h]

/-- Under RH, the phase-independent bound and the lower-end correction give
a uniform lower bound for the complete nontrivial-zero Abel action. -/
theorem quarter_zero_abel_uniform_656 (hRH : RiemannHypothesis) {r : ℝ} (hr : 328 ≤ r) :
    (-0.025234 : ℝ) ≤
      quarterAbelAction656 (r ^ 2)
        (fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) := by
  have h := zero_abel_of_phase hRH hr (fun _ hT ↦ quarter_phase_uniform_lower_656 hRH hT _)
  linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
