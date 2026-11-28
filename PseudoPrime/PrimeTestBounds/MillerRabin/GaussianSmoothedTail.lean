/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalTail663
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSmoothedInterpolation
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevRelativeRH
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalLimit656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalTrivial656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalWeights656

/-! # Smoothed Abel formula for the common Gaussian principal tail -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For a physical cutoff at least one, the signed Chebyshev derivative
integral equals an integral of the smoothed error and two cutoff terms.
Subtract the two centered prefixes and compare with the first Abel formula. -/
theorem gaussian_smoothed_tail_eq {X : ℝ} (hX : 1 ≤ X) :
    let B := X * Real.exp (21 / 8)
    let W := quarterWeight656 X
    let P := fun t ↦ t * deriv W t
    let E := fun t ↦
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
        (t - Real.log (2 * Real.pi) * Real.log t)
    (-(∫ t in X..B, (Chebyshev.psi t - t) * deriv W t)) =
      (∫ t in X..B, E t * deriv P t) + P X * E X - Real.log (2 * Real.pi) * W X := by
  intro B W P E
  have hp := zero_lt_one.trans_le hX
  have hXB : X ≤ B := le_mul_of_one_le_right hp.le (Real.one_le_exp (by norm_num only))
  have hB := hX.trans hXB
  have hlog : Real.log (B / X) = 21 / 8 := by
    dsimp only [B]
    rw [mul_div_cancel_left₀ _ hp.ne', Real.log_exp]
  have hlogX : Real.log (X / X) ≤ 21 / 8 := by
    rw [div_self hp.ne', Real.log_one]
    norm_num only
  have hpre := quarter_centered_prefix_656 hp hX hlogX (Real.log (2 * Real.pi))
  have hfull := quarter_centered_prefix_656 hp hB hlog.le (Real.log (2 * Real.pi))
  obtain ⟨hw, hd⟩ := quarter_support_jet_656 hp
  dsimp only at hpre hfull
  dsimp only [B] at hfull
  simp only [hw, hd, mul_zero, zero_mul, sub_zero, add_zero] at hfull
  have ha := quarter_principal_abel_663 hp
  dsimp only at ha
  rw [quarter_principal_finite_656 hp] at ha
  have hdom : Set.Icc 1 B ⊆ Set.Ioi 0 := fun _ ht ↦ zero_lt_one.trans_le ht.1
  have hW := ((weight_smooth_656 hp).continuousOn.mono hdom)
  have hP := abel_deriv_continuous_656 hp (b := B)
  have hA :=
    AnalyticNumberTheory.Arithmetic.continuousOn_logWeightedMangoldtSum_scaled (x := 1) zero_lt_one
      B
  simp only [one_mul] at hA
  have hE : ContinuousOn E (Set.Icc 1 B) := by
    exact
      (hA.mono (Set.Icc_subset_Icc_left zero_le_one)).sub
        (continuous_id.continuousOn.sub
          (continuous_const.continuousOn.mul
            (Real.continuousOn_log.mono (fun _ ht ↦ (hdom ht).ne'))))
  have split {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 1 B)) :
    (∫ t in (1 : ℝ)..X, f t) + (∫ t in X..B, f t) = ∫ t in (1 : ℝ)..B, f t := by
    have hi : IntervalIntegrable f MeasureTheory.volume 1 B :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hB).mpr hf.integrableOn_Icc
    exact
      intervalIntegral.integral_add_adjacent_intervals
        (hi.mono_set
          (by
            rw [Set.uIcc_of_le hX, Set.uIcc_of_le hB]
            exact Set.Icc_subset_Icc_right hXB))
        (hi.mono_set
          (by
            rw [Set.uIcc_of_le hXB, Set.uIcc_of_le hB]
            exact Set.Icc_subset_Icc_left hX))
  have hsplitW := split hW
  have hsplitE := split (f := fun t ↦ E t * deriv P t) (hE.mul hP)
  dsimp only [B, W, P, E] at hsplitW hsplitE ⊢
  linarith only [hpre, hfull, ha, hsplitW, hsplitE]

/-- A bound on the centered smoothed error and its cutoff term supplies the
signed integral bound used by the Gaussian comparison. -/
theorem gaussian_signed_tail_le {X C : ℝ} (hX : 1 ≤ X)
    (h :
      let P := fun t ↦ t * deriv (quarterWeight656 X) t
      let E := fun t ↦
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
          (t - Real.log (2 * Real.pi) * Real.log t)
      4 *
          ((∫ t in X..X * Real.exp (21 / 8), E t * deriv P t) + P X * E X -
            Real.log (2 * Real.pi) * quarterWeight656 X X) ≤
        C) :
    (-4 : ℝ) *
        (∫ t in X..X * Real.exp (21 / 8), (Chebyshev.psi t - t) * deriv (quarterWeight656 X) t) ≤
      C := by
  have he := gaussian_smoothed_tail_eq hX
  dsimp only at he h
  linarith only [he, h]

/-- The nonnegative centered tail density has mass equal to the negative
of the lower endpoint value. The upper endpoint derivative vanishes. -/
private theorem tail_density_mass {X : ℝ} (hX : 0 < X) :
    let P := fun t ↦ t * deriv (quarterWeight656 X) t
    (∫ t in X..X * Real.exp (21 / 8), deriv P t) = -P X := by
  intro P
  let B := X * Real.exp (21 / 8)
  have hXB : X ≤ B := le_mul_of_one_le_right hX.le (Real.one_le_exp (by norm_num only))
  have hdom : Set.uIcc X B ⊆ Set.Ioi 0 := fun t ht ↦
    hX.trans_le ((Set.uIcc_of_le hXB ▸ ht : t ∈ Set.Icc X B).1)
  have hs : ContDiffOn ℝ 1 P (Set.Ioi 0) :=
    contDiffOn_id.mul ((weight_smooth_656 hX).deriv_of_isOpen (m := 1) isOpen_Ioi (by decide))
  have hi := (hs.continuousOn_deriv_of_isOpen isOpen_Ioi (by decide)).mono hdom
  have he :=
    intervalIntegral.integral_deriv_eq_sub (f := P)
      (fun t ht ↦
        (hs.differentiableOn (by decide) t (hdom ht)).differentiableAt
          (isOpen_Ioi.mem_nhds (hdom ht)))
      hi.intervalIntegrable
  have hz : P B = 0 := by
    dsimp only [P, B]
    rw [(quarter_support_jet_656 hX).2, mul_zero]
  simpa only [B, hz, zero_sub] using he

/-- A constant upper bound for increments of the smoothed error controls
the Gaussian tail through the mass of the nonnegative derivative density. -/
theorem gaussian_tail_of_increment {X C : ℝ} (hX : 1 ≤ X)
    (h :
      let E := fun t ↦
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
          (t - Real.log (2 * Real.pi) * Real.log t)
      ∀ t ∈ Set.Icc X (X * Real.exp (21 / 8)), E t - E X ≤ C) :
    (-4 : ℝ) *
        (∫ t in X..X * Real.exp (21 / 8), (Chebyshev.psi t - t) * deriv (quarterWeight656 X) t) ≤
      4 *
        (C * (-(X * deriv (quarterWeight656 X) X)) -
          Real.log (2 * Real.pi) * quarterWeight656 X X) := by
  let B := X * Real.exp (21 / 8)
  let P := fun t ↦ t * deriv (quarterWeight656 X) t
  let E := fun t ↦
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
      (t - Real.log (2 * Real.pi) * Real.log t)
  have hp := zero_lt_one.trans_le hX
  have hXB : X ≤ B := le_mul_of_one_le_right hp.le (Real.one_le_exp (by norm_num only))
  have hdom : Set.Icc X B ⊆ Set.Icc 1 B := Set.Icc_subset_Icc_left hX
  have hP := (abel_deriv_continuous_656 hp (b := B)).mono hdom
  have hA :=
    AnalyticNumberTheory.Arithmetic.continuousOn_logWeightedMangoldtSum_scaled (x := 1) zero_lt_one
      B
  simp only [one_mul] at hA
  have hE : ContinuousOn E (Set.Icc X B) := by
    exact
      (hA.mono (Set.Icc_subset_Icc_left hp.le)).sub
        (continuous_id.continuousOn.sub
          (continuous_const.continuousOn.mul
            (Real.continuousOn_log.mono (fun _ ht ↦ (hp.trans_le ht.1).ne'))))
  have hmono :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hXB (f := fun t ↦ E t * deriv P t)
      (g := fun t ↦ (C + E X) * deriv P t) ((hE.mul hP).intervalIntegrable_of_Icc hXB)
      (hP.const_mul _ |>.intervalIntegrable_of_Icc hXB)
      (fun t ht ↦
        mul_le_mul_of_nonneg_right
          (by
            have hi := h t ht; linarith only [hi])
          (outer_density_nonneg hp ht.1 ht.2))
  rw [intervalIntegral.integral_const_mul, tail_density_mass hp] at hmono
  apply gaussian_signed_tail_le hX
  dsimp only [B, P, E] at hmono ⊢
  linarith only [hmono]

private theorem cutoff_log_deriv {X : ℝ} (hX : 0 < X) :
    -(X * deriv (quarterWeight656 X) X) = (137 / 105 : ℝ) * quarterWeight656 X X := by
  rw [log_deriv hX hX]
  dsimp only [shiftedCoord, weightFactor, quarterWeight656]
  rw [div_self hX.ne', Real.log_one, sub_zero]
  ring

/-- Above radius 331.5, a smoothed-error increment bound of 37 suffices for
the signed integral allowance of the first compressed K137 cell. -/
theorem gaussian_first_tail_of_increment {y : ℝ} (hy : 663 / 2 ≤ y)
    (h :
      let X := y ^ 2
      let E := fun t ↦
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
          (t - Real.log (2 * Real.pi) * Real.log t)
      ∀ t ∈ Set.Icc X (X * Real.exp (21 / 8)), E t - E X ≤ 37) :
    (-4 : ℝ) *
        (∫ t in y ^ 2..y ^ 2 * Real.exp (21 / 8),
          (Chebyshev.psi t - t) * deriv (quarterWeight656 (y ^ 2)) t) ≤
      0.053 := by
  have hp : 0 < y := by linarith only [hy]
  have hx : 1 ≤ y ^ 2 := one_le_pow₀ (by linarith only [hy] : 1 ≤ y)
  have htail := gaussian_tail_of_increment hx h
  rw [cutoff_log_deriv (sq_pos_of_pos hp)] at htail
  have hw : quarterWeight656 (y ^ 2) (y ^ 2) ∈ Set.Icc 0 ((9319732 / 100000000) / (663 / 2)) := by
    rw [quarter_cutoff_weight_656 (sq_pos_of_pos hp), Real.sqrt_sq hp.le]
    exact
      ⟨div_nonneg (by linarith only [quarter_unit_weight_656.1]) hp.le,
        (div_le_div_of_nonneg_right quarter_unit_weight_656.2.le hp.le).trans
          (div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 9319732 / 100000000)
            (by norm_num only : (0 : ℝ) < 663 / 2) hy)⟩
  have hl :=
    mul_le_mul_of_nonneg_right
      (show (1.837 : ℝ) ≤ Real.log (2 * Real.pi) by linarith only [Analysis.log_two_mul_pi_gt]) hw.1
  linarith only [htail, hl, hw.2]

/-- A covering by endpoint certificates supplies the first K137 integral
bound. Each cell can use its own pair of endpoints and error allowance. -/
theorem gaussian_first_tail_of_cells {y D : ℝ} (hy : 663 / 2 ≤ y)
    (hD : D ≤ gaussianLogError (Real.log (y ^ 2)))
    (hcover :
      ∀ t ∈ Set.Icc (y ^ 2) (y ^ 2 * Real.exp (21 / 8)),
        ∃ a b C : ℝ,
          0 < a ∧
            t ∈ Set.Icc a b ∧
            gaussianLogError (Real.log a) ≤ C ∧
            gaussianLogError (Real.log b) ≤ C ∧ C + b * ((b - a) / a) ^ 2 / 8 ≤ D + 37) :
    (-4 : ℝ) *
        (∫ t in y ^ 2..y ^ 2 * Real.exp (21 / 8),
          (Chebyshev.psi t - t) * deriv (quarterWeight656 (y ^ 2)) t) ≤
      0.053 := by
  apply gaussian_first_tail_of_increment hy
  dsimp only
  intro t ht
  obtain ⟨a, b, C, ha, hmem, hl, hr, hC⟩ := hcover t ht
  have hupper := (gaussian_error_log_cell ha hmem hl hr).trans hC
  have hy₀ : 0 < y := by linarith only [hy]
  unfold gaussianLogError at hupper hD
  rw [Real.exp_log (ha.trans_le hmem.1)] at hupper
  rw [Real.exp_log (sq_pos_of_pos hy₀)] at hD
  linarith only [hupper, hD]

private theorem tail_sqrt_moment_eq {X : ℝ} (hX : 0 < X) :
    let B := X * Real.exp (21 / 8)
    let W := quarterWeight656 X
    let P := fun t ↦ t * deriv W t
    (∫ t in X..B, Real.sqrt t * deriv P t) =
      Real.sqrt X * (-P X + W X / 2) + (∫ t in X..B, W t / Real.sqrt t) / 4 := by
  intro B W P
  have hXB : X ≤ B := le_mul_of_one_le_right hX.le (Real.one_le_exp (by norm_num only))
  have hdom : Set.uIcc X B ⊆ Set.Ioi 0 := fun t ht ↦
    hX.trans_le ((Set.uIcc_of_le hXB ▸ ht : t ∈ Set.Icc X B).1)
  have hW : ContDiffOn ℝ 2 W (Set.Ioi 0) := weight_smooth_656 hX
  have hP : ContDiffOn ℝ 1 P (Set.Ioi 0) :=
    contDiffOn_id.mul (hW.deriv_of_isOpen (m := 1) isOpen_Ioi (by decide))
  have hD : ContinuousOn (fun t : ℝ ↦ 1 / (2 * Real.sqrt t)) (Set.uIcc X B) :=
    continuous_const.continuousOn.div
      (continuous_const.continuousOn.mul Real.continuous_sqrt.continuousOn)
      (fun t ht ↦ mul_ne_zero (by norm_num only) (Real.sqrt_pos.mpr (hdom ht)).ne')
  have hS (t : ℝ) (ht : t ∈ Set.uIcc X B) := Real.hasDerivAt_sqrt (hdom ht).ne'
  have h₁ :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul hS
      (fun t ht ↦
        ((hP.differentiableOn (by decide) t (hdom ht)).differentiableAt
            (isOpen_Ioi.mem_nhds (hdom ht))).hasDerivAt)
      hD.intervalIntegrable
      ((hP.continuousOn_deriv_of_isOpen isOpen_Ioi (by decide)).mono hdom).intervalIntegrable
  have h₂ :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun t ht ↦ (hS t ht).div_const (2 : ℝ))
      (fun t ht ↦
        ((hW.differentiableOn (by decide) t (hdom ht)).differentiableAt
            (isOpen_Ioi.mem_nhds (hdom ht))).hasDerivAt)
      (hD.div_const 2).intervalIntegrable
      ((hW.continuousOn_deriv_of_isOpen isOpen_Ioi (by decide)).mono hdom).intervalIntegrable
  have he :
    (∫ t in X..B, (1 / (2 * Real.sqrt t)) * P t) = ∫ t in X..B, (Real.sqrt t / 2) * deriv W t := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only [P]
    field_simp [(Real.sqrt_pos.mpr (hdom ht)).ne']
    rw [Real.sq_sqrt (hdom ht).le]
  have hf :
    (∫ t in X..B, (1 / (2 * Real.sqrt t) / 2) * W t) = (∫ t in X..B, W t / Real.sqrt t) / 4 := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hz := quarter_support_jet_656 hX
  have hWB : W B = 0 := hz.1
  have hPB : P B = 0 := by
    dsimp only [P, W]; rw [hz.2, mul_zero]
  rw [hPB, mul_zero, he, h₂, hWB, mul_zero, hf] at h₁
  linarith only [h₁]

/-- The common Gaussian tail density, integrated against the square-root
envelope under RH, has mass at most 0.191. -/
theorem gaussian_tail_sqrt_moment_le {y : ℝ} (hy : 0 < y) :
    let X := y ^ 2
    (∫ t in X..X * Real.exp (21 / 8),
        Real.sqrt t * deriv (fun u ↦ u * deriv (quarterWeight656 X) u) t) ≤
      0.191 := by
  intro X
  let B := X * Real.exp (21 / 8)
  let W := quarterWeight656 X
  have hx : 0 < X := sq_pos_of_pos hy
  have hb : X ≤ B := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only))
  have hdom : Set.Icc X B ⊆ Set.Ioi 0 := fun _ ht ↦ hx.trans_le ht.1
  have hW := (weight_smooth_656 hx).continuousOn.mono hdom
  have hlow : ∀ t ∈ Set.Icc X B, y ≤ Real.sqrt t := by
    intro t ht
    exact (Real.sqrt_sq hy.le).symm.le.trans (Real.sqrt_le_sqrt ht.1)
  have hmono :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hb (f := fun t ↦
      W t / Real.sqrt t) (g := fun t ↦ W t / y)
      ((hW.div Real.continuous_sqrt.continuousOn
            (fun t ht ↦ (hy.trans_le (hlow t ht)).ne')).intervalIntegrable_of_Icc
        hb)
      ((hW.div_const y).intervalIntegrable_of_Icc hb)
      (fun t ht ↦ by
        have hlog : Real.log (t / X) ≤ 21 / 8 :=
          (Real.log_le_iff_le_exp (div_pos (hdom ht) hx)).mpr
            ((div_le_iff₀ hx).mpr (ht.2.trans_eq (mul_comm _ _)))
        have hv := sub_nonneg.mpr hlog
        have hn : 0 ≤ W t := by
          dsimp only [W, quarterWeight656]; positivity
        exact div_le_div_of_nonneg_left hn hy (hlow t ht))
  have hs := quarter_scale_integral_656 hx hx hb le_rfl
  rw [div_self hx.ne', mul_div_cancel_left₀ _ hx.ne'] at hs
  change (∫ t in X..B, W t) = Real.sqrt X * quarterTailMass663 at hs
  have hroot : Real.sqrt X = y := Real.sqrt_sq hy.le
  rw [hroot] at hs
  rw [intervalIntegral.integral_div, hs, mul_comm y, mul_div_cancel_right₀ _ hy.ne'] at hmono
  have h := tail_sqrt_moment_eq hx
  dsimp only at h
  rw [cutoff_log_deriv hx, quarter_cutoff_weight_656 hx, hroot] at h
  have hfactor :
    y *
        ((137 / 105 : ℝ) * ((quarterKernel656.transform 1).re / y) +
          (quarterKernel656.transform 1).re / y / 2) =
      (137 / 105 + 1 / 2 : ℝ) * (quarterKernel656.transform 1).re := by
    field_simp [hy.ne']
  rw [hfactor] at h
  linarith only [h, hmono, quarter_tail_mass_upper_663, quarter_unit_weight_656.2]

/-- A lower bound `-C` for the smoothed error at the cutoff gives a signed
integral allowance with explicit dependence on the radius and `C`. -/
theorem gaussian_k137_tail_of_cutoff (hRH : RiemannHypothesis) {y C : ℝ} (hy : 1 < y) (hC : 0 ≤ C)
    (hcut : -C ≤ gaussianLogError (Real.log (y ^ 2))) :
    (-4 : ℝ) *
        (∫ t in y ^ 2..y ^ 2 * Real.exp (21 / 8),
          (Chebyshev.psi t - t) * deriv (quarterWeight656 (y ^ 2)) t) ≤
      191 / 5000 + 4 * (21 / 20 + C) * ((137 / 105) * ((9319732 / 100000000) / y)) := by
  let X := y ^ 2
  let B := X * Real.exp (21 / 8)
  let W := quarterWeight656 X
  let P := fun t ↦ t * deriv W t
  let E := fun t ↦
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
      (t - Real.log (2 * Real.pi) * Real.log t)
  have hy₀ : 0 < y := zero_lt_one.trans hy
  have hx : 1 < X := one_lt_pow₀ hy (by decide)
  have hp : 0 < X := zero_lt_one.trans hx
  have hb : X ≤ B := le_mul_of_one_le_right hp.le (Real.one_le_exp (by norm_num only))
  have hP := (abel_deriv_continuous_656 hp (b := B)).mono (Set.Icc_subset_Icc_left hx.le)
  have hA :=
    AnalyticNumberTheory.Arithmetic.continuousOn_logWeightedMangoldtSum_scaled (x := 1) zero_lt_one
      B
  simp only [one_mul] at hA
  have hE : ContinuousOn E (Set.Icc X B) :=
    (hA.mono (Set.Icc_subset_Icc_left hp.le)).sub
      (continuous_id.continuousOn.sub
        (continuous_const.continuousOn.mul
          (Real.continuousOn_log.mono (fun _ ht ↦ (hp.trans_le ht.1).ne'))))
  have hS : ContinuousOn (fun t ↦ Real.sqrt t * deriv P t) (Set.Icc X B) :=
    Real.continuous_sqrt.continuousOn.mul hP
  have hI :
    (∫ t in X..B, E t * deriv P t) ≤
      (∫ t in X..B, Real.sqrt t * deriv P t) / 20 + (21 / 20 : ℝ) * (-(X * deriv W X)) := by
    have hm :=
      intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hb (f := fun t ↦
        E t * deriv P t) (g := fun t ↦ (Real.sqrt t / 20 + 21 / 20) * deriv P t)
        ((hE.mul hP).intervalIntegrable_of_Icc hb)
        ((((Real.continuous_sqrt.continuousOn.div_const 20).add continuous_const.continuousOn).mul
              hP).intervalIntegrable_of_Icc
          hb)
        (fun t ht ↦
          mul_le_mul_of_nonneg_right
            (by
              have he :=
                AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum_log_shift_error_le hRH
                  (hx.trans_le ht.1)
              dsimp only [E]
              linarith only [(abs_le.mp he).2])
            (outer_density_nonneg hp ht.1 ht.2))
    simp_rw [add_mul, div_mul_eq_mul_div] at hm
    rw [intervalIntegral.integral_add (hS.div_const 20 |>.intervalIntegrable_of_Icc hb)
        ((hP.const_mul 21).div_const 20 |>.intervalIntegrable_of_Icc hb),
      intervalIntegral.integral_div, intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul, tail_density_mass hp] at hm
    dsimp only [P] at hm ⊢
    linarith only [hm]
  have hw : 0 ≤ W X := by
    dsimp only [W]
    rw [quarter_cutoff_weight_656 hp]
    exact div_nonneg (by linarith only [quarter_unit_weight_656.1]) (Real.sqrt_nonneg X)
  have hs : -(X * deriv W X) ≤ (137 / 105 : ℝ) * ((9319732 / 100000000) / y) := by
    dsimp only [W]
    rw [cutoff_log_deriv hp, quarter_cutoff_weight_656 hp,
      show Real.sqrt X = y from Real.sqrt_sq hy₀.le]
    exact
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right quarter_unit_weight_656.2.le hy₀.le)
        (by norm_num only)
  have hneg := quarter_tail_weight_deriv_nonpos_663 hp ⟨le_rfl, hb⟩
  unfold gaussianLogError at hcut
  rw [Real.exp_log hp] at hcut
  have hcut' : -C ≤ E X := by
    dsimp only [E]; linarith only [hcut]
  have hj := mul_le_mul_of_nonpos_left hcut' (mul_nonpos_of_nonneg_of_nonpos hp.le hneg)
  have hlog :=
    mul_nonneg (Real.log_nonneg (show 1 ≤ 2 * Real.pi by linarith only [Real.pi_gt_three])) hw
  apply gaussian_signed_tail_le hx.le
  have hm : (∫ t in X..B, Real.sqrt t * deriv P t) ≤ 0.191 := gaussian_tail_sqrt_moment_le hy₀
  dsimp only [B, P, W, E] at hI hs hj hlog hm ⊢
  have hsC := mul_le_mul_of_nonneg_left hs (show 0 ≤ 4 * (21 / 20 + C) by linarith only [hC])
  nlinarith only [hI, hsC, hj, hlog, hm]

/-- Under RH, a smoothed-error lower bound of minus nine at the tested cutoff
alone suffices for the first Gaussian cell's integral allowance. -/
theorem gaussian_first_tail_of_cutoff (hRH : RiemannHypothesis) {y : ℝ} (hy : 663 / 2 ≤ y)
    (hcut : -9 ≤ gaussianLogError (Real.log (y ^ 2))) :
    (-4 : ℝ) *
        (∫ t in y ^ 2..y ^ 2 * Real.exp (21 / 8),
          (Chebyshev.psi t - t) * deriv (quarterWeight656 (y ^ 2)) t) ≤
      0.053 := by
  have h :=
    gaussian_k137_tail_of_cutoff hRH (by linarith only [hy] : 1 < y)
      (by norm_num only : (0 : ℝ) ≤ 9) hcut
  have hdiv :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 9319732 / 100000000)
      (by norm_num only : (0 : ℝ) < 663 / 2) hy
  linarith only [h, hdiv]

end PseudoPrime.PrimeTestBounds.MillerRabin
