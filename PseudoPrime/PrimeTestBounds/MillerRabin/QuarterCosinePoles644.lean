/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosine644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosine644
import PseudoPrime.LLS.PaperStatements.MellinKernelPoleIntegrals

/-! # Pole terms for the section 122 cosine contours -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The normalized integral on the vertical line at `c` for the Mellin kernel
`K`, scale `x` and simple pole at `p`. It is used to extract the xi poles. -/
noncomputable def quarterCosinePole (K : LLS.PaperStatements.MellinKernel) (c p x : ℝ) : ℂ :=
  let s := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ, (1 / (s t - (p : ℂ))) * (K.function (s t) * (x : ℂ) ^ s t)

/-- For a kernel holomorphic between the comparison lines and scale at least
one, the difference of normalized vertical integrals is the residue at the
interior pole. The horizontal integrals vanish by the Mellin kernel decay. -/
theorem quarter_cosine_pole_diff (K : LLS.PaperStatements.MellinKernel) (hd : K.delta = 1 / 8)
    (hK : ∀ z : ℂ, -9 / 16 ≤ z.re → z.re ≤ 9 / 16 → AnalyticAt ℂ K.function z) {x p : ℝ}
    (hx : 1 ≤ x) (hlP : -9 / 16 < p) (huP : p < 9 / 16) :
    quarterCosinePole K (9 / 16) p x - quarterCosinePole K (-9 / 16) p x =
      K.function (p : ℂ) * (x : ℂ) ^ (p : ℂ) := by
  let a : ℝ := -9 / 16
  let b : ℝ := 9 / 16
  let F := fun s : ℂ ↦ (1 / (s - (p : ℂ))) * K.function s * (x : ℂ) ^ s
  let T := fun n : ℕ ↦ (n : ℝ) + 1
  have hl : -1 / 2 - K.delta < a := by
    rw [hd]; norm_num only [a]
  have hu : b ≤ 1 / 2 + K.delta := by
    rw [hd]; norm_num only [b]
  have ha : a ≤ b := by norm_num only [a, b]
  have hxp := zero_lt_one.trans_le hx
  have hi0 :=
    LLS.PaperStatements.MellinKernel.integrable_pole_power_line K (hl.trans_le ha) hu
      (by norm_num only [b]) (ne_of_gt huP) hxp
  have hia :=
    LLS.PaperStatements.MellinKernel.integrable_pole_power_line K hl (ha.trans hu)
      (by norm_num only [a, b]) (ne_of_lt hlP) hxp
  have ht := LLS.PaperStatements.MellinKernel.tendsto_pole_horizontalIntegral K ha hl hu hx p
  have hlim :=
    AnalyticNumberTheory.RectangleGeometry.tendsto_boundaryIntegral (K := F) (a := a) (b := b) T
      (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      (by
        simpa only [F, T, neg_one_mul, Complex.ofReal_neg, neg_mul, sub_eq_add_neg, one_mul] using
          ht (-1) (Or.inr rfl))
      (by simpa only [F, T, one_mul] using ht 1 (Or.inl rfl))
      (by simpa only [F, mul_comm Complex.I, mul_assoc] using hia)
      (by simpa only [F, mul_comm Complex.I, mul_assoc] using hi0)
  let H := fun z : ℂ ↦ K.function z * (x : ℂ) ^ z
  have hH (z : ℂ) (hr : a ≤ z.re) (hs : z.re ≤ b) : AnalyticAt ℂ H z :=
    (hK z hr hs).mul (by fun_prop (disch := exact Complex.ofReal_mem_slitPlane.mpr hxp))
  have hz (n : ℕ) :
    AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral F ((a : ℂ) - T n * Complex.I)
        ((b : ℂ) + T n * Complex.I) =
      2 * Real.pi * Complex.I * H (p : ℂ) := by
    have htpos : 0 < T n := by
      dsimp only [T]; linarith only [Nat.cast_nonneg (α := ℝ) n]
    have ho :
      (p : ℂ) ∈
        AnalyticNumberTheory.RectangleGeometry.rectangleOpenBox ((a : ℂ) - T n * Complex.I)
          ((b : ℂ) + T n * Complex.I) := by
      change ((_ < _ ∧ _ < _) ∧ (_ < _ ∧ _ < _))
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, add_zero, Complex.sub_im,
        Complex.add_im, Complex.mul_im, mul_one, zero_add, zero_sub, min_eq_left ha,
        max_eq_right ha, min_eq_left (neg_le_self htpos.le), max_eq_right (neg_le_self htpos.le)]
      exact ⟨⟨hlP, huP⟩, neg_lt_zero.mpr htpos, htpos⟩
    apply
      AnalyticNumberTheory.RectangleGeometry.boundaryIntegral_simple_pole
        (by
          simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
            Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero]
          norm_num only [a, b])
        (by
          simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
            Complex.I_im, Complex.I_re, Complex.ofReal_re, mul_one, mul_zero, add_zero, zero_add,
            zero_sub] using neg_lt_self htpos)
        ho
    · intro z hbox hne
      have hr := hbox.1
      change z.re ∈ Set.uIcc _ _ at hr
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, Set.uIcc_of_le ha,
        Set.mem_Icc] at hr
      simp only [F, mul_assoc]
      exact
        ((differentiableAt_const (1 : ℂ)).div (differentiableAt_id.sub_const (p : ℂ))
              (sub_ne_zero.mpr hne)).mul
          (hH z hr.1 hr.2).differentiableAt
    · exact hH _ hlP.le huP.le
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have hn : z ≠ (p : ℂ) := hz
      dsimp only [F, H]
      rw [← mul_assoc, ← mul_assoc, one_div, mul_inv_cancel₀ (sub_ne_zero.mpr hn), one_mul]
  have h := tendsto_nhds_unique hlim (tendsto_const_nhds.congr (fun n ↦ (hz n).symm))
  rw [mul_comm (2 * (Real.pi : ℂ)) Complex.I, mul_assoc] at h
  have he := mul_left_cancel₀ Complex.I_ne_zero h
  let d : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hi : d * (2 * (Real.pi : ℂ)) = 1 := by
    dsimp only [d]
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat, one_div,
      inv_mul_cancel₀ (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))]
  have hh := congrArg (fun u ↦ d * u) he
  rw [mul_sub, ← mul_assoc, hi, one_mul] at hh
  simpa only [quarterCosinePole, F, H, a, b, d, mul_comm Complex.I, mul_assoc] using hh

/-- The cosine kernel has no poles in the comparison strip, so moving a
simple xi pole between the vertical lines adds its weighted residue. -/
theorem quarter_cosine_residue_644 {x p : ℝ} (hx : 1 ≤ x) (hlP : -9 / 16 < p) (huP : p < 9 / 16) :
    quarterCosinePole quarterSymmetricMellin644 (9 / 16) p x -
        quarterCosinePole quarterSymmetricMellin644 (-9 / 16) p x =
      quarterSymmetricKernel644 (p : ℂ) * (x : ℂ) ^ (p : ℂ) := by
  refine quarter_cosine_pole_diff quarterSymmetricMellin644 rfl ?_ hx hlP huP
  let U := Complex.re ⁻¹' Set.Ioo (-(3 / 4 : ℝ)) (3 / 4)
  have hU : IsOpen U := isOpen_Ioo.preimage Complex.continuous_re
  have hD : DifferentiableOn ℂ quarterSymmetricKernel644 U := fun z hz ↦
    (symmetric_diff hz.1.le hz.2.le).differentiableWithinAt
  exact fun z hl hu ↦ (hD.analyticOnNhd hU) z ⟨by linarith only [hl], by linarith only [hu]⟩

/-- At scale at least one, shifting both xi poles from the right comparison
line to the left contributes the sum of their two weighted residues. -/
theorem quarter_cosine_xi_poles_644 {x : ℝ} (hx : 1 ≤ x) :
    let P := quarterCosinePole quarterSymmetricMellin644
    P (9 / 16) (1 / 2) x + P (9 / 16) (-1 / 2) x -
        (P (-9 / 16) (1 / 2) x + P (-9 / 16) (-1 / 2) x) =
      quarterSymmetricKernel644 ((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ) +
        quarterSymmetricKernel644 ((-1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((-1 / 2 : ℝ) : ℂ) := by
  dsimp only
  rw [add_sub_add_comm, quarter_cosine_residue_644 hx (by norm_num only) (by norm_num only),
    quarter_cosine_residue_644 hx (by norm_num only) (by norm_num only)]

end PseudoPrime.PrimeTestBounds.MillerRabin
