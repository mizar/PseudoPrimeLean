/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalPoleInversion
public import PseudoPrime.LLS.ReciprocalGapKernel

/-! # Admissible fourth- and sixth-order rational-pole Mellin kernels -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The exponential modulation has constant norm exp(2c sigma) on a vertical line.
Take the real part of its exponent explicitly. This supplies bounded modulation
when proving absolute integrability of the rational-pole function. -/
private theorem norm_exp_rationalPole_line (c σ t : ℝ) :
    ‖Complex.exp (2 * (c : ℂ) * ((σ : ℂ) + Complex.I * t))‖ =
    Real.exp (2 * c * σ) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.add_re, Complex.I_re, zero_mul,
    Complex.I_im, add_zero, Complex.mul_im]

/-- For n>=1 and sigma+rho>0, the shifted reciprocal power is vertically integrable.
Scale the factorial-normalized power theorem and commute the imaginary factors.
This is the integrable base for the modulated rational-pole kernel. -/
private theorem integrable_shifted_reciprocal_power {n : ℕ} (hn : 1 ≤ n) {ρ σ : ℝ}
    (hσ : 0 < σ + ρ) :
    MeasureTheory.Integrable (fun t : ℝ ↦
      1 / (((σ : ℂ) + Complex.I * t) + ρ) ^ (n + 1)) := by
  have hi := (Analysis.integrable_factorial_div_pow hn hσ).const_mul
    ((n.factorial : ℂ)⁻¹)
  apply hi.congr
  exact Filter.Eventually.of_forall fun t ↦ by
    have hz : ((σ + ρ : ℝ) : ℂ) + (t : ℂ) * Complex.I = (σ : ℂ) + Complex.I * t + ρ := by
      rw [Complex.ofReal_add]
      ring
    dsimp only
    rw [hz, div_eq_mul_inv, ← mul_assoc,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), one_mul, one_div]

/-- At u=exp(2c-2a), the profile is strictly positive for a>0 and every m.
The normalized logarithmic coordinate is one and the support condition holds.
This gives the nonzero-transform field of the admissible kernel. -/
theorem rationalPoleProfile_pos (m : ℕ) {a : ℝ} (ha : 0 < a) (c : ℝ) :
    0 < Analysis.rationalPoleProfile m a c (Real.exp (2 * c - 2 * a)) := by
  have hp := Real.exp_pos (2 * c - 2 * a)
  have hl : Real.log (Real.exp (2 * c - 2 * a)) ≤ 2 * c := by
    rw [Real.log_exp]
    linarith only [ha]
  have hv : (2 * c - (2 * c - 2 * a)) / (2 * a) = 1 := by
    apply (div_eq_one_iff_eq (mul_pos (by norm_num only) ha).ne').mpr
    ring
  rw [Analysis.rationalPoleProfile, ite_eq_left ⟨hp, hl⟩, Real.log_exp, hv, one_pow, one_mul]
  exact div_pos (Real.exp_pos _) (Nat.cast_pos.mpr (Nat.factorial_pos _))

/-- For m>=1,a>0 on any line right of -1/(2a), the rational-pole function is
vertically integrable. Factor it into a constant, a reciprocal power and bounded
exponential modulation. Later multiplication by the Mellin power preserves integrability. -/
theorem integrable_rationalPole_line {m : ℕ} (hm : 1 ≤ m) {a σ : ℝ} (ha : 0 < a)
    (hσ : 0 < σ + (2 * a)⁻¹) (c : ℝ) :
    MeasureTheory.Integrable (fun t : ℝ ↦
      Analysis.rationalPoleFunction m a c ((σ : ℂ) + Complex.I * t)) := by
  have hm2 : 2 ≤ 2 * m := by nlinarith only [hm]
  have hn : 1 ≤ 2 * m - 1 := Nat.le_sub_of_add_le hm2
  have hk : 2 * m - 1 + 1 = 2 * m := Nat.sub_add_cancel
    ((by norm_num only : 1 ≤ 2).trans hm2)
  have hc : Continuous (fun t : ℝ ↦ Complex.exp (2 * (c : ℂ) * ((σ : ℂ) + Complex.I * t))) :=
    Complex.continuous_exp.comp (continuous_const.mul
      (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)))
  have hi := (integrable_shifted_reciprocal_power hn hσ).mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t ↦ (norm_exp_rationalPole_line c σ t).le)
  apply (hi.const_mul (((2 * a : ℝ) : ℂ) / ((2 * a : ℝ) : ℂ) ^ (2 * m))).congr
  exact Filter.Eventually.of_forall fun t ↦ by
    dsimp only
    rw [Analysis.rationalPole_eq_shifted_power m ha c, hk, one_div_mul_eq_div]

/-- For 0<a<1, the rational pole lies strictly left of -1/2. Compare reciprocal
positive scales to show the gap 1/(2a)-1/2 is positive. This gap selects the
previously certified reciprocal-kernel strip. -/
private theorem rationalPole_gap_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    0 < (2 * a)⁻¹ - 1 / 2 := by
  have h := (inv_lt_inv₀ (by norm_num only : (0 : ℝ) < 2)
    (mul_pos (by norm_num only) ha)).mpr (by linarith only [ha1] : 2 * a < 2)
  norm_num only at h
  exact sub_pos.mpr h

/-- For A,d>0, d<=B and A<=3B, reciprocal B^(n+2) is bounded by
3(1/d)^n/(AB). Compare reciprocal powers, multiply by nonnegative powers of B
and retain the pair denominator. This transfers the existing two-pole decay estimate. -/
private theorem reciprocal_power_le_pair {A B d : ℝ} (ha : 0 < A) (hd : 0 < d)
    (hb : d ≤ B)
    (hab : A ≤ 3 * B) (n : ℕ) :
    1 / B ^ (n + 2) ≤ 3 * (1 / d) ^ n * (1 / (A * B)) := by
  have hB := hd.trans_le hb
  have hi := pow_le_pow_left₀ (div_nonneg zero_le_one hB.le)
    (div_le_div_of_nonneg_left zero_le_one hd hb) n
  have hp := mul_le_mul_of_nonneg_right hi (pow_nonneg hB.le n)
  rw [← mul_pow, one_div_mul_cancel hB.ne', one_pow] at hp
  have ht := mul_le_mul_of_nonneg_left hp (show 0 ≤ 3 * B ^ 2 by nlinarith only [sq_nonneg B])
  have hAB := mul_le_mul_of_nonneg_right hab hB.le
  rw [mul_one_div, div_le_div_iff₀ (pow_pos hB _) (mul_pos ha hB), pow_add, pow_two]
  nlinarith only [ht, hAB]

/-- For 0<a<1, the rational-pole function is complex differentiable throughout
the certified gap strip. Its shifted denominator is nonzero there. The rational
normalization and elementary exponential differentiation establish holomorphy. -/
private theorem differentiableAt_rationalPole (m : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (c : ℝ) {z : ℂ}
    (hz : z ∈ reciprocalGapRegion ((2 * a)⁻¹ - 1 / 2)) :
    DifferentiableAt ℂ (Analysis.rationalPoleFunction m a c) z := by
  have hh := rationalPole_gap_pos ha ha1
  have hd := reciprocalGap_second_shift_ne_zero hh hz
  have he : (1 / 2 : ℝ) + ((2 * a)⁻¹ - 1 / 2) = (2 * a)⁻¹ := by ring
  rw [he] at hd
  have hf : Analysis.rationalPoleFunction m a c = fun z : ℂ ↦
      (((2 * a : ℝ) : ℂ) / ((2 * a : ℝ) : ℂ) ^ (2 * m)) *
        (Complex.exp (2 * (c : ℂ) * z) / (z + ((2 * a : ℝ)⁻¹ : ℝ)) ^ (2 * m)) :=
    funext (Analysis.rationalPole_eq_shifted_power m ha c)
  rw [hf]
  apply (differentiableAt_const _).mul
  exact (Complex.differentiable_exp.differentiableAt.comp z
    ((differentiableAt_id (𝕜 := ℂ) (x := z)).const_mul (2 * (c : ℂ)))).div
      (((differentiableAt_id (𝕜 := ℂ) (x := z)).add_const _).pow (2 * m))
      (pow_ne_zero (2 * m) hd)

/-- The modulation exp(2cz) has norm exp(2c Re z) for real c. Evaluate the real
part directly. The identity is used for a uniform strip estimate independent of height. -/
private theorem norm_exp_rationalPole (c : ℝ) (z : ℂ) :
    ‖Complex.exp (2 * (c : ℂ) * z)‖ = Real.exp (2 * c * z.re) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.mul_im, zero_mul, add_zero]

/-- If |Re z|<=3/4, modulation has norm at most exp(3|c|/2). Bound the product
by its absolute value before applying monotonicity of exp. This keeps the decay
constant uniform on the entire certified strip. -/
private theorem norm_exp_rationalPole_strip (c : ℝ) {z : ℂ} (hz : |z.re| ≤ 3 / 4) :
    ‖Complex.exp (2 * (c : ℂ) * z)‖ ≤ Real.exp ((3 / 2 : ℝ) * |c|) := by
  rw [norm_exp_rationalPole]
  apply Real.exp_le_exp.mpr
  have hp := le_abs_self (c * z.re)
  rw [abs_mul] at hp
  have hm := mul_le_mul_of_nonneg_left hz (abs_nonneg c)
  nlinarith only [hp, hm]

/-- In the positive-gap strip, the first shifted norm is at most three times
the second. The triangle inequality adds the gap, and the second norm is at least
h/2. This permits comparison to the existing reciprocal two-pole kernel. -/
private theorem first_norm_le_three_second {h : ℝ} (hh : 0 < h) {z : ℂ}
    (hz : z ∈ reciprocalGapRegion h) :
    ‖z + (1 / 2 : ℂ)‖ ≤ 3 * ‖z + ((1 / 2 + h : ℝ) : ℂ)‖ := by
  have he : z + (1 / 2 : ℂ) = (z + ((1 / 2 + h : ℝ) : ℂ)) - (h : ℂ) := by
    rw [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  have ht := norm_sub_le (z + ((1 / 2 + h : ℝ) : ℂ)) (h : ℂ)
  rw [← he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh] at ht
  linarith only [ht, reciprocalGap_second_norm_lower hz]

/-- A positive multiplier controlling rational-pole norms by the reciprocal-gap
kernel in its strip. Inputs are the order, real pole scale and modulation shift.
It absorbs bounded modulation and extra reciprocal powers for the decay proof. -/
private noncomputable def poleNormFactor (m : ℕ) (a c : ℝ) : ℝ :=
  ‖((2 * a : ℝ) : ℂ) / ((2 * a : ℝ) : ℂ) ^ (2 * m)‖ *
    Real.exp ((3 / 2 : ℝ) * |c|) * 3 * (1 / (((2 * a)⁻¹ - 1 / 2) / 2)) ^ (2 * m - 2)

/-- For m>=1,0<a<1 in the gap strip away from -1/2, the rational-pole norm
is bounded by poleNormFactor times the existing reciprocal-gap norm. Combine
the reciprocal-power comparison with uniform modulation. This reuses the old decay API. -/
private theorem norm_rationalPole_le_pair {m : ℕ} (hm : 1 ≤ m) {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (c : ℝ) {z : ℂ} (hz : z ∈ reciprocalGapRegion ((2 * a)⁻¹ - 1 / 2))
    (hne : z ≠ -1 / 2) :
    ‖Analysis.rationalPoleFunction m a c z‖ ≤
      poleNormFactor m a c * ‖Analysis.reciprocalGapFunction ((2 * a)⁻¹ - 1 / 2) z‖ := by
  let h := (2 * a)⁻¹ - 1 / 2
  have hh : 0 < h := rationalPole_gap_pos ha ha1
  have he : (1 / 2 : ℝ) + h = (2 * a)⁻¹ := by dsimp only [h]; ring
  have hA : 0 < ‖z + (1 / 2 : ℂ)‖ := norm_pos_iff.mpr (reciprocal_shift_ne_zero hne)
  have hB : 0 < ‖z + ((1 / 2 + h : ℝ) : ℂ)‖ :=
    (by linarith only [hh] : 0 < h / 2).trans_le (reciprocalGap_second_norm_lower hz)
  have hpower := reciprocal_power_le_pair hA (by linarith only [hh] : 0 < h / 2)
    (reciprocalGap_second_norm_lower hz) (first_norm_le_three_second hh hz) (2 * m - 2)
  have hk : 2 * m - 2 + 2 = 2 * m := Nat.sub_add_cancel (by nlinarith only [hm])
  rw [hk] at hpower
  have hre : |z.re| ≤ 3 / 4 := abs_le.mpr ⟨by
    have hlow := hz.1
    have hm := min_le_right (h / 2) (1 / 4 : ℝ)
    linarith only [hlow, hm], hz.2.le⟩
  have hexp := norm_exp_rationalPole_strip c hre
  have hscale := norm_nonneg (((2 * a : ℝ) : ℂ) / ((2 * a : ℝ) : ℂ) ^ (2 * m))
  have hmain := mul_le_mul_of_nonneg_left hexp hscale
  have hp := mul_le_mul_of_nonneg_left hpower
    (mul_nonneg hscale (Real.exp_pos ((3 / 2 : ℝ) * |c|)).le)
  rw [Analysis.reciprocalGapFunction, Analysis.twoPoleFunction, norm_div, norm_one,
    norm_mul]
  rw [Analysis.rationalPole_eq_shifted_power m ha c, norm_mul]
  conv_lhs => rhs; rw [norm_div, norm_pow]
  rw [← mul_div_assoc]
  change _ ≤ poleNormFactor m a c * (1 / (‖z + ((1 / 2 : ℝ) : ℂ)‖ *
    ‖z + ((1 / 2 + h : ℝ) : ℂ)‖))
  rw [he]
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [he] at hB hp
  dsimp only [poleNormFactor]
  have hd := div_le_div_of_nonneg_right hmain (pow_nonneg hB.le (2 * m))
  apply hd.trans
  convert hp using 1 <;> ring

/-- For 0<a<1, the comparison multiplier is strictly positive for every m,c.
All scale factors are nonzero, the exponential is positive and the gap is positive.
This verifies the positive constant required by the admissibility decay field. -/
private theorem poleNormFactor_pos (m : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (c : ℝ) :
    0 < poleNormFactor m a c := by
  have hA : ((2 * a : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_pos (by norm_num only) ha).ne'
  have hg := rationalPole_gap_pos ha ha1
  exact mul_pos (mul_pos (mul_pos (norm_pos_iff.mpr (div_ne_zero hA (pow_ne_zero _ hA)))
    (Real.exp_pos _)) (by norm_num only))
    (pow_pos (one_div_pos.mpr (by linarith only [hg])) _)

/-- For m>=1,0<a<1, positive eta and strip points at distance at least eta from
-1/2, the rational-pole norm has a quadratic decay bound. Transfer through the
existing reciprocal-gap estimate without adding an analytic hypothesis. -/
private theorem rationalPole_decay {m : ℕ} (hm : 1 ≤ m) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (c : ℝ)
    {η : ℝ} (hη : 0 < η) {z : ℂ}
    (hz : z ∈ reciprocalGapRegion ((2 * a)⁻¹ - 1 / 2)) (hd : η ≤ ‖z + 1 / 2‖) :
    ‖Analysis.rationalPoleFunction m a c z‖ ≤
      (poleNormFactor m a c * (3 + 6 / (η * ((2 * a)⁻¹ - 1 / 2)))) / (1 + ‖z‖ ^ 2) := by
  have hne : z ≠ -1 / 2 := by
    intro h
    rw [h, neg_div, neg_add_cancel, norm_zero] at hd
    exact (not_le_of_gt hη) hd
  have hp := norm_rationalPole_le_pair hm ha ha1 c hz hne
  have hr := reciprocalGap_strip_bound (rationalPole_gap_pos ha ha1) hη hz hd
  exact hp.trans ((mul_le_mul_of_nonneg_left hr (poleNormFactor_pos m ha ha1 c).le).trans_eq
    (mul_div_assoc _ _ _).symm)

/-- For 0<a<1, every vertical line sigma>-1/2 is right of the rational pole.
Add the strictly positive pole gap to the line condition. This converts the
admissibility line domain into the proved inverse-transform domain. -/
private theorem rationalPole_line_right {a σ : ℝ} (ha : 0 < a) (ha1 : a < 1) (hσ : -1 / 2 < σ) :
    0 < σ + (2 * a)⁻¹ := by
  have hg := rationalPole_gap_pos ha ha1
  linarith only [hg, hσ]

/-- The admissible Mellin kernel 2a exp(2cz)/(1+2az)^(2m), for m>=1 and 0<a<1.
The certified gap strip supplies holomorphy and decay; logarithmic-power inversion
supplies reality, positivity and nonvanishing. All fields are proved and no new
analytic assumptions are added. Orders four and six instantiate the proposed kernels. -/
noncomputable def rationalPoleMellinKernel (m : ℕ) (a c : ℝ) (hm : 1 ≤ m) (ha : 0 < a)
    (ha1 : a < 1) : MellinKernel where
  function := Analysis.rationalPoleFunction m a c
  delta := min (((2 * a)⁻¹ - 1 / 2) / 4) (1 / 8)
  delta_pos := by
    exact (reciprocalGapMellinKernel _ (rationalPole_gap_pos ha ha1)).delta_pos
  region := reciprocalGapRegion ((2 * a)⁻¹ - 1 / 2)
  region_open := by
    exact (reciprocalGapMellinKernel _ (rationalPole_gap_pos ha ha1)).region_open
  strip_subset := by
    exact (reciprocalGapMellinKernel _ (rationalPole_gap_pos ha ha1)).strip_subset
  holomorphic := by
    intro z hz
    exact (differentiableAt_rationalPole m ha ha1 c hz.1).differentiableWithinAt
  regularized z := (z + 1 / 2) * Analysis.rationalPoleFunction m a c z
  regularized_holomorphic := by
    intro z hz
    exact (((differentiableAt_id (𝕜 := ℂ) (x := z)).add_const _).mul
      (differentiableAt_rationalPole m ha ha1 c hz)).differentiableWithinAt
  regularized_eq := fun _ _ _ ↦ rfl
  decay := by
    intro η hη
    refine ⟨poleNormFactor m a c * (3 + 6 / (η * ((2 * a)⁻¹ - 1 / 2))), ?_, ?_⟩
    · exact mul_pos (poleNormFactor_pos m ha ha1 c)
        (add_pos_of_pos_of_nonneg (by norm_num only)
          (div_nonneg (by norm_num only) (mul_pos hη (rationalPole_gap_pos ha ha1)).le))
    · exact fun z hz hd ↦ rationalPole_decay hm ha ha1 c hη hz hd
  mellin_integrable := by
    intro σ u hσ _ hu
    exact integrable_inverseMellin_of_line hu
      (integrable_rationalPole_line hm ha (rationalPole_line_right ha ha1 hσ) c)
  mellin_eq := by
    intro σ u hσ _ hu
    rw [Analysis.inverseMellin_rationalPole hm ha (rationalPole_line_right ha ha1 hσ) hu c,
      Analysis.inverseMellin_rationalPole hm ha
        (rationalPole_line_right ha ha1 (by norm_num only)) hu c]
  mellin_nonneg := by
    intro u hu
    rw [Analysis.inverseMellin_rationalPole hm ha
        (rationalPole_line_right ha ha1 (by norm_num only)) hu c,
      Complex.ofReal_re]
    exact Analysis.rationalPoleProfile_nonneg m ha c u
  mellin_nonzero := by
    refine ⟨Real.exp (2 * c - 2 * a), Real.exp_pos _, ?_⟩
    rw [Analysis.inverseMellin_rationalPole hm ha
        (rationalPole_line_right ha ha1 (by norm_num only))
      (Real.exp_pos _) c, Complex.ofReal_re]
    exact (rationalPoleProfile_pos m ha c).ne'
  mellin_real := by
    intro u hu
    rw [Analysis.inverseMellin_rationalPole hm ha
        (rationalPole_line_right ha ha1 (by norm_num only)) hu c,
      Complex.ofReal_im]
end PseudoPrime.LLS.PaperStatements
