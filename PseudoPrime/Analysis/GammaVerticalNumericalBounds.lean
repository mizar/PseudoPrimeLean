/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaMellin
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.Real.Pi.Bounds

/-! # Numerical Gamma bounds on a fixed negative line

Recurrence gives fourth-order vertical decay. Real Gamma monotonicity provides
explicit numerator constants on the line Re s=-1/16.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- At nonzero imaginary part, two Gamma recurrences imply
norm(Gamma s) Im(s)^2≤norm(Gamma(s+2)). Each recurrence factor has norm
at least |Im s|. This is the algebraic step for higher-order vertical decay. -/
private theorem norm_Gamma_mul_im_sq_le_shift {s : ℂ} (hi : s.im ≠ 0) :
    ‖Complex.Gamma s‖ * s.im ^ 2 ≤ ‖Complex.Gamma (s + 2)‖ := by
  have hzero : s ≠ 0 := by
    intro he
    exact hi (congrArg Complex.im he)
  have hone : s + 1 ≠ 0 := by
    intro he
    have him := congrArg Complex.im he
    simp only [Complex.add_im, Complex.one_im, add_zero, Complex.zero_im] at him
    exact hi him
  have he : Complex.Gamma (s + 2) = (s + 1) * s * Complex.Gamma s := by
    calc
      _ = Complex.Gamma ((s + 1) + 1) := by
        congr 1; ring
      _ = (s + 1) * (s * Complex.Gamma s) := by
        rw [Complex.Gamma_add_one _ hone, Complex.Gamma_add_one _ hzero]
      _ = _ := by ring
  rw [he, norm_mul, norm_mul]
  have hleft := Complex.abs_im_le_norm (s + 1)
  simp only [Complex.add_im, Complex.one_im, add_zero] at hleft
  have hprod := mul_le_mul hleft (Complex.abs_im_le_norm s) (abs_nonneg s.im) (norm_nonneg (s + 1))
  have hm := mul_le_mul_of_nonneg_right hprod (norm_nonneg (Complex.Gamma s))
  rw [← pow_two, sq_abs] at hm
  linarith only [hm]

/-- For Re s>-4 and Im s≠0, the Gamma norm is at most Gamma(Re s+4)/Im(s)^4.
Apply two recurrences and the quadratic bound to the shifted argument.
This provides integrable decay when multiplied by a linear height envelope. -/
theorem norm_Gamma_le_im_fourth {s : ℂ} (hs : -4 < s.re) (hi : s.im ≠ 0) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma (s.re + 4) / s.im ^ 4 := by
  have hshift : -2 < (s + 2).re := by
    rw [Complex.add_re]
    change -2 < s.re + 2
    linarith only [hs]
  have hi' : (s + 2).im ≠ 0 := by
    simpa only [Complex.add_im, show (2 : ℂ).im = 0 from rfl, add_zero] using hi
  have hb := norm_Gamma_le_im_sq hshift hi'
  have he : (s + 2).re + 2 = s.re + 4 := by
    rw [Complex.add_re]
    change s.re + 2 + 2 = s.re + 4
    ring
  have ht : (s + 2).im = s.im := by
    simp only [Complex.add_im, show (2 : ℂ).im = 0 from rfl, add_zero]
  rw [he, ht] at hb
  have hm := norm_Gamma_mul_im_sq_le_shift hi
  have hmul := mul_le_mul_of_nonneg_right hb (sq_nonneg s.im)
  rw [div_mul_cancel₀ _ (sq_pos_of_ne_zero hi).ne'] at hmul
  rw [show s.im ^ 4 = (s.im ^ 2) ^ 2 by ring]
  apply (le_div_iff₀ (pow_pos (sq_pos_of_ne_zero hi) 2)).mpr
  nlinarith only [hm, hmul, sq_nonneg s.im]

/-- On Re s=-1/16, Gamma has norm at most thirty-two at every height.
One recurrence shifts to 15/16, where real Gamma is at most sqrt(pi)≤2;
the recurrence factor has norm at least 1/16. This covers bounded heights. -/
theorem norm_Gamma_neg_one_sixteenth_le_thirty_two {s : ℂ} (hs : s.re = -1 / 16) :
    ‖Complex.Gamma s‖ ≤ 32 := by
  have hp : 0 < (s + 1).re := by
    rw [Complex.add_re, Complex.one_re, hs]; norm_num only
  have hn := norm_Gamma_le_realGamma hp
  have hr : (s + 1).re = 15 / 16 := by
    rw [Complex.add_re, Complex.one_re, hs]
    norm_num only
  rw [hr] at hn
  have hg : Real.Gamma (15 / 16) ≤ Real.Gamma (1 / 2) :=
    Real.Gamma_strictAntiOn_Ioc.antitoneOn ⟨by norm_num only, by norm_num only⟩
      ⟨by norm_num only, by norm_num only⟩ (by norm_num only)
  rw [Real.Gamma_one_half_eq] at hg
  have hsqrt : Real.sqrt Real.pi ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by nlinarith only [Real.pi_lt_four]⟩
  have hsne : s ≠ 0 := by
    intro he
    have hz := congrArg Complex.re he
    rw [hs, Complex.zero_re] at hz
    norm_num only at hz
  rw [Complex.Gamma_add_one s hsne, norm_mul] at hn
  have hl := Complex.abs_re_le_norm s
  rw [hs] at hl
  norm_num only at hl
  have hm := mul_le_mul_of_nonneg_right hl (norm_nonneg (Complex.Gamma s))
  nlinarith only [hm, hn, hg, hsqrt]

/-- On Re s=-1/16 with nonzero height, Gamma has norm at most 6/Im(s)^4.
The fourth-order recurrence numerator has real part 63/16≤4; monotonicity
above two bounds its real Gamma value by Gamma(4)=6. This controls the tail. -/
theorem norm_Gamma_neg_one_sixteenth_le_fourth {s : ℂ} (hs : s.re = -1 / 16) (hi : s.im ≠ 0) :
    ‖Complex.Gamma s‖ ≤ 6 / s.im ^ 4 := by
  have hb :=
    norm_Gamma_le_im_fourth
      (by
        rw [hs]; norm_num only)
      hi
  rw [hs] at hb
  have hg : Real.Gamma (-1 / 16 + 4) ≤ Real.Gamma 4 :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn (by norm_num only [Set.mem_Ici])
      (by norm_num only [Set.mem_Ici]) (by norm_num only)
  have hv := Real.Gamma_nat_eq_factorial 3
  norm_num only [Nat.factorial] at hv
  rw [hv] at hg
  have h4 : 0 ≤ s.im ^ 4 := by nlinarith only [sq_nonneg (s.im ^ 2)]
  exact hb.trans (div_le_div_of_nonneg_right hg h4)

/-- On Re s=-1/16 at nonzero height, Gamma has norm at most 2/|Im s|.
One recurrence shifts to 15/16, where real Gamma is bounded by sqrt(pi)≤2.
The imaginary part bounds the recurrence factor from below.
This controls the middle region in the sharp left-integral moments. -/
theorem norm_Gamma_neg_one_sixteenth_le_inverse {s : ℂ} (hs : s.re = -1 / 16) (hi : s.im ≠ 0) :
    ‖Complex.Gamma s‖ ≤ 2 / |s.im| := by
  have hp : 0 < (s + 1).re := by
    rw [Complex.add_re, Complex.one_re, hs]; norm_num only
  have hn := norm_Gamma_le_realGamma hp
  have hr : (s + 1).re = 15 / 16 := by
    rw [Complex.add_re, Complex.one_re, hs]
    norm_num only
  rw [hr] at hn
  have hg : Real.Gamma (15 / 16) ≤ Real.Gamma (1 / 2) :=
    Real.Gamma_strictAntiOn_Ioc.antitoneOn ⟨by norm_num only, by norm_num only⟩
      ⟨by norm_num only, by norm_num only⟩ (by norm_num only)
  rw [Real.Gamma_one_half_eq] at hg
  have hsqrt : Real.sqrt Real.pi ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by nlinarith only [Real.pi_lt_four]⟩
  have hsne : s ≠ 0 := by
    intro he
    have hz := congrArg Complex.re he
    rw [hs, Complex.zero_re] at hz
    norm_num only at hz
  rw [Complex.Gamma_add_one s hsne, norm_mul] at hn
  have hm := mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm s) (norm_nonneg (Complex.Gamma s))
  have ha : 0 < |s.im| := abs_pos.mpr hi
  apply (le_div_iff₀ ha).mpr
  nlinarith only [hm, hn, hg, hsqrt]

end PseudoPrime.Analysis
