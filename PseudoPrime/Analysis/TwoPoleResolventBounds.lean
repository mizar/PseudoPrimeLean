/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic

/-! # Reciprocal two-pole kernels and adjustable Poisson widths -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The rational function 1/((s+a)(s+b)) for two real pole distances.
It is totalized at the poles. This is the function used in adjustable compact
Mellin profiles and their pointwise resolvent majorants. -/
noncomputable def twoPoleFunction (a b : ℝ) (s : ℂ) : ℂ :=
  1 / ((s + a) * (s + b))

/-- The two-pole function with distances 1/2 and 1/2+h.
Positive gap h makes the second pole strictly left of the first.
This replaces the fixed gap one in finite-scale kernel design. -/
noncomputable def reciprocalGapFunction (h : ℝ) (s : ℂ) : ℂ :=
  twoPoleFunction (1 / 2) (1 / 2 + h) s

/-- If c>0 and c^2<=a*b, the two-pole norm on the imaginary axis is bounded
by 1/(c^2+t^2). Compare the real part of a conjugate product with its norm.
This avoids a special-purpose polynomial calculation for each pole pair. -/
theorem twoPoleFunction_norm_le_resolvent {a b c t : ℝ} (hc : 0 < c) (hab : c ^ 2 ≤ a * b) :
    ‖twoPoleFunction a b (Complex.I * t)‖ ≤ 1 / (c ^ 2 + t ^ 2) := by
  have he : ((Complex.I * (t : ℂ) + a) * star (Complex.I * t + b)).re = a * b + t ^ 2 := by
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.add_re,
      Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, mul_zero, zero_add, sub_zero]
    ring
  have hd := Complex.re_le_norm ((Complex.I * (t : ℂ) + a) * star (Complex.I * t + b))
  rw [he, norm_mul, norm_star] at hd
  have hp : 0 < c ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg t)
  have hbound : c ^ 2 + t ^ 2 ≤ ‖Complex.I * (t : ℂ) + a‖ * ‖Complex.I * (t : ℂ) + b‖ := by
    linarith only [hd, hab]
  rw [twoPoleFunction, norm_div, norm_one, norm_mul]
  exact one_div_le_one_div_of_le hp hbound

/-- For positive Poisson width c with c^2<=1/4+h/2, the gap kernel has the
stated resolvent majorant. Apply the general two-pole inequality.
This is the pointwise certificate for its actual zero mass. -/
theorem reciprocalGapFunction_norm_le_resolvent {h c t : ℝ} (hc : 0 < c)
    (hbound : c ^ 2 ≤ 1 / 4 + h / 2) :
    ‖reciprocalGapFunction h (Complex.I * t)‖ ≤ 1 / (c ^ 2 + t ^ 2) := by
  apply twoPoleFunction_norm_le_resolvent hc
  nlinarith only [hbound]

/-- For any real gap h, the principal endpoint is 1/(1+h).
Normalize the rational expression. This fixes the main-term coefficient used
when comparing different gap parameters. -/
theorem reciprocalGapFunction_endpoint (h : ℝ) :
    reciprocalGapFunction h (1 / 2) = 1 / ((1 + h : ℝ) : ℂ) := by
  unfold reciprocalGapFunction twoPoleFunction
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_add]
  ring

/-- For h,c>0 and c^2=1/4+h/2, the squared leading zero-to-endpoint ratio
is 1+h^2/(1+2h). Clear positive denominators and use the width identity.
This approaches one as h decreases, but does not certify a coefficient below one. -/
theorem reciprocalGap_leading_ratio {h c : ℝ} (hh : 0 < h) (hc : 0 < c)
    (hbound : c ^ 2 = 1 / 4 + h / 2) :
    ((1 / (2 * c)) / (1 / (1 + h))) ^ 2 = 1 + h ^ 2 / (1 + 2 * h) := by
  have hd : (1 + 2 * h) ≠ 0 := ne_of_gt (by linarith only [hh])
  field_simp [hc.ne', hd]
  nlinarith only [hbound]

/-- Given nonnegative masses, unit-bounded phases and a summable Poisson
majorant, the two-pole weighted complex series is summable and has the
displayed norm bound. Use the pointwise resolvent certificate before taking
the infinite sum. This connects arbitrary phases to actual zero-mass budgets. -/
theorem twoPole_sum_bound {ι : Type*} (m t : ι → ℝ) (phase : ι → ℂ) (hm : ∀ i, 0 ≤ m i)
    (hphase : ∀ i, ‖phase i‖ ≤ 1) {a b c : ℝ} (hc : 0 < c) (hab : c ^ 2 ≤ a * b)
    (hs : Summable (fun i ↦ m i * (c / (c ^ 2 + (t i) ^ 2)))) :
    Summable (fun i ↦ (m i : ℂ) * twoPoleFunction a b (Complex.I * t i) * phase i) ∧
      ‖∑' i, (m i : ℂ) * twoPoleFunction a b (Complex.I * t i) * phase i‖ ≤
        (1 / c) * ∑' i, m i * (c / (c ^ 2 + (t i) ^ 2)) := by
  have hb (i : ι) :
    ‖(m i : ℂ) * twoPoleFunction a b (Complex.I * t i) * phase i‖ ≤
      (1 / c) * (m i * (c / (c ^ 2 + (t i) ^ 2))) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hm i)]
    have hp :=
      mul_le_of_le_one_right
        (mul_nonneg (hm i) (norm_nonneg (twoPoleFunction a b (Complex.I * t i)))) (hphase i)
    have hk :=
      mul_le_mul_of_nonneg_left (twoPoleFunction_norm_le_resolvent hc hab (t := t i)) (hm i)
    have he : m i * (1 / (c ^ 2 + (t i) ^ 2)) = (1 / c) * (m i * (c / (c ^ 2 + (t i) ^ 2))) := by
      field_simp [hc.ne']
    exact hp.trans (hk.trans_eq he)
  have hscaled := hs.mul_left (1 / c)
  have hn := hscaled.of_nonneg_of_le (fun i ↦ norm_nonneg _) hb
  have hf := Summable.of_norm_bounded hscaled hb
  refine ⟨hf, ?_⟩
  have h := (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum hb hscaled)
  rwa [tsum_mul_left] at h

end PseudoPrime.Analysis
