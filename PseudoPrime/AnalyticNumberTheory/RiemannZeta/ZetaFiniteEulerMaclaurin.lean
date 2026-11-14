/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.VerticalGrowth

/-! # Finite Euler–Maclaurin formula for zeta -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `Re s > -1`, away from zero and one, truncate the zeta formula at a
positive integer `N`. The remaining integral starts at `N`; splitting the
absolutely convergent sawtooth integral connects the finite and infinite formulas. -/
theorem zeta_eq_finite_sawtooth {s : ℂ} (hs : -1 < s.re) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (N : ℕ)
    (hN : 1 ≤ N) :
    riemannZeta s =
      (∑ k ∈ Finset.Icc 1 N, (k : ℂ) ^ (-s)) - (N : ℂ) ^ (1 - s) / (1 - s) - (N : ℂ) ^ (-s) / 2 -
        s * (s + 1) * ∫ t in Set.Ioi (N : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ) := by
  have htotal :=
    eq_sawtoothFormula_punctured (show s ∈ ({s : ℂ | -1 < s.re} \ {(1 : ℂ)}) from ⟨hs, hs1⟩)
  have hfinite := sum_cpow_eq_sawtoothFormula_finite hs0 hs1 N hN
  have hneg : s ≠ -1 := by
    intro he
    rw [he] at hs
    norm_num only [Complex.neg_re, Complex.one_re] at hs
  rw [integral_fract_sub_half_mul_cpow_eq_Icc hneg N hN] at hfinite
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsplit :=
    intervalIntegral.integral_Ioi_sub_Ioi (integrableOn_cpow_mul_sawtooth_Ioi hs) hNreal
  rw [← hsplit] at hfinite
  linear_combination htotal - hfinite

/-- For `Re s > -1`, away from zero and one, zeta is the Dirichlet sum through
127 plus its endpoint corrections and the sawtooth integral from 128 to infinity.
The formula provides the analytic remainder for the height-100 computation. -/
theorem zeta_eq_finite_128 {s : ℂ} (hs : -1 < s.re) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannZeta s =
      (∑ k ∈ Finset.Icc (1 : ℕ) 127, (k : ℂ) ^ (-s)) + (128 : ℂ) ^ (1 - s) / (s - 1) +
          (128 : ℂ) ^ (-s) / 2 -
        s * (s + 1) *
          ∫ t in Set.Ioi (128 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ) := by
  have hbase := zeta_eq_finite_sawtooth hs hs0 hs1 128 (by norm_num only)
  have hsum :
    (∑ k ∈ Finset.Icc (1 : ℕ) 128, (k : ℂ) ^ (-s)) =
      (∑ k ∈ Finset.Icc (1 : ℕ) 127, (k : ℂ) ^ (-s)) + (128 : ℂ) ^ (-s) := by
    convert
      Finset.sum_Icc_succ_top (a := 1) (b := 127) (by norm_num only)
        (fun k : ℕ => (k : ℂ) ^ (-s)) using
      1
  rw [hsum] at hbase
  have hsign : (1 - s) = -(s - 1) := by ring
  rw [hsign, div_neg] at hbase
  rw [hsign]
  linear_combination hbase

/-- For `Re s ≥ 0`, the norm of the sawtooth tail beginning at 128 is at
most `1/1024`. Bound the sawtooth by `1/8` and integrate the `t⁻²` majorant. -/
theorem norm_sawtooth_tail_128_le {s : ℂ} (hs : 0 ≤ s.re) :
    ‖∫ t in Set.Ioi (128 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ)‖ ≤ 1 / 1024 := by
  have hdom :
    MeasureTheory.IntegrableOn (fun t : ℝ => (1 / 8 : ℝ) * t ^ (-(2 : ℝ))) (Set.Ioi 128) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num only) (by norm_num only)).const_mul _
  have hbound :
    ‖∫ t in Set.Ioi (128 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ)‖ ≤
      ∫ t in Set.Ioi (128 : ℝ), (1 / 8 : ℝ) * t ^ (-(2 : ℝ)) := by
    apply (MeasureTheory.norm_integral_le_integral_norm _).trans
    apply MeasureTheory.integral_mono_of_nonneg
    · filter_upwards with t using norm_nonneg _
    · exact hdom
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
      have ht1 : 1 ≤ t := le_trans (by norm_num only : (1 : ℝ) ≤ 128) ht.le
      have ht0 : 0 < t := lt_of_lt_of_le (by norm_num only) ht1
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real, Real.norm_eq_abs]
      have he : (-s - 2).re = -(s.re + 2) := by
        simp only [Complex.sub_re, Complex.neg_re, Complex.re_ofNat]
        ring
      rw [he]
      have hp :=
        Real.rpow_le_rpow_of_exponent_le ht1 (show -(s.re + 2) ≤ -(2 : ℝ) by linarith only [hs])
      have hn := abs_zetaSawtooth_le t
      have hpos := Real.rpow_nonneg ht0.le (-(s.re + 2))
      have hpos2 := Real.rpow_nonneg ht0.le (-(2 : ℝ))
      nlinarith only [hp, hn, hpos, hpos2, abs_nonneg (zetaSawtooth t)]
  have heval : (∫ t in Set.Ioi (128 : ℝ), (1 / 8 : ℝ) * t ^ (-(2 : ℝ))) = 1 / 1024 := by
    rw [MeasureTheory.integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num only) (by norm_num only : (0 : ℝ) < 128)]
    norm_num only [show (-(2 : ℝ)) + 1 = -1 by norm_num only,
      Real.rpow_neg (show (0 : ℝ) ≤ 128 by norm_num only), Real.rpow_one, neg_div, neg_neg]
  exact hbound.trans_eq heval

/-- Coordinate bounds for the rectangle containing the height-100 circles
give bounds for `s`, `s + 1`, and the distance from the zeta pole. -/
private theorem norms_on_height_100 {s : ℂ} (hr0 : 0 ≤ s.re) (hr2 : s.re ≤ 2) (hiL : 99 ≤ s.im)
    (hiU : s.im ≤ 101) : ‖s‖ ≤ 103 ∧ ‖s + 1‖ ≤ 104 ∧ 99 ≤ ‖s - 1‖ := by
  have him : 0 ≤ s.im := by linarith only [hiL]
  have ha := Complex.norm_le_abs_re_add_abs_im s
  rw [abs_of_nonneg hr0, abs_of_nonneg him] at ha
  have hb := Complex.norm_le_abs_re_add_abs_im (s + 1)
  simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero,
    abs_of_nonneg (show 0 ≤ s.re + 1 by linarith only [hr0]), abs_of_nonneg him] at hb
  have hc := Complex.abs_im_le_norm (s - 1)
  simp only [Complex.sub_im, Complex.one_im, sub_zero, abs_of_nonneg him] at hc
  exact
    ⟨by linarith only [ha, hr2, hiU], by linarith only [hb, hr2, hiU], by linarith only [hc, hiL]⟩

/-- In the nonnegative half-plane, the two endpoint powers at 128 have
norm at most 128 and 1 respectively. -/
private theorem norms_endpoint_powers {s : ℂ} (hr0 : 0 ≤ s.re) :
    ‖(128 : ℂ) ^ (1 - s)‖ ≤ 128 ∧ ‖(128 : ℂ) ^ (-s)‖ ≤ 1 := by
  have hbase : (1 : ℝ) ≤ 128 := by norm_num only
  have hpos : (0 : ℝ) < 128 := by norm_num only
  constructor
  · rw [show (128 : ℂ) = ((128 : ℝ) : ℂ) by norm_num only [Complex.ofReal_ofNat],
      Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    simp only [Complex.sub_re, Complex.one_re]
    calc
      (128 : ℝ) ^ (1 - s.re) ≤ (128 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbase (by linarith only [hr0])
      _ = 128 := by rw [Real.rpow_one]
  · rw [show (128 : ℂ) = ((128 : ℝ) : ℂ) by norm_num only [Complex.ofReal_ofNat],
      Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.neg_re]
    calc
      (128 : ℝ) ^ (-s.re) ≤ (128 : ℝ) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbase (by linarith only [hr0])
      _ = 1 := by rw [Real.rpow_zero]

/-- Bound the three contributions of the finite Euler–Maclaurin remainder
on the rectangle containing the height-100 circles. -/
private theorem finite_remainder_norm (s p m j : ℂ) (hs : ‖s‖ ≤ 103) (hs1 : ‖s + 1‖ ≤ 104)
    (hd : 99 ≤ ‖s - 1‖) (hp : ‖p‖ ≤ 128) (hm : ‖m‖ ≤ 1) (hj : ‖j‖ ≤ 1 / 1024) :
    ‖p / (s - 1) + m / 2 - s * (s + 1) * j‖ ≤ 19 := by
  have hpole : ‖p / (s - 1)‖ ≤ 128 / 99 := by
    rw [norm_div]
    apply (div_le_div_of_nonneg_left (norm_nonneg p) (by norm_num only) hd).trans
    exact div_le_div_of_nonneg_right hp (by norm_num only)
  have hhalf : ‖m / 2‖ ≤ (1 / 2 : ℝ) := by
    rw [norm_div, Complex.norm_ofNat]
    exact div_le_div_of_nonneg_right hm (by norm_num only)
  have hprod : ‖s * (s + 1) * j‖ ≤ (103 : ℝ) * 104 / 1024 := by
    rw [norm_mul, norm_mul]
    have h1 := mul_le_mul hs hs1 (norm_nonneg _) (by norm_num only : (0 : ℝ) ≤ 103)
    have h2 := mul_le_mul h1 hj (norm_nonneg _) (by norm_num only : (0 : ℝ) ≤ 103 * 104)
    norm_num only at h2 ⊢
    exact h2
  have htri := norm_sub_le (p / (s - 1) + m / 2) (s * (s + 1) * j)
  have hadd := norm_add_le (p / (s - 1)) (m / 2)
  linarith only [hpole, hhalf, hprod, htri, hadd]

/-- On the rectangle `0 ≤ Re s ≤ 2` and `99 ≤ Im s ≤ 101`, the error after
the first 127 Dirichlet terms has norm at most 19. The finite formula and
the explicit sawtooth-tail integral provide the bound internally. -/
theorem norm_zeta_sub_sum_128_le {s : ℂ} (hr0 : 0 ≤ s.re) (hr2 : s.re ≤ 2) (hiL : 99 ≤ s.im)
    (hiU : s.im ≤ 101) : ‖riemannZeta s - ∑ n ∈ Finset.Icc (1 : ℕ) 127, (n : ℂ) ^ (-s)‖ ≤ 19 := by
  have hn0 : s ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.zero_im] at hi
    linarith only [hi, hiL]
  have hn1 : s ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.one_im] at hi
    linarith only [hi, hiL]
  have heq := zeta_eq_finite_128 (by linarith only [hr0]) hn0 hn1
  have hn := norms_on_height_100 hr0 hr2 hiL hiU
  have hp := norms_endpoint_powers hr0
  have hj := norm_sawtooth_tail_128_le hr0
  have hb :=
    finite_remainder_norm s ((128 : ℂ) ^ (1 - s)) ((128 : ℂ) ^ (-s))
      (∫ t in Set.Ioi (128 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ)) hn.1 hn.2.1 hn.2.2
      hp.1 hp.2 hj
  have hsub :
    riemannZeta s - (∑ n ∈ Finset.Icc (1 : ℕ) 127, (n : ℂ) ^ (-s)) =
      (128 : ℂ) ^ (1 - s) / (s - 1) + (128 : ℂ) ^ (-s) / 2 -
        s * (s + 1) *
          ∫ t in Set.Ioi (128 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ) := by
    linear_combination heq
  rw [hsub]
  exact hb

/-- On every circle of radius `1/2` centered on the segment from
`1/2 + 100i` to `3/2 + 100i`, the 127-term zeta approximation has error at most 19.
Each circle lies in the rectangle covered by the explicit remainder bound. -/
theorem norm_zeta_sub_sum_circle_le (t : ℝ) (ht : t ∈ Set.Icc (1 / 2) (3 / 2)) (z : ℂ)
    (hz : z ∈ Metric.sphere ((t : ℂ) + ((100 : ℝ) : ℂ) * Complex.I) (1 / 2)) :
    ‖riemannZeta z - ∑ n ∈ Finset.Icc (1 : ℕ) 127, (n : ℂ) ^ (-z)‖ ≤ 19 := by
  have hd := Metric.mem_sphere.mp hz
  rw [Complex.dist_eq] at hd
  have hreal := Complex.abs_re_le_norm (z - ((t : ℂ) + ((100 : ℝ) : ℂ) * Complex.I))
  have himag := Complex.abs_im_le_norm (z - ((t : ℂ) + ((100 : ℝ) : ℂ) * Complex.I))
  rw [hd] at hreal himag
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, sub_zero, zero_add, add_zero] at hreal himag
  have hr := abs_le.mp hreal
  have hi := abs_le.mp himag
  apply norm_zeta_sub_sum_128_le
  · linarith only [hr.1, ht.1]
  · linarith only [hr.2, ht.2]
  · linarith only [hi.1]
  · linarith only [hi.2]

/-- For `Re s > -1`, away from zero and one, the Dirichlet sum through 511
and its endpoint corrections represent zeta up to the sawtooth tail from 512. -/
theorem zeta_eq_finite_512 {s : ℂ} (hs : -1 < s.re) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannZeta s =
      (∑ k ∈ Finset.Icc (1 : ℕ) 511, (k : ℂ) ^ (-s)) + (512 : ℂ) ^ (1 - s) / (s - 1) +
          (512 : ℂ) ^ (-s) / 2 -
        s * (s + 1) *
          ∫ t in Set.Ioi (512 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ) := by
  have hbase := zeta_eq_finite_sawtooth hs hs0 hs1 512 (by norm_num only)
  have hsum :
    (∑ k ∈ Finset.Icc (1 : ℕ) 512, (k : ℂ) ^ (-s)) =
      (∑ k ∈ Finset.Icc (1 : ℕ) 511, (k : ℂ) ^ (-s)) + (512 : ℂ) ^ (-s) := by
    convert
      Finset.sum_Icc_succ_top (a := 1) (b := 511) (by norm_num only)
        (fun k : ℕ => (k : ℂ) ^ (-s)) using
      1
  rw [hsum] at hbase
  have hsign : (1 - s) = -(s - 1) := by ring
  rw [hsign, div_neg] at hbase
  rw [hsign]
  linear_combination hbase

/-- For `Re s ≥ 1/2`, the sawtooth tail from 512 has norm at most `1/90112`.
The estimate combines `sqrt t ≥ 22` with the integrable `t⁻²` majorant. -/
theorem norm_sawtooth_tail_512_le {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) :
    ‖∫ t in Set.Ioi (512 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ)‖ ≤ 1 / 90112 := by
  have hdom :
    MeasureTheory.IntegrableOn (fun t : ℝ => (1 / 176 : ℝ) * t ^ (-(2 : ℝ))) (Set.Ioi 512) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num only) (by norm_num only)).const_mul _
  have hbound :
    ‖∫ t in Set.Ioi (512 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ)‖ ≤
      ∫ t in Set.Ioi (512 : ℝ), (1 / 176 : ℝ) * t ^ (-(2 : ℝ)) := by
    apply (MeasureTheory.norm_integral_le_integral_norm _).trans
    apply MeasureTheory.integral_mono_of_nonneg
    · filter_upwards with t using norm_nonneg _
    · exact hdom
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
      change (512 : ℝ) < t at ht
      have ht1 : 1 ≤ t := le_trans (by norm_num only : (1 : ℝ) ≤ 512) ht.le
      have ht0 : 0 < t := lt_of_lt_of_le (by norm_num only) ht1
      have hsq : (22 : ℝ) ≤ Real.sqrt t := by
        apply (Real.le_sqrt (by norm_num only) ht0.le).2
        nlinarith only [ht.le]
      have hinv : 1 / Real.sqrt t ≤ (1 / 22 : ℝ) := one_div_le_one_div_of_le (by norm_num only) hsq
      have hpow : t ^ (-(5 / 2 : ℝ)) ≤ (1 / 22 : ℝ) * t ^ (-(2 : ℝ)) := by
        rw [show (-(5 / 2 : ℝ)) = -(2 : ℝ) - 1 / 2 by ring, Real.rpow_sub ht0, ← Real.sqrt_eq_rpow,
          div_eq_mul_inv, ← one_div]
        have hm := mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg ht0.le (-(2 : ℝ)))
        simpa only [mul_comm] using hm
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real, Real.norm_eq_abs]
      have he : (-s - 2).re = -(s.re + 2) := by
        simp only [Complex.sub_re, Complex.neg_re, Complex.re_ofNat]
        ring
      rw [he]
      have hp :=
        Real.rpow_le_rpow_of_exponent_le ht1 (show -(s.re + 2) ≤ -(5 / 2 : ℝ) by linarith only [hs])
      have hn := abs_zetaSawtooth_le t
      have hpos := Real.rpow_nonneg ht0.le (-(s.re + 2))
      have hpos2 := Real.rpow_nonneg ht0.le (-(2 : ℝ))
      nlinarith only [hp, hn, hpos, hpos2, hpow, abs_nonneg (zetaSawtooth t)]
  have heval : (∫ t in Set.Ioi (512 : ℝ), (1 / 176 : ℝ) * t ^ (-(2 : ℝ))) = 1 / 90112 := by
    rw [MeasureTheory.integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num only) (by norm_num only : (0 : ℝ) < 512)]
    norm_num only [show (-(2 : ℝ)) + 1 = -1 by norm_num only,
      Real.rpow_neg (show (0 : ℝ) ≤ 512 by norm_num only), Real.rpow_one, neg_div, neg_neg]
  exact hbound.trans_eq heval

/-- On the height-100 rectangle with `Re s ≥ 1/2`, the 511-term Dirichlet
sum and two endpoint corrections approximate zeta within `1/8`. This converts
grid-value certification into a finite computation without a zero table. -/
theorem norm_zeta_finite_512_le {s : ℂ} (hr0 : (1 / 2 : ℝ) ≤ s.re) (hr2 : s.re ≤ 2)
    (hiL : 99 ≤ s.im) (hiU : s.im ≤ 101) :
    ‖riemannZeta s -
          ((∑ n ∈ Finset.Icc (1 : ℕ) 511, (n : ℂ) ^ (-s)) + (512 : ℂ) ^ (1 - s) / (s - 1) +
            (512 : ℂ) ^ (-s) / 2)‖ ≤
      1 / 8 := by
  have hn0 : s ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.zero_im] at hi
    linarith only [hi, hiL]
  have hn1 : s ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.one_im] at hi
    linarith only [hi, hiL]
  have heq := zeta_eq_finite_512 (by linarith only [hr0]) hn0 hn1
  have hn := norms_on_height_100 (by linarith only [hr0]) hr2 hiL hiU
  have hj := norm_sawtooth_tail_512_le hr0
  have hprod :
    ‖s * (s + 1) * ∫ t in Set.Ioi (512 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ)‖ ≤
      (1 / 8 : ℝ) := by
    rw [norm_mul, norm_mul]
    have h1 := mul_le_mul hn.1 hn.2.1 (norm_nonneg _) (by norm_num only : (0 : ℝ) ≤ 103)
    have h2 := mul_le_mul h1 hj (norm_nonneg _) (by norm_num only : (0 : ℝ) ≤ 103 * 104)
    nlinarith only [h2]
  have hsub :
    riemannZeta s -
        ((∑ n ∈ Finset.Icc (1 : ℕ) 511, (n : ℂ) ^ (-s)) + (512 : ℂ) ^ (1 - s) / (s - 1) +
          (512 : ℂ) ^ (-s) / 2) =
      -(s * (s + 1) *
          ∫ t in Set.Ioi (512 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ)) := by
    linear_combination heq
  rw [hsub, norm_neg]
  exact hprod

/-- On the height-100 rectangle, a lower bound `9/8` for the real part of
the finite approximation through 511 proves `Re ζ(s) ≥ 1`. -/
theorem zeta_re_lower_of_finite_512 {s : ℂ} (hr0 : (1 / 2 : ℝ) ≤ s.re) (hr2 : s.re ≤ 2)
    (hiL : 99 ≤ s.im) (hiU : s.im ≤ 101)
    (h :
      (9 / 8 : ℝ) ≤
        ((∑ n ∈ Finset.Icc (1 : ℕ) 511, (n : ℂ) ^ (-s)) + (512 : ℂ) ^ (1 - s) / (s - 1) +
            (512 : ℂ) ^ (-s) / 2).re) :
    1 ≤ (riemannZeta s).re := by
  have he := (Complex.abs_re_le_norm _).trans (norm_zeta_finite_512_le hr0 hr2 hiL hiU)
  simp only [Complex.sub_re] at he
  have he' := (abs_le.mp he).1
  linarith only [he', h]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
