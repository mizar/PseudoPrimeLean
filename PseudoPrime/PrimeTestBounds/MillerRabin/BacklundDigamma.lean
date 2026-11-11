/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import PseudoPrime.AnalyticNumberTheory.Gamma.EulerLogSeries

/-! # Resolvent bounds for the reflected gamma phase -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The imaginary part of a reciprocal at height `y` is the negative
resolvent kernel. Expand the complex inverse using its norm square. -/
private theorem reciprocal_im (r y : ℝ) :
    (1 / ((r : ℂ) + (y : ℂ) * Complex.I)).im = -y / (r ^ 2 + y ^ 2) := by
  rw [one_div, Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one,
    zero_add, pow_two]

/-- The imaginary part of a shifted complex reciprocal difference is the
difference of the corresponding real resolvent kernels. This identifies the
terms in the digamma series with the telescoping estimate. -/
private theorem resolvent_difference_im (a b y : ℝ) (n : ℕ) :
    (1 / (((a : ℂ) + (y : ℂ) * Complex.I) + n) - 1 / (((b : ℂ) + (y : ℂ) * Complex.I) + n)).im =
      y / (((n : ℝ) + b) ^ 2 + y ^ 2) - y / (((n : ℝ) + a) ^ 2 + y ^ 2) := by
  have hA :
    ((a : ℂ) + (y : ℂ) * Complex.I) + n = (((n : ℝ) + a : ℝ) : ℂ) + (y : ℂ) * Complex.I := by
    push_cast
    ring
  have hB :
    ((b : ℂ) + (y : ℂ) * Complex.I) + n = (((n : ℝ) + b : ℝ) : ℂ) + (y : ℂ) * Complex.I := by
    push_cast
    ring
  rw [Complex.sub_im, hA, hB, reciprocal_im, reciprocal_im]
  ring

/-- At a positive height, the digamma recurrence shifts any real part by
one. Its imaginary correction is the negative resolvent kernel; the height
excludes every nonpositive-integer pole. -/
private theorem digamma_im_shift (r y : ℝ) (hy : 0 < y) :
    (Complex.digamma (((r + 1 : ℝ) : ℂ) + (y : ℂ) * Complex.I)).im =
      (Complex.digamma ((r : ℂ) + (y : ℂ) * Complex.I)).im - y / (r ^ 2 + y ^ 2) := by
  have hn : ∀ n : ℕ, (r : ℂ) + (y : ℂ) * Complex.I ≠ -(n : ℂ) := by
    intro n he
    have hi := congrArg Complex.im he
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_one, mul_zero, add_zero, zero_add, Complex.neg_im, Complex.natCast_im,
      neg_zero] at hi
    linarith only [hy, hi]
  have he : (((r + 1 : ℝ) : ℂ) + (y : ℂ) * Complex.I) = ((r : ℂ) + (y : ℂ) * Complex.I) + 1 := by
    push_cast
    ring
  rw [he, Complex.digamma_apply_add_one _ hn, Complex.add_im, ← one_div, reciprocal_im]
  ring

/-- For positive `y`, if `|r| ≤ s ≤ r + 1`, the difference of the
resolvent imaginary parts at `r` and `s` is nonnegative and is bounded by
the difference at `r` and `r + 1`. Compare the positive denominators. -/
theorem backlund_resolvent_between {y r s : ℝ} (hy : 0 < y) (habs : |r| ≤ s) (hrs : s ≤ r + 1) :
    0 ≤ y / (r ^ 2 + y ^ 2) - y / (s ^ 2 + y ^ 2) ∧
      y / (r ^ 2 + y ^ 2) - y / (s ^ 2 + y ^ 2) ≤
        y / (r ^ 2 + y ^ 2) - y / ((r + 1) ^ 2 + y ^ 2) := by
  have hab := abs_le.mp habs
  have hs : 0 ≤ s := le_trans (abs_nonneg r) habs
  have hsq1 : r ^ 2 ≤ s ^ 2 := by nlinarith only [hab.1, hab.2, hs, sq_nonneg (s - r)]
  have hsq2 : s ^ 2 ≤ (r + 1) ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hrs) (by linarith only [hrs, hs] : 0 ≤ r + 1 + s)
    nlinarith only [h]
  have hp1 : 0 < r ^ 2 + y ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg r) (sq_pos_of_pos hy)
  have hp2 : 0 < s ^ 2 + y ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg s) (sq_pos_of_pos hy)
  have hd1 : r ^ 2 + y ^ 2 ≤ s ^ 2 + y ^ 2 := by linarith only [hsq1]
  have hd2 : s ^ 2 + y ^ 2 ≤ (r + 1) ^ 2 + y ^ 2 := by linarith only [hsq2]
  have h1 := one_div_le_one_div_of_le hp1 hd1
  have h2 := one_div_le_one_div_of_le hp2 hd2
  have hm1 := mul_le_mul_of_nonneg_left h1 hy.le
  have hm2 := mul_le_mul_of_nonneg_left h2 hy.le
  simp only [mul_one_div] at hm1 hm2
  constructor <;> linarith only [hm1, hm2]

/-- A nonnegative sequence bounded termwise by successive differences of a
nonnegative sequence is summable, and its total is at most the first value.
Finite partial sums telescope, so no separate limit of the upper sequence
is needed. -/
private theorem summable_le_telescope {d g : ℕ → ℝ} (hd : ∀ n, 0 ≤ d n) (hg : ∀ n, 0 ≤ g n)
    (hbound : ∀ n, d n ≤ g n - g (n + 1)) : Summable d ∧ (∑' n, d n) ≤ g 0 := by
  have hpartial : ∀ n, ∑ i ∈ Finset.range n, d i ≤ g 0 := by
    intro n
    calc
      (∑ i ∈ Finset.range n, d i) ≤ ∑ i ∈ Finset.range n, (g i - g (i + 1)) :=
        Finset.sum_le_sum (fun i _ => hbound i)
      _ = g 0 - g n := Finset.sum_range_sub' g n
      _ ≤ g 0 := sub_le_self _ (hg n)
  have hsum := summable_of_sum_range_le hd hpartial
  exact ⟨hsum, hsum.tsum_le_of_sum_range_le hpartial⟩

/-- For `y > 0` and `|b| ≤ a ≤ b + 1`, the resolvent-difference series
is nonnegative, summable and at most its first telescoping term. This is the
quantitative series estimate used for the reflected digamma phase. -/
theorem backlund_resolvent_series {a b y : ℝ} (hy : 0 < y) (hab : |b| ≤ a) (ha : a ≤ b + 1) :
    Summable (fun n : ℕ => y / (((n : ℝ) + b) ^ 2 + y ^ 2) - y / (((n : ℝ) + a) ^ 2 + y ^ 2)) ∧
      0 ≤ (∑' n : ℕ, (y / (((n : ℝ) + b) ^ 2 + y ^ 2) - y / (((n : ℝ) + a) ^ 2 + y ^ 2))) ∧
      (∑' n : ℕ, (y / (((n : ℝ) + b) ^ 2 + y ^ 2) - y / (((n : ℝ) + a) ^ 2 + y ^ 2))) ≤
        y / (b ^ 2 + y ^ 2) := by
  let d : ℕ → ℝ := fun n => y / (((n : ℝ) + b) ^ 2 + y ^ 2) - y / (((n : ℝ) + a) ^ 2 + y ^ 2)
  let g : ℕ → ℝ := fun n => y / (((n : ℝ) + b) ^ 2 + y ^ 2)
  have hp : ∀ n, 0 ≤ d n ∧ d n ≤ g n - g (n + 1) := by
    intro n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hb := abs_le.mp hab
    have hab' : |(n : ℝ) + b| ≤ (n : ℝ) + a := by
      apply abs_le.mpr
      constructor <;> linarith only [hn, hb.1, hb.2]
    have ha' : (n : ℝ) + a ≤ ((n : ℝ) + b) + 1 := by linarith only [ha]
    have h := backlund_resolvent_between hy hab' ha'
    have he : ((n + 1 : ℕ) : ℝ) + b = ((n : ℝ) + b) + 1 := by
      push_cast
      ring
    dsimp only [d, g]
    rw [he]
    exact h
  have hg : ∀ n, 0 ≤ g n := by
    intro n
    apply div_nonneg hy.le
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hsum := summable_le_telescope (fun n => (hp n).1) hg (fun n => (hp n).2)
  refine ⟨hsum.1, tsum_nonneg (fun n => (hp n).1), ?_⟩
  simpa only [g, Nat.cast_zero, zero_add] using hsum.2

/-- At positive real parts, the imaginary part of the digamma difference is
the sum of the real resolvent differences. The Euler series is summable, so
the continuous imaginary-part map can be interchanged with the sum. -/
private theorem digamma_im_difference_series {a b y : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (Complex.digamma ((b : ℂ) + (y : ℂ) * Complex.I)).im -
        (Complex.digamma ((a : ℂ) + (y : ℂ) * Complex.I)).im =
      ∑' n : ℕ, (y / (((n : ℝ) + b) ^ 2 + y ^ 2) - y / (((n : ℝ) + a) ^ 2 + y ^ 2)) := by
  have hA : 0 < (((a : ℂ) + (y : ℂ) * Complex.I).re) := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero] using ha
  have hB : 0 < (((b : ℂ) + (y : ℂ) * Complex.I).re) := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero] using hb
  have hs :=
    AnalyticNumberTheory.Gamma.summable_resolventDifference (s := (a : ℂ) + (y : ℂ) * Complex.I)
      (t := (b : ℂ) + (y : ℂ) * Complex.I) hA.le hB.le
  have hd :=
    AnalyticNumberTheory.Gamma.digamma_sub_eq_resolventSeries (s := (b : ℂ) + (y : ℂ) * Complex.I)
      (t := (a : ℂ) + (y : ℂ) * Complex.I) hB hA
  have hi := congrArg Complex.im hd
  rw [Complex.sub_im, Complex.im_tsum hs] at hi
  exact hi.trans (tsum_congr (resolvent_difference_im a b y))

/-- If both real parts are positive and `|b| ≤ a ≤ b + 1`, the imaginary
digamma difference at a positive height lies between zero and the first
resolvent kernel. The Euler series and the telescoping bound supply the two
inequalities. -/
theorem backlund_digamma_im_positive {a b y : ℝ} (ha : 0 < a) (hb : 0 < b) (hy : 0 < y)
    (hab : |b| ≤ a) (ha' : a ≤ b + 1) :
    0 ≤
        (Complex.digamma ((b : ℂ) + (y : ℂ) * Complex.I)).im -
          (Complex.digamma ((a : ℂ) + (y : ℂ) * Complex.I)).im ∧
      (Complex.digamma ((b : ℂ) + (y : ℂ) * Complex.I)).im -
          (Complex.digamma ((a : ℂ) + (y : ℂ) * Complex.I)).im ≤
        y / (b ^ 2 + y ^ 2) := by
  rw [digamma_im_difference_series ha hb]
  exact (backlund_resolvent_series hy hab ha').2

/-- If `-1 < b`, `|b| ≤ a ≤ b + 1` and `y > 0`, the reflected digamma
imaginary difference is between zero and its initial resolvent kernel.
Shift both arguments by one, apply the positive-half-plane series, and use
the digamma recurrence to restore the first term. -/
theorem backlund_digamma_im_difference {a b y : ℝ} (hb : -1 < b) (hy : 0 < y) (hab : |b| ≤ a)
    (ha : a ≤ b + 1) :
    0 ≤
        (Complex.digamma ((b : ℂ) + (y : ℂ) * Complex.I)).im -
          (Complex.digamma ((a : ℂ) + (y : ℂ) * Complex.I)).im ∧
      (Complex.digamma ((b : ℂ) + (y : ℂ) * Complex.I)).im -
          (Complex.digamma ((a : ℂ) + (y : ℂ) * Complex.I)).im ≤
        y / (b ^ 2 + y ^ 2) := by
  have ha0 : 0 ≤ a := le_trans (abs_nonneg b) hab
  have hshift :=
    digamma_im_difference_series (a := a + 1) (b := b + 1) (y := y) (by linarith only [ha0])
      (by linarith only [hb])
  let d : ℕ → ℝ := fun n => y / (((n : ℝ) + b) ^ 2 + y ^ 2) - y / (((n : ℝ) + a) ^ 2 + y ^ 2)
  have hseries :
    (∑' n : ℕ, (y / (((n : ℝ) + (b + 1)) ^ 2 + y ^ 2) - y / (((n : ℝ) + (a + 1)) ^ 2 + y ^ 2))) =
      ∑' n : ℕ, d (n + 1) := by
    apply tsum_congr
    intro n
    dsimp only [d]
    push_cast
    congr 2 <;> ring
  rw [hseries, digamma_im_shift b y hy, digamma_im_shift a y hy] at hshift
  have hbound := backlund_resolvent_series hy hab ha
  have hfull := hbound.1.tsum_eq_zero_add
  change (∑' n, d n) = d 0 + ∑' n, d (n + 1) at hfull
  have hd0 : d 0 = y / (b ^ 2 + y ^ 2) - y / (a ^ 2 + y ^ 2) := by
    simp only [d, Nat.cast_zero, zero_add]
  have he :
    (Complex.digamma ((b : ℂ) + (y : ℂ) * Complex.I)).im -
        (Complex.digamma ((a : ℂ) + (y : ℂ) * Complex.I)).im =
      ∑' n, d n := by
    rw [hfull, hd0]
    linarith only [hshift]
  rw [he]
  exact hbound.2

/-- Under the reflected-strip hypotheses, the digamma imaginary difference
has absolute size at most `1/y`. The sharper nonnegative kernel bound is at
most `1/y` because its denominator is at least `y²`. -/
theorem backlund_digamma_im_le_inv {a b y : ℝ} (hb : -1 < b) (hy : 0 < y) (hab : |b| ≤ a)
    (ha : a ≤ b + 1) :
    |(Complex.digamma ((b : ℂ) + (y : ℂ) * Complex.I)).im -
          (Complex.digamma ((a : ℂ) + (y : ℂ) * Complex.I)).im| ≤
      1 / y := by
  have h := backlund_digamma_im_difference hb hy hab ha
  rw [abs_of_nonneg h.1]
  apply h.2.trans
  have hd : 0 < b ^ 2 + y ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg b) (sq_pos_of_pos hy)
  apply (div_le_div_iff₀ hd hy).2
  nlinarith only [sq_nonneg b]

/-- On the reflected segment `0 ≤ u ≤ 1` at positive height `T`, half the
absolute digamma imaginary difference is at most `1/T`. Substitute the two
Gamma arguments `1/4 ± u/2 + iT/2` into the telescoping estimate. -/
theorem backlund_digamma_reflection {T u : ℝ} (hT : 0 < T) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (1 / 2 : ℝ) *
        |(Complex.digamma (((1 / 4 - u / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * Complex.I)).im -
            (Complex.digamma (((1 / 4 + u / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * Complex.I)).im| ≤
      1 / T := by
  have hb : (-1 : ℝ) < 1 / 4 - u / 2 := by linarith only [hu.2]
  have hy : (0 : ℝ) < T / 2 := by linarith only [hT]
  have hab : |(1 / 4 : ℝ) - u / 2| ≤ 1 / 4 + u / 2 := by
    apply abs_le.mpr
    constructor <;> linarith only [hu.1]
  have ha : (1 / 4 : ℝ) + u / 2 ≤ 1 / 4 - u / 2 + 1 := by linarith only [hu.2]
  have h := backlund_digamma_im_le_inv hb hy hab ha
  have hmul := mul_le_mul_of_nonneg_left h (by norm_num only : (0 : ℝ) ≤ 1 / 2)
  have he : (1 / 2 : ℝ) * (1 / (T / 2)) = 1 / T := by
    calc
      _ = (1 / (T / 2)) / 2 := by ring
      _ = 1 / ((T / 2) * 2) := by rw [div_div]
      _ = 1 / T := by
        congr 1; ring
  rw [he] at hmul
  exact hmul

end PseudoPrime.PrimeTestBounds.MillerRabin
