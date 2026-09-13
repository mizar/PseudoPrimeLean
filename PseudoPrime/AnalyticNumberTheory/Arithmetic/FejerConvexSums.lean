/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedMangoldt

/-!
# Finite complex power sums

This file proves a finite Fejér decomposition on the unit circle using the squared norms of
`Σ_{r=0}^j z^r`. Nonnegative second differences and boundary terms give lower bounds for the
real parts of power sums with affine or geometric coefficients, used in level-change estimates.
-/

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The partial geometric power sum used in a finite Fejér decomposition. -/
def fejerPartialPowerSum (z : ℂ) (j : ℕ) : ℂ :=
  Finset.sum (Finset.range (j + 1)) fun r => z ^ r

/-- The zeroth Fejér partial sum is the constant `1`. -/
theorem fejerPartialPowerSum_zero (z : ℂ) : fejerPartialPowerSum z 0 = 1 := by
  simp only [fejerPartialPowerSum, zero_add, Finset.range_one, Finset.sum_singleton, pow_zero]

/-- The zeroth Fejér partial sum is the constant `1`, hence has norm-square `1`. -/
theorem norm_fejerPartialPowerSum_zero_sq (z : ℂ) : ‖fejerPartialPowerSum z 0‖ ^ 2 = 1 := by
  rw [fejerPartialPowerSum_zero]
  simp only [norm_one, one_pow]

/-- The first Fejér kernel expansion on the unit circle. -/
theorem norm_fejerPartialPowerSum_one_sq {z : ℂ} (hz : ‖z‖ = 1) :
    ‖fejerPartialPowerSum z 1‖ ^ 2 = 2 + 2 * z.re := by
  have hzsq : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [hz] at h
    rw [Complex.normSq_apply] at h
    nlinarith
  simp only [fejerPartialPowerSum, Nat.reduceAdd, geom_sum_two, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero]
  ring_nf
  nlinarith [hzsq]

/-- Successive Fejér partial sums differ by their newly added power. -/
theorem fejerPartialPowerSum_succ (z : ℂ) (j : ℕ) :
    fejerPartialPowerSum z (j + 1) = fejerPartialPowerSum z j + z ^ (j + 1) := by
  simp only [fejerPartialPowerSum, Finset.sum_range_succ]

/-- Every power of a unit-circle complex number has norm-square `1`. -/
theorem normSq_pow_eq_one_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) :
    Complex.normSq (z ^ n) = 1 := by
  rw [Complex.normSq_eq_norm_sq, norm_pow, hz]
  simp only [one_pow]

/-- The norm-square recurrence for successive Fejér partial sums on the unit circle. -/
theorem normSq_fejerPartialPowerSum_succ {z : ℂ} (hz : ‖z‖ = 1) (j : ℕ) :
    Complex.normSq (fejerPartialPowerSum z (j + 1)) =
      Complex.normSq (fejerPartialPowerSum z j) + 1 +
        2 * (fejerPartialPowerSum z j * (starRingEnd ℂ) (z ^ (j + 1))).re := by
  rw [fejerPartialPowerSum_succ]
  rw [Complex.normSq_add]
  rw [normSq_pow_eq_one_of_norm_eq_one hz]

/--
Nonnegative discrete second differences make a Fejér decomposition nonnegative.

The equality hypothesis is the algebraic finite-sum decomposition; isolating it here keeps the
positivity argument independent of characters and allows the identity to be proved separately by
finite-sum algebra.
-/
theorem fejer_decomposition_nonneg {a : ℕ → ℝ} {z : ℂ} {K : ℕ}
    (hconv : ∀ j ∈ Finset.range (K + 1), 0 ≤ a j - 2 * a (j + 1) + a (j + 2))
    (hdecomp :
      a 0 + 2 * (Finset.sum (Finset.Icc 1 K) fun k => a k * z ^ k).re =
        Finset.sum (Finset.range (K + 1)) fun j =>
          (a j - 2 * a (j + 1) + a (j + 2)) * ‖fejerPartialPowerSum z j‖ ^ 2) :
    0 ≤ a 0 + 2 * (Finset.sum (Finset.Icc 1 K) fun k => a k * z ^ k).re := by
  rw [hdecomp]
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (hconv j hj) (sq_nonneg _)

/-- On the unit circle, a complex number times its own conjugate is `1`. -/
theorem mul_conj_eq_one_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : z * (starRingEnd ℂ) z = 1 := by
  rw [Complex.mul_conj]
  have h := Complex.normSq_eq_norm_sq z
  rw [hz] at h
  rw [h]
  simp only [one_pow, Complex.ofReal_one]

/--
The finite geometric telescope of the Fejér partial sum against `conj z - 1`.

This is the key finite-sum identity feeding the kernel-square second-difference formula: it
collapses the partial sum `∑_{r=0}^{n} z^r` against a single factor of `conj z - 1` down to the
two endpoint terms `conj z` and `z ^ n`.
-/
theorem fejerPartialPowerSum_mul_conj_sub_one {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) :
    fejerPartialPowerSum z n * ((starRingEnd ℂ) z - 1) = (starRingEnd ℂ) z - z ^ n := by
  have hzc : z * (starRingEnd ℂ) z = 1 := mul_conj_eq_one_of_norm_eq_one hz
  induction n with
  | zero => simp only [fejerPartialPowerSum_zero, one_mul, pow_zero]
  | succ n ih =>
    rw [fejerPartialPowerSum_succ]
    have hstep : z ^ (n + 1) * ((starRingEnd ℂ) z - 1) = z ^ n - z ^ (n + 1) := by
      have : z ^ (n + 1) * (starRingEnd ℂ) z = z ^ n := by
        rw [pow_succ]
        linear_combination z ^ n * hzc
      linear_combination this
    linear_combination ih + hstep

/--
The complex-valued cross-term identity feeding the Fejér kernel-square second difference.

On the unit circle, the increment of `fejerPartialPowerSum z (n + 1) · conj (z ^ (n + 2))`
over `fejerPartialPowerSum z n · conj (z ^ (n + 1))` collapses to the single term
`conj (z ^ (n + 2))`, with no leftover dependence on the earlier partial sum.
-/
theorem fejerPartialPowerSum_succ_mul_conj_pow_sub {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) :
    fejerPartialPowerSum z (n + 1) * (starRingEnd ℂ) (z ^ (n + 2)) -
        fejerPartialPowerSum z n * (starRingEnd ℂ) (z ^ (n + 1)) =
      (starRingEnd ℂ) (z ^ (n + 2)) := by
  have hzc : z * (starRingEnd ℂ) z = 1 := mul_conj_eq_one_of_norm_eq_one hz
  have htel := fejerPartialPowerSum_mul_conj_sub_one hz n
  have hsucc := fejerPartialPowerSum_succ z n
  simp only [map_pow] at *
  rw [hsucc]
  linear_combination
    (starRingEnd ℂ) z ^ n * (starRingEnd ℂ) z * htel +
      z ^ n * (starRingEnd ℂ) z ^ n * (starRingEnd ℂ) z * hzc

/--
The Fejér kernel-square second-difference identity on the unit circle.

This is the complex counterpart of `sum_range_succ_mul_secondDiff`'s scalar telescope: unlike
the first difference `‖P_{k}‖² - ‖P_{k-1}‖²`, which accumulates a running sum, the *second*
difference of the kernel square collapses to the single term `2 · Re (z ^ (n + 2))`.
It supplies the second-difference identity used in the Fejér sum-of-squares decomposition.
-/
theorem normSq_fejerPartialPowerSum_secondDiff {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) :
    Complex.normSq (fejerPartialPowerSum z (n + 2)) -
          2 * Complex.normSq (fejerPartialPowerSum z (n + 1)) +
        Complex.normSq (fejerPartialPowerSum z n) =
      2 * (z ^ (n + 2)).re := by
  have h1 := normSq_fejerPartialPowerSum_succ hz n
  have h2 := normSq_fejerPartialPowerSum_succ hz (n + 1)
  have hcross := fejerPartialPowerSum_succ_mul_conj_pow_sub hz n
  have hre : ((starRingEnd ℂ) (z ^ (n + 2))).re = (z ^ (n + 2)).re := Complex.conj_re _
  have hcross_re := congrArg Complex.re hcross
  rw [Complex.sub_re, hre] at hcross_re
  rw [h2, h1]
  linarith only [hcross_re]

/-- Norm-square form of `normSq_fejerPartialPowerSum_secondDiff`. -/
theorem norm_sq_fejerPartialPowerSum_secondDiff {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) :
    ‖fejerPartialPowerSum z (n + 2)‖ ^ 2 - 2 * ‖fejerPartialPowerSum z (n + 1)‖ ^ 2 +
        ‖fejerPartialPowerSum z n‖ ^ 2 =
      2 * (z ^ (n + 2)).re := by
  simp only [← Complex.normSq_eq_norm_sq]
  exact normSq_fejerPartialPowerSum_secondDiff hz n

/--
The weighted discrete second-difference telescope on `Finset.range (K + 1)`.

For any real sequence, `Σ_{j=0}^K (j+1) Δ²a(j)` equals
`a(0) - (K+2)a(K+1) + (K+1)a(K+2)`. Induction cancels the interior first differences,
leaving only these endpoint terms.
-/
theorem sum_range_succ_mul_secondDiff (a : ℕ → ℝ) (K : ℕ) :
    (Finset.sum (Finset.range (K + 1)) fun j => ((j : ℝ) + 1) * (a j - 2 * a (j + 1) + a (j + 2))) =
      a 0 - ((K : ℝ) + 2) * a (K + 1) + ((K : ℝ) + 1) * a (K + 2) := by
  induction K with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, CharP.cast_eq_zero, one_mul]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/--
The predecessor kernel square, with the convention that the "square before `F 0`"
is `0`.

This packages the boundary case `F (-1) := 0` used by the general Fejér SOS identity
(`fejer_general_identity`) as an honest natural-number-indexed function, avoiding integer
indices entirely.
-/
noncomputable def fejerNormSqShift (z : ℂ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => ‖fejerPartialPowerSum z n‖ ^ 2

/-- `fejerNormSqShift` at `0` is `0` by definition. -/
theorem fejerNormSqShift_zero (z : ℂ) : fejerNormSqShift z 0 = 0 :=
  rfl

/-- `fejerNormSqShift` at `n + 1` is the kernel square at `n`, by definition. -/
theorem fejerNormSqShift_succ (z : ℂ) (n : ℕ) :
    fejerNormSqShift z (n + 1) = ‖fejerPartialPowerSum z n‖ ^ 2 :=
  rfl

/--
The uniform kernel-square second-difference identity, including the `K = 0` boundary case via
`fejerNormSqShift`.

This is the single lemma that lets the general Fejér SOS induction (`fejer_general_identity`)
treat `K = 0` and `K = n + 1` uniformly, instead of branching on the shape of `K`.
-/
theorem fejerNormSqShift_secondDiff {z : ℂ} (hz : ‖z‖ = 1) (K : ℕ) :
    ‖fejerPartialPowerSum z (K + 1)‖ ^ 2 - 2 * ‖fejerPartialPowerSum z K‖ ^ 2 +
        fejerNormSqShift z K =
      2 * (z ^ (K + 1)).re := by
  cases K with
  | zero =>
    rw [fejerNormSqShift_zero, norm_fejerPartialPowerSum_zero_sq,
      norm_fejerPartialPowerSum_one_sq hz];
    ring_nf
  | succ n =>
    rw [fejerNormSqShift_succ]; exact norm_sq_fejerPartialPowerSum_secondDiff hz n

/--
The general Fejér SOS (sum-of-squares) decomposition, without assuming any vanishing tail
`a (K + 1) = a (K + 2) = 0`.

For `‖z‖ = 1`, the boundary correction is
`a(K+1) * (2F(K) - F(K-1)) - a(K+2) * F(K)`, where
`F(j) = ‖Σ_{r=0}^j z^r‖²` and `F(-1) = 0` is represented by `fejerNormSqShift`.
Keeping both boundary squares makes the induction close using `fejerNormSqShift_secondDiff`.
-/
theorem fejer_general_identity {a : ℕ → ℝ} {z : ℂ} (hz : ‖z‖ = 1) (K : ℕ) :
    a 0 + 2 * (Finset.sum (Finset.Icc 1 K) fun k => (a k : ℂ) * z ^ k).re =
      (Finset.sum (Finset.range (K + 1)) fun j =>
            (a j - 2 * a (j + 1) + a (j + 2)) * ‖fejerPartialPowerSum z j‖ ^ 2) +
          a (K + 1) * (2 * ‖fejerPartialPowerSum z K‖ ^ 2 - fejerNormSqShift z K) -
        a (K + 2) * ‖fejerPartialPowerSum z K‖ ^ 2 := by
  induction K with
  | zero =>
    have hIcc : (Finset.Icc 1 0 : Finset ℕ) = ∅ := by decide
    have hrange :
      (Finset.sum (Finset.range 1) fun j =>
          (a j - 2 * a (j + 1) + a (j + 2)) * ‖fejerPartialPowerSum z j‖ ^ 2) =
        (a 0 - 2 * a 1 + a 2) * 1 := by
      rw [Finset.sum_range_one, norm_fejerPartialPowerSum_zero_sq]
    rw [hIcc, Finset.sum_empty, hrange, fejerNormSqShift_zero, norm_fejerPartialPowerSum_zero_sq,
      Complex.zero_re]
    ring
  | succ K
    ih =>
    have hstep :
      (Finset.sum (Finset.Icc 1 (K + 1)) fun k => (a k : ℂ) * z ^ k) =
        (Finset.sum (Finset.Icc 1 K) fun k => (a k : ℂ) * z ^ k) + (a (K + 1) : ℂ) * z ^ (K + 1) :=
      Finset.sum_Icc_succ_top (by omega) _
    have hsecond := fejerNormSqShift_secondDiff hz K
    have hsecond2 :
      a (K + 1) *
          (‖fejerPartialPowerSum z (K + 1)‖ ^ 2 - 2 * ‖fejerPartialPowerSum z K‖ ^ 2 +
            fejerNormSqShift z K) =
        a (K + 1) * (2 * (z ^ (K + 1)).re) := by
      rw [hsecond]
    have hre : ((a (K + 1) : ℂ) * z ^ (K + 1)).re = a (K + 1) * (z ^ (K + 1)).re := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [hstep, Complex.add_re, hre, Finset.sum_range_succ, fejerNormSqShift_succ]
    nlinarith [ih, hsecond2]

/--
The general Fejér SOS lower bound, without assuming a vanishing tail.

Nonnegativity of the interior second differences together with nonnegativity of the explicit
tail correction (in terms of `a (K + 1)`, `a (K + 2)` and the two boundary kernel squares) is
enough to conclude the sharp `-a 0 / 2` bound directly from `fejer_general_identity`, without any
hypothesis on `a (K + 1)` or `a (K + 2)` vanishing.
-/
theorem re_sum_ge_neg_half_head_of_fejer_general {a : ℕ → ℝ} {z : ℂ} {K : ℕ} (hz : ‖z‖ = 1)
    (hconv : ∀ j ∈ Finset.range (K + 1), 0 ≤ a j - 2 * a (j + 1) + a (j + 2))
    (htail :
      0 ≤
        a (K + 1) * (2 * ‖fejerPartialPowerSum z K‖ ^ 2 - fejerNormSqShift z K) -
          a (K + 2) * ‖fejerPartialPowerSum z K‖ ^ 2) :
    -(a 0 / 2) ≤ (Finset.sum (Finset.Icc 1 K) fun k => (a k : ℂ) * z ^ k).re := by
  have hid := fejer_general_identity (a := a) hz K
  have hinterior :
    0 ≤
      Finset.sum (Finset.range (K + 1)) fun j =>
        (a j - 2 * a (j + 1) + a (j + 2)) * ‖fejerPartialPowerSum z j‖ ^ 2 := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (hconv j hj) (sq_nonneg _)
  linarith only [hid, htail, hinterior]

/--
The affine-weight Fejér sum-of-squares lower bound on the unit circle, assuming `logP > 0`.

For the affine coefficient sequence `a k := logX - k * logP`, all interior second differences
vanish identically, so `fejer_general_identity` reduces to its tail term alone.  Writing
`logX = (K + θ) * logP` with `θ ∈ [0, 1]`, that tail term collapses to
`logP * ((1 - θ) * F (K - 1) + θ * F K)`, a positive scalar multiple of a convex combination
of two nonnegative kernel squares.
Thus the real part of the weighted sum is at least `-logX/2`, without a character assumption.
-/
theorem re_sum_logWeight_ge_neg_half {logX logP : ℝ} {θ : ℝ} {K : ℕ} {z : ℂ} (hz : ‖z‖ = 1)
    (hlogP : 0 < logP) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hlogX : logX = ((K : ℝ) + θ) * logP) :
    -((logX - 0 * logP) / 2) ≤
      (Finset.sum (Finset.Icc 1 K) fun k => ((logX - (k : ℝ) * logP : ℝ) : ℂ) * z ^ k).re := by
  set a : ℕ → ℝ := fun k => logX - (k : ℝ) * logP with ha
  have hconv : ∀ j ∈ Finset.range (K + 1), 0 ≤ a j - 2 * a (j + 1) + a (j + 2) := by
    intro j _
    simp only [ha]
    push_cast
    linarith only []
  have htail :
    0 ≤
      a (K + 1) * (2 * ‖fejerPartialPowerSum z K‖ ^ 2 - fejerNormSqShift z K) -
        a (K + 2) * ‖fejerPartialPowerSum z K‖ ^ 2 := by
    have haK1 : a (K + 1) = (θ - 1) * logP := by
      simp only [ha]; push_cast; linarith only [hlogX]
    have haK2 : a (K + 2) = (θ - 2) * logP := by
      simp only [ha]; push_cast; linarith only [hlogX]
    have hcombine :
      a (K + 1) * (2 * ‖fejerPartialPowerSum z K‖ ^ 2 - fejerNormSqShift z K) -
          a (K + 2) * ‖fejerPartialPowerSum z K‖ ^ 2 =
        logP * ((1 - θ) * fejerNormSqShift z K + θ * ‖fejerPartialPowerSum z K‖ ^ 2) := by
      rw [haK1, haK2]; ring
    rw [hcombine]
    have hshift_nonneg : 0 ≤ fejerNormSqShift z K := by
      cases K with
      | zero => rw [fejerNormSqShift_zero]
      | succ n =>
        rw [fejerNormSqShift_succ]; positivity
    positivity
  have hbound := re_sum_ge_neg_half_head_of_fejer_general (a := a) hz hconv htail
  simpa only [zero_mul, sub_zero, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_natCast,
    Complex.re_sum, Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.natCast_re,
    Complex.natCast_im, Complex.ofReal_im, mul_zero, Complex.sub_im, Complex.mul_im, add_zero,
    sub_self, ge_iff_le, ha, CharP.cast_eq_zero] using hbound

/--
The geometric-weight Fejér sum-of-squares lower bound on the unit circle.

For the coefficient sequence `a k := r ^ k - c` (`0 < r < 1`, `r ^ (K + 1) ≤ c ≤ r ^ K`), the
interior second differences are the geometric kernel `r ^ j * (1 - r) ^ 2 ≥ 0` for every `j`
(unlike the log case, they do not vanish, but they are termwise nonnegative). Regrouping the
`j = K` interior term together with the tail of `fejer_general_identity` collapses the boundary
contribution to `(r ^ K - c) * F K + (c - r ^ (K + 1)) * F (K - 1)`, a nonnegative combination
under the stated range hypothesis on `c`. Thus the real part of the weighted sum is at least
`-(1-c)/2`, without a character assumption.
-/
theorem re_sum_reciprocalWeight_ge_neg_half {r c : ℝ} {K : ℕ} {z : ℂ} (hz : ‖z‖ = 1) (hr0 : 0 < r)
    (hr1 : r < 1) (hc1 : r ^ (K + 1) ≤ c) (hc2 : c ≤ r ^ K) :
    -((1 - c) / 2) ≤ (Finset.sum (Finset.Icc 1 K) fun k => ((r ^ k - c : ℝ) : ℂ) * z ^ k).re := by
  set a : ℕ → ℝ := fun k => r ^ k - c with ha
  have hsecdiff : ∀ j, a j - 2 * a (j + 1) + a (j + 2) = r ^ j * (1 - r) ^ 2 := by
    intro j
    simp only [ha]
    ring
  have hid := fejer_general_identity (a := a) hz K
  have hrange_split :
    (Finset.sum (Finset.range (K + 1)) fun j =>
        (a j - 2 * a (j + 1) + a (j + 2)) * ‖fejerPartialPowerSum z j‖ ^ 2) =
      (Finset.sum (Finset.range K) fun j =>
          (a j - 2 * a (j + 1) + a (j + 2)) * ‖fejerPartialPowerSum z j‖ ^ 2) +
        (a K - 2 * a (K + 1) + a (K + 2)) * ‖fejerPartialPowerSum z K‖ ^ 2 :=
    Finset.sum_range_succ _ K
  have hcombine :
    (a K - 2 * a (K + 1) + a (K + 2)) * ‖fejerPartialPowerSum z K‖ ^ 2 +
          a (K + 1) * (2 * ‖fejerPartialPowerSum z K‖ ^ 2 - fejerNormSqShift z K) -
        a (K + 2) * ‖fejerPartialPowerSum z K‖ ^ 2 =
      (r ^ K - c) * ‖fejerPartialPowerSum z K‖ ^ 2 + (c - r ^ (K + 1)) * fejerNormSqShift z K := by
    simp only [ha]
    ring
  have hinterior_nonneg :
    0 ≤
      Finset.sum (Finset.range K) fun j =>
        (a j - 2 * a (j + 1) + a (j + 2)) * ‖fejerPartialPowerSum z j‖ ^ 2 := by
    apply Finset.sum_nonneg
    intro j _
    rw [hsecdiff]
    positivity
  have hshift_nonneg : 0 ≤ fejerNormSqShift z K := by
    cases K with
    | zero => rw [fejerNormSqShift_zero]
    | succ n =>
      rw [fejerNormSqShift_succ]; positivity
  have htail_nonneg :
    0 ≤
      (r ^ K - c) * ‖fejerPartialPowerSum z K‖ ^ 2 + (c - r ^ (K + 1)) * fejerNormSqShift z K := by
    have h1 : 0 ≤ r ^ K - c := by linarith
    have h2 : 0 ≤ c - r ^ (K + 1) := by linarith
    positivity
  have hRHS_nonneg :
    0 ≤
      (Finset.sum (Finset.range (K + 1)) fun j =>
            (a j - 2 * a (j + 1) + a (j + 2)) * ‖fejerPartialPowerSum z j‖ ^ 2) +
          a (K + 1) * (2 * ‖fejerPartialPowerSum z K‖ ^ 2 - fejerNormSqShift z K) -
        a (K + 2) * ‖fejerPartialPowerSum z K‖ ^ 2 := by
    rw [hrange_split]
    have := hcombine
    nlinarith [hinterior_nonneg, htail_nonneg, this]
  have ha0 : a 0 = 1 - c := by simp only [ha, pow_zero]
  rw [ha0] at hid
  have : 0 ≤ (1 - c) + 2 * (Finset.sum (Finset.Icc 1 K) fun k => (a k : ℂ) * z ^ k).re := by
    rw [hid]; exact hRHS_nonneg
  have hgoal : -((1 - c) / 2) ≤ (Finset.sum (Finset.Icc 1 K) fun k => (a k : ℂ) * z ^ k).re := by
    linarith
  simpa only [Complex.ofReal_sub, Complex.ofReal_pow, Complex.re_sum, Complex.mul_re,
    Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero,
    Finset.sum_sub_distrib, neg_le_sub_iff_le_add, ge_iff_le, ha] using hgoal

end PseudoPrime.AnalyticNumberTheory.Arithmetic
