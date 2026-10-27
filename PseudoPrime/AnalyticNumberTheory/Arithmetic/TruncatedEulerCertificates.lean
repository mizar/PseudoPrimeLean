/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalPowerBounds
public import PseudoPrime.Analysis.LogTaylorBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedMangoldtBounds

/-! # Rational certificates for finite Dirichlet prefixes and Euler bounds -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Check a positive rational input, a nonnegative Taylor displacement below one,
and containment of the rational upper Taylor endpoint. The power-of-two scale
uses the numerator bit length. The output certifies a real logarithm upper bound. -/
def rationalLogUpperCheck (N : ℚ) (terms : ℕ) (hi : ℚ) : Bool :=
  let j := Nat.log2 N.num.natAbs + 1
  let x := 1 - N / 2 ^ j
  decide
    (0 < N ∧
      0 ≤ x ∧
      x < 1 ∧
      (j : ℚ) * (6931471808 / 10000000000) - rationalLogSeries x terms + x ^ (terms + 1) / (1 - x) ≤
        hi)

/-- A successful upper-only logarithm check bounds the real logarithm by hi.
Use nonnegativity to remove the absolute value in the existing Taylor bound.
This supplies a kernel-computable scalar test for Euler-prefix certificates. -/
theorem rationalLogUpperCheck_sound {N hi : ℚ} {terms : ℕ}
    (h : rationalLogUpperCheck N terms hi = true) : Real.log (N : ℝ) ≤ (hi : ℝ) := by
  let j := Nat.log2 N.num.natAbs + 1
  let x := 1 - N / 2 ^ j
  have hc :
    0 < N ∧
      0 ≤ x ∧
      x < 1 ∧
      (j : ℚ) * (6931471808 / 10000000000) - rationalLogSeries x terms + x ^ (terms + 1) / (1 - x) ≤
        hi :=
    of_decide_eq_true h
  have hx : |1 - N / 2 ^ j| < 1 := by
    rw [show 1 - N / 2 ^ j = x from rfl, abs_of_nonneg hc.2.1]
    exact hc.2.2.1
  have hu := (rationalLogBounds_sound hc.1 j terms hx).2
  have he :
    rationalLogUpper N j terms =
      (j : ℚ) * (6931471808 / 10000000000) - rationalLogSeries x terms +
        x ^ (terms + 1) / (1 - x) := by
    simp only [rationalLogUpper, rationalLogRemainder, show 1 - N / 2 ^ j = x from rfl,
      abs_of_nonneg hc.2.1]
  rw [he] at hu
  exact hu.trans ((Rat.cast_le (K := ℝ)).mpr hc.2.2.2)

/-- For r>0, bounds for logarithmic prefix terms and both tail factors bound the
truncated numerator. Split off zero and compare nonnegative products.
This connects finite interval data to the analytic numerator cap. -/
theorem truncatedLogDirichletUpper_le_of_prefix {r : ℝ} (hr : 0 < r) (N : ℕ) (ell u : ℕ → ℝ)
    {ellN tail : ℝ} (hl : ∀ i ∈ Finset.range N, Real.log (i + 1 : ℕ) ≤ ell i)
    (hu : ∀ i ∈ Finset.range N, (i + 1 : ℕ) ^ (-r - 1) ≤ u i) (hN : Real.log N ≤ ellN)
    (ht : (N : ℝ) ^ (-r) ≤ tail) :
    truncatedLogDirichletUpper r N ≤
      (∑ i ∈ Finset.range N, ell i * u i) + tail * (ellN / r + r⁻¹ ^ 2) := by
  have hs :
    (∑ i ∈ Finset.range N, Real.log (i + 1 : ℕ) * (i + 1 : ℕ) ^ (-r - 1)) ≤
      ∑ i ∈ Finset.range N, ell i * u i := by
    refine Finset.sum_le_sum (fun i hi ↦ ?_)
    exact
      mul_le_mul (hl i hi) (hu i hi) (Real.rpow_nonneg (Nat.cast_nonneg (i + 1)) _)
        ((Real.log_natCast_nonneg (i + 1)).trans (hl i hi))
  have hbracket : Real.log N / r + r⁻¹ ^ 2 ≤ ellN / r + r⁻¹ ^ 2 :=
    add_le_add (div_le_div_of_nonneg_right hN hr.le) (le_refl _)
  have htail :=
    mul_le_mul ht hbracket
      (add_nonneg (div_nonneg (Real.log_natCast_nonneg N) hr.le) (sq_nonneg r⁻¹))
      ((Real.rpow_nonneg (Nat.cast_nonneg N) _).trans ht)
  unfold truncatedLogDirichletUpper
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, Real.log_zero, zero_mul, add_zero]
  exact add_le_add hs htail

/-- For r>0, lower prefix endpoints and a tail-power lower endpoint bound the
truncated denominator from below. Split off zero and sum inequalities.
This connects finite interval data to the analytic denominator floor. -/
theorem prefix_le_truncatedPowerDirichletLower {r : ℝ} (hr : 0 < r) (N : ℕ) (lo : ℕ → ℝ) {tail : ℝ}
    (hl : ∀ i ∈ Finset.range N, lo i ≤ (i + 1 : ℕ) ^ (-r - 1))
    (ht : tail ≤ ((N + 1 : ℕ) : ℝ) ^ (-r)) :
    (∑ i ∈ Finset.range N, lo i) + tail / r ≤ truncatedPowerDirichletLower r N := by
  have hs := Finset.sum_le_sum hl
  unfold truncatedPowerDirichletLower
  rw [Finset.sum_range_succ']
  rw [Nat.cast_zero, Real.zero_rpow (by linarith only [hr] : -r - 1 ≠ 0), add_zero]
  exact add_le_add hs (div_le_div_of_nonneg_right ht hr.le)

end PseudoPrime.Analysis

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For r>0,N>=3, a numerator cap a, positive denominator floor b and a<=cap*b
bound the full Euler series by cap. Compare positive ratios and the truncated bound.
This removes infinite sums from scalar certification. -/
theorem tsum_vonMangoldt_le_of_truncated_bounds {r a b cap : ℝ} (hr : 0 < r) {N : ℕ} (hN : 3 ≤ N)
    (ha : Analysis.truncatedLogDirichletUpper r N ≤ a)
    (hb : b ≤ Analysis.truncatedPowerDirichletLower r N) (hb0 : 0 < b) (hc : a ≤ cap * b) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r)) ≤ cap := by
  have ha0 := (Analysis.truncatedLogDirichletUpper_nonneg hr N).trans ha
  have hcap :=
    (div_le_div_of_nonneg_right ha (Analysis.truncatedPowerDirichletLower_pos hr N).le).trans
      (div_le_div_of_nonneg_left ha0 hb0 hb)
  exact (tsum_vonMangoldt_le_truncatedEuler hr hN).trans (hcap.trans ((div_le_iff₀ hb0).mpr hc))

end PseudoPrime.AnalyticNumberTheory.Arithmetic

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Check positive rational base, nonnegative endpoints, nonzero natural denominator
and two integer-power inequalities. A true result certifies a negative rational
real-power interval through the soundness theorem. -/
def rationalPowerIntervalCheck (b lo hi : ℚ) (p d : ℕ) : Bool :=
  decide (0 < b ∧ 0 ≤ lo ∧ 0 ≤ hi ∧ d ≠ 0 ∧ lo ^ d * b ^ p ≤ 1 ∧ 1 ≤ hi ^ d * b ^ p)

/-- A successful power check encloses b^(-p/d) in the proposed real interval.
Cast the rational inequalities and apply integer-power endpoint certification.
This turns exact rational computations into analytic inequalities. -/
theorem rationalPowerIntervalCheck_sound {b lo hi : ℚ} {p d : ℕ}
    (h : rationalPowerIntervalCheck b lo hi p d = true) :
    (b : ℝ) ^ (-(p : ℝ) / (d : ℝ)) ∈ Set.Icc (lo : ℝ) (hi : ℝ) := by
  have hc : 0 < b ∧ 0 ≤ lo ∧ 0 ≤ hi ∧ d ≠ 0 ∧ lo ^ d * b ^ p ≤ 1 ∧ 1 ≤ hi ^ d * b ^ p :=
    of_decide_eq_true h
  have hl := (Rat.cast_le (K := ℝ)).mpr hc.2.2.2.2.1
  have hu := (Rat.cast_le (K := ℝ)).mpr hc.2.2.2.2.2
  simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_one] at hl hu
  exact
    Analysis.negRationalPower_mem_Icc ((Rat.cast_pos (K := ℝ)).mpr hc.1)
      ((Rat.cast_nonneg (K := ℝ)).mpr hc.2.1) ((Rat.cast_nonneg (K := ℝ)).mpr hc.2.2.1) p hc.2.2.2.1
      hl hu

/-- Check a logarithm upper endpoint and a power interval for a natural base n.
The exponent is -(p+d)/d. A true result supplies one finite term of an Euler certificate. -/
def rationalEulerTermCheck (p d terms n : ℕ) (ell lo hi : ℚ) : Bool :=
  Analysis.rationalLogUpperCheck n terms ell && rationalPowerIntervalCheck n lo hi (p + d) d

/-- For nonzero d, a successful term check bounds log(n) above and n^(-p/d-1)
from both sides. Combine scalar soundness and normalize the exponent.
This supplies the real prefix inequalities consumed by Euler certification. -/
theorem rationalEulerTermCheck_sound {p d terms n : ℕ} {ell lo hi : ℚ} (hd : d ≠ 0)
    (h : rationalEulerTermCheck p d terms n ell lo hi = true) :
    Real.log (n : ℝ) ≤ (ell : ℝ) ∧
      (lo : ℝ) ≤ (n : ℝ) ^ (-(p : ℝ) / (d : ℝ) - 1) ∧
      (n : ℝ) ^ (-(p : ℝ) / (d : ℝ) - 1) ≤ (hi : ℝ) := by
  have hchecks := Bool.and_eq_true_iff.mp h
  have hl := Analysis.rationalLogUpperCheck_sound hchecks.1
  have hp := rationalPowerIntervalCheck_sound hchecks.2
  have he : -((p + d : ℕ) : ℝ) / (d : ℝ) = -(p : ℝ) / (d : ℝ) - 1 := by
    simp only [Nat.cast_add, neg_add, add_div, neg_div,
      div_self (Nat.cast_ne_zero.mpr hd : (d : ℝ) ≠ 0), sub_eq_add_neg]
  rw [he] at hp
  simpa only [Rat.cast_natCast, Set.mem_Icc] using And.intro hl hp

end PseudoPrime.AnalyticNumberTheory.Arithmetic

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Compute the rational numerator cap from prefix endpoints and tail endpoints
at gap p/d and cutoff N. Soundness checks the supporting scalar intervals.
This preserves the exact integral-tail formula. -/
def rationalEulerNumerator (p d N : ℕ) (ell u : ℕ → ℚ) (ellN tail : ℚ) : ℚ :=
  (∑ i ∈ Finset.range N, ell i * u i) +
    tail * (ellN / ((p : ℚ) / (d : ℚ)) + (((p : ℚ) / (d : ℚ))⁻¹) ^ 2)

/-- Compute the rational denominator floor from prefix lower endpoints and a tail
lower endpoint at gap p/d and cutoff N. The checker requires a positive result.
This preserves the exact integral-tail formula. -/
def rationalEulerDenominator (p d N : ℕ) (lo : ℕ → ℚ) (tail : ℚ) : ℚ :=
  (∑ i ∈ Finset.range N, lo i) + tail / ((p : ℚ) / (d : ℚ))

/-- Check gap p/d>0, N>=3, every prefix interval, both tail intervals, a positive
denominator and the proposed cap inequality. A true result certifies the full Euler
series using only exact rational arithmetic. -/
def rationalEulerIntervalCheck (p d N terms : ℕ) (ell lo u : ℕ → ℚ) (ellN tailU tailL cap : ℚ) :
    Bool :=
  decide
    (0 < p ∧
      d ≠ 0 ∧
      3 ≤ N ∧
      (∀ i ∈ Finset.range N, rationalEulerTermCheck p d terms (i + 1) (ell i) (lo i) (u i) = true) ∧
      Analysis.rationalLogUpperCheck N terms ellN = true ∧
      rationalPowerIntervalCheck N 0 tailU p d = true ∧
      rationalPowerIntervalCheck (N + 1) tailL 1 p d = true ∧
      0 < rationalEulerDenominator p d N lo tailL ∧
      rationalEulerNumerator p d N ell u ellN tailU ≤ cap * rationalEulerDenominator p d N lo tailL)

/-- A successful certificate bounds the full Mangoldt Euler series at 1+p/d.
Extract scalar intervals, sum prefixes, retain integral tails and compare positive ratios.
No GRH, character or modulus assumptions are needed. -/
theorem rationalEulerIntervalCheck_sound {p d N terms : ℕ} {ell lo u : ℕ → ℚ}
    {ellN tailU tailL cap : ℚ}
    (h : rationalEulerIntervalCheck p d N terms ell lo u ellN tailU tailL cap = true) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + (p : ℝ) / (d : ℝ))) ≤
      (cap : ℝ) := by
  have hc :
    0 < p ∧
      d ≠ 0 ∧
      3 ≤ N ∧
      (∀ i ∈ Finset.range N, rationalEulerTermCheck p d terms (i + 1) (ell i) (lo i) (u i) = true) ∧
      Analysis.rationalLogUpperCheck N terms ellN = true ∧
      rationalPowerIntervalCheck N 0 tailU p d = true ∧
      rationalPowerIntervalCheck (N + 1) tailL 1 p d = true ∧
      0 < rationalEulerDenominator p d N lo tailL ∧
      rationalEulerNumerator p d N ell u ellN tailU ≤
        cap * rationalEulerDenominator p d N lo tailL :=
    of_decide_eq_true h
  rcases hc with ⟨hp, hd, hN, hterm, hlog, htu, htl, hB, hC⟩
  have hr : 0 < (p : ℝ) / (d : ℝ) :=
    div_pos (Nat.cast_pos.mpr hp) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd))
  have ht i hi := rationalEulerTermCheck_sound hd (hterm i hi)
  simp only [neg_div] at ht
  have hlogR := Analysis.rationalLogUpperCheck_sound hlog
  have htuR := (rationalPowerIntervalCheck_sound htu).2
  have htlR := (rationalPowerIntervalCheck_sound htl).1
  simp only [Rat.cast_natCast, neg_div] at hlogR htuR htlR
  have ha :=
    Analysis.truncatedLogDirichletUpper_le_of_prefix hr N (fun i ↦ (ell i : ℝ)) (fun i ↦ (u i : ℝ))
      (fun i hi ↦ (ht i hi).1) (fun i hi ↦ (ht i hi).2.2) hlogR htuR
  have htlFinal : (tailL : ℝ) ≤ ((N + 1 : ℕ) : ℝ) ^ (-((p : ℝ) / (d : ℝ))) := by
    simpa only [Rat.cast_add, Rat.cast_natCast, Rat.cast_one, Nat.cast_add, Nat.cast_one] using htlR
  have hb :=
    Analysis.prefix_le_truncatedPowerDirichletLower hr N (fun i ↦ (lo i : ℝ))
      (fun i hi ↦ (ht i hi).2.1) htlFinal
  have ha' :
    Analysis.truncatedLogDirichletUpper ((p : ℝ) / (d : ℝ)) N ≤
      (rationalEulerNumerator p d N ell u ellN tailU : ℝ) := by
    simpa only [rationalEulerNumerator, Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_pow, Rat.cast_inv] using ha
  have hb' :
    (rationalEulerDenominator p d N lo tailL : ℝ) ≤
      Analysis.truncatedPowerDirichletLower ((p : ℝ) / (d : ℝ)) N := by
    simpa only [rationalEulerDenominator, Rat.cast_add, Rat.cast_sum, Rat.cast_div,
      Rat.cast_natCast] using hb
  have hBR := (Rat.cast_pos (K := ℝ)).mpr hB
  have hCR := (Rat.cast_le (K := ℝ)).mpr hC
  rw [Rat.cast_mul] at hCR
  exact tsum_vonMangoldt_le_of_truncated_bounds hr hN ha' hb' hBR hCR

end PseudoPrime.AnalyticNumberTheory.Arithmetic
