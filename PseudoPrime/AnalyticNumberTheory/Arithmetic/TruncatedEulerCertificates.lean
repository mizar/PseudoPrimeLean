/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalPowerBounds
public import PseudoPrime.Analysis.LogTaylorBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedMangoldtBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3

/-! # Rational certificates for finite Dirichlet prefixes and Euler bounds -/

@[expose] public section

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
