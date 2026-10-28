/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalPowerBounds
public import PseudoPrime.Analysis.LogTaylorBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedMangoldtBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates2

/-! # Rational certificates for finite Dirichlet prefixes and Euler bounds -/

@[expose] public section

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
