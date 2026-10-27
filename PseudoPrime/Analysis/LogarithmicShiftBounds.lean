/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Rational coefficients for shifted logarithmic cutoffs

The coefficients a,b,c are rational, with positive a in the comparison theorems.
Signed corrections can lower the pointwise bound. Root positivity and an explicit
lower bound on b give a common monotonicity condition for finite envelopes.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For real logarithmic input L and rational b,c, define L+b log L+c.
The coefficients may have either sign. This is the root of the shifted squared cutoff. -/
noncomputable def logarithmicShiftRoot (L : ℝ) (b c : ℚ) : ℝ :=
  L + (b : ℝ) * Real.log L + (c : ℝ)

/-- If 0 < L₁ ≤ L₂ and b ≥ -L₁, the shifted root at L₁ is at most its value
at L₂, with rational b,c of arbitrary sign. Bound log(L₂/L₁) by L₂/L₁-1
and multiply by the lower bound on b. This controls monotonicity without derivatives. -/
theorem logarithmicShiftRoot_le_of_le {L₁ L₂ : ℝ} {b c : ℚ} (hL : 0 < L₁) (horder : L₁ ≤ L₂)
    (hb : -L₁ ≤ (b : ℝ)) : logarithmicShiftRoot L₁ b c ≤ logarithmicShiftRoot L₂ b c := by
  have hL₂ : 0 < L₂ := hL.trans_le horder
  have hlog := Real.log_le_log hL horder
  have hd : 0 ≤ Real.log L₂ - Real.log L₁ := sub_nonneg.mpr hlog
  have ht := Real.log_le_sub_one_of_pos (div_pos hL₂ hL)
  rw [Real.log_div hL₂.ne' hL.ne'] at ht
  have hmul := mul_le_mul_of_nonneg_right ht hL.le
  have he : (L₂ / L₁ - 1) * L₁ = L₂ - L₁ := by rw [sub_mul, div_mul_cancel₀ _ hL.ne', one_mul]
  rw [he] at hmul
  have hbmul := mul_le_mul_of_nonneg_right hb hd
  dsimp only [logarithmicShiftRoot]
  nlinarith only [hmul, hbmul]

/-- On the monotonicity range, a nonnegative root at the lower endpoint
makes its square nondecreasing. Apply root monotonicity and the square comparison.
This permits the same pointwise expression for a finite-maximum envelope. -/
theorem logarithmicShiftRoot_sq_le_of_le {L₁ L₂ : ℝ} {b c : ℚ} (hL : 0 < L₁) (horder : L₁ ≤ L₂)
    (hb : -L₁ ≤ (b : ℝ)) (hroot : 0 ≤ logarithmicShiftRoot L₁ b c) :
    logarithmicShiftRoot L₁ b c ^ 2 ≤ logarithmicShiftRoot L₂ b c ^ 2 := by
  have h := logarithmicShiftRoot_le_of_le (c := c) hL horder hb
  exact (sq_le_sq₀ hroot (hroot.trans h)).mpr h

/-- For L > 0 and nonnegative shifted root, a strictly negative correction
b log L+c makes the shifted square smaller than L². Compare the nonnegative roots.
This verifies an improvement over the pure logarithmic square. -/
theorem logarithmicShiftRoot_sq_lt_log_sq {L : ℝ} {b c : ℚ} (hL : 0 < L)
    (hroot : 0 ≤ logarithmicShiftRoot L b c) (hcorr : (b : ℝ) * Real.log L + (c : ℝ) < 0) :
    logarithmicShiftRoot L b c ^ 2 < L ^ 2 := by
  apply (sq_lt_sq₀ hroot hL.le).mpr
  dsimp only [logarithmicShiftRoot]
  linarith only [hcorr]

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- For real logarithmic input L and rational a,b,c, define a(L+b log L+c)².
Witness bounds use a > 0; b,c may have either sign.
This common numerical expression is independent of any primality test. -/
noncomputable def logarithmicShiftCutoff (L : ℝ) (a b c : ℚ) : ℝ :=
  (a : ℝ) * logarithmicShiftRoot L b c ^ 2

/-- For rational a > 0, a nonnegative lower root and b ≥ -L₁, the shifted
cutoff is nondecreasing from L₁ to L₂. Multiply the squared-root comparison by a.
This keeps the pointwise and finite-maximum bounds at the same formula. -/
theorem logarithmicShiftCutoff_le_of_le {L₁ L₂ : ℝ} {a b c : ℚ} (ha : 0 < a) (hL : 0 < L₁)
    (horder : L₁ ≤ L₂) (hb : -L₁ ≤ (b : ℝ)) (hroot : 0 ≤ logarithmicShiftRoot L₁ b c) :
    logarithmicShiftCutoff L₁ a b c ≤ logarithmicShiftCutoff L₂ a b c := by
  exact
    mul_le_mul_of_nonneg_left (logarithmicShiftRoot_sq_le_of_le hL horder hb hroot)
      (by exact_mod_cast ha.le : (0 : ℝ) ≤ a)

/-- A rational logarithmic witness profile consists of a positive leading
coefficient a, signed coefficients b,c and a natural starting value N.
Each field specifies the formula a(log n+b log log n+c)² or its entrance n ≥ N.
Analytic consumers attach a proof for the particular coefficient-and-start pair. -/
structure RationalLogarithmicProfile where
  /-- The leading rational coefficient a. -/
  coefficient : ℚ
  /-- The signed rational log-log coefficient b. -/
  loglogCoefficient : ℚ
  /-- The signed rational constant correction c. -/
  constant : ℚ
  /-- The required strict positivity of a. -/
  coefficient_pos : 0 < coefficient
  /-- The natural input entrance N for this coefficient triple. -/
  startingValue : ℕ

/-- Evaluate the rational profile at a natural input n by casting its
coefficients to real numbers and applying the common shifted logarithmic cutoff.
The starting value is a separate applicability condition in each witness theorem.
This preserves the chosen coefficient-and-start pair when composing consumers. -/
noncomputable def RationalLogarithmicProfile.cutoff (profile : RationalLogarithmicProfile) (n : ℕ) :
    ℝ :=
  logarithmicShiftCutoff (Real.log n) profile.coefficient profile.loglogCoefficient profile.constant

end PseudoPrime.Analysis
