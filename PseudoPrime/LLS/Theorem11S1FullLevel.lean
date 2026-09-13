/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.LLS.Lemma23
import PseudoPrime.LLS.Numerics

/-! # Shared full-level interfaces and numerical comparison for LLS S1

These bounds are independent of quadraticity and are used by both analytic routes.
-/

namespace PseudoPrime.LLS

/--
The raw reciprocal-sum-preserving interface: the primitive reciprocal-weighted sum's real
part, kept unconsumed, bounds the zero-mass witness `b` at the conductor scale.
-/
def LLSPart1PrimitiveReciprocalExplicitFormulaRawAt {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℝ) :
    Prop :=
  let y := llsTheorem11S1RadiusRoot q
  let x := y ^ 2
  (1 - 1 / y) ^ 2 * b ≤
    1 / 2 * (1 - 1 / x) * Real.log ((χ.conductor : ℝ) / Real.pi) -
      (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x
          χ.primitiveCharacter).re -
      1 / 4

/--
The full-level zero-mass raw upper bound: `A(q)`'s conductor correction has already been absorbed
into the level `q` via the conductor estimate, leaving no free-standing quotient term.
-/
def LLSPart1PrimitiveZeroMassFullLevelRawAt {q : ℕ} (_χ : DirichletCharacter ℂ q) (b : ℝ) : Prop :=
  let y := llsTheorem11S1RadiusRoot q
  let x := y ^ 2
  (1 - 1 / y) ^ 2 * b ≤
    1 / 2 * (1 - 1 / x) * Real.log ((q : ℝ) / Real.pi) - llsAuxiliaryTerm q - 1 / 4

/-- The full-level upper bound for the original character's logarithmic weighted sum obtained by
the exact conductor-absorption route: both the Lemma 2.3 zero-mass witness bound and the
Lemma 2.2 conductor term have already been absorbed into the level `q`, leaving no free-standing
conductor or quotient term. Distinct from `Numerics.lean`'s `llsPart1FullLevelUpperBound`, which
uses the coarser `WithQuotient` route. -/
noncomputable def llsPart1PrimitiveFullLevelUpperBound (q : ℕ) : ℝ :=
  let y := llsTheorem11S1RadiusRoot q
  let x := y ^ 2
  (2 * y + 2 + Real.log x) / (1 - 1 / y) ^ 2 *
        (1 / 2 * (1 - 1 / x) * (Real.log q - Real.log Real.pi) - llsAuxiliaryTerm q - 1 / 4) +
      1 / 2 * (Real.log q - Real.log Real.pi) * Real.log x -
    11 / 4

/--
Input/assumptions: `q ≥ 3000`.
Conclusion: `llsPart1PrimitiveFullLevelUpperBound q ≤ llsPart1FullLevelUpperBound q`.
Content: writing `y := llsTheorem11S1RadiusRoot q`, `L := log q`, `P := log π`, `A := A(q)`, both
bounds
share the tail term `(1/2)(L - P) log(y²) - 11/4` exactly, so it suffices to compare the two
`C(y) := 2y + 2 + log(y²) ≥ 0`-weighted zero-mass terms: `[(1/2)(1 - 1/y²)(L - P) - A - 1/4] /
(1 - 1/y)² ≤ L/2 + 2/5 - A`. Clearing both denominators (multiplying by `(1-1/y)² · y² > 0`)
reduces this to a polynomial inequality. Multiplying the cleared gap by `20` gives
`40Ay - 20A - 20Ly + 20L + 10Py² - 10P + 13y² - 16y + 8 ≥ 0`; bounding each cross term termwise via
`A ≥ 0` (`llsAuxiliaryTerm_nonneg`), `L ≤ y` (`llsCorrectionTerm_nonneg`), `P ≥ 1`
(`Real.log_three_gt_d9` via `Real.strictMonoOn_log`), and `y ≥ 8`
(`eight_lt_llsTheorem11S1RadiusRoot`) reduces it to `3y² + 4y - 2 ≥ 0`, immediate from `y ≥ 8`.
Role: connects the shared full-level bound to the level-indexed numerical chain.
-/
theorem llsPart1PrimitiveFullLevelUpperBound_le_fullLevel {q : ℕ} (hq : 3000 ≤ q) :
    llsPart1PrimitiveFullLevelUpperBound q ≤ llsPart1FullLevelUpperBound q := by
  have hy8 : (8 : ℝ) < llsTheorem11S1RadiusRoot q := eight_lt_llsTheorem11S1RadiusRoot hq
  have hypos : (0 : ℝ) < llsTheorem11S1RadiusRoot q := by linarith
  have hlevel : Real.log q ≤ llsTheorem11S1RadiusRoot q :=
    le_add_of_nonneg_right (llsCorrectionTerm_nonneg q)
  have haux : (0 : ℝ) ≤ llsAuxiliaryTerm q := llsAuxiliaryTerm_nonneg q
  have hlogPi : (1 : ℝ) ≤ Real.log Real.pi := by
    have hlogThreePi : Real.log 3 < Real.log Real.pi :=
      Real.strictMonoOn_log
        (by
          change (0 : ℝ) < 3
          norm_num only)
        Real.pi_pos Real.pi_gt_three
    linarith [Real.log_three_gt_d9]
  have hinv2pos : (0 : ℝ) < (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 := by
    have : (0 : ℝ) < 1 - 1 / llsTheorem11S1RadiusRoot q := by
      rw [sub_pos, div_lt_one hypos]; linarith
    positivity
  have hxpos : (0 : ℝ) < (llsTheorem11S1RadiusRoot q) ^ 2 := by positivity
  have hkey_cleared :
    1 / 2 * ((llsTheorem11S1RadiusRoot q) ^ 2 - 1) * (Real.log q - Real.log Real.pi) -
        llsAuxiliaryTerm q * (llsTheorem11S1RadiusRoot q) ^ 2 -
        (llsTheorem11S1RadiusRoot q) ^ 2 / 4 ≤
      (llsTheorem11S1RadiusRoot q - 1) ^ 2 * (Real.log q / 2 + 2 / 5 - llsAuxiliaryTerm q) := by
    nlinarith [mul_nonneg haux (show (0 : ℝ) ≤ 2 * llsTheorem11S1RadiusRoot q - 1 by linarith),
      mul_nonneg (show (0 : ℝ) ≤ llsTheorem11S1RadiusRoot q - 1 by linarith)
        (show (0 : ℝ) ≤ llsTheorem11S1RadiusRoot q - Real.log q by linarith),
      mul_nonneg (show (0 : ℝ) ≤ Real.log Real.pi - 1 by linarith)
        (show (0 : ℝ) ≤ (llsTheorem11S1RadiusRoot q) ^ 2 - 1
          by
          have hsq :=
            mul_self_le_mul_self (show (0 : ℝ) ≤ 1 by norm_num only)
              (le_trans (by norm_num only) hy8.le)
          calc
            (0 : ℝ) ≤ 1 * 1 - 1 := by norm_num only
            _ ≤ llsTheorem11S1RadiusRoot q * llsTheorem11S1RadiusRoot q - 1 :=
              sub_le_sub_right hsq 1
            _ = (llsTheorem11S1RadiusRoot q) ^ 2 - 1 := by ring),
      mul_nonneg (show (0 : ℝ) ≤ llsTheorem11S1RadiusRoot q - 8 by linarith)
        (show (0 : ℝ) ≤ llsTheorem11S1RadiusRoot q - 8 by linarith)]
  have hyne : llsTheorem11S1RadiusRoot q ≠ 0 := hypos.ne'
  have hkey :
    1 / 2 * (1 - 1 / (llsTheorem11S1RadiusRoot q) ^ 2) * (Real.log q - Real.log Real.pi) -
        llsAuxiliaryTerm q -
        1 / 4 ≤
      (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 * (Real.log q / 2 + 2 / 5 - llsAuxiliaryTerm q) := by
    have hscaled :=
      mul_le_mul_of_nonneg_right hkey_cleared
        (show (0 : ℝ) ≤ 1 / (llsTheorem11S1RadiusRoot q) ^ 2 by positivity)
    have heq1 :
      (1 / 2 * ((llsTheorem11S1RadiusRoot q) ^ 2 - 1) * (Real.log q - Real.log Real.pi) -
            llsAuxiliaryTerm q * (llsTheorem11S1RadiusRoot q) ^ 2 -
            (llsTheorem11S1RadiusRoot q) ^ 2 / 4) *
          (1 / (llsTheorem11S1RadiusRoot q) ^ 2) =
        1 / 2 * (1 - 1 / (llsTheorem11S1RadiusRoot q) ^ 2) * (Real.log q - Real.log Real.pi) -
          llsAuxiliaryTerm q -
          1 / 4 := by
      field_simp
    have heq2 :
      ((llsTheorem11S1RadiusRoot q - 1) ^ 2 * (Real.log q / 2 + 2 / 5 - llsAuxiliaryTerm q)) *
          (1 / (llsTheorem11S1RadiusRoot q) ^ 2) =
        (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 *
          (Real.log q / 2 + 2 / 5 - llsAuxiliaryTerm q) := by
      field_simp
    rw [heq1, heq2] at hscaled
    exact hscaled
  have hC22nonneg :
    (0 : ℝ) ≤ 2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2) := by
    have hsq := mul_self_le_mul_self (show (0 : ℝ) ≤ 8 by norm_num only) hy8.le
    have hx64 : (64 : ℝ) ≤ (llsTheorem11S1RadiusRoot q) ^ 2 := by
      calc
        (64 : ℝ) = 8 * 8 := by norm_num only
        _ ≤ llsTheorem11S1RadiusRoot q * llsTheorem11S1RadiusRoot q := hsq
        _ = (llsTheorem11S1RadiusRoot q) ^ 2 := by ring
    have hlogxnn : (0 : ℝ) ≤ Real.log ((llsTheorem11S1RadiusRoot q) ^ 2) :=
      Real.log_nonneg (le_trans (by norm_num only) hx64)
    have hy_nonneg : (0 : ℝ) ≤ llsTheorem11S1RadiusRoot q := hypos.le
    have hfirst : (0 : ℝ) ≤ 2 * llsTheorem11S1RadiusRoot q + 2 :=
      add_nonneg (mul_nonneg (by norm_num only) hy_nonneg) (by norm_num only)
    exact add_nonneg hfirst hlogxnn
  have hkeydiv :
    (1 / 2 * (1 - 1 / (llsTheorem11S1RadiusRoot q) ^ 2) * (Real.log q - Real.log Real.pi) -
          llsAuxiliaryTerm q -
          1 / 4) /
        (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 ≤
      Real.log q / 2 + 2 / 5 - llsAuxiliaryTerm q :=
    (div_le_iff₀ hinv2pos).mpr
      (by
        calc
          _ =
              1 / 2 * (1 - 1 / (llsTheorem11S1RadiusRoot q) ^ 2) * (Real.log q - Real.log Real.pi) -
                llsAuxiliaryTerm q -
                1 / 4 :=
            by ring
          _ ≤
              (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 *
                (Real.log q / 2 + 2 / 5 - llsAuxiliaryTerm q) :=
            hkey
          _ = _ := by ring)
  have hmul := mul_le_mul_of_nonneg_left hkeydiv hC22nonneg
  have hmuleq :
    (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) *
        ((1 / 2 * (1 - 1 / (llsTheorem11S1RadiusRoot q) ^ 2) * (Real.log q - Real.log Real.pi) -
            llsAuxiliaryTerm q -
            1 / 4) /
          (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2) =
      (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) /
          (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 *
        (1 / 2 * (1 - 1 / (llsTheorem11S1RadiusRoot q) ^ 2) * (Real.log q - Real.log Real.pi) -
          llsAuxiliaryTerm q -
          1 / 4) := by
    ring
  rw [hmuleq] at hmul
  unfold llsPart1PrimitiveFullLevelUpperBound llsPart1FullLevelUpperBound
  linarith [hmul]

end PseudoPrime.LLS
