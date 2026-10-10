/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.XiEndpointNormNumerics
public import PseudoPrime.LLS.LogLValueBounds
public import PseudoPrime.LLS.LogCorrectionBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactorLogCost

/-! # Logarithmic character bounds for the coset comparison

Combine the primitive explicit formula, its endpoint estimate, and the
level-change error with the ambient modulus in the coset theorem.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For ambient modulus at least `64`, its logarithmic ratio to pi is at least
three. Use the certified logarithms of two and three and the tangent bound
at three for pi. This permits the ambient endpoint estimate for small moduli. -/
private theorem three_le_log_ambient_div_pi {q : ℕ} (hq : 64 ≤ q) :
    3 ≤ Real.log ((q : ℝ) / Real.pi) := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num only) hq)
  have hq64 : (64 : ℝ) ≤ q := Nat.cast_le.mpr hq
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 64) hq64
  have h64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num only, Real.log_pow]
    norm_num only
  rw [h64] at hl
  have hpi :=
    PseudoPrime.Analysis.log_le_log_add_sub_div (a := (3 : ℝ)) (by norm_num only) Real.pi_pos
  have hpile : Real.pi ≤ (22 / 7 : ℝ) := Real.pi_lt_d4.le.trans (by norm_num only)
  rw [Real.log_div hq0.ne' Real.pi_pos.ne']
  linarith only [hl, hpi, hpile, Real.log_two_gt_d9, Real.log_three_lt_d9]

/-- Under GRH, for a character of modulus at least `64`, conductor at least
three, and cutoff greater than one, the primitive norm estimate has an explicit
endpoint coefficient `(2/3) log(q/pi) + 4` in terms of the ambient modulus.
Multiply the endpoint bound by the positive cutoff logarithm and retain the
primitive zero mass, parity correction, and level-change error.
This supplies the endpoint substitution toward equation (4.8). -/
theorem norm_characterLogWeightedSum_le_ambient_explicit {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hq : 64 ≤ q) (hc : 3 ≤ χ.conductor)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ‖ ≤
      |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| *
          (2 * Real.sqrt x + 2) +
        ((2 / 3 : ℝ) * Real.log ((q : ℝ) / Real.pi) + 4) * Real.log x +
        |Real.log ((χ.conductor : ℝ) / Real.pi) * Real.log x / 2 +
            logCorrection χ.primitiveCharacter x| +
        (1 / 2 : ℝ) * (q / χ.conductor).primeFactors.card * (Real.log x) ^ 2 := by
  have hs := norm_characterLogWeightedSum_le_primitive_explicit χ hc hGRH hx
  have hb :=
    norm_logDeriv_xi_zero_le_log_ambient_of_log_lower_bound (three_le_log_ambient_div_pi hq) hc
      (Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level)
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) hGRH
  have hm := mul_le_mul_of_nonneg_right hb (Real.log_pos hx).le
  linarith only [hs, hm]

/-- For cutoffs at least `1000`, either parity's reciprocal correction is at
most `-2/7`. The lower Euler-constant certificate controls the odd case; the
square-root logarithm bound absorbs the even remainder.
This supplies the signed correction used to remove zero mass in the coset bound. -/
theorem reciprocalCorrection_le_neg_two_sevenths {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 1000 ≤ x) : reciprocalCorrection χ x ≤ -(2 / 7 : ℝ) := by
  have hx100 : (100 : ℝ) ≤ x := (by norm_num only : (100 : ℝ) ≤ 1000).trans hx
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1000) hx
  by_cases he : χ (-1) = 1
  · rw [reciprocalCorrection, ite_eq_left he]
    have h := reciprocalCorrectionEven_bounds x hx100
    have hs := sqrt_log_cutoff_bounds x hx100
    have hss := mul_nonneg (Real.sqrt_nonneg x) (sub_nonneg.mpr hs.1)
    rw [mul_sub, ← pow_two, Real.sq_sqrt hx0.le] at hss
    have hr : (Real.log x + 1 + Real.eulerMascheroniConstant / 2) / x ≤ 2 / 25 := by
      apply (div_le_iff₀ hx0).mpr
      nlinarith only [hs.2.2, hss, hx, Real.eulerMascheroniConstant_lt_two_thirds]
    nlinarith only [h.2, hr, Real.log_two_gt_d9,
      Analysis.twentyThree_fortieths_lt_eulerMascheroniConstant]
  · rw [reciprocalCorrection, ite_eq_right he]
    have h := reciprocalCorrectionOdd_bounds x hx100
    have hr : (Real.log 2 + Real.eulerMascheroniConstant / 2) / x ≤ 31 / 30000 := by
      apply (div_le_iff₀ hx0).mpr
      nlinarith only [hx, Real.log_two_lt_d9, Real.eulerMascheroniConstant_lt_two_thirds]
    nlinarith only [h.2, hr, Analysis.twentyThree_fortieths_lt_eulerMascheroniConstant]

/-- For `s ≥ 100`, the reciprocal square factor absorbs the logarithmic
mass coefficient. Clearing the positive square denominator reduces the bound
to a quadratic polynomial. This gives the coefficient `19/6` in the coset estimate. -/
private theorem logarithmic_mass_coefficient_le {s : ℝ} (hs : 100 ≤ s) :
    s + 1 ≤ (1 - 1 / s) ^ 2 * (s + 19 / 6) := by
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num only) hs
  have h := mul_nonneg (sub_nonneg.mpr hs) (add_nonneg hs0.le (by norm_num only : (0 : ℝ) ≤ 68))
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hs0)).mp
  field_simp (disch := exact hs0.ne')
  rw [mul_assoc, mul_div_cancel_left₀ _ hs0.ne']
  nlinarith only [h]

/-- Under GRH, for a primitive character of level at least three and cutoff
at least `10000`, the logarithmic zero-mass contribution is bounded by a reciprocal
character sum with coefficient `sqrt x + 19/6`. The reciprocal mass estimate and
the positive square-factor comparison retain the exact parity correction.
This is the zero-mass substitution preceding equation (4.8). -/
theorem primitive_zeroMass_logWeightedContribution_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 10000 ≤ x) :
    |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| * (2 * Real.sqrt x + 2) ≤
      (Real.sqrt x + 19 / 6) *
        ((1 - 1 / x) * Real.log ((q : ℝ) / Real.pi) -
            2 * (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ).re +
          2 * reciprocalCorrection χ x) := by
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by norm_num only) hx
  have hs : (100 : ℝ) ≤ Real.sqrt x :=
    (Real.le_sqrt (by norm_num only) (zero_lt_one.trans hx1).le).mpr
      (by
        norm_num only; exact hx)
  have hs1 : 1 < Real.sqrt x := lt_of_lt_of_le (by norm_num only) hs
  have hd : 0 < (1 - 1 / Real.sqrt x) ^ 2 :=
    sq_pos_of_pos (sub_pos.mpr ((div_lt_one (zero_lt_one.trans hs1)).mpr hs1))
  have hb := (le_div_iff₀ hd).mp (character_zeroMass_bounds χ hq hp hGRH hx1).2
  have hc :=
    mul_le_mul_of_nonneg_right (logarithmic_mass_coefficient_le hs)
      (abs_nonneg (AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ))
  have hr :=
    mul_le_mul_of_nonneg_right hb
      (add_nonneg (Real.sqrt_nonneg x) (by norm_num only : (0 : ℝ) ≤ 19 / 6))
  nlinarith only [hc, hr]

/-- Under GRH, for cutoff at least `10000` and conductor at least three, the
primitive zero-mass contribution is bounded using the original character's
reciprocal sum and the common-factor error of the level-conductor quotient.
Take real parts of the level-change norm estimate and substitute them into
the primitive bound. This keeps the character sum needed for orthogonality. -/
theorem primitive_zeroMass_logWeightedContribution_le_character {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hc : 3 ≤ χ.conductor)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 10000 ≤ x) :
    |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| *
        (2 * Real.sqrt x + 2) ≤
      (Real.sqrt x + 19 / 6) *
        ((1 - 1 / x) * Real.log ((χ.conductor : ℝ) / Real.pi) -
            2 * (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ).re +
          2 *
            AnalyticNumberTheory.Arithmetic.commonFactorReciprocalWeightedSum x (q / χ.conductor) +
          2 * reciprocalCorrection χ.primitiveCharacter x) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only) hx
  have hb :=
    primitive_zeroMass_logWeightedContribution_le χ.primitiveCharacter hc
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) hGRH hx
  have he :=
    AnalyticNumberTheory.Arithmetic.norm_characterReciprocalWeightedSum_sub_primitive_le x χ hx0
  have hre := (Complex.re_le_norm _).trans he
  rw [Complex.sub_re] at hre
  have hm :=
    mul_le_mul_of_nonneg_left hre
      (add_nonneg (Real.sqrt_nonneg x) (by norm_num only : (0 : ℝ) ≤ 19 / 6))
  nlinarith only [hb, hm]

/-- Under GRH, for modulus at least 64, conductor at least three, and cutoff at least
10000, retain the exact primitive reciprocal correction in the logarithmic character norm bound.
Substitute the reciprocal zero-mass bound and control the common-factor sum geometrically.
The correction remains available for an exact even/odd average rather than a common constant. -/
theorem norm_characterLogWeightedSum_le_reciprocal_parity_explicit {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hq : 64 ≤ q) (hc : 3 ≤ χ.conductor)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 10000 ≤ x) :
    ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ‖ ≤
      (Real.sqrt x + 19 / 6) *
          ((1 - 1 / x) * Real.log ((χ.conductor : ℝ) / Real.pi) -
              2 * (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ).re +
            2 * AnalyticNumberTheory.Arithmetic.primeFactorLogSum (q / χ.conductor) +
            2 * reciprocalCorrection χ.primitiveCharacter x) +
        ((2 / 3 : ℝ) * Real.log ((q : ℝ) / Real.pi) + 4) * Real.log x +
        |Real.log ((χ.conductor : ℝ) / Real.pi) * Real.log x / 2 +
            logCorrection χ.primitiveCharacter x| +
        (1 / 2 : ℝ) * (q / χ.conductor).primeFactors.card * (Real.log x) ^ 2 := by
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by norm_num only) hx
  have hs := norm_characterLogWeightedSum_le_ambient_explicit χ hq hc hGRH hx1
  have hb := primitive_zeroMass_logWeightedContribution_le_character χ hc hGRH hx
  have hquot : q / χ.conductor ≠ 0 :=
    Nat.ne_of_gt
      (Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level) (NeZero.pos χ.conductor))
  have he :=
    AnalyticNumberTheory.Arithmetic.commonFactorReciprocalWeightedSum_le hquot
      (zero_lt_one.trans hx1)
  have hm :=
    mul_le_mul_of_nonneg_left he
      (add_nonneg (Real.sqrt_nonneg x) (by norm_num only : (0 : ℝ) ≤ 19 / 6))
  nlinarith only [hs, hb, hm]

/-- Under GRH, for modulus at least `64`, conductor at least three, and cutoff
at least `10000`, the logarithmic character norm is bounded by its reciprocal
sum, the prime-divisor error of the level-conductor quotient, and explicit
endpoint and parity terms. Substitute the reciprocal zero-mass estimate, bound
the common-factor sum geometrically, and use correction at most `-2/7`.
This retains the reciprocal sum required for the coset character average. -/
theorem norm_characterLogWeightedSum_le_reciprocal_explicit {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hq : 64 ≤ q) (hc : 3 ≤ χ.conductor)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 10000 ≤ x) :
    ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ‖ ≤
      (Real.sqrt x + 19 / 6) *
          ((1 - 1 / x) * Real.log ((χ.conductor : ℝ) / Real.pi) -
                2 * (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ).re +
              2 * AnalyticNumberTheory.Arithmetic.primeFactorLogSum (q / χ.conductor) -
            4 / 7) +
        ((2 / 3 : ℝ) * Real.log ((q : ℝ) / Real.pi) + 4) * Real.log x +
        |Real.log ((χ.conductor : ℝ) / Real.pi) * Real.log x / 2 +
            logCorrection χ.primitiveCharacter x| +
        (1 / 2 : ℝ) * (q / χ.conductor).primeFactors.card * (Real.log x) ^ 2 := by
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by norm_num only) hx
  have hs := norm_characterLogWeightedSum_le_ambient_explicit χ hq hc hGRH hx1
  have hb := primitive_zeroMass_logWeightedContribution_le_character χ hc hGRH hx
  have hquot : q / χ.conductor ≠ 0 :=
    Nat.ne_of_gt
      (Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level) (NeZero.pos χ.conductor))
  have he :=
    AnalyticNumberTheory.Arithmetic.commonFactorReciprocalWeightedSum_le hquot
      (zero_lt_one.trans hx1)
  have hE :=
    reciprocalCorrection_le_neg_two_sevenths χ.primitiveCharacter
      ((by norm_num only : (1000 : ℝ) ≤ 10000).trans hx)
  have hA : 0 ≤ Real.sqrt x + 19 / 6 := add_nonneg (Real.sqrt_nonneg x) (by norm_num only)
  have hm := mul_le_mul_of_nonneg_left he hA
  have hEm := mul_le_mul_of_nonneg_left hE hA
  nlinarith only [hs, hb, hm, hEm]

/-- For cutoff at least `65536`, its squared logarithm is at most its square root.
Apply the logarithm tangent bound at `16` to the fourth root, then square
the resulting nonnegative inequality. This absorbs the cost per prime factor
in the conductor-change estimate. -/
theorem log_sq_le_sqrt_of_large {x : ℝ} (hx : 65536 ≤ x) : (Real.log x) ^ 2 ≤ Real.sqrt x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only) hx
  have hs : (256 : ℝ) ≤ Real.sqrt x :=
    Real.le_sqrt_of_sq_le
      (by
        norm_num only at hx ⊢; exact hx)
  have hy : (16 : ℝ) ≤ Real.sqrt (Real.sqrt x) :=
    Real.le_sqrt_of_sq_le
      (by
        norm_num only at hs ⊢; exact hs)
  have hy0 : 0 < Real.sqrt (Real.sqrt x) := lt_of_lt_of_le (by norm_num only) hy
  have ht := PseudoPrime.Analysis.log_le_log_add_sub_div (a := (16 : ℝ)) (by norm_num only) hy0
  have hl : Real.log x = 4 * Real.log (Real.sqrt (Real.sqrt x)) := by
    rw [Real.log_sqrt (Real.sqrt_nonneg x), Real.log_sqrt hx0.le]
    ring
  have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num only, Real.log_pow]
    norm_num only
  have hle : Real.log x ≤ Real.sqrt (Real.sqrt x) := by
    rw [h16] at ht
    rw [hl]
    linarith only [ht, hy, Real.log_two_lt_d9]
  have hn : 0 ≤ Real.log x := Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 65536).trans hx)
  have hsq := mul_self_le_mul_self hn hle
  simpa only [Real.mul_self_sqrt (Real.sqrt_nonneg x), ← pow_two] using hsq

/-- Under GRH, with modulus at least `64`, conductor at least three, and
cutoff at least `65536`, the conductor quotient contributes only `log 2` and
`log² x` to the norm bound. Combine the prime-factor cost inequality with
`log² x ≤ sqrt x` and the exact level-conductor logarithm identity. This removes
the prime-factor count before averaging over the annihilator. -/
theorem norm_characterLogWeightedSum_le_level_explicit {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hq : 64 ≤ q) (hc : 3 ≤ χ.conductor)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 65536 ≤ x) :
    ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ‖ ≤
      (Real.sqrt x + 19 / 6) *
          (Real.log ((q : ℝ) / Real.pi) + Real.log 2 - 4 / 7 -
            2 * (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ).re -
            Real.log ((χ.conductor : ℝ) / Real.pi) / x) +
        (Real.log x) ^ 2 +
        ((2 / 3 : ℝ) * Real.log ((q : ℝ) / Real.pi) + 4) * Real.log x +
        |Real.log ((χ.conductor : ℝ) / Real.pi) * Real.log x / 2 +
            logCorrection χ.primitiveCharacter x| := by
  have hs :=
    norm_characterLogWeightedSum_le_reciprocal_explicit χ hq hc hGRH
      ((by norm_num only : (10000 : ℝ) ≤ 65536).trans hx)
  have hA : 0 ≤ Real.sqrt x + 19 / 6 := add_nonneg (Real.sqrt_nonneg x) (by norm_num only)
  have hcost :=
    AnalyticNumberTheory.Arithmetic.primeFactorLogCost_le
      (Nat.ne_of_gt
        (Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level) (NeZero.pos χ.conductor)))
      hA (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2) (sq_nonneg (Real.log x)))
      (show 2 * ((1 / 2 : ℝ) * (Real.log x) ^ 2) ≤ Real.sqrt x + 19 / 6 by
        linarith only [log_sq_le_sqrt_of_large hx])
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hc0 : (χ.conductor : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne χ.conductor)
  have hlog :
    Real.log ((q / χ.conductor : ℕ) : ℝ) =
      Real.log ((q : ℝ) / Real.pi) - Real.log ((χ.conductor : ℝ) / Real.pi) := by
    rw [Nat.cast_div χ.conductor_dvd_level hc0, Real.log_div hq0 hc0,
      Real.log_div hq0 Real.pi_pos.ne', Real.log_div hc0 Real.pi_pos.ne']
    ring
  rw [hlog] at hcost
  simp only [div_eq_mul_inv] at hs hcost ⊢
  nlinarith only [hs, hcost]

/-- Under GRH and the explicit modulus, conductor, and cutoff bounds, absorb
the conductor-quotient costs while retaining the exact reciprocal parity correction.
The prime-factor cost inequality and level-conductor logarithm identity replace
those costs by `log 2` and `log² x`. This keeps the correction available for averaging. -/
theorem norm_characterLogWeightedSum_le_level_parity_explicit {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hq : 64 ≤ q) (hc : 3 ≤ χ.conductor)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 65536 ≤ x) :
    ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ‖ ≤
      (Real.sqrt x + 19 / 6) *
          (Real.log ((q : ℝ) / Real.pi) + Real.log 2 +
              2 * reciprocalCorrection χ.primitiveCharacter x -
            2 * (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ).re -
            Real.log ((χ.conductor : ℝ) / Real.pi) / x) +
        (Real.log x) ^ 2 +
        ((2 / 3 : ℝ) * Real.log ((q : ℝ) / Real.pi) + 4) * Real.log x +
        |Real.log ((χ.conductor : ℝ) / Real.pi) * Real.log x / 2 +
            logCorrection χ.primitiveCharacter x| := by
  have hs :=
    norm_characterLogWeightedSum_le_reciprocal_parity_explicit χ hq hc hGRH
      ((by norm_num only : (10000 : ℝ) ≤ 65536).trans hx)
  have hA : 0 ≤ Real.sqrt x + 19 / 6 := add_nonneg (Real.sqrt_nonneg x) (by norm_num only)
  have hcost :=
    AnalyticNumberTheory.Arithmetic.primeFactorLogCost_le
      (Nat.ne_of_gt
        (Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level) (NeZero.pos χ.conductor)))
      hA (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2) (sq_nonneg (Real.log x)))
      (show 2 * ((1 / 2 : ℝ) * (Real.log x) ^ 2) ≤ Real.sqrt x + 19 / 6 by
        linarith only [log_sq_le_sqrt_of_large hx])
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hc0 : (χ.conductor : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne χ.conductor)
  have hlog :
    Real.log ((q / χ.conductor : ℕ) : ℝ) =
      Real.log ((q : ℝ) / Real.pi) - Real.log ((χ.conductor : ℝ) / Real.pi) := by
    rw [Nat.cast_div χ.conductor_dvd_level hc0, Real.log_div hq0 hc0,
      Real.log_div hq0 Real.pi_pos.ne', Real.log_div hc0 Real.pi_pos.ne']
    ring
  rw [hlog] at hcost
  simp only [div_eq_mul_inv] at hs hcost ⊢
  nlinarith only [hs, hcost]

/-- The certified pi and logarithm bounds imply
`log pi - log 2 + 4/7 ≥ 1021/1000`. This rational margin absorbs the small
conductor endpoint correction in the coset norm estimate. -/
private theorem log_pi_margin : (1021 / 1000 : ℝ) ≤ Real.log Real.pi - Real.log 2 + 4 / 7 := by
  have hpi : Real.pi ≤ (22 / 7 : ℝ) := Real.pi_lt_d4.le.trans (by norm_num only)
  have hlo :=
    Analysis.log_gt_affine_of_anchor (a := (3 : ℝ)) (b := 22 / 7) (y := Real.pi) (L := 1.0986122885)
      (by norm_num only) (by norm_num only) Real.pi_gt_three.le hpi Real.log_three_gt_d9
  linarith only [hlo, Real.pi_gt_d4, Real.log_two_lt_d9]

/-- For level at least three and cutoff at least `65536`, the negative
conductor logarithm divided by the cutoff is at most `1/1000`.
A conductor at least four has nonnegative logarithm; the remaining small
level follows from the certified lower logarithm bound. -/
private theorem neg_log_conductor_div_cutoff_le {m : ℕ} (hm : 3 ≤ m) {x : ℝ} (hx : 65536 ≤ x) :
    -Real.log ((m : ℝ) / Real.pi) / x ≤ (1 / 1000 : ℝ) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only) hx
  have hL : -(1 / 20 : ℝ) ≤ Real.log ((m : ℝ) / Real.pi) := by
    by_cases hm4 : 4 ≤ m
    · exact
        (by norm_num only : -(1 / 20 : ℝ) ≤ 0).trans
          (AnalyticNumberTheory.Arithmetic.log_conductor_div_pi_nonneg_of_four_le hm4)
    · exact (log_level_div_pi_small_bounds hm ((Nat.lt_of_not_ge hm4).trans (by norm_num only))).1
  apply (div_le_iff₀ hx0).mpr
  linarith only [hL, hx]

/-- Under GRH and the explicit modulus, conductor, and cutoff lower bounds,
the logarithmic character norm has coefficient `log q - 51/50`, with its
reciprocal sum retained and explicit endpoint and parity errors.
Absorb the conductor quotient costs, use the rational logarithmic margin,
and bound the conductor endpoint correction. This supplies the norm estimate
before the final parity bound and character averaging. -/
theorem norm_characterLogWeightedSum_le_coset_explicit {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hq : 64 ≤ q) (hc : 3 ≤ χ.conductor)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 65536 ≤ x) :
    ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ‖ ≤
      (Real.sqrt x + 19 / 6) *
          (Real.log q - 51 / 50 -
            2 * (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ).re) +
        (Real.log x) ^ 2 +
        ((2 / 3 : ℝ) * Real.log ((q : ℝ) / Real.pi) + 4) * Real.log x +
        |Real.log ((χ.conductor : ℝ) / Real.pi) * Real.log x / 2 +
            logCorrection χ.primitiveCharacter x| := by
  have hs := norm_characterLogWeightedSum_le_level_explicit χ hq hc hGRH hx
  have hcError := neg_log_conductor_div_cutoff_le hc hx
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  rw [Real.log_div hq0 Real.pi_pos.ne'] at hs
  have hm :=
    mul_le_mul_of_nonneg_left hcError
      (add_nonneg (Real.sqrt_nonneg x) (by norm_num only : (0 : ℝ) ≤ 19 / 6))
  have hp :=
    mul_le_mul_of_nonneg_left log_pi_margin
      (add_nonneg (Real.sqrt_nonneg x) (by norm_num only : (0 : ℝ) ≤ 19 / 6))
  simp only [neg_div] at hm
  rw [Real.log_div hq0 Real.pi_pos.ne']
  nlinarith only [hs, hm, hp]

/-- For conductor at least three dividing the level and cutoff at least
`100`, the absolute logarithmic parity correction is bounded by half the
cutoff logarithm times `log(max(q/pi,2x))`. The upper side follows from the
nonpositive parity correction and the level bound; the lower side uses the
geometric tail bounds and certified logarithmic constants.
This eliminates the parity term from the coset character estimate. -/
theorem abs_logarithmic_parity_correction_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hc : 3 ≤ χ.conductor) {x : ℝ} (hx : 100 ≤ x) :
    |Real.log ((χ.conductor : ℝ) / Real.pi) * Real.log x / 2 +
          logCorrection χ.primitiveCharacter x| ≤
      Real.log x / 2 * Real.log (max ((q : ℝ) / Real.pi) (2 * x)) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only) hx
  have hl : 0 ≤ Real.log x := Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 100).trans hx)
  have hc0 : (χ.conductor : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne χ.conductor)
  have hcond :=
    Real.log_le_log
      (lt_of_le_of_lt zero_le_one
        (by exact_mod_cast (lt_of_lt_of_le (by norm_num only : (1 : ℕ) < 3) hc) :
          (1 : ℝ) < χ.conductor))
      (by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level : (χ.conductor : ℝ) ≤ q)
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hlevel : Real.log ((χ.conductor : ℝ) / Real.pi) ≤ Real.log ((q : ℝ) / Real.pi) := by
    rw [Real.log_div hc0 Real.pi_pos.ne', Real.log_div hq0 Real.pi_pos.ne']
    exact sub_le_sub_right hcond _
  have hmaxq :=
    Real.log_le_log (div_pos (by exact_mod_cast NeZero.pos q) Real.pi_pos)
      (le_max_left ((q : ℝ) / Real.pi) (2 * x))
  have hmaxx :=
    Real.log_le_log (mul_pos (by norm_num only : (0 : ℝ) < 2) hx0)
      (le_max_right ((q : ℝ) / Real.pi) (2 * x))
  rw [Real.log_mul (by norm_num only) hx0.ne'] at hmaxx
  have htop := mul_le_mul_of_nonneg_right (hlevel.trans hmaxq) hl
  have hbottom := mul_le_mul_of_nonneg_left hmaxx hl
  have hL : -(1 / 20 : ℝ) ≤ Real.log ((χ.conductor : ℝ) / Real.pi) := by
    by_cases hc4 : 4 ≤ χ.conductor
    · exact
        (by norm_num only : -(1 / 20 : ℝ) ≤ 0).trans
          (AnalyticNumberTheory.Arithmetic.log_conductor_div_pi_nonneg_of_four_le hc4)
    · exact (log_level_div_pi_small_bounds hc ((Nat.lt_of_not_ge hc4).trans (by norm_num only))).1
  rw [abs_le]
  by_cases he : χ.primitiveCharacter (-1) = 1
  · rw [logCorrection, ite_eq_left_iff.mpr fun hn => (hn he).elim]
    have hE := logCorrectionEven_bounds hx
    have hsign :
      0 ≤ Real.log ((χ.conductor : ℝ) / Real.pi) - Real.eulerMascheroniConstant + Real.log 2 := by
      linarith only [hL, Analysis.eulerMascheroniConstant_lt_twentyNine_fiftieths,
        Real.log_two_gt_d9]
    have hprod := mul_nonneg hsign hl
    constructor <;> nlinarith only [hE.1, hE.2, htop, hbottom, hprod]
  · rw [logCorrection, ite_eq_right_iff.mpr fun h => (he h).elim]
    have hE := logCorrectionOdd_bounds hx
    have hlog : (4 : ℝ) ≤ Real.log x := by
      have h :=
        Real.log_le_log (by norm_num only : (0 : ℝ) < 81)
          ((by norm_num only : (81 : ℝ) ≤ 100).trans hx)
      rw [show (81 : ℝ) = 3 ^ (4 : ℕ) by norm_num only, Real.log_pow] at h
      norm_num only at h
      linarith only [h, Real.log_three_gt_d9]
    have hsign :
      0 ≤
        Real.log ((χ.conductor : ℝ) / Real.pi) - Real.log 2 - Real.eulerMascheroniConstant +
          Real.log x := by
      linarith only [hL, hlog, Analysis.eulerMascheroniConstant_lt_twentyNine_fiftieths,
        Real.log_two_lt_d9]
    have hprod := mul_nonneg hsign hl
    constructor <;> nlinarith only [hE.1, hE.2, htop, hbottom, hprod]

/-- Under GRH, with modulus at least `64`, conductor at least three,
and cutoff at least `65536`, the character logarithmic norm satisfies the
explicit coset estimate with coefficient `log q - 51/50`.
Insert the absolute parity bound into the conductor-free estimate.
The retained reciprocal sum cancels after annihilator orthogonality. -/
theorem norm_characterLogWeightedSum_le_coset {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hq : 64 ≤ q) (hc : 3 ≤ χ.conductor)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 65536 ≤ x) :
    ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ‖ ≤
      (Real.sqrt x + 19 / 6) *
          (Real.log q - 51 / 50 -
            2 * (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ).re) +
        (Real.log x) ^ 2 +
        ((2 / 3 : ℝ) * Real.log ((q : ℝ) / Real.pi) + 4) * Real.log x +
        Real.log x / 2 * Real.log (max ((q : ℝ) / Real.pi) (2 * x)) := by
  have hs := norm_characterLogWeightedSum_le_coset_explicit χ hq hc hGRH hx
  have hp :=
    abs_logarithmic_parity_correction_le χ hc ((by norm_num only : (100 : ℝ) ≤ 65536).trans hx)
  linarith only [hs, hp]

/-- For a conductor at least three and positive cutoff, retain the endpoint error
as `1/(20*x)`. The certified conductor logarithm is at least `-1/20`.
This preserves the cutoff-dependent saving in parity-averaged norm bounds. -/
private theorem neg_log_conductor_div_cutoff_le_fine {m : ℕ} (hm : 3 ≤ m) {x : ℝ} (hx : 0 < x) :
    -Real.log ((m : ℝ) / Real.pi) / x ≤ 1 / (20 * x) := by
  have hL : -(1 / 20 : ℝ) ≤ Real.log ((m : ℝ) / Real.pi) := by
    by_cases hm4 : 4 ≤ m
    · exact
        (by norm_num only : -(1 / 20 : ℝ) ≤ 0).trans
          (PseudoPrime.AnalyticNumberTheory.Arithmetic.log_conductor_div_pi_nonneg_of_four_le hm4)
    · exact (log_level_div_pi_small_bounds hm ((Nat.lt_of_not_ge hm4).trans (by norm_num only))).1
  have h :=
    div_le_div_of_nonneg_right (show -Real.log ((m : ℝ) / Real.pi) ≤ 1 / 20 by linarith only [hL])
      hx.le
  convert h using 1
  ring

/-- Under GRH, modulus at least 64, conductor at least three, and cutoff at least
65536, bound the character logarithmic norm while retaining its primitive reciprocal
parity correction. Absorb conductor-quotient costs, bound the remaining endpoint
error by `1/(20*x)`, and apply the absolute logarithmic parity bound.
The retained correction can then be averaged using the exact even and odd counts. -/
theorem norm_characterLogWeightedSum_le_coset_parity {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hq : 64 ≤ q) (hc : 3 ≤ χ.conductor)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 65536 ≤ x) :
    ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ‖ ≤
      (Real.sqrt x + 19 / 6) *
          (Real.log q - Real.log Real.pi + Real.log 2 +
                2 * reciprocalCorrection χ.primitiveCharacter x -
              2 * (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ).re +
            1 / (20 * x)) +
        (Real.log x) ^ 2 +
        ((2 / 3 : ℝ) * Real.log ((q : ℝ) / Real.pi) + 4) * Real.log x +
        Real.log x / 2 * Real.log (max ((q : ℝ) / Real.pi) (2 * x)) := by
  have hs := norm_characterLogWeightedSum_le_level_parity_explicit χ hq hc hGRH hx
  have he :=
    neg_log_conductor_div_cutoff_le_fine hc (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 65536) hx)
  have hp :=
    abs_logarithmic_parity_correction_le χ hc ((by norm_num only : (100 : ℝ) ≤ 65536).trans hx)
  have hm :=
    mul_le_mul_of_nonneg_left he
      (add_nonneg (Real.sqrt_nonneg x) (by norm_num only : (0 : ℝ) ≤ 19 / 6))
  rw [Real.log_div (Nat.cast_ne_zero.mpr (NeZero.ne q)) Real.pi_pos.ne'] at hs ⊢
  simp only [neg_div] at hm
  nlinarith only [hs, hm, hp]

end PseudoPrime.LLS.PaperStatements
