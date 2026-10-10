/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.LogLValueIntegral
public import PseudoPrime.LLS.DirichletExplicitFormula
public import PseudoPrime.LLS.RiemannExplicitFormula
public import PseudoPrime.LLS.Extensions.DirichletAdmissibility
public import PseudoPrime.LLS.Extensions.PaperProofs
public import PseudoPrime.LLS.LogLValueParityBounds
public import PseudoPrime.LLS.LogLValueComparison
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.MangoldtLogSquareSeries

/-!
# Explicit logarithmic L-value bounds

The completed general Lemma 2.5 supplies the theta-free inequalities used in Section 5.
Lemma 2.3 eliminates the zero mass. Unsigned character comparisons and Lemma 5.1
then give upper and lower bounds involving only unsigned finite sums and parity corrections.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- A real error coefficient of absolute value at most one scales a nonnegative magnitude
into the interval from its negative to its positive. Multiply the coefficient bounds;
this controls the independent zero and gamma errors in the logarithmic formula. -/
private theorem bounded_real_error {θ a : ℝ} (hθ : |θ| ≤ 1) (ha : 0 ≤ a) :
    -a ≤ θ * a ∧ θ * a ≤ a := by
  have h := abs_le.mp hθ
  constructor <;>
    nlinarith only [mul_le_mul_of_nonneg_right h.1 ha, mul_le_mul_of_nonneg_right h.2 ha]

/-- For nonnegative zero mass and error magnitudes, a logarithmic formula with two
independent coefficients in [-1,1] lies between the stated endpoints.
Bound the two weighted errors separately and rearrange; no sign condition on c is needed. -/
private theorem bounded_log_formula {v A c d b e θ₁ θ₂ : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hθ₁ : |θ₁| ≤ 1) (hθ₂ : |θ₂| ≤ 1) (hv : v = A - (c + θ₁ * d) * b + θ₂ * e) :
    A - (c + d) * b - e ≤ v ∧ v ≤ A - (c - d) * b + e := by
  have h₁ := bounded_real_error hθ₁ (mul_nonneg hd hb)
  have h₂ := bounded_real_error hθ₂ he
  constructor <;> nlinarith only [hv, h₁.1, h₁.2, h₂.1, h₂.2]

/-- For a complex Dirichlet character, define the conductor and parity-dependent gamma
endpoint log(q/pi)/2 + digamma((1+a)/2)/2, using its explicit even and odd special values.
The definition requires no primitivity or RH; dividing by log x gives the deterministic
endpoint contribution in Lemma 2.5 and the L-value estimates of Section 5. -/
noncomputable def characterGammaLogTerm {q : ℕ} (χ : DirichletCharacter ℂ q) : ℝ :=
  Real.log ((q : ℝ) / Real.pi) / 2 +
    (if χ (-1) = 1 then -2 * Real.log 2 - Real.eulerMascheroniConstant
      else -Real.eulerMascheroniConstant) /
      2

/-- For a primitive character of nonzero modulus q >= 3 under its individual RH and x >= 2,
bound log(norm(L(1))) above and below with explicit zero-mass and gamma error magnitudes.
Specialize the proved general L-function formula and bound each independent real error
coefficient by one. These are the starting upper and lower inequalities of Section 5. -/
theorem characterLogLValue_bounds {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q)
    (hp : χ.IsPrimitive) (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ) {x : ℝ}
    (hx : 2 ≤ x) :
    (characterLogLValueSum χ x).re + characterGammaLogTerm χ / Real.log x -
          (1 / Real.log x + 2 / (Real.sqrt x * (Real.log x) ^ 2)) *
            |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| -
          2 / (x * (Real.log x) ^ 2) ≤
        Real.log ‖χ.LFunction 1‖ ∧
      Real.log ‖χ.LFunction 1‖ ≤
        (characterLogLValueSum χ x).re + characterGammaLogTerm χ / Real.log x -
            (1 / Real.log x - 2 / (Real.sqrt x * (Real.log x) ^ 2)) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| +
          2 / (x * (Real.log x) ^ 2) := by
  obtain ⟨θ₁, θ₂, hθ₁, hθ₂, hformula⟩ :=
    (lls_lemma25_of_general_formula Extensions.lls_propL1_general_proof) q χ hq hp hRH x hx
  have hx0 : 0 ≤ x := le_trans (by norm_num only : (0 : ℝ) ≤ 2) hx
  apply
    bounded_log_formula (abs_nonneg _)
      (div_nonneg (by norm_num only) (mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg _)))
      (div_nonneg (by norm_num only) (mul_nonneg hx0 (sq_nonneg _))) hθ₁ hθ₂
  rw [hformula]
  unfold characterGammaLogTerm
  ring

/-- For a primitive character of nonzero modulus q >= 3 under individual RH and x >= 2,
replace the real logarithmic character sum in the upper L-value bound by its unsigned sum.
Use the norm-one character bound on the nonnegative finite weights. The zero-mass term
is retained for elimination with the reciprocal formula in the upper bound of Theorem 1.5. -/
theorem logLValue_le_unsigned {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q)
    (hp : χ.IsPrimitive) (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ) {x : ℝ}
    (hx : 2 ≤ x) :
    Real.log ‖χ.LFunction 1‖ ≤
      logLValueSum x + characterGammaLogTerm χ / Real.log x -
          (1 / Real.log x - 2 / (Real.sqrt x * (Real.log x) ^ 2)) *
            |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| +
        2 / (x * (Real.log x) ^ 2) := by
  have h := (characterLogLValue_bounds χ hq hp hRH hx).2
  have hs := characterLogLValueSum_re_le χ (le_trans (by norm_num only : (1 : ℝ) ≤ 2) hx)
  linarith only [h, hs]

/-- For x > 1 and a real coefficient of absolute value at most one, the reciprocal
error factor lies between (1 - 1/sqrt x)^2 and (1 + 1/sqrt x)^2.
Expand the squares using (sqrt x)^2 = x and bound the coefficient; these bounds remove
theta from the zero-mass identity of Lemma 2.3. -/
private theorem reciprocal_factor_bounds {x θ : ℝ} (hx : 1 < x) (hθ : |θ| ≤ 1) :
    (1 - 1 / Real.sqrt x) ^ 2 ≤ 1 + 2 * θ / Real.sqrt x + 1 / x ∧
      1 + 2 * θ / Real.sqrt x + 1 / x ≤ (1 + 1 / Real.sqrt x) ^ 2 := by
  have h :=
    mul_le_mul_of_nonneg_left (abs_le.mp hθ).1
      (div_nonneg (show (0 : ℝ) ≤ 2 by norm_num only) (Real.sqrt_nonneg x))
  have h' :=
    mul_le_mul_of_nonneg_left (abs_le.mp hθ).2
      (div_nonneg (show (0 : ℝ) ≤ 2 by norm_num only) (Real.sqrt_nonneg x))
  have hs : (1 / Real.sqrt x) ^ 2 = 1 / x := by
    rw [div_pow, one_pow, Real.sq_sqrt (zero_lt_one.trans hx).le]
  simp only [div_eq_mul_inv, one_mul] at h h' hs ⊢
  constructor <;> nlinarith only [h, h', hs]

/-- If a nonnegative mass equals the inverse reciprocal error factor times R, with
x > 1 and a coefficient in [-1,1], it lies between R/(1 + 1/sqrt x)^2 and
R/(1 - 1/sqrt x)^2. Both denominators are positive; multiply out the identity and
use the factor bounds. No additional sign assumption on R is needed. -/
private theorem reciprocal_mass_bounds {x b R θ : ℝ} (hx : 1 < x) (hb : 0 ≤ b) (hθ : |θ| ≤ 1)
    (he : b = (1 + 2 * θ / Real.sqrt x + 1 / x)⁻¹ * R) :
    R / (1 + 1 / Real.sqrt x) ^ 2 ≤ b ∧ b ≤ R / (1 - 1 / Real.sqrt x) ^ 2 := by
  have hs : 1 < Real.sqrt x := by simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt zero_le_one hx
  have hm : 0 < (1 - 1 / Real.sqrt x) ^ 2 :=
    sq_pos_of_pos (sub_pos.mpr ((div_lt_one (zero_lt_one.trans hs)).mpr hs))
  have hp : 0 < (1 + 1 / Real.sqrt x) ^ 2 :=
    sq_pos_of_pos
      (add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg zero_le_one (Real.sqrt_nonneg x)))
  have hreal : (1 + 2 * θ / Real.sqrt x + 1 / x) * b = R := by
    rw [he, mul_inv_cancel_left₀ (reciprocalErrorFactor_pos hx hθ).ne']
  have hc := reciprocal_factor_bounds hx hθ
  constructor
  · apply (div_le_iff₀ hp).mpr
    nlinarith only [hreal, mul_le_mul_of_nonneg_right hc.2 hb]
  · apply (le_div_iff₀ hm).mpr
    nlinarith only [hreal, mul_le_mul_of_nonneg_right hc.1 hb]

/-- Under GRH, for a primitive character of nonzero modulus q >= 3 and x > 1, bound
its absolute real Hadamard constant using the smoothed reciprocal character sum and
its exact parity correction, with denominators (1 ± 1/sqrt x)^2.
The real clause of Lemma 2.3 and positivity of its error factor eliminate theta.
These are the two zero-mass substitutions used in the upper and lower L-value estimates. -/
theorem character_zeroMass_bounds {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q)
    (hp : χ.IsPrimitive) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 1 < x) :
    (1 / 2 * (1 - 1 / x) * Real.log ((q : ℝ) / Real.pi) -
              (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ).re +
            reciprocalCorrection χ x) /
          (1 + 1 / Real.sqrt x) ^ 2 ≤
        |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| ∧
      |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| ≤
        (1 / 2 * (1 - 1 / x) * Real.log ((q : ℝ) / Real.pi) -
              (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ).re +
            reciprocalCorrection χ x) /
          (1 - 1 / Real.sqrt x) ^ 2 := by
  obtain ⟨θ, hθ, he⟩ :=
    characterReciprocalWeightedSum_real_of_complex hq hp hGRH hx
      (characterReciprocalWeightedSum_complex_formula hq hp hGRH hx)
  exact reciprocal_mass_bounds hx (abs_nonneg _) hθ he

/-- For x >= 4, the coefficient of the zero mass in the upper logarithmic bound
is nonnegative. Use sqrt x >= 2 and log x >= 1, then clear positive denominators.
This permits substitution of the lower zero-mass estimate without reversing the bound. -/
private theorem log_zero_coefficient_nonneg {x : ℝ} (hx : 4 ≤ x) :
    0 ≤ 1 / Real.log x - 2 / (Real.sqrt x * (Real.log x) ^ 2) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 4) hx
  have hs : 2 ≤ Real.sqrt x :=
    (Real.le_sqrt (by norm_num only) hx0.le).mpr
      (by
        norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num only]
        exact hx)
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 4) hx
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow] at hl
  have hl1 : 1 ≤ Real.log x := by
    have h2 := Real.log_two_gt_d9
    norm_num only at h2
    norm_num only at hl
    linarith only [hl, h2]
  have hl0 := (zero_lt_one.trans_le hl1)
  apply sub_nonneg.mpr
  apply (div_le_div_iff₀ (mul_pos (Real.sqrt_pos.mpr hx0) (sq_pos_of_pos hl0)) hl0).mpr
  nlinarith only [mul_le_mul hs hl1 zero_le_one (Real.sqrt_nonneg x), hl0]

/-- Under GRH, for a primitive character of modulus q >= 3 and x >= 4, bound
log(norm(L(1))) using only finite logarithmic and reciprocal character sums and the
explicit parity correction. Substitute the lower zero-mass bound from Lemma 2.3
into Lemma 2.5; positivity of its coefficient justifies the inequality direction.
This removes the Hadamard constant from the upper estimate for Theorem 1.5. -/
theorem logLValue_le_reciprocal {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q)
    (hp : χ.IsPrimitive) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 4 ≤ x) :
    Real.log ‖χ.LFunction 1‖ ≤
      (characterLogLValueSum χ x).re + characterGammaLogTerm χ / Real.log x -
          (1 / Real.log x - 2 / (Real.sqrt x * (Real.log x) ^ 2)) *
            ((1 / 2 * (1 - 1 / x) * Real.log ((q : ℝ) / Real.pi) -
                  (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ).re +
                reciprocalCorrection χ x) /
              (1 + 1 / Real.sqrt x) ^ 2) +
        2 / (x * (Real.log x) ^ 2) := by
  have hx2 : 2 ≤ x := le_trans (by norm_num only : (2 : ℝ) ≤ 4) hx
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 4) hx
  have h := (characterLogLValue_bounds χ hq hp (hGRH q χ hp) hx2).2
  have hb := (character_zeroMass_bounds χ hq hp hGRH hx1).1
  have hm := mul_le_mul_of_nonneg_left hb (log_zero_coefficient_nonneg hx)
  linarith only [h, hm]

/-- Under GRH, for a primitive character of modulus q >= 3 and x >= 2, bound
log(norm(L(1))) below using finite character sums and the exact parity correction.
Substitute the upper zero-mass bound from Lemma 2.3 into the lower inequality from
Lemma 2.5, whose zero-mass coefficient is positive. This is the lower L-value estimate
before applying the arithmetic comparison of Lemma 5.1. -/
theorem reciprocal_le_logLValue {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q)
    (hp : χ.IsPrimitive) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 2 ≤ x) :
    (characterLogLValueSum χ x).re + characterGammaLogTerm χ / Real.log x -
        (1 / Real.log x + 2 / (Real.sqrt x * (Real.log x) ^ 2)) *
          ((1 / 2 * (1 - 1 / x) * Real.log ((q : ℝ) / Real.pi) -
                (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ).re +
              reciprocalCorrection χ x) /
            (1 - 1 / Real.sqrt x) ^ 2) -
        2 / (x * (Real.log x) ^ 2) ≤
      Real.log ‖χ.LFunction 1‖ := by
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 2) hx
  have h := (characterLogLValue_bounds χ hq hp (hGRH q χ hp) hx).1
  have hb := (character_zeroMass_bounds χ hq hp hGRH hx1).2
  have hc : 0 ≤ 1 / Real.log x + 2 / (Real.sqrt x * (Real.log x) ^ 2) :=
    add_nonneg (div_nonneg zero_le_one (Real.log_pos hx1).le)
      (div_nonneg (by norm_num only) (mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg _)))
  have hm := mul_le_mul_of_nonneg_left hb hc
  linarith only [h, hm]

/-- Under GRH, for a primitive character of modulus q >= 3 and x >= 4, bound
log(norm(L(1))) above using the unsigned logarithmic and reciprocal Mangoldt sums,
the conductor and the exact parity correction. Substitute the lower zero-mass bound,
then use both unsigned character comparisons with the nonnegative coefficient.
This completes removal of character sums from the upper L-value estimate of Section 5. -/
theorem logLValue_le_unsigned_reciprocal {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 3 ≤ q) (hp : χ.IsPrimitive) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x : ℝ} (hx : 4 ≤ x) :
    Real.log ‖χ.LFunction 1‖ ≤
      logLValueSum x + characterGammaLogTerm χ / Real.log x -
          (1 / Real.log x - 2 / (Real.sqrt x * (Real.log x) ^ 2)) *
            ((1 / 2 * (1 - 1 / x) * Real.log ((q : ℝ) / Real.pi) -
                  AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum x +
                reciprocalCorrection χ x) /
              (1 + 1 / Real.sqrt x) ^ 2) +
        2 / (x * (Real.log x) ^ 2) := by
  have h := logLValue_le_reciprocal χ hq hp hGRH hx
  have ht := characterLogLValueSum_re_le χ (le_trans (by norm_num only : (1 : ℝ) ≤ 4) hx)
  have hu :=
    (Complex.re_le_norm _).trans
      (AnalyticNumberTheory.Arithmetic.norm_characterReciprocalWeightedSum_le χ
        (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 4) hx))
  have hd : 0 ≤ (1 + 1 / Real.sqrt x) ^ 2 := sq_nonneg _
  have hr' :=
    div_le_div_of_nonneg_right
      (add_le_add_right (sub_le_sub_left hu (1 / 2 * (1 - 1 / x) * Real.log ((q : ℝ) / Real.pi)))
        (reciprocalCorrection χ x))
      hd
  have hm := mul_le_mul_of_nonneg_left hr' (log_zero_coefficient_nonneg hx)
  simp only [div_eq_mul_inv] at h hm ⊢
  nlinarith only [h, ht, hm]

/-- For x > 1, the coefficient of the reciprocal character sum after combining
the lower logarithmic estimate with Lemma 5.1 is nonnegative. Its denominator
(1 - 1/sqrt x) ^ 2 lies in (0,1], and the added zero-error coefficient is nonnegative.
This allows the reciprocal character sum to be replaced by its unsigned lower bound. -/
private theorem lower_reciprocal_coefficient_nonneg {x : ℝ} (hx : 1 < x) :
    0 ≤
      (1 / Real.log x + 2 / (Real.sqrt x * (Real.log x) ^ 2)) / (1 - 1 / Real.sqrt x) ^ 2 -
        1 / Real.log x := by
  have hs : 1 < Real.sqrt x := by simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt zero_le_one hx
  have ht : 0 < 1 / Real.sqrt x := div_pos zero_lt_one (zero_lt_one.trans hs)
  have ht1 : 1 / Real.sqrt x < 1 := (div_lt_one (zero_lt_one.trans hs)).mpr hs
  have hd : 0 < (1 - 1 / Real.sqrt x) ^ 2 := sq_pos_of_pos (sub_pos.mpr ht1)
  have hd1 : (1 - 1 / Real.sqrt x) ^ 2 ≤ 1 := by nlinarith only [ht, ht1]
  have hl := Real.log_pos hx
  have hc := div_nonneg zero_le_one hl.le
  have he :=
    div_nonneg (show (0 : ℝ) ≤ 2 by norm_num only)
      (mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg (Real.log x)))
  apply sub_nonneg.mpr
  apply (le_div_iff₀ hd).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hd1 hc, he]

/-- Combine a logarithmic lower bound, a comparison lower bound and an unsigned
bound on the reciprocal character term. The combined coefficient is nonnegative.
Multiply its lower bound and rearrange the two input inequalities; this isolates
the real algebra used to remove character sums from the reciprocal L-value estimate. -/
private theorem lower_bound_of_unsigned_comparison {v T A u D C U E S W l e : ℝ}
    (hl : T + A - u * ((C - U + E) / D) - e ≤ v) (ht : S - U / l ≤ T) (hu : -W ≤ U)
    (hk : 0 ≤ u / D - 1 / l) : S + A - (u / D) * (C + E) - (u / D - 1 / l) * W - e ≤ v := by
  have hm := mul_le_mul_of_nonneg_left hu hk
  simp only [div_eq_mul_inv] at hl ht hm ⊢
  nlinarith only [hl, ht, hm]

/-- Under GRH, for a primitive character of modulus q >= 3 and x >= 100, bound
log(norm(L(1))) below using unsigned logarithmic and reciprocal sums, the square
correction, the conductor and the exact parity correction. Combine Lemmas 2.3 and 2.5
with Lemma 5.1, then bound the remaining reciprocal character term by the unsigned sum.
Only the character's parity remains; zeta sum and correction estimates convert
this inequality to the elementary lower envelope used in Theorem 1.5. -/
theorem unsigned_comparison_le_logLValue {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 3 ≤ q) (hp : χ.IsPrimitive) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x : ℝ} (hx : 100 ≤ x) :
    -logLValueSum x - AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum x / Real.log x +
          2 *
            ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊ with m ^ 2 ≤ ⌊x⌋₊,
              ArithmeticFunction.vonMangoldt m *
                (1 / ((m : ℝ) ^ 2 * Real.log ((m : ℝ) ^ 2)) - 1 / (x * Real.log x)) +
          characterGammaLogTerm χ / Real.log x -
        ((1 / Real.log x + 2 / (Real.sqrt x * (Real.log x) ^ 2)) / (1 - 1 / Real.sqrt x) ^ 2) *
          (1 / 2 * (1 - 1 / x) * Real.log ((q : ℝ) / Real.pi) + reciprocalCorrection χ x) -
        ((1 / Real.log x + 2 / (Real.sqrt x * (Real.log x) ^ 2)) / (1 - 1 / Real.sqrt x) ^ 2 -
            1 / Real.log x) *
          AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum x -
        2 / (x * (Real.log x) ^ 2) ≤
      Real.log ‖χ.LFunction 1‖ := by
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 100) hx
  have hl := reciprocal_le_logLValue χ hq hp hGRH (le_trans (by norm_num only : (2 : ℝ) ≤ 100) hx)
  have ht := character_log_sum_ge_unsigned χ hx
  have hu :=
    (abs_le.mp
        ((Complex.abs_re_le_norm _).trans
          (AnalyticNumberTheory.Arithmetic.norm_characterReciprocalWeightedSum_le χ
            (zero_lt_one.trans hx1)))).1
  exact lower_bound_of_unsigned_comparison hl ht hu (lower_reciprocal_coefficient_nonneg hx1)

/-- Under GRH, for a primitive character of modulus q >= 3 and x >= 100,
bound log(norm(L(1,chi))) above and below with explicit elementary zeta terms.
T and U are upper envelopes for the unsigned logarithmic and reciprocal Mangoldt sums.
Insert the two-sided estimate of Lemma 2.6 and the reciprocal estimate of Lemma 2.4
with nonnegative coefficients. The square correction is log(pi^2/6) minus its exact
complementary-series and cutoff loss. Bounding this loss and cancelling the parity
correction gives the envelope specialized to x = (log q)^2/4 in Theorem 1.5. -/
theorem logLValue_bounds_with_explicit_zeta_terms {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 3 ≤ q) (hp : χ.IsPrimitive) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x : ℝ} (hx : 100 ≤ x) :
    let T :=
      Real.log (Real.log x) + Real.eulerMascheroniConstant - 1 +
        Real.eulerMascheroniConstant / Real.log x +
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass / (Real.sqrt x * (Real.log x) ^ 2) +
        1 / (3 * x ^ 3 * (Real.log x) ^ 2)
    let U :=
      Real.log x - (1 + Real.eulerMascheroniConstant) + Real.log (2 * Real.pi) / x +
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass / Real.sqrt x
    Real.log ‖χ.LFunction 1‖ ≤
        T + characterGammaLogTerm χ / Real.log x -
            (1 / Real.log x - 2 / (Real.sqrt x * (Real.log x) ^ 2)) *
              ((1 / 2 * (1 - 1 / x) * Real.log ((q : ℝ) / Real.pi) - U + reciprocalCorrection χ x) /
                (1 + 1 / Real.sqrt x) ^ 2) +
          2 / (x * (Real.log x) ^ 2) ∧
      -T - U / Real.log x +
            (Real.log (Real.pi ^ 2 / 6) -
              AnalyticNumberTheory.Arithmetic.squareMangoldtCorrectionLoss x) +
            characterGammaLogTerm χ / Real.log x -
          ((1 / Real.log x + 2 / (Real.sqrt x * (Real.log x) ^ 2)) / (1 - 1 / Real.sqrt x) ^ 2) *
            (1 / 2 * (1 - 1 / x) * Real.log ((q : ℝ) / Real.pi) + reciprocalCorrection χ x) -
          ((1 / Real.log x + 2 / (Real.sqrt x * (Real.log x) ^ 2)) / (1 - 1 / Real.sqrt x) ^ 2 -
              1 / Real.log x) *
            U -
          2 / (x * (Real.log x) ^ 2) ≤
        Real.log ‖χ.LFunction 1‖ := by
  dsimp only
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 100) hx
  have hx4 : 4 ≤ x := le_trans (by norm_num only : (4 : ℝ) ≤ 100) hx
  have hT := (abs_le.mp (abs_logLValueSum_error_le hGRH.riemann hx1)).2
  have hU := reciprocalWeightedMangoldtSum_le_explicit hGRH.riemann hx1
  constructor
  · have h := logLValue_le_unsigned_reciprocal χ hq hp hGRH hx4
    have hm :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right
          (add_le_add_right
            (sub_le_sub_left hU (1 / 2 * (1 - 1 / x) * Real.log ((q : ℝ) / Real.pi)))
            (reciprocalCorrection χ x))
          (sq_nonneg (1 + 1 / Real.sqrt x)))
        (log_zero_coefficient_nonneg hx4)
    simp only [div_eq_mul_inv] at h hm hT ⊢
    nlinarith only [h, hm, hT]
  · have h := unsigned_comparison_le_logLValue χ hq hp hGRH hx
    rw [AnalyticNumberTheory.Arithmetic.two_mul_squareMangoldtCorrection_eq] at h
    have hm := mul_le_mul_of_nonneg_left hU (lower_reciprocal_coefficient_nonneg hx1)
    have hd := div_le_div_of_nonneg_right hU (Real.log_pos hx1).le
    simp only [div_eq_mul_inv] at h hm hd hT ⊢
    nlinarith only [h, hm, hd, hT]

/-- Under GRH, for a primitive character of modulus q >= 3 and x >= 100,
bound log(norm(L(1,chi))) using explicit zeta envelopes and the square-loss
constant 3/(2 sqrt x). Replace the exact square loss in the lower envelope
by its arithmetic upper bound. These bounds supply the input to parity cancellation,
followed by cutoff substitution and the numerical estimates of Theorem 1.5. -/
theorem logLValue_bounds_with_bounded_square_loss {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 3 ≤ q) (hp : χ.IsPrimitive) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x : ℝ} (hx : 100 ≤ x) :
    let T :=
      Real.log (Real.log x) + Real.eulerMascheroniConstant - 1 +
        Real.eulerMascheroniConstant / Real.log x +
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass / (Real.sqrt x * (Real.log x) ^ 2) +
        1 / (3 * x ^ 3 * (Real.log x) ^ 2)
    let U :=
      Real.log x - (1 + Real.eulerMascheroniConstant) + Real.log (2 * Real.pi) / x +
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass / Real.sqrt x
    Real.log ‖χ.LFunction 1‖ ≤
        T + characterGammaLogTerm χ / Real.log x -
            (1 / Real.log x - 2 / (Real.sqrt x * (Real.log x) ^ 2)) *
              ((1 / 2 * (1 - 1 / x) * Real.log ((q : ℝ) / Real.pi) - U + reciprocalCorrection χ x) /
                (1 + 1 / Real.sqrt x) ^ 2) +
          2 / (x * (Real.log x) ^ 2) ∧
      -T - U / Real.log x + (Real.log (Real.pi ^ 2 / 6) - 3 / (2 * Real.sqrt x)) +
            characterGammaLogTerm χ / Real.log x -
          ((1 / Real.log x + 2 / (Real.sqrt x * (Real.log x) ^ 2)) / (1 - 1 / Real.sqrt x) ^ 2) *
            (1 / 2 * (1 - 1 / x) * Real.log ((q : ℝ) / Real.pi) + reciprocalCorrection χ x) -
          ((1 / Real.log x + 2 / (Real.sqrt x * (Real.log x) ^ 2)) / (1 - 1 / Real.sqrt x) ^ 2 -
              1 / Real.log x) *
            U -
          2 / (x * (Real.log x) ^ 2) ≤
        Real.log ‖χ.LFunction 1‖ := by
  have h := logLValue_bounds_with_explicit_zeta_terms χ hq hp hGRH hx
  have hs := AnalyticNumberTheory.Arithmetic.squareMangoldtCorrectionLoss_le x hx
  dsimp only at h ⊢
  exact ⟨h.1, by linarith only [h.2, hs]⟩

/-- Under GRH, a primitive character of modulus q >= 3 and x >= 100 has
explicit upper and lower logarithmic L-value bounds without parity corrections.
Insert the proved parity cancellations into the zeta and square-loss envelopes.
The remaining terms involve only q,x and fixed zeta constants, so choosing
x=(log q)^2/4 reduces Theorem 1.5 to elementary quantitative estimates. -/
theorem logLValue_bounds_without_parity {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q)
    (hp : χ.IsPrimitive) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 100 ≤ x) :
    let T :=
      Real.log (Real.log x) + Real.eulerMascheroniConstant - 1 +
        Real.eulerMascheroniConstant / Real.log x +
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass / (Real.sqrt x * (Real.log x) ^ 2) +
        1 / (3 * x ^ 3 * (Real.log x) ^ 2)
    let U :=
      Real.log x - (1 + Real.eulerMascheroniConstant) + Real.log (2 * Real.pi) / x +
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass / Real.sqrt x
    Real.log ‖χ.LFunction 1‖ ≤
        T + Real.log ((q : ℝ) / Real.pi) / (2 * Real.log x) -
          (1 / Real.log x - 2 / (Real.sqrt x * (Real.log x) ^ 2)) *
            ((1 / 2 * (1 - 1 / x) * Real.log ((q : ℝ) / Real.pi) - U) / (1 + 1 / Real.sqrt x) ^ 2) ∧
      -T + Real.log (Real.pi ^ 2 / 6) - 3 / (2 * Real.sqrt x) +
            Real.log ((q : ℝ) / Real.pi) / (2 * Real.log x) -
          ((1 / Real.log x + 2 / (Real.sqrt x * (Real.log x) ^ 2)) / (1 - 1 / Real.sqrt x) ^ 2) *
            (1 / 2 * (1 - 1 / x) * Real.log ((q : ℝ) / Real.pi) + U) ≤
        Real.log ‖χ.LFunction 1‖ := by
  have h := logLValue_bounds_with_bounded_square_loss χ hq hp hGRH hx
  have hu := reciprocalCorrection_upper_cancellation χ hx
  have hl := reciprocalCorrection_lower_cancellation χ hx
  have hg :
    characterGammaLogTerm χ =
      Real.log ((q : ℝ) / Real.pi) / 2 -
        (if χ (-1) = 1 then Real.log 2 + Real.eulerMascheroniConstant / 2
        else Real.eulerMascheroniConstant / 2) := by
    rw [characterGammaLogTerm]
    by_cases he : χ (-1) = 1
    · rw [ite_eq_left he, ite_eq_left he]
      ring
    · rw [ite_eq_right he, ite_eq_right he]
      ring
  dsimp only at h ⊢
  rw [hg] at h
  simp only [div_eq_mul_inv, mul_inv_rev] at h hu hl ⊢
  constructor
  · nlinarith only [h.1, hu]
  · nlinarith only [h.2, hl]

end PseudoPrime.LLS.PaperStatements
