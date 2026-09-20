/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ElementaryOmegaFiniteBridge
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ElementaryOmegaStatement

/-!
# Power-of-two reduction for `ElementaryOmegaFiniteStatement` certificates

To prove `m + 1 ≤ elementaryOmegaRhsReal (elementaryAnchor m)`, choose `e ≥ 4` with
`2 ^ e ≤ elementaryAnchor m`. Monotonicity reduces the goal to the power-of-two argument.
The bounds `693/1000 < log 2 < 347/500` and `log u ≤ u - 1` reduce that goal to a rational
inequality in `m`, `e`, and a split parameter `k`.
`ElementaryOmegaFiniteCertificates` uses these reductions for `1 ≤ m ≤ 162`.
-/

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

namespace ElementaryOmegaPowTwoBridgeInternal

/-- A crude rational lower bound for `Real.log 2`. -/
noncomputable def logTwoLower : ℝ :=
  693 / 1000

/-- A crude rational upper bound for `Real.log 2`. -/
noncomputable def logTwoUpper : ℝ :=
  347 / 500

theorem logTwoLower_pos : (0 : ℝ) < logTwoLower := by
  unfold logTwoLower; norm_num only

theorem logTwoLower_lt_logTwo : logTwoLower < Real.log 2 := by
  unfold logTwoLower
  linarith only [Real.log_two_gt_d9]

theorem logTwo_lt_logTwoUpper : Real.log 2 < logTwoUpper := by
  unfold logTwoUpper
  linarith only [Real.log_two_lt_d9]

/-- `exp (exp 1) < 16`, a sharper form of
`PseudoPrime.AnalyticNumberTheory.Arithmetic.exp_exp_one_lt_three_thousand` giving a small threshold
for the power-of-two domain check. -/
theorem exp_exp_one_lt_sixteen : Real.exp (Real.exp 1) < 16 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : (2.7182818286 : ℝ) < 4 * Real.log 2 := by nlinarith [Real.log_two_gt_d9]
  have h3 : Real.exp (Real.exp 1) < Real.exp (4 * Real.log 2) := Real.exp_lt_exp.mpr (h1.trans h2)
  have h4 : Real.exp ((4 : ℝ) * Real.log 2) = 16 := by
    have hpow : (4 : ℝ) * Real.log 2 = Real.log (2 ^ 4) := by
      rw [Real.log_pow]; push_cast; ring
    rw [hpow, Real.exp_log (by norm_num only)]
    norm_num only
  rwa [h4] at h3

/-- Every `2 ^ e` with `e ≥ 4` lies in
`PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryOmegaRhsReal`'s monotonicity domain. -/
theorem exp_exp_one_le_two_pow {e : ℕ} (he : 4 ≤ e) : Real.exp (Real.exp 1) ≤ (2 : ℝ) ^ e := by
  have h16 := exp_exp_one_lt_sixteen
  have hmono : (2 : ℝ) ^ 4 ≤ (2 : ℝ) ^ e := pow_le_pow_right₀ (by norm_num only) he
  norm_num only at hmono
  linarith only [h16, hmono]

/-- The elementary tangent bound `Real.log x ≤ x - 1`, applied at `x = u / 2 ^ k` and combined with
`Real.log (2 ^ k) ≤ k * logTwoUpper`, gives every positive `u` an explicit upper bound on
`log u` in terms of a free natural split parameter `k`.
This bound is rational when `u` is rational. -/
theorem log_le_powTwo_tangent {u : ℝ} (hu : 0 < u) (k : ℕ) :
    Real.log u ≤ (k : ℝ) * logTwoUpper + u / 2 ^ k - 1 := by
  have hueq : u = (2 : ℝ) ^ k * (u / 2 ^ k) := by field_simp
  have hlogu : Real.log u = (k : ℝ) * Real.log 2 + Real.log (u / 2 ^ k) := by
    conv_lhs => rw [hueq]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have htangent : Real.log (u / 2 ^ k) ≤ u / 2 ^ k - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hklog : (k : ℝ) * Real.log 2 ≤ (k : ℝ) * logTwoUpper :=
    mul_le_mul_of_nonneg_left logTwo_lt_logTwoUpper.le (by positivity)
  linarith only [hlogu, htangent, hklog]

end ElementaryOmegaPowTwoBridgeInternal

/--
Input/assumptions: natural numbers `m, e, k` with `4 ≤ e`, a power-of-two lower bound
`2 ^ e ≤ PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryAnchor m`, and the purely rational
  numeric inequality `hnum` comparing the tangent-bound upper estimate of
  `(m + 1) * log (log (2 ^ e))` against
  `PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryOmegaConstant * log (2 ^ e)`'s
  rational lower bound `elementaryOmegaConstant * e * logTwoLower`.
Conclusion: `(m + 1 : ℝ) ≤ PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryOmegaRhsReal`
  `(PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryAnchor m)`.
Content: `PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryOmegaRhsReal (2 ^ e)`
  `≤ PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryOmegaRhsReal`
  `(PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryAnchor m)` by monotonicity;
  `(m + 1) ≤ PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryOmegaRhsReal (2 ^ e)`
  follows from `hnum` by unfolding
  `PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryOmegaRhsReal` and applying the crude
  `Real.log 2` bounds plus the tangent bound for `log (log (2 ^ e)) = log (e * log 2)`.
Role: reduces each anchor certificate to a power comparison and a rational inequality,
  without evaluating logarithms of the anchor's exact integer value.
-/
theorem certificate_of_powTwo_le_anchor {m e k : ℕ} (he4 : 4 ≤ e)
    (he : (2 : ℝ) ^ e ≤ elementaryAnchor m)
    (hnum :
      ((m + 1 : ℕ) : ℝ) *
          ((k : ℝ) * ElementaryOmegaPowTwoBridgeInternal.logTwoUpper +
              (e : ℝ) * ElementaryOmegaPowTwoBridgeInternal.logTwoUpper / 2 ^ k -
            1) ≤
        elementaryOmegaConstant * ((e : ℝ) * ElementaryOmegaPowTwoBridgeInternal.logTwoLower)) :
    (m : ℝ) + 1 ≤ elementaryOmegaRhsReal (elementaryAnchor m) := by
  rw [show (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) by
      push_cast; ring]
  have hdom : Real.exp (Real.exp 1) ≤ (2 : ℝ) ^ e :=
    ElementaryOmegaPowTwoBridgeInternal.exp_exp_one_le_two_pow he4
  have hmono := elementaryOmegaRhsReal_mono hdom he
  have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast (by omega : 0 < e)
  have hlog2e :
    (e : ℝ) * ElementaryOmegaPowTwoBridgeInternal.logTwoLower ≤ Real.log ((2 : ℝ) ^ e) := by
    rw [Real.log_pow]
    exact
      mul_le_mul_of_nonneg_left ElementaryOmegaPowTwoBridgeInternal.logTwoLower_lt_logTwo.le
        hepos.le
  have he_lower : (1 : ℝ) < (e : ℝ) * ElementaryOmegaPowTwoBridgeInternal.logTwoLower := by
    have he4' : (4 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he4
    unfold ElementaryOmegaPowTwoBridgeInternal.logTwoLower
    nlinarith only [he4']
  have hlog2e_gt1 : (1 : ℝ) < Real.log ((2 : ℝ) ^ e) := he_lower.trans_le hlog2e
  have hLLpos : (0 : ℝ) < Real.log (Real.log ((2 : ℝ) ^ e)) := Real.log_pos hlog2e_gt1
  have hloglog : Real.log (Real.log ((2 : ℝ) ^ e)) = Real.log ((e : ℝ) * Real.log 2) := by
    rw [Real.log_pow]
  have hstep1 : (e : ℝ) * Real.log 2 ≤ (e : ℝ) * ElementaryOmegaPowTwoBridgeInternal.logTwoUpper :=
    mul_le_mul_of_nonneg_left ElementaryOmegaPowTwoBridgeInternal.logTwo_lt_logTwoUpper.le hepos.le
  have hstep1pos : (0 : ℝ) < (e : ℝ) * Real.log 2 := by
    have hlog2pos : (0 : ℝ) < Real.log 2 :=
      ElementaryOmegaPowTwoBridgeInternal.logTwoLower_pos.trans
        ElementaryOmegaPowTwoBridgeInternal.logTwoLower_lt_logTwo
    exact mul_pos hepos hlog2pos
  have hstep2 :
    Real.log ((e : ℝ) * Real.log 2) ≤
      Real.log ((e : ℝ) * ElementaryOmegaPowTwoBridgeInternal.logTwoUpper) :=
    Real.log_le_log hstep1pos hstep1
  have hUpos : (0 : ℝ) < ElementaryOmegaPowTwoBridgeInternal.logTwoUpper := by
    unfold ElementaryOmegaPowTwoBridgeInternal.logTwoUpper; norm_num only
  have hstep3 :=
    ElementaryOmegaPowTwoBridgeInternal.log_le_powTwo_tangent (u :=
      (e : ℝ) * ElementaryOmegaPowTwoBridgeInternal.logTwoUpper) (mul_pos hepos hUpos) k
  have hLLupper :
    Real.log (Real.log ((2 : ℝ) ^ e)) ≤
      (k : ℝ) * ElementaryOmegaPowTwoBridgeInternal.logTwoUpper +
          (e : ℝ) * ElementaryOmegaPowTwoBridgeInternal.logTwoUpper / 2 ^ k -
        1 := by
    rw [hloglog]
    linarith only [hstep2, hstep3]
  have hfinal2e : ((m + 1 : ℕ) : ℝ) ≤ elementaryOmegaRhsReal ((2 : ℝ) ^ e) := by
    unfold Arithmetic.elementaryOmegaRhsReal
    rw [le_div_iff₀ hLLpos]
    calc
      ((m + 1 : ℕ) : ℝ) * Real.log (Real.log ((2 : ℝ) ^ e)) ≤
          ((m + 1 : ℕ) : ℝ) *
            ((k : ℝ) * ElementaryOmegaPowTwoBridgeInternal.logTwoUpper +
                (e : ℝ) * ElementaryOmegaPowTwoBridgeInternal.logTwoUpper / 2 ^ k -
              1) :=
        mul_le_mul_of_nonneg_left hLLupper (by positivity)
      _ ≤ elementaryOmegaConstant * ((e : ℝ) * ElementaryOmegaPowTwoBridgeInternal.logTwoLower) :=
        hnum
      _ ≤ elementaryOmegaConstant * Real.log ((2 : ℝ) ^ e) :=
        mul_le_mul_of_nonneg_left hlog2e
          (by
            unfold elementaryOmegaConstant; norm_num only)
  exact hfinal2e.trans hmono

/--
Input/assumptions: natural numbers `m, e, k, P` with
  `PseudoPrime.NumberTheory.primePrimorialCount (m + 1) = P` (typically
  discharged by naming an existing `primePrimorialCount_cumulative_N` certificate from
  `PseudoPrime.NumberTheory.PrimorialCertificates`, letting `P` be inferred rather than restated),
  `4 ≤ e`, a power-of-two lower bound `2 ^ e ≤ 2 * P` against the *count-indexed* primorial
  (rather than `PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryAnchor m`
  itself), and the same rational `hnum` as
  `PseudoPrime.AnalyticNumberTheory.Arithmetic.certificate_of_powTwo_le_anchor`.
Conclusion: `(m : ℝ) + 1 ≤ PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryOmegaRhsReal`
  `(PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryAnchor m)`.
Content: `4 * PseudoPrime.AnalyticNumberTheory.Arithmetic.oddPrimorial m = 2 * P`
  (`PseudoPrime.AnalyticNumberTheory.Arithmetic.primePrimorialCount_succ_eq_two_mul_oddPrimorial`),
  so
  `2 ^ e ≤ 2 * P = 4 * PseudoPrime.AnalyticNumberTheory.Arithmetic.oddPrimorial m`
  `≤ PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryAnchor m` via `le_max_left`;
  then delegate to
  `PseudoPrime.AnalyticNumberTheory.Arithmetic.certificate_of_powTwo_le_anchor`.
Role: lets certificates infer the primorial numeral `P` from `hP`. There is no lower bound on
  `m` in this theorem. The generated certificates use it for `m ≥ 5`; the certificates for
  `m = 1, 2, 3, 4` use `certificate_of_powTwo_le_anchor` directly. The anchor is `3000` for
  `m = 1, 2, 3`, whereas `4 * oddPrimorial 4 = 4620 > 3000`.
-/
theorem certificate_of_primorial {m e k P : ℕ} (hP : NumberTheory.primePrimorialCount (m + 1) = P)
    (he4 : 4 ≤ e) (heP : (2 : ℝ) ^ e ≤ 2 * (P : ℝ))
    (hnum :
      ((m + 1 : ℕ) : ℝ) *
          ((k : ℝ) * ElementaryOmegaPowTwoBridgeInternal.logTwoUpper +
              (e : ℝ) * ElementaryOmegaPowTwoBridgeInternal.logTwoUpper / 2 ^ k -
            1) ≤
        elementaryOmegaConstant * ((e : ℝ) * ElementaryOmegaPowTwoBridgeInternal.logTwoLower)) :
    (m : ℝ) + 1 ≤ elementaryOmegaRhsReal (elementaryAnchor m) := by
  apply certificate_of_powTwo_le_anchor he4 _ hnum
  have h := primePrimorialCount_succ_eq_two_mul_oddPrimorial m
  rw [hP] at h
  have hR : (P : ℝ) = 2 * (oddPrimorial m : ℝ) := by exact_mod_cast h
  unfold elementaryAnchor
  calc
    (2 : ℝ) ^ e ≤ 2 * (P : ℝ) := heP
    _ = 4 * (oddPrimorial m : ℝ) := by
      rw [hR]; ring
    _ ≤ max ((4 : ℝ) * (oddPrimorial m : ℝ)) 3000 := le_max_left _ _

end PseudoPrime.AnalyticNumberTheory.Arithmetic
