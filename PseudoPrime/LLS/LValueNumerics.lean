/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.LogLValueBounds
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMassBounds

/-!
# Numerical conversion of the logarithmic bounds for L-values

At `x = (log q)^2 / 4` and `q ≥ 10^10`, rational polynomial certificates simplify
the two logarithmic envelopes. Certified exponential estimates give the upper norm
and reciprocal norm bounds of Theorem 1.5 with its stated factors and constants.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For q >= 10^10, the logarithmic cutoff (log q)^2/4 is at least 128,
its square root is log q/2, and its logarithm is 2(log log q-log 2).
Use certified log 2 and log 5 bounds to obtain log q >= 23. These identities
justify substituting the paper's cutoff into the parity-free estimates. -/
theorem lValue_log_cutoff_bounds (q : ℕ) (hq : 10 ^ 10 ≤ q) :
    23 ≤ Real.log (q : ℝ) ∧
      128 ≤ (Real.log (q : ℝ)) ^ 2 / 4 ∧
      Real.sqrt ((Real.log (q : ℝ)) ^ 2 / 4) = Real.log (q : ℝ) / 2 ∧
      Real.log ((Real.log (q : ℝ)) ^ 2 / 4) = 2 * (Real.log (Real.log (q : ℝ)) - Real.log 2) := by
  have hqR : (10 : ℝ) ^ 10 ≤ q := by exact_mod_cast hq
  have hq0 : 0 < (q : ℝ) := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 10 ^ 10) hqR
  have h := Real.log_le_log (by norm_num only : (0 : ℝ) < 10 ^ 10) hqR
  rw [Real.log_pow, Real.log_ten_eq] at h
  norm_num only [Nat.cast_ofNat] at h
  have hl : (23 : ℝ) ≤ Real.log (q : ℝ) := by
    linarith only [h, Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hl0 : 0 < Real.log (q : ℝ) := by linarith only [hl]
  have hs : Real.sqrt ((Real.log (q : ℝ)) ^ 2 / 4) = Real.log (q : ℝ) / 2 := by
    rw [show (Real.log (q : ℝ)) ^ 2 / 4 = (Real.log (q : ℝ) / 2) ^ 2 by ring,
      Real.sqrt_sq (div_nonneg hl0.le (by norm_num only))]
  have he :
    Real.log ((Real.log (q : ℝ)) ^ 2 / 4) = 2 * (Real.log (Real.log (q : ℝ)) - Real.log 2) := by
    rw [Real.log_div (pow_ne_zero 2 (ne_of_gt hl0)) (by norm_num only : (4 : ℝ) ≠ 0), Real.log_pow,
      Real.log_four_eq]
    norm_num only [Nat.cast_ofNat]
    ring
  exact ⟨hl, by nlinarith only [hl], hs, he⟩

/-- Under GRH and for a primitive character modulo q >= 10^10, specialize
the parity-free logarithmic L-value estimates to x=(log q)^2/4. The cutoff
bounds ensure x ≥ 100, so the parity cancellation estimates apply.
These envelopes are the inputs to the rational certificates and exponential
conversions that give the explicit constants of Theorem 1.5. -/
theorem logLValue_bounds_at_log_cutoff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 10 ^ 10 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    let x := (Real.log (q : ℝ)) ^ 2 / 4
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
  have hq3 : 3 ≤ q := le_trans (by norm_num only : (3 : ℕ) ≤ 10 ^ 10) hq
  have hx : 100 ≤ (Real.log (q : ℝ)) ^ 2 / 4 :=
    le_trans (by norm_num only : (100 : ℝ) ≤ 128) (lValue_log_cutoff_bounds q hq).2.1
  exact logLValue_bounds_without_parity χ hq3 hp hGRH hx

/-- For 0 ≤ u ≤ 25/122, bound the positive polynomial controlling the fifth-order
exponential remainder by 31/10. Monotonicity of powers reduces the claim to
rational arithmetic, supplying the coefficient in the L-value upper bound. -/
private theorem exponential_correction_polynomial (u : ℝ) (hu : 0 ≤ u) (hb : u ≤ 25 / 122) :
    2 + (1 + 2 * u) ^ 2 / 2 + u * (1 + 2 * u) ^ 3 / 6 + u ^ 2 * (1 + 2 * u) ^ 4 / 24 +
        u ^ 3 * (1 + 2 * u) ^ 5 / 100 ≤
      31 / 10 := by
  have h2 := pow_le_pow_left₀ hu hb 2
  have h3 := pow_le_pow_left₀ hu hb 3
  have h4 := pow_le_pow_left₀ hu hb 4
  have h5 := pow_le_pow_left₀ hu hb 5
  have h6 := pow_le_pow_left₀ hu hb 6
  have h7 := pow_le_pow_left₀ hu hb 7
  have h8 := pow_le_pow_left₀ hu hb 8
  norm_num only at h2 h3 h4 h5 h6 h7 h8
  nlinarith only [hb, h2, h3, h4, h5, h6, h7, h8]

/-- For 0 ≤ u ≤ 25/122, the fifth-order Taylor bound gives
exp(u+2u²) ≤ 1+u+3.1u². The polynomial estimate controls the remainder;
this supplies the exponential conversion of the logarithmic L-value bound. -/
theorem exponential_lValue_correction (u : ℝ) (hu : 0 ≤ u) (hb : u ≤ 25 / 122) :
    Real.exp (u + 2 * u ^ 2) ≤ 1 + u + 31 / 10 * u ^ 2 := by
  have ht0 : 0 ≤ u + 2 * u ^ 2 := by positivity
  have ht1 : u + 2 * u ^ 2 ≤ 1 := by
    have h2 := pow_le_pow_left₀ hu hb 2
    norm_num only at h2
    nlinarith only [hb, h2]
  have he := Real.exp_bound' ht0 ht1 (by norm_num only : 0 < (5 : ℕ))
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    pow_zero, pow_one, div_one, zero_add] at he
  have hp := exponential_correction_polynomial u hu hb
  have hm := mul_le_mul_of_nonneg_right hp (sq_nonneg u)
  nlinarith only [he, hm]

/-- For l ≥ 122/25, bound exp(1/l+2/l²) by 1+1/l+3.1/l².
Apply the reciprocal-variable estimate; this is the numerical conversion
needed after the explicit logarithmic upper envelope is simplified. -/
theorem exponential_lValue_log_correction (l : ℝ) (hl : 122 / 25 ≤ l) :
    Real.exp (1 / l + 2 / l ^ 2) ≤ 1 + 1 / l + 31 / (10 * l ^ 2) := by
  have hl0 : 0 < l := by linarith only [hl]
  have hu : 0 ≤ 1 / l := one_div_nonneg.mpr hl0.le
  have hb : 1 / l ≤ 25 / 122 := by
    apply (div_le_iff₀ hl0).mpr
    nlinarith only [hl]
  have he := exponential_lValue_correction (1 / l) hu hb
  convert he using 1 <;> congr 1 <;> field_simp [ne_of_gt hl0]

/-- Certify log(23/2) ≥ 61/25 by a sixth-order exponential estimate at 11/25
and the certified value of exp(1). This avoids an unproved decimal logarithm
when establishing the cutoff required by the exponential L-value estimate. -/
private theorem logarithmic_cutoff_threshold : (61 / 25 : ℝ) ≤ Real.log (23 / 2) := by
  have he :=
    Real.exp_bound' (by norm_num only : (0 : ℝ) ≤ 11 / 25) (by norm_num only : (11 / 25 : ℝ) ≤ 1)
      (by norm_num only : 0 < (6 : ℕ))
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    pow_zero, pow_one, div_one, zero_add] at he
  have h1 : Real.exp 1 ≤ (2719 / 1000 : ℝ) := by linarith only [Real.exp_one_lt_d9]
  have h2 := mul_le_mul h1 h1 (Real.exp_pos 1).le (by norm_num only : (0 : ℝ) ≤ 2719 / 1000)
  have h3 :=
    mul_le_mul h2 he (Real.exp_pos (11 / 25)).le
      (by norm_num only : (0 : ℝ) ≤ (2719 / 1000) * (2719 / 1000))
  apply (Real.le_log_iff_exp_le (by norm_num only : (0 : ℝ) < 23 / 2)).mpr
  rw [show (61 / 25 : ℝ) = (1 + 1) + 11 / 25 by norm_num only, Real.exp_add, Real.exp_add]
  norm_num only at h3
  linarith only [h3]

/-- For q ≥ 10^10, the logarithm of the paper's cutoff is at least 122/25.
Combine log q ≥ 23 with the certified logarithm threshold and log of a square.
This verifies the domain of the exponential L-value conversion. -/
theorem lValue_log_cutoff_log_lower (q : ℕ) (hq : 10 ^ 10 ≤ q) :
    (122 / 25 : ℝ) ≤ Real.log ((Real.log (q : ℝ)) ^ 2 / 4) := by
  have hb := lValue_log_cutoff_bounds q hq
  have hy : (23 / 2 : ℝ) ≤ Real.log (q : ℝ) / 2 := by linarith only [hb.1]
  have hm := Real.log_le_log (by norm_num only : (0 : ℝ) < 23 / 2) hy
  have ht := logarithmic_cutoff_threshold
  have hl : 0 < Real.log (q : ℝ) := by linarith only [hb.1]
  have he : Real.log ((Real.log (q : ℝ)) ^ 2 / 4) = 2 * Real.log (Real.log (q : ℝ) / 2) := by
    rw [show (Real.log (q : ℝ)) ^ 2 / 4 = (Real.log (q : ℝ) / 2) ^ 2 by ring, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  rw [he]
  linarith only [hm, ht]

/-- For q ≥ 10^10 and l=log((log q)²/4), the exponential coefficient
l+1+3.1/l is at most twice the upper factor of Theorem 1.5. Use the cutoff
threshold and the certified bound log 2 ≤ 0.7 to compare the reciprocals.
This connects the numerical exponential estimate to the original statement. -/
theorem lValue_upper_factor_of_log_cutoff (q : ℕ) (hq : 10 ^ 10 ≤ q) :
    let l := Real.log ((Real.log (q : ℝ)) ^ 2 / 4)
    l + 1 + 31 / (10 * l) ≤ 2 * lValueUpperFactor q := by
  let l := Real.log ((Real.log (q : ℝ)) ^ 2 / 4)
  have hl := lValue_log_cutoff_log_lower q hq
  change 122 / 25 ≤ l at hl
  have hl0 : 0 < l := by linarith only [hl]
  have hk0 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have hk : Real.log 2 ≤ 7 / 10 := by linarith only [Real.log_two_lt_d9]
  have hd : 0 < l + 2 * Real.log 2 := by linarith only [hl0, hk0]
  have hc : 31 / (10 * l) ≤ 4 / (l + 2 * Real.log 2) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 10 * l) hd).mpr
    nlinarith only [hl, hk]
  have he := (lValue_log_cutoff_bounds q hq).2.2.2
  change l = 2 * (Real.log (Real.log (q : ℝ)) - Real.log 2) at he
  change l + 1 + 31 / (10 * l) ≤ 2 * lValueUpperFactor q
  dsimp only [lValueUpperFactor]
  have ht : Real.log (Real.log (q : ℝ)) = (l + 2 * Real.log 2) / 2 := by linarith only [he]
  rw [ht]
  field_simp [ne_of_gt hl0, ne_of_gt hd] at hc ⊢
  nlinarith only [hc]

/-- For q ≥ 10^10 and a positive value v, the simplified logarithmic upper
bound implies v ≤ 2 exp(γ) times the original L-value upper factor.
Exponentiate the premise, use the certified 3.1 remainder, and compare the
cutoff expression with the paper's factor. This conversion applies to any positive
real v; the character-specific logarithmic estimate supplies its premise. -/
theorem lValue_upper_bound_of_log_bound (q : ℕ) (hq : 10 ^ 10 ≤ q) (v : ℝ) (hv : 0 < v)
    (hb :
      Real.log v ≤
        Real.log (Real.log ((Real.log (q : ℝ)) ^ 2 / 4)) + Real.eulerMascheroniConstant +
          1 / Real.log ((Real.log (q : ℝ)) ^ 2 / 4) +
          2 / (Real.log ((Real.log (q : ℝ)) ^ 2 / 4)) ^ 2) :
    v ≤ 2 * Real.exp Real.eulerMascheroniConstant * lValueUpperFactor q := by
  let l := Real.log ((Real.log (q : ℝ)) ^ 2 / 4)
  have hl := lValue_log_cutoff_log_lower q hq
  change 122 / 25 ≤ l at hl
  have hl0 : 0 < l := by linarith only [hl]
  have he := exponential_lValue_log_correction l hl
  have hf := lValue_upper_factor_of_log_cutoff q hq
  change l + 1 + 31 / (10 * l) ≤ 2 * lValueUpperFactor q at hf
  have hm :=
    mul_le_mul_of_nonneg_left he (mul_nonneg hl0.le (Real.exp_pos Real.eulerMascheroniConstant).le)
  have hh := Real.exp_le_exp.mpr hb
  change
    Real.exp (Real.log v) ≤
      Real.exp (Real.log l + Real.eulerMascheroniConstant + 1 / l + 2 / l ^ 2) at hh
  rw [Real.exp_log hv] at hh
  rw [show
      Real.log l + Real.eulerMascheroniConstant + 1 / l + 2 / l ^ 2 =
        (Real.log l + Real.eulerMascheroniConstant) + (1 / l + 2 / l ^ 2)
      by ring,
    Real.exp_add, Real.exp_add, Real.exp_log hl0] at hh
  have hi := mul_le_mul_of_nonneg_left hf (Real.exp_pos Real.eulerMascheroniConstant).le
  have hr :
    l * Real.exp Real.eulerMascheroniConstant * (1 + 1 / l + 31 / (10 * l ^ 2)) =
      Real.exp Real.eulerMascheroniConstant * (l + 1 + 31 / (10 * l)) := by
    field_simp [ne_of_gt hl0]
  rw [hr] at hm
  nlinarith only [hh, hm, hi]

/-- For y ≥ 10 and l ≥ 2, the polynomial controlling the cleared upper-envelope
numerator is nonnegative. Bound y² by y⁵ and separate the remaining positive
terms; this is the rational certificate used in the logarithmic upper bound. -/
private theorem upper_envelope_polynomial_nonneg (y l : ℝ) (hy : 10 ≤ y) (hl : 2 ≤ l) :
    0 ≤
      48 * l ^ 2 * y ^ 7 + 24 * l ^ 2 * y ^ 6 + l * y ^ 6 * (37 * y - 16) + 37 * y ^ 7 +
          96 * y ^ 6 +
          69 * y ^ 5 -
        8 * (y + 1) ^ 2 := by
  have hy0 : 0 ≤ y := by linarith only [hy]
  have hl0 : 0 ≤ l := by linarith only [hl]
  have hpow : y ^ 2 ≤ y ^ 5 :=
    pow_le_pow_right₀ (by linarith only [hy] : 1 ≤ y) (by norm_num only : (2 : ℕ) ≤ 5)
  have ht : 0 ≤ 69 * y ^ 5 - 8 * (y + 1) ^ 2 := by nlinarith only [hpow, hy]
  have hm : 0 ≤ 37 * y - 16 := by linarith only [hy]
  have hs :
    0 ≤
      48 * l ^ 2 * y ^ 7 + 24 * l ^ 2 * y ^ 6 + l * y ^ 6 * (37 * y - 16) + 37 * y ^ 7 +
        96 * y ^ 6 := by
    positivity
  linarith only [hs, ht]

/-- For real y ≥ 10, l ≥ 2, g ≤ 2/3, b ≥ 1, k ≤ 1 and m ≤ 1/16,
the normalized upper envelope is at most 1/l+2/l². Clear the positive
denominator and bound each coefficient by its rational extremum; the remaining
polynomial is nonnegative. Substituting γ, log π, log 2 and the Riemann zero mass
for g,b,k,m simplifies the GRH logarithmic L-value estimate. -/
private theorem logarithmic_upper_envelope_bound (y l g b k m : ℝ) (hy : 10 ≤ y) (hl : 2 ≤ l)
    (hg : g ≤ 2 / 3) (hb : 1 ≤ b) (hk : k ≤ 1) (hm : m ≤ 1 / 16) :
    -1 + g / l + 2 * m / (y * l ^ 2) + 1 / (3 * y ^ 6 * l ^ 2) + (y - b / 2) / l -
        (1 / l - 2 / (y * l ^ 2)) *
          (((1 - 1 / y ^ 2) * (y - b / 2) - (l - 1 - g + (k + b) / y ^ 2 + 2 * m / y)) /
            (1 + 1 / y) ^ 2) ≤
      1 / l + 2 / l ^ 2 := by
  have hy0 : 0 < y := by linarith only [hy]
  have hl0 : 0 < l := by linarith only [hl]
  have hyp : 0 < y + 1 := by linarith only [hy]
  have hly : 2 ≤ l * y := by nlinarith only [hy, hl]
  let A := l * y ^ 2 + y ^ 2 + 1
  let G := 2 * l * y + l + 2 * y
  let K := l * y - 2
  have hA : 0 ≤ A := by
    dsimp only [A]; positivity
  have hG : 0 ≤ G := by
    dsimp only [G]; positivity
  have hK : 0 ≤ K := by
    dsimp only [K]; linarith only [hly]
  have hB :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith only [hb] : 1 - b ≤ 0)
      (mul_nonneg (by positivity : 0 ≤ 3 * y ^ 5) hA)
  have hGamma :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith only [hg] : g - 2 / 3 ≤ 0)
      (mul_nonneg (by positivity : 0 ≤ 3 * y ^ 6) hG)
  have hLog :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith only [hk] : k - 1 ≤ 0)
      (mul_nonneg (by positivity : 0 ≤ 3 * y ^ 5) hK)
  have hMass :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith only [hm] : m - 1 / 16 ≤ 0)
      (mul_nonneg (by positivity : 0 ≤ 6 * y ^ 5) hA)
  have hP := upper_envelope_polynomial_nonneg y l hy hl
  let N :=
    -3 * b * y ^ 5 * A + 3 * g * y ^ 6 * G + 3 * k * y ^ 5 * K + 6 * m * y ^ 5 * A -
        6 * l ^ 2 * y ^ 7 -
        3 * l ^ 2 * y ^ 6 -
        6 * l * y ^ 7 -
        3 * l * y ^ 6 -
        6 * y ^ 7 -
        12 * y ^ 6 +
      y ^ 2 +
      2 * y +
      1
  have hN : N ≤ 0 := by
    dsimp only [N, A, G, K] at hB hGamma hLog hMass ⊢
    nlinarith only [hB, hGamma, hLog, hMass, hP]
  have hId :
    (-1 + g / l + 2 * m / (y * l ^ 2) + 1 / (3 * y ^ 6 * l ^ 2) + (y - b / 2) / l -
          (1 / l - 2 / (y * l ^ 2)) *
            (((1 - 1 / y ^ 2) * (y - b / 2) - (l - 1 - g + (k + b) / y ^ 2 + 2 * m / y)) /
              (1 + 1 / y) ^ 2) -
          (1 / l + 2 / l ^ 2)) *
        (3 * y ^ 6 * l ^ 2 * (y + 1) ^ 2) =
      N := by
    dsimp only [N, A, G, K]
    field_simp [ne_of_gt hy0, ne_of_gt hl0, ne_of_gt hyp]
    ring
  have hD : 0 < 3 * y ^ 6 * l ^ 2 * (y + 1) ^ 2 := by positivity
  nlinarith only [hN, hId, hD]

/-- For a primitive character modulo q ≥ 10^10 under GRH, the logarithm of
the L-value is at most log log x+γ+1/log x+2/(log x)² at x=(log q)²/4.
Substitute the cutoff into the parity-free envelope and apply the rational
certificate using the certified zero-mass and elementary constant bounds.
This supplies the analytic premise for the upper half of Theorem 1.5. -/
theorem logLValue_upper_bound_at_log_cutoff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 10 ^ 10 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    let x := (Real.log (q : ℝ)) ^ 2 / 4
    Real.log ‖χ.LFunction 1‖ ≤
      Real.log (Real.log x) + Real.eulerMascheroniConstant + 1 / Real.log x +
        2 / (Real.log x) ^ 2 := by
  let y := Real.log (q : ℝ) / 2
  let x := (Real.log (q : ℝ)) ^ 2 / 4
  let l := Real.log x
  have hb := lValue_log_cutoff_bounds q hq
  have hy : 10 ≤ y := by
    dsimp only [y]; linarith only [hb.1]
  have hy0 : 0 < y := by linarith only [hy]
  have hx : x = y ^ 2 := by
    dsimp only [x, y]; ring
  have hs : Real.sqrt x = y := hb.2.2.1
  have hl : 2 ≤ l := by
    have ht := lValue_log_cutoff_log_lower q hq
    change 122 / 25 ≤ l at ht
    linarith only [ht]
  have hl0 : 0 < l := by linarith only [hl]
  have hpi : 1 ≤ Real.log Real.pi := by
    have hm := Real.log_le_log (by norm_num only : (0 : ℝ) < 3) Real.pi_gt_three.le
    linarith only [hm, Real.log_three_gt_d9]
  have hk : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
  have hq0 : 0 < (q : ℝ) := by
    have hqR : (10 : ℝ) ^ 10 ≤ q := by exact_mod_cast hq
    linarith only [hqR]
  have hlog : Real.log ((q : ℝ) / Real.pi) = 2 * y - Real.log Real.pi := by
    rw [Real.log_div (ne_of_gt hq0) (ne_of_gt Real.pi_pos)]
    dsimp only [y]
    ring
  have hlog2 : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) (ne_of_gt Real.pi_pos)
  have hr :=
    logarithmic_upper_envelope_bound y l Real.eulerMascheroniConstant (Real.log Real.pi)
      (Real.log 2) AnalyticNumberTheory.RiemannXi.riemannZeroMass hy hl
      Real.eulerMascheroniConstant_lt_two_thirds.le hpi hk
      AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_one_sixteenth
  have hh := (logLValue_bounds_at_log_cutoff χ hq hp hGRH).1
  change Real.log ‖χ.LFunction 1‖ ≤ Real.log l + Real.eulerMascheroniConstant + 1 / l + 2 / l ^ 2
  change
    Real.log ‖χ.LFunction 1‖ ≤
      Real.log l + Real.eulerMascheroniConstant - 1 + Real.eulerMascheroniConstant / l +
          2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass / (Real.sqrt x * l ^ 2) +
          1 / (3 * x ^ 3 * l ^ 2) +
          Real.log ((q : ℝ) / Real.pi) / (2 * l) -
        (1 / l - 2 / (Real.sqrt x * l ^ 2)) *
          ((1 / 2 * (1 - 1 / x) * Real.log ((q : ℝ) / Real.pi) -
              (l - (1 + Real.eulerMascheroniConstant) + Real.log (2 * Real.pi) / x +
                2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass / Real.sqrt x)) /
            (1 + 1 / Real.sqrt x) ^ 2) at hh
  rw [hs, hx, hlog, hlog2] at hh
  simp only [← pow_mul, div_eq_mul_inv, mul_inv_rev] at hh hr ⊢
  nlinarith only [hh, hr]

/-- Under GRH, every primitive character modulo q ≥ 10^10 satisfies the upper
L-value inequality of Theorem 1.5. The analytic logarithmic estimate and the
certified exponential conversion yield the original factor; nonvanishing on
Re(s)=1 permits exponentiating log of the norm. -/
theorem lValue_upper_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 10 ^ 10 ≤ q)
    (hp : χ.IsPrimitive) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ‖χ.LFunction 1‖ ≤ 2 * Real.exp Real.eulerMascheroniConstant * lValueUpperFactor q := by
  have hq3 : 3 ≤ q := le_trans (by norm_num only : (3 : ℕ) ≤ 10 ^ 10) hq
  have hne := primitiveCharacter_ne_one_of_three_le hq3 hp
  have hv :=
    norm_pos_iff.mpr
      (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (s := 1) (Or.inl hne)
        (by norm_num only [Complex.one_re]))
  exact
    lValue_upper_bound_of_log_bound q hq ‖χ.LFunction 1‖ hv
      (logLValue_upper_bound_at_log_cutoff χ hq hp hGRH)

/-- For y ≥ 23/2 and l ≥ 122/25, the cleared lower-envelope polynomial is
nonnegative. Translate both variables to their nonnegative distances from the
cutoff thresholds; all coefficients in the resulting polynomial are positive.
This supplies the rational certificate for the logarithmic lower L-value bound. -/
private theorem lower_envelope_polynomial_nonneg (y l : ℝ) (hy : 23 / 2 ≤ y) (hl : 122 / 25 ≤ l) :
    0 ≤
      (12 * l ^ 2 * y ^ 7 - 96 * l ^ 2 * y ^ 6 + 60 * l ^ 2 * y ^ 5 - 3 * l * y ^ 7 -
                  60 * l * y ^ 6 -
                  3 * y ^ 7 +
                96 * y ^ 6 -
              123 * y ^ 5 -
              8 * y ^ 2 +
            16 * y -
          8) /
        4 := by
  let v := y - 23 / 2
  let t := l - 122 / 25
  have hv : 0 ≤ v := by
    dsimp only [v]; linarith only [hy]
  have ht : 0 ≤ t := by
    dsimp only [t]; linarith only [hl]
  rw [show y = v + 23 / 2 by
      dsimp only [v]; ring,
    show l = t + 122 / 25 by
      dsimp only [t]; ring]
  ring_nf
  positivity

/-- For y ≥ 23/2, l ≥ 122/25, g ≥ 1/2, b ≥ 1, k ≤ 1 and m ≤ 1/16,
the normalized lower envelope is nonnegative. Clear its
positive denominator and reduce the constant coefficients to the polynomial
certificate. Substituting γ, log π, log 2 and the Riemann zero mass for g,b,k,m
controls the reciprocal L-value inequality of Theorem 1.5. -/
private theorem logarithmic_lower_envelope_bound (y l g b k m : ℝ) (hy : 23 / 2 ≤ y)
    (hl : 122 / 25 ≤ l) (hg : 1 / 2 ≤ g) (hb : 1 ≤ b) (hk : k ≤ 1) (hm : m ≤ 1 / 16) :
    0 ≤
      1 - g / l - 2 * m / (y * l ^ 2) - 1 / (3 * y ^ 6 * l ^ 2) + 5 / (2 * y) + (y - b / 2) / l -
          ((1 / l + 2 / (y * l ^ 2)) / (1 - 1 / y) ^ 2) *
            ((1 - 1 / y ^ 2) * (y - b / 2) + (l - 1 - g + (k + b) / y ^ 2 + 2 * m / y)) +
        1 / l +
        2 / l ^ 2 := by
  have hy0 : 0 < y := by linarith only [hy]
  have hl0 : 0 < l := by linarith only [hl]
  have hym : 0 < y - 1 := by linarith only [hy]
  let A := l * y ^ 2 + y ^ 2 + 1
  let B := l * y ^ 2 - 2 * l * y + y ^ 2 - 3
  let G := 2 * l * y - l + 2 * y
  let K := l * y + 2
  have hA : 0 ≤ A := by
    dsimp only [A]; positivity
  have hB : 0 ≤ B := by
    have hyy : 2 * y ≤ y ^ 2 := by nlinarith only [hy]
    have hprod := mul_nonneg hl0.le (sub_nonneg.mpr hyy)
    dsimp only [B]
    nlinarith only [hprod, hy]
  have hG : 0 ≤ G := by
    have hprod := mul_nonneg hl0.le (by linarith only [hy] : 0 ≤ 2 * y - 1)
    dsimp only [G]
    nlinarith only [hprod, hy]
  have hK : 0 ≤ K := by
    dsimp only [K]; positivity
  have hBeta :=
    mul_nonneg (by linarith only [hb] : 0 ≤ b - 1) (mul_nonneg (by positivity : 0 ≤ 6 * y ^ 5) hB)
  have hGamma :=
    mul_nonneg (by linarith only [hg] : 0 ≤ g - 1 / 2)
      (mul_nonneg (by positivity : 0 ≤ 6 * y ^ 6) hG)
  have hLog :=
    mul_nonneg (by linarith only [hk] : 0 ≤ 1 - k) (mul_nonneg (by positivity : 0 ≤ 6 * y ^ 5) hK)
  have hMass :=
    mul_nonneg (by linarith only [hm] : 0 ≤ 1 / 16 - m)
      (mul_nonneg (by positivity : 0 ≤ 12 * y ^ 5) hA)
  have hP := lower_envelope_polynomial_nonneg y l hy hl
  let N :=
    6 * b * y ^ 5 * B + 6 * g * y ^ 6 * G - 6 * k * y ^ 5 * K - 12 * m * y ^ 5 * A +
                        3 * l ^ 2 * y ^ 7 -
                      24 * l ^ 2 * y ^ 6 +
                    15 * l ^ 2 * y ^ 5 -
                  12 * l * y ^ 7 +
                6 * l * y ^ 6 -
              12 * y ^ 7 +
            24 * y ^ 6 -
          2 * y ^ 2 +
        4 * y -
      2
  have hN : 0 ≤ N := by
    dsimp only [N, A, B, G, K] at hBeta hGamma hLog hMass ⊢
    nlinarith only [hBeta, hGamma, hLog, hMass, hP]
  have hId :
    (1 - g / l - 2 * m / (y * l ^ 2) - 1 / (3 * y ^ 6 * l ^ 2) + 5 / (2 * y) + (y - b / 2) / l -
            ((1 / l + 2 / (y * l ^ 2)) / (1 - 1 / y) ^ 2) *
              ((1 - 1 / y ^ 2) * (y - b / 2) + (l - 1 - g + (k + b) / y ^ 2 + 2 * m / y)) +
          1 / l +
          2 / l ^ 2) *
        (6 * y ^ 6 * l ^ 2 * (y - 1) ^ 2) =
      N := by
    dsimp only [N, A, B, G, K]
    field_simp [ne_of_gt hy0, ne_of_gt hl0, ne_of_gt hym]
    ring
  have hD : 0 < 6 * y ^ 6 * l ^ 2 * (y - 1) ^ 2 := by positivity
  nlinarith only [hN, hId, hD]

/-- For a primitive character modulo q ≥ 10^10 under GRH, the logarithmic
L-value is bounded below by -log log x-γ+log(π²/6)-1/log x-2/(log x)²-4/√x
at x=(log q)²/4. Apply the rational lower certificate to the parity-free
estimate. This is the analytic input for the reciprocal bound of Theorem 1.5. -/
theorem logLValue_lower_bound_at_log_cutoff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 10 ^ 10 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    let x := (Real.log (q : ℝ)) ^ 2 / 4
    (-Real.log (Real.log x) - Real.eulerMascheroniConstant + Real.log (Real.pi ^ 2 / 6) -
        1 / Real.log x -
        2 / (Real.log x) ^ 2 -
        4 / Real.sqrt x) ≤
      Real.log ‖χ.LFunction 1‖ := by
  let y := Real.log (q : ℝ) / 2
  let x := (Real.log (q : ℝ)) ^ 2 / 4
  let l := Real.log x
  have hb := lValue_log_cutoff_bounds q hq
  have hy : 23 / 2 ≤ y := by
    dsimp only [y]; linarith only [hb.1]
  have hy0 : 0 < y := by linarith only [hy]
  have hx : x = y ^ 2 := by
    dsimp only [x, y]; ring
  have hs : Real.sqrt x = y := hb.2.2.1
  have hl : 122 / 25 ≤ l := lValue_log_cutoff_log_lower q hq
  have hl0 : 0 < l := by linarith only [hl]
  have hpi : 1 ≤ Real.log Real.pi := by
    have hm := Real.log_le_log (by norm_num only : (0 : ℝ) < 3) Real.pi_gt_three.le
    linarith only [hm, Real.log_three_gt_d9]
  have hk : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
  have hq0 : 0 < (q : ℝ) := by
    have hqR : (10 : ℝ) ^ 10 ≤ q := by exact_mod_cast hq
    linarith only [hqR]
  have hlog : Real.log ((q : ℝ) / Real.pi) = 2 * y - Real.log Real.pi := by
    rw [Real.log_div (ne_of_gt hq0) (ne_of_gt Real.pi_pos)]
    dsimp only [y]
    ring
  have hlog2 : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) (ne_of_gt Real.pi_pos)
  have hr :=
    logarithmic_lower_envelope_bound y l Real.eulerMascheroniConstant (Real.log Real.pi)
      (Real.log 2) AnalyticNumberTheory.RiemannXi.riemannZeroMass hy hl
      Real.one_half_lt_eulerMascheroniConstant.le hpi hk
      AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_one_sixteenth
  have hh := (logLValue_bounds_at_log_cutoff χ hq hp hGRH).2
  change
    -Real.log l - Real.eulerMascheroniConstant + Real.log (Real.pi ^ 2 / 6) - 1 / l - 2 / l ^ 2 -
        4 / Real.sqrt x ≤
      Real.log ‖χ.LFunction 1‖
  change
    -(Real.log l + Real.eulerMascheroniConstant - 1 + Real.eulerMascheroniConstant / l +
                  2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass / (Real.sqrt x * l ^ 2) +
                  1 / (3 * x ^ 3 * l ^ 2)) +
              Real.log (Real.pi ^ 2 / 6) -
            3 / (2 * Real.sqrt x) +
          Real.log ((q : ℝ) / Real.pi) / (2 * l) -
        ((1 / l + 2 / (Real.sqrt x * l ^ 2)) / (1 - 1 / Real.sqrt x) ^ 2) *
          (1 / 2 * (1 - 1 / x) * Real.log ((q : ℝ) / Real.pi) +
            (l - (1 + Real.eulerMascheroniConstant) + Real.log (2 * Real.pi) / x +
              2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass / Real.sqrt x)) ≤
      Real.log ‖χ.LFunction 1‖ at hh
  rw [hs, hx, hlog, hlog2] at hh
  rw [hs]
  simp only [← pow_mul, div_eq_mul_inv, mul_inv_rev] at hh hr ⊢
  nlinarith only [hh, hr]

/-- For 0 ≤ z ≤ 2/23, bound the positive Taylor coefficient by five.
Monotonicity of powers reduces the estimate to rational arithmetic; this
controls the exponential of the reciprocal cutoff error. -/
private theorem reciprocal_exponential_polynomial (z : ℝ) (hz : 0 ≤ z) (hb : z ≤ 2 / 23) :
    4 + 8 * z + 32 / 3 * z ^ 2 + 32 / 3 * z ^ 3 + 256 / 25 * z ^ 4 ≤ 5 := by
  have h2 := pow_le_pow_left₀ hz hb 2
  have h3 := pow_le_pow_left₀ hz hb 3
  have h4 := pow_le_pow_left₀ hz hb 4
  norm_num only at h2 h3 h4
  nlinarith only [hb, h2, h3, h4]

/-- For y ≥ 23/2, exp(4/y) ≤ 1+5/y. Apply the fifth-order exponential
remainder and the coefficient certificate. This converts the lower logarithmic
L-value error into the explicit reciprocal-factor correction. -/
theorem exponential_reciprocal_cutoff_correction (y : ℝ) (hy : 23 / 2 ≤ y) :
    Real.exp (4 / y) ≤ 1 + 5 / y := by
  have hy0 : 0 < y := by linarith only [hy]
  have hz : 0 ≤ 1 / y := one_div_nonneg.mpr hy0.le
  have hb : 1 / y ≤ 2 / 23 := by
    apply (div_le_iff₀ hy0).mpr
    nlinarith only [hy]
  have ht : 4 / y ≤ 1 := by
    apply (div_le_iff₀ hy0).mpr
    linarith only [hy]
  have he :=
    Real.exp_bound' (div_nonneg (by norm_num only) hy0.le) ht (by norm_num only : 0 < (5 : ℕ))
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    pow_zero, pow_one, div_one, zero_add] at he
  have hp := reciprocal_exponential_polynomial (1 / y) hz hb
  have hm := mul_le_mul_of_nonneg_right hp hz
  simp only [div_eq_mul_inv, one_mul] at he hm ⊢
  nlinarith only [he, hm]

/-- For l ≥ 122/25, five times l+1+3.1/l is at most 7(l+2 log 2).
Use the certified lower bound for log 2 and clear the positive denominator.
This absorbs the cutoff error into the coefficient fourteen of Theorem 1.5. -/
private theorem reciprocal_cutoff_coefficient (l : ℝ) (hl : 122 / 25 ≤ l) :
    5 * (l + 1 + 31 / (10 * l)) ≤ 7 * (l + 2 * Real.log 2) := by
  have hl0 : 0 < l := by linarith only [hl]
  have hk : 1 / 2 ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hprod := mul_nonneg (by linarith only [hk] : 0 ≤ Real.log 2 - 1 / 2) hl0.le
  field_simp [ne_of_gt hl0]
  nlinarith only [hl, hprod]

/-- For q ≥ 10^10, the product of the exponential upper coefficient and the
cutoff-error factor is at most twice the original reciprocal factor.
Combine the upper-factor comparison with the extra coefficient bound and the
cutoff identity. Used in the reciprocal L-value estimate. -/
theorem lValue_reciprocal_factor_of_log_cutoff (q : ℕ) (hq : 10 ^ 10 ≤ q) :
    let y := Real.log (q : ℝ) / 2
    let l := Real.log ((Real.log (q : ℝ)) ^ 2 / 4)
    (l + 1 + 31 / (10 * l)) * (1 + 5 / y) ≤ 2 * lValueReciprocalFactor q := by
  let y := Real.log (q : ℝ) / 2
  let l := Real.log ((Real.log (q : ℝ)) ^ 2 / 4)
  have hb := lValue_log_cutoff_bounds q hq
  have hy : 23 / 2 ≤ y := by
    dsimp only [y]; linarith only [hb.1]
  have hy0 : 0 < y := by linarith only [hy]
  have hl := lValue_log_cutoff_log_lower q hq
  change 122 / 25 ≤ l at hl
  have hl0 : 0 < l := by linarith only [hl]
  have hf := lValue_upper_factor_of_log_cutoff q hq
  change l + 1 + 31 / (10 * l) ≤ 2 * lValueUpperFactor q at hf
  have hc := div_le_div_of_nonneg_right (reciprocal_cutoff_coefficient l hl) hy0.le
  have he := hb.2.2.2
  change l = 2 * (Real.log (Real.log (q : ℝ)) - Real.log 2) at he
  have ht : Real.log (Real.log (q : ℝ)) = (l + 2 * Real.log 2) / 2 := by linarith only [he]
  have hi :
    2 * lValueReciprocalFactor q = 2 * lValueUpperFactor q + 7 * (l + 2 * Real.log 2) / y := by
    dsimp only [lValueReciprocalFactor]
    rw [ht,
      show Real.log (q : ℝ) = 2 * y by
        dsimp only [y]; ring]
    field_simp [ne_of_gt hy0]
    ring
  change (l + 1 + 31 / (10 * l)) * (1 + 5 / y) ≤ 2 * lValueReciprocalFactor q
  rw [hi]
  simp only [div_eq_mul_inv] at hc hf ⊢
  nlinarith only [hc, hf]

/-- For q ≥ 10^10 and v > 0, the simplified logarithmic lower bound implies
the reciprocal inequality of Theorem 1.5. Exponentiate the negative logarithm,
control both positive errors, and identify the original reciprocal factor.
The logarithmic estimate remains an explicit premise of this conversion. -/
theorem lValue_reciprocal_bound_of_log_bound (q : ℕ) (hq : 10 ^ 10 ≤ q) (v : ℝ) (hv : 0 < v)
    (hb :
      -Real.log (Real.log ((Real.log (q : ℝ)) ^ 2 / 4)) - Real.eulerMascheroniConstant +
            Real.log (Real.pi ^ 2 / 6) -
          1 / Real.log ((Real.log (q : ℝ)) ^ 2 / 4) -
          2 / (Real.log ((Real.log (q : ℝ)) ^ 2 / 4)) ^ 2 -
          4 / Real.sqrt ((Real.log (q : ℝ)) ^ 2 / 4) ≤
        Real.log v) :
    1 / v ≤
      12 * Real.exp Real.eulerMascheroniConstant / Real.pi ^ 2 * lValueReciprocalFactor q := by
  let y := Real.log (q : ℝ) / 2
  let l := Real.log ((Real.log (q : ℝ)) ^ 2 / 4)
  have hcut := lValue_log_cutoff_bounds q hq
  have hy : 23 / 2 ≤ y := by
    dsimp only [y]; linarith only [hcut.1]
  have hy0 : 0 < y := by linarith only [hy]
  have hl := lValue_log_cutoff_log_lower q hq
  change 122 / 25 ≤ l at hl
  have hl0 : 0 < l := by linarith only [hl]
  rw [hcut.2.2.1] at hb
  have hn :
    -Real.log v ≤
      Real.log l + Real.eulerMascheroniConstant - Real.log (Real.pi ^ 2 / 6) + (1 / l + 2 / l ^ 2) +
        4 / y := by
    change
      -Real.log l - Real.eulerMascheroniConstant + Real.log (Real.pi ^ 2 / 6) - 1 / l - 2 / l ^ 2 -
          4 / y ≤
        Real.log v at hb
    linarith only [hb]
  have hh := Real.exp_le_exp.mpr hn
  rw [Real.exp_neg, Real.exp_log hv] at hh
  have hz : 0 < Real.pi ^ 2 / 6 := by positivity
  rw [Real.exp_add, Real.exp_add, Real.exp_sub, Real.exp_add, Real.exp_log hl0,
    Real.exp_log hz] at hh
  have he := exponential_lValue_log_correction l hl
  have h4 := exponential_reciprocal_cutoff_correction y hy
  have hpos : 0 ≤ 1 + 1 / l + 31 / (10 * l ^ 2) := by positivity
  have hp := mul_le_mul he h4 (Real.exp_pos (4 / y)).le hpos
  have hm :=
    mul_le_mul_of_nonneg_left hp
      (by positivity : 0 ≤ l * Real.exp Real.eulerMascheroniConstant / (Real.pi ^ 2 / 6))
  have hf := lValue_reciprocal_factor_of_log_cutoff q hq
  change (l + 1 + 31 / (10 * l)) * (1 + 5 / y) ≤ 2 * lValueReciprocalFactor q at hf
  have ht :=
    mul_le_mul_of_nonneg_left hf
      (by positivity : 0 ≤ 6 * Real.exp Real.eulerMascheroniConstant / Real.pi ^ 2)
  have hi :
    (l * Real.exp Real.eulerMascheroniConstant / (Real.pi ^ 2 / 6)) *
        ((1 + 1 / l + 31 / (10 * l ^ 2)) * (1 + 5 / y)) =
      (6 * Real.exp Real.eulerMascheroniConstant / Real.pi ^ 2) *
        ((l + 1 + 31 / (10 * l)) * (1 + 5 / y)) := by
    field_simp [ne_of_gt hl0, ne_of_gt hy0, ne_of_gt Real.pi_pos]
  rw [hi] at hm
  have ha := le_trans (by simpa only [mul_assoc] using hh) hm
  have hbFinal := le_trans ha ht
  convert hbFinal using 1 <;> field_simp [ne_of_gt Real.pi_pos]
  ring

/-- Under GRH, a primitive character modulo q ≥ 10^10 satisfies the reciprocal
L-value inequality of Theorem 1.5. The logarithmic lower bound and the
certified exponential conversion give the original constants; nonvanishing
at one ensures the norm is positive. -/
theorem lValue_reciprocal_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 10 ^ 10 ≤ q)
    (hp : χ.IsPrimitive) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    1 / ‖χ.LFunction 1‖ ≤
      12 * Real.exp Real.eulerMascheroniConstant / Real.pi ^ 2 * lValueReciprocalFactor q := by
  have hq3 : 3 ≤ q := le_trans (by norm_num only : (3 : ℕ) ≤ 10 ^ 10) hq
  have hne := primitiveCharacter_ne_one_of_three_le hq3 hp
  have hv :=
    norm_pos_iff.mpr
      (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (s := 1) (Or.inl hne)
        (by norm_num only [Complex.one_re]))
  exact
    lValue_reciprocal_bound_of_log_bound q hq ‖χ.LFunction 1‖ hv
      (logLValue_lower_bound_at_log_cutoff χ hq hp hGRH)

end PseudoPrime.LLS.PaperStatements
