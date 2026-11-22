/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.IntegerIntervals
public import PseudoPrime.Analysis.LogTaylorBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! # Paired logarithm Taylor error for interval certificates -/

public section

namespace PseudoPrime.Analysis

/-- Pair positive and negative logarithm Taylor sums to approximate the logarithm
of `(1+z)/(1-z)` for `|z|<1`. The two certified remainders add. -/
theorem log_paired_error {z : ℝ} (hz : |z| < 1) (n : ℕ) :
    |Real.log ((1 + z) / (1 - z)) -
          ((∑ i ∈ Finset.range n, z ^ (i + 1) / (i + 1)) -
            (∑ i ∈ Finset.range n, (-z) ^ (i + 1) / (i + 1)))| ≤
      2 * (|z| ^ (n + 1) / (1 - |z|)) := by
  have hp := Real.abs_log_sub_add_sum_range_le hz n
  have hm := Real.abs_log_sub_add_sum_range_le (x := -z) (by simpa only [abs_neg] using hz) n
  have h1 : 0 < 1 - z := sub_pos.mpr (abs_lt.mp hz).2
  have h2 : 0 < 1 + z := by linarith only [(abs_lt.mp hz).1]
  rw [Real.log_div h2.ne' h1.ne']
  rw [abs_le] at hp hm ⊢
  simp only [sub_neg_eq_add, abs_neg] at hm
  constructor <;> linarith only [hp.1, hp.2, hm.1, hm.2]

-- The explicit 81st and 120th powers require deeper numeral normalization.
set_option maxRecDepth 2048 in
/-- At `|z|≤1/3`, the 80-term paired logarithm approximation has error
at most `2^-120`, matching the fixed-point checker error budget. -/
theorem log_paired80_error {z : ℝ} (hz : |z| ≤ 1 / 3) :
    |Real.log ((1 + z) / (1 - z)) -
          ((∑ i ∈ Finset.range 80, z ^ (i + 1) / (i + 1)) -
            (∑ i ∈ Finset.range 80, (-z) ^ (i + 1) / (i + 1)))| ≤
      (1 / 2 ^ 120 : ℝ) := by
  have hz1 : |z| < 1 := hz.trans_lt (by norm_num only)
  have hp := pow_le_pow_left₀ (abs_nonneg z) hz 81
  have hd : (2 / 3 : ℝ) ≤ 1 - |z| := by linarith only [hz]
  have h :=
    div_le_div₀ (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 3) 81) hp (by norm_num only) hd
  have hn : 2 * ((1 / 3 : ℝ) ^ 81 / (2 / 3)) ≤ 1 / 2 ^ 120 := by norm_num only
  exact
    (log_paired_error hz1 80).trans
      ((mul_le_mul_of_nonneg_left h (by norm_num only : (0 : ℝ) ≤ 2)).trans hn)

/-- A certified interval for the paired finite logarithm sum encloses the
true logarithm after widening by the `2^-120` remainder budget. -/
theorem log_paired80_contains {I : IntegerInterval} {G r : ℤ} {z : ℝ} (hz : |z| ≤ 1 / 3)
    (hp :
      I.Contains G
        ((∑ i ∈ Finset.range 80, z ^ (i + 1) / (i + 1)) -
          (∑ i ∈ Finset.range 80, (-z) ^ (i + 1) / (i + 1))))
    (hr : (1 / 2 ^ 120 : ℝ) ≤ (r : ℝ) / G) :
    (I.widen r).Contains G (Real.log ((1 + z) / (1 - z))) := by
  exact IntegerInterval.widen_contains hp ((log_paired80_error hz).trans hr)

/-- Pairing the first `2*n` positive and negative Taylor terms removes all
even powers, leaving twice the first `n` odd terms. Induct in pairs of terms. -/
theorem log_paired_eq_odd (z : ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (2 * n), z ^ (i + 1) / (i + 1)) -
        (∑ i ∈ Finset.range (2 * n), (-z) ^ (i + 1) / (i + 1)) =
      2 * ∑ j ∈ Finset.range n, z ^ (2 * j + 1) / (2 * j + 1) := by
  induction n with
  | zero => simp only [mul_zero, Finset.sum_range_zero, sub_self]
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]
    simp only [Finset.sum_range_succ]
    have hn : (-z) ^ (2 * n + 1) = -(z ^ (2 * n + 1)) := by
      simp only [pow_add, pow_mul, neg_sq, pow_one]
      ring
    have he : (-z) ^ (2 * n + 1 + 1) = z ^ (2 * n + 1 + 1) := by
      rw [pow_succ, hn, pow_succ]
      ring
    rw [hn, he]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, neg_div]
    linarith only [ih]

/-- The forty odd terms used by the logarithm evaluator approximate the
logarithm ratio within `2^-120` on the certified small domain. -/
theorem log_odd40_error {z : ℝ} (hz : |z| ≤ 1 / 3) :
    |Real.log ((1 + z) / (1 - z)) - 2 * ∑ j ∈ Finset.range 40, z ^ (2 * j + 1) / (2 * j + 1)| ≤
      (1 / 2 ^ 120 : ℝ) := by
  have h := log_paired80_error hz
  rw [show 80 = 2 * 40 by rfl, log_paired_eq_odd] at h
  exact h

/-- Transform a mantissa in `[1,2]` to the small logarithm-ratio domain.
The fractional parameter has absolute value at most one third. -/
theorem log_mantissa_domain {m : ℝ} (hm : 1 ≤ m) (hm2 : m ≤ 2) : |(m - 1) / (m + 1)| ≤ 1 / 3 := by
  have hp : 0 < m + 1 := by linarith only [hm]
  have hz : 0 ≤ (m - 1) / (m + 1) := div_nonneg (sub_nonneg.mpr hm) hp.le
  rw [abs_of_nonneg hz]
  apply (div_le_iff₀ hp).2
  linarith only [hm2]

/-- The logarithm-ratio substitution recovers a mantissa at least one.
Positive denominator permits clearing the rational identity. -/
theorem log_mantissa_ratio {m : ℝ} (hm : 1 ≤ m) :
    (1 + (m - 1) / (m + 1)) / (1 - (m - 1) / (m + 1)) = m := by
  have hn : m + 1 ≠ 0 := by linarith only [hm]
  field_simp [hn]
  ring

/-- The forty-term logarithm approximation is valid for every mantissa in
`[1,2]`, using the standard fractional substitution and the paired error bound. -/
theorem log_mantissa40_error {m : ℝ} (hm : 1 ≤ m) (hm2 : m ≤ 2) :
    |Real.log m - 2 * ∑ j ∈ Finset.range 40, ((m - 1) / (m + 1)) ^ (2 * j + 1) / (2 * j + 1)| ≤
      (1 / 2 ^ 120 : ℝ) := by
  have h := log_odd40_error (log_mantissa_domain hm hm2)
  rwa [log_mantissa_ratio hm] at h

/-- Binary mantissa normalization holds for every integer exponent, including
negative exponents. This joins the small-domain logarithm to arbitrary scales. -/
theorem log_binary_mantissa (k : ℤ) {m : ℝ} (hm : 0 < m) :
    Real.log ((2 : ℝ) ^ k * m) = (k : ℝ) * Real.log 2 + Real.log m := by
  rw [Real.log_mul (zpow_ne_zero k (by norm_num only : (2 : ℝ) ≠ 0)) hm.ne', Real.log_zpow]

/-- Certified logarithms of two and the mantissa compose into a certified
logarithm of their binary-scaled product, for positive or negative exponents. -/
theorem log_binary_contains {L M : IntegerInterval} {G k : ℤ} {m : ℝ} (hm : 0 < m)
    (hL : L.Contains G (Real.log 2)) (hM : M.Contains G (Real.log m)) :
    ((L.scale k).add M).Contains G (Real.log ((2 : ℝ) ^ k * m)) := by
  rw [log_binary_mantissa k hm]
  exact IntegerInterval.add_contains (IntegerInterval.scale_contains hL) hM

/-- The forty odd logarithm terms evaluated in rational arithmetic at a
rational mantissa. This finite value is checked without external numeric tables. -/
@[expose]
def rationalMantissaLog40 (m : ℚ) : ℚ :=
  2 * ∑ j ∈ Finset.range 40, ((m - 1) / (m + 1)) ^ (2 * j + 1) / (2 * j + 1)

/-- Rational evaluation of the forty-term logarithm sum agrees with real
evaluation after casting. This identifies finite certificates with the analytic sum. -/
theorem rationalMantissaLog40_cast (m : ℚ) :
    (rationalMantissaLog40 m : ℝ) =
      2 * ∑ j ∈ Finset.range 40, (((m : ℝ) - 1) / ((m : ℝ) + 1)) ^ (2 * j + 1) / (2 * j + 1) := by
  simp only [rationalMantissaLog40, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_sum, Rat.cast_div,
    Rat.cast_pow, Rat.cast_sub, Rat.cast_add, Rat.cast_one, Rat.cast_natCast]

/-- Check rational mantissa logarithm bounds, including the domain and analytic
error budget. Concrete instances may be discharged by `decide_cbv`. -/
@[expose]
def mantissaLog40Check (m l u : ℚ) : Bool :=
  decide
    (1 ≤ m ∧
      m ≤ 2 ∧ l ≤ rationalMantissaLog40 m - 1 / 2 ^ 120 ∧ rationalMantissaLog40 m + 1 / 2 ^ 120 ≤ u)

/-- Successful rational mantissa checking supplies bounds for the true real
logarithm, using the internally proved forty-term analytic remainder. -/
theorem mantissaLog40Check_sound {m l u : ℚ} (h : mantissaLog40Check m l u = true) :
    (l : ℝ) ≤ Real.log (m : ℝ) ∧ Real.log (m : ℝ) ≤ (u : ℝ) := by
  have hc := of_decide_eq_true h
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast hc.1
  have hm2 : (m : ℝ) ≤ 2 := by exact_mod_cast hc.2.1
  have hl : (l : ℝ) ≤ (rationalMantissaLog40 m : ℝ) - 1 / 2 ^ 120 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hc.2.2.1
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using hh
  have hu : (rationalMantissaLog40 m : ℝ) + 1 / 2 ^ 120 ≤ (u : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hc.2.2.2
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using hh
  have he := abs_le.mp (log_mantissa40_error hm hm2)
  rw [← rationalMantissaLog40_cast] at he
  constructor <;> linarith only [hl, hu, he.1, he.2]

/-- Rational logarithm bounds compose with any signed binary exponent.
A checked mantissa and certified log-two bounds yield rational endpoints for the
scaled input; the endpoint choices reverse when the exponent is negative. -/
theorem log_binary_rational_bounds (k : ℤ) {m ml mu l u : ℚ}
    (hm : mantissaLog40Check m ml mu = true) (hl : (l : ℝ) ≤ Real.log 2)
    (hu : Real.log 2 ≤ (u : ℝ)) :
    (((k : ℚ) * (if 0 ≤ (k : ℚ) then l else u) + ml : ℚ) : ℝ) ≤ Real.log ((2 : ℝ) ^ k * (m : ℝ)) ∧
      Real.log ((2 : ℝ) ^ k * (m : ℝ)) ≤
        (((k : ℚ) * (if 0 ≤ (k : ℚ) then u else l) + mu : ℚ) : ℝ) := by
  have hc := of_decide_eq_true hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hc.1
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (by norm_num only) hm1
  have hmant := mantissaLog40Check_sound hm
  have hs := signed_rational_node_bounds (b := (k : ℚ)) hl hu
  rw [log_binary_mantissa k hm0]
  constructor
  · simpa only [Rat.cast_add, Rat.cast_intCast] using add_le_add hs.1 hmant.1
  · simpa only [Rat.cast_add, Rat.cast_intCast] using add_le_add hs.2 hmant.2

/-- Positive endpoint logarithm bounds enclose the logarithm throughout a
real interval. This bridges certified point computations and continuous cells. -/
theorem log_interval_bounds {a b l u x : ℝ} (ha : 0 < a) (hx : a ≤ x ∧ x ≤ b) (hl : l ≤ Real.log a)
    (hu : Real.log b ≤ u) : l ≤ Real.log x ∧ Real.log x ≤ u := by
  have hxp := ha.trans_le hx.1
  exact ⟨hl.trans (Real.log_le_log ha hx.1), (Real.log_le_log hxp hx.2).trans hu⟩

/-- Logarithm bounds at the integer source endpoints certify every real input
in that interval. Positivity is verified at the source lower endpoint. -/
theorem integer_log_contains {A L : IntegerInterval} {G : ℤ} {x : ℝ} (ha : 0 < (A.lower : ℝ) / G)
    (hx : A.Contains G x) (hl : (L.lower : ℝ) / G ≤ Real.log ((A.lower : ℝ) / G))
    (hu : Real.log ((A.upper : ℝ) / G) ≤ (L.upper : ℝ) / G) : L.Contains G (Real.log x) := by
  exact log_interval_bounds ha hx hl hu

/-- Checked mantissa logarithms at rational endpoints give continuous real
logarithm bounds on the whole interval, without sampling interior points. -/
theorem mantissaLog40_interval {a b la ua lb ub : ℚ} {x : ℝ}
    (ha : mantissaLog40Check a la ua = true) (hb : mantissaLog40Check b lb ub = true)
    (hx : (a : ℝ) ≤ x ∧ x ≤ (b : ℝ)) : (la : ℝ) ≤ Real.log x ∧ Real.log x ≤ (ub : ℝ) := by
  have hc := of_decide_eq_true ha
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast hc.1
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le (by norm_num only) ha1
  exact log_interval_bounds ha0 hx (mantissaLog40Check_sound ha).1 (mantissaLog40Check_sound hb).2

end PseudoPrime.Analysis
