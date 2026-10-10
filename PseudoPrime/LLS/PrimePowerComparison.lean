/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperDefinitions
public import PseudoPrime.Analysis.ComplexPowerBounds

/-!
# Prime-power comparison estimates for LLS Lemma 5.1

These estimates apply to general complex characters without GRH. The first-five-term
identity retains the favorable odd powers, and its polynomial for the prime two is bounded
below by more than `5/36` for `x ≥ 100`. A geometric-series calculation bounds the even tail
by `5/36`, proving nonnegativity of the prime-two head and even-tail contribution.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The real weight `Λ(p^k) * (1/(p^k log(p^k)) - 1/(x log x))` for real `x` and
natural `p, k`, with division interpreted as in Lean even when a denominator vanishes.
No primality or positivity is required to define it. When `1 < p^k ≤ x`, the weight is
nonnegative; it weights each prime-power contribution in the comparison for Lemma 5.1. -/
noncomputable def primePowerComparisonWeight (x : ℝ) (p k : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt (p ^ k) *
    (1 / ((p : ℝ) ^ k * Real.log ((p : ℝ) ^ k)) - 1 / (x * Real.log x))

/-- The prime-power comparison weight is nonnegative when `1 < p^k ≤ x`.
Monotonicity of the logarithm makes the reciprocal difference nonnegative. This permits
multiplying the real-part comparison inequalities by the actual paper weights. -/
theorem primePowerComparisonWeight_nonneg {x : ℝ} {p k : ℕ} (hn : 1 < (p : ℝ) ^ k)
    (hx : (p : ℝ) ^ k ≤ x) : 0 ≤ primePowerComparisonWeight x p k := by
  have hp : 0 < (p : ℝ) ^ k := lt_trans zero_lt_one hn
  have hl : 0 < Real.log ((p : ℝ) ^ k) := Real.log_pos hn
  have hm : (p : ℝ) ^ k * Real.log ((p : ℝ) ^ k) ≤ x * Real.log x :=
    mul_le_mul hx (Real.log_le_log hp hx) hl.le (hp.le.trans hx)
  exact
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (sub_nonneg.mpr (one_div_le_one_div_of_le (mul_pos hp hl) hm))

/-- A nonzero complex Dirichlet character value has norm one. A nonunit would map
to zero; at a unit use the character norm theorem. No primitivity or GRH is needed. -/
theorem character_norm_one_of_ne_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {p : ℕ}
    (hp : χ p ≠ 0) : ‖χ p‖ = 1 := by
  by_cases hu : IsUnit (p : ZMod q)
  · exact χ.unit_norm_eq_one hu.unit
  · exact False.elim (hp (χ.map_nonunit hu))

/-- For a character modulo a nonzero modulus, a nonzero value `χ p`, and a finite
set of exponents with nonnegative comparison weights, bound the weighted real-part difference
from below by `(1 + Re (χ p)) * (firstWeight - evenQuadraticWeightSum)`, where
`firstWeight` is zero if exponent one is absent from the set. Multiplicativity reduces the
proof to the unit-circle power inequality. This lower bound
applies to general characters; no primality, primitivity, or GRH is assumed here. -/
theorem primePower_character_comparison {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {p : ℕ}
    (hp : χ p ≠ 0) (x : ℝ) (s : Finset ℕ) (hw : ∀ k ∈ s, 0 ≤ primePowerComparisonWeight x p k) :
    (1 + (χ p).re) *
        (∑ k ∈ s,
          if k = 1 then primePowerComparisonWeight x p k
          else if Even k then -(k : ℝ) ^ 2 * primePowerComparisonWeight x p k else 0) ≤
      ∑ k ∈ s, primePowerComparisonWeight x p k * ((χ (p ^ k)).re - (-1 : ℝ) ^ k) := by
  have h :=
    Analysis.weighted_power_difference_le (character_norm_one_of_ne_zero χ hp) s
      (primePowerComparisonWeight x p) hw
  simpa only [Nat.cast_pow, map_pow] using h

/-- For a prime and `x ≥ 1`, all positive powers through `p.log (floor x)` have
nonnegative comparison weights. The natural logarithm cutoff bounds the power by `x`.
This removes weight-sign hypotheses when using the paper's actual finite exponent range. -/
theorem primePowerComparisonWeight_nonneg_Icc {x : ℝ} (hx : 1 ≤ x) {p : ℕ} (hp : p.Prime) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 (p.log ⌊x⌋₊)) : 0 ≤ primePowerComparisonWeight x p k := by
  have hk' := Finset.mem_Icc.mp hk
  have hn : 1 < (p : ℝ) ^ k := one_lt_pow₀ (by exact_mod_cast hp.one_lt) (Nat.ne_of_gt hk'.1)
  have hf : ⌊x⌋₊ ≠ 0 := Nat.ne_of_gt (Nat.floor_pos.mpr hx)
  have hb : (p : ℝ) ^ k ≤ x := by
    have h := Nat.pow_le_of_le_log hf hk'.2
    exact
      (by exact_mod_cast h : (p : ℝ) ^ k ≤ (⌊x⌋₊ : ℝ)).trans (Nat.floor_le (zero_le_one.trans hx))
  exact primePowerComparisonWeight_nonneg hn hb

/-- For a prime `p`, a nonzero character value `χ p`, and `x ≥ 1`, bound the
comparison over `1 ≤ k ≤ p.log (floor x)` by
`(1 + Re (χ p)) * (firstWeight - evenQuadraticWeightSum)`. The cutoff supplies weight
nonnegativity, so the unit-circle comparison applies without a separate sign hypothesis.
This separates the
character factor from the prime-power coefficient estimated in the finite comparisons. -/
theorem primePower_character_comparison_Icc {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {p : ℕ}
    (hp : p.Prime) (hc : χ p ≠ 0) {x : ℝ} (hx : 1 ≤ x) :
    (1 + (χ p).re) *
        (∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊),
          if k = 1 then primePowerComparisonWeight x p k
          else if Even k then -(k : ℝ) ^ 2 * primePowerComparisonWeight x p k else 0) ≤
      ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊),
        primePowerComparisonWeight x p k * ((χ (p ^ k)).re - (-1 : ℝ) ^ k) := by
  exact
    primePower_character_comparison χ hc x _ fun _ hk ↦
      primePowerComparisonWeight_nonneg_Icc hx hp hk

/-- For arbitrary real weights and unit-norm `z`, the first five alternating comparison
terms factor as `(1+Re z)` times an explicit quartic polynomial. Expand via the power
recurrence. The exact identity retains the odd terms needed for the prime-two case. -/
theorem first_five_power_difference {z : ℂ} (hz : ‖z‖ = 1) (w : ℕ → ℝ) :
    w 1 * (z.re + 1) + w 2 * ((z ^ 2).re - 1) + w 3 * ((z ^ 3).re + 1) + w 4 * ((z ^ 4).re - 1) +
        w 5 * ((z ^ 5).re + 1) =
      (1 + z.re) *
        (w 1 + 2 * w 2 * (z.re - 1) + w 3 * (2 * z.re - 1) ^ 2 + 8 * w 4 * z.re ^ 2 * (z.re - 1) +
          w 5 * (4 * z.re ^ 2 - 2 * z.re - 1) ^ 2) := by
  have h2 := Analysis.re_pow_add_two_of_norm_eq_one hz 0
  have h3 := Analysis.re_pow_add_two_of_norm_eq_one hz 1
  have h4 := Analysis.re_pow_add_two_of_norm_eq_one hz 2
  have h5 := Analysis.re_pow_add_two_of_norm_eq_one hz 3
  simp only [zero_add, pow_zero, pow_one, Complex.one_re] at h2 h3
  rw [h5, h4, h3, h2]
  ring

/-- For arbitrary real weights `w` and real `a`, define
`w 1 + 2*w 2*(a-1) + w 3*(2*a-1)² + 8*w 4*a²*(a-1) + w 5*(4*a²-2*a-1)²`.
This polynomial has degree at most four. At `a = Re z` for unit-norm `z`, multiplying it by
`1 + Re z` gives the first five weighted comparison terms. The prime-two comparison uses
its lower bound with the actual prime-power weights against the even-tail mass. -/
noncomputable def firstFiveComparisonPolynomial (w : ℕ → ℝ) (a : ℝ) : ℝ :=
  w 1 + 2 * w 2 * (a - 1) + w 3 * (2 * a - 1) ^ 2 + 8 * w 4 * a ^ 2 * (a - 1) +
    w 5 * (4 * a ^ 2 - 2 * a - 1) ^ 2

/-- For unit-norm `z`, arbitrary first-five weights, and nonnegative weights on a
finite tail of exponents at least six, the first five comparison terms plus the tail are
at least `(1 + Re z) * (firstFiveComparisonPolynomial w (Re z) - evenTail)`, where
`evenTail` sums `k²*w k` over the even tail exponents. Combine the exact head identity with
the unit-circle lower bound for the tail. Both the polynomial and the tail subtraction
are inside the same factor, giving the interface for the prime-two estimate. -/
theorem first_five_with_tail_le {z : ℂ} (hz : ‖z‖ = 1) (w : ℕ → ℝ) (s : Finset ℕ)
    (hw : ∀ k ∈ s, 0 ≤ w k) (hk : ∀ k ∈ s, 6 ≤ k) :
    (1 + z.re) *
        (firstFiveComparisonPolynomial w z.re - ∑ k ∈ s, if Even k then (k : ℝ) ^ 2 * w k else 0) ≤
      w 1 * (z.re + 1) + w 2 * ((z ^ 2).re - 1) + w 3 * ((z ^ 3).re + 1) + w 4 * ((z ^ 4).re - 1) +
        w 5 * ((z ^ 5).re + 1) +
        ∑ k ∈ s, w k * ((z ^ k).re - (-1 : ℝ) ^ k) := by
  classical
  have ht := Analysis.weighted_power_difference_le hz s w hw
  have he :
    (∑ k ∈ s, if k = 1 then w k else if Even k then -(k : ℝ) ^ 2 * w k else 0) =
      -(∑ k ∈ s, if Even k then (k : ℝ) ^ 2 * w k else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hmem
    have hne : k ≠ 1 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 1 < 6) (hk k hmem))
    rw [ite_eq_right hne]
    split_ifs <;> ring
  rw [he] at ht
  have hh := first_five_power_difference hz w
  change _ = (1 + z.re) * firstFiveComparisonPolynomial w z.re at hh
  nlinarith only [ht, hh]

/-- For `a ≥ -1`, the limiting prime-two head polynomial is at least `91/480`.
A square decomposition bounds its quadratic-through-quartic part below by zero.
This is a rational certificate for the exceptional prime-two calculation. -/
theorem prime_two_limiting_polynomial_lower {a : ℝ} (ha : -1 ≤ a) :
    (91 / 480 : ℝ) ≤ firstFiveComparisonPolynomial (fun k ↦ 1 / ((k : ℝ) * 2 ^ k)) a := by
  have hs : 0 ≤ a ^ 2 * ((a + 1 / 8) ^ 2 / 10 + 29 / 1920) :=
    mul_nonneg (sq_nonneg a)
      (add_nonneg (div_nonneg (sq_nonneg _) (by norm_num only)) (by norm_num only))
  simp only [firstFiveComparisonPolynomial]
  norm_num only
  nlinarith only [hs, ha]

/-- On `[-1,1]`, the head polynomial with all weights one is at most fifteen.
Bound the fourth power by the square, then split on the sign of `a` for the cubic term.
This bounds the common cutoff correction in the prime-two head. -/
theorem prime_two_correction_polynomial_upper {a : ℝ} (ha : -1 ≤ a) (ha' : a ≤ 1) :
    firstFiveComparisonPolynomial (fun _ ↦ 1) a ≤ 15 := by
  have hs : a ^ 2 ≤ 1 := by nlinarith only [ha, ha']
  have h4 := mul_le_mul_of_nonneg_left hs (sq_nonneg a)
  by_cases h : 0 ≤ a
  · have h3 : 0 ≤ a ^ 3 := pow_nonneg h 3
    simp only [firstFiveComparisonPolynomial]
    nlinarith only [hs, h4, h3, ha']
  · have hn : a ≤ 0 := le_of_not_ge h
    have h3 : a ≤ a ^ 3 := by
      have ht :=
        mul_nonneg (mul_nonneg_of_nonpos_of_nonpos hn (sub_nonpos.mpr ha'))
          (by linarith only [ha] : 0 ≤ a + 1)
      nlinarith only [ht]
    simp only [firstFiveComparisonPolynomial]
    nlinarith only [hs, h4, h3, ha]

/-- On `[-1,1]`, weights `1/(k 2^k)-t` with `0 ≤ t ≤ 1/400` give a head polynomial
strictly larger than `5/36`. Its limiting lower bound and correction upper bound supply
an exact rational certificate. This is the margin needed against the even tail. -/
theorem prime_two_polynomial_lower {a t : ℝ} (ha : -1 ≤ a) (ha' : a ≤ 1) (ht : 0 ≤ t)
    (ht' : t ≤ 1 / 400) :
    (5 / 36 : ℝ) < firstFiveComparisonPolynomial (fun k ↦ 1 / ((k : ℝ) * 2 ^ k) - t) a := by
  have h0 := prime_two_limiting_polynomial_lower ha
  have h1 := mul_le_mul_of_nonneg_left (prime_two_correction_polynomial_upper ha ha') ht
  have h2 := mul_le_mul_of_nonneg_right ht' (by norm_num only : (0 : ℝ) ≤ 15)
  have he :
    firstFiveComparisonPolynomial (fun k ↦ 1 / ((k : ℝ) * 2 ^ k) - t) a =
      firstFiveComparisonPolynomial (fun k ↦ 1 / ((k : ℝ) * 2 ^ k)) a -
        t * firstFiveComparisonPolynomial (fun _ ↦ 1) a := by
    simp only [firstFiveComparisonPolynomial]
    ring
  rw [he]
  linarith only [h0, h1, h2]

/-- For `x ≥ 100`, the prime-two cutoff correction `log 2/(x log x)` lies in `[0,1/400]`.
Use `16 ≤ x` to obtain `4 log 2 ≤ log x`, then the lower bound on `x`.
No approximate evaluation of a logarithm enters the polynomial certificate. -/
theorem prime_two_correction_le {x : ℝ} (hx : 100 ≤ x) :
    0 ≤ Real.log 2 / (x * Real.log x) ∧ Real.log 2 / (x * Real.log x) ≤ 1 / 400 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 100) hx
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num only)
  have hlog : 4 * Real.log (2 : ℝ) ≤ Real.log x := by
    have h :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 2 ^ 4)
        (le_trans (by norm_num only : (2 : ℝ) ^ 4 ≤ 100) hx)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hd : 0 < x * Real.log x := mul_pos hx0 (lt_of_lt_of_le (mul_pos (by norm_num only) hl) hlog)
  refine ⟨div_nonneg hl.le hd.le, (div_le_iff₀ hd).mpr ?_⟩
  have hm := mul_le_mul hx hlog (mul_pos (by norm_num only) hl).le hx0.le
  nlinarith only [hm]

/-- For `x ≥ 100` and `a ∈ [-1,1]`, the prime-two polynomial with its actual cutoff
correction is strictly larger than `5/36`. Apply the rational polynomial certificate
and the logarithmic correction bound. This proves the head margin in Lemma 5.1. -/
theorem prime_two_corrected_polynomial_lower {x a : ℝ} (hx : 100 ≤ x) (ha : -1 ≤ a) (ha' : a ≤ 1) :
    (5 / 36 : ℝ) <
      firstFiveComparisonPolynomial (fun k ↦ 1 / ((k : ℝ) * 2 ^ k) - Real.log 2 / (x * Real.log x))
        a := by
  exact
    prime_two_polynomial_lower ha ha' (prime_two_correction_le hx).1 (prime_two_correction_le hx).2

/-- The normalized prime-two even tail has sum `5/36`. Combine the geometric and
linear-times-geometric series at ratio one quarter, then shift the index by three.
This is the exact mass against which the first-five polynomial is compared. -/
theorem hasSum_prime_two_even_tail :
    HasSum (fun j : ℕ ↦ 2 * ((j : ℝ) + 3) * (1 / 4 : ℝ) ^ (j + 3)) (5 / 36 : ℝ) := by
  have hr : ‖(1 / 4 : ℝ)‖ < 1 := by norm_num only [Real.norm_eq_abs]
  have hs :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hr).add
      ((hasSum_geometric_of_norm_lt_one hr).mul_left 3)
  have ht := hs.mul_left (1 / 32 : ℝ)
  convert ht using 1
  · ext j
    rw [pow_add]
    norm_num only
    ring
  · norm_num only

/-- For a prime and a positive exponent, the paper weight equals
`1/(k p^k) - log p/(x log x)`. Use the prime-power Mangoldt and logarithm identities.
This identifies the actual prime-two weights with the certified corrected polynomial. -/
theorem primePowerComparisonWeight_eq {x : ℝ} {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    primePowerComparisonWeight x p k =
      1 / ((k : ℝ) * (p : ℝ) ^ k) - Real.log p / (x * Real.log x) := by
  have hl : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hp' : (p : ℝ) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
  rw [primePowerComparisonWeight, ArithmeticFunction.vonMangoldt_apply_pow hk,
    ArithmeticFunction.vonMangoldt_apply_prime hp, Real.log_pow, mul_sub]
  congr 1
  · field_simp [hl, hk', hp']
  · ring

/-- Every finite set of normalized prime-two even tail indices has mass at most `5/36`.
Nonnegativity compares the finite sum to the absolutely convergent geometric tail.
This allows the head polynomial certificate to be applied to finite exponent cutoffs. -/
theorem prime_two_even_tail_sum_le (s : Finset ℕ) :
    ∑ j ∈ s, 2 * ((j : ℝ) + 3) * (1 / 4 : ℝ) ^ (j + 3) ≤ (5 / 36 : ℝ) := by
  have hs := hasSum_prime_two_even_tail
  have h :=
    hs.summable.sum_le_tsum s
      (fun j _ ↦
        mul_nonneg
          (mul_nonneg (by norm_num only) (add_nonneg (Nat.cast_nonneg j) (by norm_num only)))
          (pow_nonneg (by norm_num only) _))
  rw [hs.tsum_eq] at h
  exact h

/-- For `x ≥ 100` and positive exponent `k`, the quadratic prime-two weight is at most
`k/2^k`. Remove the nonnegative common cutoff correction and cancel the positive index.
This is the summable majorant for the exceptional prime's even powers. -/
theorem prime_two_weight_majorant {x : ℝ} (hx : 100 ≤ x) {k : ℕ} (hk : k ≠ 0) :
    (k : ℝ) ^ 2 * primePowerComparisonWeight x 2 k ≤ (k : ℝ) / 2 ^ k := by
  rw [primePowerComparisonWeight_eq Nat.prime_two hk]
  have ht := (prime_two_correction_le hx).1
  have h :
    (k : ℝ) ^ 2 * (1 / ((k : ℝ) * 2 ^ k) - Real.log 2 / (x * Real.log x)) ≤
      (k : ℝ) ^ 2 * (1 / ((k : ℝ) * 2 ^ k)) :=
    mul_le_mul_of_nonneg_left (sub_le_self _ ht) (sq_nonneg _)
  have he : (k : ℝ) ^ 2 * (1 / ((k : ℝ) * 2 ^ k)) = (k : ℝ) / 2 ^ k := by
    field_simp [Nat.cast_ne_zero.mpr hk]
  rw [he] at h
  exact h

/-- The even exponent `2(j+3)` transforms `k/2^k` into the shifted geometric tail term.
Real casts and power multiplication give the identity. This matches the exact tail mass. -/
theorem prime_two_even_majorant_eq (j : ℕ) :
    ((2 * (j + 3) : ℕ) : ℝ) / (2 : ℝ) ^ (2 * (j + 3)) =
      2 * ((j : ℝ) + 3) * (1 / 4 : ℝ) ^ (j + 3) := by
  rw [Nat.cast_mul, Nat.cast_add, pow_mul]
  norm_num only [Nat.cast_ofNat]
  simp only [div_eq_mul_inv, ← inv_pow]
  ring

/-- For `x ≥ 100`, the quadratic weights on any finite set of even exponents at least
six sum to at most `5/36`. Apply the pointwise weight majorant, reindex the even exponents,
and use the finite geometric-tail bound. This connects the polynomial margin to actual weights. -/
theorem prime_two_weighted_even_tail_le {x : ℝ} (hx : 100 ≤ x) (s : Finset ℕ) :
    ∑ j ∈ s, (((2 * (j + 3) : ℕ) : ℝ) ^ 2 * primePowerComparisonWeight x 2 (2 * (j + 3))) ≤
      (5 / 36 : ℝ) := by
  apply
    le_trans
      (Finset.sum_le_sum
        (fun j _ ↦
          prime_two_weight_majorant hx (Nat.mul_ne_zero (by decide) (Nat.succ_ne_zero (j + 2)))))
  simpa only [prime_two_even_majorant_eq] using prime_two_even_tail_sum_le s

/-- For `x ≥ 100` and `a ∈ [-1,1]`, the first-five polynomial with the actual
prime-two weights is strictly larger than `5/36`. Rewrite its five weights to the
normalized form and apply the certified quartic lower bound. -/
theorem prime_two_actual_polynomial_lower {x a : ℝ} (hx : 100 ≤ x) (ha : -1 ≤ a) (ha' : a ≤ 1) :
    (5 / 36 : ℝ) < firstFiveComparisonPolynomial (primePowerComparisonWeight x 2) a := by
  have h := prime_two_corrected_polynomial_lower hx ha ha'
  simp only [firstFiveComparisonPolynomial] at h ⊢
  rw [primePowerComparisonWeight_eq Nat.prime_two (by decide : 1 ≠ 0),
    primePowerComparisonWeight_eq Nat.prime_two (by decide : 2 ≠ 0),
    primePowerComparisonWeight_eq Nat.prime_two (by decide : 3 ≠ 0),
    primePowerComparisonWeight_eq Nat.prime_two (by decide : 4 ≠ 0),
    primePowerComparisonWeight_eq Nat.prime_two (by decide : 5 ≠ 0)]
  exact h

/-- For a unit-norm complex value, `x ≥ 100`, and nonnegative actual even tail weights,
the first-five polynomial contribution plus any finite even tail comparison is nonnegative.
Combine the polynomial margin and the quadratic tail mass. This completes their local comparison. -/
theorem prime_two_head_even_tail_nonneg {x : ℝ} (hx : 100 ≤ x) {z : ℂ} (hz : ‖z‖ = 1) (s : Finset ℕ)
    (hw : ∀ j ∈ s, 0 ≤ primePowerComparisonWeight x 2 (2 * (j + 3))) :
    0 ≤
      (1 + z.re) * firstFiveComparisonPolynomial (primePowerComparisonWeight x 2) z.re +
        ∑ j ∈ s, primePowerComparisonWeight x 2 (2 * (j + 3)) * ((z ^ (2 * (j + 3))).re - 1) := by
  have ha := Complex.abs_re_le_norm z
  rw [hz] at ha
  have hp := prime_two_actual_polynomial_lower hx (neg_le_of_abs_le ha) (le_of_abs_le ha)
  have hn : 0 ≤ 1 + z.re := by linarith only [neg_le_of_abs_le ha]
  have ht := prime_two_weighted_even_tail_le hx s
  have hs :
    -(1 + z.re) *
        (∑ j ∈ s, (((2 * (j + 3) : ℕ) : ℝ) ^ 2 * primePowerComparisonWeight x 2 (2 * (j + 3)))) ≤
      ∑ j ∈ s, primePowerComparisonWeight x 2 (2 * (j + 3)) * ((z ^ (2 * (j + 3))).re - 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have he : Even (2 * (j + 3)) := ⟨j + 3, by ring⟩
    have h := mul_le_mul_of_nonneg_left (Analysis.even_power_difference_le hz he) (hw j hj)
    nlinarith only [h]
  have hc := mul_nonneg hn (sub_nonneg.mpr (le_trans ht hp.le))
  nlinarith only [hs, hc]

/-- For `x ≥ 100`, unit-norm `z`, and any finite even tail whose powers are at most `x`,
the first-five contribution plus that tail comparison is nonnegative. The cutoff ensures
weight positivity, so no separate sign assumption is imposed. This is the prime-two local bound. -/
theorem prime_two_head_even_tail_nonneg_of_cutoff {x : ℝ} (hx : 100 ≤ x) {z : ℂ} (hz : ‖z‖ = 1)
    (s : Finset ℕ) (hcut : ∀ j ∈ s, (2 : ℝ) ^ (2 * (j + 3)) ≤ x) :
    0 ≤
      (1 + z.re) * firstFiveComparisonPolynomial (primePowerComparisonWeight x 2) z.re +
        ∑ j ∈ s, primePowerComparisonWeight x 2 (2 * (j + 3)) * ((z ^ (2 * (j + 3))).re - 1) := by
  apply prime_two_head_even_tail_nonneg hx hz s
  intro j hj
  exact
    primePowerComparisonWeight_nonneg
      (one_lt_pow₀ (by norm_num only : (1 : ℝ) < 2)
        (Nat.mul_ne_zero (by decide) (Nat.succ_ne_zero (j + 2))))
      (hcut j hj)

end PseudoPrime.LLS.PaperStatements
