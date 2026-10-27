/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.StableEulerProduct

/-! # Certified rational rounding of finite Euler products -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a pair of rational numbers. Output: the complex number with those components.
Role: give executable rational node calculations a precise complex interpretation. -/
def rationalComplexCast (z : ℚ × ℚ) : ℂ :=
  ⟨z.1, z.2⟩

/-- Input: two rational component pairs. Output: their complex product in components.
Role: compute finite products using exact rational arithmetic. -/
def rationalComplexMul (z w : ℚ × ℚ) : ℚ × ℚ :=
  (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

/-- Input: a natural grid denominator G and rational value.
Output: floor(G*q)/G. Role: bound intermediate denominator growth in product certificates. -/
def rationalGridFloor (G : ℕ) (q : ℚ) : ℚ :=
  (⌊q * (G : ℚ)⌋ : ℚ) / (G : ℚ)

/-- Input: a grid denominator and rational component pair.
Output: the two components rounded downward on that grid.
Role: control certificate size with a proved complex norm error. -/
def rationalComplexRound (G : ℕ) (z : ℚ × ℚ) : ℚ × ℚ :=
  (rationalGridFloor G z.1, rationalGridFloor G z.2)

/-- Input: two rational component pairs.
Claim: component multiplication agrees with complex multiplication.
Proof: compare real and imaginary parts and commute rational casts.
Role: verify rational computations against their complex meaning. -/
theorem rationalComplexCast_mul (z w : ℚ × ℚ) :
    rationalComplexCast (rationalComplexMul z w) =
      rationalComplexCast z * rationalComplexCast w := by
  apply Complex.ext
  · simp only [rationalComplexCast, rationalComplexMul, Rat.cast_sub, Rat.cast_mul, Complex.mul_re]
  · simp only [rationalComplexCast, rationalComplexMul, Rat.cast_add, Rat.cast_mul, Complex.mul_im]

/-- Input: a positive grid denominator and rational value.
Claim: the absolute rounding error is at most 1/G.
Proof: use the two defining inequalities for the integer floor.
Role: certify every component rounding operation. -/
theorem rationalGridFloor_error {G : ℕ} (hG : 0 < G) (q : ℚ) :
    |q - rationalGridFloor G q| ≤ 1 / (G : ℚ) := by
  have hg : (0 : ℚ) < G := Nat.cast_pos.mpr hG
  have he : (q - rationalGridFloor G q) * (G : ℚ) = q * G - (⌊q * (G : ℚ)⌋ : ℚ) := by
    rw [rationalGridFloor, sub_mul, div_mul_cancel₀ _ hg.ne']
  have hn : 0 ≤ q - rationalGridFloor G q := by
    apply (mul_nonneg_iff_of_pos_right hg).mp
    rw [he]
    exact sub_nonneg.mpr (Int.floor_le _)
  rw [abs_of_nonneg hn]
  apply (le_div_iff₀ hg).mpr
  rw [he]
  linarith only [Int.lt_floor_add_one (q * (G : ℚ))]

/-- Input: a positive grid denominator and rational complex value.
Claim: the complex rounding error is at most 2/G.
Proof: bound the norm by the sum of the two component errors.
Role: supply the local multiplication error for contractive products. -/
theorem norm_rationalComplexRound_error {G : ℕ} (hG : 0 < G) (z : ℚ × ℚ) :
    ‖rationalComplexCast (rationalComplexRound G z) - rationalComplexCast z‖ ≤ 2 / (G : ℝ) := by
  have hr := (Rat.cast_le (K := ℝ)).mpr (rationalGridFloor_error hG z.1)
  have hi := (Rat.cast_le (K := ℝ)).mpr (rationalGridFloor_error hG z.2)
  simp only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] at hr hi
  have hn :=
    Complex.norm_le_abs_re_add_abs_im
      (rationalComplexCast (rationalComplexRound G z) - rationalComplexCast z)
  simp only [rationalComplexCast, rationalComplexRound, Complex.sub_re, Complex.sub_im] at hn
  rw [abs_sub_comm (rationalGridFloor G z.1 : ℝ), abs_sub_comm (rationalGridFloor G z.2 : ℝ)] at hn
  have he : (2 : ℝ) / G = 1 / G + 1 / G := by ring
  rw [he]
  exact hn.trans (add_le_add hr hi)

/-- Input: a rational ordinate and natural index n.
Output: the rational real and imaginary parts of (n+1)/(n+3/2+i*t).
Role: evaluate every normalized half-line Euler factor exactly. -/
def eulerHalfRationalFactor (t : ℚ) (n : ℕ) : ℚ × ℚ :=
  let j : ℚ := n + 1
  let a := j + 1 / 2
  (j * a / (a ^ 2 + t ^ 2), -j * t / (a ^ 2 + t ^ 2))

/-- Input: a rational ordinate and natural index.
Claim: the rational component formula equals the complex normalized factor.
Proof: expand complex division and compare the two components.
Role: connect executable factors to the analytic product. -/
theorem eulerHalfRationalFactor_cast (t : ℚ) (n : ℕ) :
    rationalComplexCast (eulerHalfRationalFactor t n) =
      ((n + 1 : ℕ) : ℂ) / ((1 / 2 : ℂ) + Complex.I * (t : ℂ) + ((n + 1 : ℕ) : ℂ)) := by
  apply Complex.ext
  · norm_num only [rationalComplexCast, eulerHalfRationalFactor, Rat.cast_div, Rat.cast_mul,
      Rat.cast_add, Rat.cast_pow, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat, Complex.div_re,
      Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
      Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ratCast_re, Complex.ratCast_im,
      Nat.cast_add, Nat.cast_one, zero_mul, mul_zero, one_mul, mul_one, sub_zero, zero_sub,
      add_zero, zero_add, zero_div]
    ring
  · norm_num only [rationalComplexCast, eulerHalfRationalFactor, Rat.cast_div, Rat.cast_mul,
      Rat.cast_add, Rat.cast_pow, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat, Rat.cast_neg,
      Complex.div_im, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.natCast_re,
      Complex.natCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofNat_re,
      Complex.div_ofNat_im, Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ratCast_re,
      Complex.ratCast_im, Nat.cast_add, Nat.cast_one, zero_mul, mul_zero, one_mul, mul_one,
      sub_zero, zero_sub, add_zero, zero_add, zero_div]
    ring

/-- Input: a grid denominator, rational ordinate and finite order.
Output: a product starting at one and rounded after every factor multiplication.
Role: calculate nodes without storing full exact product numerators and denominators. -/
def roundedEulerUnitProduct (G : ℕ) (t : ℚ) : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | n + 1 =>
    rationalComplexRound G
      (rationalComplexMul (roundedEulerUnitProduct G t n) (eulerHalfRationalFactor t n))

/-- Input: a positive grid denominator, rational ordinate and finite order.
Claim: the rounded product differs from the analytic normalized product by at most 2*n/G.
Proof: combine exact rational-factor casts with local rounding and contractivity.
Role: provide a fully proved error allowance for Gamma phase node certificates. -/
theorem roundedEulerUnitProduct_error {G : ℕ} (hG : 0 < G) (t : ℚ) (n : ℕ) :
    ‖rationalComplexCast (roundedEulerUnitProduct G t n) -
          eulerUnitProduct ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) n‖ ≤
      (n : ℝ) * (2 / (G : ℝ)) := by
  apply
    norm_approx_eulerUnitProduct_le
      (by
        norm_num only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, Complex.ratCast_re, Complex.ratCast_im, zero_mul, mul_zero,
          sub_zero, add_zero] :
        0 ≤ ((1 / 2 : ℂ) + Complex.I * (t : ℂ)).re)
      (fun j ↦ rationalComplexCast (roundedEulerUnitProduct G t j))
      (by
        apply Complex.ext <;>
          norm_num only [roundedEulerUnitProduct, rationalComplexCast, Rat.cast_one, Rat.cast_zero,
            Complex.one_re, Complex.one_im])
  intro j
  have h :=
    norm_rationalComplexRound_error hG
      (rationalComplexMul (roundedEulerUnitProduct G t j) (eulerHalfRationalFactor t j))
  rw [rationalComplexCast_mul, eulerHalfRationalFactor_cast] at h
  exact h

/-- Claim: the rounded order-256 product at t=109/50 on the 10^12 grid has these components.
Proof: kernel evaluation of all 256 exact rational factors and rounding steps.
Role: check executable node evaluation at the previously observed smallest-gap ordinate. -/
theorem roundedEulerUnitProduct_grid12_at_109_div_50 :
    roundedEulerUnitProduct (10 ^ 12) (109 / 50) 256 =
      ((2485413517 / 1000000000000 : ℚ), (11230133857 / 1000000000000 : ℚ)) := by
  decide +kernel

end PseudoPrime.Analysis
