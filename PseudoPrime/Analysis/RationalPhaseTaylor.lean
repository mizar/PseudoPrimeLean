/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RoundedEulerProduct
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Rational Taylor approximations with certified phase interval error -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: rational complex component pairs. Output: their componentwise sum.
Role: compute phase polynomials without analytic complex values. -/
def rationalComplexAdd (z w : ℚ × ℚ) : ℚ × ℚ :=
  (z.1 + w.1, z.2 + w.2)

/-- Input: a rational scalar and component pair. Output: their scalar product.
Role: implement exact Taylor coefficients. -/
def rationalComplexScale (c : ℚ) (z : ℚ × ℚ) : ℚ × ℚ :=
  (c * z.1, c * z.2)

/-- Input: a rational complex pair and natural exponent. Output: its repeated product.
Definition: the zeroth power is (1,0), followed by component multiplication.
Role: compute rational Taylor monomials. -/
def rationalComplexPow (z : ℚ × ℚ) : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | n + 1 => rationalComplexMul (rationalComplexPow z n) z

/-- Input: a rational phase center v and truncation length n.
Output: the sum of (i*v)^k/k! for k<n, stored as a rational pair.
Role: provide executable phase approximations with certified analytic error. -/
def rationalPhaseTaylor (v : ℚ) (n : ℕ) : ℚ × ℚ :=
  (Finset.range n).sum
    (fun k ↦ rationalComplexScale (1 / (k.factorial : ℚ)) (rationalComplexPow (0, v) k))

/-- Input: two rational pairs. Claim: casting preserves their sum.
Proof: compare both components. Role: transfer rational sums into complex arithmetic. -/
theorem rationalComplexCast_add (z w : ℚ × ℚ) :
    rationalComplexCast (rationalComplexAdd z w) =
      rationalComplexCast z + rationalComplexCast w := by
  apply Complex.ext
  · simp only [rationalComplexCast, rationalComplexAdd, Rat.cast_add, Complex.add_re]
  · simp only [rationalComplexCast, rationalComplexAdd, Rat.cast_add, Complex.add_im]

/-- Input: a rational scalar and pair. Claim: casting preserves scalar multiplication.
Proof: compare both components. Role: identify exact Taylor terms. -/
theorem rationalComplexCast_scale (c : ℚ) (z : ℚ × ℚ) :
    rationalComplexCast (rationalComplexScale c z) = (c : ℂ) * rationalComplexCast z := by
  apply Complex.ext
  · simp only [rationalComplexCast, rationalComplexScale, Rat.cast_mul, Complex.mul_re,
      Complex.ratCast_re, Complex.ratCast_im, zero_mul, sub_zero]
  · simp only [rationalComplexCast, rationalComplexScale, Rat.cast_mul, Complex.mul_im,
      Complex.ratCast_re, Complex.ratCast_im, zero_mul, add_zero]

/-- Input: a rational pair and exponent. Claim: casting preserves powers.
Proof: induct on the exponent. Role: identify rational phase monomials. -/
theorem rationalComplexCast_pow (z : ℚ × ℚ) (n : ℕ) :
    rationalComplexCast (rationalComplexPow z n) = rationalComplexCast z ^ n := by
  induction n with
  | zero =>
    simp only [rationalComplexPow, rationalComplexCast, Rat.cast_one, Rat.cast_zero, pow_zero]
    rfl
  | succ n ih => rw [rationalComplexPow, rationalComplexCast_mul, ih, pow_succ]

/-- Input: a finite set and rational pairs. Claim: casting commutes with the finite sum.
Proof: induct on the finite set. Role: identify a complete Taylor polynomial. -/
theorem rationalComplexCast_sum {ι : Type*} (S : Finset ι) (f : ι → ℚ × ℚ) :
    rationalComplexCast (S.sum f) = S.sum (fun i ↦ rationalComplexCast (f i)) := by
  classical
    induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, rationalComplexCast, Prod.fst_zero, Prod.snd_zero, Rat.cast_zero];
    rfl
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    change rationalComplexCast (rationalComplexAdd (f i) (S.sum f)) = _
    rw [rationalComplexCast_add, ih]

/-- Input: a rational phase center and truncation length.
Claim: the rational Taylor pair casts to the usual complex Taylor sum.
Proof: commute the cast with finite sums, scalar products and powers.
Role: apply the analytic exponential remainder estimate to executable arithmetic. -/
theorem rationalPhaseTaylor_cast (v : ℚ) (n : ℕ) :
    rationalComplexCast (rationalPhaseTaylor v n) =
      ∑ k ∈ Finset.range n, (Complex.I * (v : ℂ)) ^ k / (k.factorial : ℂ) := by
  rw [rationalPhaseTaylor, rationalComplexCast_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [rationalComplexCast_scale, rationalComplexCast_pow]
  have he : rationalComplexCast (0, v) = Complex.I * (v : ℂ) := by
    apply Complex.ext
    · simp only [rationalComplexCast, Rat.cast_zero, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ratCast_re, Complex.ratCast_im, zero_mul, mul_zero, sub_zero]
    · simp only [rationalComplexCast, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ratCast_re, Complex.ratCast_im, zero_mul, one_mul, zero_add]
  rw [he]
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  ring

/-- Input: real phase angles. Claim: the unit exponential distance is at most their distance.
Proof: factor out the unit exponential and apply the sine bound.
Role: transfer a rational phase enclosure to the exponential. -/
theorem norm_phase_exp_sub_le (θ v : ℝ) :
    ‖Complex.exp (Complex.I * θ) - Complex.exp (Complex.I * v)‖ ≤ |θ - v| := by
  have he :
    Complex.exp (Complex.I * θ) - Complex.exp (Complex.I * v) =
      Complex.exp (Complex.I * v) * (Complex.exp (Complex.I * (θ - v)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    ring
  rw [he, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  simpa only [Complex.ofReal_sub, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ - v))

/-- Input: a rational phase v and length n with |v|/(n+1)<=1/2.
Claim: the Taylor error is at most 2*|v|^n/n!.
Proof: apply the complex exponential remainder estimate.
Role: obtain an explicit rational error budget at each node. -/
theorem norm_phaseTaylor_error (v : ℚ) (n : ℕ) (hv : |(v : ℝ)| / (n + 1 : ℕ) ≤ 1 / 2) :
    ‖Complex.exp (Complex.I * (v : ℂ)) - rationalComplexCast (rationalPhaseTaylor v n)‖ ≤
      |(v : ℝ)| ^ n / (n.factorial : ℝ) * 2 := by
  have hn : ‖Complex.I * (v : ℂ)‖ = |(v : ℝ)| := by
    rw [norm_mul, Complex.norm_I, one_mul, ← Complex.ofReal_ratCast, Complex.norm_real,
      Real.norm_eq_abs]
  rw [rationalPhaseTaylor_cast]
  have h :=
    Complex.exp_bound' (n := n) (x := Complex.I * (v : ℂ))
      (by
        rw [hn]; exact hv)
  rw [hn] at h
  exact h

/-- Input: a phase within epsilon of a rational center and a valid Taylor length.
Claim: the total error is at most epsilon+2*|v|^n/n!.
Proof: combine unit-phase stability and the Taylor remainder by the triangle inequality.
Role: allow a logarithmic interval rather than an exact phase value. -/
theorem norm_phaseTaylor_interval_error {θ : ℝ} (v : ℚ) (n : ℕ) {ε : ℝ}
    (hv : |(v : ℝ)| / (n + 1 : ℕ) ≤ 1 / 2) (hε : |θ - (v : ℝ)| ≤ ε) :
    ‖Complex.exp (Complex.I * θ) - rationalComplexCast (rationalPhaseTaylor v n)‖ ≤
      ε + |(v : ℝ)| ^ n / (n.factorial : ℝ) * 2 := by
  have htri :=
    norm_sub_le_norm_sub_add_norm_sub (Complex.exp (Complex.I * θ))
      (Complex.exp (Complex.I * (v : ℂ))) (rationalComplexCast (rationalPhaseTaylor v n))
  have hphase := norm_phase_exp_sub_le θ (v : ℝ)
  simp only [Complex.ofReal_ratCast] at hphase
  exact htri.trans (add_le_add (hphase.trans hε) (norm_phaseTaylor_error v n hv))

/-- Input: a coefficient norm cap and a certified phase center and Taylor length.
Claim: the Taylor product real part minus the full error is a lower bound for the phase.
Proof: bound the real part by the complex norm and multiply the error allowance.
Role: certify Gamma-resolvent node inequalities using rational arithmetic. -/
theorem phase_product_re_lower_of_taylor {C : ℂ} {K θ ε : ℝ} (v : ℚ) (n : ℕ) (hK : ‖C‖ ≤ K)
    (hv : |(v : ℝ)| / (n + 1 : ℕ) ≤ 1 / 2) (hε : |θ - (v : ℝ)| ≤ ε) :
    (C * rationalComplexCast (rationalPhaseTaylor v n)).re -
        K * (ε + |(v : ℝ)| ^ n / (n.factorial : ℝ) * 2) ≤
      (C * Complex.exp (Complex.I * θ)).re := by
  have h := norm_phaseTaylor_interval_error v n hv hε
  have hE : 0 ≤ ε + |(v : ℝ)| ^ n / (n.factorial : ℝ) * 2 := le_trans (norm_nonneg _) h
  have hm := mul_le_mul hK h (norm_nonneg _) (le_trans (norm_nonneg _) hK)
  have hr :=
    Complex.abs_re_le_norm
      (C * (Complex.exp (Complex.I * θ) - rationalComplexCast (rationalPhaseTaylor v n)))
  rw [norm_mul, mul_sub, Complex.sub_re] at hr
  have hab := (abs_le.mp (hr.trans hm)).1
  linarith only [hab]

end PseudoPrime.Analysis
