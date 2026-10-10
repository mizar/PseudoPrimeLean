/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.Circle

/-!
# Poisson-weighted Cayley moments

On the line Re z = 1, the Cayley quotient (z - 2) / z has unit norm.
Its positive powers, weighted by inverse norm square, are finite inverse-power combinations.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For a complex number with real part one, subtraction of two equals its negative
conjugate. Compare real and imaginary parts. This relates the Cayley numerator to its
denominator and supplies the Poisson-weighted moment identity. -/
theorem cayley_sub_two_eq_neg_conj {z : ℂ} (hz : z.re = 1) : z - 2 = -(starRingEnd ℂ) z := by
  apply Complex.ext
  · simp only [Complex.sub_re, show (2 : ℂ).re = (2 : ℝ) from rfl, Complex.neg_re, Complex.conj_re,
      hz]
    norm_num only
  · simp only [Complex.sub_im, show (2 : ℂ).im = (0 : ℝ) from rfl, sub_zero, Complex.neg_im,
      Complex.conj_im, neg_neg]

/-- For a complex number with real part one, the Cayley quotient (z - 2) / z has norm one.
The numerator is the negative conjugate of the nonzero denominator.
This places weighted height moments on the unit circle. -/
theorem cayley_norm {z : ℂ} (hz : z.re = 1) : ‖(z - 2) / z‖ = 1 := by
  have hn : z ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hz
    norm_num only at hz
  rw [norm_div, cayley_sub_two_eq_neg_conj hz, norm_neg, RCLike.norm_conj,
    div_self (norm_ne_zero_iff.mpr hn)]

/-- On the line Re z = 1, multiplying the Cayley quotient by 1/normSq z gives -1/z ^ 2.
Use z conjugate(z) = normSq z and the negative-conjugate numerator, then compare
nonzero denominators. This is the first Poisson-weighted Cayley moment. -/
theorem cayley_weighted_first {z : ℂ} (hz : z.re = 1) :
    (1 / (Complex.normSq z : ℂ)) * ((z - 2) / z) = -1 / z ^ 2 := by
  have hn : z ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hz
    norm_num only at hz
  have hs : (Complex.normSq z : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Complex.normSq_pos.mpr hn))
  have he : (Complex.normSq z : ℂ) = -z * (z - 2) := by
    rw [cayley_sub_two_eq_neg_conj hz, mul_neg, neg_mul, neg_neg]
    exact (Complex.mul_conj z).symm
  rw [div_mul_div_comm, one_mul, div_eq_div_iff (mul_ne_zero hs hn) (pow_ne_zero _ hn), he]
  ring

/-- For Re z = 1, complex multiplicity m, and n >= 0, the Poisson-weighted Cayley power
of degree n+1 equals the finite sum of -choose(n,j) (-2) ^ j m / z ^ (j+2).
Remove the first weighted power, write the quotient as 1-2/z, and expand by the binomial
theorem. The identity converts every nonconstant circle moment to inverse-power moments. -/
theorem cayley_weighted_power_expansion {z : ℂ} (hz : z.re = 1) (m : ℂ) (n : ℕ) :
    (m / (Complex.normSq z : ℂ)) * ((z - 2) / z) ^ (n + 1) =
      ∑ j ∈ Finset.range (n + 1), -(n.choose j : ℂ) * (-2 : ℂ) ^ j * (m / z ^ (j + 2)) := by
  have hn : z ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hz
    norm_num only at hz
  have hc : (z - 2) / z = (-2 / z) + 1 := by
    rw [sub_div, div_self hn]
    ring
  calc
    (m / (Complex.normSq z : ℂ)) * ((z - 2) / z) ^ (n + 1) = (-m / z ^ 2) * ((z - 2) / z) ^ n := by
      rw [pow_succ]
      have hh := congrArg (fun w : ℂ => m * w) (cayley_weighted_first hz)
      have he : m / (Complex.normSq z : ℂ) * ((z - 2) / z) = -m / z ^ 2 := by
        convert hh using 1 <;> ring
      rw [show
          m / (Complex.normSq z : ℂ) * (((z - 2) / z) ^ n * ((z - 2) / z)) =
            (m / (Complex.normSq z : ℂ) * ((z - 2) / z)) * ((z - 2) / z) ^ n
          by ring,
        he]
    _ = _ := by
      rw [hc, add_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [one_pow, mul_one, div_pow]
      rw [← mul_assoc, div_mul_div_comm]
      rw [show z ^ 2 * z ^ j = z ^ (j + 2) by
          rw [pow_add]; ring]
      ring

end PseudoPrime.Analysis
