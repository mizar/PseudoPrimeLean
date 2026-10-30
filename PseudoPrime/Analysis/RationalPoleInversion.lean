/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.InverseMellinRules
public import PseudoPrime.Analysis.InverseMellinShift
public import PseudoPrime.Analysis.MellinLogPowers
public import PseudoPrime.Analysis.RationalPoleKernel

/-! # Inverse Mellin transforms of the single-pole rational family -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For n>=1, sigma>0 and u>0, the inverse of 1/z^(n+1) is the n-th logarithmic
weight divided by n!. Apply the factorial-normalized inversion and cancel its nonzero
constant. This supplies every even pole order required by the rational kernel family. -/
theorem inverseMellin_reciprocal_power {n : ℕ} (hn : 1 ≤ n) {σ u : ℝ} (hσ : 0 < σ) (hu : 0 < u) :
    inverseMellin (fun z : ℂ ↦ 1 / z ^ (n + 1)) σ u =
      mellinLogPowerWeight n u / (n.factorial : ℂ) := by
  have hm :
    inverseMellin (fun z : ℂ ↦ (n.factorial : ℂ) / z ^ (n + 1)) σ u = mellinLogPowerWeight n u := by
    rw [inverseMellin_eq_mellinInv]
    exact mellinInv_logPowerWeight hn hσ hu
  have he :
    (fun z : ℂ ↦ (n.factorial : ℂ) / z ^ (n + 1)) = fun z : ℂ ↦
      (n.factorial : ℂ) * (1 / z ^ (n + 1)) := by
    funext z
    exact (mul_one_div _ _).symm
  rw [he, inverseMellin_const_mul] at hm
  exact (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))).mpr ((mul_comm _ _).trans hm)

/-- For n>=1, u>0 and sigma+rho>0, invert exp(2cz)/(z+rho)^(n+1).
The result is the translated logarithmic weight times (u exp(-2c))^rho/n!.
Exponential translation, pole translation and reciprocal-power inversion prove the formula. -/
theorem inverseMellin_shifted_power {n : ℕ} (hn : 1 ≤ n) {ρ σ u : ℝ} (hσ : 0 < σ + ρ) (hu : 0 < u)
    (c : ℝ) :
    inverseMellin (fun z : ℂ ↦ Complex.exp (2 * (c : ℂ) * z) / (z + ρ) ^ (n + 1)) σ u =
      ((u * Real.exp (-(2 * c)) : ℝ) : ℂ) ^ (ρ : ℂ) *
        (mellinLogPowerWeight n (u * Real.exp (-(2 * c))) / (n.factorial : ℂ)) := by
  have hf :
    (fun z : ℂ ↦ Complex.exp (2 * (c : ℂ) * z) / (z + ρ) ^ (n + 1)) = fun z : ℂ ↦
      Complex.exp (((2 * c : ℝ) : ℂ) * z) * (fun w : ℂ ↦ 1 / w ^ (n + 1)) (z + ρ) := by
    funext z
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, div_eq_mul_inv, one_mul]
  rw [hf, inverseMellin_exp_mul _ _ _ hu,
    inverseMellin_shift (fun w : ℂ ↦ 1 / w ^ (n + 1)) ρ σ (mul_pos hu (Real.exp_pos _)),
    inverseMellin_reciprocal_power hn hσ (mul_pos hu (Real.exp_pos _))]

/-- For a>0, rewrite the rational-pole function as a constant times
exp(2cz)/(z+1/(2a))^(2m). Factor the denominator using the nonzero scale 2a.
This identifies the proposed Fourier-inspired function with the proved inversion family. -/
theorem rationalPole_eq_shifted_power (m : ℕ) {a : ℝ} (ha : 0 < a) (c : ℝ) (z : ℂ) :
    rationalPoleFunction m a c z =
      ((2 * a : ℝ) : ℂ) / ((2 * a : ℝ) : ℂ) ^ (2 * m) *
        (Complex.exp (2 * (c : ℂ) * z) / (z + ((2 * a : ℝ)⁻¹ : ℝ)) ^ (2 * m)) := by
  have hA : ((2 * a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mul_pos (by norm_num only) ha).ne'
  have hd : 1 + 2 * (a : ℂ) * z = ((2 * a : ℝ) : ℂ) * (z + ((2 * a : ℝ)⁻¹ : ℝ)) := by
    rw [Complex.ofReal_inv, mul_add, mul_inv_cancel₀ hA, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  unfold rationalPoleFunction
  rw [hd, mul_pow, div_mul_div_comm]

/-- For m>=1, a>0, u>0 and sigma+1/(2a)>0, invert the rational-pole function
as a scaled translated logarithmic weight. Normalize its denominator and apply the
shifted-power formula. The resulting expression is independent of the vertical line. -/
theorem inverseMellin_rationalPole_log {m : ℕ} (hm : 1 ≤ m) {a σ u : ℝ} (ha : 0 < a)
    (hσ : 0 < σ + (2 * a)⁻¹) (hu : 0 < u) (c : ℝ) :
    inverseMellin (rationalPoleFunction m a c) σ u =
      ((2 * a : ℝ) : ℂ) / ((2 * a : ℝ) : ℂ) ^ (2 * m) *
        (((u * Real.exp (-(2 * c)) : ℝ) : ℂ) ^ (((2 * a : ℝ)⁻¹ : ℝ) : ℂ) *
          (mellinLogPowerWeight (2 * m - 1) (u * Real.exp (-(2 * c))) /
            ((2 * m - 1).factorial : ℂ))) := by
  have hm2 : 2 ≤ 2 * m := by nlinarith only [hm]
  have hn : 1 ≤ 2 * m - 1 := Nat.le_sub_of_add_le hm2
  have he : 2 * m - 1 + 1 = 2 * m := Nat.sub_add_cancel ((by norm_num only : 1 ≤ 2).trans hm2)
  have hf :
    rationalPoleFunction m a c = fun z : ℂ ↦
      (((2 * a : ℝ) : ℂ) / ((2 * a : ℝ) : ℂ) ^ (2 * m)) *
        (Complex.exp (2 * (c : ℂ) * z) / (z + ((2 * a : ℝ)⁻¹ : ℝ)) ^ (2 * m)) :=
    funext (rationalPole_eq_shifted_power m ha c)
  rw [hf, inverseMellin_const_mul]
  congr 1
  exact he ▸ inverseMellin_shifted_power hn hσ hu c

/-- For nonzero A and any natural n, A/A^(n+1) times v^n equals (v/A)^n.
Cancel the single nonzero scale before combining powers. This normalizes the real
profile without clearing or expanding large symbolic denominators. -/
private theorem scaled_power_cancel {A : ℝ} (ha : A ≠ 0) (v : ℝ) (n : ℕ) :
    A / A ^ (n + 1) * v ^ n = (v / A) ^ n := by
  rw [pow_succ, mul_comm (A ^ n) A, div_mul_eq_div_div, div_self ha, one_div_mul_eq_div, ← div_pow]

/-- For m>=1,a>0,u>0, the scaled real logarithmic inverse equals the proposed
rational-pole profile. Split at its exact logarithmic cutoff, identify the exponential
factor and cancel powers of 2a. Both the supported and zero branches are included. -/
theorem scaled_log_eq_rationalPoleProfile {m : ℕ} (hm : 1 ≤ m) {a u : ℝ} (ha : 0 < a) (hu : 0 < u)
    (c : ℝ) :
    (2 * a) / (2 * a) ^ (2 * m) * (u * Real.exp (-(2 * c))) ^ ((2 * a)⁻¹) *
        ((-Real.log (min (u * Real.exp (-(2 * c))) 1)) ^ (2 * m - 1) /
          ((2 * m - 1).factorial : ℕ)) =
      rationalPoleProfile m a c u := by
  have hp := mul_pos hu (Real.exp_pos (-(2 * c)))
  have hl : Real.log (u * Real.exp (-(2 * c))) = Real.log u - 2 * c := by
    rw [Real.log_mul hu.ne' (Real.exp_ne_zero _), Real.log_exp]
    exact rfl
  have he :
    (u * Real.exp (-(2 * c))) ^ ((2 * a)⁻¹) = Real.exp (-((2 * c - Real.log u) / (2 * a))) := by
    rw [Real.rpow_def_of_pos hp, hl]
    congr 1
    simp only [div_eq_mul_inv]
    ring
  have hn : 1 ≤ 2 * m - 1 := Nat.le_sub_of_add_le (by nlinarith only [hm])
  by_cases hcut : Real.log u ≤ 2 * c
  · have ht : u * Real.exp (-(2 * c)) ≤ 1 := by
      apply (Real.log_le_log_iff hp (by norm_num only : (0 : ℝ) < 1)).mp
      rw [hl, Real.log_one]
      exact sub_nonpos.mpr hcut
    rw [min_eq_left ht, hl, he, rationalPoleProfile, ite_eq_left ⟨hu, hcut⟩]
    have hk : 2 * m - 1 + 1 = 2 * m := Nat.sub_add_cancel (show 1 ≤ 2 * m by nlinarith only [hm])
    have hc :
      (2 * a) / (2 * a) ^ (2 * m) * (2 * c - Real.log u) ^ (2 * m - 1) =
        ((2 * c - Real.log u) / (2 * a)) ^ (2 * m - 1) := by
      simpa only [hk] using
        scaled_power_cancel (mul_pos (by norm_num only) ha).ne' (2 * c - Real.log u) (2 * m - 1)
    rw [← mul_div_assoc, mul_right_comm, neg_sub, hc]
  · have ht : 1 ≤ u * Real.exp (-(2 * c)) := by
      apply (Real.log_le_log_iff (by norm_num only : (0 : ℝ) < 1) hp).mp
      rw [hl, Real.log_one]
      exact sub_nonneg.mpr (le_of_not_ge hcut)
    rw [min_eq_right ht, Real.log_one, neg_zero, zero_pow (Nat.ne_zero_of_lt hn), zero_div,
      mul_zero, rationalPoleProfile, ite_eq_right (fun h ↦ hcut h.2)]

/-- For m>=1,a>0,u>0 and a line sigma right of the pole, the actual inverse Mellin
transform of the rational-pole function equals the real nonnegative profile.
Combine logarithmic inversion with the closed real profile identity. This supplies
line independence, reality and positivity for the later admissible-kernel construction. -/
theorem inverseMellin_rationalPole {m : ℕ} (hm : 1 ≤ m) {a σ u : ℝ} (ha : 0 < a)
    (hσ : 0 < σ + (2 * a)⁻¹) (hu : 0 < u) (c : ℝ) :
    inverseMellin (rationalPoleFunction m a c) σ u = (rationalPoleProfile m a c u : ℂ) := by
  have hp := mul_pos hu (Real.exp_pos (-(2 * c)))
  have hn : 1 ≤ 2 * m - 1 := Nat.le_sub_of_add_le (by nlinarith only [hm])
  rw [inverseMellin_rationalPole_log hm ha hσ hu c, ← Complex.ofReal_cpow hp.le,
    logPowerWeight_eq_log_min hn hp]
  rw [← mul_assoc]
  simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_natCast] using
    congrArg Complex.ofReal (scaled_log_eq_rationalPoleProfile hm ha hu c)

end PseudoPrime.Analysis
