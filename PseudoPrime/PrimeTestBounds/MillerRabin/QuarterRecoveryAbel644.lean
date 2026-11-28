/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterRecovery644
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1423toMillion

/-! # Centered Abel lower bound for the additional reflected recovery -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem finite_abel_lower {a b : ℝ} (ha : 1423 ≤ a) (hab : a ≤ b) (hb : b ≤ 1000000)
    {f g : ℝ → ℝ} (hd : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hf : ContinuousOn (deriv f) (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hle : ∀ t ∈ Set.Icc a b, |deriv f t| ≤ g t) (hfa : 0 ≤ f a) (hfb : 0 ≤ f b) :
    (∫ t in a..b, f t) - (4 / 5) * Real.sqrt a * f a - (4 / 5) * Real.sqrt b * f b -
        (∫ t in a..b, (4 / 5) * Real.sqrt t * g t) ≤
      ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * f n := by
  have hψ (t : ℝ) (ht : t ∈ Set.Icc a b) :=
    AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million (ha.trans ht.1) (ht.2.trans hb)
  have he :
    |∫ t in a..b, (Chebyshev.psi t - t) * deriv f t| ≤
      ∫ t in a..b, (4 / 5) * Real.sqrt t * g t := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab, ←
      Real.norm_eq_abs]
    have hc : ContinuousOn (fun t ↦ (4 / 5 : ℝ) * Real.sqrt t * g t) (Set.Icc a b) :=
      (continuousOn_const.mul Real.continuous_sqrt.continuousOn).mul hg
    apply
      MeasureTheory.norm_integral_le_of_norm_le
        (hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    have ht' : t ∈ Set.Icc a b := ⟨ht.1.le, ht.2⟩
    rw [Real.norm_eq_abs, abs_mul]
    exact
      mul_le_mul (hψ t ht') (hle t ht') (abs_nonneg _)
        (mul_nonneg (by norm_num only) (Real.sqrt_nonneg _))
  have h :=
    AnalyticNumberTheory.Arithmetic.mangoldt_centered_abel_interval (by linarith only [ha]) hab hd
      hf.integrableOn_Icc
  have h₁ := mul_le_mul_of_nonneg_right (abs_le.mp (hψ a (Set.left_mem_Icc.mpr hab))).2 hfa
  have h₂ := mul_le_mul_of_nonneg_right (abs_le.mp (hψ b (Set.right_mem_Icc.mpr hab))).1 hfb
  linarith only [h, h₁, h₂, (abs_le.mp he).2]

/-- The reflected prime-power weight with a fixed logarithmic shift z. -/
noncomputable def quarterReflectedWeight (z t : ℝ) : ℝ :=
  t ^ (-(157 / 100) : ℝ) * (z + Real.log t) ^ 5

private theorem reflected_weight_deriv (z : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (quarterReflectedWeight z)
      (t ^ (-(257 / 100) : ℝ) * (z + Real.log t) ^ 4 * (5 - (157 / 100) * (z + Real.log t))) t := by
  have h :=
    (Real.hasDerivAt_rpow_const (p := -(157 / 100 : ℝ)) (Or.inl ht.ne')).mul
      (((Real.hasDerivAt_log ht.ne').const_add z).pow 5)
  apply h.congr_deriv
  have hp : -(157 / 100 : ℝ) - 1 = -(257 / 100) := by norm_num only
  rw [hp,
    show t ^ (-(157 / 100 : ℝ)) = t ^ (-(257 / 100 : ℝ)) * t
      by
      rw [← Real.rpow_add_one ht.ne']
      norm_num only]
  norm_num only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub]
  field_simp [ht.ne']
  ring

private theorem reflected_weight_bound (z : ℝ) (hz : 0 ≤ z) {t : ℝ} (ht : 2701 ≤ t) :
    |deriv (quarterReflectedWeight z) t| ≤
      (157 / 100 : ℝ) * t ^ (-(257 / 100) : ℝ) * (z + Real.log t) ^ 5 := by
  have hp : 0 < t := by linarith only [ht]
  have hlog : 4 ≤ Real.log t := by
    have he := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 4
    apply (Real.le_log_iff_exp_le hp).mpr
    rw [show (4 : ℝ) = (4 : ℕ) * (1 : ℝ) by norm_num only, Real.exp_natCast_mul]
    linarith only [he, ht]
  have h₀ : 0 ≤ t ^ (-(257 / 100) : ℝ) * (z + Real.log t) ^ 4 :=
    mul_nonneg (Real.rpow_nonneg hp.le _) (pow_nonneg (by linarith only [hz, hlog]) _)
  have h₁ : 5 - (157 / 100 : ℝ) * (z + Real.log t) ≤ 0 := by linarith only [hz, hlog]
  rw [(reflected_weight_deriv z hp).deriv, abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos h₀ h₁)]
  nlinarith only [h₀]

/-- Centered Abel summation bounds the recovered sum by its main integral
minus both square-root boundary costs and an integral bounding the slope error.
The logarithmic shift is nonnegative, as required by the section 122 weight. -/
theorem quarter_recovery_abel_644 {z : ℝ} (hz : 0 ≤ z) :
    let f := quarterReflectedWeight z
    (∫ t in (2701 : ℝ)..99000, f t) - (4 / 5) * Real.sqrt 2701 * f 2701 -
        (4 / 5) * Real.sqrt 99000 * f 99000 -
        (∫ t in (2701 : ℝ)..99000,
          (4 / 5) * Real.sqrt t * ((157 / 100) * t ^ (-(257 / 100) : ℝ) * (z + Real.log t) ^ 5)) ≤
      ∑ n ∈ Finset.Ioc 2701 99000, ArithmeticFunction.vonMangoldt n * f n := by
  intro f
  have hp (t : ℝ) (ht : t ∈ Set.Icc (2701 : ℝ) 99000) : 0 < t := by linarith only [ht.1]
  have hd (t : ℝ) (ht : t ∈ Set.Icc (2701 : ℝ) 99000) := reflected_weight_deriv z (hp t ht)
  have hc (t : ℝ) (ht : t ∈ Set.Icc (2701 : ℝ) 99000) :=
    continuousAt_const.add (Real.continuousAt_log (hp t ht).ne') (f := fun _ : ℝ ↦ z)
  have hx (t : ℝ) (ht : t ∈ Set.Icc (2701 : ℝ) 99000) :=
    Real.continuousAt_rpow_const t (-(257 / 100 : ℝ)) (Or.inl (hp t ht).ne')
  have hf : ContinuousOn (deriv f) (Set.Icc 2701 99000) := by
    apply ContinuousOn.congr _ (fun t ht ↦ (hd t ht).deriv)
    intro t ht
    exact
      (((hx t ht).mul ((hc t ht).pow 4)).mul
          (continuousAt_const.sub (continuousAt_const.mul (hc t ht)))).continuousWithinAt
  have hg :
    ContinuousOn (fun t : ℝ ↦ (157 / 100) * t ^ (-(257 / 100) : ℝ) * (z + Real.log t) ^ 5)
      (Set.Icc 2701 99000) := by
    intro t ht
    exact ((continuousAt_const.mul (hx t ht)).mul ((hc t ht).pow 5)).continuousWithinAt
  have hn (t : ℝ) (ht : 1 ≤ t) : 0 ≤ f t :=
    mul_nonneg (Real.rpow_nonneg (zero_le_one.trans ht) _)
      (pow_nonneg (add_nonneg hz (Real.log_nonneg ht)) _)
  have h :=
    finite_abel_lower (a := 2701) (b := 99000) (by norm_num only) (by norm_num only)
      (by norm_num only) (fun t ht ↦ (hd t ht).differentiableAt) hf hg
      (fun t ht ↦ reflected_weight_bound z hz ht.1) (hn _ (by norm_num only))
      (hn _ (by norm_num only))
  simpa only [Nat.floor_ofNat] using h

private theorem shifted_moment_deriv {d t : ℝ} (hd : 0 < d) (ht : 0 < t) (z : ℝ) :
    HasDerivAt (fun x : ℝ ↦ -x ^ (-d) * Analysis.logPowerTailPoly d 5 (z + Real.log x))
      (t ^ (-d - 1) * (z + Real.log t) ^ 5) t := by
  have hp := (Real.hasDerivAt_rpow_const (p := -d) (Or.inl ht.ne')).neg
  have hl :=
    (Analysis.log_power_tail_poly_deriv hd 5 (z + Real.log t)).comp t
      ((Real.hasDerivAt_log ht.ne').const_add z)
  apply (hp.mul hl).congr_deriv
  dsimp only [Pi.neg_apply, Function.comp_apply]
  rw [Real.rpow_sub_one ht.ne']
  ring

private theorem shifted_moment_integral {d a b : ℝ} (hd : 0 < d) (ha : 0 < a) (hab : a ≤ b)
    (z : ℝ) :
    (∫ t in a..b, t ^ (-d - 1) * (z + Real.log t) ^ 5) =
      a ^ (-d) * Analysis.logPowerTailPoly d 5 (z + Real.log a) -
        b ^ (-d) * Analysis.logPowerTailPoly d 5 (z + Real.log b) := by
  have hc : ContinuousOn (fun t : ℝ ↦ t ^ (-d - 1) * (z + Real.log t) ^ 5) (Set.uIcc a b) := by
    intro t ht
    have ht' := (ha.trans_le ((Set.uIcc_of_le hab) ▸ ht).1).ne'
    exact
      ((Real.continuousAt_rpow_const t _ (Or.inl ht')).mul
          ((continuousAt_const.add (Real.continuousAt_log ht')).pow 5)).continuousWithinAt
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦ shifted_moment_deriv hd (ha.trans_le ((Set.uIcc_of_le hab) ▸ ht).1) z)
      hc.intervalIntegrable
  rw [h]
  ring

/-- Evaluate the two integrals in the reflected Abel lower bound by the
shifted logarithmic moments at 2701 and 99000. Both boundary costs remain. -/
theorem quarter_recovery_moments_644 {z : ℝ} (hz : 0 ≤ z) :
    let P := fun (d t : ℝ) ↦ t ^ (-d) * Analysis.logPowerTailPoly d 5 (z + Real.log t)
    P (57 / 100) 2701 - P (57 / 100) 99000 -
        (4 / 5) *
          ((2701 : ℝ) ^ (-(107 / 100) : ℝ) * (z + Real.log 2701) ^ 5 +
            (99000 : ℝ) ^ (-(107 / 100) : ℝ) * (z + Real.log 99000) ^ 5 +
            (157 / 100) * (P (107 / 100) 2701 - P (107 / 100) 99000)) ≤
      ∑ n ∈ Finset.Ioc 2701 99000,
        ArithmeticFunction.vonMangoldt n * quarterReflectedWeight z n := by
  intro P
  have hm :=
    shifted_moment_integral (d := 57 / 100) (a := 2701) (b := 99000) (by norm_num only)
      (by norm_num only) (by norm_num only) z
  have he :=
    shifted_moment_integral (d := 107 / 100) (a := 2701) (b := 99000) (by norm_num only)
      (by norm_num only) (by norm_num only) z
  rw [show -(57 / 100 : ℝ) - 1 = -(157 / 100) by norm_num only] at hm
  have h := quarter_recovery_abel_644 hz
  dsimp only at h
  unfold quarterReflectedWeight at h
  rw [hm] at h
  have hs (t : ℝ) (ht : 0 < t) : Real.sqrt t * t ^ (-(157 / 100) : ℝ) = t ^ (-(107 / 100) : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht]
    norm_num only
  have hI :
    (∫ t in (2701 : ℝ)..99000,
        (4 / 5) * Real.sqrt t * ((157 / 100) * t ^ (-(257 / 100) : ℝ) * (z + Real.log t) ^ 5)) =
      ((4 / 5) * (157 / 100)) * (P (107 / 100) 2701 - P (107 / 100) 99000) := by
    rw [← he, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    have hp : 0 < t :=
      lt_of_lt_of_le (by norm_num only)
        ((Set.uIcc_of_le (by norm_num only : (2701 : ℝ) ≤ 99000)) ▸ ht).1
    have hx : Real.sqrt t * t ^ (-(257 / 100) : ℝ) = t ^ (-(107 / 100 : ℝ) - 1) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp]
      norm_num only
    linear_combination ((4 / 5) * (157 / 100) * (z + Real.log t) ^ 5) * hx
  rw [hI] at h
  dsimp only [P] at h ⊢
  have hB (t : ℝ) (ht : 0 < t) :
    (4 / 5) * Real.sqrt t * (t ^ (-(157 / 100) : ℝ) * (z + Real.log t) ^ 5) =
      (4 / 5) * t ^ (-(107 / 100) : ℝ) * (z + Real.log t) ^ 5 := by
    linear_combination ((4 / 5) * (z + Real.log t) ^ 5) * hs t ht
  rw [hB 2701 (by norm_num only), hB 99000 (by norm_num only)] at h
  unfold quarterReflectedWeight
  linarith only [h]

/-- Any lower bound of the endpoint reflected sum at radius 322
is also a lower bound for the normalized recovery after multiplication
by its positive Mellin factor, uniformly on the four section 122 rows. -/
theorem quarter_recovery_of_sum_644 {r M : ℝ} (hr : r ∈ Set.Icc 316 322)
    (hM :
      M ≤
        ∑ n ∈ Finset.Ioc 2701 99000,
          ArithmeticFunction.vonMangoldt n *
            quarterReflectedWeight (2687 / 1000 + 2 * Real.log 322) n) :
    (4 * (107 / 100 : ℝ) ^ 5 * Real.exp (-(107 / 100) * (2687 / 1000)) / 120) *
        (322 : ℝ) ^ (-(107 / 50) : ℝ) *
        M ≤
      quarterRecovery644 r := by
  apply le_trans _ (quarter_recovery_at_322 hr)
  unfold quarterRecovery644
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (mul_le_mul_of_nonneg_left hM (Real.rpow_nonneg (by norm_num only) _)).trans_eq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  unfold quarterReflectedWeight quarterRecoveryFactor
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
