/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogDirichletNumericalBounds

/-! # Finite Dirichlet prefixes with exact logarithmic and power integral tails -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For r>0 and c>=1, evaluate the envelope integral from c to infinity exactly.
Apply its derivative primitive and the zero endpoint limit on the restricted half-line.
This retains the cutoff dependence lost by evaluating every tail from one. -/
theorem integral_logPower_envelope_tail {r c : ℝ} (hr : 0 < r) (hc : 1 ≤ c) :
    (∫ x : ℝ in Set.Ioi c, (Real.log x + 1) * x ^ (-r - 1)) =
      (Real.log c / r + r⁻¹ ^ 2 + r⁻¹) * c ^ (-r) := by
  have hi :=
    (integrableOn_logPower_envelope hr).mono_set
      (show Set.Ioi c ⊆ Set.Ioi 1 from fun x hx ↦ hc.trans_lt hx)
  have he :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun x hx ↦ hasDerivAt_logPower_primitive hr (zero_lt_one.trans_le (hc.trans hx))) hi
      (tendsto_logPower_primitive_zero hr)
  simpa only [zero_sub, neg_mul, neg_neg] using he

/-- For r>0 and c>=1, the logarithmic-power tail integral is
c^(-r)*(log(c)/r+r^(-2)). Subtract the pure power integral from the envelope integral.
This is the explicit tail used in the truncated zeta-derivative numerator. -/
theorem integral_logPower_tail {r c : ℝ} (hr : 0 < r) (hc : 1 ≤ c) :
    (∫ x : ℝ in Set.Ioi c, Real.log x * x ^ (-r - 1)) = c ^ (-r) * (Real.log c / r + r⁻¹ ^ 2) := by
  have hc0 := zero_lt_one.trans_le hc
  have hs : Set.Ioi c ⊆ Set.Ioi 1 := fun x hx ↦ hc.trans_lt hx
  have hi := (integrableOn_logPower hr).mono_set hs
  have hpow := integrableOn_Ioi_rpow_of_lt (by linarith only [hr] : -r - 1 < -1) hc0
  have hv := integral_Ioi_rpow_of_lt (by linarith only [hr] : -r - 1 < -1) hc0
  rw [show -r - 1 + 1 = -r by ring, div_neg, neg_div, neg_neg] at hv
  have he := integral_logPower_envelope_tail hr hc
  have hf :
    (fun x : ℝ ↦ (Real.log x + 1) * x ^ (-r - 1)) =
      (fun x : ℝ ↦ Real.log x * x ^ (-r - 1) + x ^ (-r - 1)) := by
    funext x; ring
  rw [hf, MeasureTheory.integral_add hi hpow, hv] at he
  simp only [div_eq_mul_inv] at he ⊢
  nlinarith only [he]

/-- The finite logarithmic-power sum through N plus its exact integral tail from N.
Inputs r and N are totalized; the upper-bound theorem assumes r>0 and N>=3.
This approximates the full logarithmic Dirichlet numerator without discarding its prefix. -/
noncomputable def truncatedLogDirichletUpper (r : ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.range (N + 1), Real.log n * (n : ℝ) ^ (-r - 1)) +
    (N : ℝ) ^ (-r) * (Real.log N / r + r⁻¹ ^ 2)

/-- The finite power sum through N plus the exact integral tail from N+1.
Inputs r and N are totalized; the lower-bound theorem assumes r>0.
The strict positive tail makes this a valid denominator in the Euler-ratio bound. -/
noncomputable def truncatedPowerDirichletLower (r : ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.range (N + 1), (n : ℝ) ^ (-r - 1)) + ((N + 1 : ℕ) : ℝ) ^ (-r) / r

/-- For r>0 and any natural cutoff, the truncated logarithmic numerator is nonnegative.
Every natural logarithm and real power term is nonnegative, as is the integral expression.
This permits replacing the full denominator by a positive lower bound. -/
theorem truncatedLogDirichletUpper_nonneg {r : ℝ} (hr : 0 < r) (N : ℕ) :
    0 ≤ truncatedLogDirichletUpper r N := by
  exact
    add_nonneg
      (Finset.sum_nonneg
        (fun n _ ↦ mul_nonneg (Real.log_natCast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)))
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
        (add_nonneg (div_nonneg (Real.log_natCast_nonneg N) hr.le) (sq_nonneg r⁻¹)))

/-- For r>0 and any natural cutoff, the truncated power denominator is strictly positive.
Its finite sum is nonnegative and its tail from N+1 is strictly positive.
This supplies the nonzero denominator premise for explicit Euler caps. -/
theorem truncatedPowerDirichletLower_pos {r : ℝ} (hr : 0 < r) (N : ℕ) :
    0 < truncatedPowerDirichletLower r N := by
  exact
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun n _ ↦ Real.rpow_nonneg (Nat.cast_nonneg n) _))
      (div_pos (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.succ_pos N)) _) hr)

/-- For r>0 the natural logarithmic-power Dirichlet series is summable.
Dominate its norm by the established logarithmic envelope termwise.
This justifies exact separation of any finite prefix from the infinite tail. -/
theorem summable_logPower {r : ℝ} (hr : 0 < r) :
    Summable (fun n : ℕ ↦ Real.log n * (n : ℝ) ^ (-r - 1)) := by
  apply (summable_logPower_envelope hr).of_norm_bounded
  intro n
  rw [Real.norm_of_nonneg
      (mul_nonneg (Real.log_natCast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _))]
  exact
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- For r>0 and cutoff N>=3, the full logarithmic-power series is at most the finite
prefix through N plus its integral tail from N. Restrict monotonicity and integrability
to the cutoff half-line, apply the integral test and split the summable series.
This preserves a sharp numerator for finite-scale Euler estimates. -/
theorem tsum_logPower_le_truncated {r : ℝ} (hr : 0 < r) {N : ℕ} (hN : 3 ≤ N) :
    (∑' n : ℕ, Real.log n * (n : ℝ) ^ (-r - 1)) ≤ truncatedLogDirichletUpper r N := by
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by linarith only [hN3]
  have hi :=
    (integrableOn_logPower hr).mono_set
      (show Set.Ioi (N : ℝ) ⊆ Set.Ioi 1 from fun x hx ↦ hN1.trans_lt hx)
  have ha :=
    (antitoneOn_logPower_three hr).mono
      (show Set.Ici (N : ℝ) ⊆ Set.Ici 3 from fun x hx ↦ hN3.trans hx)
  have ht :=
    AntitoneOn.tsum_comp_add_le_integral N ha hi
      (fun x hx ↦
        mul_nonneg (Real.log_nonneg (hN1.trans hx.le))
          (Real.rpow_nonneg ((zero_lt_one.trans_le hN1).trans hx).le _))
  rw [integral_logPower_tail hr hN1] at ht
  have hs := (summable_logPower hr).sum_add_tsum_nat_add (N + 1)
  have he :
    (∑' n : ℕ, Real.log (n + (N + 1) : ℕ) * (n + (N + 1) : ℕ) ^ (-r - 1)) ≤
      (N : ℝ) ^ (-r) * (Real.log N / r + r⁻¹ ^ 2) := by
    simpa only [Nat.add_assoc] using ht
  rw [← hs]
  exact add_le_add (le_refl _) he

/-- For r>0 and any natural cutoff N, the finite power sum through N plus its integral
from N+1 is at most the full power series. Use monotonicity of the negative power
and the lower integral test. This retains the finite denominator prefix exactly. -/
theorem truncatedPowerDirichletLower_le_tsum {r : ℝ} (hr : 0 < r) (N : ℕ) :
    truncatedPowerDirichletLower r N ≤ ∑' n : ℕ, (n : ℝ) ^ (-r - 1) := by
  have hc : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos N)
  have ht :=
    AntitoneOn.integral_le_tsum_comp_add (N + 1) (antitoneOn_neg_rpow hr hc) (summable_neg_rpow hr)
      (fun x hx ↦ Real.rpow_nonneg (hc.trans hx).le _)
  have hv := integral_Ioi_rpow_of_lt (by linarith only [hr] : -r - 1 < -1) hc
  rw [show -r - 1 + 1 = -r by ring, div_neg, neg_div, neg_neg] at hv
  rw [hv] at ht
  rw [← (summable_neg_rpow hr).sum_add_tsum_nat_add (N + 1)]
  exact add_le_add (le_refl _) ht

/-- For r>0 and N>=3, advancing the cutoff decreases the logarithmic numerator cap.
Compare the next summand with its preceding unit integral. This supports cutoff refinement. -/
theorem truncatedLogDirichletUpper_succ_le {r : ℝ} (hr : 0 < r) {N : ℕ} (hN : 3 ≤ N) :
    truncatedLogDirichletUpper r (N + 1) ≤ truncatedLogDirichletUpper r N := by
  let f := fun x : ℝ ↦ Real.log x * x ^ (-r - 1)
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by linarith only [hN3]
  have hi : MeasureTheory.IntegrableOn f (Set.Ioi (N : ℝ)) :=
    (integrableOn_logPower hr).mono_set (fun x hx ↦ hN1.trans_lt hx)
  have hi1 : MeasureTheory.IntegrableOn f (Set.Ioi ((N : ℝ) + 1)) :=
    hi.mono_set (fun x hx ↦ (lt_add_one (N : ℝ)).trans hx)
  have ha : AntitoneOn f (Set.Icc (N : ℝ) ((N : ℝ) + 1)) :=
    (antitoneOn_logPower_three hr).mono (fun x hx ↦ hN3.trans hx.1)
  have hcell :=
    AntitoneOn.sum_le_integral (f := f) (x₀ := (N : ℝ)) (a := 1)
      (by simpa only [Nat.cast_one] using ha)
  simp only [Finset.sum_range_one, Nat.zero_add, Nat.cast_one] at hcell
  have hs := intervalIntegral.integral_interval_add_Ioi hi hi1
  dsimp only [f] at hcell hs
  rw [integral_logPower_tail hr (by linarith only [hN1]), integral_logPower_tail hr hN1] at hs
  unfold truncatedLogDirichletUpper
  rw [Finset.sum_range_succ]
  simp only [Nat.cast_add, Nat.cast_one]
  linarith only [hcell, hs]

/-- For r>0 and any cutoff N, advancing the cutoff increases the power denominator floor.
Compare a unit integral with its left endpoint. This supports cutoff refinement. -/
theorem truncatedPowerDirichletLower_le_succ {r : ℝ} (hr : 0 < r) (N : ℕ) :
    truncatedPowerDirichletLower r N ≤ truncatedPowerDirichletLower r (N + 1) := by
  let f := fun x : ℝ ↦ x ^ (-r - 1)
  let a := (N : ℝ) + 1
  have ha0 : 0 < a := by
    dsimp only [a]; linarith only [(show (0 : ℝ) ≤ N from Nat.cast_nonneg N)]
  have hi : MeasureTheory.IntegrableOn f (Set.Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by linarith only [hr]) ha0
  have hi1 : MeasureTheory.IntegrableOn f (Set.Ioi (a + 1)) :=
    hi.mono_set (fun x hx ↦ (lt_add_one a).trans hx)
  have ha : AntitoneOn f (Set.Icc a (a + 1)) := (antitoneOn_neg_rpow hr ha0).mono (fun x hx ↦ hx.1)
  have hcell :=
    AntitoneOn.integral_le_sum (f := f) (x₀ := a) (a := 1) (by simpa only [Nat.cast_one] using ha)
  simp only [Finset.sum_range_one, Nat.cast_one, Nat.cast_zero, add_zero] at hcell
  have hs := intervalIntegral.integral_interval_add_Ioi hi hi1
  have hv (c : ℝ) (hc : 0 < c) : (∫ x : ℝ in Set.Ioi c, f x) = c ^ (-r) / r := by
    dsimp only [f]
    rw [integral_Ioi_rpow_of_lt (by linarith only [hr] : -r - 1 < -1) hc,
      show -r - 1 + 1 = -r by ring, div_neg, neg_div, neg_neg]
  rw [hv a ha0, hv (a + 1) (by linarith only [ha0])] at hs
  dsimp only [a, f] at hs hcell
  unfold truncatedPowerDirichletLower
  nth_rw 2 [Finset.sum_range_succ]
  simp only [Nat.cast_add, Nat.cast_one]
  linarith only [hcell, hs]

/-- For r>0 and 3<=N<=M, the numerator cap at M is at most its value at N.
Iterate the one-step integral comparison; larger finite prefixes improve the cap. -/
theorem truncatedLogDirichletUpper_antitone_cutoff {r : ℝ} (hr : 0 < r) {N M : ℕ} (hN : 3 ≤ N)
    (hNM : N ≤ M) : truncatedLogDirichletUpper r M ≤ truncatedLogDirichletUpper r N := by
  induction M, hNM using Nat.le_induction with
  | base => exact le_refl _
  | succ k hNk ih => exact (truncatedLogDirichletUpper_succ_le hr (hN.trans hNk)).trans ih

/-- For r>0 and N<=M, the denominator floor at N is at most its value at M.
Iterate the one-step comparison; larger finite prefixes improve the floor. -/
theorem truncatedPowerDirichletLower_monotone_cutoff {r : ℝ} (hr : 0 < r) {N M : ℕ} (hNM : N ≤ M) :
    truncatedPowerDirichletLower r N ≤ truncatedPowerDirichletLower r M := by
  induction M, hNM using Nat.le_induction with
  | base => exact le_refl _
  | succ k _ ih => exact ih.trans (truncatedPowerDirichletLower_le_succ hr k)

/-- For r>0 and N>=3, the truncated numerator cap is bounded by the coarse Euler numerator.
Reduce to cutoff three and bound its finite terms and integral tail. This compares both APIs. -/
theorem truncatedLogDirichletUpper_le_euler_numerator {r : ℝ} (hr : 0 < r) {N : ℕ} (hN : 3 ≤ N) :
    truncatedLogDirichletUpper r N ≤ r⁻¹ ^ 2 + (r + 1)⁻¹ := by
  apply (truncatedLogDirichletUpper_antitone_cutoff hr (N := 3) (by norm_num only) hN).trans
  have hs : Set.Ioi (3 : ℝ) ⊆ Set.Ioi 1 := fun x hx ↦ lt_trans (by norm_num only : (1 : ℝ) < 3) hx
  have ht :=
    MeasureTheory.setIntegral_mono_set (integrableOn_logPower hr)
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
        exact mul_nonneg (Real.log_nonneg hx.le) (Real.rpow_nonneg (zero_lt_one.trans hx).le _))
      (Filter.Eventually.of_forall hs)
  rw [integral_logPower hr, integral_logPower_tail hr (by norm_num only)] at ht
  have h2 :=
    logPower_le_half_inv (by linarith only [hr] : 0 < r + 1) (by norm_num only : (1 : ℝ) ≤ 2)
  have h3 :=
    logPower_le_half_inv (by linarith only [hr] : 0 < r + 1) (by norm_num only : (1 : ℝ) ≤ 3)
  rw [show -(r + 1) = -r - 1 by ring] at h2 h3
  simp only [one_div] at h2 h3
  have he : (2 * (r + 1))⁻¹ = (r + 1)⁻¹ / 2 := by rw [mul_inv, div_eq_mul_inv, mul_comm]
  rw [he] at h2 h3
  norm_num only [truncatedLogDirichletUpper, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, Real.log_zero, Real.log_one, zero_mul, zero_add,
    add_zero]
  linarith only [ht, h2, h3]

/-- For r>0 and N>=1, the truncated denominator floor dominates the coarse Euler denominator.
Evaluate cutoff one and use cutoff monotonicity. This compares both APIs. -/
theorem euler_denominator_le_truncatedPowerDirichletLower {r : ℝ} (hr : 0 < r) {N : ℕ}
    (hN : 1 ≤ N) : 1 + (2 : ℝ) ^ (-r) / r ≤ truncatedPowerDirichletLower r N := by
  have hB := truncatedPowerDirichletLower_monotone_cutoff hr (N := 1) hN
  have he : truncatedPowerDirichletLower r 1 = 1 + (2 : ℝ) ^ (-r) / r := by
    norm_num only [truncatedPowerDirichletLower, Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat,
      Real.zero_rpow (by linarith only [hr] : -r - 1 ≠ 0), Real.one_rpow, zero_add]
  rw [he] at hB
  exact hB

end PseudoPrime.Analysis
