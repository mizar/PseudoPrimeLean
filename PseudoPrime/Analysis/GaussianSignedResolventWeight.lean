/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SignedExponentialMoments
public import PseudoPrime.Analysis.GaussianResolventCertificate

/-! # Nonnegative signed Gaussian Euler weights from finite moment certificates -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The rational moment at degree n after reflecting the Gaussian scales at seven.
These moments certify positivity of the signed exponential combination. -/
def gaussianResolventMoment (n : ℕ) : ℚ :=
  (gaussianResolventCoefficients.map (fun ab ↦ ab.2 * (7 - ab.1) ^ n)).sum

/-- The first thirty-two Gaussian moments are nonnegative by exact rational arithmetic. -/
theorem gaussianResolvent_small_moments : ∀ n ∈ Finset.range 32, 0 ≤ gaussianResolventMoment n := by
  decide +kernel

/-- Casting the rational Gaussian moment gives its real signed power sum. -/
theorem gaussianResolvent_moment_cast (n : ℕ) :
    (gaussianResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ) * (7 - (ab.1 : ℝ)) ^ n)).sum =
      (gaussianResolventMoment n : ℝ) := by
  norm_num only [gaussianResolventMoment, gaussianResolventCoefficients, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Rat.cast_add, Rat.cast_mul, Rat.cast_sub,
    Rat.cast_pow, Rat.cast_ofNat, Rat.cast_div]

/-- Below degree thirty-two, the real Gaussian moments inherit rational positivity. -/
theorem gaussianResolvent_small_moments_real {n : ℕ} (hn : n < 32) :
    0 ≤ (gaussianResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ) * (7 - (ab.1 : ℝ)) ^ n)).sum := by
  rw [gaussianResolvent_moment_cast]
  exact Rat.cast_nonneg.mpr (gaussianResolvent_small_moments n (Finset.mem_range.mpr hn))

/-- All reflected tail scales lie between zero and the first reflected scale. -/
theorem gaussianResolvent_tail_range :
    gaussianResolventCoefficients.tail.Forall
      (fun ab ↦ (0 : ℚ) ≤ 7 - ab.1 ∧ 7 - ab.1 ≤ 7 - 110 / 200) := by
  decide +kernel

/-- At degree thirty-two the first positive coefficient dominates all negative tail terms. -/
theorem gaussianResolvent_anchor_dominates :
    (gaussianResolventCoefficients.tail.map
          (fun ab ↦ max 0 (-(ab.2 : ℝ)) * (7 - (ab.1 : ℝ)) ^ 32)).sum ≤
      (61938394 / 100000000 : ℝ) * (7 - 110 / 200) ^ 32 := by
  norm_num only [gaussianResolventCoefficients, List.tail_cons, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, max_def, ite_true, ite_false]

/-- Every Gaussian moment is nonnegative. The finite prefix is checked exactly;
anchor domination propagates the tail to every higher degree. -/
theorem gaussianResolvent_all_moments_nonneg :
    ∀ n : ℕ,
      0 ≤ (gaussianResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ) * (7 - (ab.1 : ℝ)) ^ n)).sum := by
  change
    ∀ n : ℕ,
      0 ≤
        ((((110 / 200 : ℚ), (61938394 / 100000000 : ℚ)) :: gaussianResolventCoefficients.tail).map
            (fun ab ↦ (ab.2 : ℝ) * (7 - (ab.1 : ℝ)) ^ n)).sum
  apply list_moments_nonneg_of_finite_certificate (N := 32)
  · norm_num only
  · intro ab hab
    have hq := List.forall_iff_forall_mem.mp gaussianResolvent_tail_range ab hab
    have h1 := Rat.cast_nonneg (K := ℝ) |>.mpr hq.1
    have h2 := Rat.cast_le (K := ℝ) |>.mpr hq.2
    norm_num only [Rat.cast_sub, Rat.cast_ofNat, Rat.cast_div] at h1 h2 ⊢
    exact ⟨h1, h2⟩
  · intro n hn
    change 0 ≤ (gaussianResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ) * (7 - (ab.1 : ℝ)) ^ n)).sum
    exact gaussianResolvent_small_moments_real hn
  · have h := gaussianResolvent_anchor_dominates
    norm_num only at h ⊢
    exact h

/-- The signed Gaussian Euler weight at a real base m, retaining all twelve coefficients.
It multiplies Mangoldt terms in the real-axis zero-mass identity. -/
noncomputable def gaussianResolventEulerWeight (m : ℝ) : ℝ :=
  (gaussianResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ) * m ^ (-(1 / 2 + (ab.1 : ℝ))))).sum

/-- At a positive base the Gaussian Euler weight factors into a positive exponential
and the exponential combination of reflected scales. -/
theorem gaussianResolventEulerWeight_eq_exp_moments {m : ℝ} (hm : 0 < m) :
    gaussianResolventEulerWeight m =
      Real.exp (-(15 / 2 : ℝ) * Real.log m) *
        (gaussianResolventCoefficients.map
            (fun ab ↦ (ab.2 : ℝ) * Real.exp ((7 - (ab.1 : ℝ)) * Real.log m))).sum := by
  unfold gaussianResolventEulerWeight
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab _
  rw [Real.rpow_def_of_pos hm]
  have he :
    Real.log m * (-(1 / 2 + (ab.1 : ℝ))) =
      -(15 / 2 : ℝ) * Real.log m + (7 - (ab.1 : ℝ)) * Real.log m := by
    ring
  rw [he, Real.exp_add]
  ring

/-- For every real m at least one, the signed Gaussian Euler weight is nonnegative.
Expand the reflected exponential combination using its nonnegative moments. -/
theorem gaussian_resolvent_euler_weight_nonneg {m : ℝ} (hm : 1 ≤ m) :
    0 ≤ gaussianResolventEulerWeight m := by
  rw [gaussianResolventEulerWeight_eq_exp_moments (zero_lt_one.trans_le hm)]
  exact
    mul_nonneg (Real.exp_pos _).le
      (list_exp_nonneg_of_moments gaussianResolventCoefficients (fun ab ↦ (ab.2 : ℝ))
        (fun ab ↦ 7 - (ab.1 : ℝ)) gaussianResolvent_all_moments_nonneg (Real.log_nonneg hm))

end PseudoPrime.Analysis
