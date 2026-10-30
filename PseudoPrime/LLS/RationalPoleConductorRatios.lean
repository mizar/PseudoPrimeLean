/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.ResidueSubgroup
public import PseudoPrime.LLS.RationalPolePrimeBounds

/-! # Wider small-index conductor conditions from rational-pole kernels -/

@[expose] public section
namespace PseudoPrime.LLS.PaperStatements
/-- The certified rational-pole coefficient and stated conductor ratio leave a
strict margin below the original Theorem 1.3 coefficient. Use a rational lower
logarithm endpoint and exact rational arithmetic; no decimal approximation is assumed. -/
theorem rationalPole_index_four_ratio_gap :
    (623/1000 : ℝ) * (51/100)^2 < (1/4) * (1-1/(4:ℝ))^2 *
      (Real.log (2*(4:ℝ)) / (Real.log (2*(4:ℝ))-4))^2 := by
  have hid : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    have he := Real.log_pow (2 : ℝ) 3
    norm_num only at he
    exact he
  norm_num only
  apply coefficient_lt_of_log_lower (l := (2079/1000 : ℝ))
    (by norm_num only) (by norm_num only) (by norm_num only)
  · rw [hid]
    linarith only [Real.log_two_gt_d9]
  · rw [hid]
    linarith only [Real.log_two_lt_d9]
  · norm_num only
/-- Under GRH and the stated primitive conductor-sum budget, the original
Theorem 1.3 target holds for all sufficiently large moduli uniformly in subgroups.
Transport the rational-pole conductor estimate through its strict ratio gap.
This widens a conditional branch and does not assert the unrestricted theorem. -/
theorem rationalPole_theorem13_index_four
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ Q : ℕ, 20000 ≤ Q ∧ ∀ (q : ℕ) [NeZero q], Q ≤ q →
      ∀ H : Subgroup (ZMod q)ˣ, H.index = 4 →
        subgroupConductorLogSum H ≤ (51/100 : ℝ) * ((4 : ℝ)-1) * Real.log q →
        ∃ p : ℕ, IsLeast (NumberTheory.primesOutside q H) p ∧ (p : ℝ) <
          (1/4) * (1-1/(4:ℝ))^2 *
            (Real.log (2*(4:ℝ)) / (Real.log (2*(4:ℝ))-4))^2 * (Real.log q)^2 := by
  exact least_prime_bound_of_conductor_ratio (by norm_num only : 1 < 4)
    (by norm_num only : (0:ℝ) < 623/1000) (by norm_num only : (0:ℝ) ≤ 51/100)
    rationalPole_index_four_ratio_gap (fun _ hε ↦ rationalPole_index_four_conductor hg hε)
/-- The certified rational-pole coefficient and stated conductor ratio leave a
strict margin below the original Theorem 1.3 coefficient. Use a rational lower
logarithm endpoint and exact rational arithmetic; no decimal approximation is assumed. -/
theorem rationalPole_index_five_ratio_gap :
    (23/40 : ℝ) * (5/7)^2 < (1/4) * (1-1/(5:ℝ))^2 *
      (Real.log (2*(5:ℝ)) / (Real.log (2*(5:ℝ))-4))^2 := by
  have hid : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
    have he := Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0)
      (by norm_num only : (5 : ℝ) ≠ 0)
    norm_num only at he
    exact he
  norm_num only
  apply coefficient_lt_of_log_lower (l := (2302/1000 : ℝ))
    (by norm_num only) (by norm_num only) (by norm_num only)
  · rw [hid]
    linarith only [Real.log_two_gt_d9, Real.log_five_gt_d9]
  · rw [hid]
    linarith only [Real.log_two_lt_d9, Real.log_five_lt_d9]
  · norm_num only
/-- Under GRH and the stated primitive conductor-sum budget, the original
Theorem 1.3 target holds for all sufficiently large moduli uniformly in subgroups.
Transport the rational-pole conductor estimate through its strict ratio gap.
This widens a conditional branch and does not assert the unrestricted theorem. -/
theorem rationalPole_theorem13_index_five
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ Q : ℕ, 20000 ≤ Q ∧ ∀ (q : ℕ) [NeZero q], Q ≤ q →
      ∀ H : Subgroup (ZMod q)ˣ, H.index = 5 →
        subgroupConductorLogSum H ≤ (5/7 : ℝ) * ((5 : ℝ)-1) * Real.log q →
        ∃ p : ℕ, IsLeast (NumberTheory.primesOutside q H) p ∧ (p : ℝ) <
          (1/4) * (1-1/(5:ℝ))^2 *
            (Real.log (2*(5:ℝ)) / (Real.log (2*(5:ℝ))-4))^2 * (Real.log q)^2 := by
  exact least_prime_bound_of_conductor_ratio (by norm_num only : 1 < 5)
    (by norm_num only : (0:ℝ) < 23/40) (by norm_num only : (0:ℝ) ≤ 5/7)
    rationalPole_index_five_ratio_gap (fun _ hε ↦ rationalPole_index_five_conductor hg hε)
/-- The certified rational-pole coefficient and stated conductor ratio leave a
strict margin below the original Theorem 1.3 coefficient. Use a rational lower
logarithm endpoint and exact rational arithmetic; no decimal approximation is assumed. -/
theorem rationalPole_index_six_ratio_gap :
    (549/1000 : ℝ) * (23/25)^2 < (1/4) * (1-1/(6:ℝ))^2 *
      (Real.log (2*(6:ℝ)) / (Real.log (2*(6:ℝ))-4))^2 := by
  have hid : Real.log (12 : ℝ) = 2 * Real.log 2 + Real.log 3 := by
    have he := Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0)
      (by norm_num only : (3 : ℝ) ≠ 0)
    have hp := Real.log_pow (2 : ℝ) 2
    norm_num only at he hp
    rw [hp] at he
    exact he
  norm_num only
  apply coefficient_lt_of_log_lower (l := (2484/1000 : ℝ))
    (by norm_num only) (by norm_num only) (by norm_num only)
  · rw [hid]
    linarith only [Real.log_two_gt_d9, Real.log_three_gt_d9]
  · rw [hid]
    linarith only [Real.log_two_lt_d9, Real.log_three_lt_d9]
  · norm_num only
/-- Under GRH and the stated primitive conductor-sum budget, the original
Theorem 1.3 target holds for all sufficiently large moduli uniformly in subgroups.
Transport the rational-pole conductor estimate through its strict ratio gap.
This widens a conditional branch and does not assert the unrestricted theorem. -/
theorem rationalPole_theorem13_index_six
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ Q : ℕ, 20000 ≤ Q ∧ ∀ (q : ℕ) [NeZero q], Q ≤ q →
      ∀ H : Subgroup (ZMod q)ˣ, H.index = 6 →
        subgroupConductorLogSum H ≤ (23/25 : ℝ) * ((6 : ℝ)-1) * Real.log q →
        ∃ p : ℕ, IsLeast (NumberTheory.primesOutside q H) p ∧ (p : ℝ) <
          (1/4) * (1-1/(6:ℝ))^2 *
            (Real.log (2*(6:ℝ)) / (Real.log (2*(6:ℝ))-4))^2 * (Real.log q)^2 := by
  exact least_prime_bound_of_conductor_ratio (by norm_num only : 1 < 6)
    (by norm_num only : (0:ℝ) < 549/1000) (by norm_num only : (0:ℝ) ≤ 23/25)
    rationalPole_index_six_ratio_gap (fun _ hε ↦ rationalPole_index_six_conductor hg hε)
end PseudoPrime.LLS.PaperStatements
