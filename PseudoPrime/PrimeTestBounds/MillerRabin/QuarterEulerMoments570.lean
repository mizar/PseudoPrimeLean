/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerError570
public import PseudoPrime.Analysis.LogPowerTailIntegral

/-! # Endpoint evaluation of the section 31 Euler integrals -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A logarithmic moment of degree k with decay exponent d+1, used to integrate the Euler tail. -/
noncomputable def eulerMoment570 (d : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  Real.log t ^ k * t ^ (-d - 1)

/-- The closed upper-tail integral of the logarithmic moment at a positive endpoint. -/
noncomputable def eulerMomentValue570 (d : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  t ^ (-d) * Analysis.logPowerTailPoly d k (Real.log t)

/-- For positive decay and ordered endpoints above one, subtract the two improper moments
to evaluate the finite integral. -/
theorem eulerMoment570_interval {d a b : ℝ} (hd : 0 < d) (ha : 1 ≤ a) (hab : a ≤ b) (k : ℕ) :
    (∫ t : ℝ in a..b, eulerMoment570 d k t) =
      eulerMomentValue570 d k a - eulerMomentValue570 d k b := by
  have hi := Analysis.log_power_tail_integrable hd ha k
  unfold eulerMoment570 eulerMomentValue570
  rw [← intervalIntegral.integral_Ioi_sub_Ioi hi hab, Analysis.log_power_tail_integral hd ha,
    Analysis.log_power_tail_integral hd (ha.trans hab)]

/-- Integrate a quadratic in the logarithm times a shifted logarithmic moment by evaluating
its three monomials at the endpoints. -/
theorem euler570_polynomial_interval {d a b : ℝ} (hd : 0 < d) (ha : 1 ≤ a) (hab : a ≤ b) {f : ℝ → ℝ}
    (c : Fin 3 → ℝ) (k : ℕ)
    (hf : ∀ t ∈ Set.Icc a b, f t = ∑ j : Fin 3, c j * eulerMoment570 d (k + j.val) t) :
    (∫ t : ℝ in a..b, f t) =
      ∑ j : Fin 3,
        c j * (eulerMomentValue570 d (k + j.val) a - eulerMomentValue570 d (k + j.val) b) := by
  have hi (j : Fin 3) :
    IntervalIntegrable (fun t ↦ c j * eulerMoment570 d (k + j.val) t) MeasureTheory.volume a b := by
    apply IntervalIntegrable.const_mul
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact (Analysis.log_power_tail_integrable hd ha (k + j.val)).mono_set Set.Ioc_subset_Ioi_self
  rw [intervalIntegral.integral_congr
      (by
        intro t ht; exact hf t (Set.uIcc_of_le hab ▸ ht)),
    intervalIntegral.integral_finsetSum (fun j _ ↦ hi j)]
  exact
    Finset.sum_congr rfl
      (fun j _ ↦ by rw [intervalIntegral.integral_const_mul, eulerMoment570_interval hd ha hab])

/-- Evaluate the main Euler integral on an interval above one at decay exponent 13/25. -/
theorem euler570_main_interval {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, eulerDensity570 t) =
      ∑ j : Fin 3,
        ![(3 / 8 : ℝ), 153 / 400, 2601 / 20000] j *
          (eulerMomentValue570 (13 / 25) j.val a - eulerMomentValue570 (13 / 25) j.val b) := by
  apply euler570_polynomial_interval (k := 0) (by norm_num only) ha hab
  intro t ht
  rw [Fin.sum_univ_three]
  change
    _ =
      3 / 8 * eulerMoment570 _ 0 t + 153 / 400 * eulerMoment570 _ 1 t +
        2601 / 20000 * eulerMoment570 _ 2 t
  unfold eulerMoment570 eulerDensity570
  rw [show -(13 / 25 : ℝ) - 1 = -(38 / 25 : ℝ) by norm_num only]
  ring

/-- Evaluate the four-fifths square-root error integral via moments of degrees zero to two. -/
theorem euler570_low_interval {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, (4 / 5 : ℝ) * Real.sqrt t * -eulerSlope570 t) =
      ∑ j : Fin 3,
        ![(4 / 5 : ℝ) * (3 / 16), (4 / 5 : ℝ) * (3213 / 10000), (4 / 5 : ℝ) * (49419 / 250000)] j *
          (eulerMomentValue570 (51 / 50) (0 + j.val) a -
            eulerMomentValue570 (51 / 50) (0 + j.val) b) := by
  apply euler570_polynomial_interval (by norm_num only) ha hab
  intro t ht
  have hp : 0 < t := zero_lt_one.trans_le (ha.trans ht.1)
  have he : Real.sqrt t * t ^ (-(63 / 25 : ℝ)) = t ^ (-(51 / 50 : ℝ) - 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp]
    norm_num only
  rw [Fin.sum_univ_three]
  change
    _ =
      (4 / 5 : ℝ) * (3 / 16) * eulerMoment570 _ 0 t +
        (4 / 5 : ℝ) * (3213 / 10000) * eulerMoment570 _ 1 t +
        (4 / 5 : ℝ) * (49419 / 250000) * eulerMoment570 _ 2 t
  unfold eulerSlope570 eulerMoment570
  rw [← he]
  ring

/-- Evaluate the RH log-square error integral via moments of degrees two to four. -/
theorem euler570_high_interval {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, Real.sqrt t * (Real.log t ^ 2 / 24) * -eulerSlope570 t) =
      ∑ j : Fin 3,
        ![(1 / 24 : ℝ) * (3 / 16), (1 / 24 : ℝ) * (3213 / 10000), (1 / 24 : ℝ) * (49419 / 250000)]
            j *
          (eulerMomentValue570 (51 / 50) (2 + j.val) a -
            eulerMomentValue570 (51 / 50) (2 + j.val) b) := by
  apply euler570_polynomial_interval (by norm_num only) ha hab
  intro t ht
  have hp : 0 < t := zero_lt_one.trans_le (ha.trans ht.1)
  have he : Real.sqrt t * t ^ (-(63 / 25 : ℝ)) = t ^ (-(51 / 50 : ℝ) - 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp]
    norm_num only
  rw [Fin.sum_univ_three]
  change
    _ =
      (1 / 24 : ℝ) * (3 / 16) * eulerMoment570 _ 2 t +
        (1 / 24 : ℝ) * (3213 / 10000) * eulerMoment570 _ 3 t +
        (1 / 24 : ℝ) * (49419 / 250000) * eulerMoment570 _ 4 t
  unfold eulerSlope570 eulerMoment570
  rw [← he]
  ring

/-- Any finite remainder past 2701 meeting the rational threshold supplies the total Euler
mass required by the three-character estimate, by positivity of the omitted terms. -/
theorem euler570_total_of_interval {N : ℕ} (hN : 2701 ≤ N)
    (h :
      (1335906798741 / 2500000000000 : ℝ) ≤
        ∑ n ∈ Finset.Ioc 2701 N, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) :
    37275 / 10000 ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n := by
  have ht :=
    quarter_euler_weight_summable_570.sum_le_tsum (Finset.Ioc 0 N)
      (fun n _ ↦
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (quarter_euler_weight_nonneg_570_all n))
  rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le 2701) hN,
    Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)] at ht
  linarith only [quarter_euler_prefix_lower_570, h, ht]

end PseudoPrime.PrimeTestBounds.MillerRabin
