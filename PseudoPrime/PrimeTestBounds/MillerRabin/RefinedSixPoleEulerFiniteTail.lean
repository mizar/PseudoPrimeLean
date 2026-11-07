/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerVariation
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PowerLogBoundarySummation

/-! # Finite double partial summation for the refined Euler tail -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The clipped logarithmic atom times the refined variation is integrable
on every positive finite interval. Continuity of the clipped logarithm and
variation density establishes the finite-sum interchange. -/
theorem refined_clipped_integrable {v a b : ℝ} (hv : 0 < v) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t ↦ Analysis.positiveLogRatio v t * refinedEulerVariation t)
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  apply ContinuousOn.mul (Analysis.positiveLogRatio_continuous hv).continuousOn
  intro t ht
  have ht0 := ha.trans_le ht.1
  unfold refinedEulerVariation
  exact
    (((Real.continuousAt_rpow_const t (-(79 / 50 : ℝ) - 1) (Or.inl ht0.ne')).mul
            (((continuousAt_const.mul ((Real.continuousAt_log ht0.ne').pow 2)).add
                  (continuousAt_const.mul (Real.continuousAt_log ht0.ne'))).sub
              continuousAt_const)).div_const
        8).continuousWithinAt

/-- A finite weighted sum of positive clipped-log atoms has the exact
refined variation integral and its two endpoint sums. The integrable atom
identity permits interchanging the finite sum and the integral. -/
theorem refined_finite_log_integral {ι : Type*} (S : Finset ι) (c v : ι → ℝ) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hv : ∀ i ∈ S, 0 < v i) (hvb : ∀ i ∈ S, v i ≤ b) :
    (∫ t in a..b, (∑ i ∈ S, c i * Analysis.positiveLogRatio (v i) t) * refinedEulerVariation t) =
      ∑ i ∈ S,
        c i *
          ((Real.log (b / v i) * refinedEulerSlope b - refinedEulerRealWeight b) -
            (Real.log (max a (v i) / v i) * refinedEulerSlope (max a (v i)) -
              refinedEulerRealWeight (max a (v i)))) := by
  simp only [Finset.sum_mul, mul_assoc]
  rw [intervalIntegral.integral_finsetSum
      (fun i hi ↦ (refined_clipped_integrable (hv i hi) ha hab).const_mul (c i))]
  simp only [intervalIntegral.integral_const_mul]
  exact
    Finset.sum_congr rfl
      (fun i hi ↦
        congrArg (fun z : ℝ ↦ c i * z) (refined_clipped_log_integral (hv i hi) ha hab (hvb i hi)))

/-- The finite integral of the logarithmically weighted Mangoldt sum against
the refined variation density equals the explicit clipped endpoint sum.
Represent the arithmetic sum by its finite clipped-log form and apply the
atom identity. No RH or limit to infinity is needed. -/
theorem refined_logWeighted_integral_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b,
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * refinedEulerVariation t) =
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊,
        ArithmeticFunction.vonMangoldt m *
          ((Real.log (b / m) * refinedEulerSlope b - refinedEulerRealWeight b) -
            (Real.log (max a (m : ℝ) / m) * refinedEulerSlope (max a (m : ℝ)) -
              refinedEulerRealWeight (max a (m : ℝ)))) := by
  have hi :=
    refined_finite_log_integral (Finset.Ioc 0 ⌊b⌋₊) (fun m ↦ ArithmeticFunction.vonMangoldt m)
      (fun m ↦ (m : ℝ)) ha hab (fun m hm ↦ Nat.cast_pos.mpr (Finset.mem_Ioc.mp hm).1)
      (fun m hm ↦ (Nat.le_floor_iff (ha.trans_le hab).le).mp (Finset.mem_Ioc.mp hm).2)
  have he :
    (∫ t in a..b,
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * refinedEulerVariation t) =
      ∫ t in a..b,
        (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊,
            ArithmeticFunction.vonMangoldt m * Analysis.positiveLogRatio (m : ℝ) t) *
          refinedEulerVariation t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have h :=
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum_eq_clipped_scaled (x := (1 : ℝ))
        (by norm_num only) (ha.trans_le ht.1).le ht.2
    simp only [one_mul, div_one] at h
    dsimp only
    rw [h]
  exact he.trans hi

/-- The finite refined upper boundary sum equals logarithmic slope times
the smoothed Mangoldt sum minus weight times Chebyshev psi. Expanding the
finite sums gives the exact boundary used in the tail formula. -/
theorem refined_boundary_sum_eq (b : ℝ) :
    (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊,
        ArithmeticFunction.vonMangoldt m *
          (Real.log (b / m) * refinedEulerSlope b - refinedEulerRealWeight b)) =
      refinedEulerSlope b * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum b -
        refinedEulerRealWeight b * Chebyshev.psi b := by
  rw [Chebyshev.psi_eq_sum_Icc, ← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le _),
    ArithmeticFunction.map_zero, add_zero]
  simp only [AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum,
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun m hm ↦ by ring)

/-- The lower clipped endpoint splits into its Chebyshev boundary minus the
finite refined Euler tail. Splitting at the lower cutoff preserves prime
powers on the correct side of the open endpoint. -/
theorem refined_clipped_lower_boundary {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊,
        ArithmeticFunction.vonMangoldt m *
          (Real.log (max a (m : ℝ) / m) * refinedEulerSlope (max a (m : ℝ)) -
            refinedEulerRealWeight (max a (m : ℝ)))) =
      (refinedEulerSlope a * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a -
          refinedEulerRealWeight a * Chebyshev.psi a) -
        ∑ m ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
          ArithmeticFunction.vonMangoldt m * refinedEulerRealWeight m := by
  rw [AnalyticNumberTheory.Arithmetic.power_prefix_sum_split hab]
  have hp :
    (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊,
        ArithmeticFunction.vonMangoldt m *
          (Real.log (max a (m : ℝ) / m) * refinedEulerSlope (max a (m : ℝ)) -
            refinedEulerRealWeight (max a (m : ℝ)))) =
      refinedEulerSlope a * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a -
        refinedEulerRealWeight a * Chebyshev.psi a := by
    rw [← refined_boundary_sum_eq a]
    exact
      Finset.sum_congr rfl
        (fun m hm ↦ by rw [max_eq_left ((Nat.le_floor_iff ha.le).mp (Finset.mem_Ioc.mp hm).2)])
  rw [hp]
  have ht :
    (∑ m ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
        ArithmeticFunction.vonMangoldt m *
          (Real.log (max a (m : ℝ) / m) * refinedEulerSlope (max a (m : ℝ)) -
            refinedEulerRealWeight (max a (m : ℝ)))) =
      -(∑ m ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
          ArithmeticFunction.vonMangoldt m * refinedEulerRealWeight m) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    rw [max_eq_right ((Nat.floor_lt ha.le).mp (Finset.mem_Ioc.mp hm).1).le, Real.log_div_self,
      zero_mul, zero_sub]
    ring
  rw [ht]
  ring

/-- On a positive finite interval, the refined Euler tail equals the
log-weighted variation integral with exact lower and upper Chebyshev boundary
terms. Combine the finite atom formula and the two boundary identities.
This is the finite double-Abel identity for the total Euler-mass estimate. -/
theorem refined_mangoldt_finite_tail {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∑ m ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt m * refinedSixEulerWeight m) =
      (∫ t in a..b,
            AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * refinedEulerVariation t) -
          (refinedEulerSlope b * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum b -
            refinedEulerRealWeight b * Chebyshev.psi b) +
        (refinedEulerSlope a * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a -
          refinedEulerRealWeight a * Chebyshev.psi a) := by
  have h := refined_logWeighted_integral_eq ha hab
  have he :
    (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊,
        ArithmeticFunction.vonMangoldt m *
          ((Real.log (b / m) * refinedEulerSlope b - refinedEulerRealWeight b) -
            (Real.log (max a (m : ℝ) / m) * refinedEulerSlope (max a (m : ℝ)) -
              refinedEulerRealWeight (max a (m : ℝ))))) =
      (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊,
          ArithmeticFunction.vonMangoldt m *
            (Real.log (b / m) * refinedEulerSlope b - refinedEulerRealWeight b)) -
        (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊,
          ArithmeticFunction.vonMangoldt m *
            (Real.log (max a (m : ℝ) / m) * refinedEulerSlope (max a (m : ℝ)) -
              refinedEulerRealWeight (max a (m : ℝ)))) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  rw [he, refined_boundary_sum_eq b, refined_clipped_lower_boundary ha hab] at h
  simp only [refined_weight_nat] at h
  linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
