/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerBoundary
public import PseudoPrime.LLS.PowerLogTailConvergence

/-! Infinite-tail identity for the refined six-pole Euler weight. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The finite Euler prefixes converge to the complete Euler sum. -/
theorem refined_euler_prefix_tendsto :
    Filter.Tendsto
      (fun n : ℕ ↦ ∑ m ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt m * refinedSixEulerWeight m)
      Filter.atTop
      (nhds (∑' m : ℕ, ArithmeticFunction.vonMangoldt m * refinedSixEulerWeight m)) := by
  have ht :=
    refined_six_euler_weight_summable.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  apply Filter.Tendsto.congr (fun n ↦ ?_) ht
  dsimp only [Function.comp_apply]
  rw [Nat.range_eq_Icc_zero_sub_one (n + 1) (Nat.add_one_ne_zero n), Nat.add_sub_cancel, ←
    Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le n)]
  simp only [ArithmeticFunction.map_zero, zero_mul, add_zero]

/-- Euler tails beyond a fixed cutoff converge to the corresponding infinite tail. -/
theorem refined_euler_tail_tendsto (a : ℝ) :
    Filter.Tendsto
      (fun n : ℕ ↦
        ∑ m ∈ Finset.Ioc ⌊a⌋₊ n, ArithmeticFunction.vonMangoldt m * refinedSixEulerWeight m)
      Filter.atTop
      (nhds
        ((∑' m : ℕ, ArithmeticFunction.vonMangoldt m * refinedSixEulerWeight m) -
          ∑ m ∈ Finset.Ioc 0 ⌊a⌋₊,
            ArithmeticFunction.vonMangoldt m * refinedSixEulerWeight m)) := by
  have ht :=
    refined_euler_prefix_tendsto.sub_const
      (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt m * refinedSixEulerWeight m)
  apply Filter.Tendsto.congr' ?_ ht
  apply (Filter.eventually_ge_atTop ⌊a⌋₊).mono
  intro n hn
  have hd : Disjoint (Finset.Ioc 0 ⌊a⌋₊) (Finset.Ioc ⌊a⌋₊ n) :=
    Finset.disjoint_left.mpr
      (fun m hm ht ↦ (not_lt_of_ge (Finset.mem_Ioc.mp hm).2) (Finset.mem_Ioc.mp ht).1)
  have he :=
    Finset.sum_union (f := fun m ↦ ArithmeticFunction.vonMangoldt m * refinedSixEulerWeight m) hd
  rw [Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hn] at he
  dsimp only
  linarith only [he]

/-- Under RH and boundary decay, the Euler tail equals its double summation-by-parts expression. -/
theorem refined_euler_infinite_tail_of_boundary (hRH : RiemannHypothesis) {a : ℝ} (ha : 3 ≤ a)
    (hb :
      Filter.Tendsto
        (fun t : ℝ ↦
          refinedEulerSlope t * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
            refinedEulerRealWeight t * Chebyshev.psi t)
        Filter.atTop (nhds 0)) :
    (∑' m : ℕ, ArithmeticFunction.vonMangoldt m * refinedSixEulerWeight m) -
        (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt m * refinedSixEulerWeight m) =
      (∫ t in Set.Ioi a,
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * refinedEulerVariation t) +
        (refinedEulerSlope a * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a -
          refinedEulerRealWeight a * Chebyshev.psi a) := by
  have ha0 : 0 < a := by linarith only [ha]
  have hp := refined_euler_tail_tendsto a
  have hi :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi a
      (refined_variation_mangoldt_integrable hRH ha)
      (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop)
  have hb' :=
    hb.comp
      (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop)
  have hr :=
    (hi.sub hb').add_const
      (refinedEulerSlope a * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a -
        refinedEulerRealWeight a * Chebyshev.psi a)
  simp only [sub_zero] at hr
  have he :
    (fun n : ℕ ↦
        ∑ m ∈ Finset.Ioc ⌊a⌋₊ n,
          ArithmeticFunction.vonMangoldt m * refinedSixEulerWeight m) =ᶠ[Filter.atTop]
      (fun n : ℕ ↦
        (∫ t in a..(n : ℝ),
              AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * refinedEulerVariation t) -
            (refinedEulerSlope n * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum n -
              refinedEulerRealWeight n * Chebyshev.psi n) +
          (refinedEulerSlope a * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a -
            refinedEulerRealWeight a * Chebyshev.psi a)) := by
    apply (tendsto_natCast_atTop_atTop.eventually (Filter.eventually_ge_atTop a)).mono
    intro n hn
    simpa only [Nat.floor_natCast] using refined_mangoldt_finite_tail ha0 hn
  exact tendsto_nhds_unique (hp.congr' he) hr

/-- Under RH, the infinite Euler tail equals its double summation-by-parts expression. -/
theorem refined_euler_infinite_tail (hRH : RiemannHypothesis) {a : ℝ} (ha : 3 ≤ a) :
    (∑' m : ℕ, ArithmeticFunction.vonMangoldt m * refinedSixEulerWeight m) -
        (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt m * refinedSixEulerWeight m) =
      (∫ t in Set.Ioi a,
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * refinedEulerVariation t) +
        (refinedEulerSlope a * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a -
          refinedEulerRealWeight a * Chebyshev.psi a) := by
  exact refined_euler_infinite_tail_of_boundary hRH ha (refined_euler_boundary_tendsto hRH)

end PseudoPrime.PrimeTestBounds.MillerRabin
