/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedDifferences

/-!
# Finite measures associated with scaled Mangoldt sums

Place mass `max(Λ(n)/x, 0)` at `n/x` for each member of a finite index set.
For positive scale, integration and interval masses recover the normalized arithmetic sums.
This connects interval asymptotics to bounded continuous test functions.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For a finite set of natural indices and a real scale, place nonnegative mass
`max(Λ(n)/x, 0)` at `n/x`. The measure is finite because it is a finite sum of weighted
point masses. At positive scale its integrals represent normalized Mangoldt sums,
which are used in the truncated Mellin-kernel comparison. -/
noncomputable def scaledMangoldtMeasure (s : Finset ℕ) (x : ℝ) : MeasureTheory.FiniteMeasure ℝ :=
  ∑ n ∈ s,
    (ArithmeticFunction.vonMangoldt n / x).toNNReal •
      (show MeasureTheory.FiniteMeasure ℝ from
        ⟨MeasureTheory.Measure.dirac ((n : ℝ) / x), inferInstance⟩)

/-- At positive scale, integration against the finite Mangoldt measure equals the
weighted arithmetic sum divided by the scale. Evaluate each weighted Dirac integral and
sum. No regularity of the real test function is needed for this finite atomic identity. -/
theorem integral_scaledMangoldtMeasure (s : Finset ℕ) {x : ℝ} (hx : 0 < x) (f : ℝ → ℝ) :
    (∫ u, f u ∂(scaledMangoldtMeasure s x : MeasureTheory.Measure ℝ)) =
      (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * f ((n : ℝ) / x)) / x := by
  rw [scaledMangoldtMeasure, MeasureTheory.FiniteMeasure.toMeasure_sum]
  rw [MeasureTheory.integral_finsetSum_measure]
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    rw [MeasureTheory.FiniteMeasure.toMeasure_smul, MeasureTheory.integral_smul_nnreal_measure]
    change
      (ArithmeticFunction.vonMangoldt n / x).toNNReal *
          (∫ u, f u ∂MeasureTheory.Measure.dirac ((n : ℝ) / x)) =
        _
    rw [MeasureTheory.integral_dirac,
      Real.coe_toNNReal _ (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_of_lt hx))]
    ring
  · intro n hn
    rw [MeasureTheory.FiniteMeasure.toMeasure_smul]
    exact (MeasureTheory.integrable_dirac (by finiteness)).smul_measure_nnreal

open Classical in
/-- On a measurable set, the real mass is the normalized Mangoldt sum over indices whose
scaled point lies in the set. Integrate its indicator using the atomic integral identity.
This is the set-mass interface for proving weak convergence. -/
theorem scaledMangoldtMeasure_apply_real (s : Finset ℕ) {x : ℝ} (hx : 0 < x) {A : Set ℝ}
    (hA : MeasurableSet A) :
    (scaledMangoldtMeasure s x A : ℝ) =
      (∑ n ∈ s with (((n : ℕ) : ℝ) / x) ∈ A, ArithmeticFunction.vonMangoldt n) / x := by
  classical
  have h := integral_scaledMangoldtMeasure s hx (A.indicator (fun _ ↦ 1))
  rw [MeasureTheory.integral_indicator_const 1 hA,
    MeasureTheory.FiniteMeasure.measureReal_eq_coe_coeFn, smul_eq_mul, mul_one] at h
  rw [h, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hm : (n : ℝ) / x ∈ A
  · rw [Set.indicator_of_mem hm, ite_eq_left hm, mul_one]
  · rw [Set.indicator_of_notMem hm, ite_eq_right hm, mul_zero]

/-- For positive scale, total mass is the Mangoldt sum over the finite index set divided
by the scale. Apply the atomic integral formula to the constant one function.
This supplies the total-mass hypothesis of the finite-measure convergence criterion. -/
theorem scaledMangoldtMeasure_mass_real (s : Finset ℕ) {x : ℝ} (hx : 0 < x) :
    ((scaledMangoldtMeasure s x).mass : ℝ) = (∑ n ∈ s, ArithmeticFunction.vonMangoldt n) / x := by
  have h := integral_scaledMangoldtMeasure s hx (fun _ ↦ 1)
  rw [MeasureTheory.integral_const, MeasureTheory.FiniteMeasure.measureReal_eq_coe_coeFn,
    smul_eq_mul, mul_one] at h
  simpa only [MeasureTheory.FiniteMeasure.mass, mul_one] using h

/-- For a nonzero natural index and positive scale, membership in the interval of
floors is equivalent to membership of the scaled point in the real half-open interval.
The nonzero condition permits negative endpoints. This converts cutoff intersections. -/
theorem mem_scaled_Ioc {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) (a b : ℝ) :
    n ∈ Finset.Ioc ⌊a * x⌋₊ ⌊b * x⌋₊ ↔ (n : ℝ) / x ∈ Set.Ioc a b := by
  rw [Finset.mem_Ioc, Nat.floor_lt' hn, Nat.le_floor_iff' hn, Set.mem_Ioc, lt_div_iff₀ hx,
    div_le_iff₀ hx]

open Classical in
/-- Filtering scaled natural indices by a second real interval gives the interval with
maximum lower endpoint and minimum upper endpoint. Remove zero, translate membership
through the floor inequalities, and regroup the bounds. Empty intersections are allowed. -/
theorem filter_scaled_Ioc {x : ℝ} (hx : 0 < x) (a b c d : ℝ) :
    (Finset.Ioc ⌊a * x⌋₊ ⌊b * x⌋₊).filter (fun n : ℕ ↦ (n : ℝ) / x ∈ Set.Ioc c d) =
      Finset.Ioc ⌊max a c * x⌋₊ ⌊min b d * x⌋₊ := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.not_lt_zero, false_and]
  · rw [Finset.mem_filter, mem_scaled_Ioc hx hn, mem_scaled_Ioc hx hn, Set.mem_Ioc, Set.mem_Ioc,
      Set.mem_Ioc, max_lt_iff, le_min_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      exact ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
    · rintro ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
      exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩

open Classical in
/-- The mass of a half-open interval for a cutoff Mangoldt measure is the normalized
sum over the intersection of the two scaled intervals. Combine the set-mass identity and
cutoff filtering. This is the interval input to the continuous-weight limit theorem. -/
theorem scaledMangoldtMeasure_Ioc_real {x : ℝ} (hx : 0 < x) (a b c d : ℝ) :
    (scaledMangoldtMeasure (Finset.Ioc ⌊a * x⌋₊ ⌊b * x⌋₊) x (Set.Ioc c d) : ℝ) =
      (∑ n ∈ Finset.Ioc ⌊max a c * x⌋₊ ⌊min b d * x⌋₊, ArithmeticFunction.vonMangoldt n) / x := by
  rw [scaledMangoldtMeasure_apply_real _ hx measurableSet_Ioc]
  convert
    congrArg (fun s : Finset ℕ ↦ (∑ n ∈ s, ArithmeticFunction.vonMangoldt n) / x)
      (filter_scaled_Ioc hx a b c d) using
    1
  congr 3

end PseudoPrime.AnalyticNumberTheory.Arithmetic
