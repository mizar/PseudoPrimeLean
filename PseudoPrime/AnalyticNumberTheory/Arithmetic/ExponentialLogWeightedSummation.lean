/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialLogKernel
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedSummationByParts
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExponentialMangoldtBounds

/-! # Finite logarithmic partial summation for the full exponential weight -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A real multiplier transports the finite exponential atom identity to a
weighted clipped-log integral and its two boundary terms. Move the constant
outside the integral. This supports the finite Mangoldt summation. -/
private theorem weighted_exponential_atom {v y : ℝ} (hv : 0 < v) (hvy : v ≤ y) (c : ℝ) :
    c * Real.exp (-v) =
      (∫ u in (0 : ℝ)..y, (c * Analysis.positiveLogRatio v u) * ((u - 1) * Real.exp (-u))) +
        (y * Real.exp (-y)) * (c * Analysis.positiveLogRatio v y) +
        Real.exp (-y) * c := by
  have h := congrArg (fun z : ℝ ↦ c * z) (Analysis.exponential_log_atom hv hvy)
  rw [Analysis.positiveLogRatio_eq_log hvy]
  simp only [mul_assoc, intervalIntegral.integral_const_mul]
  linarith only [h]

/-- For finitely many positive atoms through y, express their exponential
weighted sum by the clipped logarithmic integral and two endpoint sums.
Interchange the finite sum with the integral using continuous products.
This retains the endpoints needed before passing to the full series. -/
theorem finite_sum_exponential_eq_log_integral {ι : Type*} (s : Finset ι) (c v : ι → ℝ) {y : ℝ}
    (hv : ∀ i ∈ s, 0 < v i) (hvy : ∀ i ∈ s, v i ≤ y) :
    (∑ i ∈ s, c i * Real.exp (-v i)) =
      (∫ u in (0 : ℝ)..y,
          (∑ i ∈ s, c i * Analysis.positiveLogRatio (v i) u) * ((u - 1) * Real.exp (-u))) +
        (y * Real.exp (-y)) * (∑ i ∈ s, c i * Analysis.positiveLogRatio (v i) y) +
        Real.exp (-y) * (∑ i ∈ s, c i) := by
  have he := Finset.sum_congr rfl (fun i hi ↦ weighted_exponential_atom (hv i hi) (hvy i hi) (c i))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at he
  rw [←
    intervalIntegral.integral_finsetSum
      (fun i hi ↦
        (show
              Continuous
                (fun u : ℝ ↦ (c i * Analysis.positiveLogRatio (v i) u) * ((u - 1) * Real.exp (-u)))
              from
              (continuous_const.mul (Analysis.positiveLogRatio_continuous (hv i hi))).mul
                ((continuous_id.sub continuous_const).mul
                  (Real.continuous_exp.comp continuous_id.neg))).intervalIntegrable
          (0 : ℝ) y)] at he
  simpa only [Finset.sum_mul] using he

/-- The Chebyshev psi sum equals its positive-index finite sum.
Remove the vanishing von Mangoldt term at zero. This matches the logarithmic cutoff convention. -/
private theorem psi_eq_sum_Ioc (t : ℝ) :
    Chebyshev.psi t = ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt n := by
  rw [Chebyshev.psi_eq_sum_Icc, ← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le _),
    ArithmeticFunction.map_zero, add_zero]

/-- The finite exponential Mangoldt sum equals the positive-index sum
with coefficients on the left of exp(-n/x). Remove the zero term and commute products.
This connects the atom identity to the existing arithmetic definition. -/
private theorem exponential_sum_eq_positive_sum (x y : ℝ) :
    exponentialMangoldtSum x (x * y) =
      ∑ n ∈ Finset.Ioc 0 ⌊x * y⌋₊,
        ArithmeticFunction.vonMangoldt n * Real.exp (-((n : ℝ) / x)) := by
  rw [exponentialMangoldtSum, ← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le _)]
  simp only [ArithmeticFunction.map_zero, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro n _
  rw [neg_div, mul_comm]

/-- For x>0 and y>=0, the actual exponential Mangoldt sum through xy equals
the logarithmically weighted integral plus y exp(-y)A(xy) and exp(-y)psi(xy).
Use the finite atom reconstruction, justified interchange, and arithmetic cutoff identities.
This is the exact double-partial-summation formula with its finite endpoint terms. -/
theorem exponentialMangoldtSum_eq_logWeighted_integral {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    exponentialMangoldtSum x (x * y) =
      (∫ u in (0 : ℝ)..y, logWeightedMangoldtSum (x * u) * ((u - 1) * Real.exp (-u))) +
        y * Real.exp (-y) * logWeightedMangoldtSum (x * y) +
        Real.exp (-y) * Chebyshev.psi (x * y) := by
  have h :=
    finite_sum_exponential_eq_log_integral (y := y) (Finset.Ioc 0 ⌊x * y⌋₊)
      (fun n ↦ ArithmeticFunction.vonMangoldt n) (fun n ↦ (n : ℝ) / x)
      (fun n hn ↦ div_pos (Nat.cast_pos.mpr (Finset.mem_Ioc.mp hn).1) hx)
      (fun n hn ↦
        (div_le_iff₀ hx).mpr
          (by
            have he := (Nat.le_floor_iff (mul_nonneg hx.le hy)).mp (Finset.mem_Ioc.mp hn).2
            linarith only [he]))
  have hi :
    (∫ u in (0 : ℝ)..y,
        (∑ n ∈ Finset.Ioc 0 ⌊x * y⌋₊,
            ArithmeticFunction.vonMangoldt n * Analysis.positiveLogRatio ((n : ℝ) / x) u) *
          ((u - 1) * Real.exp (-u))) =
      ∫ u in (0 : ℝ)..y, logWeightedMangoldtSum (x * u) * ((u - 1) * Real.exp (-u)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hy] at hu
    dsimp only
    rw [← logWeightedMangoldtSum_eq_clipped_scaled hx hu.1 hu.2]
  rw [← exponential_sum_eq_positive_sum, hi, ←
    logWeightedMangoldtSum_eq_clipped_scaled hx hy le_rfl, ← psi_eq_sum_Ioc] at h
  exact h

/-- At positive scale, the logarithmically weighted sum A(xu) is continuous
on every nonnegative-cutoff interval [0,y]. Use its fixed finite clipped-log
representation. This supplies integrability for the quantitative error decomposition. -/
theorem continuousOn_logWeightedMangoldtSum_scaled {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ContinuousOn (fun u ↦ logWeightedMangoldtSum (x * u)) (Set.Icc 0 y) := by
  have hc :
    Continuous
      (fun u ↦
        ∑ n ∈ Finset.Ioc 0 ⌊x * y⌋₊,
          ArithmeticFunction.vonMangoldt n * Analysis.positiveLogRatio ((n : ℝ) / x) u) :=
    continuous_finsetSum _
      (fun n hn ↦
        continuous_const.mul
          (Analysis.positiveLogRatio_continuous
            (div_pos (Nat.cast_pos.mpr (Finset.mem_Ioc.mp hn).1) hx)))
  exact hc.continuousOn.congr (fun u hu ↦ logWeightedMangoldtSum_eq_clipped_scaled hx hu.1 hu.2)

/-- Every positive Mangoldt coefficient in the cutoff interval is at most
the real cutoff. Use Lambda(n)<=log(n)<=n-1 and the floor bound.
This supplies an elementary polynomial bound for the psi endpoint. -/
private theorem vonMangoldt_le_cutoff {t : ℝ} (ht : 0 ≤ t) {n : ℕ} (hn : n ∈ Finset.Ioc 0 ⌊t⌋₊) :
    ArithmeticFunction.vonMangoldt n ≤ t := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Finset.mem_Ioc.mp hn).1
  have hnle : (n : ℝ) ≤ t := (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le ht)
  linarith only [ArithmeticFunction.vonMangoldt_le_log (n := n), Real.log_le_sub_one_of_pos hnpos,
    hnle]

/-- For t>=0, psi(t)<=t^2. Bound each positive coefficient by t and the
number of indices by floor(t)<=t. This polynomial estimate is used only to
prove exponential decay of the endpoint, without a quantitative PNT input. -/
theorem psi_le_self_sq {t : ℝ} (ht : 0 ≤ t) : Chebyshev.psi t ≤ t ^ 2 := by
  have he := Finset.sum_le_sum (fun n hn ↦ vonMangoldt_le_cutoff ht hn)
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc, Nat.sub_zero] at he
  rw [psi_eq_sum_Ioc]
  have hm := mul_le_mul_of_nonneg_right (Nat.floor_le ht) ht
  nlinarith only [he, hm]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
