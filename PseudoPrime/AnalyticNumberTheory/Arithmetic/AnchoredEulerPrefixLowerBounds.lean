/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PowerLogBoundarySummation
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExponentialLogWeightedSummation
public import PseudoPrime.LLS.PairedEulerExcludedBounds
public import PseudoPrime.LLS.RiemannWeightedErrorBounds
public import PseudoPrime.LLS.ReflectedSplitWitnessBounds
public import PseudoPrime.LLS.VariableRampPrincipalBounds

/-! # Anchored analytic lower bounds for finite Euler prefixes -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For a nonnegative exponent, positive ordered endpoints and a continuous lower
profile F for the actual logarithmically weighted sum, the displayed integral and
boundary expression bounds the Mangoldt power tail below. Use exact double partial
summation, integral monotonicity and nonnegative psi at the upper endpoint.
This keeps an exact finite anchor while estimating only the subsequent tail. -/
theorem power_mangoldt_tail_ge_of_logWeighted_lower {σ a b : ℝ} (hσ : 0 ≤ σ) (ha : 0 < a)
    (hab : a ≤ b) (F : ℝ → ℝ) (hF : ContinuousOn F (Set.Icc a b))
    (hl : ∀ t ∈ Set.Icc a b, F t ≤ logWeightedMangoldtSum t) :
    (∫ t in a..b, F t * (σ ^ 2 * t ^ (-σ - 1))) -
          a ^ (-σ) * (Chebyshev.psi a + σ * logWeightedMangoldtSum a) +
        b ^ (-σ) * (σ * F b) ≤
      ∑ m ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-σ) := by
  have hpos : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht ↦ ha.trans_le ht.1
  have hA0 := continuousOn_logWeightedMangoldtSum_scaled (x := 1) (by norm_num only) b
  simp only [one_mul] at hA0
  have hA : ContinuousOn logWeightedMangoldtSum (Set.Icc a b) :=
    hA0.mono (fun t ht ↦ ⟨ha.le.trans ht.1, ht.2⟩)
  have hw : ContinuousOn (fun t : ℝ ↦ σ ^ 2 * t ^ (-σ - 1)) (Set.Icc a b) :=
    continuousOn_const.mul (continuousOn_id.rpow_const (fun t ht ↦ Or.inl (hpos t ht).ne'))
  have hiF := (hF.mul hw)
  have hiA := (hA.mul hw)
  rw [← Set.uIcc_of_le hab] at hiF hiA
  have hi :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab hiF.intervalIntegrable
      hiA.intervalIntegrable
      (fun t ht ↦
        mul_le_mul_of_nonneg_right (hl t ht)
          (mul_nonneg (sq_nonneg σ) (Real.rpow_nonneg (hpos t ht).le _)))
  simp only [Pi.mul_apply] at hi
  have hb :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hl b ⟨hab, le_rfl⟩) hσ)
      (Real.rpow_nonneg (ha.trans_le hab).le (-σ))
  have hp := mul_nonneg (Real.rpow_nonneg (ha.trans_le hab).le (-σ)) (Chebyshev.psi_nonneg b)
  rw [power_mangoldt_tail_eq_log_integral σ ha hab]
  nlinarith only [hi, hb, hp]

/-- The finite Mangoldt power prefix at anchor a plus an analytic tail lower expression
to cutoff b. The upper psi term is dropped, and a lower smoothed profile F replaces
the upper smoothed value and integral. This gives a compact alternative to enumerating
all terms up to b. -/
noncomputable def anchoredPowerPrefixLower (σ a b : ℝ) (F : ℝ → ℝ) : ℝ :=
  (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-σ)) +
        (∫ t in a..b, F t * (σ ^ 2 * t ^ (-σ - 1))) -
      a ^ (-σ) * (Chebyshev.psi a + σ * logWeightedMangoldtSum a) +
    b ^ (-σ) * (σ * F b)

/-- Under the continuous smoothed lower-profile assumptions and nonnegative exponent,
the anchored expression bounds the full finite Mangoldt power prefix below.
Add the exact retained prefix to the proved tail bound. This connects the analytic
estimate to a finite arithmetic sum. -/
theorem anchoredPowerPrefixLower_le {σ a b : ℝ} (hσ : 0 ≤ σ) (ha : 0 < a) (hab : a ≤ b) (F : ℝ → ℝ)
    (hF : ContinuousOn F (Set.Icc a b)) (hl : ∀ t ∈ Set.Icc a b, F t ≤ logWeightedMangoldtSum t) :
    anchoredPowerPrefixLower σ a b F ≤
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-σ) := by
  have ht := power_mangoldt_tail_ge_of_logWeighted_lower hσ ha hab F hF hl
  rw [power_prefix_sum_split hab]
  dsimp only [anchoredPowerPrefixLower]
  linarith only [ht]

/-- For nonnegative power exponent and logarithmic coefficient and positive ordered
cutoffs, retain the logarithmic Euler contribution at the anchor while bounding
the first power prefix analytically. Nonnegativity lets the logarithmic prefix
grow to the upper cutoff. This supplies the paired Euler weight used by witnesses. -/
theorem anchoredPowerPrefixLower_add_logPrefix_le {σ τ c a b : ℝ} (hσ : 0 ≤ σ) (hc : 0 ≤ c)
    (ha : 0 < a) (hab : a ≤ b) (F : ℝ → ℝ) (hF : ContinuousOn F (Set.Icc a b))
    (hl : ∀ t ∈ Set.Icc a b, F t ≤ logWeightedMangoldtSum t) :
    anchoredPowerPrefixLower σ a b F +
        (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, c * Real.log m * ArithmeticFunction.vonMangoldt m / (m : ℝ) ^ τ) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, pairedEulerPrefixWeight σ τ c m := by
  have hp := anchoredPowerPrefixLower_le hσ ha hab F hF hl
  have he :
    (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-σ)) =
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, ArithmeticFunction.vonMangoldt m / (m : ℝ) ^ σ := by
    apply Finset.sum_congr rfl
    intro m _
    rw [Real.rpow_neg (Nat.cast_nonneg m), div_eq_mul_inv]
  have hsub : Finset.Ioc 0 ⌊a⌋₊ ⊆ Finset.Ioc 0 ⌊b⌋₊ :=
    Finset.Ioc_subset_Ioc le_rfl (Nat.floor_mono hab)
  have ht :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun m _ _ ↦
        div_nonneg
          (mul_nonneg (mul_nonneg hc (Real.log_natCast_nonneg m))
            (ArithmeticFunction.vonMangoldt_nonneg (n := m)))
          (Real.rpow_nonneg (Nat.cast_nonneg m) τ))
  rw [he] at hp
  simp only [pairedEulerPrefixWeight, Finset.sum_add_distrib]
  linarith only [hp, ht]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
