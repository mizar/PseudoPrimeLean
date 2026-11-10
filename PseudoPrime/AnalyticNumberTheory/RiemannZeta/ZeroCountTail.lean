/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTailFinite
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountInverseSquare
import PseudoPrime.Analysis.FiniteHeightAbel

/-! # Finite height tails and inverse-cube integration -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For positive ordered endpoints, integrate the inverse-cube kernel used in
the partial-summation formula for inverse-square zero weights. -/
theorem inv_cube_integral {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b, 2 * t⁻¹ ^ 3) = a⁻¹ ^ 2 - b⁻¹ ^ 2 := by
  have hi : IntervalIntegrable (fun t : ℝ ↦ 2 * t⁻¹ ^ 3) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    exact
      (continuousAt_const.mul
          ((continuousAt_id.inv₀ (ne_of_gt (lt_of_lt_of_le (zero_lt_one.trans ha) ht.1))).pow
            3)) |>.continuousWithinAt
  have hd : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun x : ℝ ↦ -(x⁻¹ ^ 2)) (2 * t⁻¹ ^ 3) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le (zero_lt_one.trans ha) ht.1)
    have h := ((hasDerivAt_inv ht0).pow 2).neg
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, ← inv_pow] at h
    convert h using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  ring

/-- Integrate the inverse-cube kernel above an interior height cutoff. -/
theorem inv_cube_cutoff_high {a b γ : ℝ} (ha : 1 < a) (haγ : a < γ) (hγb : γ ≤ b) :
    (∫ t in a..b, if γ ≤ t then 2 * t⁻¹ ^ 3 else 0) = γ⁻¹ ^ 2 - b⁻¹ ^ 2 := by
  have hs : Set.Ici γ ∩ Set.Ioc a b = Set.Icc γ b := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc, Set.mem_Icc]
    constructor
    · intro h
      exact ⟨h.1, h.2.2⟩
    · intro h
      exact ⟨h.1, lt_of_lt_of_le haγ h.1, h.2⟩
  change (∫ t in a..b, (Set.Ici γ).indicator (fun t : ℝ ↦ 2 * t⁻¹ ^ 3) t) = _
  rw [intervalIntegral.integral_of_le (haγ.le.trans hγb),
    MeasureTheory.integral_indicator measurableSet_Ici,
    MeasureTheory.Measure.restrict_restrict measurableSet_Ici, hs,
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hγb,
    inv_cube_integral (lt_trans ha haγ) hγb]

/-- A cutoff below the lower endpoint leaves the inverse-cube integral unchanged. -/
theorem inv_cube_cutoff_low {a b γ : ℝ} (ha : 1 < a) (hab : a ≤ b) (hγa : γ ≤ a) :
    (∫ t in a..b, if γ ≤ t then 2 * t⁻¹ ^ 3 else 0) = a⁻¹ ^ 2 - b⁻¹ ^ 2 := by
  rw [← inv_cube_integral ha hab]
  apply intervalIntegral.integral_congr
  rw [Set.uIcc_of_le hab]
  intro t ht
  simp only [hγa.trans ht.1, ↓reduceIte]

/-- For nonnegative ordered heights, the inverse-square sum over `(a, b]`
equals the difference of the two closed-height sums. This retains the
multiplicity and includes zeros at the upper endpoint only. -/
theorem finite_tail_eq_sub {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∑ ρ ∈ (zerosUpTo b).filter (fun ρ ↦ a < |ρ.im|),
        (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) =
      (∑ ρ ∈ zerosUpTo b, (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) -
        (∑ ρ ∈ zerosUpTo a, (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) := by
  classical
  have hs : (zerosUpTo b).filter (fun ρ ↦ |ρ.im| ≤ a) = zerosUpTo a := by
    ext ρ
    rw [Finset.mem_filter, mem_zerosUpTo (ha.trans hab), mem_zerosUpTo ha]
    constructor
    · rintro ⟨⟨hz, hre, htop⟩, hcut⟩
      exact ⟨hz, hre, hcut⟩
    · rintro ⟨hz, hre, hcut⟩
      exact ⟨⟨hz, hre, hcut.trans hab⟩, hcut⟩
  rw [← hs, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  by_cases h : |ρ.im| ≤ a
  · simp only [h, not_lt_of_ge h, ↓reduceIte, sub_self]
  · have ht : a < |ρ.im| := lt_of_not_ge h
    simp only [h, ht, ↓reduceIte, sub_zero]

/-- For ordered heights above one, integrate the zero count against the inverse-cube
kernel. Integrating each cutoff separately gives the finite height-ledger sum. -/
theorem zeroCount_invCube_integral {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b, zeroCount t * (2 * t⁻¹ ^ 3)) =
      ∑ ρ ∈ zerosUpTo b,
        (riemannZetaZeroMultiplicity ρ : ℝ) * ((max a |ρ.im|)⁻¹ ^ 2 - b⁻¹ ^ 2) := by
  classical
  let S := zerosUpTo b
  have hc : ContinuousOn (fun t : ℝ ↦ (2 * t⁻¹ ^ 3)) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    exact
      (continuousAt_const.mul
          ((continuousAt_id.inv₀ (ne_of_gt (lt_of_lt_of_le (zero_lt_one.trans ha) ht.1))).pow
            3)) |>.continuousWithinAt
  have hI :
    ∀ ρ ∈ S,
      IntervalIntegrable
        (fun t : ℝ ↦ if |ρ.im| ≤ t then (riemannZetaZeroMultiplicity ρ : ℝ) * (2 * t⁻¹ ^ 3) else 0)
        MeasureTheory.volume a b := by
    intro ρ hρ
    have h :=
      (Analysis.FiniteHeightAbel.intervalIntegrable_cutoff (riemannZetaZeroMultiplicity ρ : ℝ)
            |ρ.im| a b).mul_continuousOn
        hc
    convert h using 1
    funext t
    by_cases hh : |ρ.im| ≤ t
    · simp only [hh, ↓reduceIte]
    · simp only [hh, ↓reduceIte, zero_mul]
  have heq :
    (∫ t in a..b, zeroCount t * (2 * t⁻¹ ^ 3)) =
      ∫ t in a..b,
        ∑ ρ ∈ S, if |ρ.im| ≤ t then (riemannZetaZeroMultiplicity ρ : ℝ) * (2 * t⁻¹ ^ 3) else 0 := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hab]
    intro t ht
    dsimp only
    rw [zeroCount_eq_sum]
    have hs : (S.filter (fun ρ ↦ |ρ.im| ≤ t)) = zerosUpTo t := by
      ext ρ
      rw [Finset.mem_filter, mem_zerosUpTo (le_trans (zero_lt_one.trans ha).le hab),
        mem_zerosUpTo (le_trans (zero_lt_one.trans ha).le ht.1)]
      constructor
      · rintro ⟨⟨hz, hre, htop⟩, hcut⟩
        exact ⟨hz, hre, hcut⟩
      · rintro ⟨hz, hre, hcut⟩
        exact ⟨⟨hz, hre, hcut.trans ht.2⟩, hcut⟩
    rw [← hs, Finset.sum_filter, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ρ hρ
    by_cases hh : |ρ.im| ≤ t
    · simp only [hh, ↓reduceIte]
    · simp only [hh, ↓reduceIte, zero_mul]
  rw [heq, intervalIntegral.integral_finsetSum hI]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hγb := ((mem_zerosUpTo ((zero_lt_one.trans ha).le.trans hab)).1 hρ).2.2
  have hmul :
    (∫ t in a..b, if |ρ.im| ≤ t then (riemannZetaZeroMultiplicity ρ : ℝ) * (2 * t⁻¹ ^ 3) else 0) =
      (riemannZetaZeroMultiplicity ρ : ℝ) *
        ∫ t in a..b, if |ρ.im| ≤ t then (2 * t⁻¹ ^ 3) else 0 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    by_cases hh : |ρ.im| ≤ t
    · simp only [hh, ↓reduceIte]
    · simp only [hh, ↓reduceIte, mul_zero]
  rw [hmul]
  by_cases hh : |ρ.im| ≤ a
  · rw [max_eq_left hh, inv_cube_cutoff_low ha hab hh]
  · have hh' := lt_of_not_ge hh
    rw [max_eq_right hh'.le, inv_cube_cutoff_high ha hh' hγb]

/-- For `1 < a ≤ b`, the finite inverse-square ordinate tail equals the
endpoint count terms plus the inverse-cube integral of the zero count. The
closed height ledgers retain zeros at `b` and exclude those at `a`. -/
theorem finite_tail_abel {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∑ ρ ∈ (zerosUpTo b).filter (fun ρ ↦ a < |ρ.im|),
        (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) =
      zeroCount b / b ^ 2 - zeroCount a / a ^ 2 + ∫ t in a..b, zeroCount t * (2 * t⁻¹ ^ 3) := by
  classical
  let S := zerosUpTo b
  have hs : S.filter (fun ρ ↦ |ρ.im| ≤ a) = zerosUpTo a := by
    ext ρ
    rw [Finset.mem_filter, mem_zerosUpTo ((zero_lt_one.trans ha).le.trans hab),
      mem_zerosUpTo (zero_lt_one.trans ha).le]
    constructor
    · rintro ⟨⟨hz, hre, htop⟩, hcut⟩
      exact ⟨hz, hre, hcut⟩
    · rintro ⟨hz, hre, hcut⟩
      exact ⟨⟨hz, hre, hcut.trans hab⟩, hcut⟩
  rw [finite_tail_eq_sub (zero_lt_one.trans ha).le hab, zeroCount_invCube_integral ha hab,
    zeroCount_eq_sum, zeroCount_eq_sum, ← hs, Finset.sum_div, Finset.sum_div, Finset.sum_filter,
    Finset.sum_filter]
  have heq :
    ∀ ρ ∈ S,
      (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2 -
          (if |ρ.im| ≤ a then (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2 else 0) =
        (riemannZetaZeroMultiplicity ρ : ℝ) / b ^ 2 -
            (if |ρ.im| ≤ a then (riemannZetaZeroMultiplicity ρ : ℝ) / a ^ 2 else 0) +
          (riemannZetaZeroMultiplicity ρ : ℝ) * ((max a |ρ.im|)⁻¹ ^ 2 - b⁻¹ ^ 2) := by
    intro ρ hρ
    by_cases h : |ρ.im| ≤ a
    · simp only [h, ↓reduceIte, max_eq_left h, div_eq_mul_inv, inv_pow]
      ring
    · have hh := (lt_of_not_ge h).le
      simp only [h, ↓reduceIte, max_eq_right hh, div_eq_mul_inv, inv_pow]
      ring
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl heq

/-- Under RH, the finite Abel expressions converge to the full inverse-square
ordinate tail. Apply the finite identity at all sufficiently large heights. -/
theorem ordinateTail_abel_limit (hRH : RiemannHypothesis) {a : ℝ} (ha : 1 < a) :
    Filter.Tendsto
      (fun b : ℝ ↦
        zeroCount b / b ^ 2 - zeroCount a / a ^ 2 + ∫ t in a..b, zeroCount t * (2 * t⁻¹ ^ 3))
      Filter.atTop (nhds (ordinateTail a)) := by
  apply (ordinateTail_limit hRH a).congr'
  filter_upwards [Filter.eventually_ge_atTop a] with b hb
  exact finite_tail_abel ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
