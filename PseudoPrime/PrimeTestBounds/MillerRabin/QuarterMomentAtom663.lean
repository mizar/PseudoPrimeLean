/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEndpointCert663
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPowerSieve663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPowerGain663

/-! # Rational enclosures for the centered Mangoldt moments -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The minimum and maximum of the four products of the two endpoints of
each interval. This also covers negative odd centered moments. -/
def momentMulBox {α : Type*} [LinearOrder α] [Mul α] (a b : α × α) : α × α :=
  (min (min (a.1 * b.1) (a.1 * b.2)) (min (a.2 * b.1) (a.2 * b.2)),
    max (max (a.1 * b.1) (a.1 * b.2)) (max (a.2 * b.1) (a.2 * b.2)))

/-- Interpret integer endpoints over their common denominator. -/
def momentScaledBox (a : ℤ × ℤ) (d : ℕ) : ℚ × ℚ :=
  ((a.1 : ℚ) / d, (a.2 : ℚ) / d)

/-- The integer corner products over the product denominator reproduce
the rational interval product. All endpoints keep a common denominator. -/
theorem moment_mul_scaled_box (a b : ℤ × ℤ) (d e : ℕ) :
    momentMulBox (momentScaledBox a d) (momentScaledBox b e) =
      momentScaledBox (momentMulBox a b) (d * e) := by
  have hn : (0 : ℚ) ≤ (d : ℚ) * (e : ℚ) := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  simp only [momentMulBox, momentScaledBox, div_mul_div_comm, Nat.cast_mul, Int.cast_mul,
    Int.cast_min, Int.cast_max, min_div_div_right hn, max_div_div_right hn]

private theorem mul_box_sound {x y : ℝ} {a b : ℚ × ℚ} (hx : x ∈ Set.Icc (a.1 : ℝ) (a.2 : ℝ))
    (hy : y ∈ Set.Icc (b.1 : ℝ) (b.2 : ℝ)) :
    x * y ∈ Set.Icc ((momentMulBox a b).1 : ℝ) ((momentMulBox a b).2 : ℝ) := by
  unfold momentMulBox
  simp only [Rat.cast_min, Rat.cast_max, Rat.cast_mul, Set.mem_Icc]
  constructor
  · by_cases hy₀ : 0 ≤ y
    · refine
        (show
              min (min ((a.1 : ℝ) * b.1) ((a.1 : ℝ) * b.2))
                  (min ((a.2 : ℝ) * b.1) ((a.2 : ℝ) * b.2)) ≤
                (a.1 : ℝ) * y
              from ?_).trans
          (mul_le_mul_of_nonneg_right hx.1 hy₀)
      by_cases ha : 0 ≤ (a.1 : ℝ)
      · exact (min_le_left _ _).trans ((min_le_left _ _).trans (mul_le_mul_of_nonneg_left hy.1 ha))
      · exact
          (min_le_left _ _).trans
            ((min_le_right _ _).trans (mul_le_mul_of_nonpos_left hy.2 (le_of_not_ge ha)))
    · refine
        (show
              min (min ((a.1 : ℝ) * b.1) ((a.1 : ℝ) * b.2))
                  (min ((a.2 : ℝ) * b.1) ((a.2 : ℝ) * b.2)) ≤
                (a.2 : ℝ) * y
              from ?_).trans
          (mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hy₀))
      by_cases ha : 0 ≤ (a.2 : ℝ)
      · exact (min_le_right _ _).trans ((min_le_left _ _).trans (mul_le_mul_of_nonneg_left hy.1 ha))
      · exact
          (min_le_right _ _).trans
            ((min_le_right _ _).trans (mul_le_mul_of_nonpos_left hy.2 (le_of_not_ge ha)))
  · by_cases hy₀ : 0 ≤ y
    · refine (mul_le_mul_of_nonneg_right hx.2 hy₀).trans ?_
      by_cases ha : 0 ≤ (a.2 : ℝ)
      · exact
          (mul_le_mul_of_nonneg_left hy.2 ha).trans ((le_max_right _ _).trans (le_max_right _ _))
      · exact
          (mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge ha)).trans
            ((le_max_left _ _).trans (le_max_right _ _))
    · refine (mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hy₀)).trans ?_
      by_cases ha : 0 ≤ (a.1 : ℝ)
      · exact (mul_le_mul_of_nonneg_left hy.2 ha).trans ((le_max_right _ _).trans (le_max_left _ _))
      · exact
          (mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge ha)).trans
            ((le_max_left _ _).trans (le_max_left _ _))

/-- Repeated interval multiplication bounds any natural power. -/
def momentPowBox {α : Type*} [LinearOrder α] [Mul α] [One α] (a : α × α) : ℕ → α × α
  | 0 => (1, 1)
  | k + 1 => momentMulBox (momentPowBox a k) a

/-- Repeated integer products give the same interval as repeated rational
products, with denominator raised to the corresponding natural power. -/
theorem moment_pow_scaled_box (a : ℤ × ℤ) (d j : ℕ) :
    momentPowBox (momentScaledBox a d) j = momentScaledBox (momentPowBox a j) (d ^ j) := by
  induction j with
  | zero => simp only [momentPowBox, pow_zero, momentScaledBox, Int.cast_one, Nat.cast_one, div_one]
  | succ k ih => rw [momentPowBox, ih, moment_mul_scaled_box, pow_succ, momentPowBox]

private theorem pow_box_sound {x : ℝ} {a : ℚ × ℚ} (hx : x ∈ Set.Icc (a.1 : ℝ) (a.2 : ℝ)) (k : ℕ) :
    x ^ k ∈ Set.Icc ((momentPowBox a k).1 : ℝ) ((momentPowBox a k).2 : ℝ) := by
  induction k with
  | zero => simp only [momentPowBox, pow_zero, Rat.cast_one, Set.mem_Icc, le_refl, and_self]
  | succ k ih =>
    rw [momentPowBox, pow_succ]
    exact mul_box_sound ih hx

/-- Given bounds for both logarithms at a prime power, check the positive
power enclosure and bound the resulting centered Mangoldt moment. -/
theorem quarter_moment_from_logs_663 {n p k j : ℕ} (hp : p.Prime) (hk : k ≠ 0) (hn : n = p ^ k)
    (P L V : ℚ × ℚ) (hP : Real.log (p : ℝ) ∈ Set.Icc (P.1 : ℝ) (P.2 : ℝ))
    (hL : Real.log (n : ℝ) ∈ Set.Icc (L.1 : ℝ) (L.2 : ℝ))
    (hV : AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (n : ℚ)⁻¹ V.1 V.2 3 5 = true) :
    let B := momentMulBox (momentMulBox V P) (momentPowBox (12 - L.2, 12 - L.1) j)
    (n : ℝ) ^ (3 / 5 : ℝ) * ArithmeticFunction.vonMangoldt n * (12 - Real.log n) ^ j ∈
      Set.Icc (B.1 : ℝ) (B.2 : ℝ) := by
  intro B
  have hv := AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound hV
  have hn₀ : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  simp only [Rat.cast_inv, Rat.cast_natCast, Real.inv_rpow hn₀, Real.rpow_neg hn₀, inv_inv,
    Nat.cast_ofNat, neg_div] at hv
  have hc : 12 - Real.log n ∈ Set.Icc ((12 - L.2 : ℚ) : ℝ) ((12 - L.1 : ℚ) : ℝ) := by
    simp only [Rat.cast_sub, Rat.cast_ofNat, Set.mem_Icc]
    exact ⟨sub_le_sub_left hL.2 _, sub_le_sub_left hL.1 _⟩
  have hm : ArithmeticFunction.vonMangoldt n = Real.log p := by
    rw [hn, ArithmeticFunction.vonMangoldt_apply_pow hk,
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  rw [hm]
  exact mul_box_sound (mul_box_sound hv hP) (pow_box_sound hc j)

/-- At a prime power, two logarithm checks and a positive-power enclosure
give the exact rational interval for a single centered Mangoldt moment. -/
theorem quarter_moment_atom_663 {n p k j jp jn : ℕ} (hp : p.Prime) (hk : k ≠ 0) (hn : n = p ^ k)
    (P L V : ℚ × ℚ) (hP : Analysis.rationalLogIntervalCheck (p : ℚ) jp 22 P.1 P.2 = true)
    (hL : Analysis.rationalLogIntervalCheck (n : ℚ) jn 22 L.1 L.2 = true)
    (hV : AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (n : ℚ)⁻¹ V.1 V.2 3 5 = true) :
    let B := momentMulBox (momentMulBox V P) (momentPowBox (12 - L.2, 12 - L.1) j)
    (n : ℝ) ^ (3 / 5 : ℝ) * ArithmeticFunction.vonMangoldt n * (12 - Real.log n) ^ j ∈
      Set.Icc (B.1 : ℝ) (B.2 : ℝ) := by
  have hp' := Analysis.rationalLogIntervalCheck_sound hP
  have hn' := Analysis.rationalLogIntervalCheck_sound hL
  simp only [Rat.cast_natCast] at hp' hn'
  exact quarter_moment_from_logs_663 hp hk hn P L V hp' hn' hV

/-- A complete finite list of prime powers in a window and rational enclosures
for its terms bound the difference of the two cumulative moments. -/
theorem quarter_moment_window_box_663 {N B j : ℕ} (hNB : N ≤ B) (S : Finset ℕ)
    (hS : ∀ n, n ∈ S ↔ n ∈ Finset.Ioc N B ∧ IsPrimePow n) (lo hi : ℕ → ℚ)
    (h :
      ∀ n ∈ S,
        (n : ℝ) ^ (3 / 5 : ℝ) * ArithmeticFunction.vonMangoldt n * (12 - Real.log n) ^ j ∈
          Set.Icc (lo n : ℝ) (hi n : ℝ)) :
    quarterMangoldtPrefix663 B j - quarterMangoldtPrefix663 N j ∈
      Set.Icc ((∑ n ∈ S, lo n : ℚ) : ℝ) ((∑ n ∈ S, hi n : ℚ) : ℝ) := by
  let f := fun n : ℕ ↦
    (n : ℝ) ^ (3 / 5 : ℝ) * ArithmeticFunction.vonMangoldt n * (12 - Real.log n) ^ j
  have hsub : S ⊆ Finset.Ioc N B := fun n hn ↦ ((hS n).mp hn).1
  have hzero (n : ℕ) (hn : n ∈ Finset.Ioc N B) (hnS : n ∉ S) : f n = 0 := by
    have hp : ¬IsPrimePow n := fun hp ↦ hnS ((hS n).mpr ⟨hn, hp⟩)
    simp only [f, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hp, mul_zero, zero_mul]
  have hsum := Finset.sum_subset hsub hzero
  have hsplit :
    (∑ n ∈ Finset.Ioc N B, f n) = quarterMangoldtPrefix663 B j - quarterMangoldtPrefix663 N j :=
    mangoldt_moment_window hNB j
  rw [← hsplit, ← hsum]
  simp only [Rat.cast_sum]
  exact ⟨Finset.sum_le_sum fun n hn ↦ (h n hn).1, Finset.sum_le_sum fun n hn ↦ (h n hn).2⟩

/-- Prefix sums of the rounded lower and upper term bounds can be reused
at both ends of every window within the certified prime-power support. -/
theorem quarter_moment_prefix_box_663 {L U N B j : ℕ} (hLN : L ≤ N) (hNB : N ≤ B) (hBU : B ≤ U)
    (S : Finset ℕ) (hS : ∀ n, n ∈ S ↔ n ∈ Finset.Ioc L U ∧ IsPrimePow n) (lo hi : ℕ → ℚ)
    (h :
      ∀ n ∈ S,
        (n : ℝ) ^ (3 / 5 : ℝ) * ArithmeticFunction.vonMangoldt n * (12 - Real.log n) ^ j ∈
          Set.Icc (lo n : ℝ) (hi n : ℝ)) :
    quarterMangoldtPrefix663 B j - quarterMangoldtPrefix663 N j ≤
      (((∑ n ∈ S.filter (fun n ↦ n ≤ B), hi n) - ∑ n ∈ S.filter (fun n ↦ n ≤ N), lo n : ℚ) :
        ℝ) := by
  let T := fun X : ℕ ↦ S.filter (fun n ↦ n ≤ X)
  have hT (X : ℕ) (hLX : L ≤ X) (hXU : X ≤ U) :
    quarterMangoldtPrefix663 X j - quarterMangoldtPrefix663 L j ∈
      Set.Icc ((∑ n ∈ T X, lo n : ℚ) : ℝ) ((∑ n ∈ T X, hi n : ℚ) : ℝ) := by
    refine
      quarter_moment_window_box_663 hLX (T X) ?_ lo hi (fun n hn ↦ h n (Finset.mem_filter.mp hn).1)
    intro n
    simp only [T, Finset.mem_filter, hS, Finset.mem_Ioc]
    exact
      ⟨fun hn ↦ ⟨⟨hn.1.1.1, hn.2⟩, hn.1.2⟩, fun hn ↦ ⟨⟨⟨hn.1.1, hn.1.2.trans hXU⟩, hn.2⟩, hn.1.2⟩⟩
  have h₁ := (hT N hLN (hNB.trans hBU)).1
  have h₂ := (hT B (hLN.trans hNB) hBU).2
  simp only [Rat.cast_sub]
  linarith only [h₁, h₂]

/-- The complete section 137 sieve supplies the support for both prefix
bounds. Once the term enclosures are checked, no separate coverage proof
is needed at the window endpoints. -/
theorem quarter_sieved_prefix_box_663 {N B j : ℕ} (hN : 107584 ≤ N) (hNB : N ≤ B) (hB : B ≤ 1517026)
    (lo hi : ℕ → ℚ)
    (h :
      ∀ n ∈ quarterSievedPowers663 107584 1517026,
        (n : ℝ) ^ (3 / 5 : ℝ) * ArithmeticFunction.vonMangoldt n * (12 - Real.log n) ^ j ∈
          Set.Icc (lo n : ℝ) (hi n : ℝ)) :
    let S := quarterSievedPowers663 107584 1517026
    quarterMangoldtPrefix663 B j - quarterMangoldtPrefix663 N j ≤
      (((∑ n ∈ S.filter (fun n ↦ n ≤ B), hi n) - ∑ n ∈ S.filter (fun n ↦ n ≤ N), lo n : ℚ) :
        ℝ) := by
  exact
    quarter_moment_prefix_box_663 hN hNB hB _ (fun _ ↦ quarter_sieved_power_iff_663 le_rfl) lo hi h

end PseudoPrime.PrimeTestBounds.MillerRabin
