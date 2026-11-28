/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197PowerBounds
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197PowerBounds
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Power340
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPowerNumerics656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPowerGain663

/-! # A retained power comparison below radius 426 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private def powersAbove426 : Finset ℕ :=
  (fixedPowers663.erase (337 ^ 2)).filter (fun n ↦ 426 ^ 2 ≤ n)

private def rowsAbove426 : Finset PowerRow656 :=
  powers340.toFinset.filter (fun a ↦ 426 ^ 2 ≤ a.p ^ a.k)

private theorem rows_above426_image : rowsAbove426.image (fun a ↦ a.p ^ a.k) = powersAbove426 := by
  decide +kernel

private theorem rows_above426_credit : (∑ a ∈ rowsAbove426, a.credit) = 71314429 := by
  decide +kernel

private theorem power_gain_above426_at340 :
    (0.07131 : ℝ) ≤
      ∑ n ∈ powersAbove426,
        4 * (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) ((340 : ℝ) ^ 2) n).re := by
  have hL :=
    (Analysis.rationalLogIntervalCheck_sound (N := 340) (j := 8) (n := 27) (lo :=
        5828945614 / 1000000000) (hi := 5828945626 / 1000000000) (by decide +kernel)).1
  simp only [Rat.cast_ofNat] at hL
  have hmem (a : PowerRow656) (ha : a ∈ rowsAbove426) := (Finset.mem_filter.mp ha).1
  have h :=
    Finset.sum_le_sum (s := rowsAbove426)
      (fun a ha ↦
        PowerRow656.sound a (by norm_num only : (0 : ℝ) < (340 : ℕ)) hL
          (powers340_valid a (List.mem_toFinset.mp (hmem a ha))))
  rw [← Finset.sum_div, ← Nat.cast_sum, rows_above426_credit, Nat.cast_ofNat] at h
  have hinj := Finset.injOn_of_card_image_eq powers340_card
  rw [← rows_above426_image,
    Finset.sum_image (fun _ ha _ hb hab ↦ hinj (hmem _ ha) (hmem _ hb) hab)]
  exact (by norm_num only : (0.07131 : ℝ) ≤ 71314429 / 1000000000).trans h

private theorem power_above_cutoff {r : ℝ} (hr : r ∈ Set.Ico 340 426) {n : ℕ}
    (hn : n ∈ powersAbove426) : r ^ 2 < (n : ℝ) := by
  have hN : (426 : ℝ) ^ 2 ≤ n := by exact_mod_cast (Finset.mem_filter.mp hn).2
  have hr₀ : 0 ≤ r := (by norm_num only : (0 : ℝ) ≤ 340).trans hr.1
  exact (pow_lt_pow_left₀ hr.2 hr₀ (by decide : (2 : ℕ) ≠ 0)).trans_le hN

private theorem power_gain_below426 {r : ℝ} (hr : r ∈ Set.Ico 340 426) :
    (0.07131 : ℝ) ≤
      ∑ n ∈ powersAbove426,
        4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n) := by
  refine power_gain_above426_at340.trans (Finset.sum_le_sum fun n hn ↦ ?_)
  have hcut := power_above_cutoff hr hn
  have hlog := retained_log_support (r := 340) (by norm_num only) (Finset.mem_filter.mp hn).1
  have hp := Nat.cast_pos.mp ((sq_nonneg r).trans_lt hcut)
  rw [quarter_summand_656 (by norm_num only) hp hlog, mul_comm (quarterWeight656 _ _)]
  exact
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (weight_radius_mono (by norm_num only) hr.1 hcut.le hlog)
        ArithmeticFunction.vonMangoldt_nonneg)
      (by norm_num only)

/-- For radii from 340 up to but excluding 426, the retained K197 powers
with index at least 426 squared contribute 0.07131 to the comparison. -/
theorem gaussian_comparison_below426 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r t : ℝ}
    (hr : r ∈ Set.Ico 340 426) (hL : Real.log p + Real.log q + Real.log k = 4 * t)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) :
    let x := r ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    let R := (quarterKernel656.transform x⁻¹).re
    let T :=
      (∫ z in Set.Ioi x, gaussianDensity197 z) - (Chebyshev.psi x - x) * gaussianDensity197 x +
        gaussianAbelError197 x
    4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) + 0.07131 +
        (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        (15.0472769 - 4 * T) ≤
      (3 / 4 + gaussianAuxMix197 quarterConductorProfile663) * t + 4 * t * R +
          3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re -
        (quarterMainEuler656 a x + quarterMainEuler656 b x + quarterMainEuler656 c x) := by
  exact
    retained_comparison_of_gain ha hb hc hp hq hk hG
      ((by norm_num only : (336.8 : ℝ) ≤ 340).trans hr.1) powersAbove426
      (fun _ hn ↦ (Finset.mem_filter.mp hn).1) (fun _ hn ↦ power_above_cutoff hr hn) hL ht hpa hpb
      hpc (power_gain_below426 hr)

end PseudoPrime.PrimeTestBounds.MillerRabin
