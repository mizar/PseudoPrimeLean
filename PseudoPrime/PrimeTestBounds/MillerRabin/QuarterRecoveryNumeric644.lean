/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterRecoveryAbel644
import all PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3
import all PseudoPrime.Analysis.LogTaylorBounds

/-! # One endpoint certificate for the section 122 reflected recovery -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem moment_bounds {d t v l u p q : ℝ} (hd : 0 < d) (hl : 0 ≤ l) (hv : v ∈ Set.Icc l u)
    (hp : 0 ≤ p) (ht : t ^ (-d) ∈ Set.Icc p q) :
    t ^ (-d) * Analysis.logPowerTailPoly d 5 v ∈
      Set.Icc (p * Analysis.logPowerTailPoly d 5 l) (q * Analysis.logPowerTailPoly d 5 u) := by
  have hv0 := hl.trans hv.1
  exact
    ⟨mul_le_mul ht.1 (Analysis.log_power_tail_poly_mono hd hl hv.1 5)
        (Analysis.log_power_tail_poly_nonneg hd hl 5) (hp.trans ht.1),
      mul_le_mul ht.2 (Analysis.log_power_tail_poly_mono hd hv0 hv.2 5)
        (Analysis.log_power_tail_poly_nonneg hd hv0 5) (hp.trans (ht.1.trans ht.2))⟩

private theorem boundary_upper {t v u q : ℝ} (hv : 0 ≤ v) (hvu : v ≤ u)
    (ht : t ^ (-(107 / 100) : ℝ) ≤ q) (ht0 : 0 ≤ t) : t ^ (-(107 / 100) : ℝ) * v ^ 5 ≤ q * u ^ 5 :=
  mul_le_mul ht (pow_le_pow_left₀ hv hvu 5) (pow_nonneg hv _) ((Real.rpow_nonneg ht0 _).trans ht)

private theorem recovery_sum_322 :
    (117190 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 2701 99000,
        ArithmeticFunction.vonMangoldt n *
          quarterReflectedWeight (2687 / 1000 + 2 * Real.log 322) n := by
  have hr :=
    Analysis.rationalLogIntervalCheck_sound (N := 322) (j := 9) (n := 27) (lo :=
      5774551542 / 1000000000) (hi := 5774551549 / 1000000000) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  have hb :=
    Analysis.rationalLogIntervalCheck_sound (N := 2701) (j := 12) (n := 27) (lo :=
      7901377350 / 1000000000) (hi := 7901377357 / 1000000000) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hb
  have hu :=
    Analysis.rationalLogIntervalCheck_sound (N := 99000) (j := 17) (n := 27) (lo :=
      11502875119 / 1000000000) (hi := 11502875140 / 1000000000) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hu
  have hbd :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 2701) (p := 57) (d :=
      100) (lo := 1106702744661 / 100000000000000) (hi := 1106702744662 / 100000000000000)
      (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hbd
  have hud :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 99000) (p := 57) (d :=
      100) (lo := 142065275894 / 100000000000000) (hi := 142065275895 / 100000000000000)
      (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hud
  have hba :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 2701) (p := 107) (d :=
      100) (lo := 21294561179 / 100000000000000) (hi := 21294561180 / 100000000000000)
      (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hba
  have hua :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 99000) (p := 107) (d :=
      100) (lo := 451513085 / 100000000000000) (hi := 451513086 / 100000000000000)
      (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hua
  let z : ℝ := 2687 / 1000 + 2 * Real.log 322
  have hvb : z + Real.log 2701 ∈ Set.Icc (22137480434 / 1000000000) (22137480455 / 1000000000) :=
    ⟨by
      dsimp only [z]; linarith only [hr.1, hb.1], by
      dsimp only [z]; linarith only [hr.2, hb.2]⟩
  have hvu : z + Real.log 99000 ∈ Set.Icc (25738978203 / 1000000000) (25738978238 / 1000000000) :=
    ⟨by
      dsimp only [z]; linarith only [hr.1, hu.1], by
      dsimp only [z]; linarith only [hr.2, hu.2]⟩
  have hbd' := moment_bounds (by norm_num only) (by norm_num only) hvb (by norm_num only) hbd
  have hud' := moment_bounds (by norm_num only) (by norm_num only) hvu (by norm_num only) hud
  have hba' := moment_bounds (by norm_num only) (by norm_num only) hvb (by norm_num only) hba
  have hua' := moment_bounds (by norm_num only) (by norm_num only) hvu (by norm_num only) hua
  have hb' :=
    boundary_upper (zero_le_one.trans (by linarith only [hvb.1])) hvb.2 hba.2 (by norm_num only)
  have hu' :=
    boundary_upper (zero_le_one.trans (by linarith only [hvu.1])) hvu.2 hua.2 (by norm_num only)
  have hz : 0 ≤ z := by
    dsimp only [z]
    linarith only [hr.1]
  have h := quarter_recovery_moments_644 hz
  dsimp only at h
  have h₁ := hbd'.1
  have h₂ := hud'.2
  have h₃ := hba'.2
  have h₄ := hua'.1
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
    Nat.reduceAdd] at h h₁ h₂ h₃ h₄ hb' hu'
  change
    (117190 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 2701 99000, ArithmeticFunction.vonMangoldt n * quarterReflectedWeight z n
  linarith only [h, h₁, h₂, h₃, h₄, hb', hu']

/-- A single endpoint certificate gives a reflected recovery of at least
0.0013281 on the full four-row section 122 radius interval. -/
theorem quarter_recovery_lower_644 {r : ℝ} (hr : r ∈ Set.Icc 316 322) :
    (0.0013281 : ℝ) ≤ quarterRecovery644 r := by
  apply le_trans _ (quarter_recovery_of_sum_644 hr recovery_sum_322)
  have he :=
    Analysis.exp_le_taylor_add_two_next (x := (287509 / 100000 : ℝ)) (n := 24) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at he
  have hl := one_div_le_one_div_of_le (Real.exp_pos _) he
  rw [one_div (Real.exp _), ← Real.exp_neg] at hl
  have hExp : (5641106227 / 100000000000 : ℝ) ≤ Real.exp (-(107 / 100) * (2687 / 1000)) := by
    rw [show -(107 / 100 : ℝ) * (2687 / 1000) = -(287509 / 100000) by norm_num only]
    linarith only [hl]
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 322) (p := 107) (d :=
        50) (lo := 4297228373 / 1000000000000000) (hi := 4297228374 / 1000000000000000)
        (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hp
  calc
    _ ≤
        (4 * (107 / 100 : ℝ) ^ 5 * (5641106227 / 100000000000) / 120) *
          (4297228373 / 1000000000000000) *
          117190 :=
      by norm_num only
    _ ≤ _ := by gcongr

/-- For three characters satisfying the trace bound and the prime-passing
hypothesis, the finite reflected tail pays the unsigned cost minus the
certified section 122 recovery, uniformly on all four rows. -/
theorem quarter_reflected_saving_644 {p q s N : ℕ} (hN : 99000 ≤ N) {r : ℝ}
    (hr : r ∈ Set.Icc 316 322) (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ s) (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    let C := (107 / 100 : ℝ) ^ 5 * Real.exp (-(107 / 100) * (2687 / 1000)) / 120
    let W := fun m : ℕ ↦
      (ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-(157 / 100) : ℝ)) *
        quarterRecoveryFactor (2687 / 1000 + Real.log m) r
    C * (∑ m ∈ Finset.Ioc 2701 N, -((a m).re + (b m).re + (c m).re) * W m) ≤
      C * (∑ m ∈ Finset.Ioc 2701 N, W m) - 0.0013281 := by
  intro C W
  have h :=
    quarter_reflected_recovery_644 hr hN (fun m ↦ (a m).re + (b m).re + (c m).re) ht
      (fun _ hm hΛ ↦ quarter_recovery_trace_644 hr a b c hA hB hC hm hΛ)
  change _ ≤ C * (∑ m ∈ Finset.Ioc 2701 N, W m) - quarterRecovery644 322 at h
  have h322 : (322 : ℝ) ∈ Set.Icc 316 322 := by norm_num only [Set.mem_Icc, and_self]
  exact h.trans (sub_le_sub_left (quarter_recovery_lower_644 h322) _)

end PseudoPrime.PrimeTestBounds.MillerRabin
