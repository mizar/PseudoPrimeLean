/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.AGP.RoundedPolynomialHeight

/-! # Unconditional narrow-modulus theta supply -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

open Classical in
/-- Fixed natural constants supply the original narrow-modulus theta estimate at every
sufficiently large integer scale. The exceptional set is chosen before the modulus, has
uniformly bounded cardinality, and contains only numbers greater than one not dividing four.
Choose a rounded polynomial-root height, apply unconditional polynomial theta supply, and
absorb rounding by the cubic time scale. No unproved analytic input remains. -/
theorem exists_unconditional_narrow_theta_supply :
    ∃ J D Xtheta : ℕ,
      2 ≤ J ∧
        ∀ Z : ℕ,
          Xtheta ≤ Z →
            ∃ E : Finset ℕ,
              E.card ≤ D ∧
                (∀ e ∈ E, 1 < e ∧ ¬e ∣ 4) ∧
                ∀ m d a : ℕ,
                  (m = 1 ∨ m = 4) →
                    0 < d →
                    Nat.Coprime d m →
                    1 < d * m →
                    (d * m) ^ J ≤ Z →
                    Nat.Coprime a (d * m) →
                    (∀ e ∈ E, ¬e ∣ d * m) →
                    (((d * Z ^ 3 : ℕ) : ℝ) / (2 * (Nat.totient (d * m) : ℝ))) ≤
                      thetaInProgressionReal ((d * Z ^ 3 : ℕ) : ℝ) (d * m) a := by
  obtain ⟨b, hb, R₀, X, hR₀, hX, htheta⟩ := exists_uniform_polynomial_theta_supply
  obtain ⟨A, C, hA, hC, hexcept⟩ :=
    DirichletLFunction.LogFreeDensity.exists_bounded_exceptionalFamilyConductorsAwayFromFour
  obtain ⟨D, hD⟩ := hexcept 1 (by norm_num only)
  let n := 4 * b
  have hn : 0 < n := Nat.mul_pos (by norm_num only) (Nat.zero_lt_of_lt hb)
  let W := max R₀ (max 4 (Real.exp 2))
  have hW4 : 4 ≤ W := (le_max_left _ _).trans (le_max_right _ _)
  have hWpos : 0 < W := by linarith only [hW4]
  obtain ⟨Xtheta, hthreshold⟩ := exists_nat_ge (max X (max ((2 : ℝ) ^ (2 * n)) (W ^ n)))
  refine ⟨2 * n, D, Xtheta, ?_, ?_⟩
  · have hn1 : 1 ≤ n := hn
    simpa only [mul_one] using Nat.mul_le_mul_left 2 hn1
  intro Z hZ
  have hZthreshold : max X (max ((2 : ℝ) ^ (2 * n)) (W ^ n)) ≤ (Z : ℝ) :=
    hthreshold.trans (Nat.cast_le.mpr hZ)
  have hZX : X ≤ (Z : ℝ) := (le_max_left _ _).trans hZthreshold
  have hZtwo : (2 : ℝ) ^ (2 * n) ≤ (Z : ℝ) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hZthreshold
  have hZW : W ^ n ≤ (Z : ℝ) := ((le_max_right _ _).trans (le_max_right _ _)).trans hZthreshold
  have hZone : (1 : ℝ) ≤ Z := by linarith only [hX.trans hZX]
  have hWroot :=
    Real.rpow_le_rpow (pow_nonneg hWpos.le n) hZW (one_div_pos.mpr (Nat.cast_pos.mpr hn)).le
  rw [(rpow_nat_root_cancel hWpos.le hn).2] at hWroot
  let R := ⌈(Z : ℝ) ^ (1 / (n : ℝ))⌉₊
  have hWR : W ≤ (R : ℝ) := hWroot.trans (Nat.le_ceil _)
  have hR4 : 4 ≤ R := by exact_mod_cast hW4.trans hWR
  have hR2 : 2 ≤ R := (by norm_num only : 2 ≤ (4 : ℕ)).trans hR4
  have hlog : (2 : ℝ) ≤ Real.log R := by
    have he : Real.exp 2 ≤ (R : ℝ) :=
      ((le_max_right 4 (Real.exp 2)).trans (le_max_right R₀ (max 4 (Real.exp 2)))).trans hWR
    have hl := Real.log_le_log (Real.exp_pos 2) he
    simpa only [Real.log_exp] using hl
  refine
    ⟨DirichletLFunction.LogFreeDensity.exceptionalFamilyConductorsAwayFromFour R
        (1 - 1 / Real.log R),
      (hD R hR2 (by simpa only [mul_one] using hlog)).1,
      (hD R hR2 (by simpa only [mul_one] using hlog)).2, ?_⟩
  intro m d a _hm hd _hcop hq hqpow ha havoid
  let q := d * m
  have hqpos : 0 < q := (by norm_num only : 0 < (1 : ℕ)).trans hq
  let : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
  have hqrpow : (q : ℝ) ^ (2 * n) ≤ (Z : ℝ) := by exact_mod_cast hqpow
  have hrounded := rounded_polynomial_height_bounds hZone hn
  have hqsq : (q : ℝ) ^ 2 ≤ (R : ℝ) := hrounded.2 q hqrpow
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
  have hqR : q ≤ R := by
    have hm := mul_nonneg (Nat.cast_nonneg q) (sub_nonneg.mpr hqone)
    have hh : (q : ℝ) ≤ R := by nlinarith only [hm, hqsq]
    exact_mod_cast hh
  have hqx : (q : ℝ) ≤ Real.sqrt R := Real.le_sqrt_of_sq_le hqsq
  have hRpower : (R : ℝ) ^ (8 * b) ≤ ((d * Z ^ 3 : ℕ) : ℝ) := by
    have hnEq : 2 * n = 8 * b := by
      dsimp only [n]; ring
    have hmain : (R : ℝ) ^ (2 * n) ≤ (Z : ℝ) ^ 3 := by
      have hm := mul_le_mul_of_nonneg_right hZtwo (sq_nonneg (Z : ℝ))
      calc
        (R : ℝ) ^ (2 * n) ≤ (2 : ℝ) ^ (2 * n) * (Z : ℝ) ^ 2 := hrounded.1
        _ ≤ (Z : ℝ) * (Z : ℝ) ^ 2 := hm
        _ = (Z : ℝ) ^ 3 := by ring
    have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hm := mul_le_mul_of_nonneg_right hdreal (pow_nonneg (Nat.cast_nonneg Z) 3)
    simp only [one_mul] at hm
    rw [hnEq] at hmain
    exact hmain.trans (by simpa only [Nat.cast_mul, Nat.cast_pow] using hm)
  have htime : X ≤ ((d * Z ^ 3 : ℕ) : ℝ) := by
    have hZsq : 1 ≤ (Z : ℝ) ^ 2 := one_le_pow₀ hZone
    have hZcube : (Z : ℝ) ≤ (Z : ℝ) ^ 3 := by
      have hm := mul_le_mul_of_nonneg_left hZsq (Nat.cast_nonneg Z : (0 : ℝ) ≤ Z)
      nlinarith only [hm]
    have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hm := mul_le_mul_of_nonneg_right hdreal (pow_nonneg (Nat.cast_nonneg Z) 3)
    simp only [one_mul] at hm
    exact hZX.trans (hZcube.trans (by simpa only [Nat.cast_mul, Nat.cast_pow] using hm))
  have hH : 3 ≤ R - 1 := Nat.le_sub_of_add_le hR4
  have hReq : R - 1 + 1 = R := Nat.sub_add_cancel ((by norm_num only : 1 ≤ (4 : ℕ)).trans hR4)
  have hRR : R₀ ≤ (R : ℝ) := (le_max_left R₀ (max 4 (Real.exp 2))).trans hWR
  have ht := htheta (R - 1) hH
  rw [hReq] at ht
  exact ht hRR q a ha hqR hqx havoid ((d * Z ^ 3 : ℕ) : ℝ) htime hRpower

end PseudoPrime.AnalyticNumberTheory.AGP
