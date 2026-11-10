/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.MomentEnvelopeIntegral

/-! # Boundary-free explicit Mangoldt moment tails -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For nonzero decay `r`, the logarithmic tail polynomial recurrence
eliminates the boundary monomial from its Abel main term. The case `k = 0`
is included separately because natural subtraction truncates at zero. -/
theorem moment_main_poly_identity (r z : ℝ) (hr : r ≠ 0) (k : ℕ) :
    (r + 1) * Analysis.logPowerTailPoly r k z - (k : ℝ) * Analysis.logPowerTailPoly r (k - 1) z -
        z ^ k =
      Analysis.logPowerTailPoly r k z := by
  cases k with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, sub_zero, pow_zero, Analysis.logPowerTailPoly]
    field_simp
    ring
  | succ k =>
    simp only [Nat.succ_sub_one, Analysis.logPowerTailPoly]
    field_simp
    ring

/-- For positive `a` and `σ > 1`, the actual main integral and the boundary
monomial combine into the elementary logarithmic tail polynomial. Apply the
polynomial recurrence and the real-power multiplication rule. -/
theorem moment_main_boundary_eq {σ a : ℝ} (ha : 0 < a) (hσ : 1 < σ) (k : ℕ) :
    -Arithmetic.mangoldtMomentWeight σ k a * a -
        (-σ * (a ^ (-(σ - 1)) * Analysis.logPowerTailPoly (σ - 1) k (Real.log a)) +
          (k : ℝ) * (a ^ (-(σ - 1)) * Analysis.logPowerTailPoly (σ - 1) (k - 1) (Real.log a))) =
      a ^ (-(σ - 1)) * Analysis.logPowerTailPoly (σ - 1) k (Real.log a) := by
  have hr : σ - 1 ≠ 0 := ne_of_gt (by linarith only [hσ])
  have hi := moment_main_poly_identity (σ - 1) (Real.log a) hr k
  have hp : a ^ (-σ) * a = a ^ (-(σ - 1)) := by
    have h := Real.rpow_add ha (-σ) 1
    rw [Real.rpow_one] at h
    convert h.symm using 1
    congr 1
    ring
  dsimp only [Arithmetic.mangoldtMomentWeight]
  have hm := congrArg (fun z : ℝ ↦ a ^ (-(σ - 1)) * z) hi
  have hpp := congrArg (fun z : ℝ ↦ z * Real.log a ^ k) hp
  nlinarith only [hm, hpp]

/-- Under RH and the stated Rosser-type count estimate, a decreasing
power-logarithm Mangoldt tail above logarithmic scale 43 has explicit bounds
without a `ψ(a)` boundary value. The same Chebyshev error envelope bounds the
boundary, while finite tail polynomials evaluate the improper integrals. -/
theorem mangoldt_tail_boundary_free (hRH : RiemannHypothesis) {σ a : ℝ} (k : ℕ) (ha : 0 < a)
    (hL : 43 ≤ Real.log a) (hσ : 1 < σ) (hk : (k : ℝ) ≤ σ * Real.log a)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t)) :
    let M :=
      -σ * (a ^ (-(σ - 1)) * Analysis.logPowerTailPoly (σ - 1) k (Real.log a)) +
        (k : ℝ) * (a ^ (-(σ - 1)) * Analysis.logPowerTailPoly (σ - 1) (k - 1) (Real.log a))
    let R :=
      -σ * (a ^ (-(σ - 1 / 2)) * Analysis.logPowerTailPoly (σ - 1 / 2) (k + 2) (Real.log a)) +
        (k : ℝ) * (a ^ (-(σ - 1 / 2)) * Analysis.logPowerTailPoly (σ - 1 / 2) (k + 1) (Real.log a))
    let W := Arithmetic.mangoldtMomentWeight σ k a
    let B := Real.sqrt a * (Real.log a * (Real.log a - Real.log (Real.log a)) / (8 * Real.pi))
    let S :=
      (∑' m : ℕ, Arithmetic.mangoldtMomentWeight σ k m * ArithmeticFunction.vonMangoldt m) -
        (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊,
          Arithmetic.mangoldtMomentWeight σ k m * ArithmeticFunction.vonMangoldt m)
    (-W * (a + B) - M + R / (8 * Real.pi) ≤ S) ∧ (S ≤ -W * (a - B) - M - R / (8 * Real.pi)) := by
  dsimp only
  have ha1 : 1 ≤ a := (Real.log_pos_iff ha.le).mp (by linarith only [hL]) |>.le
  have hw : 0 ≤ Arithmetic.mangoldtMomentWeight σ k a := by
    dsimp only [Arithmetic.mangoldtMomentWeight]
    exact mul_nonneg (Real.rpow_nonneg ha.le _) (pow_nonneg (Real.log_nonneg ha1) k)
  have hp := (abs_le.mp (chebyshev_errors_43 hRH ha hL hQ).1)
  have hlo := mul_le_mul_of_nonneg_left hp.1 hw
  have hhi := mul_le_mul_of_nonneg_left hp.2 hw
  have hb := mangoldt_tail_explicit_43 hRH k ha hL hσ hk hQ
  dsimp only at hb
  constructor
  · nlinarith only [hb.1, hhi]
  · nlinarith only [hb.2, hlo]

/-- Under RH and the stated Rosser-type count estimate, the infinite
Mangoldt moment tail lies between its elementary main tail polynomial plus
and minus explicit Chebyshev boundary and integral errors. The weight must
decrease above a cutoff with logarithm at least 43. -/
theorem mangoldt_tail_main_error (hRH : RiemannHypothesis) {σ a : ℝ} (k : ℕ) (ha : 0 < a)
    (hL : 43 ≤ Real.log a) (hσ : 1 < σ) (hk : (k : ℝ) ≤ σ * Real.log a)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t)) :
    let P := a ^ (-(σ - 1)) * Analysis.logPowerTailPoly (σ - 1) k (Real.log a)
    let R :=
      -σ * (a ^ (-(σ - 1 / 2)) * Analysis.logPowerTailPoly (σ - 1 / 2) (k + 2) (Real.log a)) +
        (k : ℝ) * (a ^ (-(σ - 1 / 2)) * Analysis.logPowerTailPoly (σ - 1 / 2) (k + 1) (Real.log a))
    let W := Arithmetic.mangoldtMomentWeight σ k a
    let B := Real.sqrt a * (Real.log a * (Real.log a - Real.log (Real.log a)) / (8 * Real.pi))
    let S :=
      (∑' m : ℕ, Arithmetic.mangoldtMomentWeight σ k m * ArithmeticFunction.vonMangoldt m) -
        (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊,
          Arithmetic.mangoldtMomentWeight σ k m * ArithmeticFunction.vonMangoldt m)
    (P - W * B + R / (8 * Real.pi) ≤ S) ∧ (S ≤ P + W * B - R / (8 * Real.pi)) := by
  dsimp only
  have hb := mangoldt_tail_boundary_free hRH k ha hL hσ hk hQ
  dsimp only at hb
  have hi := moment_main_boundary_eq ha hσ k
  constructor
  · nlinarith only [hb.1, hi]
  · nlinarith only [hb.2, hi]

/-- Under RH and the stated Rosser-type count estimate, the absolute
difference between a decreasing Mangoldt moment tail and its elementary main
tail polynomial is bounded by the explicit boundary and integral errors.
The cutoff must have logarithm at least 43. -/
theorem mangoldt_tail_abs_error (hRH : RiemannHypothesis) {σ a : ℝ} (k : ℕ) (ha : 0 < a)
    (hL : 43 ≤ Real.log a) (hσ : 1 < σ) (hk : (k : ℝ) ≤ σ * Real.log a)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t)) :
    let P := a ^ (-(σ - 1)) * Analysis.logPowerTailPoly (σ - 1) k (Real.log a)
    let R :=
      -σ * (a ^ (-(σ - 1 / 2)) * Analysis.logPowerTailPoly (σ - 1 / 2) (k + 2) (Real.log a)) +
        (k : ℝ) * (a ^ (-(σ - 1 / 2)) * Analysis.logPowerTailPoly (σ - 1 / 2) (k + 1) (Real.log a))
    let W := Arithmetic.mangoldtMomentWeight σ k a
    let B := Real.sqrt a * (Real.log a * (Real.log a - Real.log (Real.log a)) / (8 * Real.pi))
    let S :=
      (∑' m : ℕ, Arithmetic.mangoldtMomentWeight σ k m * ArithmeticFunction.vonMangoldt m) -
        (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊,
          Arithmetic.mangoldtMomentWeight σ k m * ArithmeticFunction.vonMangoldt m)
    |S - P| ≤ W * B - R / (8 * Real.pi) := by
  dsimp only
  have h := mangoldt_tail_main_error hRH k ha hL hσ hk hQ
  dsimp only at h
  apply abs_le.mpr
  constructor
  · linarith only [h.1]
  · linarith only [h.2]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
