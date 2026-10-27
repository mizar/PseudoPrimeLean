/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.EightDegreeRatioBounds
public import PseudoPrime.NumberTheory.Heilbronn.HeightWeightExchange

/-! # Explicit natural coefficients for the full finite-fiber count -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- The natural count coefficient 4K_c(2a+1), for the explicit eight-degree
coefficient K_c and positive inverse loss 1/a. A precision 1/c≤1/(2a)
leaves half the loss to absorb the harmonic height sum. No rounding is needed. -/
def finiteFiberCountCoefficient (c a : ℕ) : ℕ :=
  4 * eightDegreeFiberCoefficient c * (2 * a + 1)

/-- The explicit count coefficient is positive for all c,a. Combine
positivity of the degree sum with the two positive natural factors. -/
theorem finiteFiberCountCoefficient_pos (c a : ℕ) : 0 < finiteFiberCountCoefficient c a := by
  exact Nat.mul_pos (Nat.mul_pos (by decide) (eightDegreeFiberCoefficient_pos c)) (Nat.succ_pos _)

/-- The natural coefficient agrees exactly with the real harmonic-loss
coefficient. Simplify reciprocals and collect products; the identity also
holds at a=0. This avoids an existential ceiling coefficient. -/
theorem finiteFiberCountCoefficient_cast (c a : ℕ) :
    (finiteFiberCountCoefficient c a : ℝ) =
      4 * (eightDegreeFiberCoefficient c : ℝ) * (1 + 1 / ((1 / (a : ℝ)) / 2)) := by
  rw [one_div_div, div_div_eq_mul_div, div_one]
  simp only [finiteFiberCountCoefficient, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  ring

/-- For positive a,c with 1/c≤(1/a)/2, all admissible full signed counts
are bounded by the explicit natural coefficient times H p^(1/84+1/a).
Use the eight-degree ratio bound, exact height-weight exchange, and half
the exponent loss for the harmonic sum. This fixes all count constants. -/
theorem boundedCongruenceCount_le_explicit_finite_fiber {a c : ℕ} (ha : 0 < a) (hc : 0 < c)
    (hprec : 1 / (c : ℝ) ≤ (1 / (a : ℝ)) / 2) :
    ∀ (p H : ℕ) [Fact p.Prime],
      Odd p →
        H < p →
        (H : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ) →
        (boundedCongruenceCount p H : ℝ) ≤
          finiteFiberCountCoefficient c a * H * (p : ℝ) ^ (1 / 84 + 1 / (a : ℝ)) := by
  let eta : ℝ := 1 / (a : ℝ)
  have heta : 0 < eta := div_pos (by norm_num only) (Nat.cast_pos.mpr ha)
  have hdelta : 0 < eta / 2 := half_pos heta
  let K : ℝ := eightDegreeFiberCoefficient c
  have hK : 0 < K := Nat.cast_pos.mpr (eightDegreeFiberCoefficient_pos c)
  have hR := heightRestrictedRatioSet_le_explicit_finite_fiber_ratio_bound hc hprec
  let C : ℝ := 4 * K * (1 + 1 / (eta / 2))
  intro p H hp hodd hHp htop
  rw [finiteFiberCountCoefficient_cast]
  change (boundedCongruenceCount p H : ℝ) ≤ C * H * (p : ℝ) ^ (1 / 84 + eta)
  have hp1 : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (Fact.out : p.Prime).pos
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hcount :=
    boundedCongruenceCount_le_of_uniform_height_ratios hodd hHp hK.le
      (fun T hT ↦ hR p H T hHp ((Nat.cast_le.mpr hT).trans htop))
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg H) (Nat.cast_le.mpr hHp.le) hdelta.le
  have hlog :=
    (Real.log_natCast_le_rpow_div H hdelta).trans (div_le_div_of_nonneg_right hpow hdelta.le)
  have hone : (1 : ℝ) ≤ (p : ℝ) ^ (eta / 2) := by
    have h := Real.rpow_le_rpow_of_exponent_le hp1 hdelta.le
    simpa only [Real.rpow_zero] using h
  have hlog' : 1 + Real.log H ≤ (1 + 1 / (eta / 2)) * (p : ℝ) ^ (eta / 2) := by
    have hh := add_le_add hone hlog
    convert hh using 1
    ring
  have hm :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlog'
        (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hK.le) (Nat.cast_nonneg H)))
      (Real.rpow_nonneg hp0.le (1 / 84 + eta / 2))
  apply hcount.trans
  convert hm using 1
  dsimp only [C]
  rw [show (1 / 84 + eta : ℝ) = eta / 2 + (1 / 84 + eta / 2) by ring, Real.rpow_add hp0]
  ring

end PseudoPrime.NumberTheory.Heilbronn
