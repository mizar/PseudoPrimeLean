/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.AGP.ScalarThetaBudget

/-! # Unconditional theta supply above a polynomial height scale -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

/-- A polynomial time bound of exponent eight times the cutoff exponent puts the cutoff
below the eighth root of time and above the height parameter. -/
theorem polynomial_cutoff_le_eighth_root {R x : ℝ} (hR : 1 ≤ R) {b : ℕ} (hb : 1 ≤ b)
    (hx : R ^ (8 * b) ≤ x) : R ≤ R ^ b ∧ R ^ b ≤ x ^ (1 / 8 : ℝ) := by
  have hp := Real.rpow_le_rpow_of_exponent_le hR (by exact_mod_cast hb : (1 : ℝ) ≤ (b : ℝ))
  rw [Real.rpow_one, Real.rpow_natCast] at hp
  refine ⟨hp, ?_⟩
  have hnonneg : 0 ≤ R := zero_le_one.trans hR
  have hr := Real.rpow_le_rpow (pow_nonneg hnonneg (8 * b)) hx (by norm_num only : (0 : ℝ) ≤ 1 / 8)
  have he : (R ^ (8 * b)) ^ (1 / 8 : ℝ) = R ^ b := by
    rw [← Real.rpow_natCast R (8 * b), ← Real.rpow_natCast R b, ← Real.rpow_mul hnonneg]
    congr 1
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    ring
  exact he ▸ hr

/-- For time at least four, its eighth root is below four fifths of time. Compare with
the square root and use its defining square identity. -/
theorem eighth_root_le_four_fifths {x : ℝ} (hx : 4 ≤ x) : x ^ (1 / 8 : ℝ) ≤ 4 * x / 5 := by
  have hxone : 1 ≤ x := by linarith only [hx]
  have hxp : 0 ≤ x := by linarith only [hx]
  have hp := Real.rpow_le_rpow_of_exponent_le hxone (by norm_num only : (1 / 8 : ℝ) ≤ 1 / 2)
  rw [← Real.sqrt_eq_rpow] at hp
  have hs := Real.sq_sqrt hxp
  have hspos := Real.sqrt_nonneg x
  have hstwo : 2 ≤ Real.sqrt x := by nlinarith only [hs, hspos, hx]
  have hm := mul_nonneg hspos (sub_nonneg.mpr hstwo)
  nlinarith only [hp, hs, hm]

/-- An absolute polynomial exponent and thresholds give unconditional progression theta
supply for levels below the square root of the height and avoiding its exceptional conductors.
All thresholds precede the modulus and residue; no scalar error budget remains as an input.
The proof joins the actual family half-scale estimate with uniform scalar error absorption. -/
theorem exists_uniform_polynomial_theta_supply :
    ∃ b : ℕ,
      1 ≤ b ∧
        ∃ R₀ X : ℝ,
          4 ≤ R₀ ∧
            4 ≤ X ∧
            ∀ H : ℕ,
              3 ≤ H →
                R₀ ≤ ((H + 1 : ℕ) : ℝ) →
                ∀ q a : ℕ,
                  ∀ [NeZero q],
                    Nat.Coprime a q →
                      q ≤ H + 1 →
                      (q : ℝ) ≤ Real.sqrt ((H + 1 : ℕ) : ℝ) →
                      (∀
                        e ∈
                          DirichletLFunction.LogFreeDensity.exceptionalFamilyConductorsAwayFromFour
                            (H + 1) (1 - 1 / Real.log ((H + 1 : ℕ) : ℝ)),
                        ¬e ∣ q) →
                      ∀ x : ℝ,
                        X ≤ x →
                          ((H + 1 : ℕ) : ℝ) ^ (8 * b) ≤ x →
                          x / (2 * (q.totient : ℝ)) ≤ thetaInProgressionReal x q a := by
  have hε : 0 < Real.log (5 / 4) / 512 :=
    div_pos (Real.log_pos (by norm_num only)) (by norm_num only)
  obtain ⟨b, hb, R₀, X₀, hR₀, hX₀, htheta⟩ :=
    exists_uniform_polynomial_half_scale_theta_threshold (Real.log (5 / 4) / 512) hε
  obtain ⟨X₁, hX₁, hbudget⟩ := exists_uniform_scalar_theta_budget_threshold
  refine ⟨b, hb, R₀, max 4 (max X₀ X₁), hR₀, le_max_left _ _, ?_⟩
  intro H hH hR q a inst ha hq hsqrt havoid x hx hpow
  have hx4 : 4 ≤ x := (le_max_left 4 (max X₀ X₁)).trans hx
  have hx₀ : X₀ ≤ x := ((le_max_left X₀ X₁).trans (le_max_right 4 (max X₀ X₁))).trans hx
  have hx₁ : X₁ ≤ x := ((le_max_right X₀ X₁).trans (le_max_right 4 (max X₀ X₁))).trans hx
  have hRone : (1 : ℝ) ≤ ((H + 1 : ℕ) : ℝ) := by linarith only [hR₀.trans hR]
  have hp := polynomial_cutoff_le_eighth_root hRone hb hpow
  have hqsmall : (q : ℝ) ≤ x ^ (1 / 8 : ℝ) := (Nat.cast_le.mpr hq).trans (hp.1.trans hp.2)
  exact
    htheta H hH hR q a ha hq hsqrt havoid x hx₀ (hp.2.trans (eighth_root_le_four_fifths hx4))
      (hbudget q (((H + 1 : ℕ) : ℝ) ^ b) x hx₁ (one_le_pow₀ hRone) hqsmall hp.2)

end PseudoPrime.AnalyticNumberTheory.AGP
