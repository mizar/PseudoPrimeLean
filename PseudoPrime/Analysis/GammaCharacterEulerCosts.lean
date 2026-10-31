/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaPrimePowerCosts
public import PseudoPrime.Analysis.GammaOddPrimePowerCosts

/-! # Character Euler costs for arbitrary finite positive-power prefixes -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Every actual character Euler correction is nonnegative. The character
norm is at most one, so its real part is at most one; the common Mangoldt
weight is nonnegative. This permits enlarging arbitrary finite power prefixes. -/
theorem gamma_character_euler_correction_nonneg {f : ℕ} (χ : DirichletCharacter ℂ f) (n : ℕ) :
    0 ≤ (1 - (χ n).re) * gammaResolventMangoldtWeight n := by
  exact
    mul_nonneg (sub_nonneg.mpr ((Complex.re_le_norm (χ n)).trans (χ.norm_le_one n)))
      (gammaResolventMangoldtWeight_nonneg n)

/-- The odd positive Mangoldt power series of a prime converges and has
sum log p times the signed odd Euler cost. Mangoldt equals log p on each
positive prime power. This supplies the infinite majorant for arbitrary prefixes. -/
theorem gamma_odd_mangoldt_series_eq_cost {p : ℕ} (hp : p.Prime) :
    Summable (fun k : ℕ ↦ gammaResolventMangoldtWeight (p ^ (2 * k + 1))) ∧
      (∑' k : ℕ, gammaResolventMangoldtWeight (p ^ (2 * k + 1))) =
        Real.log p * gammaPrimeOddEulerCost p := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  simp only [gammaResolventMangoldtWeight,
    ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero _),
    ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow]
  constructor
  · exact (summable_gammaResolventEulerWeight_odd_powers hpR).mul_left (Real.log p)
  · rw [tsum_mul_left, tsum_gammaResolventEulerWeight_odd_powers_eq_cost hpR]

/-- When chi(p)=-1, the actual correction over all positive powers converges
and sums to twice log p times the odd Euler cost. Split the index by parity:
odd powers give twice the weight and even powers vanish. This retains the
exact parity cancellation for an arbitrary positive-power Euler prefix. -/
theorem gamma_minus_one_positive_euler_series_eq_cost {f p : ℕ} (χ : DirichletCharacter ℂ f)
    (hp : p.Prime) (hχ : χ p = -1) :
    Summable (fun k : ℕ ↦ (1 - (χ (p ^ (k + 1))).re) * gammaResolventMangoldtWeight (p ^ (k + 1))) ∧
      (∑' k : ℕ, (1 - (χ (p ^ (k + 1))).re) * gammaResolventMangoldtWeight (p ^ (k + 1))) =
        2 * (Real.log p * gammaPrimeOddEulerCost p) := by
  let F : ℕ → ℝ := fun k ↦ (1 - (χ (p ^ (k + 1))).re) * gammaResolventMangoldtWeight (p ^ (k + 1))
  have heq (k : ℕ) : F (2 * k) = 2 * gammaResolventMangoldtWeight (p ^ (2 * k + 1)) :=
    (gamma_character_minus_one_power_corrections χ hχ k).2
  have hoq (k : ℕ) : F (2 * k + 1) = 0 := by
    dsimp only [F]
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
    exact (gamma_character_minus_one_power_corrections χ hχ (k + 1)).1
  have he := ((gamma_odd_mangoldt_series_eq_cost hp).1.mul_left 2).congr (fun k ↦ (heq k).symm)
  have ho : Summable (fun k : ℕ ↦ F (2 * k + 1)) := by
    simpa only [hoq] using (summable_zero : Summable (fun _ : ℕ ↦ (0 : ℝ)))
  refine ⟨Summable.even_add_odd he ho, ?_⟩
  change (∑' k : ℕ, F k) = _
  rw [← tsum_even_add_odd he ho]
  simp only [heq, hoq, tsum_zero, add_zero, tsum_mul_left, (gamma_odd_mangoldt_series_eq_cost hp).2]

/-- At local value minus one, any finite set of positive Euler powers has
cost at most twice log p times the odd Euler cost. Nonnegativity enlarges
the arbitrary prefix to the full parity-cancelled series. -/
theorem gamma_minus_one_positive_prime_correction_le_cost {f p : ℕ} (χ : DirichletCharacter ℂ f)
    (hp : p.Prime) (hχ : χ p = -1) (K : Finset ℕ) :
    (∑ k ∈ K, (1 - (χ (p ^ (k + 1))).re) * gammaResolventMangoldtWeight (p ^ (k + 1))) ≤
      2 * (Real.log p * gammaPrimeOddEulerCost p) := by
  have hs := gamma_minus_one_positive_euler_series_eq_cost χ hp hχ
  rw [← hs.2]
  exact
    hs.1.sum_le_tsum K
      (fun k hk ↦ by
        simpa only [Nat.cast_pow] using gamma_character_euler_correction_nonneg χ (p ^ (k + 1)))

end PseudoPrime.Analysis
