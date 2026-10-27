/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HalfScaleBudgetUniformMajorant

/-! # Uniform absorption above polynomial scales -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- The logarithmic height weight tends to zero. This separates height decay from time decay. -/
theorem tendsto_height_log_div_sqrt :
    Filter.Tendsto (fun R : ℝ ↦ (Real.log 2 + Real.log R + 2) / Real.sqrt R) Filter.atTop
      (nhds 0) := by
  have hδ : (0 : ℝ) < 1 / 2 := by norm_num only
  have h1 : Filter.Tendsto (fun R : ℝ ↦ Real.log R / R ^ (1 / 2 : ℝ)) Filter.atTop (nhds 0) := by
    simpa only [pow_one] using tendsto_log_pow_div_rpow hδ 1
  have h0 : Filter.Tendsto (fun R : ℝ ↦ 1 / R ^ (1 / 2 : ℝ)) Filter.atTop (nhds 0) := by
    simpa only [pow_zero] using tendsto_log_pow_div_rpow hδ 0
  have hc := h1.add (h0.const_mul (Real.log 2 + 2))
  simp only [mul_zero, add_zero] at hc
  convert hc using 1
  funext R
  rw [Real.sqrt_eq_rpow]
  ring

/-- For positive decay exponent and nonnegative budget constants, a height threshold absorbs the
remainder uniformly under the stated power balance. The proof combines two vanishing weights. -/
theorem exists_uniform_remainder_absorption_of_power_balance {σ δ C K T ε : ℝ} (hσ : 1 / 2 ≤ σ)
    (hδ : 0 < δ) (hbalance : σ + 2 * δ ≤ 1) (hC : 0 ≤ C) (hK : 0 ≤ K) (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ R₀ : ℝ,
      4 ≤ R₀ ∧
        ∀ (H : ℕ),
          3 ≤ H →
            R₀ ≤ ((H + 1 : ℕ) : ℝ) →
            ∀ (q : ℕ),
              1 ≤ q →
                q ≤ H + 1 →
                (q : ℝ) ≤ Real.sqrt ((H + 1 : ℕ) : ℝ) →
                ∀ x : ℝ,
                  4 ≤ x →
                    ((H + 1 : ℕ) : ℝ) ≤ x →
                    ((H + 1 : ℕ) : ℝ) ^ 2 ≤ x ^ δ →
                    (q : ℝ) * primitiveHalfScaleRemainderBudget q x σ H C K T +
                        (q : ℝ) ^ 2 * (Real.log x) ^ 2 ≤
                      ε * x := by
  have hu :
    Filter.Tendsto (fun R : ℝ ↦ 240 * T * ((Real.log 2 + Real.log R + 2) / Real.sqrt R))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_height_log_div_sqrt.const_mul (240 * T)
  have hv :
    Filter.Tendsto (fun x : ℝ ↦ halfScaleTimeBudgetConstant C K * ((Real.log x + 1) ^ 3 / x ^ δ))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_log_add_one_cube_div_rpow hδ).const_mul (halfScaleTimeBudgetConstant C K)
  obtain ⟨R₁, hR₁⟩ := Filter.eventually_atTop.mp (hu.eventually (gt_mem_nhds (half_pos hε)))
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.mp (hv.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨max 4 (max R₁ X₁), le_max_left _ _, ?_⟩
  intro H hH hR q hq hqr hsqrt x hx hRx hpow
  have hr :=
    hR₁ ((H + 1 : ℕ) : ℝ) ((le_max_left R₁ X₁).trans ((le_max_right 4 (max R₁ X₁)).trans hR))
  have ht := hX₁ x (((le_max_right R₁ X₁).trans ((le_max_right 4 (max R₁ X₁)).trans hR)).trans hRx)
  have hb :=
    weighted_primitive_remainder_le_normalized_majorant hq hH hqr hsqrt hx hRx hpow hσ hbalance hC
      hK hT
  have hm := mul_le_mul_of_nonneg_left (add_le_add hr.le ht.le) (by linarith only [hx] : 0 ≤ x)
  nlinarith only [hb, hm]

/-- A polynomial lower bound on time implies both power-balance inequalities when the
polynomial exponent times the decay exponent is at least two. -/
theorem polynomial_scale_gives_power_balance {R x δ : ℝ} (hR : 1 ≤ R) (hδ : 0 ≤ δ) {b : ℕ}
    (hb : 1 ≤ b) (hbδ : 2 ≤ (b : ℝ) * δ) (hx : R ^ b ≤ x) : R ≤ x ∧ R ^ 2 ≤ x ^ δ := by
  have hrpow : R ≤ R ^ b := by
    have hp := Real.rpow_le_rpow_of_exponent_le hR (by exact_mod_cast hb : (1 : ℝ) ≤ b)
    simpa only [Real.rpow_one, Real.rpow_natCast] using hp
  have hnonneg : 0 ≤ R := zero_le_one.trans hR
  have hbase : R ^ 2 ≤ (R ^ b) ^ δ := by
    rw [← Real.rpow_natCast R 2, ← Real.rpow_natCast R b, ← Real.rpow_mul hnonneg]
    exact Real.rpow_le_rpow_of_exponent_le hR hbδ
  exact ⟨hrpow.trans hx, hbase.trans (Real.rpow_le_rpow (pow_nonneg hnonneg b) hx hδ)⟩

/-- For a fixed strip strictly below one and nonnegative budget constants, choose the exponent
and height threshold before the modulus and time. Every larger polynomial exponent absorbs
the arithmetic remainder into the prescribed positive multiple of time. -/
theorem exists_uniform_remainder_absorption_above_polynomial_scale {σ C K T ε : ℝ}
    (hσlo : 1 / 2 ≤ σ) (hσhi : σ < 1) (hC : 0 ≤ C) (hK : 0 ≤ K) (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ b₀ : ℕ,
      1 ≤ b₀ ∧
        ∃ R₀ : ℝ,
          4 ≤ R₀ ∧
            ∀ (b : ℕ),
              b₀ ≤ b →
                ∀ (H : ℕ),
                  3 ≤ H →
                    R₀ ≤ ((H + 1 : ℕ) : ℝ) →
                    ∀ (q : ℕ),
                      1 ≤ q →
                        q ≤ H + 1 →
                        (q : ℝ) ≤ Real.sqrt ((H + 1 : ℕ) : ℝ) →
                        ∀ x : ℝ,
                          (((H + 1 : ℕ) : ℝ) ^ b) ≤ x →
                            (q : ℝ) * primitiveHalfScaleRemainderBudget q x σ H C K T +
                                (q : ℝ) ^ 2 * (Real.log x) ^ 2 ≤
                              ε * x := by
  let δ := (1 - σ) / 2
  have hδ : 0 < δ := by
    dsimp only [δ]; linarith only [hσhi]
  have hbalance : σ + 2 * δ ≤ 1 := by
    dsimp only [δ]; linarith only []
  obtain ⟨R₀, hR₀, hbound⟩ :=
    exists_uniform_remainder_absorption_of_power_balance hσlo hδ hbalance hC hK hT hε
  obtain ⟨b₀, hb₀⟩ := exists_nat_gt (max 1 (2 / δ))
  have hbpos : 1 ≤ b₀ := by exact_mod_cast (le_max_left 1 (2 / δ)).trans hb₀.le
  have hbδ : 2 ≤ (b₀ : ℝ) * δ := (div_le_iff₀ hδ).mp ((le_max_right 1 (2 / δ)).trans hb₀.le)
  refine ⟨b₀, hbpos, R₀, hR₀, ?_⟩
  intro b hb H hH hR q hq hqr hsqrt x hx
  have hRone : 1 ≤ ((H + 1 : ℕ) : ℝ) := by linarith only [hR₀.trans hR]
  have hbb : 2 ≤ (b : ℝ) * δ := hbδ.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hb) hδ.le)
  have hp := polynomial_scale_gives_power_balance hRone hδ.le (hbpos.trans hb) hbb hx
  exact hbound H hH hR q hq hqr hsqrt x ((hR₀.trans hR).trans hp.1) hp.1 hp.2

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
