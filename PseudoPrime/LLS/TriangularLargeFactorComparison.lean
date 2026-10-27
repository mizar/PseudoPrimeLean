/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularFiniteComparison

/-! # Large-factor alpha-18 comparison without a prime-list certificate -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- At nonzero level and scale x > 1, if every level prime is at least x,
the exact geometric correction budget is at most 36 log q/(sqrt x-1).
Compare denominators and sum the prime logarithms. -/
theorem triangular18_level_prime_budget_le_of_large_factors {q : ℕ} [NeZero q] {x : ℝ} (hx : 1 < x)
    (hlarge : ∀ p ∈ q.primeFactors, x ≤ (p : ℝ)) :
    (∑ p ∈ q.primeFactors, 36 * (Real.log p / (Real.sqrt p - 1))) ≤
      36 * Real.log q / (Real.sqrt x - 1) := by
  have hs : 1 < Real.sqrt x := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num only : (0 : ℝ) ≤ 1) hx
  have hd : 0 < Real.sqrt x - 1 := sub_pos.mpr hs
  have hb :=
    Finset.sum_le_sum
      (fun p (hp : p ∈ q.primeFactors) ↦ by
        have hden : Real.sqrt x - 1 ≤ Real.sqrt p - 1 :=
          sub_le_sub_right (Real.sqrt_le_sqrt (hlarge p hp)) 1
        exact
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) hd hden)
            (by norm_num only : (0 : ℝ) ≤ 36))
  simp only [← Finset.mul_sum, ← Finset.sum_div] at hb
  rw [← Finset.mul_sum]
  have hl :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (AnalyticNumberTheory.Arithmetic.sum_log_primeFactors_le_log (NeZero.ne q))
        (by norm_num only : (0 : ℝ) ≤ 36))
      hd.le
  exact hb.trans (by simpa only [mul_div_assoc] using hl)

/-- Under GRH at x > 1 with large level factors and no eligible outside prime,
the finite triangular comparison has only the level logarithm and subgroup index
as arithmetic costs. Bound the conductor sum and prime geometric correction. -/
theorem triangular18_comparison_of_large_prime_factors {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 < x)
    (hlarge : ∀ p ∈ q.primeFactors, x ≤ (p : ℝ))
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ x → residueInSubgroup q H p) :
    (H.index : ℝ) *
        (Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
          36 * Real.log q / (Real.sqrt x - 1)) ≤
      300000000 * Real.sqrt x + 1300000 * x ^ (1 / 4 : ℝ) +
        ((H.index : ℝ) - 1) *
          (36 * Real.log q + 1350000000000000 + 55000 +
            4000000000000 * (Real.log q + 284) * x ^ (-9 / 16 : ℝ)) := by
  have hb := triangular18_level_prime_budget_le_of_large_factors hx hlarge
  have hl :=
    mul_le_mul_of_nonneg_left
      (sub_le_sub_left hb (Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ)))
      (Nat.cast_nonneg H.index)
  have hc := hl.trans (triangular18_finite_principal_comparison H hGRH hx.le hsmall)
  have hcoef : 0 ≤ 36 + 4000000000000 * x ^ (-9 / 16 : ℝ) :=
    add_nonneg (by norm_num only)
      (mul_nonneg (by norm_num only) (Real.rpow_nonneg (zero_lt_one.trans hx).le _))
  have hu := mul_le_mul_of_nonneg_left (subgroupConductorLogSum_le H) hcoef
  nlinarith only [hc, hu]

/-- Under GRH at nonzero level and x > 1, a strict explicit numerical gap
produces a prime through x that divides the level or lies outside the subgroup.
If neither exists, all level factors are large and the finite comparison contradicts the gap.
The gap is a numerical condition still to be certified at the chosen scale. -/
theorem exists_prime_factor_or_outside_of_triangular18_gap {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 1 < x)
    (hgap :
      300000000 * Real.sqrt x + 1300000 * x ^ (1 / 4 : ℝ) +
          ((H.index : ℝ) - 1) *
            (36 * Real.log q + 1350000000000000 + 55000 +
              4000000000000 * (Real.log q + 284) * x ^ (-9 / 16 : ℝ)) <
        (H.index : ℝ) *
          (Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
            36 * Real.log q / (Real.sqrt x - 1))) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ (p ∣ q ∨ ¬residueInSubgroup q H p) := by
  classical
  by_contra hnone
  have hlarge (p : ℕ) (hp : p ∈ q.primeFactors) : x ≤ (p : ℝ) := by
    by_contra hlt
    exact
      hnone
        ⟨p, Nat.prime_of_mem_primeFactors hp, (lt_of_not_ge hlt).le,
          Or.inl (Nat.dvd_of_mem_primeFactors hp)⟩
  have hsmall (p : ℕ) (hp : p.Prime) (_ : ¬p ∣ q) (hle : (p : ℝ) ≤ x) :
    residueInSubgroup q H p := by
    by_contra hout
    exact hnone ⟨p, hp, hle, Or.inr hout⟩
  exact (not_le_of_gt hgap) (triangular18_comparison_of_large_prime_factors H hGRH hx hlarge hsmall)

end PseudoPrime.LLS.PaperStatements
