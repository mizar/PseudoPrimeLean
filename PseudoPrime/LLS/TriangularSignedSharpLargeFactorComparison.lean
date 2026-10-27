/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularSignedSharpConductorComparison
public import PseudoPrime.LLS.TriangularLargeFactorComparison

/-! # Signed large-factor comparison for triangular prime witnesses -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, scale above one, large level factors and containment of eligible
small primes, the signed alpha-18 comparison depends only on the level logarithm
and subgroup index. The fixed per-character cost is 5964 and the independent
scale-one cost is 602600000. This is the scalar comparison for the improved gap. -/
theorem triangular18_signed_sharp_comparison_of_large_prime_factors {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 1 < x) (hlarge : ∀ p ∈ q.primeFactors, x ≤ (p : ℝ))
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ x → residueInSubgroup q H p) :
    (H.index : ℝ) *
        (Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
          36 * Real.log q / (Real.sqrt x - 1)) ≤
      300000000 * Real.sqrt x + 1300000 * x ^ (1 / 4 : ℝ) + 602600000 +
        ((H.index : ℝ) - 1) *
          (36 * Real.log q + 5964 + 4000000000000 * (Real.log q + 284) * x ^ (-9 / 16 : ℝ)) := by
  have hb := triangular18_level_prime_budget_le_of_large_factors hx hlarge
  have hl :=
    (sub_le_sub_left hb (Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ))).trans
      (triangular18_finite_principal_lower_of_rh (q := q) hGRH.riemann (zero_lt_one.trans hx))
  have hm := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg H.index)
  have hc :=
    hm.trans (triangular18_principal_sum_le_signed_sharp_conductor_numeric H hGRH hx.le hsmall)
  have hcoef : 0 ≤ 36 + 4000000000000 * x ^ (-9 / 16 : ℝ) :=
    add_nonneg (by norm_num only)
      (mul_nonneg (by norm_num only) (Real.rpow_nonneg (zero_lt_one.trans hx).le _))
  have hu := mul_le_mul_of_nonneg_left (subgroupConductorLogSum_le H) hcoef
  nlinarith only [hc, hu]

/-- Under GRH at nonzero level and scale above one, a strict signed alpha-18
gap produces a prime dividing the level or outside the subgroup. Derive the
large-factor and containment hypotheses from absence of such a witness.
This connects the improved analytic budget to the prime-witness interface;
the gap still needs numerical certification at the desired scale. -/
theorem exists_prime_factor_or_outside_of_triangular18_signed_sharp_gap {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 1 < x)
    (hgap :
      300000000 * Real.sqrt x + 1300000 * x ^ (1 / 4 : ℝ) + 602600000 +
          ((H.index : ℝ) - 1) *
            (36 * Real.log q + 5964 + 4000000000000 * (Real.log q + 284) * x ^ (-9 / 16 : ℝ)) <
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
  exact
    (not_le_of_gt hgap)
      (triangular18_signed_sharp_comparison_of_large_prime_factors H hGRH hx hlarge hsmall)

end PseudoPrime.LLS.PaperStatements
