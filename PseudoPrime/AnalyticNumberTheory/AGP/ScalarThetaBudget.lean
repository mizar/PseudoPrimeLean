/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.AGP.PolynomialHalfScaleThetaSupply

/-! # Uniform absorption of the scalar theta error budget -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

/-- The normalized scalar theta error envelope tends to zero. Each logarithmic term is
dominated by its positive power denominator, uniformly independently of the modulus and cutoff. -/
theorem scalar_theta_budget_decay :
    Filter.Tendsto
      (fun x : ℝ ↦
        (1 / 2 : ℝ) * ((Real.log x) ^ 2 / x ^ (7 / 8 : ℝ)) +
          4 * (Real.log 4 + 4) * ((Real.log 2 + Real.log x) / x ^ (3 / 4 : ℝ)) +
          18 * Real.log (5 / 4) * (1 / x ^ (3 / 8 : ℝ)))
      Filter.atTop (nhds 0) := by
  have h2 := DirichletLFunction.tendsto_log_pow_div_rpow (by norm_num only : (0 : ℝ) < 7 / 8) 2
  have h1 := DirichletLFunction.tendsto_log_pow_div_rpow (by norm_num only : (0 : ℝ) < 3 / 4) 1
  have h0 := DirichletLFunction.tendsto_log_pow_div_rpow (by norm_num only : (0 : ℝ) < 3 / 4) 0
  have hlast := DirichletLFunction.tendsto_log_pow_div_rpow (by norm_num only : (0 : ℝ) < 3 / 8) 0
  simp only [pow_one] at h1
  simp only [pow_zero] at h0 hlast
  have hm := (h0.const_mul (Real.log 2)).add h1
  have hm' :
    Filter.Tendsto (fun x : ℝ ↦ (Real.log 2 + Real.log x) / x ^ (3 / 4 : ℝ)) Filter.atTop
      (nhds 0) := by
    convert hm using 1
    · funext x; ring
    · simp only [mul_zero, add_zero]
  have ht :=
    ((h2.const_mul (1 / 2 : ℝ)).add (hm'.const_mul (4 * (Real.log 4 + 4)))).add
      (hlast.const_mul (18 * Real.log (5 / 4)))
  simpa only [mul_zero, add_zero] using ht

open Classical in
/-- For time at least two, a cutoff at least one, and modulus and cutoff bounded by the
eighth root of time, the explicit theta error budget is bounded by a scalar envelope.
Bound cardinality and totient by the modulus and combine the two cutoff powers. -/
theorem scalar_theta_budget_le_envelope {q : ℕ} [NeZero q] {L x ε : ℝ} (hx : 2 ≤ x) (hL : 1 ≤ L)
    (hq : (q : ℝ) ≤ x ^ (1 / 8 : ℝ)) (hLs : L ≤ x ^ (1 / 8 : ℝ)) :
    (1 / 2 : ℝ) * q.primeFactors.card * (Real.log x) ^ 2 +
        (4 * ε * x +
          2 * (((Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1).card : ℝ) *
            ((Real.log 4 + 4) * (2 * L) * Real.log (2 * L))) +
        18 * (q.totient : ℝ) * Real.sqrt x * Real.log (5 / 4) ≤
      4 * ε * x + (1 / 2 : ℝ) * x ^ (1 / 8 : ℝ) * (Real.log x) ^ 2 +
        4 * (Real.log 4 + 4) * x ^ (1 / 4 : ℝ) * (Real.log 2 + Real.log x) +
        18 * Real.log (5 / 4) * x ^ (5 / 8 : ℝ) := by
  have hxpos : 0 < x := by linarith only [hx]
  have hxone : 1 ≤ x := by linarith only [hx]
  have hω : (q.primeFactors.card : ℝ) ≤ x ^ (1 / 8 : ℝ) :=
    (Nat.cast_le.mpr (Arithmetic.card_primeFactors_le_level (NeZero.ne q))).trans hq
  have hcard :
    (((Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1).card : ℝ) ≤ x ^ (1 / 8 : ℝ) :=
    (Nat.cast_le.mpr (Arithmetic.card_character_family_le_level _)).trans hq
  have hφ : (q.totient : ℝ) ≤ x ^ (1 / 8 : ℝ) := (Nat.cast_le.mpr (Nat.totient_le q)).trans hq
  have hLx : L ≤ x := by
    have hh := Real.rpow_le_rpow_of_exponent_le hxone (by norm_num only : (1 / 8 : ℝ) ≤ 1)
    rw [Real.rpow_one] at hh
    exact hLs.trans hh
  have hlog :=
    Real.log_le_log (by linarith only [hL] : 0 < 2 * L)
      (mul_le_mul_of_nonneg_left hLx (by norm_num only : (0 : ℝ) ≤ 2))
  rw [Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) hxpos.ne'] at hlog
  have hlogL : 0 ≤ Real.log (2 * L) := Real.log_nonneg (by linarith only [hL])
  have hlogsum : 0 ≤ Real.log 2 + Real.log x := hlogL.trans hlog
  have hc : 0 ≤ Real.log 4 + 4 := by
    have hh := Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 4)
    linarith only [hh]
  have hpair :=
    mul_le_mul hcard hLs (by linarith only [hL] : 0 ≤ L) (Real.rpow_nonneg hxpos.le (1 / 8))
  have hpowpair : x ^ (1 / 8 : ℝ) * x ^ (1 / 8 : ℝ) = x ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hxpos]
    norm_num only
  rw [hpowpair] at hpair
  have hprod := mul_le_mul hpair hlog hlogL (Real.rpow_nonneg hxpos.le (1 / 4))
  have hcorr := mul_le_mul_of_nonneg_left hprod (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hc)
  have homega := mul_le_mul_of_nonneg_right hω (sq_nonneg (Real.log x))
  have hsqrt := mul_le_mul_of_nonneg_right hφ (Real.sqrt_nonneg x)
  have hpowsqrt : x ^ (1 / 8 : ℝ) * Real.sqrt x = x ^ (5 / 8 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hxpos]
    norm_num only
  rw [hpowsqrt] at hsqrt
  have hlog54 : 0 ≤ Real.log (5 / 4) := Real.log_nonneg (by norm_num only)
  have hprime := mul_le_mul_of_nonneg_right hsqrt hlog54
  nlinarith only [homega, hcorr, hprime]

/-- For positive time, express any real power as time divided by its complementary power.
This normalizes the scalar theta envelope before applying its limiting estimate. -/
theorem rpow_eq_time_div_complement {x : ℝ} (hx : 0 < x) (a : ℝ) : x ^ a = x / x ^ (1 - a) := by
  conv_rhs =>
    lhs; rw [← Real.rpow_one x]
  rw [← Real.rpow_sub hx]
  congr 1
  ring

open Classical in
/-- An absolute time threshold absorbs the scalar theta budget at tolerance log(5/4)/512
whenever both modulus and cutoff are bounded by the eighth root of time. The threshold
is chosen before both parameters using the normalized envelope limit. -/
theorem exists_uniform_scalar_theta_budget_threshold :
    ∃ X : ℝ,
      2 ≤ X ∧
        ∀ q : ℕ,
          ∀ [NeZero q],
            ∀ L x : ℝ,
              X ≤ x →
                1 ≤ L →
                (q : ℝ) ≤ x ^ (1 / 8 : ℝ) →
                L ≤ x ^ (1 / 8 : ℝ) →
                (1 / 2 : ℝ) * q.primeFactors.card * (Real.log x) ^ 2 +
                    (4 * (Real.log (5 / 4) / 512) * x +
                      2 * (((Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1).card : ℝ) *
                        ((Real.log 4 + 4) * (2 * L) * Real.log (2 * L))) +
                    18 * (q.totient : ℝ) * Real.sqrt x * Real.log (5 / 4) ≤
                  (1 / 32 : ℝ) * x * Real.log (5 / 4) := by
  have hl : 0 < Real.log (5 / 4) := Real.log_pos (by norm_num only)
  obtain ⟨X, hX⟩ :=
    Filter.eventually_atTop.mp
      (scalar_theta_budget_decay.eventually
        (gt_mem_nhds (div_pos hl (by norm_num only : (0 : ℝ) < 128))))
  refine ⟨max 2 X, le_max_left _ _, ?_⟩
  intro q inst L x hx hL hq hLs
  have hx2 : 2 ≤ x := (le_max_left 2 X).trans hx
  have hxp : 0 < x := by linarith only [hx2]
  have hs := hX x ((le_max_right 2 X).trans hx)
  have hm := mul_le_mul_of_nonneg_left hs.le hxp.le
  have hb := scalar_theta_budget_le_envelope hx2 hL hq hLs (ε := Real.log (5 / 4) / 512)
  have hp1 := rpow_eq_time_div_complement hxp (1 / 8)
  have hp2 := rpow_eq_time_div_complement hxp (1 / 4)
  have hp3 := rpow_eq_time_div_complement hxp (5 / 8)
  norm_num only at hp1 hp2 hp3
  rw [hp1, hp2, hp3] at hb
  simp only [div_eq_mul_inv] at hb hm
  nlinarith only [hb, hm, mul_pos hl hxp]

end PseudoPrime.AnalyticNumberTheory.AGP
