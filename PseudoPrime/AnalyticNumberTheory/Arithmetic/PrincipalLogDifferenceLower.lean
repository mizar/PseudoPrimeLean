/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedDifferences
public import Mathlib.Analysis.Complex.ExponentialBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrincipalCharacterSums

/-! # An elementary principal logarithmic difference with a positive margin -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Eventually the Chebyshev psi function exceeds two thirds of its scale.
Use its elementary lower bound, the numerical lower bound for `log 2`, and
`log t = o(t)` to absorb the logarithmic remainder. This provides a strict
margin above one half after comparing the scales `x` and `4x/5`. -/
theorem eventually_two_thirds_mul_le_psi :
    ∀ᶠ t : ℝ in Filter.atTop, (2 / 3 : ℝ) * t ≤ Chebyshev.psi t := by
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.mp
      (Real.isLittleO_log_id_atTop.bound (by norm_num only : (0 : ℝ) < 1 / 100))
  filter_upwards [Filter.eventually_ge_atTop (max N 100)] with t ht
  have ht100 : 100 ≤ t := (le_max_right N 100).trans ht
  have htN : N ≤ t + 2 := by linarith only [(le_max_left N 100).trans ht]
  have hlog := hN (t + 2) htN
  have htp : 0 ≤ t + 2 := by linarith only [ht100]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, id_eq, abs_of_nonneg htp] at hlog
  have hlog' := (le_abs_self (Real.log (t + 2))).trans hlog
  have hcheb := Chebyshev.psi_ge' (by linarith only [ht100] : 0 ≤ t)
  have hnum := Real.log_two_gt_d9
  have hprod := mul_le_mul_of_nonneg_right hnum.le (by linarith only [ht100] : 0 ≤ t - 1)
  nlinarith only [ht100, hlog', hcheb, hprod]

/-- There is an absolute cutoff above which the unsigned logarithmic difference
between `x` and `4x/5` exceeds `17x log(5/4)/32`. Apply the finite difference
inequality to the eventual Chebyshev lower bound. The coefficient exceeds one
half, leaving room for nonprincipal and prime-power errors in theta supply. -/
theorem exists_logWeightedMangoldtSum_four_fifths_difference_lower :
    ∃ X : ℝ,
      1 ≤ X ∧
        ∀ x : ℝ,
          X ≤ x →
            (17 / 32 : ℝ) * x * Real.log (5 / 4) ≤
              logWeightedMangoldtSum x - logWeightedMangoldtSum (4 * x / 5) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp eventually_two_thirds_mul_le_psi
  refine ⟨max 1 (5 * N / 4), le_max_left _ _, ?_⟩
  intro x hx
  have hxone : 1 ≤ x := (le_max_left 1 (5 * N / 4)).trans hx
  have hNx : N ≤ 4 * x / 5 := by linarith only [(le_max_right 1 (5 * N / 4)).trans hx]
  have ht : 0 < 4 * x / 5 := by linarith only [hxone]
  have htx : 4 * x / 5 ≤ x := by linarith only [hxone]
  have hratio : x / (4 * x / 5) = (5 / 4 : ℝ) := by
    apply (div_eq_iff ht.ne').2
    ring
  have hlog : 0 ≤ Real.log (5 / 4 : ℝ) := Real.log_nonneg (by norm_num only)
  have hp := hN (4 * x / 5) hNx
  have hb := (logWeightedMangoldtSum_difference_bounds ht htx).1
  rw [hratio] at hb
  exact
    (mul_le_mul_of_nonneg_right
          (by linarith only [hp, hxone] : (17 / 32 : ℝ) * x ≤ Chebyshev.psi (4 * x / 5)) hlog).trans
      hb

/-- At a positive scale the common-factor correction is nonnegative, for any
level. Each index lies below the cutoff, hence its logarithmic weight is
nonnegative. This lets a principal difference discard its lower-end correction. -/
theorem commonFactorLogWeightedSum_nonneg {x : ℝ} (hx : 0 < x) (q : ℕ) :
    0 ≤ commonFactorLogWeightedSum x q := by
  apply Finset.sum_nonneg
  intro n hn
  have hnI := (Finset.mem_filter.mp hn).1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hnI).1
  have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp (Finset.mem_Ioc.mp hnI).2
  exact
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.log_nonneg ((le_div_iff₀ hnpos).mpr (by simpa only [one_mul] using hnx)))

/-- For nonzero level and positive scale, the principal logarithmic difference
is at least the unsigned difference minus `omega(q) log(x)^2/2`. Use the exact
principal-character identity and discard the nonnegative lower-end correction.
This keeps the modulus dependence explicit for the uniform theta-supply budget. -/
theorem principalLogDifference_ge_unsigned_sub_common_bound {q : ℕ} (hq : q ≠ 0) {x : ℝ}
    (hx : 0 < x) :
    logWeightedMangoldtSum x - logWeightedMangoldtSum (4 * x / 5) -
        (1 / 2 : ℝ) * q.primeFactors.card * (Real.log x) ^ 2 ≤
      (characterLogWeightedSum x (1 : DirichletCharacter ℂ q) -
          characterLogWeightedSum (4 * x / 5) (1 : DirichletCharacter ℂ q)).re := by
  rw [Complex.sub_re, characterLogWeightedSum_one_re_eq, characterLogWeightedSum_one_re_eq]
  have hb := commonFactorLogWeightedSum_le hq hx
  have hsmall :=
    commonFactorLogWeightedSum_nonneg
      (show 0 < 4 * x / 5 from div_pos (mul_pos (by norm_num only) hx) (by norm_num only)) q
  linarith only [hb, hsmall]

/-- Above one absolute cutoff, every nonzero level has principal logarithmic
difference at least `17x log(5/4)/32` minus its common-factor bound. Combine the
unsigned Chebyshev difference with the principal-character identity. The cutoff
is independent of the modulus, which is essential for the later uniform supply. -/
theorem exists_principalLogDifference_lower :
    ∃ X : ℝ,
      1 ≤ X ∧
        ∀ (q : ℕ),
          q ≠ 0 →
            ∀ x : ℝ,
              X ≤ x →
                (17 / 32 : ℝ) * x * Real.log (5 / 4) -
                    (1 / 2 : ℝ) * q.primeFactors.card * (Real.log x) ^ 2 ≤
                  (characterLogWeightedSum x (1 : DirichletCharacter ℂ q) -
                      characterLogWeightedSum (4 * x / 5) (1 : DirichletCharacter ℂ q)).re := by
  obtain ⟨X, hX, hbound⟩ := exists_logWeightedMangoldtSum_four_fifths_difference_lower
  refine ⟨X, hX, fun q hq x hx ↦ ?_⟩
  exact
    (sub_le_sub_right (hbound x hx) _).trans
      (principalLogDifference_ge_unsigned_sub_common_bound hq (zero_lt_one.trans_le (hX.trans hx)))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
