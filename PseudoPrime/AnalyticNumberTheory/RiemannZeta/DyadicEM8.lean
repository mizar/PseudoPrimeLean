/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.DyadicPowerSums
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaFiniteEM8

/-! # Dyadic odd-sum decomposition of the Euler–Maclaurin approximation -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- At a positive cutoff, the zero-extended range sum equals the sum over positive integers below
the cutoff. The only additional term is zero. This connects the dyadic recurrence to the finite
Euler–Maclaurin approximation. -/
theorem dyadicPowerTerm_range (s : ℂ) {N : ℕ} (hN : 0 < N) :
    (∑ k ∈ Finset.Icc 1 (N - 1), (k : ℂ) ^ (-s)) = ∑ k ∈ Finset.range N, dyadicPowerTerm s k := by
  calc
    _ = ∑ k ∈ Finset.Icc 1 (N - 1), dyadicPowerTerm s k := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk0 : k ≠ 0 := Nat.ne_of_gt ((Finset.mem_Icc.mp hk).1)
      simp only [dyadicPowerTerm, hk0, ↓reduceIte]
    _ = _ := by
      apply Finset.sum_subset
      · intro k hk
        exact Finset.mem_range.mpr (Nat.lt_of_le_pred hN (Finset.mem_Icc.mp hk).2)
      · intro k hk hnot
        have hkN := Finset.mem_range.mp hk
        have hk0 : k = 0 := by
          by_contra h
          apply hnot
          exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr h, Nat.le_pred_of_lt hkN⟩
        simp only [hk0, dyadicPowerTerm, ↓reduceIte]

/-- At a positive power-of-two cutoff, the finite Euler–Maclaurin approximation equals its odd
sum plus a scaled half-length sum and the exact grouped correction at the cutoff. The grouped
formula and the dyadic recurrence prove the identity; no numerical approximation is introduced.
The result is the first Horner step for the compact zero-endpoint checker. -/
theorem finiteEM8At_dyadic (t : ℝ) (m : ℕ) :
    finiteEM8At (2 ^ (m + 1)) t =
      let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
      (∑ k ∈ Finset.range (2 ^ m), dyadicPowerTerm s (2 * k + 1)) +
        (2 : ℂ) ^ (-s) * (∑ k ∈ Finset.range (2 ^ m), dyadicPowerTerm s k) +
        finiteEM8CoefficientAt (2 ^ (m + 1)) t * (2 ^ (m + 1) : ℂ) ^ (-s) := by
  rw [finiteEM8At_eq_grouped _ (pow_pos (by decide) _),
    dyadicPowerTerm_range _ (pow_pos (by decide) _), dyadicPowerTerm_sum]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

/-- At cutoff `2 ^ m`, the exact Euler–Maclaurin finite expression is the odd-sum Horner
recurrence plus the grouped correction. The power-of-two cutoff is positive and the recurrence
equals the original finite sum, so this identity applies at 512 without numerical assumptions. -/
theorem finiteEM8At_oddHorner (t : ℝ) (m : ℕ) :
    finiteEM8At (2 ^ m) t =
      let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
      dyadicOddHorner s m + finiteEM8CoefficientAt (2 ^ m) t * (2 ^ m : ℂ) ^ (-s) := by
  rw [finiteEM8At_eq_grouped _ (pow_pos (by decide) _),
    dyadicPowerTerm_range _ (pow_pos (by decide) _), ← dyadicOddHorner_eq]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

/-- The exact Euler–Maclaurin expression at cutoff `2 ^ m` uses only odd power sums and the
shared complex power at two. The correction's cutoff power is the mth power of the same value.
This combines the Horner identity with the positive-base power law for compact endpoint checks. -/
theorem finiteEM8At_oddHorner_pow (t : ℝ) (m : ℕ) :
    finiteEM8At (2 ^ m) t =
      let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
      dyadicOddHorner s m + finiteEM8CoefficientAt (2 ^ m) t * ((2 : ℂ) ^ (-s)) ^ m := by
  rw [finiteEM8At_oddHorner]
  simp only [dyadic_cpow]

/-- At cutoff `2 ^ (m + 1)`, the exact Euler–Maclaurin expression is obtained from the first
component of the cumulative odd-sum pair and the grouped correction. The correction reuses the
same base-two complex power. The equality connects the one-pass odd-prefix recurrence to the
finite expression used in zero-endpoint certification. -/
theorem finiteEM8At_oddPair (t : ℝ) (m : ℕ) :
    finiteEM8At (2 ^ (m + 1)) t =
      let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
      (dyadicOddPair s m).1 +
        finiteEM8CoefficientAt (2 ^ (m + 1)) t * ((2 : ℂ) ^ (-s)) ^ (m + 1) := by
  rw [finiteEM8At_oddHorner_pow]
  simp only [dyadicOddHorner_eq, dyadicOddPair_eq]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
