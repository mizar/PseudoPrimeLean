/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimePowerLogRows

/-! # Coverage of prime-power increment certificates -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- If the prime-power values in a duplicate-free row list are exactly the
prime powers in `(a, b]`, their Mangoldt weights sum to the interval increment.
Non-prime-powers contribute zero; the proof never indexes the list. -/
theorem prime_power_rows_cover_sum {a b : ℕ} (rows : List PrimePowerLogRow)
    (hn : (rows.map (fun r ↦ r.p ^ (r.k + 1))).Nodup)
    (hcover :
      ∀ n : ℕ, n ∈ (Finset.Ioc a b).filter IsPrimePow ↔ n ∈ rows.map (fun r ↦ r.p ^ (r.k + 1))) :
    (∑ n ∈ Finset.Ioc a b, ArithmeticFunction.vonMangoldt n) =
      (rows.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum := by
  classical
  have hs : (Finset.Ioc a b).filter IsPrimePow = (rows.map (fun r ↦ r.p ^ (r.k + 1))).toFinset := by
    ext n
    simpa only [List.mem_toFinset] using hcover n
  calc
    (∑ n ∈ Finset.Ioc a b, ArithmeticFunction.vonMangoldt n) =
        ∑ n ∈ (Finset.Ioc a b).filter IsPrimePow, ArithmeticFunction.vonMangoldt n :=
      by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro n hn hn'
      have hnp : ¬IsPrimePow n := by
        intro hp
        exact hn' (Finset.mem_filter.mpr ⟨hn, hp⟩)
      exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnp
    _ = ∑ n ∈ (rows.map (fun r ↦ r.p ^ (r.k + 1))).toFinset, ArithmeticFunction.vonMangoldt n := by
      rw [hs]
    _ = (rows.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum := by
      rw [List.sum_toFinset _ hn, List.map_map]
      rfl

/-- A duplicate-free, complete, checked list of prime-power logarithm rows
extends certified bounds for `psi a` to `psi b`. Coverage and the row checks
are separate hypotheses, so an unverified generator cannot supply the result. -/
theorem psi_prefix_bounds_of_complete_rows {a b : ℕ} {L U : ℝ} (hab : a ≤ b)
    (hL : L ≤ Chebyshev.psi a) (hU : Chebyshev.psi a ≤ U) (rows : List PrimePowerLogRow)
    (hrows : rows.all primePowerLogCheck = true) (hn : (rows.map (fun r ↦ r.p ^ (r.k + 1))).Nodup)
    (hcover :
      ∀ n : ℕ, n ∈ (Finset.Ioc a b).filter IsPrimePow ↔ n ∈ rows.map (fun r ↦ r.p ^ (r.k + 1))) :
    L + (rows.map (fun r ↦ (r.lo : ℝ))).sum ≤ Chebyshev.psi b ∧
      Chebyshev.psi b ≤ U + (rows.map (fun r ↦ (r.hi : ℝ))).sum := by
  exact psi_prefix_bounds_of_rows hab hL hU rows hrows (prime_power_rows_cover_sum rows hn hcover)

/-- A finite-set coverage certificate supplies the support hypothesis for
prime-power row sums. Unlike a universally quantified proposition, the
finite-set equality can be checked directly by a finite arithmetic checker. -/
theorem prime_power_rows_cover_of_finset {a b : ℕ} (rows : List PrimePowerLogRow)
    (hn : (rows.map (fun r ↦ r.p ^ (r.k + 1))).Nodup)
    (hcover : (Finset.Ioc a b).filter IsPrimePow = (rows.map (fun r ↦ r.p ^ (r.k + 1))).toFinset) :
    (∑ n ∈ Finset.Ioc a b, ArithmeticFunction.vonMangoldt n) =
      (rows.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum := by
  apply prime_power_rows_cover_sum rows hn
  intro n
  rw [hcover, List.mem_toFinset]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
