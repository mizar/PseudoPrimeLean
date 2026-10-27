/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaFiniteEulerIntervals

/-! # Certified finite-row blocks for one-sided Euler prefix bounds -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- One finite prime-power row and its rational interval certificate data.
The fields give a prime base, exponent minus one, logarithm Taylor scale
and term count, logarithm endpoints and node-power intervals. A valid row
requires prime primality and a true check; block support is verified separately. -/
structure GammaFiniteEulerRow where
  prime : ℕ
  exponent : ℕ
  logScale : ℕ
  logTerms : ℕ
  logLower : ℚ
  logUpper : ℚ
  ratios : ℚ → ℚ × ℚ

/-- The natural prime-power input represented by a row.
Exponent plus one ensures a positive power. Block certificates verify
its interval membership and exclude repeated indices. -/
def GammaFiniteEulerRow.index (r : GammaFiniteEulerRow) : ℕ :=
  r.prime ^ (r.exponent + 1)

/-- The rational Mangoldt-weight lower allowance for one row.
Multiply the logarithm lower endpoint by the signed Euler-weight lower
endpoint. Its soundness requires primality and the row interval check. -/
def GammaFiniteEulerRow.lower (r : GammaFiniteEulerRow) : ℚ :=
  r.logLower * gammaFiniteEulerLower r.ratios

/-- Check the real-power intervals, logarithm interval and Euler
lower endpoint nonnegativity. The primality proof is separate so that
large primes can use the kernel arithmetic reflection tactic. -/
def GammaFiniteEulerRow.check (r : GammaFiniteEulerRow) : Bool :=
  gammaFiniteEulerRatioCheck r.index r.ratios &&
    rationalLogIntervalCheck r.prime r.logScale r.logTerms r.logLower r.logUpper &&
    decide (0 ≤ gammaFiniteEulerLower r.ratios)

/-- A prime row with a successful interval check has its rational
lower allowance below the actual Mangoldt Euler weight. Extract all checks
and apply the proved prime-power row bounds. -/
theorem GammaFiniteEulerRow.lower_le (r : GammaFiniteEulerRow) (hp : r.prime.Prime)
    (hc : r.check = true) : (r.lower : ℝ) ≤ gammaResolventMangoldtWeight r.index := by
  have hh :
    (gammaFiniteEulerRatioCheck r.index r.ratios &&
        rationalLogIntervalCheck r.prime r.logScale r.logTerms r.logLower r.logUpper) &&
      decide (0 ≤ gammaFiniteEulerLower r.ratios) = true :=
    hc
  obtain ⟨hb, hlo⟩ := Bool.and_eq_true_iff.mp hh
  obtain ⟨hpow, hlog⟩ := Bool.and_eq_true_iff.mp hb
  exact (gamma_prime_power_row_check_bounds hp hpow hlog (of_decide_eq_true hlo)).1

/-- A list of certified prime-power rows with distinct indices
inside (lo,hi] gives a lower bound for the actual full Euler block.
Sum the row inequalities and use nonnegativity on the omitted inputs.
Exact support coverage is unnecessary for this one-sided certificate. -/
theorem gamma_finite_row_block_lower (rows : List GammaFiniteEulerRow) (lo hi : ℕ)
    (hp : rows.Forall (fun r ↦ r.prime.Prime)) (hc : rows.Forall (fun r ↦ r.check = true))
    (hn : (rows.map GammaFiniteEulerRow.index).Nodup)
    (hm : rows.Forall (fun r ↦ lo < r.index ∧ r.index ≤ hi)) :
    (((rows.map GammaFiniteEulerRow.lower).sum : ℚ) : ℝ) ≤
      ∑ m ∈ Finset.Ioc lo hi, gammaResolventMangoldtWeight m := by
  have hl :=
    List.sum_le_sum
      (fun (r : GammaFiniteEulerRow) hr ↦
        r.lower_le (List.forall_iff_forall_mem.mp hp r hr) (List.forall_iff_forall_mem.mp hc r hr))
  have hs : (rows.map GammaFiniteEulerRow.index).toFinset ⊆ Finset.Ioc lo hi := by
    intro m hmem
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hmem)
    exact Finset.mem_Ioc.mpr (List.forall_iff_forall_mem.mp hm r hr)
  have ht :=
    Finset.sum_le_sum_of_subset_of_nonneg hs (fun m _ _ ↦ gammaResolventMangoldtWeight_nonneg m)
  rw [List.sum_toFinset gammaResolventMangoldtWeight hn, List.map_map] at ht
  norm_num only [Rat.cast_list_sum, List.map_map, Function.comp_def]
  exact hl.trans ht

end PseudoPrime.Analysis
