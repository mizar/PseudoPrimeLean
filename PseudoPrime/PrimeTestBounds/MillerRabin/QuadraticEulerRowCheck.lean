/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaFiniteEulerIntervals

/-! # Checked row interface for finite Euler-center data -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational data for one prime-power Euler contribution.
Fields p and k encode p^(k+1); j normalizes the 32-term Taylor logarithm;
lo and hi enclose log p; ratios give signed-node power intervals.
The checker verifies primality, root inequalities and nonnegativity rather
than trusting any field. Rows feed the finite Euler-center certificate. -/
structure EulerCenterRow where
  p : ℕ
  k : ℕ
  j : ℕ
  lo : ℚ
  hi : ℚ
  ratios : ℚ → ℚ × ℚ

/-- Check every rational premise for a row using fast prime decision,
twentieth-power endpoint checks, a 32-term Taylor logarithm and signed
weight positivity. The Boolean result is interpreted by the soundness
theorem; it introduces no numerical assumptions into the real bound. -/
def eulerCenterRowCheck (r : EulerCenterRow) : Bool :=
  @decide r.p.Prime (Nat.decidablePrime' r.p) &&
    Analysis.gammaFiniteEulerRatioCheck (r.p ^ (r.k + 1) : ℕ) r.ratios &&
    Analysis.rationalLogIntervalCheck r.p r.j 32 r.lo r.hi &&
    decide (0 ≤ Analysis.gammaFiniteEulerLower r.ratios)

/-- A successful row check proves primality and both actual real
Mangoldt bounds. Extract the Boolean conditions and apply the existing
prime-power row soundness theorem. This connects finite data to real sums. -/
theorem eulerCenterRowCheck_sound {r : EulerCenterRow} (h : eulerCenterRowCheck r = true) :
    r.p.Prime ∧
      ((r.lo * Analysis.gammaFiniteEulerLower r.ratios : ℚ) : ℝ) ≤
        Analysis.gammaResolventMangoldtWeight (r.p ^ (r.k + 1)) ∧
      Analysis.gammaResolventMangoldtWeight (r.p ^ (r.k + 1)) ≤
        ((r.hi * Analysis.gammaFiniteEulerUpper r.ratios : ℚ) : ℝ) := by
  obtain ⟨h, hh⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h, hl⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hp, hc⟩ := Bool.and_eq_true_iff.mp h
  let : Decidable r.p.Prime := Nat.decidablePrime' r.p
  have hprime : r.p.Prime := of_decide_eq_true hp
  exact ⟨hprime, Analysis.gamma_prime_power_row_check_bounds hprime hc hl (of_decide_eq_true hh)⟩

/-- A list whose rows all pass the checker has its actual Mangoldt sum
between the sums of the rational row endpoints. Apply row soundness at
each list member and sum the inequalities. This aggregates finite numerical
certificates without changing their exact prime-power interpretation. -/
theorem euler_checked_rows_sum_bounds (rows : List EulerCenterRow)
    (h : rows.all eulerCenterRowCheck = true) :
    (rows.map (fun r ↦ ((r.lo * Analysis.gammaFiniteEulerLower r.ratios : ℚ) : ℝ))).sum ≤
        (rows.map (fun r ↦ Analysis.gammaResolventMangoldtWeight (r.p ^ (r.k + 1)))).sum ∧
      (rows.map (fun r ↦ Analysis.gammaResolventMangoldtWeight (r.p ^ (r.k + 1)))).sum ≤
        (rows.map (fun r ↦ ((r.hi * Analysis.gammaFiniteEulerUpper r.ratios : ℚ) : ℝ))).sum :=
  ⟨List.sum_le_sum (fun r hr ↦ (eulerCenterRowCheck_sound (List.all_eq_true.mp h r hr)).2.1),
    List.sum_le_sum (fun r hr ↦ (eulerCenterRowCheck_sound (List.all_eq_true.mp h r hr)).2.2)⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
