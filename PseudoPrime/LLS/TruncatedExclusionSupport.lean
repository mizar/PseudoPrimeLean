/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TruncatedCubicExclusion

/-! # Replace localized exclusion support by a smaller modulus -/

public section

namespace PseudoPrime.LLS.PaperStatements

/-- If every excluded prime below X either divides a nonzero modulus D or
has character value one, the localized cost is bounded by the full cost at D.
Remove the zero summands outside D and enlarge the remaining nonnegative sum.
This separates fixed ramified support from arbitrarily large added factors. -/
theorem truncatedCharacterExclusionCost_le_of_prime_coverage {f M D : ℕ}
    (χ : DirichletCharacter ℂ f) (hD : D ≠ 0) {X : ℝ}
    (hcover : ∀ p : ℕ, p.Prime → p ∣ M → (p : ℝ) ≤ X → p ∣ D ∨ χ p = 1) :
    truncatedCharacterExclusionCost χ M X ≤
      AnalyticNumberTheory.Arithmetic.characterExclusionCost χ D := by
  classical
  let S := M.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) ≤ X)
  let w := fun p : ℕ ↦ (1 - (χ p).re) * Real.log p
  have he : ∑ p ∈ S ∩ D.primeFactors, w p = ∑ p ∈ S, w p := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro p hp hnot
    have hm := Finset.mem_filter.mp hp
    have hprime := Nat.prime_of_mem_primeFactors hm.1
    rcases hcover p hprime (Nat.dvd_of_mem_primeFactors hm.1) hm.2 with hd | hv
    · exact (hnot (Finset.mem_inter.mpr ⟨hp, Nat.mem_primeFactors.mpr ⟨hprime, hd, hD⟩⟩)).elim
    · simp only [w, hv, Complex.one_re, sub_self, zero_mul]
  change (∑ p ∈ S, w p) ≤ ∑ p ∈ D.primeFactors, w p
  rw [← he]
  apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
  intro p _ _
  exact
    mul_nonneg (AnalyticNumberTheory.Arithmetic.character_defect_nonneg χ p)
      (Real.log_natCast_nonneg p)

end PseudoPrime.LLS.PaperStatements
