/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.ExplicitTripleBounds
public import PseudoPrime.Analysis.FiniteThirdMomentTruncation

/-! # Retaining Heilbronn energy below a third-moment cutoff -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Full additive energy is at most its third moment, since all counts
are natural numbers. Apply the generic finite moment comparison. This
controls rounding of the E-dependent integer height cutoff. -/
theorem heilbronnEnergy_le_thirdEnergy {p : ℕ} [Fact p.Prime] :
    heilbronnEnergy p ≤ heilbronnThirdEnergy p := by
  exact
    PseudoPrime.Analysis.finite_square_mass_le_cube_mass Finset.univ
      (fun a ↦ Nat.card (cosetDifferenceAt p 0 0 a))

/-- The nonzero energy is exactly partitioned at height M into the lower
and upper levels. Expand both level filters and apply the finite predicate
partition identity. Zero differences remain separated throughout. -/
theorem heilbronnLevelEnergy_cutoff_partition {p : ℕ} [Fact p.Prime] (M : ℕ) :
    heilbronnLevelEnergy p (fun v ↦ v ≤ M) + heilbronnLevelEnergy p (fun v ↦ M < v) =
      heilbronnLevelEnergy p (fun _ ↦ True) := by
  classical
  have hlo :
    (heilbronnCorrelationLevel p (fun _ ↦ True)).filter
        (fun a ↦ Nat.card (cosetDifferenceAt p 0 0 a) ≤ M) =
      heilbronnCorrelationLevel p (fun v ↦ v ≤ M) := by
    ext a
    simp only [Finset.mem_filter, mem_heilbronnCorrelationLevel, and_true]
  have hhi :
    (heilbronnCorrelationLevel p (fun _ ↦ True)).filter
        (fun a ↦ ¬Nat.card (cosetDifferenceAt p 0 0 a) ≤ M) =
      heilbronnCorrelationLevel p (fun v ↦ M < v) := by
    ext a
    simp only [Finset.mem_filter, mem_heilbronnCorrelationLevel, and_true, not_le]
  have h :=
    Finset.sum_filter_add_sum_filter_not (heilbronnCorrelationLevel p (fun _ ↦ True))
      (fun a ↦ Nat.card (cosetDifferenceAt p 0 0 a) ≤ M)
      (fun a ↦ Nat.card (cosetDifferenceAt p 0 0 a) ^ 2)
  rw [hlo, hhi] at h
  exact h

/-- Upper nonzero level energy times the cutoff is at most the full third
moment. Apply the generic upper-tail inequality and enlarge the third
moment sum to all residues. This justifies removing large correlations. -/
theorem heilbronnLevelEnergy_upper_tail_mul_le {p : ℕ} [Fact p.Prime] (M : ℕ) :
    M * heilbronnLevelEnergy p (fun v ↦ M < v) ≤ heilbronnThirdEnergy p := by
  classical
  have h :=
    PseudoPrime.Analysis.finite_upper_square_tail_mul_le_cube_mass
      (heilbronnCorrelationLevel p (fun _ ↦ True)) (fun a ↦ Nat.card (cosetDifferenceAt p 0 0 a)) M
  have he :
    (heilbronnCorrelationLevel p (fun _ ↦ True)).filter
        (fun a ↦ M < Nat.card (cosetDifferenceAt p 0 0 a)) =
      heilbronnCorrelationLevel p (fun v ↦ M < v) := by
    ext a
    simp only [Finset.mem_filter, mem_heilbronnCorrelationLevel, and_true]
  rw [he] at h
  exact h.trans (Finset.sum_le_sum_of_subset (Finset.subset_univ _))

/-- If the zero-difference energy is at most E/4, an integer height cutoff
M retains at least E/2 in the nonzero lower level and satisfies 4E₃≤ME≤5E₃.
Use the exact energy partition and proved third-moment tail inequality.
No large-correlation counting estimate is assumed. -/
theorem exists_heilbronn_energy_retaining_cutoff {p : ℕ} [Fact p.Prime]
    (hd : 4 * (p - 1) ^ 2 ≤ heilbronnEnergy p) :
    ∃ M : ℕ,
      0 < M ∧
        4 * heilbronnThirdEnergy p ≤ M * heilbronnEnergy p ∧
        M * heilbronnEnergy p ≤ 5 * heilbronnThirdEnergy p ∧
        heilbronnEnergy p ≤ 2 * heilbronnLevelEnergy p (fun v ↦ v ≤ M) := by
  obtain ⟨M, hM, hlo, hhi⟩ :=
    PseudoPrime.Analysis.exists_third_moment_cutoff
      (Nat.zero_lt_one.trans_le (one_le_heilbronnEnergy (p := p)))
      (heilbronnEnergy_le_thirdEnergy (p := p))
  refine ⟨M, hM, hlo, hhi, ?_⟩
  have he := heilbronnEnergy_eq_diagonal_add_level (p := p)
  rw [← heilbronnLevelEnergy_cutoff_partition M] at he
  apply
    PseudoPrime.Analysis.half_energy_le_of_third_moment_cutoff (by simpa only [add_assoc] using he)
      hd (heilbronnLevelEnergy_upper_tail_mul_le M) hlo hM

end PseudoPrime.NumberTheory.Heilbronn
