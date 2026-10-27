/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.InvariantDifferenceIncidence

/-! # Mixed third-energy contributions on correlation levels -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Sum of squared Heilbronn correlations over ordered S-pairs whose
nonzero difference belongs to the level selected by P. This is one band
of the mixed third energy; no bound or invariance is assumed in its definition. -/
noncomputable def mixedCorrelationLevelSum (p : ℕ) [Fact p.Prime] (S : Finset (ZMod (p ^ 2)))
    (P : ℕ → Prop) : ℕ :=
  ∑ z ∈ (S ×ˢ S).filter (fun z ↦ z.1 - z.2 ∈ heilbronnCorrelationLevel p P),
    Nat.card (cosetDifferenceAt p 0 0 (z.1 - z.2)) ^ 2

/-- If the level predicate forces correlation at most ω, its mixed energy
is at most ω² times the difference incidence. Bound each nonnegative
summand and sum the constant over the filtered pair set. This isolates
the Fourier incidence comparison from the purely arithmetic weight. -/
theorem mixedCorrelationLevelSum_le_incidence {p ω : ℕ} [Fact p.Prime] (S : Finset (ZMod (p ^ 2)))
    (P : ℕ → Prop) (hω : ∀ v, P v → v ≤ ω) :
    mixedCorrelationLevelSum p S P ≤
      ω ^ 2 * residueDifferenceIncidence S (heilbronnCorrelationLevel p P) := by
  unfold mixedCorrelationLevelSum residueDifferenceIncidence
  calc
    _ ≤ ∑ _z ∈ (S ×ˢ S).filter (fun z ↦ z.1 - z.2 ∈ heilbronnCorrelationLevel p P), ω ^ 2 := by
      apply Finset.sum_le_sum
      intro z hz
      have h := (mem_heilbronnCorrelationLevel P (z.1 - z.2)).mp (Finset.mem_filter.mp hz).2
      exact Nat.pow_le_pow_left (hω _ h.2) 2
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_comm]

/-- A positive correlation level bounded by ω satisfies the explicit mixed
third-energy estimate ω²(card(S)²card(Ω)/p²+M(Ω)card(S)). Use the proved
Fourier envelope for the actual invariant level Ω. The only predicate
conditions are excluding zero and bounding its correlation height. -/
theorem mixedCorrelationLevelSum_le_fourier {p ω : ℕ} [Fact p.Prime] (S : Finset (ZMod (p ^ 2)))
    (P : ℕ → Prop) (hP : ¬P 0) (hω : ∀ v, P v → v ≤ ω) :
    (mixedCorrelationLevelSum p S P : ℝ) ≤
      (ω : ℝ) ^ 2 *
        ((S.card : ℝ) ^ 2 * (heilbronnCorrelationLevel p P).card / (p : ℝ) ^ 2 +
          invariantFourierEnvelope p (heilbronnCorrelationLevel p P) * S.card) := by
  have hnat := mixedCorrelationLevelSum_le_incidence S P hω
  have hreal :
    (mixedCorrelationLevelSum p S P : ℝ) ≤
      (ω : ℝ) ^ 2 * (residueDifferenceIncidence S (heilbronnCorrelationLevel p P) : ℝ) := by
    exact_mod_cast hnat
  exact
    hreal.trans
      (mul_le_mul_of_nonneg_left (residueDifferenceIncidence_le_correlation_level S P hP)
        (sq_nonneg _))

end PseudoPrime.NumberTheory.Heilbronn
