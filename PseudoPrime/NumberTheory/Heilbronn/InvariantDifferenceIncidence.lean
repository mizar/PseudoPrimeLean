/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.CorrelationLevels
public import PseudoPrime.NumberTheory.Heilbronn.DifferenceIncidenceBounds

/-! # Difference incidences on invariant Heilbronn correlation levels -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Fourth-root Fourier envelope sqrt(sqrt(p² E card(Q)³))/(p-1).
For a prime modulus this nonnegative value bounds every nonzero Fourier
coefficient of an invariant unit set. It retains exact finite constants. -/
noncomputable def invariantFourierEnvelope (p : ℕ) [Fact p.Prime] (Q : Finset (ZMod (p ^ 2))) : ℝ :=
  Real.sqrt (Real.sqrt ((p : ℝ) ^ 2 * heilbronnEnergy p * (Q.card : ℝ) ^ 3)) / (p - 1 : ℕ)

/-- The invariant Fourier envelope is nonnegative, including an empty set.
Both square roots and the natural denominator are nonnegative. This sign
permits use of the generic finite difference-incidence comparison. -/
theorem invariantFourierEnvelope_nonneg {p : ℕ} [Fact p.Prime] (Q : Finset (ZMod (p ^ 2))) :
    0 ≤ invariantFourierEnvelope p Q := by exact div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)

/-- Every nonzero Fourier coefficient of an invariant unit set is bounded
by its explicit fourth-root envelope. Compare fourth powers and divide by
the positive p-1. The underlying fourth-power estimate includes nonunits. -/
theorem norm_residueCharacterSum_le_invariantFourierEnvelope {p : ℕ} [Fact p.Prime]
    (Q : Finset (ZMod (p ^ 2))) (hinv : IsHeilbronnInvariant Q) (hQ : ∀ x ∈ Q, IsUnit x)
    {l : ZMod (p ^ 2)} (hl : l ≠ 0) : ‖residueCharacterSum Q l‖ ≤ invariantFourierEnvelope p Q := by
  have ht : (0 : ℝ) < (p - 1 : ℕ) :=
    Nat.cast_pos.mpr (Nat.sub_pos_of_lt (Nat.Prime.one_lt Fact.out))
  have hK : 0 ≤ (p : ℝ) ^ 2 * heilbronnEnergy p * (Q.card : ℝ) ^ 3 :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) (pow_nonneg (Nat.cast_nonneg _) 3)
  have he :
    (Real.sqrt (Real.sqrt ((p : ℝ) ^ 2 * heilbronnEnergy p * (Q.card : ℝ) ^ 3))) ^ 4 =
      (p : ℝ) ^ 2 * heilbronnEnergy p * (Q.card : ℝ) ^ 3 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hK]
  apply (le_div_iff₀ ht).mpr
  apply le_of_pow_le_pow_left₀ (by decide : 4 ≠ 0) (Real.sqrt_nonneg _)
  rw [he, mul_pow]
  exact (mul_comm _ _).trans_le (invariant_character_fourth_le_energy Q hinv hQ hl)

/-- An arbitrary finite set S has at most card(S)²card(Q)/p² plus
card(S) times the Fourier envelope differences in an invariant unit set Q.
Apply the generic incidence bound with the proved envelope, so no additional
analytic hypothesis is introduced. -/
theorem residueDifferenceIncidence_le_invariant {p : ℕ} [Fact p.Prime] (S Q : Finset (ZMod (p ^ 2)))
    (hinv : IsHeilbronnInvariant Q) (hQ : ∀ x ∈ Q, IsUnit x) :
    (residueDifferenceIncidence S Q : ℝ) ≤
      (S.card : ℝ) ^ 2 * Q.card / (p : ℝ) ^ 2 + invariantFourierEnvelope p Q * S.card := by
  have h :=
    residueDifferenceIncidence_le_of_fourier_bound S Q (invariantFourierEnvelope_nonneg Q)
      (fun l hl ↦ norm_residueCharacterSum_le_invariantFourierEnvelope Q hinv hQ hl)
  simpa only [Nat.cast_pow] using h

/-- Every correlation level excluding correlation zero satisfies the
explicit difference-incidence estimate for arbitrary S. Substitute its
proved invariance and unit support. This is the Fourier contribution to
the mixed third energy on one dyadic band. -/
theorem residueDifferenceIncidence_le_correlation_level {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod (p ^ 2))) (P : ℕ → Prop) (hP : ¬P 0) :
    (residueDifferenceIncidence S (heilbronnCorrelationLevel p P) : ℝ) ≤
      (S.card : ℝ) ^ 2 * (heilbronnCorrelationLevel p P).card / (p : ℝ) ^ 2 +
        invariantFourierEnvelope p (heilbronnCorrelationLevel p P) * S.card := by
  exact
    residueDifferenceIncidence_le_invariant S _ (heilbronnCorrelationLevel_invariant P)
      (heilbronnCorrelationLevel_units P hP)

end PseudoPrime.NumberTheory.Heilbronn
