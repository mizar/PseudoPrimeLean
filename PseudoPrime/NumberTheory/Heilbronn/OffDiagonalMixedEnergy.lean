/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.TripleCorrelationIdentities
public import PseudoPrime.NumberTheory.Heilbronn.MixedThirdEnergyBounds
public import PseudoPrime.Analysis.FiniteSupportedPairBounds
public import PseudoPrime.NumberTheory.Heilbronn.DyadicCorrelationBandEnvelope

/-! # Off-diagonal triple amplification controlled by mixed third energy -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Mixed third energy is the exact off-diagonal pair sum on S. Expand
the product filter and use a-b≠0 iff a≠b. This aligns the existing mixed
energy definition with the support bound for the Cauchy weight. -/
theorem mixedHeilbronnThirdEnergy_eq_pair_sum {p : ℕ} [Fact p.Prime] (S : Finset (ZMod (p ^ 2))) :
    mixedHeilbronnThirdEnergy p S =
      ∑ a ∈ S, ∑ b ∈ S, if a = b then 0 else Nat.card (cosetDifferenceAt p 0 0 (a - b)) ^ 2 := by
  simp only [mixedHeilbronnThirdEnergy, Finset.sum_filter, Finset.sum_product, sub_ne_zero, ite_not]

/-- Reversing an ordered difference preserves its Heilbronn correlation.
Apply negation symmetry. This reconciles the b-a edge from the triple
coordinate exchange with the a-b edge in mixed third energy. -/
theorem heilbronn_correlation_sub_rev {p : ℕ} [Fact p.Prime] (a b : ZMod (p ^ 2)) :
    Nat.card (cosetDifferenceAt p 0 0 (b - a)) = Nat.card (cosetDifferenceAt p 0 0 (a - b)) := by
  simpa only [neg_sub] using heilbronn_correlation_neg (a - b)

/-- The squared off-diagonal triple sum is bounded by the third energy times
the weighted pair correlation square sum.

Input: A prime `p` and a natural-number weight `g` on `ZMod (p^2)`.
Claim: The square of the off-diagonal triple sum is at most the third energy
times the pair sum weighted by `g(a)^2 g(b)^2` and the squared difference
correlation.
Proof: Apply finite triple-correlation Cauchy--Schwarz and rewrite the
diagonal-excluded square term as a sum over nonzero differences.
Role: Isolates the pair quantity to which the all-band Fourier bound applies.
-/
theorem weightedHeilbronnOffDiagonal_sq_le_weightedPair {p : ℕ} [Fact p.Prime]
    (g : ZMod (p ^ 2) → ℕ) :
    weightedHeilbronnOffDiagonal p g ^ 2 ≤
      heilbronnThirdEnergy p *
        (∑ a : ZMod (p ^ 2),
          ∑ b ∈ Finset.univ.filter (fun b ↦ a - b ≠ 0),
            g a ^ 2 * g b ^ 2 * Nat.card (cosetDifferenceAt p 0 0 (a - b)) ^ 2) := by
  classical
  have hc :=
    PseudoPrime.Analysis.finite_triple_correlation_weighted_square_le (heilbronnElements p)
      (fun a b ↦ if a = b then 0 else g a * g b * Nat.card (cosetDifferenceAt p 0 0 (b - a)))
  have hc' :
    weightedHeilbronnOffDiagonal p g ^ 2 ≤
      heilbronnThirdEnergy p *
        ∑ a : ZMod (p ^ 2),
          ∑ b : ZMod (p ^ 2),
            (if a = b then 0 else g a * g b * Nat.card (cosetDifferenceAt p 0 0 (b - a))) ^ 2 := by
    rw [weightedHeilbronnOffDiagonal_eq_correlation_sum]
    simpa only [heilbronnTripleCorrelation, ← heilbronn_correlation_eq_finiteDifferenceCorrelation,
      heilbronnThirdEnergy] using hc
  have hsum :
    (∑ a : ZMod (p ^ 2),
        ∑ b : ZMod (p ^ 2),
          (if a = b then 0 else g a * g b * Nat.card (cosetDifferenceAt p 0 0 (b - a))) ^ 2) =
      ∑ a : ZMod (p ^ 2),
        ∑ b ∈ Finset.univ.filter (fun b ↦ a - b ≠ 0),
          g a ^ 2 * g b ^ 2 * Nat.card (cosetDifferenceAt p 0 0 (a - b)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hab : a = b
    · subst b
      simp only [eq_self, ite_true, zero_pow (by decide : 2 ≠ 0), sub_self, ne_eq,
        not_true_eq_false, ite_false]
    · have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
      simp only [hab, ite_false]
      rw [heilbronn_correlation_sub_rev, ite_eq_left hne]
      ring_nf
  rw [hsum] at hc'
  exact hc'

/-- Combine triple-correlation Cauchy--Schwarz with the all-band Fourier
estimate for the squared weight.

Input: An odd prime `p` and a natural-number weight `g` on `ZMod (p^2)`.
Claim: The square of the off-diagonal triple sum is at most the third energy
times the weighted Fourier main term and band-free error for `g^2`.
Proof: Apply the preceding Cauchy--Schwarz estimate, then use the weighted
pair-correlation bound with weight `a ↦ g(a)^2`.
Role: Provides the weighted replacement for the support-and-maximum bound.
-/
theorem weightedHeilbronnOffDiagonal_sq_le_fourier_bound {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (g : ZMod (p ^ 2) → ℕ) :
    (weightedHeilbronnOffDiagonal p g : ℝ) ^ 2 ≤
      (heilbronnThirdEnergy p : ℝ) *
        (4 * heilbronnEnergy p * (weightedResidueMass (fun a ↦ g a ^ 2) : ℝ) ^ 2 / (p : ℝ) ^ 2 +
          65536 * (p : ℝ) * Real.sqrt (heilbronnEnergy p) *
            ∑ a : ZMod (p ^ 2), (g a ^ 2 : ℝ) ^ 2) := by
  have hc := weightedHeilbronnOffDiagonal_sq_le_weightedPair g
  have hcReal :
    (weightedHeilbronnOffDiagonal p g : ℝ) ^ 2 ≤
      (heilbronnThirdEnergy p : ℝ) *
        (↑(∑ a : ZMod (p ^ 2),
                ∑ b ∈ Finset.univ.filter (fun b ↦ a - b ≠ 0),
                  g a ^ 2 * g b ^ 2 * Nat.card (cosetDifferenceAt p 0 0 (a - b)) ^ 2 :
              ℕ) :
          ℝ) := by
    exact_mod_cast hc
  have hpair := weighted_pair_correlation_square_le hodd (fun a ↦ g a ^ 2)
  calc
    _ ≤
        (heilbronnThirdEnergy p : ℝ) *
          (↑(∑ a : ZMod (p ^ 2),
                  ∑ b ∈ Finset.univ.filter (fun b ↦ a - b ≠ 0),
                    g a ^ 2 * g b ^ 2 * Nat.card (cosetDifferenceAt p 0 0 (a - b)) ^ 2 :
                ℕ) :
            ℝ) :=
      hcReal
    _ ≤ _ := mul_le_mul_of_nonneg_left hpair (Nat.cast_nonneg _)
    _ = _ := by simp only [Nat.cast_pow]

/-- For a weight g supported on S and bounded by Δ, the actual off-diagonal
triple sum has square at most Δ⁴E₃E₃*(S,Γ). Rewrite it against C₃, apply
the proved square-sum identity, and bound its supported weight mass.
The triple-correlation and mixed-energy inputs are proved identities. -/
theorem weightedHeilbronnOffDiagonal_square_le {p : ℕ} [Fact p.Prime] (S : Finset (ZMod (p ^ 2)))
    (g : ZMod (p ^ 2) → ℕ) (Δ : ℕ) (hz : ∀ a, a ∉ S → g a = 0) (hg : ∀ a, g a ≤ Δ) :
    weightedHeilbronnOffDiagonal p g ^ 2 ≤
      Δ ^ 4 * heilbronnThirdEnergy p * mixedHeilbronnThirdEnergy p S := by
  classical
  have hc :=
    PseudoPrime.Analysis.finite_triple_correlation_weighted_square_le (heilbronnElements p)
      (fun a b ↦ if a = b then 0 else g a * g b * Nat.card (cosetDifferenceAt p 0 0 (b - a)))
  have hc' :
    weightedHeilbronnOffDiagonal p g ^ 2 ≤
      heilbronnThirdEnergy p *
        ∑ a : ZMod (p ^ 2),
          ∑ b : ZMod (p ^ 2),
            (if a = b then 0 else g a * g b * Nat.card (cosetDifferenceAt p 0 0 (b - a))) ^ 2 := by
    rw [weightedHeilbronnOffDiagonal_eq_correlation_sum]
    simpa only [heilbronnTripleCorrelation, ← heilbronn_correlation_eq_finiteDifferenceCorrelation,
      heilbronnThirdEnergy] using hc
  have hb :=
    PseudoPrime.Analysis.finite_supported_off_diagonal_square_le S g
      (fun a b ↦ Nat.card (cosetDifferenceAt p 0 0 (b - a))) Δ hz hg
  simp_rw [heilbronn_correlation_sub_rev] at hc' hb
  rw [← mixedHeilbronnThirdEnergy_eq_pair_sum] at hb
  exact (hc'.trans (Nat.mul_le_mul_left _ hb)).trans_eq (by ring)

/-- A selected correlation level bounded above by Δ satisfies the actual
off-diagonal triple estimate with its own finite support. Derive support
and height bounds from the level predicate, discharging both premises
of the general mixed-energy bound. -/
theorem level_weight_offDiagonal_square_le {p : ℕ} [Fact p.Prime] (P : ℕ → Prop) (Δ : ℕ)
    (hP : ∀ v, P v → v ≤ Δ) :
    weightedHeilbronnOffDiagonal p (heilbronnLevelWeight p P) ^ 2 ≤
      Δ ^ 4 * heilbronnThirdEnergy p *
        mixedHeilbronnThirdEnergy p (heilbronnCorrelationLevel p P) := by
  classical
  apply weightedHeilbronnOffDiagonal_square_le
  · intro a ha
    simp only [heilbronnLevelWeight, ha, ite_false]
  · intro a
    by_cases ha : a ∈ heilbronnCorrelationLevel p P
    · rw [heilbronnLevelWeight, ite_eq_left ha]
      exact hP _ ((mem_heilbronnCorrelationLevel P a).mp ha).2
    · rw [heilbronnLevelWeight, ite_eq_right ha]
      exact Nat.zero_le Δ

end PseudoPrime.NumberTheory.Heilbronn
