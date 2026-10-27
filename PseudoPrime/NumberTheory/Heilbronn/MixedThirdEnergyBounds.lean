/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.UniformMixedBandBounds
public import PseudoPrime.Analysis.FiniteDyadicCover

/-! # Explicit mixed third-energy bound for arbitrary finite residue sets -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Mixed third energy E₃*(S,Γ): sum rΓ(x-y)² over ordered S-pairs with
nonzero difference. Grouping the pairs by difference gives the conventional
sum of rS(a)rΓ(a)² over nonzero a. All quantities here are finite counts. -/
noncomputable def mixedHeilbronnThirdEnergy (p : ℕ) [Fact p.Prime] (S : Finset (ZMod (p ^ 2))) :
    ℕ :=
  ∑ z ∈ (S ×ˢ S).filter (fun z ↦ z.1 - z.2 ≠ 0), Nat.card (cosetDifferenceAt p 0 0 (z.1 - z.2)) ^ 2

/-- The full mixed energy is covered by log₂(p)+1 dyadic correlation bands.
Apply the generic finite dyadic cover to the nonzero S-pair differences;
each correlation is at most p. No sample or range enumeration is involved. -/
theorem mixedHeilbronnThirdEnergy_le_sum_bands {p : ℕ} [Fact p.Prime] (S : Finset (ZMod (p ^ 2))) :
    mixedHeilbronnThirdEnergy p S ≤
      ∑ j ∈ Finset.range (Nat.log2 p + 1),
        mixedCorrelationLevelSum p S (fun v ↦ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j) := by
  have h :=
    Analysis.sum_squares_le_sum_dyadic_bands ((S ×ˢ S).filter (fun z ↦ z.1 - z.2 ≠ 0))
      (fun z ↦ Nat.card (cosetDifferenceAt p 0 0 (z.1 - z.2))) p
      (fun z _ ↦ (card_cosetDifferenceAt_le 0 0 (z.1 - z.2)).trans (Nat.sub_le p 1))
  apply h.trans_eq
  apply Finset.sum_congr rfl
  intro j _
  unfold mixedCorrelationLevelSum
  congr 1
  ext z
  simp only [Finset.mem_filter, mem_heilbronnCorrelationLevel, and_assoc]

/-- For odd prime p and arbitrary S, mixed third energy is at most
(log₂(p)+1)(4card(S)²E/p²+4096card(S)p sqrt(E)). Every dyadic band has the
same bound, so sum the finite covering. This supplies the quantitative
mixed-energy input for the 32/13 Heilbronn energy amplification. -/
theorem mixedHeilbronnThirdEnergy_le_explicit {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (S : Finset (ZMod (p ^ 2))) :
    (mixedHeilbronnThirdEnergy p S : ℝ) ≤
      (Nat.log2 p + 1 : ℕ) *
        (4 * (S.card : ℝ) ^ 2 * heilbronnEnergy p / (p : ℝ) ^ 2 +
          4096 * S.card * p * Real.sqrt (heilbronnEnergy p)) := by
  have hn := mixedHeilbronnThirdEnergy_le_sum_bands S
  have hr :
    (mixedHeilbronnThirdEnergy p S : ℝ) ≤
      ∑ j ∈ Finset.range (Nat.log2 p + 1),
        (mixedCorrelationLevelSum p S (fun v ↦ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j) : ℝ) := by
    exact_mod_cast hn
  calc
    _ ≤ _ := hr
    _ ≤
        ∑ _j ∈ Finset.range (Nat.log2 p + 1),
          (4 * (S.card : ℝ) ^ 2 * heilbronnEnergy p / (p : ℝ) ^ 2 +
            4096 * S.card * p * Real.sqrt (heilbronnEnergy p)) :=
      by
      apply Finset.sum_le_sum
      intro j _
      exact
        mixedCorrelationLevelSum_le_uniform hodd S _ (pow_pos (by decide : 0 < 2) j) (fun _ h ↦ h.1)
          (fun _ h ↦ h.2)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]

end PseudoPrime.NumberTheory.Heilbronn
