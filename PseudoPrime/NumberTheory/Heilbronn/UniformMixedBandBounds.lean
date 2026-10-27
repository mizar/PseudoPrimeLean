/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.FullCorrelationTail
public import PseudoPrime.NumberTheory.Heilbronn.MixedCorrelationLevels
public import PseudoPrime.Analysis.MixedFourierBandBudget

/-! # Uniform mixed-energy estimates for every dyadic correlation band -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- A positive correlation level above K satisfies both the quadratic
energy budget and cubic tail budget. Apply the general tail estimates to
its proved unit support. These complementary inequalities eliminate K
from the Fourier error after combination. -/
theorem correlation_level_tail_budgets {p K : ℕ} [Fact p.Prime] (hodd : Odd p) (P : ℕ → Prop)
    (hP : ¬P 0) (hK : ∀ v, P v → K ≤ v) :
    (heilbronnCorrelationLevel p P).card * K ^ 2 ≤ heilbronnEnergy p ∧
      (heilbronnCorrelationLevel p P).card * K ^ 3 ≤ 262144 * p ^ 3 := by
  have hlow : ∀ x ∈ heilbronnCorrelationLevel p P, K ≤ Nat.card (cosetDifferenceAt p 0 0 x) :=
    fun x hx ↦ hK _ ((mem_heilbronnCorrelationLevel P x).mp hx).2
  exact
    ⟨card_mul_sq_le_of_correlation_ge _ hlow,
      card_mul_cube_le_of_unit_correlation_ge hodd _ (heilbronnCorrelationLevel_units P hP) hlow⟩

/-- For every positive correlation level above K, its Fourier envelope
 multiplied by 4K² is at most 4096p sqrt(E). Combine the quadratic and cubic
budgets with p≤2(p-1). The bound is independent of the band height. -/
theorem correlation_level_fourier_error_le {p K : ℕ} [Fact p.Prime] (hodd : Odd p) (P : ℕ → Prop)
    (hP : ¬P 0) (hK : ∀ v, P v → K ≤ v) :
    4 * (K : ℝ) ^ 2 * invariantFourierEnvelope p (heilbronnCorrelationLevel p P) ≤
      4096 * (p : ℝ) * Real.sqrt (heilbronnEnergy p) := by
  have hb := correlation_level_tail_budgets hodd P hP hK
  have hquad : ((heilbronnCorrelationLevel p P).card : ℝ) * (K : ℝ) ^ 2 ≤ heilbronnEnergy p := by
    exact_mod_cast hb.1
  have hcube :
    ((heilbronnCorrelationLevel p P).card : ℝ) * (K : ℝ) ^ 3 ≤ (262144 : ℝ) * (p : ℝ) ^ 3 := by
    exact_mod_cast hb.2
  have ht : (0 : ℝ) < (p - 1 : ℕ) :=
    Nat.cast_pos.mpr (Nat.sub_pos_of_lt (Nat.Prime.one_lt Fact.out))
  have hpt : (p : ℝ) ≤ 2 * (p - 1 : ℕ) := by
    rw [Nat.cast_sub (Nat.one_le_of_lt (Nat.Prime.one_lt Fact.out)), Nat.cast_one]
    have hp : (2 : ℝ) ≤ p := Nat.cast_le.mpr (Nat.Prime.two_le Fact.out)
    linarith only [hp]
  have h :=
    Analysis.mixed_band_fourier_error_le (Nat.cast_nonneg _) (Nat.cast_nonneg K) (Nat.cast_nonneg _)
      (by norm_num only : (0 : ℝ) ≤ 262144) (Nat.cast_nonneg p) ht hpt hquad hcube
  have hs : Real.sqrt (262144 : ℝ) = 512 := by
    rw [show (262144 : ℝ) = 512 ^ 2 by norm_num only,
      Real.sqrt_sq (by norm_num only : (0 : ℝ) ≤ 512)]
  norm_num only [hs] at h
  exact h

/-- Any correlation band K≤r≤2K with K>0 has mixed third-energy contribution
at most 4 card(S)² E/p²+4096 card(S)p sqrt(E). Bound the incidence main term
by the quadratic tail and the Fourier term by the uniform error estimate.
This is the band-independent comparison summed in the dyadic argument. -/
theorem mixedCorrelationLevelSum_le_uniform {p K : ℕ} [Fact p.Prime] (hodd : Odd p)
    (S : Finset (ZMod (p ^ 2))) (P : ℕ → Prop) (hK : 0 < K) (hlow : ∀ v, P v → K ≤ v)
    (hhigh : ∀ v, P v → v ≤ 2 * K) :
    (mixedCorrelationLevelSum p S P : ℝ) ≤
      4 * (S.card : ℝ) ^ 2 * heilbronnEnergy p / (p : ℝ) ^ 2 +
        4096 * S.card * p * Real.sqrt (heilbronnEnergy p) := by
  have hP : ¬P 0 := fun h ↦ (Nat.not_le_of_lt hK) (hlow 0 h)
  have hbase := mixedCorrelationLevelSum_le_fourier S P hP hhigh
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, mul_pow] at hbase
  have hb := correlation_level_tail_budgets hodd P hP hlow
  have hquad : ((heilbronnCorrelationLevel p P).card : ℝ) * (K : ℝ) ^ 2 ≤ heilbronnEnergy p := by
    exact_mod_cast hb.1
  have hmain :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hquad
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) (sq_nonneg (S.card : ℝ))))
      (sq_nonneg (p : ℝ))
  have herr :=
    mul_le_mul_of_nonneg_right (correlation_level_fourier_error_le hodd P hP hlow)
      (Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)
  calc
    _ ≤ _ := hbase
    _ =
        (4 * (S.card : ℝ) ^ 2 * (((heilbronnCorrelationLevel p P).card : ℝ) * (K : ℝ) ^ 2)) /
            (p : ℝ) ^ 2 +
          (4 * (K : ℝ) ^ 2 * invariantFourierEnvelope p (heilbronnCorrelationLevel p P)) * S.card :=
      by ring
    _ ≤
        4 * (S.card : ℝ) ^ 2 * heilbronnEnergy p / (p : ℝ) ^ 2 +
          (4096 * (p : ℝ) * Real.sqrt (heilbronnEnergy p)) * S.card :=
      add_le_add hmain herr
    _ = _ := by ring

end PseudoPrime.NumberTheory.Heilbronn
