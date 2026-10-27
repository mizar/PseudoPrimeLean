/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.HeilbronnFrequencySquareMass
public import PseudoPrime.NumberTheory.Heilbronn.HeilbronnFourierMoments
public import PseudoPrime.NumberTheory.Heilbronn.WeightedFourthPower

/-! # Short Heilbronn Fourier sums controlled by the proved energy budget -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Apply weighted Cauchy-Schwarz twice to actual frequency multiplicities.
The exact mass, square mass and character fourth moment give the displayed bound. -/
theorem weighted_heilbronn_fourth_power_le {p H : ℕ} [Fact p.Prime] :
    (∑ w : ZMod (p ^ 2), (heilbronnFrequencyMultiplicity p H w : ℝ) * ‖heilbronnCharacterSum p w‖) ^
        4 ≤
      ((2 * H * (p - 1) : ℕ) : ℝ) ^ 2 * (((p - 1) * boundedCongruenceCount p H : ℕ) : ℝ) *
        (((p ^ 2 : ℕ) : ℝ) * heilbronnEnergy p) := by
  have h :=
    weighted_fourth_power_le (Finset.univ : Finset (ZMod (p ^ 2)))
      (fun w ↦ (heilbronnFrequencyMultiplicity p H w : ℝ)) (fun w ↦ ‖heilbronnCharacterSum p w‖)
      (fun w hw ↦ Nat.cast_nonneg _)
  have hmass :
    (∑ w : ZMod (p ^ 2), (heilbronnFrequencyMultiplicity p H w : ℝ)) =
      ((2 * H * (p - 1) : ℕ) : ℝ) := by
    exact_mod_cast (sum_heilbronnFrequencyMultiplicity (p := p) (H := H))
  have hsquare :
    (∑ w : ZMod (p ^ 2), (heilbronnFrequencyMultiplicity p H w : ℝ) ^ 2) =
      (((p - 1) * boundedCongruenceCount p H : ℕ) : ℝ) := by
    exact_mod_cast (sum_heilbronnFrequencyMultiplicity_sq (p := p) (H := H))
  rw [hmass, hsquare, heilbronn_character_fourth_moment] at h
  exact h

/-- The coset character sum equals the sum over the subgroup of units,
by the proved bijection between the subgroup and the zero-shift coset. -/
theorem heilbronnCharacterSum_eq_subgroup_sum {p : ℕ} [Fact p.Prime] (w : ZMod (p ^ 2)) :
    heilbronnCharacterSum p w =
      (by
        classical
          exact ∑ u : heilbronnSubgroup p, ZMod.stdAddChar (w * (u.val : ZMod (p ^ 2)))) := by
  classical
  rw [heilbronnCharacterSum, Finset.sum_subtype _ (fun x ↦ Set.mem_toFinset) _]
  exact
    (Fintype.sum_equiv (Equiv.ofBijective _ heilbronnSubgroupToCoset_bijective) _ _
        (fun u ↦ rfl)).symm

/-- Multiplying a frequency by a Heilbronn subgroup element leaves its character sum
unchanged. Left multiplication permutes the subgroup elements in the sum. -/
theorem heilbronnCharacterSum_mul_subgroup {p : ℕ} [Fact p.Prime] (u : heilbronnSubgroup p)
    (w : ZMod (p ^ 2)) :
    heilbronnCharacterSum p ((u.val : ZMod (p ^ 2)) * w) = heilbronnCharacterSum p w := by
  classical
  rw [heilbronnCharacterSum_eq_subgroup_sum, heilbronnCharacterSum_eq_subgroup_sum]
  apply Fintype.sum_equiv (Equiv.mulLeft u)
  intro v
  congr 1
  change (u.val : ZMod (p ^ 2)) * w * (v.val : ZMod (p ^ 2)) = w * ((u * v).val : ZMod (p ^ 2))
  rw [Subgroup.coe_mul, Units.val_mul]
  ring

/-- The multiplicity-weighted Fourier norm sum is p-1 times the raw short norm sum.
Partition by residue frequency, then use subgroup invariance. -/
theorem weighted_heilbronn_sum_eq_short_sum {p H : ℕ} [Fact p.Prime] :
    (∑ w : ZMod (p ^ 2), (heilbronnFrequencyMultiplicity p H w : ℝ) * ‖heilbronnCharacterSum p w‖) =
      ((p - 1 : ℕ) : ℝ) *
        ∑ z ∈ signedShortIntegers H, ‖heilbronnCharacterSum p (z : ZMod (p ^ 2))‖ := by
  classical
  let f := fun z : heilbronnSubgroup p × ℤ ↦ (z.1.val : ZMod (p ^ 2)) * (z.2 : ZMod (p ^ 2))
  have hf (w : ZMod (p ^ 2)) :
    (heilbronnFrequencyMultiplicity p H w : ℝ) * ‖heilbronnCharacterSum p w‖ =
      ∑ z ∈ (heilbronnFrequencyPairs p H).filter (fun z ↦ f z = w),
        ‖heilbronnCharacterSum p (f z)‖ := by
    rw [heilbronnFrequencyMultiplicity, ← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_congr rfl
    intro z hz
    have he : f z = w := (Finset.mem_filter.mp hz).2
    rw [he]
  simp only [hf]
  rw [Finset.sum_fiberwise, heilbronnFrequencyPairs, Finset.sum_product]
  simp only [f, heilbronnCharacterSum_mul_subgroup, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Nat.card_eq_fintype_card, card_heilbronnSubgroup]

/-- For any prime p and height H, the short Fourier norm sum has fourth power at most
8H^2*p*E_p*N_p(H). Cancel the positive subgroup order and use p<=2(p-1). -/
theorem short_heilbronn_fourth_power_le {p H : ℕ} [Fact p.Prime] :
    (∑ z ∈ signedShortIntegers H, ‖heilbronnCharacterSum p (z : ZMod (p ^ 2))‖) ^ 4 ≤
      8 * (H : ℝ) ^ 2 * (p : ℝ) * heilbronnEnergy p * (boundedCongruenceCount p H : ℝ) := by
  let A := ∑ z ∈ signedShortIntegers H, ‖heilbronnCharacterSum p (z : ZMod (p ^ 2))‖
  let c : ℝ := (p - 1 : ℕ)
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hc : 0 < c := Nat.cast_pos.mpr (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
  have he : (p : ℝ) ≤ 2 * c := by
    dsimp only [c]
    rw [Nat.cast_sub (Nat.one_le_of_lt (Fact.out : p.Prime).one_lt), Nat.cast_one]
    have hpR : (2 : ℝ) ≤ p := Nat.cast_le.mpr hp
    linarith only [hpR]
  have h := weighted_heilbronn_fourth_power_le (p := p) (H := H)
  rw [weighted_heilbronn_sum_eq_short_sum] at h
  have hh :
    c ^ 3 * (c * A ^ 4) ≤
      c ^ 3 *
        (4 * (H : ℝ) ^ 2 * (p : ℝ) ^ 2 * heilbronnEnergy p * (boundedCongruenceCount p H : ℝ)) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] at h
    convert h using 1 <;> dsimp only [c, A] <;> ring
  have hcancel := (mul_le_mul_iff_right₀ (pow_pos hc 3)).mp hh
  have hn : 0 ≤ 4 * (H : ℝ) ^ 2 * (p : ℝ) * heilbronnEnergy p * (boundedCongruenceCount p H : ℝ) :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num only) (sq_nonneg (H : ℝ))) (Nat.cast_nonneg p))
        (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  have hm := mul_le_mul_of_nonneg_left he hn
  apply (mul_le_mul_iff_right₀ hc).mp
  change c * A ^ 4 ≤ _
  calc
    _ ≤ 4 * (H : ℝ) ^ 2 * (p : ℝ) ^ 2 * heilbronnEnergy p * (boundedCongruenceCount p H : ℝ) :=
      hcancel
    _ ≤ _ := by nlinarith only [hm]

/-- A strict weighted energy budget gives a strict short Fourier fourth-power bound.
For H>0 multiply the budget by 8H^2 and combine it with the unconditional norm bound. -/
theorem short_heilbronn_fourth_power_lt_of_energy_budget {p H M k : ℕ} [Fact p.Prime] (hH : 0 < H)
    (hbudget : (M * p) * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2) :
    (M : ℝ) * (∑ z ∈ signedShortIntegers H, ‖heilbronnCharacterSum p (z : ZMod (p ^ 2))‖) ^ 4 <
      8 * (H : ℝ) ^ 2 * (k : ℝ) ^ 2 := by
  have hb : ((M : ℝ) * p) * heilbronnEnergy p * (boundedCongruenceCount p H : ℝ) < (k : ℝ) ^ 2 := by
    exact_mod_cast hbudget
  have h :=
    mul_le_mul_of_nonneg_left (short_heilbronn_fourth_power_le (p := p) (H := H))
      (Nat.cast_nonneg M)
  have hscale : 0 < 8 * (H : ℝ) ^ 2 := mul_pos (by norm_num only) (pow_pos (Nat.cast_pos.mpr hH) 2)
  have hs := mul_lt_mul_of_pos_left hb hscale
  nlinarith only [h, hs]

/-- For any fixed weight M and r>=16185, all sufficiently large odd primes admit
a cutoff of exponent 28/15 with a strict short Fourier budget. The threshold comes
from the proved symbolic energy coefficient; no finite search is performed. -/
theorem exists_uniform_short_fourier_budget {M r : ℕ} (hr : 16185 ≤ r) :
    ∃ P : ℕ,
      ∀ (p : ℕ) [Fact p.Prime],
        Odd p →
          P ≤ p →
          ∃ k : ℕ,
            0 < k ∧
              k ≤ p ^ 2 ∧
              p ^ 28 ≤ k ^ 15 ∧
              k ^ 15 ≤ 32768 * p ^ 28 ∧
              (M : ℝ) *
                  (∑ z ∈ signedShortIntegers (p ^ 2 / k),
                      ‖heilbronnCharacterSum p (z : ZMod (p ^ 2))‖) ^
                    4 <
                8 * ((p ^ 2 / k : ℕ) : ℝ) ^ 2 * (k : ℝ) ^ 2 := by
  obtain ⟨P, hP⟩ := exists_uniform_weighted_short_congruence_energy_budget (M := M) hr
  refine ⟨P, ?_⟩
  intro p hp hodd hlarge
  obtain ⟨k, hk, hkp, hlo, hhi, hb⟩ := hP p hodd hlarge
  refine ⟨k, hk, hkp, hlo, hhi, ?_⟩
  exact short_heilbronn_fourth_power_lt_of_energy_budget (Nat.div_pos hkp hk) hb

end PseudoPrime.NumberTheory.Heilbronn
