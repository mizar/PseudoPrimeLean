/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.SubquadraticEnergyBudget
public import PseudoPrime.NumberTheory.Heilbronn.FiniteCharacterMoments

/-! # Fourier fourth moments from the proved Heilbronn energy bound -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- The positive-phase standard character sum over the zero-shift Heilbronn coset.
Input p is prime and l a residue modulo p^2. Summing the p-1 subgroup elements gives
the Fourier sum used in the interval distribution comparison. -/
noncomputable def heilbronnCharacterSum (p : ℕ) [Fact p.Prime] (l : ZMod (p ^ 2)) : ℂ := by
  classical exact ∑ x ∈ (shiftedTeichCoset p 0).toFinset, ZMod.stdAddChar (l * x)

/-- For prime p, the sum of fourth powers of the character-sum norms equals p^2*heilbronnEnergy.
Identify the generic equal-difference quadruple filter with the existing energy quadruple type. -/
theorem heilbronn_character_fourth_moment {p : ℕ} [Fact p.Prime] :
    (∑ l : ZMod (p ^ 2), ‖heilbronnCharacterSum p l‖ ^ 4) =
      ((p ^ 2 : ℕ) : ℝ) * heilbronnEnergy p := by
  classical
  let A := (shiftedTeichCoset p 0).toFinset
  have he :
    (((A ×ˢ A) ×ˢ (A ×ˢ A)).filter (fun z ↦ z.1.1 - z.1.2 = z.2.1 - z.2.2)) =
      (equalDifferenceQuadruples p).toFinset := by
    ext z
    rw [Set.mem_toFinset]
    simp only [A, Finset.mem_filter, Finset.mem_product, Set.mem_toFinset,
      equalDifferenceQuadruples, Set.mem_ofPred_eq, and_assoc]
  have hc :
    (((A ×ˢ A) ×ˢ (A ×ˢ A)).filter (fun z ↦ z.1.1 - z.1.2 = z.2.1 - z.2.2)).card =
      heilbronnEnergy p := by
    rw [he, Set.toFinset_card, heilbronnEnergy_eq_card_quadruples, Nat.card_eq_fintype_card]
  have h := char_sum_fourth_moment A (fun x ↦ x)
  rw [hc] at h
  simpa only [heilbronnCharacterSum, A] using h

/-- For odd prime p, the square of the fourth Fourier moment is at most 18874370*p^9.
Combine the exact moment identity with the proved uniform energy-square bound. -/
theorem heilbronn_character_fourth_moment_square_le {p : ℕ} [Fact p.Prime] (hodd : Odd p) :
    (∑ l : ZMod (p ^ 2), ‖heilbronnCharacterSum p l‖ ^ 4) ^ 2 ≤ (18874370 : ℝ) * (p : ℝ) ^ 9 := by
  rw [heilbronn_character_fourth_moment]
  have h :=
    Nat.cast_le (α := ℝ).mpr (Nat.mul_le_mul_left (p ^ 4) (heilbronnEnergy_square_le_uniform hodd))
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h ⊢
  nlinarith only [h]

/-- The complex indicator of the zero-shift Heilbronn coset in ZMod(p^2).
It is one on the subgroup and zero elsewhere, providing the standard discrete Fourier input. -/
noncomputable def heilbronnIndicator (p : ℕ) [Fact p.Prime] (x : ZMod (p ^ 2)) : ℂ := by
  classical exact if x ∈ shiftedTeichCoset p 0 then 1 else 0

/-- For prime p, the mathlib discrete Fourier transform of the Heilbronn indicator at l
is heilbronnCharacterSum at -l. Filter the transform sum and match the negative-phase convention. -/
theorem dft_heilbronnIndicator {p : ℕ} [Fact p.Prime] (l : ZMod (p ^ 2)) :
    ZMod.dft (heilbronnIndicator p) l = heilbronnCharacterSum p (-l) := by
  classical
  simp only [ZMod.dft_apply, heilbronnIndicator, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have he :
    (Finset.univ.filter (fun x : ZMod (p ^ 2) ↦ x ∈ shiftedTeichCoset p 0)) =
      (shiftedTeichCoset p 0).toFinset := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset]
  rw [he, heilbronnCharacterSum]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  ring

/-- The actual mathlib discrete Fourier transform of the Heilbronn indicator has fourth moment
p^2*heilbronnEnergy. Negating the frequency permutes the positive-phase sum. -/
theorem dft_heilbronnIndicator_fourth_moment {p : ℕ} [Fact p.Prime] :
    (∑ l : ZMod (p ^ 2), ‖ZMod.dft (heilbronnIndicator p) l‖ ^ 4) =
      ((p ^ 2 : ℕ) : ℝ) * heilbronnEnergy p := by
  simp only [dft_heilbronnIndicator]
  have he :
    (∑ l : ZMod (p ^ 2), ‖heilbronnCharacterSum p (-l)‖ ^ 4) =
      ∑ l : ZMod (p ^ 2), ‖heilbronnCharacterSum p l‖ ^ 4 :=
    Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ ↦ rfl)
  exact he.trans heilbronn_character_fourth_moment

end PseudoPrime.NumberTheory.Heilbronn
