/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.NonunitFourier
public import PseudoPrime.NumberTheory.Heilbronn.WeightedFourthPower

/-! # Averaging Fourier sums of multiplicatively invariant residue sets -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Positive-phase Fourier sum of the indicator of a finite residue set Q.
The modulus is nonzero and the multiplier is any residue. Norms agree with
the usual negative-phase transform after negating the frequency. -/
noncomputable def residueCharacterSum {N : ℕ} [NeZero N] (Q : Finset (ZMod N)) (l : ZMod N) : ℂ :=
  ∑ x ∈ Q, ZMod.stdAddChar (l * x)

/-- A finite residue set is Heilbronn-invariant if multiplication by each
subgroup element maps the set onto itself. This supplies the exact finite
sum permutation used in the Fourier averaging identity. -/
def IsHeilbronnInvariant {p : ℕ} [Fact p.Prime] (Q : Finset (ZMod (p ^ 2))) : Prop :=
  ∀ γ ∈ shiftedTeichCoset p 0, Q.image (fun x ↦ γ * x) = Q

/-- Every zero-shift Heilbronn coset element is a unit. Write it as a nonzero
Teichmuller lift and use its explicit inverse. This justifies multiplication
as an injective map when averaging invariant finite sets. -/
theorem isUnit_of_mem_heilbronn {p : ℕ} [Fact p.Prime] {γ : ZMod (p ^ 2)}
    (hγ : γ ∈ shiftedTeichCoset p 0) : IsUnit γ := by
  obtain ⟨b, hb, he⟩ := hγ
  rw [he, principalShift_zero, one_mul]
  exact teichLift_isUnit b hb

/-- Multiplying the summation variable by a Heilbronn element preserves the
Fourier sum of an invariant set. Apply the exact finite image identity and
unit cancellation. This is the pointwise identity behind subgroup averaging. -/
theorem invariant_character_sum_mul {p : ℕ} [Fact p.Prime] (Q : Finset (ZMod (p ^ 2)))
    (hQ : IsHeilbronnInvariant Q) (l : ZMod (p ^ 2)) {γ : ZMod (p ^ 2)}
    (hγ : γ ∈ shiftedTeichCoset p 0) :
    (∑ x ∈ Q, ZMod.stdAddChar (l * x * γ)) = residueCharacterSum Q l := by
  classical
  have he :=
    Finset.sum_image (f := fun x ↦ ZMod.stdAddChar (l * x)) (s := Q) (g := fun x ↦ γ * x)
      (fun x _ y _ h ↦ (isUnit_of_mem_heilbronn hγ).mul_left_cancel h)
  rw [hQ γ hγ] at he
  change (∑ x ∈ Q, ZMod.stdAddChar (l * x * γ)) = ∑ x ∈ Q, ZMod.stdAddChar (l * x)
  rw [he]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  ring

/-- Averaging Heilbronn sums over an invariant finite set equals the subgroup
order times its Fourier sum. Interchange finite sums and use invariance for
each subgroup element. This permits a fourth-moment bound without dividing
by the subgroup order. -/
theorem invariant_character_average {p : ℕ} [Fact p.Prime] (Q : Finset (ZMod (p ^ 2)))
    (hQ : IsHeilbronnInvariant Q) (l : ZMod (p ^ 2)) :
    (∑ x ∈ Q, heilbronnCharacterSum p (l * x)) = ((p - 1 : ℕ) : ℂ) * residueCharacterSum Q l := by
  classical
  simp only [heilbronnCharacterSum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ _γ ∈ (shiftedTeichCoset p 0).toFinset, residueCharacterSum Q l :=
      Finset.sum_congr rfl (fun γ hγ ↦ invariant_character_sum_mul Q hQ l (Set.mem_toFinset.mp hγ))
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, Set.toFinset_card, ← Nat.card_eq_fintype_card,
        card_shiftedTeichCoset]

/-- The fourth power of a finite complex sum is at most card(S)³ times its
fourth norm moment. Combine the triangle inequality with the proved weighted
fourth-power inequality at unit weights. This includes the empty set. -/
theorem norm_sum_fourth_le_card_cube_mul_sum {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    ‖∑ x ∈ S, f x‖ ^ 4 ≤ (S.card : ℝ) ^ 3 * ∑ x ∈ S, ‖f x‖ ^ 4 := by
  have h := weighted_fourth_power_le S (fun _ ↦ (1 : ℝ)) (fun x ↦ ‖f x‖) (fun _ _ ↦ zero_le_one)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have hn := pow_le_pow_left₀ (norm_nonneg (∑ x ∈ S, f x)) (norm_sum_le S f) 4
  calc
    _ ≤ _ := hn
    _ ≤ (S.card : ℝ) ^ 2 * S.card * ∑ x ∈ S, ‖f x‖ ^ 4 := h
    _ = _ := by ring

/-- An invariant set's Fourier fourth power times the subgroup order to the
fourth is bounded by its cardinality cubed times the Heilbronn fourth moment
sampled on lQ. Apply the generic finite fourth-power estimate to the exact
averaging identity. No unit-frequency assumption is needed here. -/
theorem invariant_character_fourth_le_sampled {p : ℕ} [Fact p.Prime] (Q : Finset (ZMod (p ^ 2)))
    (hQ : IsHeilbronnInvariant Q) (l : ZMod (p ^ 2)) :
    (((p - 1 : ℕ) : ℝ) ^ 4) * ‖residueCharacterSum Q l‖ ^ 4 ≤
      (Q.card : ℝ) ^ 3 * ∑ x ∈ Q, ‖heilbronnCharacterSum p (l * x)‖ ^ 4 := by
  have h := norm_sum_fourth_le_card_cube_mul_sum Q (fun x ↦ heilbronnCharacterSum p (l * x))
  rw [invariant_character_average Q hQ l, norm_mul, Complex.norm_natCast, mul_pow] at h
  exact h

end PseudoPrime.NumberTheory.Heilbronn
