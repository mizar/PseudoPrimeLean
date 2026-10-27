/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.InvariantFourierMean

/-! # Fourth-power Fourier bounds for Heilbronn-invariant unit sets -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- The Heilbronn additive energy is at least one for every prime p.
Its zero-difference contribution is (p-1)² and p≥2. This elementary lower
bound absorbs nonunit frequency samples into the full fourth-moment budget. -/
theorem one_le_heilbronnEnergy {p : ℕ} [Fact p.Prime] : 1 ≤ heilbronnEnergy p := by
  have hp : 1 ≤ p - 1 := Nat.le_sub_one_of_lt (Nat.Prime.one_lt Fact.out)
  have hs : 1 ≤ (p - 1) ^ 2 := Nat.one_le_pow 2 (p - 1) hp
  rw [heilbronnEnergy_eq_normalized_moment]
  exact hs.trans (Nat.le_add_right _ _)

/-- At a unit frequency l, sampling the Heilbronn fourth moment on lQ is
bounded by the full Fourier fourth moment p²E. Multiplication by l is
injective, so nonnegative terms can be extended to all frequencies. -/
theorem sampled_heilbronn_fourth_le_of_unit {p : ℕ} [Fact p.Prime] (Q : Finset (ZMod (p ^ 2)))
    {l : ZMod (p ^ 2)} (hl : IsUnit l) :
    (∑ x ∈ Q, ‖heilbronnCharacterSum p (l * x)‖ ^ 4) ≤ (p : ℝ) ^ 2 * heilbronnEnergy p := by
  have h :=
    Finset.sum_le_sum_of_injOn (s := Q) (fun x : ZMod (p ^ 2) ↦ l * x)
      (fun x _ y _ he ↦ hl.mul_left_cancel he) (Finset.subset_univ _) (fun _ _ ↦ le_rfl)
      (fun a _ _ ↦ pow_nonneg (norm_nonneg (heilbronnCharacterSum p a)) 4)
  rw [heilbronn_character_fourth_moment] at h
  simpa only [Nat.cast_pow] using h

/-- For a finite unit set Q and nonzero nonunit l, the sampled fourth moment
is exactly card(Q). Every lx is nonzero and nonunit, so the exact Heilbronn
sum is minus one. This avoids an unjustified injectivity claim at nonunits. -/
theorem sampled_heilbronn_fourth_eq_card_of_nonunit {p : ℕ} [Fact p.Prime]
    (Q : Finset (ZMod (p ^ 2))) (hQ : ∀ x ∈ Q, IsUnit x) {l : ZMod (p ^ 2)} (hl : l ≠ 0)
    (hu : ¬IsUnit l) : (∑ x ∈ Q, ‖heilbronnCharacterSum p (l * x)‖ ^ 4) = Q.card := by
  have hz : squareReduction p l = 0 := by
    by_contra h
    exact hu ((isUnit_iff_reduction_ne_zero l).mpr h)
  have ht : ∀ x ∈ Q, ‖heilbronnCharacterSum p (l * x)‖ = 1 := by
    intro x hx
    apply norm_heilbronnCharacterSum_nonunit
    · intro he
      apply hl
      exact (hQ x hx).mul_right_cancel (he.trans (zero_mul x).symm)
    · intro h
      apply (isUnit_iff_reduction_ne_zero (l * x)).mp h
      rw [map_mul, hz, zero_mul]
  calc
    _ = ∑ _x ∈ Q, (1 : ℝ) := Finset.sum_congr rfl (fun x hx ↦ by rw [ht x hx, one_pow])
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Any finite subset of ZMod(p²) has cardinality at most p²E.
Use card(Q)≤p² and E≥1. This is the nonunit-frequency comparison needed
for the uniform sampled fourth-moment estimate. -/
theorem card_le_heilbronn_fourth_budget {p : ℕ} [Fact p.Prime] (Q : Finset (ZMod (p ^ 2))) :
    (Q.card : ℝ) ≤ (p : ℝ) ^ 2 * heilbronnEnergy p := by
  have hc : (Q.card : ℝ) ≤ (p : ℝ) ^ 2 := by
    have hn := (Finset.card_le_univ Q).trans_eq (ZMod.card (p ^ 2))
    exact_mod_cast hn
  have he : (1 : ℝ) ≤ heilbronnEnergy p := by exact_mod_cast (one_le_heilbronnEnergy (p := p))
  have hb := mul_le_mul_of_nonneg_left he (sq_nonneg (p : ℝ))
  exact hc.trans (by simpa only [mul_one] using hb)

/-- For every nonzero frequency and unit set Q, the sampled fourth moment
is at most p²E. Unit frequencies use injective extension; nonunit frequencies
use their exact value and the elementary cardinality budget. -/
theorem sampled_heilbronn_fourth_le_of_ne_zero {p : ℕ} [Fact p.Prime] (Q : Finset (ZMod (p ^ 2)))
    (hQ : ∀ x ∈ Q, IsUnit x) {l : ZMod (p ^ 2)} (hl : l ≠ 0) :
    (∑ x ∈ Q, ‖heilbronnCharacterSum p (l * x)‖ ^ 4) ≤ (p : ℝ) ^ 2 * heilbronnEnergy p := by
  by_cases hu : IsUnit l
  · exact sampled_heilbronn_fourth_le_of_unit Q hu
  rw [sampled_heilbronn_fourth_eq_card_of_nonunit Q hQ hl hu]
  exact card_le_heilbronn_fourth_budget Q

/-- For every nonzero frequency, an invariant unit set Q satisfies
(p-1)⁴|Qhat(l)|⁴≤p²E card(Q)³. Combine subgroup averaging with the sampled
fourth-moment bound, including the nonunit case. This is the Fourier input
for mixed third energy and the improved 32/13 energy estimate. -/
theorem invariant_character_fourth_le_energy {p : ℕ} [Fact p.Prime] (Q : Finset (ZMod (p ^ 2)))
    (hinv : IsHeilbronnInvariant Q) (hQ : ∀ x ∈ Q, IsUnit x) {l : ZMod (p ^ 2)} (hl : l ≠ 0) :
    (((p - 1 : ℕ) : ℝ) ^ 4) * ‖residueCharacterSum Q l‖ ^ 4 ≤
      (p : ℝ) ^ 2 * heilbronnEnergy p * (Q.card : ℝ) ^ 3 := by
  have h := invariant_character_fourth_le_sampled Q hinv l
  have hm :=
    mul_le_mul_of_nonneg_left (sampled_heilbronn_fourth_le_of_ne_zero Q hQ hl)
      (pow_nonneg (Nat.cast_nonneg Q.card : (0 : ℝ) ≤ Q.card) 3)
  exact (h.trans hm).trans_eq (by ring)

end PseudoPrime.NumberTheory.Heilbronn
