/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.FiniteDifferenceIncidence

/-! # Finite difference-incidence bounds from nonzero Fourier coefficients -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- At zero frequency a finite residue Fourier sum equals the cardinality.
Every additive-character term is one. This isolates the main term of the
finite difference-incidence identity. -/
theorem residueCharacterSum_zero {N : ℕ} [NeZero N] (Q : Finset (ZMod N)) :
    residueCharacterSum Q 0 = Q.card := by
  simp only [residueCharacterSum, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, nsmul_eq_mul,
    mul_one]

/-- The real part of the exact incidence identity weights the squared
Fourier norms of S by the real Fourier coefficients of Q. Take real parts
of the complex identity; all squared norms are real scalars. -/
theorem residueDifferenceIncidence_fourier_re {N : ℕ} [NeZero N] (S Q : Finset (ZMod N)) :
    (∑ l : ZMod N, (residueCharacterSum Q (-l)).re * ‖residueCharacterSum S l‖ ^ 2) =
      (N : ℝ) * residueDifferenceIncidence S Q := by
  have h := congrArg Complex.re (residueDifferenceIncidence_fourier S Q)
  simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, Complex.natCast_re, Complex.natCast_im] using h

/-- Separate the zero frequency from the incidence identity. Its exact
contribution is card(Q)card(S)²; all other frequencies remain in a finite
sum. This retains the main term before applying an upper Fourier envelope. -/
theorem residueDifferenceIncidence_fourier_split {N : ℕ} [NeZero N] (S Q : Finset (ZMod N)) :
    (N : ℝ) * residueDifferenceIncidence S Q =
      (Q.card : ℝ) * (S.card : ℝ) ^ 2 +
        ∑ l ∈ Finset.univ.erase (0 : ZMod N),
          (residueCharacterSum Q (-l)).re * ‖residueCharacterSum S l‖ ^ 2 := by
  have h :=
    Finset.sum_erase_add (Finset.univ : Finset (ZMod N))
      (fun l ↦ (residueCharacterSum Q (-l)).re * ‖residueCharacterSum S l‖ ^ 2)
      (Finset.mem_univ (0 : ZMod N))
  rw [residueDifferenceIncidence_fourier_re, neg_zero, residueCharacterSum_zero,
    residueCharacterSum_zero, Complex.natCast_re, Complex.norm_natCast] at h
  exact h.symm.trans (add_comm _ _)

/-- A uniform bound M≥0 for all nonzero Fourier coefficients of Q bounds
N times the difference incidence by card(Q)card(S)²+NMcard(S). Apply the
envelope termwise and use the exact second Fourier moment of S.
This is the finite analytic comparison needed on every correlation band. -/
theorem residueDifferenceIncidence_mul_le_of_fourier_bound {N : ℕ} [NeZero N]
    (S Q : Finset (ZMod N)) {M : ℝ} (hM : 0 ≤ M)
    (hQ : ∀ l : ZMod N, l ≠ 0 → ‖residueCharacterSum Q l‖ ≤ M) :
    (N : ℝ) * residueDifferenceIncidence S Q ≤
      (Q.card : ℝ) * (S.card : ℝ) ^ 2 + (N : ℝ) * M * S.card := by
  rw [residueDifferenceIncidence_fourier_split]
  apply add_le_add le_rfl
  have ht :
    (∑ l ∈ Finset.univ.erase (0 : ZMod N),
        (residueCharacterSum Q (-l)).re * ‖residueCharacterSum S l‖ ^ 2) ≤
      M * ∑ l ∈ Finset.univ.erase (0 : ZMod N), ‖residueCharacterSum S l‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l hl
    have hn : -l ≠ 0 := neg_ne_zero.mpr (Finset.mem_erase.mp hl).1
    exact mul_le_mul_of_nonneg_right ((Complex.re_le_norm _).trans (hQ (-l) hn)) (sq_nonneg _)
  have hs :
    (∑ l ∈ Finset.univ.erase (0 : ZMod N), ‖residueCharacterSum S l‖ ^ 2) ≤ (N : ℝ) * S.card := by
    rw [← residueCharacterSum_second_moment S]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun l _ _ ↦ sq_nonneg _)
  exact (ht.trans (mul_le_mul_of_nonneg_left hs hM)).trans_eq (by ring)

/-- Divide the scaled incidence estimate by the positive modulus.
The result is card(S)²card(Q)/N+Mcard(S), separating the exact main term
from the nonzero-frequency error without additional hypotheses on S. -/
theorem residueDifferenceIncidence_le_of_fourier_bound {N : ℕ} [NeZero N] (S Q : Finset (ZMod N))
    {M : ℝ} (hM : 0 ≤ M) (hQ : ∀ l : ZMod N, l ≠ 0 → ‖residueCharacterSum Q l‖ ≤ M) :
    (residueDifferenceIncidence S Q : ℝ) ≤ (S.card : ℝ) ^ 2 * Q.card / N + M * S.card := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  apply (mul_le_mul_iff_right₀ hN).mp
  calc
    _ ≤ (Q.card : ℝ) * (S.card : ℝ) ^ 2 + (N : ℝ) * M * S.card :=
      residueDifferenceIncidence_mul_le_of_fourier_bound S Q hM hQ
    _ = (N : ℝ) * ((S.card : ℝ) ^ 2 * Q.card / N + M * S.card) := by field_simp [hN.ne']

end PseudoPrime.NumberTheory.Heilbronn
