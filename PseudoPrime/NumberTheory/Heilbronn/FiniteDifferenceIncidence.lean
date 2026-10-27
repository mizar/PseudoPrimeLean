/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.InvariantFourierMean

/-! # Fourier inversion for finite difference incidences -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Number of ordered pairs from S whose difference lies in Q. The modulus
is arbitrary and nonzero. This natural count is the finite incidence form
of the mixed third-energy contribution on one correlation band. -/
def residueDifferenceIncidence {N : ℕ} [NeZero N] (S Q : Finset (ZMod N)) : ℕ :=
  ((S ×ˢ S).filter (fun z ↦ z.1 - z.2 ∈ Q)).card

/-- Fourier inversion for a finite residue indicator, multiplied by N.
Expand the Fourier sum and use exact additive-character orthogonality.
This is a finite identity, without integrals or convergence hypotheses. -/
theorem sum_residueCharacterSum_mul_char {N : ℕ} [NeZero N] (Q : Finset (ZMod N)) (a : ZMod N) :
    (∑ l : ZMod N, residueCharacterSum Q (-l) * ZMod.stdAddChar (l * a)) =
      if a ∈ Q then (N : ℂ) else 0 := by
  classical
  simp only [residueCharacterSum, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ q ∈ Q, if a = q then (N : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      have he :
        (∑ l : ZMod N, ZMod.stdAddChar (-l * q) * ZMod.stdAddChar (l * a)) =
          ∑ l : ZMod N, ZMod.stdAddChar ((a - q) * l) := by
        apply Finset.sum_congr rfl
        intro l _
        rw [← AddChar.map_add_eq_mul]
        congr 1
        ring
      rw [he, sum_stdAddChar_mul]
      simp only [sub_eq_zero]
    _ = _ := Finset.sum_ite_eq Q a (fun _ ↦ (N : ℂ))

/-- The second Fourier moment of a finite residue set is N card(S).
The exact indexed moment counts equal ordered pairs, which form the diagonal.
This supplies the nonzero-frequency mass budget for incidence estimates. -/
theorem residueCharacterSum_second_moment {N : ℕ} [NeZero N] (S : Finset (ZMod N)) :
    (∑ l : ZMod N, ‖residueCharacterSum S l‖ ^ 2) = (N : ℝ) * S.card := by
  have h := char_sum_second_moment S (fun x ↦ x)
  rw [← Finset.diag_eq_filter, Finset.diag_card] at h
  simpa only [residueCharacterSum, Complex.normSq_eq_norm_sq] using h

/-- The complex square norm of a residue Fourier sum equals its sum over
ordered differences. Specialize the existing indexed identity to distinct
residues. This permits exact finite Fourier expansion of incidences. -/
theorem residueCharacterSum_norm_sq_pairs {N : ℕ} [NeZero N] (S : Finset (ZMod N)) (l : ZMod N) :
    ((‖residueCharacterSum S l‖ ^ 2 : ℝ) : ℂ) =
      ∑ x ∈ S, ∑ y ∈ S, ZMod.stdAddChar (l * (x - y)) := by
  simpa only [residueCharacterSum, Complex.normSq_eq_norm_sq] using
    (char_sum_normSq_pairs S (fun x ↦ x) l)

/-- The Fourier sum of Q against the squared Fourier norm of S equals N
 times the number of S-differences in Q. Interchange finite sums and use
indicator inversion. This is the exact starting identity for mixed energy. -/
theorem residueDifferenceIncidence_fourier {N : ℕ} [NeZero N] (S Q : Finset (ZMod N)) :
    (∑ l : ZMod N, residueCharacterSum Q (-l) * ((‖residueCharacterSum S l‖ ^ 2 : ℝ) : ℂ)) =
      (N : ℂ) * residueDifferenceIncidence S Q := by
  classical
  simp only [residueCharacterSum_norm_sq_pairs, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ =
        ∑ x ∈ S,
          ∑ y ∈ S, ∑ l : ZMod N, residueCharacterSum Q (-l) * ZMod.stdAddChar (l * (x - y)) :=
      by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = ∑ x ∈ S, ∑ y ∈ S, if x - y ∈ Q then (N : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      exact sum_residueCharacterSum_mul_char Q (x - y)
    _ = (N : ℂ) * (∑ z ∈ S ×ˢ S, if z.1 - z.2 ∈ Q then (1 : ℂ) else 0) := by
      simp only [Finset.sum_product, Finset.mul_sum, mul_ite, mul_one, mul_zero]
    _ = _ := by
      rw [Finset.sum_boole]; rfl

end PseudoPrime.NumberTheory.Heilbronn
