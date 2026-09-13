/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import PseudoPrime.PrimeTest.Lucas.Defs
import Mathlib.Tactic.Ring

/-!
# Integer identities for Selfridge Method A and Method A*

The identities in Appendix `S:Astar` of `bfw-Revised-arXiv-v2.tex` are proved
directly from the Lucas recurrences.  This avoids introducing the algebraic
numbers used in the paper's Binet-formula proof.
-/

namespace PseudoPrime.PrimeTest

private theorem lucasU_four_step (P Q : ℤ) (k : ℕ) :
    lucasU P Q (k + 4) = (P * P - 2 * Q) * lucasU P Q (k + 2) - Q * Q * lucasU P Q k := by
  have h3 := lucasU_succ_succ P Q (k + 2)
  have h2 := lucasU_succ_succ P Q k
  have h1 := lucasU_succ_succ P Q (k + 1)
  simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at h3 h2 h1 ⊢
  rw [h3, h1, h2]
  ring

private theorem lucasV_four_step (P Q : ℤ) (k : ℕ) :
    lucasV P Q (k + 4) = (P * P - 2 * Q) * lucasV P Q (k + 2) - Q * Q * lucasV P Q k := by
  have h3 := lucasV_succ_succ P Q (k + 2)
  have h2 := lucasV_succ_succ P Q k
  have h1 := lucasV_succ_succ P Q (k + 1)
  simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at h3 h2 h1 ⊢
  rw [h3, h1, h2]
  ring

/-- Appendix `S:Astar`, the unlabeled even-index U identity in the first theorem. -/
theorem lucasU_methodAStar_even (m : ℕ) : lucasU 5 5 (2 * m) = 5 ^ m * lucasU 1 (-1) (2 * m) := by
  induction m using Nat.twoStepInduction with
  | zero => simp [lucasU]
  | one => simp [lucasU]
  | more m hm hm1 =>
    have hs := lucasU_four_step 5 5 (2 * m)
    have ho := lucasU_four_step 1 (-1) (2 * m)
    have hm1' : lucasU 5 5 (2 + 2 * m) = 5 ^ (m + 1) * lucasU 1 (-1) (2 + 2 * m) := by
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hm1
    simp only [Nat.mul_add, Nat.add_comm] at hs ho hm1' ⊢
    rw [hs, ho, hm1', hm]
    ring_nf

/-- Appendix `S:Astar`, equation (13): even-index V values. -/
theorem lucasV_methodAStar_even (m : ℕ) : lucasV 5 5 (2 * m) = 5 ^ m * lucasV 1 (-1) (2 * m) := by
  induction m using Nat.twoStepInduction with
  | zero => simp [lucasV]
  | one => simp [lucasV]
  | more m hm hm1 =>
    have hs := lucasV_four_step 5 5 (2 * m)
    have ho := lucasV_four_step 1 (-1) (2 * m)
    have hm1' : lucasV 5 5 (2 + 2 * m) = 5 ^ (m + 1) * lucasV 1 (-1) (2 + 2 * m) := by
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hm1
    simp only [Nat.mul_add, Nat.add_comm] at hs ho hm1' ⊢
    rw [hs, ho, hm1', hm]
    ring_nf

/-- Appendix `S:Astar`, equation (11): odd-index U values. -/
theorem lucasU_methodAStar_odd (m : ℕ) :
    lucasU 5 5 (2 * m + 1) = 5 ^ m * lucasV 1 (-1) (2 * m + 1) := by
  induction m using Nat.twoStepInduction with
  | zero => simp [lucasU, lucasV]
  | one => simp [lucasU, lucasV]
  | more m hm hm1 =>
    have hs := lucasU_four_step 5 5 (2 * m + 1)
    have ho := lucasV_four_step 1 (-1) (2 * m + 1)
    have hm' : lucasU 5 5 (1 + 2 * m) = 5 ^ m * lucasV 1 (-1) (1 + 2 * m) := by
      simpa only [Nat.add_comm] using hm
    have hm1' : lucasU 5 5 (2 + (2 * m + 1)) = 5 ^ (m + 1) * lucasV 1 (-1) (2 + (2 * m + 1)) := by
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hm1
    simp only [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at hs ho hm1' ⊢
    rw [hs, ho, hm1', hm']
    ring_nf

/-- Appendix `S:Astar`, equation (12): odd-index V values. -/
theorem lucasV_methodAStar_odd (m : ℕ) :
    lucasV 5 5 (2 * m + 1) = 5 ^ (m + 1) * lucasU 1 (-1) (2 * m + 1) := by
  induction m using Nat.twoStepInduction with
  | zero => simp [lucasU, lucasV]
  | one => simp [lucasU, lucasV]
  | more m hm hm1 =>
    have hs := lucasV_four_step 5 5 (2 * m + 1)
    have ho := lucasU_four_step 1 (-1) (2 * m + 1)
    have hm' : lucasV 5 5 (1 + 2 * m) = 5 ^ (m + 1) * lucasU 1 (-1) (1 + 2 * m) := by
      simpa only [Nat.add_comm] using hm
    have hm1' : lucasV 5 5 (2 + (2 * m + 1)) = 5 ^ (m + 2) * lucasU 1 (-1) (2 + (2 * m + 1)) := by
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        pow_succ] using hm1
    simp only [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at hs ho hm1' ⊢
    rw [hs, ho, hm1', hm']
    ring_nf

end PseudoPrime.PrimeTest
