/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.HeilbronnFourierMoments

/-! # Heilbronn Fourier sums at nonzero nonunit frequencies -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- The standard additive character modulo p², restricted to the additive
lift a↦pa, is the standard character modulo prime p. Compare the exponential
formulas and cancel the nonzero p. This handles nonunit Fourier frequencies. -/
theorem stdAddChar_primeLift {p : ℕ} [Fact p.Prime] (a : ZMod p) :
    ZMod.stdAddChar (primeLift p a) = ZMod.stdAddChar a := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
  have ha : (a.val : ZMod p) = ((a.val : ℤ) : ZMod p) := by rw [Int.cast_natCast]
  rw [primeLift, ← Nat.cast_mul]
  have he : ((p * a.val : ℕ) : ZMod (p ^ 2)) = ((p * a.val : ℤ) : ZMod (p ^ 2)) := by
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast, Nat.cast_mul]
  rw [he, ZMod.stdAddChar_coe]
  conv_rhs => rw [← ZMod.natCast_zmod_val a, ha, ZMod.stdAddChar_coe]
  simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_pow]
  congr 1
  field_simp [hp]

/-- At a nonzero multiplier, the standard additive character summed over
all nonzero residues is minus one. Remove zero from the orthogonality sum.
This works for every nonzero modulus and supplies the nonunit Heilbronn sum. -/
theorem sum_stdAddChar_mul_nonzero {N : ℕ} [NeZero N] (a : ZMod N) (ha : a ≠ 0) :
    (∑ b : { b : ZMod N // b ≠ 0 }, ZMod.stdAddChar (a * b.val)) = -1 := by
  classical
  have he :=
    Finset.sum_subtype (p := fun b : ZMod N ↦ b ≠ 0) (F := inferInstance)
      (Finset.univ.erase (0 : ZMod N))
      (fun b ↦ by simp only [Finset.mem_erase, Finset.mem_univ, and_true])
      (fun b ↦ ZMod.stdAddChar (a * b))
  rw [← he]
  have h :=
    Finset.sum_erase_add (Finset.univ : Finset (ZMod N)) (fun b ↦ ZMod.stdAddChar (a * b))
      (Finset.mem_univ (0 : ZMod N))
  rw [sum_stdAddChar_mul, ite_eq_right ha, mul_zero, AddChar.map_zero_eq_one] at h
  exact eq_neg_of_add_eq_zero_left h

/-- The Heilbronn character sum at the additive lift of a is the standard
character sum over the nonzero residues modulo p. Parametrize the subgroup
by its reduction equivalence and apply the additive-character lift identity.
This includes both zero and nonzero lifted frequencies. -/
theorem heilbronnCharacterSum_primeLift {p : ℕ} [Fact p.Prime] (a : ZMod p) :
    heilbronnCharacterSum p (primeLift p a) =
      ∑ b : { b : ZMod p // b ≠ 0 }, ZMod.stdAddChar (a * b.val) := by
  classical
  rw [heilbronnCharacterSum]
  have he :=
    Finset.sum_subtype (p := fun x : ZMod (p ^ 2) ↦ x ∈ shiftedTeichCoset p 0) (F := inferInstance)
      (shiftedTeichCoset p 0).toFinset (fun x ↦ Set.mem_toFinset)
      (fun x ↦ ZMod.stdAddChar (primeLift p a * x))
  rw [he]
  calc
    _ = ∑ x : shiftedTeichCoset p 0, ZMod.stdAddChar (a * squareReduction p x.val) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← primeLift_mul, stdAddChar_primeLift]
    _ = _ :=
      (shiftedTeichCosetEquivResidues (p := p) 0).sum_comp (fun b ↦ ZMod.stdAddChar (a * b.val))

/-- At every nonzero nonunit frequency modulo p², the Heilbronn character
sum is exactly minus one. Express the frequency in the additive reduction
kernel and use orthogonality over the nonzero residues. This closes the
nonunit case of the invariant-set Fourier comparison. -/
theorem heilbronnCharacterSum_nonunit {p : ℕ} [Fact p.Prime] {l : ZMod (p ^ 2)} (hl : l ≠ 0)
    (hu : ¬IsUnit l) : heilbronnCharacterSum p l = -1 := by
  have hz : squareReduction p l = 0 := by
    by_contra h
    exact hu ((isUnit_iff_reduction_ne_zero l).mpr h)
  obtain ⟨a, ha⟩ := primeLift_surjective_kernel l hz
  have ha0 : a ≠ 0 := by
    intro h
    subst a
    rw [primeLift_zero] at ha
    exact hl ha.symm
  rw [← ha, heilbronnCharacterSum_primeLift, sum_stdAddChar_mul_nonzero a ha0]

/-- The norm of a nonzero nonunit Heilbronn frequency is one. Rewrite its
exact value and use norm(-1)=1. This supplies the numerical contribution
when an invariant-set Fourier bound separates unit and nonunit frequencies. -/
theorem norm_heilbronnCharacterSum_nonunit {p : ℕ} [Fact p.Prime] {l : ZMod (p ^ 2)} (hl : l ≠ 0)
    (hu : ¬IsUnit l) : ‖heilbronnCharacterSum p l‖ = 1 := by
  rw [heilbronnCharacterSum_nonunit hl hu, norm_neg, norm_one]

end PseudoPrime.NumberTheory.Heilbronn
