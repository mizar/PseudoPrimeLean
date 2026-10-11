/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Kronecker.Basic
public import PseudoPrime.NumberTheory.Kronecker.Compatibility

/-! # Zero values and exact coprimality for the Kronecker specification -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- At a nonzero integer denominator, Kronecker and absolute-denominator Jacobi vanish together.
The denominator sign is nonzero, and squaring the factor at two does not alter its zero set.
This transfers the natural Jacobi coprimality criterion to the integer specification. -/
theorem kroneckerSym_zero_iff_jacobiSym (a n : ℤ) (hn : n ≠ 0) :
    kroneckerSym a n = 0 ↔ jacobiSym a n.natAbs = 0 := by
  have hs : kroneckerDenominatorSign a n ≠ 0 := by
    dsimp only [kroneckerDenominatorSign]
    split <;> decide
  rw [kroneckerSym, ite_eq_right hn,
    jacobiSym_two_adic_right a n.natAbs (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hn)), ←
    kroneckerAtTwo_sq_eq_jacobiSym_two]
  simp only [mul_eq_zero, hs, false_or, pow_eq_zero_iff']
  exact
    ⟨fun h ↦ h.elim (fun h ↦ Or.inl ⟨⟨h.1, by decide⟩, h.2⟩) Or.inr, fun h ↦
      h.elim (fun h ↦ Or.inl ⟨h.1.1, h.2⟩) Or.inr⟩

/-- The Kronecker symbol vanishes exactly when the absolute-input gcd is not one.
The zero denominator is handled directly; otherwise use the natural Jacobi criterion.
The formulation includes gcd zero at the input pair `(0, 0)`. -/
theorem kroneckerSym_zero_iff (a n : ℤ) : kroneckerSym a n = 0 ↔ Nat.gcd a.natAbs n.natAbs ≠ 1 := by
  exact
    if hn : n = 0 then
      (show _ by
        subst n
        rw [kroneckerSym_zero_right]
        simp only [Int.natAbs_zero, Nat.gcd_zero_right]
        exact
          if ha : a.natAbs = 1 then
            (show _ by simp only [ha, ite_true, one_ne_zero, ne_eq, not_true_eq_false])
          else (show _ by simp only [ha, ite_false, ne_eq, not_false_eq_true]))
    else
      (show _ by
        let : NeZero n.natAbs := ⟨Int.natAbs_ne_zero.mpr hn⟩
        exact
          (kroneckerSym_zero_iff_jacobiSym a n hn).trans
            (show jacobiSym a n.natAbs = 0 ↔ a.natAbs.gcd n.natAbs ≠ 1 by
              simpa only [Int.gcd_eq_natAbs, Int.natAbs_natCast] using
                (jacobiSym.eq_zero_iff_not_coprime (a := a) (b := n.natAbs))))

end PseudoPrime.NumberTheory
