/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleIntTransforms

/-! # Tail signs for integer profile rows -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- One translated numerator test proves the signs of all derivatives on the tail. -/
public theorem MiddleIntRow.tail_signs (r : MiddleIntRow) (N : ℕ) (b : ℤ) (hr : 0 < r.den)
    (hs : ∀ i : Fin (N + 1), 0 ≤ (gaussianAffineIntRow N b 1 r.num)[i.val]?.getD 0) (j : ℕ) {x : ℝ}
    (hx : (b : ℝ) ≤ x) :
    0 ≤ ((Polynomial.derivative^[j]) ((r.poly N).map (Rat.castHom ℝ))).eval x := by
  refine
    middle_profile_sign_of_row (r.poly N) N b r.den r.num hr
      (Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos N) _)) ?_ ?_ j hx
  · intro i hi
    rw [r.poly_coeff hi, ← mul_div_assoc, mul_comm (r.den : ℚ),
      mul_div_cancel_right₀ _ (Int.cast_ne_zero.mpr hr.ne')]
  · exact fun i hi ↦ hs ⟨i, Nat.lt_succ_of_le hi⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
