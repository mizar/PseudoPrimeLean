/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.CorrelationIncidence

/-! # Constant row sums of invariant Heilbronn difference weights -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Multiplication by a nonzero Teichmuller lift permutes the finite
Heilbronn set. Its inverse multiplies by the lift of the inverse residue.
This supplies an explicit summation permutation for invariant weights. -/
noncomputable def heilbronnMulEquiv {p : ℕ} [Fact p.Prime] (b : ZMod p) (hb : b ≠ 0) :
    heilbronnElements p ≃ heilbronnElements p := by
  refine
    { toFun := fun x ↦
        ⟨x.val * teichLift p b,
          (mem_heilbronnElements _).mpr
            (mul_teichLift_mem_shiftedTeichCoset ((mem_heilbronnElements _).mp x.property) b hb)⟩
      invFun := fun x ↦
        ⟨x.val * teichLift p b⁻¹,
          (mem_heilbronnElements _).mpr
            (mul_teichLift_mem_shiftedTeichCoset ((mem_heilbronnElements _).mp x.property) b⁻¹
              (inv_ne_zero hb))⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    apply Subtype.ext
    change (x.val * teichLift p b) * teichLift p b⁻¹ = x.val
    rw [mul_assoc, teichLift_mul_inv b hb, mul_one]
  · intro x
    apply Subtype.ext
    change (x.val * teichLift p b⁻¹) * teichLift p b = x.val
    rw [mul_assoc, mul_comm (teichLift p b⁻¹), teichLift_mul_inv b hb, mul_one]

/-- Every row of a multiplicatively invariant difference weight on the
Heilbronn set has the same sum as the row at 1. Scale the summation variable
by the row's Teichmuller parameter. No symmetry or positivity is needed. -/
theorem invariant_weight_row_sum {p : ℕ} [Fact p.Prime] (g : ZMod (p ^ 2) → ℕ)
    (hg : ∀ γ ∈ shiftedTeichCoset p 0, ∀ a, g (γ * a) = g a) (x : heilbronnElements p) :
    (∑ y : heilbronnElements p, g (x.val - y.val)) = ∑ y : heilbronnElements p, g (1 - y.val) := by
  obtain ⟨b, hb, hx⟩ := (mem_heilbronnElements x.val).mp x.property
  have hx' : x.val = teichLift p b := by simpa only [principalShift_zero, one_mul] using hx
  rw [← (heilbronnMulEquiv b hb).sum_comp (fun y ↦ g (x.val - y.val))]
  apply Finset.sum_congr rfl
  intro y _
  change g (x.val - y.val * teichLift p b) = g (1 - y.val)
  rw [hx']
  have hd : teichLift p b - y.val * teichLift p b = teichLift p b * (1 - y.val) := by ring
  rw [hd, hg (teichLift p b) ⟨b, hb, by rw [principalShift_zero, one_mul]⟩]

end PseudoPrime.NumberTheory.Heilbronn
