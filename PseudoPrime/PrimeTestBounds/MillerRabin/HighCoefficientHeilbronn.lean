/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HeightLayerHeilbronnBounds

/-! # Non-explicit high-coefficient bound for nonsquarefree inputs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For every sufficiently large odd nonsquarefree `n > 1`, a prime MR
witness is at most `(7 / 16) * log n ^ 2` without assuming GRH. Apply the
existing height-layer bound with exponent `37 / 20 < 2` and absorb it
asymptotically. The result does not specify a numerical entrance. -/
theorem eventually_highCoeff_nonsquarefree :
    Filter.Eventually
      (fun n : ℕ ↦
        1 < n →
          Odd n →
          ¬Squarefree n →
          ∃ q : ℕ,
            q.Prime ∧
              (q : ℝ) ≤ (7 / 16 : ℝ) * (Real.log n) ^ 2 ∧
              ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n))
      Filter.atTop := by
  have hL : Filter.Tendsto (fun n : ℕ ↦ Real.log n) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow :=
    hL.eventually
      (NumberTheory.eventually_const_mul_rpow_le_rpow (C := (16 / 7 : ℝ)) (b := (37 / 20 : ℝ)) (A :=
        (2 : ℝ)) (by norm_num only))
  filter_upwards [eventually_exists_prime_witness_of_height_layers (A := (37 / 20 : ℝ))
      (by norm_num only),
    hpow] with n h hbound hn ho hns
  obtain ⟨q, hq, hb, hf⟩ := h hn ho hns
  have hcomp : (Real.log n) ^ (37 / 20 : ℝ) ≤ (7 / 16 : ℝ) * (Real.log n) ^ 2 := by
    rw [Real.rpow_two] at hbound
    linarith only [hbound]
  exact ⟨q, hq, hb.trans hcomp, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
