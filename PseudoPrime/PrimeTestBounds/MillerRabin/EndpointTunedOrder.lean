/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointTunedPointwise
public import PseudoPrime.PrimeTestBounds.MillerRabin.SharpEnvelopeOrder

/-! # Normal-domain order of the tuned finite-principal envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Above the small branch and below the first high entrance, the finite tuned minimum
is at least 23. Every fixed prime and the current sharp fallback have this lower bound. -/
theorem tunedFiniteWitness_floor23 {n : ℕ} (hN : 3000 ≤ n) (hU : Real.log n < 30000000000) :
    (23 : ℝ) ≤ tunedFiniteWitness n := by
  have hn : 1 < n := lt_of_lt_of_le (by decide : 1 < 3000) hN
  apply tunedFinite_lower_of_candidates hn
  · rw [sharp_eq_selected hn]
    exact sharpSelected_floor23 hN hU
  · intro f _
    cases f with
    | finite f =>
      cases f <;>
        norm_num only [Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
          Nat.cast_ofNat]
    | p79 => norm_num only [Analysis.TunedPrimeProfile.bound, Nat.cast_ofNat]

/-- The exact selected finite envelope inherits the same regular lower bound of 23.
This numerical bound connects the preserved small branch to the regular domain. -/
theorem tunedFiniteSelected_floor23 {n : ℕ} (hN : 3000 ≤ n) (hU : Real.log n < 30000000000) :
    (23 : ℝ) ≤ tunedFiniteSelected n := by
  rw [← tunedFinite_eq_selected (lt_of_lt_of_le (by decide : 1 < 3000) hN)]
  exact tunedFiniteWitness_floor23 hN hU

/-- For regular inputs with log n below thirty billion, the finite tuned minimum increases.
Below the final cap use the monotone pointwise form; beyond it use the sharp fallback
and non-worsening to cover the transition from any earlier fixed-prime interval. -/
theorem tunedFiniteWitness_mono_large {m n : ℕ} (hm : 3000 ≤ m) (hmn : m ≤ n)
    (hU : Real.log n < 30000000000) : tunedFiniteWitness m ≤ tunedFiniteWitness n := by
  have hm1 : 1 < m := lt_of_lt_of_le (by decide : 1 < 3000) hm
  have hn1 : 1 < n := hm1.trans_le hmn
  have hn : 3000 ≤ n := hm.trans hmn
  have hlog : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hm1)) (Nat.cast_le.mpr hmn)
  by_cases hcap : Real.log n ≤ 126409 / 10000
  · rw [tunedFinite_eq_selected hm1, tunedFinite_eq_selected hn1, ←
      tunedFinitePointwise_eq_selected hm1 hm (hlog.trans hcap), ←
      tunedFinitePointwise_eq_selected hn1 hn hcap]
    exact tunedFinitePointwise_mono hlog
  · rw [tunedFinite_eq_sharp_of_log hn1 (lt_of_not_ge hcap)]
    exact
      (tunedFiniteWitness_le_sharp hm1).trans
        (by
          rw [sharp_eq_selected hm1, sharp_eq_selected hn1]
          exact sharpSelected_mono_normal ((by decide : 9 ≤ 3000).trans hm) hmn hU)

/-- For 9 <= m <= n below the first high entrance, the full finite tuned envelope increases.
The regular-domain result and the floor 23 connect the unchanged small values 2 and 3. -/
theorem tunedFiniteWitness_mono_normal {m n : ℕ} (hm : 9 ≤ m) (hmn : m ≤ n)
    (hU : Real.log n < 30000000000) : tunedFiniteWitness m ≤ tunedFiniteWitness n := by
  by_cases hnsmall : n < 3000
  · rw [tunedFiniteWitness_eq_small (lt_of_le_of_lt hmn hnsmall),
      tunedFiniteWitness_eq_small hnsmall, ← sharpWitness_eq_small (lt_of_le_of_lt hmn hnsmall), ←
      sharpWitness_eq_small hnsmall, sharp_eq_selected (lt_of_lt_of_le (by decide : 1 < 9) hm),
      sharp_eq_selected (lt_of_lt_of_le (by decide : 1 < 9) (hm.trans hmn))]
    exact sharpSelected_mono_normal hm hmn hU
  · by_cases hmsmall : m < 3000
    · have hf := tunedFiniteWitness_floor23 (le_of_not_gt hnsmall) hU
      rw [tunedFiniteWitness_eq_small hmsmall]
      dsimp only [smallIntervalBound]
      split_ifs <;> linarith only [hf]
    · exact tunedFiniteWitness_mono_large (le_of_not_gt hmsmall) hmn hU

/-- The exact fixed-prime selection increases on the same natural-input domain.
Transfer order through the numerical identity with the guarded witness envelope. -/
theorem tunedFiniteSelected_mono_normal {m n : ℕ} (hm : 9 ≤ m) (hmn : m ≤ n)
    (hU : Real.log n < 30000000000) : tunedFiniteSelected m ≤ tunedFiniteSelected n := by
  have hm1 : 1 < m := lt_of_lt_of_le (by decide : 1 < 9) hm
  rw [← tunedFinite_eq_selected hm1, ← tunedFinite_eq_selected (hm1.trans_le hmn)]
  exact tunedFiniteWitness_mono_normal hm hmn hU

end PseudoPrime.PrimeTestBounds.MillerRabin
