/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeSmallFactor
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterElevenCell

/-! # The eighth signed-product semiprime cell -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An odd product of distinct ordered primes with logarithm between 14.96
and 15 has an unconditional quarter-square rejecting prime. For small
local moduli, primes through 55 generate the local group; for larger moduli,
531 checked weighted products and their negatives exceed the local kernel. -/
theorem quarter_semiprime_eighth {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hL : (374 / 25 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 15) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1062 10 32 (696 / 100) 7 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hD : (696 / 100 : ℝ) ≤ Real.log ((2 * quarterElevenRow.getD 73 0 : ℕ) : ℝ) := by
    change (696 / 100 : ℝ) ≤ Real.log (1062 : ℝ)
    linarith only [hlog]
  have hA : Real.log 2 + (73 : ℝ) / 10 ≤ 201 / 25 := by linarith only [Real.log_two_lt_d9]
  have hB : (55 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  apply quarter_eleven_cell hn ho hp hq hprod 73 55 (by decide) (by decide) hA hD hB
  intro hqsmall
  have hmax : max (201 / 25 : ℝ) (Real.log n - 696 / 100) ≤ 201 / 25 := by
    apply max_le le_rfl
    linarith only [hU]
  have hqlog : Real.log q ≤ (201 / 25 : ℝ) := hqsmall.trans hmax
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 3136 11 32 (8045 / 1000) 9 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hqR : (q : ℝ) < 3136 :=
    (Real.log_lt_log_iff (Nat.cast_pos.mpr hq.pos) (by norm_num only : (0 : ℝ) < 3136)).mp
      (by linarith only [hqlog, hcert])
  have hsize : q < (55 + 1) ^ 2 := by
    norm_num only
    exact_mod_cast hqR
  obtain ⟨r, hr, hrB, hf⟩ :=
    semiprime_small_factor_witness hn ho hp hq hpq hprod (by decide : 0 < 55) hsize
  exact ⟨r, hr, (Nat.cast_le.mpr hrB).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
