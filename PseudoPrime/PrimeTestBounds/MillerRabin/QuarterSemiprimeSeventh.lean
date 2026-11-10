/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeSmallFactor
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterElevenCell

/-! # The seventh signed-product semiprime cell -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An odd product of distinct ordered primes with logarithm between 14.8
and 14.96 has an unconditional quarter-square rejecting prime. For small
local moduli, primes through 54 generate the local group; for larger moduli,
531 checked weighted products and their negatives exceed the local kernel. -/
theorem quarter_semiprime_seventh {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q) (hL : (74 / 5 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 374 / 25) :
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
  have hA : Real.log 2 + (73 : ℝ) / 10 ≤ 8 := by linarith only [Real.log_two_lt_d9]
  have hB : (54 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  apply quarter_eleven_cell hn ho hp hq hprod 73 54 (by decide) (by decide) hA hD hB
  intro hqsmall
  have hmax : max (8 : ℝ) (Real.log n - 696 / 100) ≤ 8 := by
    apply max_le le_rfl
    linarith only [hU]
  have hqlog : Real.log q ≤ (8 : ℝ) := hqsmall.trans hmax
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 3025 11 32 (801 / 100) 9 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hqR : (q : ℝ) < 3025 :=
    (Real.log_lt_log_iff (Nat.cast_pos.mpr hq.pos) (by norm_num only : (0 : ℝ) < 3025)).mp
      (by linarith only [hqlog, hcert])
  have hsize : q < (54 + 1) ^ 2 := by
    norm_num only
    exact_mod_cast hqR
  obtain ⟨r, hr, hrB, hf⟩ :=
    semiprime_small_factor_witness hn ho hp hq hpq hprod (by decide : 0 < 54) hsize
  exact ⟨r, hr, (Nat.cast_le.mpr hrB).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
