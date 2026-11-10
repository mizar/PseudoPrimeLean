/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterNineCell
public import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeSmallFactor

/-! # The third signed-product semiprime cell -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An odd product of distinct ordered primes with logarithm between 12.69
and 13.81 has an unconditional quarter-square rejecting prime. For small
local moduli, primes through 40 generate the local group; for larger moduli,
307 checked weighted products and their negatives exceed the local kernel. -/
theorem quarter_semiprime_third {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hL : (1269 / 100 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 1381 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 614 9 32 (641 / 100) 7 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hD : (641 / 100 : ℝ) ≤ Real.log ((2 * quarterNine90Row.getD 67 0 : ℕ) : ℝ) := by
    change _ ≤ Real.log (614 : ℝ)
    linarith only [hlog]
  have hA : Real.log 2 + (67 : ℝ) / 10 ≤ 74 / 10 := by linarith only [Real.log_two_lt_d9]
  have hB : (40 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  apply quarter_nine_cell hn ho hp hq hprod 67 40 (by decide) (by decide) hA hD hB
  intro hqsmall
  have hmax : max (74 / 10 : ℝ) (Real.log n - 641 / 100) ≤ 74 / 10 := by
    apply max_le le_rfl
    linarith only [hU]
  have hqlog : Real.log q ≤ (74 / 10 : ℝ) := hqsmall.trans hmax
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1681 10 32 (742 / 100) 8 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hqR : (q : ℝ) < 1681 :=
    (Real.log_lt_log_iff (Nat.cast_pos.mpr hq.pos) (by norm_num only : (0 : ℝ) < 1681)).mp
      (by linarith only [hqlog, hcert])
  have hsize : q < (40 + 1) ^ 2 := by
    norm_num only
    exact_mod_cast hqR
  obtain ⟨r, hr, hrB, hf⟩ :=
    semiprime_small_factor_witness hn ho hp hq hpq hprod (by decide : 0 < 40) hsize
  exact ⟨r, hr, (Nat.cast_le.mpr hrB).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
