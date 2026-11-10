/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterNineCell
public import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeSmallFactor

/-! # The fourth signed-product semiprime cell -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An odd product of distinct ordered primes with logarithm between 13.81
and 14.30 has an unconditional quarter-square rejecting prime. For small
local moduli, primes through 47 generate the local group; for larger moduli,
368 checked weighted products and their negatives exceed the local kernel. -/
theorem quarter_semiprime_fourth {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hL : (1381 / 100 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 143 / 10) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 736 9 32 (66 / 10) 7 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hD : (66 / 10 : ℝ) ≤ Real.log ((2 * quarterNine90Row.getD 70 0 : ℕ) : ℝ) := by
    change _ ≤ Real.log (736 : ℝ)
    linarith only [hlog]
  have hA : Real.log 2 + (70 : ℝ) / 10 ≤ 77 / 10 := by linarith only [Real.log_two_lt_d9]
  have hB : (47 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  apply quarter_nine_cell hn ho hp hq hprod 70 47 (by decide) (by decide) hA hD hB
  intro hqsmall
  have hmax : max (77 / 10 : ℝ) (Real.log n - 66 / 10) ≤ 77 / 10 := by
    apply max_le le_rfl
    linarith only [hU]
  have hqlog : Real.log q ≤ (77 / 10 : ℝ) := hqsmall.trans hmax
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 2304 11 32 (774 / 100) 8 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hqR : (q : ℝ) < 2304 :=
    (Real.log_lt_log_iff (Nat.cast_pos.mpr hq.pos) (by norm_num only : (0 : ℝ) < 2304)).mp
      (by linarith only [hqlog, hcert])
  have hsize : q < (47 + 1) ^ 2 := by
    norm_num only
    exact_mod_cast hqR
  obtain ⟨r, hr, hrB, hf⟩ :=
    semiprime_small_factor_witness hn ho hp hq hpq hprod (by decide : 0 < 47) hsize
  exact ⟨r, hr, (Nat.cast_le.mpr hrB).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
