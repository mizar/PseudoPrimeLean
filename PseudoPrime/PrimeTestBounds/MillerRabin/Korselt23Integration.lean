/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt23Block0
public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt23Block1
public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt23Block2
public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt23Block3
public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt23Block4
public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt23Block5
public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt23Block6
public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt23Block7
public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt23Block8
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformLow

/-! # Integration of bounded uniform Korselt factor certificates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Every uniform Korselt triple at most `2^23` has a prime divisor at most 53.
The ordered-factor parameterization places any larger smallest factor in one
of the independently checked empty search blocks. -/
theorem korselt23_small_prime {n : ℕ} (hu : UniformKorseltTriple n) (hbound : n ≤ 2 ^ 23) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p ≤ 53 := by
  obtain ⟨p, q, r, hp, hq, hr, hpq, hqr, hn⟩ := uniform_korselt_ordered hu
  have hpn : p ∣ n := hn ▸ dvd_mul_of_dvd_left (dvd_mul_right p q) r
  by_cases hp53 : p ≤ 53
  · exact ⟨p, hp, hpn, hp53⟩
  have hp59 : 59 ≤ p := by
    by_contra h
    have hnp : ∀ k ∈ Finset.Icc 54 58, ¬Nat.Prime k := by decide +kernel
    exact
      hnp p
        (Finset.mem_Icc.mpr
          ⟨Nat.succ_le_of_lt (Nat.lt_of_not_ge hp53), Nat.lt_succ_iff.mp (Nat.lt_of_not_ge h)⟩)
        hp
  have hcube : p ^ 3 ≤ n := by
    rw [hn, pow_succ, pow_two]
    exact Nat.mul_le_mul (Nat.mul_le_mul (le_refl p) hpq.le) (hpq.trans hqr).le
  have hp204 : p < 204 := by
    by_contra h
    have hpow := Nat.pow_le_pow_left (Nat.le_of_not_gt h) 3
    have hnum : 2 ^ 23 < (204 : ℕ) ^ 3 := by norm_num only
    exact (not_le_of_gt hnum) (hpow.trans (hcube.trans hbound))
  obtain ⟨a, ha, hap, heq, hdiv⟩ := uniformKorselt_ordered_parameters hn hp hq hr hpq hqr hu
  have hrec := korselt_parameter_reconstruct ha hr.one_lt.le heq
  by_cases h0 : p < 70
  · have hmem :=
      korselt23_mem hu hn hp hq hr hpq hqr hbound (lo := 59) (len := 11) (by linarith only [hp59])
        (by linarith only [h0]) ha hap hdiv hrec.1 hrec.2
    rw [korselt23_block0] at hmem
    exact False.elim (List.not_mem_nil hmem)
  by_cases h1 : p < 80
  · have hmem :=
      korselt23_mem hu hn hp hq hr hpq hqr hbound (lo := 70) (len := 10)
        (by linarith only [hp59, h0]) (by linarith only [h1]) ha hap hdiv hrec.1 hrec.2
    rw [korselt23_block1] at hmem
    exact False.elim (List.not_mem_nil hmem)
  by_cases h2 : p < 90
  · have hmem :=
      korselt23_mem hu hn hp hq hr hpq hqr hbound (lo := 80) (len := 10)
        (by linarith only [hp59, h0, h1]) (by linarith only [h2]) ha hap hdiv hrec.1 hrec.2
    rw [korselt23_block2] at hmem
    exact False.elim (List.not_mem_nil hmem)
  by_cases h3 : p < 100
  · have hmem :=
      korselt23_mem hu hn hp hq hr hpq hqr hbound (lo := 90) (len := 10)
        (by linarith only [hp59, h0, h1, h2]) (by linarith only [h3]) ha hap hdiv hrec.1 hrec.2
    rw [korselt23_block3] at hmem
    exact False.elim (List.not_mem_nil hmem)
  by_cases h4 : p < 120
  · have hmem :=
      korselt23_mem hu hn hp hq hr hpq hqr hbound (lo := 100) (len := 20)
        (by linarith only [hp59, h0, h1, h2, h3]) (by linarith only [h4]) ha hap hdiv hrec.1 hrec.2
    rw [korselt23_block4] at hmem
    exact False.elim (List.not_mem_nil hmem)
  by_cases h5 : p < 140
  · have hmem :=
      korselt23_mem hu hn hp hq hr hpq hqr hbound (lo := 120) (len := 20)
        (by linarith only [hp59, h0, h1, h2, h3, h4]) (by linarith only [h5]) ha hap hdiv hrec.1
        hrec.2
    rw [korselt23_block5] at hmem
    exact False.elim (List.not_mem_nil hmem)
  by_cases h6 : p < 160
  · have hmem :=
      korselt23_mem hu hn hp hq hr hpq hqr hbound (lo := 140) (len := 20)
        (by linarith only [hp59, h0, h1, h2, h3, h4, h5]) (by linarith only [h6]) ha hap hdiv hrec.1
        hrec.2
    rw [korselt23_block6] at hmem
    exact False.elim (List.not_mem_nil hmem)
  by_cases h7 : p < 180
  · have hmem :=
      korselt23_mem hu hn hp hq hr hpq hqr hbound (lo := 160) (len := 20)
        (by linarith only [hp59, h0, h1, h2, h3, h4, h5, h6]) (by linarith only [h7]) ha hap hdiv
        hrec.1 hrec.2
    rw [korselt23_block7] at hmem
    exact False.elim (List.not_mem_nil hmem)
  have hmem :=
    korselt23_mem hu hn hp hq hr hpq hqr hbound (lo := 180) (len := 24) (by linarith only [h7])
      (by linarith only [hp204]) ha hap hdiv hrec.1 hrec.2
  rw [korselt23_block8] at hmem
  exact False.elim (List.not_mem_nil hmem)

/-- A uniform Korselt triple with logarithm between 15 and 15.621 has a
quarter-square rejecting prime. A logarithm certificate bounds the input,
and the small factor supplied by the finite search is itself a witness. -/
theorem quarter_uniform_gap {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hL : (15 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 15621 / 1000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 8388608 24 32 (15621 / 1000) 17 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hnle : n ≤ 2 ^ 23 := by
    have hl : Real.log (n : ℝ) ≤ Real.log (8388608 : ℝ) := hU.trans hcert
    have hnR :=
      (Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
            (by norm_num only : (0 : ℝ) < 8388608)).mp
        hl
    norm_num only at hnR ⊢
    exact_mod_cast hnR
  obtain ⟨p, hp, hpn, hp53⟩ := korselt23_small_prime hu hnle
  have hb : (53 : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  exact
    ⟨p, hp, (Nat.cast_le.mpr hp53).trans hb,
      PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hpn⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
