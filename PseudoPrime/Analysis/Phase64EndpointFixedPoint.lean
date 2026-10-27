/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FixedPointMangoldtAtoms
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedSummationByParts

/-! # Natural fixed-point execution for the two first-cell endpoint sums -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The natural lower fixed-point ramp atom at the first cell's lower endpoint.
Use the exponential Mangoldt lower atom before the ramp; on the final ramp multiply
by 495*(4096-n)/4096 and round down. Scale is 10^10. -/
def phase64RampFixedLower (n : ℕ) : ℕ :=
  let v := mangoldtExpFixedLower n 163840 99 10000000000 24 64
  if n * 9900 ≤ 247 * 163840 then v else v * 495 * (4096 - n) / 4096

/-- The natural upper exponential Mangoldt atom at the first cell's upper
endpoint, at scale 10^10 with 24 logarithm and 64 exponential Taylor terms. -/
def phase64PrincipalFixedUpper (n : ℕ) : ℕ :=
  mangoldtExpFixedUpper n 4096128001 2475000 10000000000 24 64

/-- Check the logarithm interval only on prime-power indices. Return true
elsewhere because the Mangoldt atom vanishes. This avoids a table of logarithm values. -/
def phase64EndpointLogCheck (n : ℕ) : Bool :=
  if IsPrimePow n then logFixedCheck (n.minFac : ℚ) (n.minFac.log2 + 1) 24 else true

/-- At a prime-power index a successful endpoint log check supplies the
underlying rational logarithm check. Unfold the supported branch. -/
theorem phase64_endpoint_log_sound {n : ℕ} (hc : phase64EndpointLogCheck n = true)
    (hn : IsPrimePow n) : logFixedCheck (n.minFac : ℚ) (n.minFac.log2 + 1) 24 = true := by
  simpa only [phase64EndpointLogCheck, ite_eq_left hn] using hc

/-- A successful index check certifies the computed upper atom for the
actual exponential Mangoldt term at the upper endpoint. Apply the generic atom bound
and simplify the rational scale exactly. -/
theorem phase64_principal_fixed_upper_sound (n : ℕ) (hc : phase64EndpointLogCheck n = true) :
    (10000000000 : ℝ) *
        (Real.exp (-(n : ℝ) / (4096128001 / 2475000)) * ArithmeticFunction.vonMangoldt n) ≤
      (phase64PrincipalFixedUpper n : ℝ) := by
  have h :=
    mangoldtExpFixedUpper_ge n 4096128001 2475000 10000000000 24 64 (by norm_num only)
      (by norm_num only) (phase64_endpoint_log_sound hc)
  have he : -((n * 2475000 : ℕ) : ℝ) / 4096128001 = -(n : ℝ) / (4096128001 / 2475000) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    ring
  norm_num only [Nat.cast_ofNat, Nat.cast_pow] at h
  rw [he] at h
  exact h

/-- At indices through 4096, a successful log check certifies the natural
lower atom for the actual ramp Mangoldt term. Prove the Taylor size gate, split at
the ramp join and round its rational linear factor down. -/
theorem phase64_ramp_fixed_lower_sound (n : ℕ) (hn : n ≤ 4096)
    (hc : phase64EndpointLogCheck n = true) :
    (phase64RampFixedLower n : ℝ) ≤
      (10000000000 : ℝ) *
        (ArithmeticFunction.vonMangoldt n * exponentialRampWeight ((n : ℝ) / (163840 / 99))) := by
  have hnR : (n : ℝ) ≤ 4096 := by exact_mod_cast hn
  have hsize : (((n * 99 : ℕ) : ℝ) / 163840) / (64 + 1 : ℕ) ≤ 1 / 2 := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    linarith only [hnR]
  have h :=
    mangoldtExpFixedLower_le n 163840 99 10000000000 24 64 (by norm_num only) (by norm_num only)
      (phase64_endpoint_log_sound hc) hsize
  have he : -((n * 99 : ℕ) : ℝ) / 163840 = -(n : ℝ) / (163840 / 99) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    ring
  norm_num only [Nat.cast_ofNat, Nat.cast_pow] at h
  rw [he] at h
  by_cases hj : n * 9900 ≤ 247 * 163840
  · have hjR : (n : ℝ) * 9900 ≤ 247 * 163840 := by exact_mod_cast hj
    have hu : (n : ℝ) / (163840 / 99) ≤ 247 / 100 := by linarith only [hjR]
    rw [phase64RampFixedLower, ite_eq_left hj, exponentialRampWeight_eq_exp_of_le_left hu]
    simpa only [neg_div, mul_comm] using h
  · have hjR : 247 * 163840 < (n : ℝ) * 9900 := by exact_mod_cast Nat.lt_of_not_ge hj
    have hlo : (247 / 100 : ℝ) ≤ (n : ℝ) / (163840 / 99) := by linarith only [hjR]
    have hhi : (n : ℝ) / (163840 / 99) ≤ 99 / 40 := by linarith only [hnR]
    have hm := fixedPoint_rational_mul_lower (a := 495 * (4096 - n)) (b := 4096) h
    norm_num only [Nat.cast_mul, Nat.cast_sub hn, Nat.cast_ofNat] at hm
    rw [phase64RampFixedLower, ite_eq_right hj, exponentialRampWeight_eq_middle hlo hhi]
    convert hm using 1
    · rw [Nat.mul_assoc]
    · rw [neg_div]
      ring

/-- Successful logarithm checks through 4096 transfer the computed natural
sum to a lower bound for the actual ramp sum at 163840/99, scaled by 10^10.
The real cutoff is exactly 4096; compare atoms and commute the scalar with the finite sum. -/
theorem phase64_ramp_fixed_sum_sound
    (hc : ∀ n ∈ Finset.Ioc 0 4096, phase64EndpointLogCheck n = true) :
    ((∑ n ∈ Finset.Ioc 0 4096, phase64RampFixedLower n : ℕ) : ℝ) ≤
      (10000000000 : ℝ) *
        AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum (163840 / 99) := by
  have h :=
    Finset.sum_le_sum
      (fun n hn ↦ phase64_ramp_fixed_lower_sound n (Finset.mem_Ioc.mp hn).2 (hc n hn))
  have hf : ⌊(163840 / 99 : ℝ) * (99 / 40)⌋₊ = 4096 := by
    rw [show (163840 / 99 : ℝ) * (99 / 40) = 4096 by ring, Nat.floor_ofNat]
  rw [AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum, hf, Finset.mul_sum]
  simpa only [Nat.cast_sum] using h

/-- Successful logarithm checks below 40000 transfer the computed natural
upper sum to an upper bound for the actual exponential prefix at the upper endpoint.
Compare the certified atoms and commute casting and finite summation. -/
theorem phase64_principal_fixed_sum_sound
    (hc : ∀ n ∈ Finset.range 40000, phase64EndpointLogCheck n = true) :
    (10000000000 : ℝ) *
        (∑ n ∈ Finset.range 40000,
          Real.exp (-(n : ℝ) / (4096128001 / 2475000)) * ArithmeticFunction.vonMangoldt n) ≤
      ((∑ n ∈ Finset.range 40000, phase64PrincipalFixedUpper n : ℕ) : ℝ) := by
  have h := Finset.sum_le_sum (fun n hn ↦ phase64_principal_fixed_upper_sound n (hc n hn))
  rw [Finset.mul_sum]
  simpa only [Nat.cast_sum] using h

end PseudoPrime.Analysis
