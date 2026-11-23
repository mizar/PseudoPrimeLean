/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis131072
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis131072

/-! # Lower theta transfer across a certified restart window -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- Transfer a scalar lower bound across a sieve window using its certified prime count
and a rational lower bound for the logarithm of its left endpoint. -/
theorem theta_restart_gain (a b d k j : ℕ) (e f q u : ℚ) (ha : 1000000 ≤ a)
    (hb : b < (131072 + 1) * (131072 + 1)) (he : a + 8 * 2 ^ d = b) (hc : packedCount131072 a d = k)
    (hl : PseudoPrime.Analysis.rationalLogIntervalCheck a j 20 q u = true) (hf : f ≤ e + k * q)
    (hentry : (e : ℝ) ≤ Chebyshev.theta a) : (f : ℝ) ≤ Chebyshev.theta b := by
  have ha1 : 1 ≤ a := (by decide : 1 ≤ 1000000).trans ha
  have hwid : 2 * (4 * 2 ^ d) = 8 * 2 ^ d := (Nat.mul_assoc 2 4 (2 ^ d)).symm
  have hend : a + 2 * (4 * 2 ^ d) = b := hwid ▸ he
  have hg :=
    rank_gain a a (liveBits basis a (4 * 2 ^ d)) d ha1 le_rfl
      (fun _ hi => live_is_prime basis (fun _ => coversPacked) ha1 (hend ▸ hb) hi)
  change (packedCount131072 a d : ℝ) * Real.log a ≤ _ at hg
  rw [hend, hc] at hg
  have hq : (q : ℝ) ≤ Real.log a := by
    simpa only [Rat.cast_natCast] using (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1
  have hk := mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg (α := ℝ) k)
  have hf' := (Rat.cast_le (K := ℝ)).2 hf
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast] at hf'
  linarith only [hf', hk, hg, hentry]

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
