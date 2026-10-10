/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ResidueGapNumerics
public import PseudoPrime.NumberTheory.TotientPrimeCountBounds

/-! Endpoint logarithm certificates and prime-count ratios for residue intervals. -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a modulus in a positive integer interval with at most N prime factors,
checked endpoint logarithms and the prime-count totient ratio bound its logarithm,
totient and totient-log radius. Assume 1≤N≤5 and nonnegative ratio and lower logarithm.
Transport logarithms by monotonicity and multiply nonnegative bounds.
This supplies geometric hypotheses shared by analytic interval certificates. -/
theorem totientLogRadius_bounds_of_endpoint_checks {q a b N ja jb n : ℕ} {lo hi : ℚ} (ha : 0 < a)
    (haq : a ≤ q) (hqb : q ≤ b) (hN : 1 ≤ N) (hN' : N ≤ 5) (hc : q.primeFactors.card ≤ N)
    (hr : 0 ≤ (NumberTheory.totientPrimeCountLowerRatio N : ℝ)) (hlo : 0 ≤ lo)
    (hl : Analysis.rationalLogIntervalCheck a ja n lo hi = true)
    (hu : Analysis.rationalLogIntervalCheck b jb n lo hi = true) :
    (lo : ℝ) ≤ Real.log q ∧
      Real.log q ≤ (hi : ℝ) ∧
      (NumberTheory.totientPrimeCountLowerRatio N : ℝ) * a ≤ q.totient ∧
      ((NumberTheory.totientPrimeCountLowerRatio N : ℝ) * a) * (lo : ℝ) ≤
        (q.totient : ℝ) * Real.log q ∧
      (q.totient : ℝ) * Real.log q ≤ (b : ℝ) * (hi : ℝ) := by
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have haqR : (a : ℝ) ≤ q := Nat.cast_le.mpr haq
  have hqbR : (q : ℝ) ≤ b := Nat.cast_le.mpr hqb
  have hlow := (Analysis.rationalLogIntervalCheck_sound hl).1
  have hupp := (Analysis.rationalLogIntervalCheck_sound hu).2
  simp only [Rat.cast_natCast] at hlow hupp
  have hL := hlow.trans (Real.log_le_log haR haqR)
  have hU := (Real.log_le_log (haR.trans_le haqR) hqbR).trans hupp
  have hh :=
    (mul_le_mul_of_nonneg_left haqR hr).trans
      (NumberTheory.totient_ge_primeCount_ratio_real hN hN' hc)
  have hloR : (0 : ℝ) ≤ lo := (Rat.cast_nonneg (K := ℝ)).mpr hlo
  have hs := mul_le_mul hh hL hloR (Nat.cast_nonneg q.totient)
  have ht : (q.totient : ℝ) ≤ b := (Nat.cast_le.mpr (Nat.totient_le q)).trans hqbR
  have hS := mul_le_mul ht hU (hloR.trans hL) (Nat.cast_nonneg b)
  exact ⟨hL, hU, hh, hs, hS⟩

/-- Positive lower and upper radius bounds, a lower-square threshold and a
checked upper-square logarithm imply the cutoff threshold, logarithm bound and
natural exponent bound. Square the radius inequalities, use logarithm monotonicity
and the certified lower bound for log two. These conclusions feed interval
prime-power estimates without separate real-valued certificate calculations. -/
theorem totientLogCutoff_bounds_of_radius_checks {s : ℝ} {s₀ S T : ℚ} {j n K : ℕ} (hs₀ : 0 < s₀)
    (hss : (s₀ : ℝ) ≤ s) (hsS : s ≤ (S : ℝ)) (hx : 65536 ≤ s₀ ^ 2)
    (hl : Analysis.rationalLogIntervalCheck (S ^ 2) j n 0 T = true)
    (hK : T < (K + 1) * (6931471803 / 10000000000 : ℚ)) :
    65536 ≤ s ^ 2 ∧ Real.log (s ^ 2) ≤ (T : ℝ) ∧ ⌊Real.log (s ^ 2) / Real.log 2⌋₊ ≤ K := by
  have hpos : (0 : ℝ) < s₀ := (Rat.cast_pos (K := ℝ)).mpr hs₀
  have hbase : (65536 : ℝ) ≤ (s₀ : ℝ) ^ 2 := by exact_mod_cast hx
  have hcut := hbase.trans (pow_le_pow_left₀ hpos.le hss 2)
  have hupper := pow_le_pow_left₀ (hpos.le.trans hss) hsS 2
  have hlog := (Analysis.rationalLogIntervalCheck_sound hl).2
  simp only [Rat.cast_pow] at hlog
  have hT := (Real.log_le_log (pow_pos (hpos.trans_le hss) 2) hupper).trans hlog
  exact ⟨hcut, hT, logCutoff_exponentBound_of_rational_upper hT hK⟩

/-- With h≥2, a positive cutoff and nonnegative cutoff-log upper bound,
the parity coefficient is nonnegative above the modulus-log threshold.
Check each product and quotient separately. This supplies the sign guard
needed before increasing the radius multiplier in interval comparisons. -/
theorem residueParityIntervalCoefficient_nonneg {h X L T : ℝ} (hh : 2 ≤ h) (hX : 0 < X)
    (hL : 1719 / 1000 ≤ L) (hT : 0 ≤ T) : 0 ≤ residueParityIntervalCoefficient h X L T := by
  have hh0 : 0 ≤ h := (by norm_num only : (0 : ℝ) ≤ 2).trans hh
  have hh1 : 0 ≤ h - 1 := by linarith only [hh]
  have hh2 : 0 ≤ h - 2 := sub_nonneg.mpr hh
  have hLo : 0 ≤ L - 1719 / 1000 := sub_nonneg.mpr hL
  have hTo : 0 ≤ T + 1 + 29 / 100 := by linarith only [hT]
  have hm := mul_nonneg hh1 hLo
  have hn :=
    add_nonneg (add_nonneg (div_nonneg hh1 (by norm_num only : (0 : ℝ) ≤ 20)) (mul_nonneg hh2 hTo))
      (mul_nonneg hh0 (by norm_num only : (0 : ℝ) ≤ 693148 / 1000000 + 29 / 100))
  exact add_nonneg (add_nonneg hm (by norm_num only)) (div_nonneg hn hX.le)

/-- A positive radius and cutoff-log upper bound at least 1+23/40 make the
principal reciprocal correction nonnegative. Each remaining term is nonnegative.
This supplies the second sign guard of the common parity interval theorem. -/
theorem residueParityReciprocalCorrection_nonneg {s T : ℝ} (hs : 0 < s) (hT : 1 + 23 / 40 ≤ T) :
    0 ≤ T - (1 + 23 / 40) + 1839 / 1000 / s ^ 2 + 1 / (20 * s) := by
  exact
    add_nonneg (add_nonneg (sub_nonneg.mpr hT) (div_nonneg (by norm_num only) (sq_nonneg s)))
      (div_nonneg zero_le_one (mul_nonneg (by norm_num only) hs.le))

end PseudoPrime.LLS.PaperStatements
