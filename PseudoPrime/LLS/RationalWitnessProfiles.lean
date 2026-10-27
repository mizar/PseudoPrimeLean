/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RationalTheorem11S1Subgroup
public import PseudoPrime.LLS.ParityRationalWitnessProfiles
public import PseudoPrime.Analysis.LogarithmicShiftBounds

/-! # Prepared rational Part 1 coefficient-and-start profile -/

@[expose] public section

namespace PseudoPrime.LLS

-- The former profile remains as a compatibility value.
-- The candidate catalog below now selects parityPart1Profile.
/-- The retained rational Part 1 tuple is (1,1791/250,499/250), starting at 3000.
The positive leading coefficient and signed coefficient slots use the common profile structure.
This records the formula and its entrance as one object. -/
def rationalPart1Profile : Analysis.RationalLogarithmicProfile :=
  ⟨1, 1791 / 250, 499 / 250, by norm_num only, 3000⟩

/-- Under GRH, the retained Part 1 profile bounds outside primes for every
proper subgroup from 3000. Apply the rational subgroup theorem and normalize the casts.
This attaches a proof to the coefficient-and-start pair. -/
theorem rationalPart1Profile_bound : UniformSubgroupProfileBound rationalPart1Profile := by
  intro q H hH hGRH hq
  obtain ⟨p, hp, hb⟩ := exists_prime_outside_subgroup_le_rationalProfile3000 hq H hH hGRH
  refine ⟨p, hp, ?_⟩
  simpa only [Analysis.RationalLogarithmicProfile.cutoff, Analysis.logarithmicShiftCutoff,
    Analysis.logarithmicShiftRoot, rationalPart1Profile, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one,
    one_mul] using hb

/-- For 3000 ≤ n ≤ m, the retained Part 1 cutoff at n is at most its value at m.
Use monotonicity of the logarithm and the positive-root shifted cutoff comparison.
This permits the same formula for a finite-range envelope. -/
theorem rationalPart1Profile_cutoff_le {n m : ℕ} (hn : 3000 ≤ n) (horder : n ≤ m) :
    rationalPart1Profile.cutoff n ≤ rationalPart1Profile.cutoff m := by
  have hL := Analysis.eight_lt_log_level hn
  have hL0 : 0 < Real.log n := by linarith only [hL]
  have hz := Real.log_nonneg (show 1 ≤ Real.log n by linarith only [hL])
  have hlog :=
    Real.log_le_log (Nat.cast_pos.mpr ((by decide : (0 : ℕ) < 3000).trans_le hn))
      (Nat.cast_le.mpr horder)
  have hb : -Real.log n ≤ ((1791 / 250 : ℚ) : ℝ) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    linarith only [hL]
  have hroot : 0 ≤ Analysis.logarithmicShiftRoot (Real.log n) (1791 / 250) (499 / 250) := by
    norm_num only [Analysis.logarithmicShiftRoot, Rat.cast_div, Rat.cast_ofNat]
    linarith only [hL, hz]
  exact Analysis.logarithmicShiftCutoff_le_of_le (by norm_num only : (0 : ℚ) < 1) hL0 hlog hb hroot

/-- Under GRH, for 3000 ≤ q ≤ B and H proper, an outside prime exists through
the retained Part 1 cutoff evaluated at B. Transfer the pointwise witness by monotonicity.
The envelope uses the same coefficient triple and starting value. -/
theorem exists_prime_outside_le_rationalPart1Profile_envelope {q B : ℕ} (hq : 3000 ≤ q)
    (hqB : q ≤ B) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, PrimeOutsideSubgroup q H p ∧ (p : ℝ) ≤ rationalPart1Profile.cutoff B := by
  obtain ⟨p, hp, hb⟩ := rationalPart1Profile_bound q H hH hGRH hq
  exact ⟨p, hp, hb.trans (rationalPart1Profile_cutoff_le hq hqB)⟩

/-- The retained uniform-unit-subgroup catalog contains the proved Part 1 profile.
Each retained tuple is eligible and useful below 10^100 among the prepared candidates.
Dominated tuples and larger-start tuples are omitted from this candidate catalog. -/
def retainedRationalProfiles : List Analysis.RationalLogarithmicProfile :=
  [parityPart1Profile]

end PseudoPrime.LLS
