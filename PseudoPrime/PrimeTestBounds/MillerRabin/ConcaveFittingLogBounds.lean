/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ConcaveFitting

/-! # Logarithmic domain guards for finite Miller--Rabin fitting witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Every stored MR vertex lies below the envelope of the checked fits.
Apply both individual vertex bounds and take their minimum.
This supplies certified anchors for the finite witness consumers. -/
theorem mrRegion_vertex_bound {v : ℚ × ℚ} (hv : v ∈ mrSmallRegionVertices) :
    (v.2 : ℝ) ≤ mrSmallRegionEnvelope (v.1 : ℝ) := by
  exact
    le_min (mrSmallRegionAffineFit.vertex_bound mrSmallRegionAffineFit_checked hv)
      (mrSmallRegionQuadraticFit.vertex_bound mrSmallRegionQuadraticFit_checked hv)

/-- The logarithm of 100000 lies below the checked right endpoint.
Use a kernel-verified rational Taylor interval at scale seventeen.
This identifies the finite numerical range of the proposed MR envelope. -/
theorem mrRegion_log_100000_upper :
    Real.log (100000 : ℝ) ≤ (mrSmallRegionQuadraticFit.right : ℝ) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 100000 17 32 (11512 / 1000) (11513 / 1000) = true
          from by decide +kernel)).2
  simpa only [mrSmallRegionQuadraticFit, Rat.cast_ofNat] using h

/-- The logarithm of 2047 exceeds the second stored MR vertex.
Use a kernel-verified rational logarithm interval at scale eleven.
This places the sole small base-two exception where the envelope is at least three. -/
theorem mrRegion_log_2047_lower : ((953 / 125 : ℚ) : ℝ) ≤ Real.log (2047 : ℝ) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 2047 11 32 (953 / 125) (763 / 100) = true from by
          decide +kernel)).1
  simpa only [Rat.cast_ofNat] using h

/-- For n at least nine, log n is above the first stored MR vertex.
Compare with log nine and the certified lower bound on log three.
This gives the lower domain guard for every odd composite above one. -/
theorem mrRegion_log_lower {n : ℕ} (hn9 : 9 ≤ n) : ((2197 / 1000 : ℚ) : ℝ) ≤ Real.log n := by
  have hlog := Real.log_le_log (by norm_num only : (0 : ℝ) < 9) (Nat.cast_le.mpr hn9)
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num only, Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  linarith only [hlog, Real.log_three_gt_d9]

/-- For positive n at most 100000, log n is below the checked right endpoint.
Use logarithm monotonicity and the rational endpoint certificate.
This supplies the upper guard for the envelope monotonicity theorem. -/
theorem mrRegion_log_upper {n : ℕ} (hn0 : 0 < n) (hnmax : n ≤ 100000) :
    Real.log n ≤ (mrSmallRegionQuadraticFit.right : ℝ) := by
  exact
    (Real.log_le_log (Nat.cast_pos.mpr hn0) (Nat.cast_le.mpr hnmax)).trans mrRegion_log_100000_upper

/-- For nine through 100000, the proposed MR envelope is at least two.
Transfer its first vertex bound by the proved monotonicity.
This absorbs actual base-two witnesses into the fitted pointwise expression. -/
theorem mrRegion_envelope_ge_two {n : ℕ} (hn9 : 9 ≤ n) (hnmax : n ≤ 100000) :
    (2 : ℝ) ≤ mrSmallRegionEnvelope (Real.log n) := by
  have hv :=
    mrRegion_vertex_bound
      (show ((2197 / 1000, 2) : ℚ × ℚ) ∈ mrSmallRegionVertices from List.mem_cons.mpr (Or.inl rfl))
  have hm :=
    mrSmallRegionEnvelope_monotone (mrRegion_log_lower hn9)
      (mrRegion_log_upper ((by decide : 0 < 9).trans_le hn9) hnmax)
  exact hv.trans hm

/-- For 2047 through 100000, the proposed MR envelope is at least three.
Transfer the second vertex using the certified logarithm of 2047 and monotonicity.
This absorbs either base two or base three into the same fitted expression. -/
theorem mrRegion_envelope_ge_three {n : ℕ} (hn : 2047 ≤ n) (hnmax : n ≤ 100000) :
    (3 : ℝ) ≤ mrSmallRegionEnvelope (Real.log n) := by
  have hv :=
    mrRegion_vertex_bound
      (show ((953 / 125, 3) : ℚ × ℚ) ∈ mrSmallRegionVertices from
        List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
  have hlog := Real.log_le_log (by norm_num only : (0 : ℝ) < 2047) (Nat.cast_le.mpr hn)
  have hm :=
    mrSmallRegionEnvelope_monotone (mrRegion_log_2047_lower.trans hlog)
      (mrRegion_log_upper ((by decide : 0 < 2047).trans_le hn) hnmax)
  exact hv.trans hm

end PseudoPrime.PrimeTestBounds.MillerRabin
