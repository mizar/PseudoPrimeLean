/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaLower1100000
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaLower2000000
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaLower4000000
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaLower8096000
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaLower13922560
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaLower21563648
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaLower31072512
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaLower42488064
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaLowerMillion

/-! # Finite prefix of the lower Lee-Nosal estimate -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- The first eight certified windows propagate the entrance bound to 42488064. -/
private theorem prefix_segment :
    ThetaLowerSegment 1050624 42488064 (5243944 / 5) (4248067478303 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join theta_segment_1050624_1100000 theta_segment_1100000_2000000)
        (ThetaLowerSegment.join theta_segment_2000000_4000000 theta_segment_4000000_8096000))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join theta_segment_8096000_13922560 theta_segment_13922560_21563648)
        (ThetaLowerSegment.join theta_segment_21563648_31072512 theta_segment_31072512_42488064)))

/-- Apply the initial theta bound and cover the full closed interval from 2657. -/
theorem theta_lower_2657_42488064 {x : ℝ} (hx : 2657 ≤ x) (hy : x ≤ 42488064) :
    (x - Chebyshev.theta x) / Real.sqrt x ≤
      Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
  rcases le_total x 1050624 with h | h
  · exact theta_lower_2657_1050624 hx h
  have hs :=
    prefix_segment
      (by simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using theta_entry_1050624)
  exact hs.2 x (by simpa only [Nat.cast_ofNat] using h) (by simpa only [Nat.cast_ofNat] using hy)

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
