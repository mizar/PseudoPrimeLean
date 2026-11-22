/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.MillionEndpoint
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.BandEnvelope
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.FirstHighPrefix

/-! # Closing the joint finite estimates at one million -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- The remaining high-range certificate has fixed scalar endpoints and two real bounds. -/
def HighSegment : Prop :=
  Segment Valid highEstimate
    ⟨3500, 3483879109733892, 3483920680466223, 74422413522765, 74422413522895⟩ millionEdge

/-- A checked final segment closes both square-root estimates at one million. -/
theorem high_closed {s : Edge} (hs : Valid s) (h : Segment Valid highEstimate s millionEdge) {x : ℝ}
    (hl : (s.n : ℝ) ≤ x) (hr : x ≤ 1000000) : highEstimate x := by
  obtain ⟨ht, hi⟩ := h hs
  rcases hr.lt_or_eq with hx | rfl
  · exact hi x hl hx
  · exact million_endpoint ht

/-- Once the final segment is supplied, the two lower theta bands and the certified
million endpoint give the normalized Lee–Nosal bound over the entire finite interval. -/
theorem theta_million_of_segment (h : HighSegment) {x : ℝ} (hl : 2657 ≤ x) (hr : x ≤ 1000000) :
    |Chebyshev.theta x - x| / Real.sqrt x ≤
      Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
  rcases le_total x 3500 with hx | hx
  · exact theta_lee_nosal_2657_3500 hl hx
  · exact
      theta_ratio_of_coeff (by linarith only [hl]) (high_closed prefix3500.1 h hx hr).2
        (coefficient3500 hx)

/-- A high segment extends the four-fifths psi estimate across the finite interval. -/
theorem psi_four_fifths_of_segment (h : HighSegment) {x : ℝ} (hl : 1423 ≤ x) (hr : x ≤ 1000000) :
    |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x := by
  rcases lt_or_ge x 2657 with hx | hx
  · exact theta_entry.2 x hl hx
  rcases lt_or_ge x 3100 with hy | hy
  · exact (prefix3100.2 x hx hy).1
  rcases lt_or_ge x 3500 with hz | hz
  · exact (prefix3500.2 x hy hz).1
  exact (high_closed prefix3500.1 h hz hr).1

/-- The same high segment extends the 81 percent estimate from seventeen. -/
theorem psi_81_of_segment (h : HighSegment) {x : ℝ} (hl : 17 ≤ x) (hr : x ≤ 1000000) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  rcases lt_or_ge x 101 with hx | hx
  · exact low_prefix.2.2 x hl hx
  rcases lt_or_ge x 1423 with hy | hy
  · exact middle_prefix.2 x hx hy
  exact
    (psi_four_fifths_of_segment h hy hr).trans
      (mul_le_mul_of_nonneg_right (by norm_num only) (Real.sqrt_nonneg x))

/-- The 94 percent estimate combines the initial cells with the 81 percent result. -/
theorem psi_94_of_segment (h : HighSegment) {x : ℝ} (hl : 11 ≤ x) (hr : x ≤ 1000000) :
    |Chebyshev.psi x - x| ≤ (47 / 50 : ℝ) * Real.sqrt x := by
  rcases lt_or_ge x 17 with hx | hx
  · exact low_prefix.2.1 x hl hx
  exact
    (psi_81_of_segment h hx hr).trans
      (mul_le_mul_of_nonneg_right (by norm_num only) (Real.sqrt_nonneg x))

/-- The first high segment extends the normalized theta bound up to the cursor at 6539. -/
theorem theta_lee_nosal_before_6539 {x : ℝ} (hl : 2657 ≤ x) (hr : x < 6539) :
    |Chebyshev.theta x - x| / Real.sqrt x ≤
      Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
  rcases le_total x 3500 with hx | hx
  · exact theta_lee_nosal_2657_3500 hl hx
  · exact
      theta_ratio_of_coeff (by linarith only [hl]) (first_high_prefix.2 x hx hr).2
        (coefficient3500 hx)

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
