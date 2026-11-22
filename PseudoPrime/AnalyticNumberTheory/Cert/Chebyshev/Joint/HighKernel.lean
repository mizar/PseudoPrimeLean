/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.BandSound
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.GcdStep

/-! # Independent kernel replay of high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- The two high-range square-root estimates supplied by the shared integer scan. -/
def highEstimate (x : ℝ) : Prop :=
  |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x ∧
    |Chebyshev.theta x - x| ≤ (97 / 50 : ℝ) * Real.sqrt x

/-- A successful high-band batch check exports only its two scalar states and the real estimates. -/
theorem high_batch {s t : Edge} (lo : 3500 ≤ s.n) (hi : t.n ≤ 1000000) (extra : ℕ → ℕ) (count : ℕ)
    (check : batchAccepted s.n t.n extra (fun _ ↦ (4, 5)) count s t = true) :
    Segment Valid highEstimate s t := by
  apply accepted_band (by linarith only [hi]) (by linarith only [lo]) 97 50 _ extra count check
  intro n hn _
  have h := lo.trans hn
  rw [thetaBand, ite_eq_right (Nat.not_lt_of_ge ((by decide : 3100 ≤ 3500).trans h)),
    ite_eq_right (Nat.not_lt_of_ge h)]

/-- A gcd-based replay supplies the same segment theorem and checks every outgoing tick. -/
theorem gcd_batch {s t : Edge} (lo : 3500 ≤ s.n) (hi : t.n ≤ 1000000) (extra : ℕ → ℕ) (count : ℕ)
    (check : replayWith (gcdStep s.n t.n) s.n t.n extra (fun _ ↦ (4, 5)) count s = some t) :
    Segment Valid highEstimate s t := by
  rw [gcdStep_eq] at check
  exact high_batch lo hi extra count (decide_eq_true check)

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
