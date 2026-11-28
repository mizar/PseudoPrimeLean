/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.SignedWalk
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.Band3500
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin3500To41539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin41539To81539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin81539To121539
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.SignedWalk
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.GcdStep

/-! # Signed Chebyshev bounds at the quarter-square and Gaussian join -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def bridgeStart : Edge :=
  ⟨106539, 106549429284512030, 106550353297655247, 375783751498545, 375788393804346⟩

private theorem bridge_start_valid : Valid bridgeStart := by
  have h := (joined41539To81539 (joined3500To41539 prefix3500.1).1).1
  exact (batch101539 (batch96539 (batch91539 (batch86539 (batch81539 h).1).1).1).1).1

private def bridgeLower (n : ℕ) : ℤ :=
  if 109958 ≤ n then -6000000000000
  else
    if 108901 ≤ n then -51708000000000
    else
      if 108242 ≤ n then -88894000000000
      else if 107585 ≤ n then -84645000000000 else -1000000000000000

set_option maxRecDepth 16384 in
private theorem bridge_check :
    signedWalk (gcdStep 106539 110125) bridgeLower 3586 bridgeStart = true := by decide +kernel

private theorem bridge_bound {n : ℕ} (hl : 107585 ≤ n) (hu : n ≤ 110124) {x : ℝ}
    (hx₁ : ((n - 1 : ℕ) : ℝ) ≤ x) (hx₂ : x ≤ (n : ℝ)) :
    (bridgeLower n : ℝ) / scale ≤ Chebyshev.psi x - x := by
  exact
    signed_walk_sound bridgeLower 3586 bridgeStart bridge_start_valid (by decide) (by decide)
      (by decide) bridge_check n ((by decide : bridgeStart.n ≤ 107585).trans hl)
      (Nat.lt_succ_of_le hu) x hx₁ hx₂

private theorem clipped_bridge_bound {a b : ℕ} (ha : 107585 ≤ a + 1) (hab : a < b) (hb : b ≤ 110124)
    {x : ℝ} (hl : (a : ℝ) ≤ x) (hu : x ≤ (b : ℝ)) :
    ∃ n ∈ Finset.Icc (a + 1) b, (bridgeLower n : ℝ) / scale ≤ Chebyshev.psi x - x := by
  have hx : 0 ≤ x := (Nat.cast_nonneg a).trans hl
  let n := min (⌊x⌋₊ + 1) b
  have hn₁ : a + 1 ≤ n := le_min (Nat.succ_le_succ (Nat.le_floor hl)) hab
  have hn₂ : n ≤ b := min_le_right _ _
  have hleft : ((n - 1 : ℕ) : ℝ) ≤ x := by
    have h : n - 1 ≤ ⌊x⌋₊ := Nat.sub_le_of_le_add (min_le_left _ _)
    exact (Nat.cast_le.mpr h).trans (Nat.floor_le hx)
  have hright : x ≤ (n : ℝ) := by
    simpa only [n, Nat.cast_min, Nat.cast_add, Nat.cast_one] using
      le_min (Nat.lt_floor_add_one x).le hu
  exact ⟨n, Finset.mem_Icc.mpr ⟨hn₁, hn₂⟩, bridge_bound (ha.trans hn₁) (hn₂.trans hb) hleft hright⟩

/-- The signed lower bound on the first squared-radius interval. -/
theorem psi_quarter_bridge_658 {x : ℝ} (hl : 107584 ≤ x) (hu : x ≤ 108241) :
    -84.645 ≤ Chebyshev.psi x - x := by
  obtain ⟨n, hn, h⟩ :=
    clipped_bridge_bound (a := 107584) (b := 108241) (by decide) (by decide) (by decide) hl hu
  obtain ⟨ha, hb⟩ := Finset.mem_Icc.mp hn
  norm_num only [bridgeLower, ite_eq_right (hb.trans_lt (by decide : 108241 < 109958)).not_ge,
    ite_eq_right (hb.trans_lt (by decide : 108241 < 108901)).not_ge,
    ite_eq_right (hb.trans_lt (by decide : 108241 < 108242)).not_ge, ite_eq_left ha, scale,
    Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed lower bound on the second squared-radius interval. -/
theorem psi_quarter_bridge_660 {x : ℝ} (hl : 108241 ≤ x) (hu : x ≤ 108900) :
    -88.894 ≤ Chebyshev.psi x - x := by
  obtain ⟨n, hn, h⟩ :=
    clipped_bridge_bound (a := 108241) (b := 108900) (by decide) (by decide) (by decide) hl hu
  obtain ⟨ha, hb⟩ := Finset.mem_Icc.mp hn
  norm_num only [bridgeLower, ite_eq_right (hb.trans_lt (by decide : 108900 < 109958)).not_ge,
    ite_eq_right (hb.trans_lt (by decide : 108900 < 108901)).not_ge, ite_eq_left ha, scale,
    Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed lower bound on the last squared-radius interval. -/
theorem psi_quarter_bridge_663 {x : ℝ} (hl : 108900 ≤ x) (hu : x ≤ 439569 / 4) :
    -51.708 ≤ Chebyshev.psi x - x := by
  obtain ⟨n, hn, h⟩ :=
    clipped_bridge_bound (a := 108900) (b := 109893) (by decide) (by decide) (by decide) hl
      (hu.trans (by norm_num only))
  obtain ⟨ha, hb⟩ := Finset.mem_Icc.mp hn
  norm_num only [bridgeLower, ite_eq_right (hb.trans_lt (by decide : 109893 < 109958)).not_ge,
    ite_eq_left ha, scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The first compressed Gaussian cell has a signed Chebyshev lower bound of
minus six. The same signed walk checks the enclosing squared-radius interval. -/
theorem psi_gaussian_first {x : ℝ} (hl : 109957 ≤ x) (hu : x ≤ 110124) :
    -6 ≤ Chebyshev.psi x - x := by
  obtain ⟨n, hn, h⟩ :=
    clipped_bridge_bound (a := 109957) (b := 110124) (by decide) (by decide) (by decide) hl hu
  norm_num only [bridgeLower, ite_eq_left (Finset.mem_Icc.mp hn).1, scale, Int.cast_neg,
    Int.cast_ofNat] at h
  linarith only [h]

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
