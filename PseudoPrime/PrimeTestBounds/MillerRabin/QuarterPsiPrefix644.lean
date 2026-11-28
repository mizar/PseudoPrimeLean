/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin3500To41539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin41539To81539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch81539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch86539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch91539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.Band3500
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.SignedWalk

/-! # Shared signed Chebyshev bounds through logarithm 644 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The certified state at the beginning of the local signed walk.
Its Mangoldt sums include all indices strictly below 96539. -/
private def signedStart644 : AnalyticNumberTheory.Cert.Chebyshev.Joint.Edge :=
  ⟨96539, 96648815437795990, 96649678592660318, 354688711387439, 354692955040586⟩

/-- The four lower bounds in fixed-point ticks. When a unit interval
meets two radius rows, its required bound is the larger of the two. -/
private def signedTicks644 (n : ℕ) : ℤ :=
  if n < 99856 then -1000000000000000
  else
    if n < 102400 then -36080000000000
    else
      if n ≤ 103524 then -20780000000000
      else if n < 103556 then -32670000000000 else -21580000000000

/-- Extend the shared walk with a uniform signed deficit for section 132. -/
private def signedTicks656 (n : ℕ) : ℤ :=
  if n ≤ 103684 then signedTicks644 n else -70400000000000

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
-- The shared certificate reduces 11046 consecutive steps in the kernel.
/-- Check the section 132 deficit with the previously certified initial state. -/
private theorem signed656_check :
    AnalyticNumberTheory.Cert.Chebyshev.Joint.signedWalk
        (AnalyticNumberTheory.Cert.Chebyshev.Joint.gcdStep 96539 107585) signedTicks656 11046
        signedStart644 =
      true := by
  decide +kernel

/-- The existing joint estimates supply the initial certified scalar state. -/
private theorem signed644_start_valid :
    AnalyticNumberTheory.Cert.Chebyshev.Joint.Valid signedStart644 := by
  have h₁ :=
    (AnalyticNumberTheory.Cert.Chebyshev.Joint.joined3500To41539
        AnalyticNumberTheory.Cert.Chebyshev.Joint.prefix3500.1).1
  have h₂ := (AnalyticNumberTheory.Cert.Chebyshev.Joint.joined41539To81539 h₁).1
  have h₃ := (AnalyticNumberTheory.Cert.Chebyshev.Joint.batch81539 h₂).1
  have h₄ := (AnalyticNumberTheory.Cert.Chebyshev.Joint.batch86539 h₃).1
  exact (AnalyticNumberTheory.Cert.Chebyshev.Joint.batch91539 h₄).1

/-- At a real argument in the squared-radius range, the ceiling selects
the certified unit interval and hence the lower bound in ticks. -/
private theorem signed644_of_ceil {x : ℝ} (hl : 99856 ≤ x) (hu : x ≤ 103684) :
    (signedTicks644 ⌈x⌉₊ : ℝ) / AnalyticNumberTheory.Cert.Chebyshev.Joint.scale ≤
      Chebyshev.psi x - x := by
  have hn : (96539 : ℕ) ≤ ⌈x⌉₊ :=
    Nat.cast_le.mp ((show (96539 : ℝ) ≤ 99856 by norm_num only).trans (hl.trans (Nat.le_ceil x)))
  have hm : ⌈x⌉₊ ≤ 103684 := Nat.ceil_le.mpr hu
  have hx : ((⌈x⌉₊ - 1 : ℕ) : ℝ) ≤ x :=
    (Nat.cast_le.mpr (Nat.sub_le_of_le_add (Nat.ceil_le_floor_add_one x))).trans
      (Nat.floor_le (by linarith only [hl]))
  have h :=
    AnalyticNumberTheory.Cert.Chebyshev.Joint.signed_walk_sound signedTicks656 11046 signedStart644
      signed644_start_valid (by decide) (by decide) (by decide) signed656_check _ hn
      (hm.trans_lt (by decide : 103684 < 107585)) x hx (Nat.le_ceil x)
  simpa only [signedTicks656, ite_eq_left hm] using h

private theorem signed_of_ceil {x : ℝ} (hl : 99856 ≤ x) (hu : x ≤ 103684) {D : ℝ}
    (hD : D ≤ (signedTicks644 ⌈x⌉₊ : ℝ) / AnalyticNumberTheory.Cert.Chebyshev.Joint.scale) :
    D ≤ Chebyshev.psi x - x := by exact hD.trans (signed644_of_ceil hl hu)

/-- One signed Chebyshev walk covers the four section 122 radius rows.
Bounds are for real arguments, including the fractional shared endpoints. -/
theorem quarter_psi_signed_rows_644 :
    (∀ r ∈ Set.Icc 316 320, -36.080 ≤ Chebyshev.psi (r ^ 2) - r ^ 2) ∧
      (∀ r ∈ Set.Icc 320 (1287 / 4), -20.780 ≤ Chebyshev.psi (r ^ 2) - r ^ 2) ∧
      (∀ r ∈ Set.Icc (1287 / 4) (1609 / 5), -32.670 ≤ Chebyshev.psi (r ^ 2) - r ^ 2) ∧
      (∀ r ∈ Set.Icc (1609 / 5) 322, -21.580 ≤ Chebyshev.psi (r ^ 2) - r ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    have ha := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 316) hr.1 2
    have hu := pow_le_pow_left₀ ((by norm_num only : (0 : ℝ) ≤ 316).trans hr.1) hr.2 2
    have hx : 99856 ≤ r ^ 2 := by linarith only [ha]
    have hy : r ^ 2 ≤ 102400 := by linarith only [hu]
    apply signed_of_ceil (by linarith only [hx]) (by linarith only [hy])
    let n := ⌈r ^ 2⌉₊
    change _ ≤ (signedTicks644 n : ℝ) / AnalyticNumberTheory.Cert.Chebyshev.Joint.scale
    have hn : 99856 ≤ n := Nat.cast_le.mp (hx.trans (Nat.le_ceil _))
    have hm : n ≤ 102400 := Nat.ceil_le.mpr hy
    by_cases h : n < 102400
    · simp only [signedTicks644, ite_eq_right (not_lt_of_ge hn), ite_eq_left h]
      norm_num only [AnalyticNumberTheory.Cert.Chebyshev.Joint.scale]
    have h' := hm.trans (by decide : 102400 ≤ 103524)
    simp only [signedTicks644, ite_eq_right (not_lt_of_ge hn), ite_eq_right h, ite_eq_left h']
    norm_num only [AnalyticNumberTheory.Cert.Chebyshev.Joint.scale]
  · intro r hr
    have ha := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 320) hr.1 2
    have hu := pow_le_pow_left₀ ((by norm_num only : (0 : ℝ) ≤ 320).trans hr.1) hr.2 2
    have hx : 102400 ≤ r ^ 2 := by linarith only [ha]
    have hy : r ^ 2 ≤ 103524 := by linarith only [hu]
    apply signed_of_ceil (by linarith only [hx]) (by linarith only [hy])
    let n := ⌈r ^ 2⌉₊
    change _ ≤ (signedTicks644 n : ℝ) / AnalyticNumberTheory.Cert.Chebyshev.Joint.scale
    have hn : 102400 ≤ n := Nat.cast_le.mp (hx.trans (Nat.le_ceil _))
    have hm : n ≤ 103524 := Nat.ceil_le.mpr hy
    have H : 99856 ≤ n := (by decide : 99856 ≤ 102400).trans hn
    simp only [signedTicks644, ite_eq_right (not_lt_of_ge H), ite_eq_right (not_lt_of_ge hn),
      ite_eq_left hm]
    norm_num only [AnalyticNumberTheory.Cert.Chebyshev.Joint.scale]
  · intro r hr
    have ha := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 1287 / 4) hr.1 2
    have hu := pow_le_pow_left₀ ((by norm_num only : (0 : ℝ) ≤ 1287 / 4).trans hr.1) hr.2 2
    have hx : 103523.0625 ≤ r ^ 2 := by linarith only [ha]
    have hy : r ^ 2 ≤ 103556 := by linarith only [hu]
    apply signed_of_ceil (by linarith only [hx]) (by linarith only [hy])
    let n := ⌈r ^ 2⌉₊
    change _ ≤ (signedTicks644 n : ℝ) / AnalyticNumberTheory.Cert.Chebyshev.Joint.scale
    have hn : 103524 ≤ n := by
      apply Nat.succ_le_of_lt
      exact Nat.cast_lt.mp (show (103523 : ℝ) < n by linarith only [hx, Nat.le_ceil (r ^ 2)])
    have H : ¬n < 99856 := not_lt_of_ge ((by decide : 99856 ≤ 103524).trans hn)
    have J : ¬n < 102400 := not_lt_of_ge ((by decide : 102400 ≤ 103524).trans hn)
    by_cases h : n ≤ 103524
    · simp only [signedTicks644, ite_eq_right H, ite_eq_right J, ite_eq_left h]
      norm_num only [AnalyticNumberTheory.Cert.Chebyshev.Joint.scale]
    by_cases hh : n < 103556
    · simp only [signedTicks644, ite_eq_right H, ite_eq_right J, ite_eq_right h, ite_eq_left hh]
      norm_num only [AnalyticNumberTheory.Cert.Chebyshev.Joint.scale]
    simp only [signedTicks644, ite_eq_right H, ite_eq_right J, ite_eq_right h, ite_eq_right hh]
    norm_num only [AnalyticNumberTheory.Cert.Chebyshev.Joint.scale]
  · intro r hr
    have ha := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 1609 / 5) hr.1 2
    have hu := pow_le_pow_left₀ ((by norm_num only : (0 : ℝ) ≤ 1609 / 5).trans hr.1) hr.2 2
    have hx : 103555.24 ≤ r ^ 2 := by linarith only [ha]
    have hy : r ^ 2 ≤ 103684 := by linarith only [hu]
    apply signed_of_ceil (by linarith only [hx]) (by linarith only [hy])
    let n := ⌈r ^ 2⌉₊
    change _ ≤ (signedTicks644 n : ℝ) / AnalyticNumberTheory.Cert.Chebyshev.Joint.scale
    have hn : 103556 ≤ n := by
      apply Nat.succ_le_of_lt
      exact Nat.cast_lt.mp (show (103555 : ℝ) < n by linarith only [hx, Nat.le_ceil (r ^ 2)])
    have H : ¬n < 99856 := not_lt_of_ge ((by decide : 99856 ≤ 103556).trans hn)
    have J : ¬n < 102400 := not_lt_of_ge ((by decide : 102400 ≤ 103556).trans hn)
    have K : ¬n ≤ 103524 := not_le_of_gt ((by decide : 103524 < 103556).trans_le hn)
    simp only [signedTicks644, ite_eq_right H, ite_eq_right J, ite_eq_right K,
      ite_eq_right (not_lt_of_ge hn)]
    norm_num only [AnalyticNumberTheory.Cert.Chebyshev.Joint.scale]

/-- For real arguments from 103684 to 107584, the signed Chebyshev
deficit is bounded below by -70.4. -/
theorem quarter_psi_signed_656 {x : ℝ} (hl : 103684 ≤ x) (hu : x ≤ 107584) :
    -70.4 ≤ Chebyshev.psi x - x := by
  have hn : (103684 : ℕ) ≤ ⌈x⌉₊ := Nat.cast_le.mp (hl.trans (Nat.le_ceil x))
  have hm : ⌈x⌉₊ ≤ 107584 := Nat.ceil_le.mpr hu
  have hx : ((⌈x⌉₊ - 1 : ℕ) : ℝ) ≤ x :=
    (Nat.cast_le.mpr (Nat.sub_le_of_le_add (Nat.ceil_le_floor_add_one x))).trans
      (Nat.floor_le (by linarith only [hl]))
  have h :=
    AnalyticNumberTheory.Cert.Chebyshev.Joint.signed_walk_sound signedTicks656 11046 signedStart644
      signed644_start_valid (by decide) (by decide) (by decide) signed656_check _
      ((by decide : 96539 ≤ 103684).trans hn) (hm.trans_lt (by decide : 107584 < 107585)) x hx
      (Nat.le_ceil x)
  by_cases he : ⌈x⌉₊ ≤ 103684
  · have hEq := le_antisymm he hn
    have ht : signedTicks656 103684 = -21580000000000 := by decide
    rw [hEq, ht] at h
    norm_num only [AnalyticNumberTheory.Cert.Chebyshev.Joint.scale, Int.cast_neg, Int.cast_ofNat,
      Nat.cast_ofNat, Nat.reducePow] at h
    linarith only [h]
  · norm_num only [signedTicks656, ite_eq_right he, AnalyticNumberTheory.Cert.Chebyshev.Joint.scale,
      Int.cast_neg, Int.cast_ofNat, Nat.cast_ofNat, Nat.reducePow] at h
    linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
