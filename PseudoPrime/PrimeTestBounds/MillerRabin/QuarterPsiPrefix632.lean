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

/-! # Shared signed Chebyshev bounds for the five comparisons through logarithm 632 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The certified state at the beginning of the local signed walk.
Its Mangoldt sums include all indices strictly below 96539. -/
private def signedStart632 : AnalyticNumberTheory.Cert.Chebyshev.Joint.Edge :=
  ⟨96539, 96648815437795990, 96649678592660318, 354688711387439, 354692955040586⟩

/-- Fixed-point lower bounds for the five comparisons, relaxed by at most 0.011 to
reuse the existing certified prefix. At a fractional shared endpoint the
stricter adjacent bound governs the unit interval containing that endpoint. -/
private def signedTicks632 (n : ℕ) : ℤ :=
  if n < 97969 then -1000000000000000
  else
    if n ≤ 98344 then -28592000000000
    else
      if n ≤ 98596 then -20120000000000
      else
        if n ≤ 98878 then -23674500000000 else if n < 99225 then -9170000000000 else 10585000000000

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
-- The joint kernel checks one local walk with 3318 cursor updates.
/-- One calculation certifies the five signed bounds with a shared running sum. -/
private theorem signed632_check :
    AnalyticNumberTheory.Cert.Chebyshev.Joint.signedWalk
        (AnalyticNumberTheory.Cert.Chebyshev.Joint.gcdStep 96539 99857) signedTicks632 3318
        signedStart632 =
      true := by
  decide +kernel

/-- The existing joint estimates supply the initial certified scalar state. -/
private theorem signed632_start_valid :
    AnalyticNumberTheory.Cert.Chebyshev.Joint.Valid signedStart632 := by
  have h₁ :=
    (AnalyticNumberTheory.Cert.Chebyshev.Joint.joined3500To41539
        AnalyticNumberTheory.Cert.Chebyshev.Joint.prefix3500.1).1
  have h₂ := (AnalyticNumberTheory.Cert.Chebyshev.Joint.joined41539To81539 h₁).1
  have h₃ := (AnalyticNumberTheory.Cert.Chebyshev.Joint.batch81539 h₂).1
  have h₄ := (AnalyticNumberTheory.Cert.Chebyshev.Joint.batch86539 h₃).1
  exact (AnalyticNumberTheory.Cert.Chebyshev.Joint.batch91539 h₄).1

/-- At a real argument in the squared-radius range, the ceiling selects
the certified unit interval and hence the lower bound in ticks. -/
private theorem signed632_of_ceil {x : ℝ} (hl : 97969 ≤ x) (hu : x ≤ 99856) :
    (signedTicks632 ⌈x⌉₊ : ℝ) / AnalyticNumberTheory.Cert.Chebyshev.Joint.scale ≤
      Chebyshev.psi x - x := by
  have hn : (96539 : ℕ) ≤ ⌈x⌉₊ :=
    Nat.cast_le.mp ((show (96539 : ℝ) ≤ 97969 by norm_num only).trans (hl.trans (Nat.le_ceil x)))
  have hm : ⌈x⌉₊ ≤ 99856 := Nat.ceil_le.mpr hu
  have hx : ((⌈x⌉₊ - 1 : ℕ) : ℝ) ≤ x :=
    (Nat.cast_le.mpr (Nat.sub_le_of_le_add (Nat.ceil_le_floor_add_one x))).trans
      (Nat.floor_le (by linarith only [hl]))
  exact
    AnalyticNumberTheory.Cert.Chebyshev.Joint.signed_walk_sound signedTicks632 3318 signedStart632
      signed632_start_valid (by decide) (by decide) (by decide) signed632_check _ hn
      (hm.trans_lt (by decide : 99856 < 99857)) x hx (Nat.le_ceil x)

/-- The signed Chebyshev lower bound for radii from 313 to 1568 / 5. -/
theorem quarter_psi_signed_3136 {r : ℝ} (hl : 313 ≤ r) (hu : r ≤ 1568 / 5) :
    -28.592 ≤ Chebyshev.psi (r ^ 2) - r ^ 2 := by
  have hxl := pow_le_pow_left₀ (by norm_num only : 0 ≤ (313 : ℝ)) hl 2
  have hxu := pow_le_pow_left₀ (by linarith only [hl] : 0 ≤ r) hu 2
  have hs := signed632_of_ceil (x := r ^ 2) (by linarith only [hxl]) (by linarith only [hxu])
  apply le_trans _ hs
  let n := ⌈r ^ 2⌉₊
  change -28.592 ≤ (signedTicks632 n : ℝ) / AnalyticNumberTheory.Cert.Chebyshev.Joint.scale
  have hn : 97969 ≤ n := by
    exact Nat.cast_le.mp ((by linarith only [hxl] : (97969 : ℝ) ≤ r ^ 2).trans (Nat.le_ceil _))
  have hm : n ≤ 98345 :=
    Nat.ceil_le.mpr
      (by
        norm_num only [Nat.cast_ofNat]
        linarith only [hxu])
  by_cases h : n ≤ 98344
  · simp only [signedTicks632, ite_eq_right (not_lt_of_ge hn), ite_eq_left h]
    norm_num only [AnalyticNumberTheory.Cert.Chebyshev.Joint.scale]
  · have h' : n ≤ 98596 := hm.trans (by decide)
    simp only [signedTicks632, ite_eq_right (not_lt_of_ge hn), ite_eq_right h, ite_eq_left h']
    norm_num only [AnalyticNumberTheory.Cert.Chebyshev.Joint.scale]

/-- The signed Chebyshev lower bound for radii from 1568 / 5 to 314. -/
theorem quarter_psi_signed_314 {r : ℝ} (hl : 1568 / 5 ≤ r) (hu : r ≤ 314) :
    -20.120 ≤ Chebyshev.psi (r ^ 2) - r ^ 2 := by
  have hxl := pow_le_pow_left₀ (by norm_num only : 0 ≤ (1568 / 5 : ℝ)) hl 2
  have hxu := pow_le_pow_left₀ (by linarith only [hl] : 0 ≤ r) hu 2
  have hs := signed632_of_ceil (x := r ^ 2) (by linarith only [hxl]) (by linarith only [hxu])
  apply le_trans _ hs
  let n := ⌈r ^ 2⌉₊
  change -20.120 ≤ (signedTicks632 n : ℝ) / AnalyticNumberTheory.Cert.Chebyshev.Joint.scale
  have hn : 98345 ≤ n := by
    exact
      Nat.succ_le_of_lt
        (lt_of_not_ge
          (fun h ↦
            (not_le_of_gt (by linarith only [hxl] : (98344 : ℝ) < r ^ 2)) (Nat.ceil_le.mp h)))
  have hm : n ≤ 98596 :=
    Nat.ceil_le.mpr
      (by
        norm_num only [Nat.cast_ofNat]
        linarith only [hxu])
  have h' : ¬n ≤ 98344 := not_le_of_gt (lt_of_lt_of_le (by decide) hn)
  have h₀ : ¬n < 97969 := not_lt_of_ge ((by decide : 97969 ≤ 98345).trans hn)
  simp only [signedTicks632, ite_eq_right h₀, ite_eq_right h', ite_eq_left hm]
  norm_num only [AnalyticNumberTheory.Cert.Chebyshev.Joint.scale]

/-- The signed Chebyshev lower bound for radii from 314 to 6289 / 20. -/
theorem quarter_psi_signed_31445 {r : ℝ} (hl : 314 ≤ r) (hu : r ≤ 6289 / 20) :
    -23.6745 ≤ Chebyshev.psi (r ^ 2) - r ^ 2 := by
  have hxl := pow_le_pow_left₀ (by norm_num only : 0 ≤ (314 : ℝ)) hl 2
  have hxu := pow_le_pow_left₀ (by linarith only [hl] : 0 ≤ r) hu 2
  have hs := signed632_of_ceil (x := r ^ 2) (by linarith only [hxl]) (by linarith only [hxu])
  apply le_trans _ hs
  let n := ⌈r ^ 2⌉₊
  change -23.6745 ≤ (signedTicks632 n : ℝ) / AnalyticNumberTheory.Cert.Chebyshev.Joint.scale
  have hn : 98596 ≤ n := by
    exact Nat.cast_le.mp ((by linarith only [hxl] : (98596 : ℝ) ≤ r ^ 2).trans (Nat.le_ceil _))
  have hm : n ≤ 98879 :=
    Nat.ceil_le.mpr
      (by
        norm_num only [Nat.cast_ofNat]
        linarith only [hxu])
  have h₀ : ¬n < 97969 := not_lt_of_ge ((by decide : 97969 ≤ 98596).trans hn)
  have h₁ : ¬n ≤ 98344 := not_le_of_gt ((by decide : 98344 < 98596).trans_le hn)
  by_cases h₂ : n ≤ 98596
  · simp only [signedTicks632, ite_eq_right h₀, ite_eq_right h₁, ite_eq_left h₂]
    norm_num only [AnalyticNumberTheory.Cert.Chebyshev.Joint.scale]
  · by_cases h₃ : n ≤ 98878
    · simp only [signedTicks632, ite_eq_right h₀, ite_eq_right h₁, ite_eq_right h₂, ite_eq_left h₃]
      norm_num only [AnalyticNumberTheory.Cert.Chebyshev.Joint.scale]
    · have h₄ : n < 99225 := hm.trans_lt (by decide)
      simp only [signedTicks632, ite_eq_right h₀, ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₃,
        ite_eq_left h₄]
      norm_num only [AnalyticNumberTheory.Cert.Chebyshev.Joint.scale]

/-- The signed Chebyshev lower bound for radii from 6289 / 20 to 315. -/
theorem quarter_psi_signed_315 {r : ℝ} (hl : 6289 / 20 ≤ r) (hu : r ≤ 315) :
    -9.170 ≤ Chebyshev.psi (r ^ 2) - r ^ 2 := by
  have hxl := pow_le_pow_left₀ (by norm_num only : 0 ≤ (6289 / 20 : ℝ)) hl 2
  have hxu := pow_le_pow_left₀ (by linarith only [hl] : 0 ≤ r) hu 2
  have hs := signed632_of_ceil (x := r ^ 2) (by linarith only [hxl]) (by linarith only [hxu])
  apply le_trans _ hs
  let n := ⌈r ^ 2⌉₊
  change -9.170 ≤ (signedTicks632 n : ℝ) / AnalyticNumberTheory.Cert.Chebyshev.Joint.scale
  have hn : 98879 ≤ n := by
    exact
      Nat.succ_le_of_lt
        (lt_of_not_ge
          (fun h ↦
            (not_le_of_gt (by linarith only [hxl] : (98878 : ℝ) < r ^ 2)) (Nat.ceil_le.mp h)))
  have h₀ : ¬n < 97969 := not_lt_of_ge ((by decide : 97969 ≤ 98879).trans hn)
  have h₁ : ¬n ≤ 98344 := not_le_of_gt ((by decide : 98344 < 98879).trans_le hn)
  have h₂ : ¬n ≤ 98596 := not_le_of_gt ((by decide : 98596 < 98879).trans_le hn)
  have h₃ : ¬n ≤ 98878 := not_le_of_gt ((by decide : 98878 < 98879).trans_le hn)
  by_cases h₄ : n < 99225
  · simp only [signedTicks632, ite_eq_right h₀, ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₃,
      ite_eq_left h₄]
    norm_num only [AnalyticNumberTheory.Cert.Chebyshev.Joint.scale]
  · simp only [signedTicks632, ite_eq_right h₀, ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₃,
      ite_eq_right h₄]
    norm_num only [AnalyticNumberTheory.Cert.Chebyshev.Joint.scale]

/-- The signed Chebyshev lower bound for radii from 315 to 316. -/
theorem quarter_psi_signed_316 {r : ℝ} (hl : 315 ≤ r) (hu : r ≤ 316) :
    10.585 ≤ Chebyshev.psi (r ^ 2) - r ^ 2 := by
  have hxl := pow_le_pow_left₀ (by norm_num only : 0 ≤ (315 : ℝ)) hl 2
  have hxu := pow_le_pow_left₀ (by linarith only [hl] : 0 ≤ r) hu 2
  have hs := signed632_of_ceil (x := r ^ 2) (by linarith only [hxl]) (by linarith only [hxu])
  apply le_trans _ hs
  let n := ⌈r ^ 2⌉₊
  change 10.585 ≤ (signedTicks632 n : ℝ) / AnalyticNumberTheory.Cert.Chebyshev.Joint.scale
  have hn : 99225 ≤ n := by
    exact Nat.cast_le.mp ((by linarith only [hxl] : (99225 : ℝ) ≤ r ^ 2).trans (Nat.le_ceil _))
  have h₀ : ¬n < 97969 := not_lt_of_ge ((by decide : 97969 ≤ 99225).trans hn)
  have h₁ : ¬n ≤ 98344 := not_le_of_gt ((by decide : 98344 < 99225).trans_le hn)
  have h₂ : ¬n ≤ 98596 := not_le_of_gt ((by decide : 98596 < 99225).trans_le hn)
  have h₃ : ¬n ≤ 98878 := not_le_of_gt ((by decide : 98878 < 99225).trans_le hn)
  simp only [signedTicks632, ite_eq_right h₀, ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₃,
    ite_eq_right (not_lt_of_ge hn)]
  norm_num only [AnalyticNumberTheory.Cert.Chebyshev.Joint.scale]

end PseudoPrime.PrimeTestBounds.MillerRabin
