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
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch81539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch86539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch91539
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.SignedWalk
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.GcdStep

/-! # Signed Chebyshev lower bounds for the section 107 intervals -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def start : Edge :=
  ⟨96539, 96648815437795990, 96649678592660318, 354688711387439, 354692955040586⟩

private def first : Edge :=
  ⟨86539, 86566559281221489, 86567344155290023, 348961863957856, 348966058918126⟩

private def middle : Edge :=
  ⟨91539, 91524323397062698, 91525148737217362, 348961863957856, 348966058918126⟩

private theorem first_valid : Valid first := by
  exact (batch81539 (joined41539To81539 (joined3500To41539 prefix3500.1).1).1).1

private theorem middle_valid : Valid middle :=
  (batch86539 first_valid).1

private theorem start_valid : Valid start :=
  (batch91539 middle_valid).1

private def sectionLower (n : ℕ) : ℤ :=
  if 97346 ≤ n then 7900000000000
  else
    if 94865 ≤ n then 25000000000000
    else
      if 92417 ≤ n then -36000000000000
      else if 90001 ≤ n then -89000000000000 else -1000000000000000

set_option maxRecDepth 16384 in
private theorem first_check : signedWalk (gcdStep 86539 91539) sectionLower 5000 first = true := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem middle_check :
    signedWalk (gcdStep 91539 96539) sectionLower 5000 middle = true := by decide +kernel

set_option maxRecDepth 8192 in
private theorem last_check : signedWalk (gcdStep 96539 97971) sectionLower 1432 start = true := by
  decide +kernel

private theorem floor_bound {a b k : ℕ} {s : Edge} (hv : Valid s) (ha : a ≤ s.n) (hb : s.n + k ≤ b)
    (hcap : b ≤ 1000001) (hc : signedWalk (gcdStep a b) sectionLower k s = true) {x : ℝ}
    (hx : 0 ≤ x) (hl : s.n ≤ ⌊x⌋₊ + 1) (hu : ⌊x⌋₊ + 1 < s.n + k) :
    (sectionLower (⌊x⌋₊ + 1) : ℝ) / scale ≤ Chebyshev.psi x - x := by
  exact
    signed_walk_sound sectionLower k s hv ha hb hcap hc _ hl hu x
      (by simpa only [Nat.add_sub_cancel] using Nat.floor_le hx)
      (by simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one x).le)

/-- The three checkpoint segments give the signed lower envelope at every
real argument between the first and last square cutoffs of section 107. -/
private theorem section_bound {x : ℝ} (hl : 90000 ≤ x) (hu : x ≤ 97969) :
    (sectionLower (⌊x⌋₊ + 1) : ℝ) / scale ≤ Chebyshev.psi x - x := by
  let n := ⌊x⌋₊ + 1
  have hx : 0 ≤ x := (by norm_num only : (0 : ℝ) ≤ 90000).trans hl
  have hL : 90001 ≤ n := Nat.succ_le_succ (Nat.le_floor hl)
  have hU : n ≤ 97970 := Nat.succ_le_succ (Nat.floor_le_of_le hu)
  by_cases h₁ : n < 91539
  · exact
      floor_bound first_valid (by decide) (by decide) (by decide) first_check hx
        ((by decide : first.n ≤ 90001).trans hL) h₁
  by_cases h₂ : n < 96539
  · exact
      floor_bound middle_valid (by decide) (by decide) (by decide) middle_check hx (le_of_not_gt h₁)
        h₂
  exact
    floor_bound start_valid (by decide) (by decide) (by decide) last_check hx (le_of_not_gt h₂)
      (Nat.lt_succ_of_le hU)

/-- For arguments in the first squared-radius interval of section 107,
the signed error is at least minus 89. -/
theorem psi_section107_first {x : ℝ} (hl : 90000 ≤ x) (hu : x ≤ 92416) :
    -89 ≤ Chebyshev.psi x - x := by
  have h := section_bound hl (hu.trans (by norm_num only))
  have hn : 90001 ≤ ⌊x⌋₊ + 1 := Nat.succ_le_succ (Nat.le_floor hl)
  have hm : ⌊x⌋₊ + 1 ≤ 92417 := Nat.succ_le_succ (Nat.floor_le_of_le hu)
  have ha : ¬97346 ≤ ⌊x⌋₊ + 1 := (hm.trans_lt (by decide)).not_ge
  have hb : ¬94865 ≤ ⌊x⌋₊ + 1 := (hm.trans_lt (by decide)).not_ge
  by_cases hc : 92417 ≤ ⌊x⌋₊ + 1
  · norm_num only [sectionLower, ite_eq_right ha, ite_eq_right hb, ite_eq_left hc, scale,
      Int.cast_neg, Int.cast_ofNat] at h
    linarith only [h]
  · norm_num only [sectionLower, ite_eq_right ha, ite_eq_right hb, ite_eq_right hc, ite_eq_left hn,
      scale, Int.cast_neg, Int.cast_ofNat] at h
    exact h

/-- For arguments in the second squared-radius interval of section 107,
the signed error is at least minus 36. -/
theorem psi_section107_second {x : ℝ} (hl : 92416 ≤ x) (hu : x ≤ 94864) :
    -36 ≤ Chebyshev.psi x - x := by
  have h :=
    section_bound ((by norm_num only : (90000 : ℝ) ≤ 92416).trans hl) (hu.trans (by norm_num only))
  have hn : 92417 ≤ ⌊x⌋₊ + 1 := Nat.succ_le_succ (Nat.le_floor hl)
  have hm : ⌊x⌋₊ + 1 ≤ 94865 := Nat.succ_le_succ (Nat.floor_le_of_le hu)
  have ha : ¬97346 ≤ ⌊x⌋₊ + 1 := (hm.trans_lt (by decide)).not_ge
  by_cases hb : 94865 ≤ ⌊x⌋₊ + 1
  · norm_num only [sectionLower, ite_eq_right ha, ite_eq_left hb, scale, Int.cast_ofNat] at h
    linarith only [h]
  · norm_num only [sectionLower, ite_eq_right ha, ite_eq_right hb, ite_eq_left hn, scale,
      Int.cast_neg, Int.cast_ofNat] at h
    exact h

/-- For arguments in the third squared-radius interval of section 107,
the signed error is at least 25. -/
theorem psi_section107_third {x : ℝ} (hl : 94864 ≤ x) (hu : x ≤ 97344) :
    25 ≤ Chebyshev.psi x - x := by
  have h :=
    section_bound ((by norm_num only : (90000 : ℝ) ≤ 94864).trans hl) (hu.trans (by norm_num only))
  have hn : 94865 ≤ ⌊x⌋₊ + 1 := Nat.succ_le_succ (Nat.le_floor hl)
  have hm : ⌊x⌋₊ + 1 ≤ 97345 := Nat.succ_le_succ (Nat.floor_le_of_le hu)
  have ha : ¬97346 ≤ ⌊x⌋₊ + 1 := (hm.trans_lt (by decide)).not_ge
  norm_num only [sectionLower, ite_eq_right ha, ite_eq_left hn, scale, Int.cast_ofNat] at h
  exact h

/-- From the certified prefix at 96539, the signed walk gives
\(\psi(x)-x\ge79/10\) throughout the last squared-radius interval of section 107. -/
theorem psi_section107_last {x : ℝ} (hl : 97344 ≤ x) (hu : x ≤ 97969) :
    79 / 10 ≤ Chebyshev.psi x - x := by
  have hn : 97345 ≤ ⌊x⌋₊ + 1 := Nat.succ_le_succ (Nat.le_floor hl)
  have h := section_bound ((by norm_num only : (90000 : ℝ) ≤ 97344).trans hl) hu
  by_cases h₁ : 97346 ≤ ⌊x⌋₊ + 1
  · norm_num only [sectionLower, ite_eq_left h₁, scale, Int.cast_ofNat] at h
    exact h
  · have h₂ := (by decide : 94865 ≤ 97345).trans hn
    norm_num only [sectionLower, ite_eq_right h₁, ite_eq_left h₂, scale, Int.cast_ofNat] at h
    linarith only [h]

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
