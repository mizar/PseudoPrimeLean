/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.Band3500
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin3500To41539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch41539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch46539

/-! # One-sided psi replay on ten-integer cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Each guard compares the next ten integers against the incoming lower tick
and an integer lower bound for the square root. The exit cursor is retained
for chaining replay batches. -/
def psiLowerWalk (u d : ℕ) (step : Edge → Edge) : ℕ → Edge → Option Edge
  | 0, s => some s
  | k + 1, s =>
    if d * scale * (s.n + 10) ≤ d * s.psiLo + u * scale * s.n.sqrt then
      psiLowerWalk u d step k (walk step 10 s)
    else none

private theorem psiLower_cell {u d : ℕ} (hd : 0 < d) {s : Edge} (hs : Valid s)
    (hg : d * scale * (s.n + 10) ≤ d * s.psiLo + u * scale * s.n.sqrt) {x : ℝ} (hx : (s.n : ℝ) ≤ x)
    (hy : x ≤ s.n + 10) : x - (u : ℝ) / d * Real.sqrt x ≤ Chebyshev.psi x := by
  have hi : ((s.n.sqrt : ℕ) : ℝ) ≤ Real.sqrt x := by
    apply Real.le_sqrt_of_sq_le
    exact le_trans (by exact_mod_cast Nat.sqrt_le' s.n) hx
  have hm :=
    Chebyshev.psi_mono
      ((show (((s.n - 1 : ℕ) : ℝ)) ≤ s.n by exact_mod_cast Nat.sub_le s.n 1).trans hx)
  have hh := hs.2.psiLo
  have hg' : (d : ℝ) * (scale : ℝ) * (s.n + 10) ≤ d * s.psiLo + u * scale * (s.n.sqrt : ℝ) := by
    exact_mod_cast hg
  norm_num only [scale, Nat.cast_pow, Nat.cast_ofNat] at hg' hh
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have he := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg (α := ℝ) u)
  rw [div_mul_eq_mul_div, sub_le_comm, le_div_iff₀ hd']
  have hpsi := hh.trans (mul_le_mul_of_nonneg_left hm (by positivity))
  nlinarith only [hg', he, mul_le_mul_of_nonneg_right hpsi hd'.le,
    mul_le_mul_of_nonneg_right hy hd'.le]

/-- A ten-integer replay proves the lower bound at every real point of the
covered interval and validates the outgoing edge. -/
theorem psiLower_segment {u d : ℕ} (hd : 0 < d) {a b k : ℕ} {s t : Edge} (ha : a ≤ s.n)
    (hb : s.n + 10 * k ≤ b) (hu : b ≤ 1000001)
    (check : psiLowerWalk u d (gcdStep a b) k s = some t) :
    Segment Valid (fun x ↦ x - (u : ℝ) / d * Real.sqrt x ≤ Chebyshev.psi x) s t := by
  rw [gcdStep_eq] at check
  induction k generalizing s with
  | zero =>
    obtain rfl := Option.some.inj check
    exact fun hs ↦ ⟨hs, fun _ hx hy ↦ False.elim (hy.not_ge hx)⟩
  | succ k ih =>
    rw [psiLowerWalk] at check
    split at check
    next hg =>
      intro hs
      have hw := walk_valid 10 s hs ha (by linarith only [hb, Nat.zero_le k]) hu
      have hnext := ih (ha.trans (by linarith only [hw.1])) (by linarith only [hw.1, hb]) check hw.2
      refine ⟨hnext.1, fun x hx hy ↦ ?_⟩
      by_cases h : x ≤ (s.n : ℝ) + 10
      · exact psiLower_cell hd hs hg hx h
      · apply hnext.2 x _ hy
        rw [hw.1, Nat.cast_add, Nat.cast_ofNat]
        exact le_of_not_ge h
    next => contradiction

/-- Replay the seven-tenths lower bound on consecutive ten-integer cells. -/
abbrev lower70Walk :=
  psiLowerWalk 7 10

/-- A ten-integer replay proves the lower bound at every real point of the
covered interval and validates the outgoing edge. -/
theorem lower70_segment {a b k : ℕ} {s t : Edge} (ha : a ≤ s.n) (hb : s.n + 10 * k ≤ b)
    (hu : b ≤ 1000001) (check : lower70Walk (gcdStep a b) k s = some t) :
    Segment Valid (fun x ↦ x - 7 / 10 * Real.sqrt x ≤ Chebyshev.psi x) s t := by
  exact psiLower_segment (by decide : 0 < 10) ha hb hu check

private def edge0 : Edge :=
  ⟨51539, 51522757957835874, 51523239117218398, 262975175719775, 262977893348012⟩

private def edge1 : Edge :=
  ⟨56539, 56557371116941355, 56557880493476111, 273859936122240, 273862672658375⟩

private def edge2 : Edge :=
  ⟨61539, 61556418269392894, 61556951470195781, 285919808194029, 285922634206487⟩

private def edge3 : Edge :=
  ⟨66539, 66492899855141710, 66493451560970070, 297687483794043, 297690390601889⟩

private def edge4 : Edge :=
  ⟨71539, 71527462009707256, 71528092128377610, 306973203214881, 306976483863075⟩

private def edge5 : Edge :=
  ⟨76539, 76516825709496550, 76517511241989268, 318170025089659, 318173836614825⟩

private def edge6 : Edge :=
  ⟨81539, 81557656554439411, 81558397564588102, 340448479726655, 340452523982820⟩

private theorem block0 :
    Segment Valid (fun x ↦ x - 7 / 10 * Real.sqrt x ≤ Chebyshev.psi x) edge0 edge1 := by
  apply lower70_segment (a := 51539) (b := 56539) (k := 500) (by decide) (by decide) (by decide)
  decide +kernel

private theorem block1 :
    Segment Valid (fun x ↦ x - 7 / 10 * Real.sqrt x ≤ Chebyshev.psi x) edge1 edge2 := by
  apply lower70_segment (a := 56539) (b := 61539) (k := 500) (by decide) (by decide) (by decide)
  decide +kernel

private theorem block2 :
    Segment Valid (fun x ↦ x - 7 / 10 * Real.sqrt x ≤ Chebyshev.psi x) edge2 edge3 := by
  apply lower70_segment (a := 61539) (b := 66539) (k := 500) (by decide) (by decide) (by decide)
  decide +kernel

private theorem block3 :
    Segment Valid (fun x ↦ x - 7 / 10 * Real.sqrt x ≤ Chebyshev.psi x) edge3 edge4 := by
  apply lower70_segment (a := 66539) (b := 71539) (k := 500) (by decide) (by decide) (by decide)
  decide +kernel

private theorem block4 :
    Segment Valid (fun x ↦ x - 7 / 10 * Real.sqrt x ≤ Chebyshev.psi x) edge4 edge5 := by
  apply lower70_segment (a := 71539) (b := 76539) (k := 500) (by decide) (by decide) (by decide)
  decide +kernel

private theorem block5 :
    Segment Valid (fun x ↦ x - 7 / 10 * Real.sqrt x ≤ Chebyshev.psi x) edge5 edge6 := by
  apply lower70_segment (a := 76539) (b := 81539) (k := 500) (by decide) (by decide) (by decide)
  decide +kernel

/-- The certified lower ticks give a seven-tenths one-sided psi estimate on
every real point from 51539 up to, but excluding, 81539. -/
theorem psi70_window {x : ℝ} (ha : 51539 ≤ x) (hb : x < 81539) :
    x - 7 / 10 * Real.sqrt x ≤ Chebyshev.psi x := by
  have h :=
    (segment_comp (segment_comp block0 block1)
      (segment_comp (segment_comp block2 block3) (segment_comp block4 block5)))
  have hs := (batch46539 (batch41539 (joined3500To41539 prefix3500.1).1).1).1
  exact (h hs).2 x ha hb

private theorem thirdBlock4 :
    Segment Valid (fun x ↦ x - 1 / 3 * Real.sqrt x ≤ Chebyshev.psi x) edge4 edge5 := by
  rw [← Nat.cast_one (R := ℝ)]
  apply
    psiLower_segment (u := 1) (by decide : 0 < 3) (a := 71539) (b := 76539) (k := 500) (by decide)
      (by decide) (by decide)
  decide +kernel

private theorem thirdBlock5 :
    Segment Valid (fun x ↦ x - 1 / 3 * Real.sqrt x ≤ Chebyshev.psi x) edge5 edge6 := by
  rw [← Nat.cast_one (R := ℝ)]
  apply
    psiLower_segment (u := 1) (by decide : 0 < 3) (a := 76539) (b := 81539) (k := 500) (by decide)
      (by decide) (by decide)
  decide +kernel

/-- On the last two batches, a one-third error covers every real argument. -/
theorem psi_third_window {x : ℝ} (ha : 71539 ≤ x) (hb : x < 81539) :
    x - 1 / 3 * Real.sqrt x ≤ Chebyshev.psi x := by
  have hs := (batch46539 (batch41539 (joined3500To41539 prefix3500.1).1).1).1
  have hm := (segment_comp (segment_comp block0 block1) (segment_comp block2 block3)) hs
  exact ((segment_comp thirdBlock4 thirdBlock5) hm.1).2 x ha hb

private def edge7 : Edge :=
  ⟨82539, 82621251295573281, 82622002214453640, 340448479726655, 340452523982820⟩

private theorem thirdBlock6 :
    Segment Valid (fun x ↦ x - 1 / 3 * Real.sqrt x ≤ Chebyshev.psi x) edge6 edge7 := by
  rw [← Nat.cast_one (R := ℝ)]
  apply
    psiLower_segment (u := 1) (by decide : 0 < 3) (a := 81539) (b := 82539) (k := 100) (by decide)
      (by decide) (by decide)
  decide +kernel

/-- The one-third lower bound for psi holds on the real interval from 71539 up to 82539.
One hundred additional ten-integer cells extend the estimate beyond the previous endpoint. -/
theorem psi_third_window_82539 {x : ℝ} (ha : 71539 ≤ x) (hb : x < 82539) :
    x - 1 / 3 * Real.sqrt x ≤ Chebyshev.psi x := by
  by_cases h : x < 81539
  · exact psi_third_window ha h
  have hs := (batch46539 (batch41539 (joined3500To41539 prefix3500.1).1).1).1
  have hm := (segment_comp (segment_comp block0 block1) (segment_comp block2 block3)) hs
  exact (thirdBlock6 ((segment_comp thirdBlock4 thirdBlock5) hm.1).1).2 x (le_of_not_gt h) hb

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
