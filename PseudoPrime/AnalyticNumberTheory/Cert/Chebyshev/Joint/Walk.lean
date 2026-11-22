/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.MarkerSound
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.CheckedCell

/-! # Certified traversal of one joint cell -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Advance a scalar prefix by the given number of integers with a prepared step function. -/
def walk (step : Edge → Edge) : ℕ → Edge → Edge
  | 0, s => s
  | k + 1, s => walk step k (step s)

/-- One step of the certified traversal using the segment's prime and higher-power markers. -/
def segmentStep (a b : ℕ) (s : Edge) : Edge :=
  advance certifiedTicks s (if b ≤ 101 then directMarker s.n else markerAt a b s.n)

private theorem step_valid {a b : ℕ} {s : Edge} (hs : Valid s) (ha : a ≤ s.n) (hb : s.n < b)
    (hu : s.n ≤ 1000000) : Valid (segmentStep a b s) := by
  apply advance_valid hs
  split
  · exact directMarker_sound _
  · exact markerAt_sound ha hb hu

private theorem advance_index (f : ℕ → ℕ × ℕ) (s : Edge) (p : ℕ) : (advance f s p).n = s.n + 1 := by
  unfold advance
  split
  · rfl
  · split <;> rfl

/-- Traversing any number of integers inside a certified segment advances the cursor
by that count and preserves the prefix bounds through its predecessor. -/
theorem walk_valid {a b : ℕ} (k : ℕ) (s : Edge) (hs : Valid s) (ha : a ≤ s.n) (hb : s.n + k ≤ b)
    (hu : b ≤ 1000001) :
    let t := walk (segmentStep a b) k s
    t.n = s.n + k ∧ Valid t := by
  induction k generalizing s with
  | zero => exact ⟨rfl, hs⟩
  | succ k ih =>
    have hl : s.n < b := by linarith only [hb]
    have hn : (segmentStep a b s).n = s.n + 1 := advance_index _ _ _
    have hv := step_valid hs ha hl (by linarith only [hl, hu])
    obtain ⟨ht, hV⟩ :=
      ih (segmentStep a b s) hv (by linarith only [ha, hn]) (by linarith only [hb, hn])
    exact ⟨by rw [walk, ht, hn, Nat.add_right_comm, Nat.add_assoc], hV⟩

/-- The first update supplies the left prefix and the remaining updates supply the right
prefix. A successful check then certifies every real point between the two cursors. -/
theorem walked_cell {a b k u v : ℕ} {s : Edge} (ha : a ≤ s.n) (hb : s.n + (k + 1) ≤ b)
    (hu : b ≤ 1000001) (hv : 0 < v) (hc : (u : ℝ) / v ≤ 2) (hpos : (1 : ℝ) ≤ s.n) :
    let f := segmentStep a b s
    let t := walk (segmentStep a b) k f
    cellCheck s.n t.n u v f.psiLo (f.psiLo - f.powerLo) t.psiHi t.powerHi = true →
      Segment Valid
        (fun x ↦
          |Chebyshev.psi x - x| ≤ ((u : ℝ) / v) * Real.sqrt x ∧
            (2657 ≤ s.n →
              (u : ℝ) / v ≤ 4 / 5 →
              |Chebyshev.theta x - x| ≤
                ((thetaBand s.n).1 / ((thetaBand s.n).2 : ℝ)) * Real.sqrt x))
        s t := by
  intro f t hg hs
  have hn : f.n = s.n + 1 := advance_index _ _ _
  have hl : s.n < b := by linarith only [hb]
  have hf : Valid f := step_valid hs ha hl (by linarith only [hl, hu])
  have ht :=
    (walk_valid (a := a) k f hf (by linarith only [ha, hn]) (by linarith only [hb, hn]) hu).2
  have hp : Prefix s.n f.psiLo f.psiHi f.powerLo f.powerHi := by
    simpa only [hn, Nat.add_sub_cancel] using hf.2
  exact ⟨ht, fun x hx hy ↦ cellCheck_sound hp ht.2 hv hc hpos hx hy hg⟩

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
