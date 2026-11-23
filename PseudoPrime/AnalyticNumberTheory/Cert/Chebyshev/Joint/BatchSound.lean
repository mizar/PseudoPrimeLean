/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.Walk

/-! # Combining successive certified cells within a batch -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

deriving instance DecidableEq for Edge

/-- Cell bounds with the psi coefficient chosen at its left endpoint. -/
def CellBound (a u v : ℕ) (x : ℝ) : Prop :=
  |Chebyshev.psi x - x| ≤ ((u : ℝ) / v) * Real.sqrt x ∧
    (2657 ≤ a →
      (u : ℝ) / v ≤ 4 / 5 →
      |Chebyshev.theta x - x| ≤ ((thetaBand a).1 / ((thetaBand a).2 : ℝ)) * Real.sqrt x)

/-- Replay a sequence of positive cell widths. The width function stores the number of
additional integers after the first. Return the final edge only when every guard succeeds. -/
def replayWith (step : Edge → Edge) (a b : ℕ) (extra : ℕ → ℕ) (coef : ℕ → ℕ × ℕ) :
    ℕ → Edge → Option Edge
  | 0, s => some s
  | count + 1, s =>
    let k := extra s.n
    let c := coef s.n
    if a ≤ s.n ∧ s.n + (k + 1) ≤ b ∧ 1 ≤ s.n ∧ 0 < c.2 ∧ c.1 ≤ 2 * c.2 then
      let f := step s
      let t := walk step k f
      if cellCheck s.n t.n c.1 c.2 f.psiLo (f.psiLo - f.powerLo) t.psiHi t.powerHi then
        replayWith step a b extra coef count t
      else none
    else none

/-- Replay using the certified segmented sieve transition. -/
abbrev replayCells (a b : ℕ) :=
  replayWith (segmentStep a b) a b

/-- Successful replay transports the initial prefix and combines the real estimates
on all consecutive cells. The caller supplies the implication for its coefficient regime. -/
theorem replayCells_sound {a b : ℕ} {extra : ℕ → ℕ} {coef : ℕ → ℕ × ℕ} {bound : ℝ → Prop}
    (hu : b ≤ 1000001)
    (lift :
      ∀ n x,
        a ≤ n →
          n + (extra n + 1) ≤ b →
          (n : ℝ) ≤ x → x < (n + (extra n + 1) : ℕ) → CellBound n (coef n).1 (coef n).2 x → bound x)
    (count : ℕ) {s t : Edge} (h : replayCells a b extra coef count s = some t) :
    Segment Valid bound s t := by
  induction count generalizing s with
  | zero =>
    have he : s = t := Option.some.inj h
    subst t
    exact fun hs ↦ ⟨hs, fun _ hx hy ↦ False.elim ((not_lt_of_ge hx) hy)⟩
  | succ count ih =>
    rw [replayCells, replayWith] at h
    dsimp only at h
    split at h
    next hr =>
      obtain ⟨ha, hb, hn, hv, hc⟩ := hr
      split at h
      next hg =>
        have hv' := Nat.cast_pos (α := ℝ).mpr hv
        have hc' : ((coef s.n).1 : ℝ) / (coef s.n).2 ≤ 2 :=
          (div_le_iff₀ hv').2 (by exact_mod_cast hc)
        have seg := walked_cell ha hb hu hv hc' (by exact_mod_cast hn) hg
        apply segment_comp (k := ih h)
        intro hs
        obtain ⟨ht, hx⟩ := seg hs
        have he := (walk_valid (a := a) (extra s.n + 1) s hs ha hb hu).1
        exact ⟨ht, fun x hl hh ↦ lift s.n x ha hb hl (he ▸ hh) (hx x hl hh)⟩
      next => contradiction
    next => contradiction

/-- Check the computed exit cursor and all four ticks against the claimed batch boundary. -/
def batchAccepted (a b : ℕ) (extra : ℕ → ℕ) (coef : ℕ → ℕ × ℕ) (count : ℕ) (s t : Edge) : Bool :=
  decide (replayCells a b extra coef count s = some t)

/-- A batch with matching output provides a segment theorem at the claimed scalar endpoints. -/
theorem accepted_segment {a b count : ℕ} {extra : ℕ → ℕ} {coef : ℕ → ℕ × ℕ} {bound : ℝ → Prop}
    {s t : Edge} (hu : b ≤ 1000001)
    (lift :
      ∀ n x,
        a ≤ n →
          n + (extra n + 1) ≤ b →
          (n : ℝ) ≤ x → x < (n + (extra n + 1) : ℕ) → CellBound n (coef n).1 (coef n).2 x → bound x)
    (h : batchAccepted a b extra coef count s t = true) : Segment Valid bound s t := by
  exact replayCells_sound hu lift count (of_decide_eq_true h)

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
