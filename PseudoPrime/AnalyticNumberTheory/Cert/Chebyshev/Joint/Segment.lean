/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Basic.Real.Basic

/-! # Scalar boundaries for simultaneous Chebyshev certificates -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- State immediately before integer `n`. The two pairs bound the sums through `n - 1`
for all prime powers and for powers of exponent at least two, respectively.
The validity predicate of a segment supplies the mathematical invariant. -/
structure Edge where
  n : ℕ
  psiLo : ℕ
  psiHi : ℕ
  powerLo : ℕ
  powerHi : ℕ

/-- A segment transports the scalar invariant from `a` to `b` and establishes the
pointwise predicate on their half-open real interval. The predicate can contain
multiple conditional bounds with different lower cutoffs. -/
def Segment (valid : Edge → Prop) (bound : ℝ → Prop) (a b : Edge) : Prop :=
  valid a → valid b ∧ ∀ x : ℝ, (a.n : ℝ) ≤ x → x < b.n → bound x

/-- Adjacent segments with the same invariant and pointwise predicate compose
by splitting at the common scalar index. Used at every internal tree node. -/
theorem segment_comp {valid bound a b c} (h : Segment valid bound a b)
    (k : Segment valid bound b c) : Segment valid bound a c := by
  intro ha
  obtain ⟨hb, hab⟩ := h ha
  obtain ⟨hc, hbc⟩ := k hb
  exact ⟨hc, fun x hx hy ↦ (lt_or_ge x (b.n : ℝ)).elim (hab x hx) (fun hbx ↦ hbc x hbx hy)⟩

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
