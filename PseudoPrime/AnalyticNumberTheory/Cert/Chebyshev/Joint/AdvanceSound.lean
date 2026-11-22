/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.PrimeTicks
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.Prefix

/-! # Soundness of the marker-driven runtime transition -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- An edge with positive cursor encloses the functions through the preceding integer. -/
def Valid (s : Edge) : Prop :=
  0 < s.n ∧ Prefix (s.n - 1) s.psiLo s.psiHi s.powerLo s.powerHi

/-- A zero marker certifies a non-power. A prime marks itself; a composite power carries
its prime base and an exponent witness. No sieve array occurs in this specification. -/
inductive Marker (n : ℕ) : ℕ → Prop where
  | other (hn : ¬IsPrimePow n) : Marker n 0
  | prime (hn : n.Prime) : Marker n n
  | power {p k : ℕ} (hn : n = p ^ k) (hp : p.Prime) (hk : k ≠ 0) (hc : ¬n.Prime) : Marker n p

/-- The runtime logarithm calculator instantiated with its kernel-certified grid. -/
abbrev certifiedTicks :=
  primeTicks gridTicks (gridTicks 32)

/-- The initial cursor is one and its four prefix sums are zero. -/
theorem initial_valid : Valid ⟨1, 0, 0, 0, 0⟩ := by exact ⟨Nat.zero_lt_one, prefix_zero⟩

/-- A correct scalar marker suffices for the actual scanner update to preserve validity.
Each nonzero branch obtains both logarithm bounds from the certified runtime formula. -/
theorem advance_valid {s : Edge} {p : ℕ} (hs : Valid s) (hm : Marker s.n p) :
    Valid (advance certifiedTicks s p) := by
  obtain ⟨n, l, h, d, e⟩ := s
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ hs.1)
  | succ n =>
    have a : Prefix n l h d e := hs.2
    change Marker (n + 1) p at hm
    cases hm with
    | other hn => exact ⟨Nat.succ_pos _, prefix_other a hn (fun hp ↦ hn hp.isPrimePow)⟩
    | prime hp =>
      have ht := primeTicks_sound hp.ne_zero
      simpa only [advance, ite_eq_right hp.ne_zero, ite_true, Valid, Nat.add_sub_cancel] using
        And.intro (Nat.succ_pos (n + 1)) (prefix_prime a hp ht.1 ht.2)
    | power hn hp hk hc =>
      have ht := primeTicks_sound hp.ne_zero
      have hne : _ ≠ n + 1 := fun he ↦ hc (he ▸ hp)
      simpa only [advance, ite_eq_right hp.ne_zero, ite_eq_right hne, Valid,
        Nat.add_sub_cancel] using
        And.intro (Nat.succ_pos (n + 1)) (prefix_power a hn hp hk hc ht.1 ht.2)

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
