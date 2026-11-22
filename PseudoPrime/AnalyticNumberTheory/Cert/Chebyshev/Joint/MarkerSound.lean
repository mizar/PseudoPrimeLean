/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.AdvanceSound
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.PowerLookup

/-! # Complete scalar classification of the integers in a batch -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Absolute-index marker obtained from the primality flag and the local power table. -/
def markerAt (a b n : ℕ) : ℕ :=
  if sieveFlag a b n then n else powerAt a b n

/-- A segment through one million returns the correct Mangoldt base at every queried
integer. Completeness of the two searches covers the zero marker as well. -/
theorem markerAt_sound {a b n : ℕ} (ha : a ≤ n) (hb : n < b) (hu : n ≤ 1000000) :
    Marker n (markerAt a b n) := by
  by_cases hp : n.Prime
  · rw [markerAt, ite_eq_left ((sieveFlag_iff ha hb hu).2 hp)]
    exact Marker.prime hp
  · rw [markerAt, ite_eq_right (fun hf ↦ hp ((sieveFlag_iff ha hb hu).1 hf))]
    have h := powerAt_spec ha hb hu hp
    by_cases hz : powerAt a b n = 0
    · rw [hz]
      exact Marker.other (h.1 hz)
    · obtain ⟨hpr, k, hk, he⟩ := h.2 hz
      exact Marker.power he.symm hpr (Nat.ne_of_gt (Nat.zero_lt_of_lt hk)) hp

/-- The segment classification discharges the marker hypothesis of the runtime update. -/
theorem advance_in_segment {a b : ℕ} {s : Edge} (hs : Valid s) (ha : a ≤ s.n) (hb : s.n < b)
    (hu : s.n ≤ 1000000) : Valid (advance certifiedTicks s (markerAt a b s.n)) := by
  exact advance_valid hs (markerAt_sound ha hb hu)

/-- On short low segments, direct primality and prime-power decisions avoid building
the base table. Higher powers use their least prime factor as marker. -/
def directMarker (n : ℕ) : ℕ :=
  if n.Prime then n else if IsPrimePow n then n.minFac else 0

/-- Direct classification has the same three Mangoldt cases as the segmented sieve. -/
theorem directMarker_sound (n : ℕ) : Marker n (directMarker n) := by
  unfold directMarker
  split
  next hp => exact Marker.prime hp
  next hc =>
    split
    next hh =>
      obtain ⟨p, k, hpr, hk, he⟩ := (isPrimePow_nat_iff n).mp hh
      have hm : n.minFac = p := he ▸ hpr.pow_minFac hk.ne'
      rw [hm]
      exact Marker.power he.symm hpr hk.ne' hc
    next hh => exact Marker.other hh

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
