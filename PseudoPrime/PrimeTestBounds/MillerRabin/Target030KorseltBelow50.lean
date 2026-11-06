/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030KorseltBelow40
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Korselt40to50

/-! # Combined uniform Korselt search below smallest factor 50 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The independently checked factor ranges below 40 and from 40 to 49 give
exactly the six listed parameter triples below smallest factor 50. -/
theorem target030_candidates_below50 :
    target030CandidateRows 50 =
      [(7, 2, 18), (13, 2, 60), (13, 8, 36), (19, 14, 198), (41, 22, 72), (43, 26, 126)] := by
  have hsplit := target030CandidateRows_split 40 10
  norm_num only at hsplit
  have hzero : target030CandidateRange 0 40 = target030CandidateRows 40 := by
    simp only [target030CandidateRange, target030CandidateRows, List.range_eq_range']
  rw [hzero, target030_candidates_below40, target030_candidates_40to50] at hsplit
  exact hsplit

/-- A bounded uniform Korselt triple with ordered smallest factor below 50 is
one of six explicit products. Map each checked parameter tuple to the input
reconstructed from its three factors. -/
theorem uniformKorselt_below50_cases {n p q r : ℕ} (hu : UniformKorseltTriple n)
    (hbound : n ≤ 2 ^ 22) (hn : n = p * q * r) (hp : p.Prime) (hq : q.Prime) (hrp : r.Prime)
    (hpq : p < q) (hqr : q < r) (hsmall : p < 50) :
    n ∈ [8911, 314821, 29341, 1024651, 410041, 1152271] := by
  obtain ⟨hpb, a, ha, hap, hdiv, hadiv, hrform⟩ :=
    uniformKorselt_finite_parameters hn hp hq hrp hpq hqr hu hbound
  have hm : (p, a, q - 1) ∈ target030CandidateRows 50 :=
    uniformKorselt_candidate_mem hu hn hp hq hrp hpq hqr hbound hsmall ha hap hdiv hadiv hrform
  rw [target030_candidates_below50] at hm
  let f : ℕ × ℕ × ℕ → ℕ := fun x ↦ x.1 * (x.2.2 + 1) * ((x.1 * (x.2.2 + 1) - 1) / x.2.1 + 1)
  have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel hq.one_lt.le
  have heq : f (p, a, q - 1) = n := by
    dsimp only [f]
    rw [hqsub, ← hrform, ← hn]
  have hh := List.mem_map.mpr ⟨(p, a, q - 1), hm, heq⟩
  norm_num only [List.map_cons, List.map_nil, f] at hh
  exact hh

end PseudoPrime.PrimeTestBounds.MillerRabin
