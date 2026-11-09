/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.KorseltParameters

/-! # Finite candidate enumeration for uniform Korselt triples -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Decide whether a bounded parameter triple reconstructs an ordered prime
Korselt triple with equal predecessor valuations. This predicate supplies the
finite search whose completeness is proved below. -/
def korseltCandidateGood (p a d : ℕ) : Bool :=
  let q := d + 1
  let r := (p * q - 1) / a + 1
  let n := p * q * r
  decide
    (p < q ∧
      1 ≤ a ∧
      a < p ∧
      a ∣ p * q - 1 ∧
      d ∣ (p - 1) * (p + a) ∧
      q.Prime ∧
      r.Prime ∧
      q < r ∧
      n ≤ 2 ^ 22 ∧
      (p - 1 ∣ n - 1) ∧
      (q - 1 ∣ n - 1) ∧
      (r - 1 ∣ n - 1) ∧
      padicValNat 2 (p - 1) = padicValNat 2 (q - 1) ∧ padicValNat 2 (p - 1) = padicValNat 2 (r - 1))

/-- Enumerate candidate parameter triples with smallest factor below N.
The middle predecessor is bounded using the product limit and integer square root. -/
def korseltCandidateRows (N : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range N).flatMap fun p ↦
    if p.Prime then
      (List.range p).flatMap fun a ↦
        (List.range (Nat.sqrt ((2 ^ 22) / p) + 1)).filterMap fun d ↦
          if korseltCandidateGood p a d then some (p, a, d) else none
    else []

/-- Enumerate the same candidate parameters for a consecutive range of
smallest factors. Separate ranges permit independent kernel certificates. -/
def korseltCandidateRange (lo len : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range' lo len).flatMap fun p ↦
    if p.Prime then
      (List.range p).flatMap fun a ↦
        (List.range (Nat.sqrt ((2 ^ 22) / p) + 1)).filterMap fun d ↦
          if korseltCandidateGood p a d then some (p, a, d) else none
    else []

/-- Splitting the smallest-factor range preserves the complete candidate list.
This joins separately checked blocks without repeating their enumeration. -/
theorem korseltCandidateRows_split (m n : ℕ) :
    korseltCandidateRows (m + n) = korseltCandidateRange 0 m ++ korseltCandidateRange m n := by
  unfold korseltCandidateRows korseltCandidateRange
  rw [List.range_eq_range', ← List.range'_append]
  simp only [one_mul, zero_add, List.flatMap_append]

/-- Every bounded ordered uniform Korselt triple is present in the candidate
list at the parameters supplied by the arithmetic classification. -/
theorem uniformKorselt_candidate_mem {n p q r a N : ℕ} (hu : UniformKorseltTriple n)
    (hn : n = p * q * r) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpq : p < q) (hqr : q < r)
    (hbound : n ≤ 2 ^ 22) (hap : p < N) (ha : 1 ≤ a) (haplt : a < p)
    (hdiv : q - 1 ∣ (p - 1) * (p + a)) (hadiv : a ∣ p * q - 1) (hrform : r = (p * q - 1) / a + 1) :
    (p, a, q - 1) ∈ korseltCandidateRows N := by
  have hqn : q ∣ n := hn ▸ dvd_mul_of_dvd_left (dvd_mul_left q p) r
  have hpn : p ∣ n := hn ▸ dvd_mul_of_dvd_left (dvd_mul_right p q) r
  have hrn : r ∣ n := hn ▸ dvd_mul_left r (p * q)
  have hmul : q * q * p ≤ 2 ^ 22 := by
    calc
      q * q * p = p * q * q := by ring
      _ ≤ p * q * r := Nat.mul_le_mul_left (p * q) hqr.le
      _ ≤ 2 ^ 22 := hn ▸ hbound
  have hqsq : q * q ≤ (2 ^ 22) / p := (Nat.le_div_iff_mul_le hp.pos).2 hmul
  have hqbound : q ≤ Nat.sqrt ((2 ^ 22) / p) := Nat.le_sqrt.2 hqsq
  have hdlt : q - 1 < Nat.sqrt ((2 ^ 22) / p) + 1 :=
    Nat.lt_succ_of_le ((Nat.sub_le q 1).trans hqbound)
  have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel hq.one_lt.le
  have hqk := hu.2.2.1 q hq hqn
  have hpk := hu.2.2.1 p hp hpn
  have hrk := hu.2.2.1 r hr hrn
  have hpqv := hu.2.2.2 p q hp hq hpn hqn
  have hprv := hu.2.2.2 p r hp hr hpn hrn
  have hgood : korseltCandidateGood p a (q - 1) = true := by
    simp only [korseltCandidateGood, decide_eq_true_eq, hqsub, ← hrform, ← hn]
    exact ⟨hpq, ha, haplt, hadiv, hdiv, hq, hr, hqr, hbound, hpk, hqk, hrk, hpqv, hprv⟩
  unfold korseltCandidateRows
  apply List.mem_flatMap.mpr
  refine ⟨p, List.mem_range.mpr hap, ?_⟩
  rw [ite_eq_left hp]
  apply List.mem_flatMap.mpr
  refine ⟨a, List.mem_range.mpr haplt, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨q - 1, List.mem_range.mpr hdlt, ?_⟩
  rw [hgood]
  rfl

/-- Every uniform Korselt triple at most `2^22` is represented in the finite
candidate list. The parameters reconstruct its ordered prime factors and the
original product, so checking the list covers every such input. -/
theorem uniformKorselt_mem_candidates {n : ℕ} (hu : UniformKorseltTriple n) (hbound : n ≤ 2 ^ 22) :
    ∃ p q r a : ℕ,
      p.Prime ∧
        q.Prime ∧
        r.Prime ∧
        p < q ∧
        q < r ∧
        n = p * q * r ∧ r = (p * q - 1) / a + 1 ∧ (p, a, q - 1) ∈ korseltCandidateRows 162 := by
  obtain ⟨p, q, r, a, hp, hq, hr, hpq, hqr, hn, hpbound, ha, hap, hdiv, hadiv, hrform⟩ :=
    uniformKorselt_search_complete hu hbound
  exact
    ⟨p, q, r, a, hp, hq, hr, hpq, hqr, hn, hrform,
      uniformKorselt_candidate_mem hu hn hp hq hr hpq hqr hbound (by linarith only [hpbound]) ha hap
        hdiv hadiv hrform⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
