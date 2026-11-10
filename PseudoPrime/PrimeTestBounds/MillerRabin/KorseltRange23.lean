/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.KorseltParameters

/-! # Bounded Korselt parameter search up to two to the twenty-third -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Check reconstructed Korselt parameters for an input at most `2^23`.
The three values represent the smallest prime, quotient, and middle predecessor. -/
def korseltGood23 (p a d : ℕ) : Bool :=
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
      n ≤ 2 ^ 23 ∧
      (p - 1 ∣ n - 1) ∧
      (q - 1 ∣ n - 1) ∧
      (r - 1 ∣ n - 1) ∧
      padicValNat 2 (p - 1) = padicValNat 2 (q - 1) ∧ padicValNat 2 (p - 1) = padicValNat 2 (r - 1))

/-- Enumerate one smallest-prime interval with early primality and valuation
filters. Disjoint intervals can be kernel-checked independently. -/
def korseltFastRange23 (lo len : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range' lo len).flatMap fun p ↦
    if p.Prime then
      (List.range (Nat.sqrt ((2 ^ 23) / p) + 1)).flatMap fun d ↦
        if p < d + 1 ∧ (d + 1).Prime ∧ padicValNat 2 (p - 1) = padicValNat 2 d then
          (List.range p).filterMap fun a ↦ if korseltGood23 p a d then some (p, a, d) else none
        else []
    else []

/-- The parameters of a bounded ordered uniform Korselt triple occur in the
reordered finite search for any interval containing its smallest factor. -/
theorem korselt23_mem {n p q r a lo len : ℕ} (hu : UniformKorseltTriple n) (hn : n = p * q * r)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpq : p < q) (hqr : q < r) (hbound : n ≤ 2 ^ 23)
    (hlo : lo ≤ p) (hhi : p < lo + len) (ha : 1 ≤ a) (hap : a < p)
    (hdiv : q - 1 ∣ (p - 1) * (p + a)) (hadiv : a ∣ p * q - 1) (hrform : r = (p * q - 1) / a + 1) :
    (p, a, q - 1) ∈ korseltFastRange23 lo len := by
  have hqn : q ∣ n := hn ▸ dvd_mul_of_dvd_left (dvd_mul_left q p) r
  have hpn : p ∣ n := hn ▸ dvd_mul_of_dvd_left (dvd_mul_right p q) r
  have hrn : r ∣ n := hn ▸ dvd_mul_left r (p * q)
  have hmul : q * q * p ≤ 2 ^ 23 := by
    calc
      q * q * p = p * q * q := by ring
      _ ≤ p * q * r := Nat.mul_le_mul_left (p * q) hqr.le
      _ ≤ 2 ^ 23 := hn ▸ hbound
  have hqsq : q * q ≤ (2 ^ 23) / p := (Nat.le_div_iff_mul_le hp.pos).2 hmul
  have hqbound : q ≤ Nat.sqrt ((2 ^ 23) / p) := Nat.le_sqrt.2 hqsq
  have hdlt : q - 1 < Nat.sqrt ((2 ^ 23) / p) + 1 :=
    Nat.lt_succ_of_le ((Nat.sub_le q 1).trans hqbound)
  have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel hq.one_lt.le
  have hqk := hu.2.2.1 q hq hqn
  have hpk := hu.2.2.1 p hp hpn
  have hrk := hu.2.2.1 r hr hrn
  have hpqv := hu.2.2.2 p q hp hq hpn hqn
  have hprv := hu.2.2.2 p r hp hr hpn hrn
  have hgood : korseltGood23 p a (q - 1) = true := by
    simp only [korseltGood23, decide_eq_true_eq, hqsub, ← hrform, ← hn]
    exact ⟨hpq, ha, hap, hadiv, hdiv, hq, hr, hqr, hbound, hpk, hqk, hrk, hpqv, hprv⟩
  have hpre :
    p < (q - 1) + 1 ∧ ((q - 1) + 1).Prime ∧ padicValNat 2 (p - 1) = padicValNat 2 (q - 1) := by
    simpa only [hqsub] using ⟨hpq, hq, hpqv⟩
  have hpindex : p - lo < len :=
    (Nat.sub_lt_iff_lt_add hlo).mpr (by simpa only [Nat.add_comm] using hhi)
  unfold korseltFastRange23
  apply List.mem_flatMap.mpr
  refine ⟨p, List.mem_range'.mpr ⟨p - lo, hpindex, ?_⟩, ?_⟩
  · simp only [one_mul, Nat.add_sub_of_le hlo]
  rw [ite_eq_left hp]
  apply List.mem_flatMap.mpr
  refine ⟨q - 1, List.mem_range.mpr hdlt, ?_⟩
  rw [ite_eq_left hpre]
  apply List.mem_filterMap.mpr
  refine ⟨a, List.mem_range.mpr hap, ?_⟩
  rw [hgood]
  rfl

end PseudoPrime.PrimeTestBounds.MillerRabin
