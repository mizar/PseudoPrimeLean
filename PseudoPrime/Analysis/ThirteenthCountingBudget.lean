/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Integer exponent accounting for thirteenth-energy estimates -/

public section

namespace PseudoPrime.Analysis

/-- A count with height exponent `2a-b` and a thirteenth-energy power
estimate gives `pEN < k²` when `71a+13g < 39b`. Raise the count and height
bounds to thirteen, cancel the positive integer slack, and compare powers.
This algebraic lemma is independent of the arithmetic origin of `E,N,D`. -/
theorem thirteenth_counting_budget {p E N H D k a b g : ℕ} (hp : 0 < p) (ha : 0 < a)
    (hb : b ≤ 2 * a) (hslack : 71 * a + 13 * g < 39 * b) (hcut : p ^ b ≤ k ^ a)
    (hheight : H ^ a ≤ p ^ (2 * a - b)) (hcount : N ^ a ≤ D ^ a * H ^ a * p ^ g)
    (henergy : (E * D) ^ (13 * a) < p ^ (32 * a + (39 * b - (71 * a + 13 * g)))) :
    p * E * N < k ^ 2 := by
  have hN : N ^ (13 * a) ≤ D ^ (13 * a) * H ^ (13 * a) * p ^ (13 * g) := by
    simpa only [mul_pow, ← pow_mul, Nat.mul_comm a 13, Nat.mul_comm g 13] using
      Nat.pow_le_pow_left hcount 13
  have hH : H ^ (13 * a) ≤ p ^ (13 * (2 * a - b)) := by
    simpa only [← pow_mul, Nat.mul_comm a 13, Nat.mul_comm (2 * a - b) 13] using
      Nat.pow_le_pow_left hheight 13
  have hpow :
    (p * E * N) ^ (13 * a) ≤ (E * D) ^ (13 * a) * p ^ (13 * a + 13 * (2 * a - b) + 13 * g) := by
    calc
      _ = (p ^ (13 * a) * E ^ (13 * a)) * N ^ (13 * a) := by rw [mul_pow, mul_pow]
      _ ≤ (p ^ (13 * a) * E ^ (13 * a)) * (D ^ (13 * a) * H ^ (13 * a) * p ^ (13 * g)) :=
        Nat.mul_le_mul_left _ hN
      _ ≤ (p ^ (13 * a) * E ^ (13 * a)) * (D ^ (13 * a) * p ^ (13 * (2 * a - b)) * p ^ (13 * g)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hH))
      _ = _ := by
        rw [mul_pow, pow_add, pow_add]; ring
  have hid :
    (32 * a + (39 * b - (71 * a + 13 * g))) + (13 * a + 13 * (2 * a - b) + 13 * g) = 26 * b := by
    have hsub := Nat.sub_add_cancel hb
    have hsl := Nat.sub_add_cancel hslack.le
    nlinarith only [hsub, hsl]
  have hstrict :=
    Nat.mul_lt_mul_of_pos_right henergy
      (Nat.pow_pos hp : 0 < p ^ (13 * a + 13 * (2 * a - b) + 13 * g))
  rw [← pow_add, hid] at hstrict
  have hk : p ^ (26 * b) ≤ (k ^ 2) ^ (13 * a) := by
    have hh := Nat.pow_le_pow_left hcut 26
    convert hh using 1
    · rw [← pow_mul, Nat.mul_comm b 26]
    · rw [← pow_mul, ← pow_mul]
      congr 1
      ring
  exact
    (Nat.pow_lt_pow_iff_left (Nat.ne_of_gt (Nat.mul_pos (by norm_num only : 0 < 13) ha))).mp
      (hpow.trans_lt (hstrict.trans_le hk))

/-- Inputs: positive `p` and `a`, a cutoff exponent `b ≤ 2a`, cutoff and height
bounds, a powered count bound, and the strict slack inequality `71a+13g < 39b`.
Claim: if the thirteenth-power energy estimate has exponent `32a+r`, where `r`
does not exceed the available slack `39b-(71a+13g)`, then `p*E*N < k²`.
Proof: enlarge the energy exponent to the full available slack and apply
`thirteenth_counting_budget`. Role: lets explicit energy estimates retain a
smaller remainder exponent without duplicating the count-budget argument. -/
theorem thirteenth_counting_budget_of_energy_exponent_le {p E N H D k a b g r : ℕ} (hp : 0 < p)
    (ha : 0 < a) (hb : b ≤ 2 * a) (hslack : 71 * a + 13 * g < 39 * b) (hcut : p ^ b ≤ k ^ a)
    (hheight : H ^ a ≤ p ^ (2 * a - b)) (hcount : N ^ a ≤ D ^ a * H ^ a * p ^ g)
    (henergy : (E * D) ^ (13 * a) < p ^ (32 * a + r)) (hr : r ≤ 39 * b - (71 * a + 13 * g)) :
    p * E * N < k ^ 2 := by
  have henergy' : (E * D) ^ (13 * a) < p ^ (32 * a + (39 * b - (71 * a + 13 * g))) := by
    exact henergy.trans_le (Nat.pow_le_pow_right hp (Nat.add_le_add_left hr (32 * a)))
  exact thirteenth_counting_budget hp ha hb hslack hcut hheight hcount henergy'

end PseudoPrime.Analysis
