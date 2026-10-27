/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.HeilbronnIntervalKernel

/-! # A uniform interval bound from a nonnegative short-frequency kernel -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For positive H with 32Hk<=p^2, the proved energy gap gives A_p(H)<p.
Compare fourth powers using the short Fourier estimate and the height inequality. -/
theorem short_fourier_sum_lt_prime_of_energy_budget {p H k : ℕ} [Fact p.Prime] (hH : 0 < H)
    (hHk : 32 * H * k ≤ p ^ 2) (hb : p * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2) :
    (∑ z ∈ signedShortIntegers H, ‖heilbronnCharacterSum p (z : ZMod (p ^ 2))‖) < (p : ℝ) := by
  have hh :=
    short_heilbronn_fourth_power_lt_of_energy_budget (M := 1) hH (by simpa only [one_mul] using hb)
  simp only [Nat.cast_one, one_mul] at hh
  have hr : (32 : ℝ) * H * k ≤ (p : ℝ) ^ 2 := by exact_mod_cast hHk
  have hnon : 0 ≤ (32 : ℝ) * H * k :=
    mul_nonneg (mul_nonneg (by norm_num only) (Nat.cast_nonneg H)) (Nat.cast_nonneg k)
  have hs := pow_le_pow_left₀ hnon hr 2
  apply lt_of_pow_lt_pow_left₀ 4 (Nat.cast_nonneg p)
  nlinarith only [hh, hs, sq_nonneg ((H : ℝ) * k)]

/-- For 0<k<p^2 and 32k<=p^2, an energy gap at floor(p^2/(32k))
gives p times the initial interval count less than 256k. Apply the nonnegative kernel
and bound its short Fourier sum by p; integer division supplies the reciprocal height. -/
theorem heilbronnInitialCount_lt_of_floor_energy_budget {p k : ℕ} [Fact p.Prime] (hk : 0 < k)
    (hkp : k < p ^ 2) (hheight : 32 * k ≤ p ^ 2)
    (hb : p * heilbronnEnergy p * boundedCongruenceCount p (p ^ 2 / (32 * k)) < k ^ 2) :
    p * heilbronnInitialCount p k < 256 * k := by
  let H := p ^ 2 / (32 * k)
  have hd : 0 < 32 * k := Nat.mul_pos (by decide) hk
  have hH : 0 < H := Nat.div_pos hheight hd
  have hHk : 32 * H * k ≤ p ^ 2 := by
    have h := Nat.div_mul_le_self (p ^ 2) (32 * k)
    dsimp only [H]
    nlinarith only [h]
  have hA := short_fourier_sum_lt_prime_of_energy_budget hH hHk hb
  have hcount := heilbronnInitialCount_mul_height_le hkp hHk
  have hfloor : (p : ℝ) ^ 2 ≤ (32 : ℝ) * k * (H + 1 : ℝ) := by
    have h := (Nat.lt_mul_div_succ (p ^ 2) hd).le
    dsimp only [H]
    exact_mod_cast h
  have hsmall : (heilbronnInitialCount p k : ℝ) * (H + 1 : ℝ) < 8 * (p : ℝ) := by
    have hc : ((p - 1 : ℕ) : ℝ) ≤ p := Nat.cast_le.mpr (Nat.sub_le p 1)
    linarith only [hcount, hA, hc]
  have hm :=
    mul_lt_mul_of_pos_left hsmall
      (show (0 : ℝ) < 32 * k from mul_pos (by norm_num only) (Nat.cast_pos.mpr hk))
  have hf :=
    mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg (heilbronnInitialCount p k) : (0 : ℝ) ≤ _)
  have hfinal : (p : ℝ) * ((p : ℝ) * heilbronnInitialCount p k) < (p : ℝ) * (256 * k) := by
    nlinarith only [hm, hf]
  have hp : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hc := (mul_lt_mul_iff_right₀ hp).mp hfinal
  exact_mod_cast hc

/-- Increasing the integer height can only increase the bounded congruence count.
Include each old solution using its two interval bounds. -/
theorem boundedCongruenceCount_mono {p H K : ℕ} [Fact p.Prime] (hHK : H ≤ K) :
    boundedCongruenceCount p H ≤ boundedCongruenceCount p K := by
  apply Finset.card_le_card
  intro z hz
  have ht := (mem_boundedHeilbronnCongruences_iff z).mp hz
  have hr : (H : ℤ) ≤ K := Nat.cast_le.mpr hHK
  apply (mem_boundedHeilbronnCongruences_iff z).mpr
  exact
    ⟨ht.1, ⟨by linarith only [hr, ht.2.1.1], ht.2.1.2.trans hr⟩,
      ⟨by linarith only [hr, ht.2.2.1.1], ht.2.2.1.2.trans hr⟩, ht.2.2.2⟩

/-- The upper cutoff power bound and a fixed symbolic lower bound on p imply 32k<p^2.
Compare fifteenth powers; the remaining scale difference is p^2. -/
theorem cutoff_thirty_two_mul_lt_square {p k : ℕ} (hp : 1 < p) (hlarge : 32 ^ 15 * 32768 < p)
    (hcut : k ^ 15 ≤ 32768 * p ^ 28) : 32 * k < p ^ 2 := by
  have hpp : p ≤ p ^ 2 := by nlinarith only [hp]
  have hc := hlarge.trans_le hpp
  apply (Nat.pow_lt_pow_iff_left (by decide : 15 ≠ 0)).mp
  calc
    (32 * k) ^ 15 = 32 ^ 15 * k ^ 15 := Nat.mul_pow _ _ _
    _ ≤ 32 ^ 15 * (32768 * p ^ 28) := Nat.mul_le_mul_left _ hcut
    _ = (32 ^ 15 * 32768) * p ^ 28 := by ring
    _ < p ^ 2 * p ^ 28 := Nat.mul_lt_mul_of_pos_right hc (Nat.pow_pos (lt_trans (by decide) hp))
    _ = (p ^ 2) ^ 15 := by ring

/-- For r>=16185, all sufficiently large odd primes admit a cutoff of exponent 28/15
with initial interval count less than 256k/p. Transfer the existing energy gap to a smaller
height by monotonicity, then apply the short-frequency nonnegative kernel. -/
theorem exists_uniform_heilbronn_interval_bound {r : ℕ} (hr : 16185 ≤ r) :
    ∃ P : ℕ,
      ∀ (p : ℕ) [Fact p.Prime],
        Odd p →
          P ≤ p →
          ∃ k : ℕ,
            0 < k ∧
              k < p ^ 2 ∧
              p ^ 28 ≤ k ^ 15 ∧
              k ^ 15 ≤ 32768 * p ^ 28 ∧ p * heilbronnInitialCount p k < 256 * k := by
  obtain ⟨P, hP⟩ := exists_uniform_weighted_short_congruence_energy_budget (M := 1) hr
  refine ⟨max P (32 ^ 15 * 32768 + 1), ?_⟩
  intro p hp hodd hlarge
  have hPp := (max_le_iff.mp hlarge).1
  have hc : 32 ^ 15 * 32768 < p := lt_of_lt_of_le (Nat.lt_succ_self _) (max_le_iff.mp hlarge).2
  obtain ⟨k, hk, hkp, hlo, hhi, hb⟩ := hP p hodd hPp
  have hheight := cutoff_thirty_two_mul_lt_square (Fact.out : p.Prime).one_lt hc hhi
  have h32 : k ≤ 32 * k := by nlinarith only [hk]
  have hkp' := h32.trans_lt hheight
  refine ⟨k, hk, hkp', hlo, hhi, ?_⟩
  apply heilbronnInitialCount_lt_of_floor_energy_budget hk hkp' hheight.le
  have hmono :=
    boundedCongruenceCount_mono (p := p) (Nat.div_le_div_left h32 hk : p ^ 2 / (32 * k) ≤ p ^ 2 / k)
  have hm := Nat.mul_le_mul_left (p * heilbronnEnergy p) hmono
  simp only [one_mul] at hb
  exact hm.trans_lt hb

end PseudoPrime.NumberTheory.Heilbronn
