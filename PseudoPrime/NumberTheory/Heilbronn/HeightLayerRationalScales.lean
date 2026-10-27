/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.HeightLayerEnergyBridge
public import PseudoPrime.NumberTheory.Heilbronn.RationalEnergyScales

/-! # Rational Heilbronn scales above 116/63 from height-layer counts -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Every rational scale b/a above 116/63 admits the fixed scaled exponents
42a,42b,a+1 and positive layer parameters. The integer gap supplies strict
energy slack, while the height exponent lies below the shifted degree-six cutoff.
These choices depend only on a,b and are uniform in the prime. -/
theorem height_layer_rational_parameters {a b : ℕ} (ha : 0 < a) (hgap : 116 * a < 63 * b)
    (hsmall : b < 2 * a) :
    11 * (42 * a) + 2 * (a + 1) < 6 * (42 * b) ∧
      (0 : ℝ) < 1 / (84 * a) ∧
      (0 : ℝ) < 1 / (504 * a) ∧
      (1 : ℝ) / (504 * a) < 1 / 42 ∧
      (1 : ℝ) / (504 * a) + (1 / (84 * a)) / 6 ≤ 1 / (42 * a) ∧
      ((a + 1 : ℕ) : ℝ) / (42 * a : ℕ) = 1 / 42 + 1 / (42 * a) ∧
      ((2 * (42 * a) - 42 * b : ℕ) : ℝ) / (42 * a : ℕ) ≤ 1 / 6 - 1 / (504 * a) := by
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have ha1 : (1 : ℝ) ≤ a := Nat.one_le_cast.mpr ha
  have hg : (116 : ℝ) * a + 1 ≤ 63 * b := by
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat] using
      (Nat.cast_le (α := ℝ).mpr (Nat.succ_le_of_lt hgap))
  have hb : 42 * b ≤ 2 * (42 * a) := by omega
  refine
    ⟨by omega, div_pos (by norm_num only) (mul_pos (by norm_num only) haR),
      div_pos (by norm_num only) (mul_pos (by norm_num only) haR), ?_, ?_, ?_, ?_⟩
  · apply (div_lt_div_iff₀ (mul_pos (by norm_num only) haR) (by norm_num only : (0 : ℝ) < 42)).mpr
    nlinarith only [ha1]
  · have hdiv : (1 / (84 * a) : ℝ) / 6 = 1 / (504 * a) := by
      rw [div_div]
      congr 1
      ring
    rw [hdiv, ← add_div]
    apply (div_le_div_iff₀ (mul_pos (by norm_num only) haR) (mul_pos (by norm_num only) haR)).mpr
    nlinarith only [haR]
  · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [add_div]
    have hcancel : (a : ℝ) / (42 * a) = 1 / 42 := by
      apply
        (div_eq_div_iff (ne_of_gt (mul_pos (by norm_num only) haR))
            (by norm_num only : (42 : ℝ) ≠ 0)).mpr
      ring
    rw [hcancel]
  · rw [Nat.cast_sub hb]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    apply (div_le_iff₀ (mul_pos (by norm_num only) haR)).mpr
    have hcancel : (1 / (504 * a) : ℝ) * (42 * a) = 1 / 12 := by
      rw [one_div_mul_eq_div]
      apply
        (div_eq_div_iff (ne_of_gt (mul_pos (by norm_num only) haR))
            (by norm_num only : (12 : ℝ) ≠ 0)).mpr
      ring
    rw [sub_mul, hcancel]
    nlinarith only [hg]

/-- For any rational scale 116/63<b/a<2, all sufficiently large odd primes
admit a cutoff with the strict energy budget at height floor(p²/k).
Use the proved global height-layer count, exact root selection, and the fixed
parameter choice. This improves the former 13/7 energy range without a count
hypothesis or GRH. -/
theorem exists_uniform_height_layer_rational_energy_budget {a b : ℕ} (ha : 0 < a)
    (hgap : 116 * a < 63 * b) (hsmall : b < 2 * a) :
    ∃ P : ℕ,
      ∀ (p : ℕ) [Fact p.Prime],
        Odd p →
          P ≤ p →
          ∃ k : ℕ,
            0 < k ∧
              k ≤ p ^ 2 ∧
              p ^ b ≤ k ^ a ∧
              k ^ a ≤ 2 ^ a * p ^ b ∧
              p * heilbronnEnergy p * boundedCongruenceCount p (p ^ 2 / k) < k ^ 2 := by
  have hpar := height_layer_rational_parameters ha hgap hsmall
  have ha' : 0 < 42 * a := Nat.mul_pos (by decide) ha
  have hb' : 42 * b ≤ 2 * (42 * a) := by omega
  obtain ⟨P, hP⟩ :=
    exists_global_height_layer_energy_budget hpar.2.1 hpar.2.2.1 hpar.2.2.2.1 hpar.2.2.2.2.1 ha'
      hpar.2.2.2.2.2.1 hb' hpar.1
  refine ⟨P, ?_⟩
  intro p hp hodd hlarge
  have hp0 := (Fact.out : p.Prime).pos
  have hp1 := (Fact.out : p.Prime).one_lt
  have hmass : p ^ b < (p ^ 2) ^ a := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right hp1 hsmall
  rcases exists_power_cutoff_or_base (U := p ^ 2) (Nat.pow_pos (n := b) hp0) ha with
    ⟨k, hk, hkp, hlo, hhi⟩ | hbase
  · refine ⟨k, hk, hkp, hlo, hhi, ?_⟩
    have hlo' : p ^ (42 * b) ≤ k ^ (42 * a) := by
      have hh := Nat.pow_le_pow_left hlo 42
      simpa only [← pow_mul, Nat.mul_comm] using hh
    have hheight := floor_power_budget hp0 hb' hlo'
    have hd : 2 * (42 * a) - 42 * b < 42 * a := by omega
    have hHp : p ^ 2 / k < p := by
      by_contra hn
      have hh := (Nat.pow_le_pow_left (Nat.le_of_not_gt hn) (42 * a)).trans hheight
      exact (not_le_of_gt (Nat.pow_lt_pow_right hp1 hd)) hh
    have htop := height_le_shifted_cutoff_of_power ha' hp1.le hpar.2.2.2.2.2.2 hheight
    exact hP p (p ^ 2 / k) k hodd hlarge hHp htop hlo' hheight
  · exact (not_le_of_gt hmass hbase).elim

/-- Every rational scale above 116/63 and below two gives, uniformly for large
odd primes, an initial subgroup count less than 256k/p. Transfer the global
height-layer energy budget to the smaller Fourier height and use the
nonnegative interval kernel. No GRH is required. -/
theorem exists_uniform_height_layer_heilbronn_interval_bound {a b : ℕ} (ha : 0 < a)
    (hgap : 116 * a < 63 * b) (hsmall : b < 2 * a) :
    ∃ P : ℕ,
      ∀ (p : ℕ) [Fact p.Prime],
        Odd p →
          P ≤ p →
          ∃ k : ℕ,
            0 < k ∧
              k < p ^ 2 ∧
              p ^ b ≤ k ^ a ∧ k ^ a ≤ 2 ^ a * p ^ b ∧ p * heilbronnInitialCount p k < 256 * k := by
  obtain ⟨P, hP⟩ := exists_uniform_height_layer_rational_energy_budget ha hgap hsmall
  refine ⟨max P (32 ^ a * 2 ^ a + 1), ?_⟩
  intro p hp hodd hlarge
  have hPp := (max_le_iff.mp hlarge).1
  have hc : 32 ^ a * 2 ^ a < p := lt_of_lt_of_le (Nat.lt_succ_self _) (max_le_iff.mp hlarge).2
  obtain ⟨k, hk, hkp, hlo, hhi, hb⟩ := hP p hodd hPp
  have hheight :=
    rational_cutoff_thirty_two_mul_lt_square (Fact.out : p.Prime).one_lt ha hsmall hc hhi
  have h32 : k ≤ 32 * k := by nlinarith only [hk]
  have hkp' := h32.trans_lt hheight
  refine ⟨k, hk, hkp', hlo, hhi, ?_⟩
  apply heilbronnInitialCount_lt_of_floor_energy_budget hk hkp' hheight.le
  have hmono :=
    boundedCongruenceCount_mono (p := p) (Nat.div_le_div_left h32 hk : p ^ 2 / (32 * k) ≤ p ^ 2 / k)
  have hm := Nat.mul_le_mul_left (p * heilbronnEnergy p) hmono
  exact hm.trans_lt hb

end PseudoPrime.NumberTheory.Heilbronn
