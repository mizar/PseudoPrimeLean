/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.ThirteenthFiniteFiberBudget
public import PseudoPrime.NumberTheory.Heilbronn.FiniteFiberRationalScales
public import PseudoPrime.NumberTheory.Heilbronn.RationalEnergyScales

/-! # Rational Heilbronn scales above 5977/3276 -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Every rational scale b/a strictly above 5977/3276 and below two
admits the fixed scaled parameters 1176a,1176b,14a+1. The integer exponent gap
leaves strict energy slack and the height lies below p^(5/28). These rational
choices are uniform in the prime and do not assert the endpoint. -/
theorem thirteenth_finite_fiber_rational_parameters {a b : ℕ} (ha : 0 < a)
    (hgap : 5977 * a < 3276 * b) (hsmall : b < 2 * a) :
    71 * (1176 * a) + 13 * (14 * a + 1) < 39 * (1176 * b) ∧
      (0 : ℝ) < 1 / (1176 * a) ∧
      ((14 * a + 1 : ℕ) : ℝ) / (1176 * a : ℕ) = 1 / 84 + 1 / (1176 * a) ∧
      ((2 * (1176 * a) - 1176 * b : ℕ) : ℝ) / (1176 * a : ℕ) ≤ 5 / 28 := by
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hg : (5977 : ℝ) * a + 1 ≤ 3276 * b := by
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat] using
      (Nat.cast_le (α := ℝ).mpr (Nat.succ_le_of_lt hgap))
  have hb : 1176 * b ≤ 2 * (1176 * a) := by nlinarith only [hsmall]
  refine
    ⟨by nlinarith only [Nat.succ_le_of_lt hgap],
      div_pos (by norm_num only) (mul_pos (by norm_num only) haR), ?_, ?_⟩
  · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, add_div]
    have he : (14 * a : ℝ) / (1176 * a) = 1 / 84 := by
      apply
        (div_eq_div_iff (ne_of_gt (mul_pos (by norm_num only) haR))
            (by norm_num only : (84 : ℝ) ≠ 0)).mpr
      ring
    rw [he]
  · rw [Nat.cast_sub hb]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    apply (div_le_iff₀ (mul_pos (by norm_num only) haR)).mpr
    nlinarith only [hg, haR]

/-- For each fixed rational 5977/3276<b/a<2, all sufficiently large odd
primes admit a cutoff with the strict Heilbronn energy budget. Fix the
finite-fiber parameters, use the logarithmic-exponent-two energy estimate,
and select an exact natural cutoff. No GRH or additional count hypothesis is
required. -/
theorem exists_thirteenth_finite_fiber_rational_energy_budget {a b : ℕ} (ha : 0 < a)
    (hgap : 5977 * a < 3276 * b) (hsmall : b < 2 * a) :
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
  have hpar := thirteenth_finite_fiber_rational_parameters ha hgap hsmall
  have ha' : 0 < 1176 * a := Nat.mul_pos (by decide) ha
  have hb' : 1176 * b ≤ 2 * (1176 * a) := by nlinarith only [hsmall]
  obtain ⟨P, hP⟩ := exists_log_square_finite_fiber_energy_budget hpar.2.1 ha' hpar.2.2.1 hb' hpar.1
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
    have hlo' : p ^ (1176 * b) ≤ k ^ (1176 * a) := by
      have hh := Nat.pow_le_pow_left hlo 1176
      simpa only [← pow_mul, Nat.mul_comm] using hh
    have hheight := floor_power_budget hp0 hb' hlo'
    have hd : 2 * (1176 * a) - 1176 * b < 1176 * a := by
      apply (Nat.sub_lt_iff_lt_add hb').mpr
      nlinarith only [hgap]
    have hHp : p ^ 2 / k < p := by
      by_contra hn
      have hh := (Nat.pow_le_pow_left (Nat.le_of_not_gt hn) (1176 * a)).trans hheight
      exact (not_le_of_gt (Nat.pow_lt_pow_right hp1 hd)) hh
    have htop := height_le_real_power_of_power ha' hp1.le hpar.2.2.2 hheight
    exact hP p (p ^ 2 / k) k hodd hlarge hHp htop hlo' hheight
  · exact (not_le_of_gt hmass hbase).elim

/-- For every fixed rational scale above 5977/3276 and below two, uniformly
for sufficiently large odd primes, a cutoff has initial subgroup count
less than 256k/p. Transfer the energy budget to the smaller Fourier height.
This supplies the existing smooth-number-to-Fermat-quotient argument. -/
theorem exists_thirteenth_finite_fiber_heilbronn_interval_bound {a b : ℕ} (ha : 0 < a)
    (hgap : 5977 * a < 3276 * b) (hsmall : b < 2 * a) :
    ∃ P : ℕ,
      ∀ (p : ℕ) [Fact p.Prime],
        Odd p →
          P ≤ p →
          ∃ k : ℕ,
            0 < k ∧
              k < p ^ 2 ∧
              p ^ b ≤ k ^ a ∧ k ^ a ≤ 2 ^ a * p ^ b ∧ p * heilbronnInitialCount p k < 256 * k := by
  obtain ⟨P, hP⟩ := exists_thirteenth_finite_fiber_rational_energy_budget ha hgap hsmall
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
  exact (Nat.mul_le_mul_left (p * heilbronnEnergy p) hmono).trans_lt hb

end PseudoPrime.NumberTheory.Heilbronn
