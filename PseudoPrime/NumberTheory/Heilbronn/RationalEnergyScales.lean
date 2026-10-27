/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.HeilbronnIntervalBound

/-! # Rational cutoff scales above the Heilbronn exponent 13/7 -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Given positive a and 13a<7b<14a, select positive polynomial parameters n,r.
The height exponent d=2a-b satisfies 14d<2a, and the complete polynomial
energy exponent has a strict gap below 4bn7r. Keep all coefficients symbolic.
This supplies the numerical parameters for rational cutoff scales b/a. -/
theorem exists_rational_energy_parameters {a b : ℕ} (hgap : 13 * a < 7 * b) (hsmall : b < 2 * a) :
    ∃ n r : ℕ,
      0 < n ∧
        0 < r ∧
        (2 * a - b) * 14 < 2 * a ∧
        a * (7 * (n * 7 * r)) + (2 * a - b) * congruencePolynomialHeightExponent 7 n r +
            a * (n * r) <
          b * (4 * (n * 7 * r)) := by
  let d := 2 * a - b
  let n := 42 * d + 1
  let r := d * (14 * n + 168 * n ^ 2) + 1
  have hbd : b + d = 2 * a := Nat.add_sub_of_le hsmall.le
  have hn : 0 < n := Nat.succ_pos _
  have hr : 0 < r := Nat.succ_pos _
  have hd : d * 14 < 2 * a := by nlinarith only [hgap, hbd]
  have hmul := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hgap)
  have hbdn := congrArg (fun x : ℕ ↦ x * n) hbd
  have hlead : a * (50 * n) + d * (14 * n + 42) < b * (28 * n) := by
    dsimp only [n] at hmul hbdn ⊢
    nlinarith only [hmul, hbdn]
  have hleadR := Nat.mul_le_mul_right r (Nat.succ_le_of_lt hlead)
  refine ⟨n, r, hn, hr, hd, ?_⟩
  dsimp only [congruencePolynomialHeightExponent]
  norm_num only
  change
    a * (7 * (n * 7 * r)) + d * (2 * (n * 7 * r) + 42 * r + 2 * (n * 7) + 28 * (n ^ 2 * 6)) +
        a * (n * r) <
      _
  have hrest : d * (14 * n + 168 * n ^ 2) < r := Nat.lt_succ_self _
  nlinarith only [hleadR, hrest]

/-- For 13a<7b and b<2a, all sufficiently large odd primes admit a cutoff
with p^b<=k^a<=2^a*p^b and the strict weighted energy budget at floor(p²/k).
Select polynomial parameters, absorb their fixed coefficient into p, and
use exact integer-root selection. The threshold depends only on a,b,M. -/
theorem exists_uniform_rational_energy_budget {a b M : ℕ} (ha : 0 < a) (hgap : 13 * a < 7 * b)
    (hsmall : b < 2 * a) :
    ∃ P : ℕ,
      ∀ (p : ℕ) [Fact p.Prime],
        Odd p →
          P ≤ p →
          ∃ k : ℕ,
            0 < k ∧
              k ≤ p ^ 2 ∧
              p ^ b ≤ k ^ a ∧
              k ^ a ≤ 2 ^ a * p ^ b ∧
              (M * p) * heilbronnEnergy p * boundedCongruenceCount p (p ^ 2 / k) < k ^ 2 := by
  obtain ⟨n, r, hn, hr, hd, hbal⟩ := exists_rational_energy_parameters hgap hsmall
  refine ⟨weightedCongruenceEnergyCoefficient M 7 n r ^ a + 1, ?_⟩
  intro p hp hodd hlarge
  have hp0 := (Fact.out : p.Prime).pos
  have hp1 := (Fact.out : p.Prime).one_lt
  have hmass : p ^ b < (p ^ 2) ^ a := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right hp1 hsmall
  rcases exists_power_cutoff_or_base (U := p ^ 2) (Nat.pow_pos (n := b) hp0) ha with
    ⟨k, hk, hkp, hlo, hhi⟩ | hbase
  · refine ⟨k, hk, hkp, hlo, hhi, ?_⟩
    have hheight := floor_power_budget hp0 hsmall.le hlo
    exact
      weighted_energy_budget_of_power_scales hodd (Nat.div_pos hkp hk) (by norm_num only : 0 < 7) hn
        hr ha hp1 (power_height_injectivity ha hp1 hheight hd) hheight hlo
        (lt_of_lt_of_le (Nat.lt_succ_self _) hlarge) hbal
  · exact (not_le_of_gt hmass hbase).elim

/-- For positive a and b<2a, a rational cutoff upper bound implies 32k<p²
once 32^a*2^a<p. Compare a-th powers and absorb the fixed coefficient in one
power of p. This supplies the positive reciprocal height of the interval kernel. -/
theorem rational_cutoff_thirty_two_mul_lt_square {p k a b : ℕ} (hp : 1 < p) (ha : 0 < a)
    (hsmall : b < 2 * a) (hlarge : 32 ^ a * 2 ^ a < p) (hcut : k ^ a ≤ 2 ^ a * p ^ b) :
    32 * k < p ^ 2 := by
  apply (Nat.pow_lt_pow_iff_left (ne_of_gt ha)).mp
  calc
    (32 * k) ^ a = 32 ^ a * k ^ a := Nat.mul_pow _ _ _
    _ ≤ 32 ^ a * (2 ^ a * p ^ b) := Nat.mul_le_mul_left _ hcut
    _ = (32 ^ a * 2 ^ a) * p ^ b := by ring
    _ < p * p ^ b :=
      Nat.mul_lt_mul_of_pos_right hlarge (Nat.pow_pos (lt_trans (by decide : 0 < 1) hp))
    _ = p ^ (b + 1) := by rw [pow_succ, Nat.mul_comm]
    _ ≤ p ^ (2 * a) :=
      Nat.pow_le_pow_right (lt_trans (by decide : 0 < 1) hp) (Nat.succ_le_of_lt hsmall)
    _ = (p ^ 2) ^ a := by rw [← pow_mul]

/-- For any rational scale 13/7<b/a<2, sufficiently large odd primes admit
cutoffs p^b<=k^a<=2^a*p^b with p times the initial subgroup interval count
less than 256k. Restrict the energy height to floor(p²/(32k)) and apply the
nonnegative Fourier kernel. No GRH or external count hypothesis is used. -/
theorem exists_uniform_rational_heilbronn_interval_bound {a b : ℕ} (ha : 0 < a)
    (hgap : 13 * a < 7 * b) (hsmall : b < 2 * a) :
    ∃ P : ℕ,
      ∀ (p : ℕ) [Fact p.Prime],
        Odd p →
          P ≤ p →
          ∃ k : ℕ,
            0 < k ∧
              k < p ^ 2 ∧
              p ^ b ≤ k ^ a ∧ k ^ a ≤ 2 ^ a * p ^ b ∧ p * heilbronnInitialCount p k < 256 * k := by
  obtain ⟨P, hP⟩ := exists_uniform_rational_energy_budget (M := 1) ha hgap hsmall
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
  simp only [one_mul] at hb
  exact hm.trans_lt hb

end PseudoPrime.NumberTheory.Heilbronn
