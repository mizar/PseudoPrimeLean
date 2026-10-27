/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.PolynomialEnergyScales

/-! # Uniform subquadratic energy budgets with truncation height allowance -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For m=7,n=24 and r at least 16185, prove the strict exponent balance for a=120,d=17,b=224.
The exponent difference is 102*r-1650768. Evaluate only the small integer coefficients. -/
theorem energy_balance_seven_twentyfour {r : ℕ} (hr : 16185 ≤ r) :
    120 * (7 * (24 * 7 * r)) + 17 * congruencePolynomialHeightExponent 7 24 r + 120 * (24 * r) <
      224 * (4 * (24 * 7 * r)) := by
  norm_num only [congruencePolynomialHeightExponent]
  nlinarith only [hr]

/-- For odd prime p, positive H, r at least 16185, H^120 at most p^17 and p^28 at most k^15,
coefficient absorption gives M*p*energy*fullCount less than k^2.
The height allowance exceeds p^(2/15), retaining room for a later Fourier truncation loss.
Raise the cutoff inequality to the eighth power and apply the generic scale comparison. -/
theorem weighted_energy_budget_twenty_eight_fifteenths {p H M k r : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hH : 0 < H) (hr : 16185 ≤ r) (hheight : H ^ 120 ≤ p ^ 17) (hcut : p ^ 28 ≤ k ^ 15)
    (hcoefficient : weightedCongruenceEnergyCoefficient M 7 24 r ^ 120 < p) :
    (M * p) * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2 := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have ha : 0 < (120 : ℕ) := by norm_num only
  have hcut' : p ^ 224 ≤ k ^ 120 := by
    simpa only [← pow_mul, Nat.reduceMul] using Nat.pow_le_pow_left hcut 8
  exact
    weighted_energy_budget_of_power_scales hodd hH (by norm_num only : 0 < 7)
      (by norm_num only : 0 < 24) (lt_of_lt_of_le (by norm_num only : 0 < 16185) hr) ha hp
      (power_height_injectivity ha hp hheight (by norm_num only : 17 * (2 * 7) < 2 * 120)) hheight
      hcut' hcoefficient (energy_balance_seven_twentyfour hr)

/-- For odd prime p, r at least 16185 and p^28 at most k^15 with k at most p^2,
coefficient absorption gives the weighted energy comparison at floor(p^2/k).
Its fifteenth power is at most p^2, so its 120-th power is at most p^16 and hence p^17. -/
theorem weighted_energy_budget_floor_twenty_eight_fifteenths {p M k r : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hr : 16185 ≤ r) (hcut : p ^ 28 ≤ k ^ 15) (hsmall : k ≤ p ^ 2)
    (hcoefficient : weightedCongruenceEnergyCoefficient M 7 24 r ^ 120 < p) :
    (M * p) * heilbronnEnergy p * boundedCongruenceCount p (p ^ 2 / k) < k ^ 2 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hk : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hpos : 0 < k ^ 15 := (Nat.pow_pos hp).trans_le hcut
    rw [hz, zero_pow (by decide : 15 ≠ 0)] at hpos
    exact (Nat.lt_irrefl 0) hpos
  have hbase : (p ^ 2 / k) ^ 15 ≤ p ^ 2 := by
    have h := floor_power_budget hp (by norm_num only : 28 ≤ 2 * 15) hcut
    simpa only [Nat.reduceMul, Nat.reduceSub] using h
  have hheight : (p ^ 2 / k) ^ 120 ≤ p ^ 17 := by
    have hpow : (p ^ 2 / k) ^ 120 ≤ p ^ 16 := by
      simpa only [← pow_mul, Nat.reduceMul] using Nat.pow_le_pow_left hbase 8
    exact hpow.trans (Nat.pow_le_pow_right hp (by norm_num only : 16 ≤ 17))
  exact
    weighted_energy_budget_twenty_eight_fifteenths hodd (Nat.div_pos hsmall hk) hr hheight hcut
      hcoefficient

/-- Above the symbolic coefficient threshold, odd prime p admits positive k at most p^2 with
p^28 at most k^15 at most 32768*p^28 and the weighted energy gap at floor(p^2/k).
The cutoff has scale p^(28/15), strictly below p^(15/8); use exact natural-root selection. -/
theorem exists_weighted_short_congruence_energy_budget {p M r : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hr : 16185 ≤ r) (hcoefficient : weightedCongruenceEnergyCoefficient M 7 24 r ^ 120 < p) :
    ∃ k : ℕ,
      0 < k ∧
        k ≤ p ^ 2 ∧
        p ^ 28 ≤ k ^ 15 ∧
        k ^ 15 ≤ 32768 * p ^ 28 ∧
        (M * p) * heilbronnEnergy p * boundedCongruenceCount p (p ^ 2 / k) < k ^ 2 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hmass : p ^ 28 < (p ^ 2) ^ 15 := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by norm_num only)
  rcases
    exists_power_cutoff_or_base (U := p ^ 2) (Nat.pow_pos (n := 28) hp)
      (by norm_num only : 0 < 15) with
    ⟨k, hk, hkp, hlow, hhigh⟩ | hbase
  · refine
      ⟨k, hk, hkp, hlow, ?_,
        weighted_energy_budget_floor_twenty_eight_fifteenths hodd hr hlow hkp hcoefficient⟩
    simpa only [Nat.reducePow] using hhigh
  · exact (not_le_of_gt hmass hbase).elim

/-- For any fixed natural M and r at least 16185, choose a threshold independent of p,k so
every odd prime beyond it admits the proved 28/15-scale cutoff and weighted energy gap.
Choose weightedCongruenceEnergyCoefficient(M,7,24,r)^120+1 without evaluating it.
This closes the numerical comparison, with space below the target Fermat exponent 15/8;
it does not yet prove the Fourier interval bound or extract a nonzero Fermat quotient. -/
theorem exists_uniform_weighted_short_congruence_energy_budget {M r : ℕ} (hr : 16185 ≤ r) :
    ∃ P : ℕ,
      ∀ (p : ℕ) [Fact p.Prime],
        Odd p →
          P ≤ p →
          ∃ k : ℕ,
            0 < k ∧
              k ≤ p ^ 2 ∧
              p ^ 28 ≤ k ^ 15 ∧
              k ^ 15 ≤ 32768 * p ^ 28 ∧
              (M * p) * heilbronnEnergy p * boundedCongruenceCount p (p ^ 2 / k) < k ^ 2 := by
  refine ⟨weightedCongruenceEnergyCoefficient M 7 24 r ^ 120 + 1, ?_⟩
  intro p hp hodd hlarge
  exact
    exists_weighted_short_congruence_energy_budget hodd hr
      (lt_of_lt_of_le (Nat.lt_succ_self _) hlarge)

end PseudoPrime.NumberTheory.Heilbronn
