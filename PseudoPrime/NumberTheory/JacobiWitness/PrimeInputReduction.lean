/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.JacobiWitness.Basic
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Prime inputs and the quadratic nonresidue content of uniform Jacobi bounds -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- For p=1 mod 4 and odd q, reciprocity identifies the Jacobi value (p/q)
with the Legendre value (q/p). No primality assumption on q is needed. -/
theorem jacobi_prime_input_eq_legendre {p q : ℕ} [Fact p.Prime] (hp4 : p % 4 = 1) (hq : Odd q) :
    jacobiSym (p : ℤ) q = legendreSym p (q : ℤ) := by
  rw [jacobiSym.quadratic_reciprocity_one_mod_four hp4 hq, ← jacobiSym.legendreSym.to_jacobiSym]

/-- For prime p=1 mod 8, two is a quadratic residue modulo p, by the supplementary law. -/
theorem legendre_two_eq_one_of_one_mod_eight {p : ℕ} [Fact p.Prime] (hp8 : p % 8 = 1) :
    legendreSym p 2 = 1 := by
  have hp2 : p ≠ 2 := by
    intro he
    norm_num only [he, Nat.reduceMod] at hp8
  rw [legendreSym.at_two hp2, ZMod.χ₈_nat_mod_eight p, hp8, Nat.cast_one, map_one]

/-- For prime p=1 mod 8, its odd-prime negative Jacobi witnesses are exactly
its prime quadratic nonresidues. Two is excluded by its Legendre value one. -/
theorem negative_prime_witness_iff_nonresidue {p q : ℕ} [Fact p.Prime] (hp8 : p % 8 = 1) :
    q ∈ primeNegOneWitnessSet p ↔ q.Prime ∧ legendreSym p (q : ℤ) = -1 := by
  have hp4 : p % 4 = 1 := by
    have h := Nat.mod_mod_of_dvd p (by decide : 4 ∣ 8)
    rw [hp8] at h
    exact h.symm
  constructor
  · intro h
    exact ⟨h.1, (jacobi_prime_input_eq_legendre hp4 h.2.1) ▸ h.2.2⟩
  · rintro ⟨hq, hleg⟩
    have hq2 : q ≠ 2 := by
      intro he
      rw [he, Nat.cast_ofNat, legendre_two_eq_one_of_one_mod_eight hp8] at hleg
      norm_num only at hleg
    have hodd := hq.odd_of_ne_two hq2
    exact ⟨hq, hodd, (jacobi_prime_input_eq_legendre hp4 hodd).symm ▸ hleg⟩

/-- Below p, a non-one Jacobi witness for prime p=1 mod 8 is exactly a prime quadratic
nonresidue. The strict upper bound excludes the zero value at q=p. -/
theorem non_one_prime_witness_iff_nonresidue_below_prime {p q : ℕ} [Fact p.Prime] (hp8 : p % 8 = 1)
    (hqp : q < p) : q ∈ primeNeOneWitnessSet p ↔ q.Prime ∧ legendreSym p (q : ℤ) = -1 := by
  constructor
  · intro h
    have hp4 : p % 4 = 1 := by
      have he := Nat.mod_mod_of_dvd p (by decide : 4 ∣ 8)
      rw [hp8] at he
      exact he.symm
    have hnz : ((q : ℤ) : ZMod p) ≠ 0 := by
      rw [Int.cast_natCast]
      intro hz
      have he := congrArg ZMod.val hz
      rw [ZMod.val_natCast_of_lt hqp, ZMod.val_zero] at he
      exact (Nat.ne_of_gt h.1.pos) he
    refine ⟨h.1, (legendreSym.eq_neg_one_iff_not_one p hnz).mpr ?_⟩
    rw [← jacobi_prime_input_eq_legendre hp4 h.2.1]
    exact h.2.2
  · intro h
    exact
      primeNegOneWitnessSet.subset_primeNeOneWitnessSet p
        ((negative_prime_witness_iff_nonresidue hp8).mpr h)

/-- For prime p=1 mod 8, bounded negative Jacobi witness existence is equivalent
to bounded prime quadratic nonresidue existence for any real bound. -/
theorem exists_negative_prime_witness_le_iff_nonresidue {p : ℕ} [Fact p.Prime] (hp8 : p % 8 = 1)
    (B : ℝ) :
    (∃ q ∈ primeNegOneWitnessSet p, (q : ℝ) ≤ B) ↔
      (∃ q : ℕ, q.Prime ∧ (q : ℝ) ≤ B ∧ legendreSym p (q : ℤ) = -1) := by
  constructor
  · rintro ⟨q, hq, hb⟩
    have h := (negative_prime_witness_iff_nonresidue hp8).mp hq
    exact ⟨q, h.1, hb, h.2⟩
  · rintro ⟨q, hq, hb, hleg⟩
    exact ⟨q, (negative_prime_witness_iff_nonresidue hp8).mpr ⟨hq, hleg⟩, hb⟩

/-- The same bounded equivalence holds for non-one witnesses when the bound is below p.
Retain this restriction so that a zero Legendre value is not treated as negative. -/
theorem exists_non_one_prime_witness_le_iff_nonresidue {p : ℕ} [Fact p.Prime] (hp8 : p % 8 = 1)
    {B : ℝ} (hBp : B < p) :
    (∃ q ∈ primeNeOneWitnessSet p, (q : ℝ) ≤ B) ↔
      (∃ q : ℕ, q.Prime ∧ (q : ℝ) ≤ B ∧ legendreSym p (q : ℤ) = -1) := by
  constructor
  · rintro ⟨q, hq, hb⟩
    have hqp : q < p := Nat.cast_lt.mp (hb.trans_lt hBp)
    have h := (non_one_prime_witness_iff_nonresidue_below_prime hp8 hqp).mp hq
    exact ⟨q, h.1, hb, h.2⟩
  · rintro ⟨q, hq, hb, hleg⟩
    exact
      ⟨q,
        primeNegOneWitnessSet.subset_primeNeOneWitnessSet p
          ((negative_prime_witness_iff_nonresidue hp8).mpr ⟨hq, hleg⟩),
        hb⟩

/-- If the least non-one witness is below prime p=1 mod 8, it equals the least negative witness.
Use the negative membership criterion and minimality in both directions. -/
theorem primeNeOneWitness_eq_primeNegOneWitness_of_lt_prime {p : ℕ} [Fact p.Prime] (hp8 : p % 8 = 1)
    (hneg : (primeNegOneWitnessSet p).Nonempty)
    (hsmall : primeNeOneWitness p (primeNeOneWitnessSet_nonempty_of_negOne hneg) < p) :
    primeNeOneWitness p (primeNeOneWitnessSet_nonempty_of_negOne hneg) =
      primeNegOneWitness p hneg := by
  apply Nat.le_antisymm (primeNeOneWitness_le_primeNegOneWitness p hneg)
  have hm := primeNeOneWitness_mem p (primeNeOneWitnessSet_nonempty_of_negOne hneg)
  have hleg := (non_one_prime_witness_iff_nonresidue_below_prime hp8 hsmall).mp hm
  exact primeNegOneWitness_le p hneg ((negative_prime_witness_iff_nonresidue hp8).mpr hleg)

/-- A prime natural number is not a square. A square root dividing the prime must be one
or the prime itself, and both possibilities contradict primality. -/
theorem prime_not_isSquare {p : ℕ} (hp : p.Prime) : ¬IsSquare p := by
  rintro ⟨a, ha⟩
  have hd : a ∣ p := ha ▸ dvd_mul_right a a
  rcases (Nat.dvd_prime hp).mp hd with h1 | he
  · rw [h1, one_mul] at ha
    exact hp.ne_one ha
  · rw [he] at ha
    nlinarith only [ha, hp.one_lt]

/-- For any real C,A, the function C*log(n)^A is eventually below n.
Use the standard little-o estimate with exponent one; no witness existence is asserted. -/
theorem eventually_const_log_power_lt_self (C A : ℝ) :
    Filter.Eventually (fun n : ℕ ↦ C * (Real.log n) ^ A < (n : ℝ)) Filter.atTop := by
  have h₀ := (isLittleO_log_rpow_rpow_atTop A (s := 1) zero_lt_one).const_mul_left C
  have h := h₀.tendsto_div_nhds_zero
  have hs := (h.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_lt_const zero_lt_one
  filter_upwards [hs, Filter.eventually_gt_atTop (0 : ℕ)] with n hn hpos
  have hb : C * (Real.log n) ^ A / (n : ℝ) < 1 := by
    simpa only [Function.comp_apply, Real.rpow_one] using hn
  exact (div_lt_one (Nat.cast_pos.mpr hpos)).mp hb

/-- Any eventual negative Jacobi witness bound on all odd nonsquares yields the same
prime quadratic nonresidue bound for p=1 mod 8, by restriction and reciprocity. -/
theorem eventually_prime_nonresidue_of_negative_bound (F : ℕ → ℝ)
    (hbound :
      Filter.Eventually
        (fun n : ℕ ↦ Odd n → ¬IsSquare n → ∃ q ∈ primeNegOneWitnessSet n, (q : ℝ) ≤ F n)
        Filter.atTop) :
    Filter.Eventually
      (fun p : ℕ ↦
        ∀ hp : p.Prime,
          p % 8 = 1 → ∃ q : ℕ, q.Prime ∧ (q : ℝ) ≤ F p ∧ @legendreSym p ⟨hp⟩ (q : ℤ) = -1)
      Filter.atTop := by
  apply hbound.mono
  intro p hb hp hp8
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    intro he
    norm_num only [he, Nat.reduceMod] at hp8
  exact
    (exists_negative_prime_witness_le_iff_nonresidue hp8 (F p)).mp
      (hb (hp.odd_of_ne_two hp2) (prime_not_isSquare hp))

/-- Any eventual non-one Jacobi log-power bound on all odd nonsquares yields the same
prime quadratic nonresidue bound for primes p=1 mod 8. First put the bound below p
using its sublinear growth, then exclude zero values. -/
theorem eventually_prime_nonresidue_of_non_one_log_bound (C A : ℝ)
    (hbound :
      Filter.Eventually
        (fun n : ℕ ↦
          Odd n → ¬IsSquare n → ∃ q ∈ primeNeOneWitnessSet n, (q : ℝ) ≤ C * (Real.log n) ^ A)
        Filter.atTop) :
    Filter.Eventually
      (fun p : ℕ ↦
        ∀ hp : p.Prime,
          p % 8 = 1 →
            ∃ q : ℕ, q.Prime ∧ (q : ℝ) ≤ C * (Real.log p) ^ A ∧ @legendreSym p ⟨hp⟩ (q : ℤ) = -1)
      Filter.atTop := by
  filter_upwards [hbound, eventually_const_log_power_lt_self C A] with p hb hsmall hp hp8
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    intro he
    norm_num only [he, Nat.reduceMod] at hp8
  exact
    (exists_non_one_prime_witness_le_iff_nonresidue hp8 hsmall).mp
      (hb (hp.odd_of_ne_two hp2) (prime_not_isSquare hp))

end PseudoPrime.NumberTheory
