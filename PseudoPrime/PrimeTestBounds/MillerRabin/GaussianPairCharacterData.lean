/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticPairSign

/-! # Pair characters under uniform Korselt Miller–Rabin passage -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Passing prime bases for an odd uniform Korselt triple makes the three
Jacobi pair characters trivial on the tested primes. The pair characters
are primitive, nonprincipal, even and self-inverse. -/
public theorem pair_data_of_uniform_pass {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] [NeZero n]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n) (hprod : n = p * q * r) (hp : Odd p)
    (hq : Odd q) (hr : Odd r) (X : ℝ) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    (∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) →
      2 ≤ p * q ∧
        2 ≤ p * r ∧
        2 ≤ q * r ∧
        (a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) ∧
        (b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even) ∧
        (c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) ∧
        (∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1 ∧ b l = 1 ∧ c l = 1) := by
  intro a b c hpass
  have hpq : p * q ∣ n := ⟨r, hprod⟩
  have hpr : p * r ∣ n := ⟨q, hprod.trans (by ac_rfl)⟩
  have hqr : q * r ∣ n := ⟨p, hprod.trans (by ac_rfl)⟩
  have dp := (dvd_mul_right p q).trans hpq
  have dq := (dvd_mul_left q p).trans hpq
  have dr := (dvd_mul_left r p).trans hpr
  have hpK := hu.2.2.1 p Fact.out dp
  have hqK := hu.2.2.1 q Fact.out dq
  have hrK := hu.2.2.1 r Fact.out dr
  have hvq := hu.2.2.2 q p Fact.out Fact.out dq dp
  have hvr := hu.2.2.2 r p Fact.out Fact.out dr dp
  have hp₁ : 1 < p := (Fact.out : p.Prime).one_lt
  have hq₁ : 1 < q := (Fact.out : q.Prime).one_lt
  have hq₀ : 0 < q := (Fact.out : q.Prime).pos
  have hr₀ : 0 < r := (Fact.out : r.Prime).pos
  have hqp := (Fact.out : p.Prime).two_le.trans (Nat.le_mul_of_pos_right p hq₀)
  have hrp := (Fact.out : p.Prime).two_le.trans (Nat.le_mul_of_pos_right p hr₀)
  have hrq := (Fact.out : q.Prime).two_le.trans (Nat.le_mul_of_pos_right q hr₀)
  refine
    ⟨hqp, hrp, hrq,
      ⟨pair_character_primitive hu.1 hpq _,
        pair_character_ne_one hu.1 hpq _ (hp₁.trans_le (Nat.le_mul_of_pos_right _ hq₀)),
        (NumberTheory.complexJacobiNumeratorCharacter_isQuadratic _ _).inv,
        pair_character_even_of_korselt hn ho hp hq hpK hqK hvq⟩,
      ⟨pair_character_primitive hu.1 hpr _,
        pair_character_ne_one hu.1 hpr _ (hp₁.trans_le (Nat.le_mul_of_pos_right _ hr₀)),
        (NumberTheory.complexJacobiNumeratorCharacter_isQuadratic _ _).inv,
        pair_character_even_of_korselt hn ho hp hr hpK hrK hvr⟩,
      ⟨pair_character_primitive hu.1 hqr _,
        pair_character_ne_one hu.1 hqr _ (hq₁.trans_le (Nat.le_mul_of_pos_right _ hr₀)),
        (NumberTheory.complexJacobiNumeratorCharacter_isQuadratic _ _).inv,
        pair_character_even_of_korselt hn ho hq hr hqK hrK (hvr.trans hvq.symm)⟩,
      ?_⟩
  intro l hl hle
  have h := hpass l hl hle
  exact
    ⟨pair_character_nat_eq_one hn ho hp hq dp dq hpq hpK hqK hvq l h,
      pair_character_nat_eq_one hn ho hp hr dp dr hpr hpK hrK hvr l h,
      pair_character_nat_eq_one hn ho hq hr dq dr hqr hqK hrK (hvr.trans hvq.symm) l h⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
