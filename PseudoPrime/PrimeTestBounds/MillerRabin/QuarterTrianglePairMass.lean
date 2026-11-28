/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangleZeroMass
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticPairSign
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleConductors

/-! # Triangle zero masses for the three Jacobi pair characters -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For two Korselt factors with the same predecessor valuation, small prime
passes bound the zero mass of their Jacobi character at its exact pair conductor. -/
theorem triangle_pair_zero_mass {n p q : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero (p * q)]
    [Fact p.Prime] [Fact q.Prime] [Fact (2 < p)] [Fact (2 < q)] (hn : 1 < n) (ho : Odd n)
    (hs : Squarefree n) (hp : Odd p) (hq : Odd q) (hd : p * q ∣ n) (hk : p - 1 ∣ n - 1)
    (hj : q - 1 ∣ n - 1) (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hb :
      ∀ b : ℕ, b.Prime → b ≤ ⌊Real.exp (5 / 2)⌋₊ → PrimeTest.StrongMillerRabinPass n (b : ZMod n)) :
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 5 / 4)
    let χ := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    (2 / 5) * (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) < Real.log (p * q : ℕ) - 28 / 5 := by
  have hprod :=
    (Fact.out : p.Prime).one_lt.trans_le (Nat.le_mul_of_pos_right p (Fact.out : q.Prime).pos)
  apply
    triangle_zero_mass_of_prime_pass hprod hGRH (pair_character_primitive hs hd (hp.mul hq))
      (pair_character_ne_one hs hd (hp.mul hq) hprod)
      (NumberTheory.complexJacobiNumeratorCharacter_isQuadratic _ _).inv
      (pair_character_even_of_korselt hn ho hp hq hk hj hv)
  intro b hprime hbound
  exact
    pair_character_nat_eq_one hn ho hp hq ((dvd_mul_right p q).trans hd)
      ((dvd_mul_left q p).trans hd) hd hk hj hv b (hb b hprime hbound)

/-- For a squarefree uniform Korselt triple passing the origin primes, the three
normalized absolute zero masses together are strictly below twice log n minus 84/5. -/
theorem triangle_triple_zero_mass {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hs : Squarefree n) (he : n = p * q * r) (hp : Odd p) (hq : Odd q)
    (hr : Odd r) (hk : p - 1 ∣ n - 1) (hj : q - 1 ∣ n - 1) (hm : r - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hw : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hb :
      ∀ b : ℕ, b.Prime → b ≤ ⌊Real.exp (5 / 2)⌋₊ → PrimeTest.StrongMillerRabinPass n (b : ZMod n)) :
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 5 / 4)
    let mass {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) :=
      (2 / 5 : ℝ) * ∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖
    mass (NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hq)) +
        mass (NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hr)) +
        mass (NumberTheory.complexJacobiNumeratorCharacter _ (hq.mul hr)) <
      2 * Real.log n - 84 / 5 := by
  have ha : p * q ∣ n := he ▸ dvd_mul_right _ _
  have hB : p * r ∣ n := by
    rw [he, mul_right_comm]; exact dvd_mul_right _ _
  have hc : q * r ∣ n := by
    rw [he, Nat.mul_assoc]; exact dvd_mul_left _ _
  have hab := triangle_pair_zero_mass hn ho hs hp hq ha hk hj hv hGRH hb
  have hac := triangle_pair_zero_mass hn ho hs hp hr hB hk hm hw hGRH hb
  have hbc := triangle_pair_zero_mass hn ho hs hq hr hc hj hm (hw.trans hv.symm) hGRH hb
  dsimp only at hab hac hbc ⊢
  linarith only [hab, hac, hbc, pair_level_log_sum he]

end PseudoPrime.PrimeTestBounds.MillerRabin
