/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticSignedGamma
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleConductors

/-! # Actual pair-character Gamma gap under MR passage -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For a squarefree three-prime product with Korselt predecessors and
uniform valuations, passage of every prime through the cutoff forces the
actual Gamma gap inequality. Construct the three original pair characters,
their primitivity, nonprincipality, evenness and small-prime triviality
internally. Pair levels at least 20000 permit using each as its own ambient
analytic level. This supplies formula (G) to the finite-cell witness transfer. -/
theorem gamma_pair_gap_of_all_pass {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r) (hpq : 20000 ≤ p * q) (hpr : 20000 ≤ p * r)
    (hqr : 20000 ≤ q * r) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hn : 1 < n) (ho : Odd n) (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n)
    (hrn : r ∣ n) (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {X x : ℝ} (hx : 2 ≤ x) (s : Finset ℕ)
    (hs : ∀ k ∈ s, (k : ℝ) ≤ X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    4 * (∑ k ∈ s, Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x) ≤
      (∑' k : ℕ, Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x) +
            2 * (11783423 / 25000000 : ℝ) * (Real.log n) -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ s, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * (Real.log n) + 12) / Real.sqrt x +
        (105 / 2 : ℝ) * x ^ (-9 / 16 : ℝ) +
        3 / (x * Real.sqrt x) := by
  let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
  let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
  let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
  apply
    three_even_gamma_gap_le a b c hpq hpr hqr
      (NumberTheory.complexJacobiNumeratorCharacter_isQuadratic _ _)
      (NumberTheory.complexJacobiNumeratorCharacter_isQuadratic _ _)
      (NumberTheory.complexJacobiNumeratorCharacter_isQuadratic _ _)
      (pair_character_primitive hsq hpqn (hp.mul hq))
      (pair_character_primitive hsq hprn (hp.mul hr))
      (pair_character_primitive hsq hqrn (hq.mul hr))
      (pair_character_ne_one hsq hpqn (hp.mul hq) ((by decide : 1 < 20000).trans_le hpq))
      (pair_character_ne_one hsq hprn (hp.mul hr) ((by decide : 1 < 20000).trans_le hpr))
      (pair_character_ne_one hsq hqrn (hq.mul hr) ((by decide : 1 < 20000).trans_le hqr))
      (pair_character_even_of_korselt hn ho hp hq hpK hqK hvq)
      (pair_character_even_of_korselt hn ho hp hr hpK hrK hvr)
      (pair_character_even_of_korselt hn ho hq hr hqK hrK (hvr.trans hvq.symm)) hGRH hx
      (pair_level_log_sum hnprod) s hs
  · intro k
    simpa only [Int.cast_natCast] using
      pair_character_sum_ge_neg_one (k : ℤ) p q r (hp.mul hq) (hp.mul hr) (hq.mul hr)
  · intro l hl hlX
    exact pair_character_nat_eq_one hn ho hp hq hpn hqn hpqn hpK hqK hvq l (hpass l hl hlX)
  · intro l hl hlX
    exact pair_character_nat_eq_one hn ho hp hr hpn hrn hprn hpK hrK hvr l (hpass l hl hlX)
  · intro l hl hlX
    exact
      pair_character_nat_eq_one hn ho hq hr hqn hrn hqrn hqK hrK (hvr.trans hvq.symm) l
        (hpass l hl hlX)

/-- If all primes through a real cutoff pass MR for an odd modulus, each
prime divisor exceeds the cutoff. A divisor itself is a rejecting base.
This removes small-factor exceptions from the pair-character branch. -/
theorem factor_gt_of_all_prime_pass {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hpn : p ∣ n)
    {X : ℝ}
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    X < (p : ℝ) :=
  lt_of_not_ge
    (fun h ↦ PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hpn (hpass p hp h))

/-- Above cutoff 142, universal small-prime passage forces any two prime
divisors to have product at least 20000. Each factor is at least 143.
This discharges the ambient-level entrance for the reflected Gamma bounds. -/
theorem pair_level_large_of_all_pass {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpn : p ∣ n) (hqn : q ∣ n) {X : ℝ} (hX : 142 ≤ X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    20000 ≤ p * q := by
  have hpR : (142 : ℝ) < p := hX.trans_lt (factor_gt_of_all_prime_pass hn ho hp hpn hpass)
  have hqR : (142 : ℝ) < q := hX.trans_lt (factor_gt_of_all_prime_pass hn ho hq hqn hpass)
  have hpN : 143 ≤ p := by exact_mod_cast hpR
  have hqN : 143 ≤ q := by exact_mod_cast hqR
  exact (by decide : 20000 ≤ 143 * 143).trans (Nat.mul_le_mul hpN hqN)

/-- Universal prime passage through a cutoff at least 142 yields the
three-prime Gamma gap without separate lower bounds for the pair levels.
Derive those bounds from the rejecting-prime-factor criterion and apply
the actual pair-character comparison. This prepares the finite-cell transfer. -/
theorem gamma_pair_gap_of_cutoff_pass {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {X x : ℝ} (hx : 2 ≤ x) (s : Finset ℕ)
    (hs : ∀ k ∈ s, (k : ℝ) ≤ X) (hX : 142 ≤ X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    4 * (∑ k ∈ s, Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x) ≤
      (∑' k : ℕ, Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x) +
            2 * (11783423 / 25000000 : ℝ) * (Real.log n) -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ s, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * (Real.log n) + 12) / Real.sqrt x +
        (105 / 2 : ℝ) * x ^ (-9 / 16 : ℝ) +
        3 / (x * Real.sqrt x) := by
  have hpq :=
    pair_level_large_of_all_pass hn ho (Fact.out : p.Prime) (Fact.out : q.Prime) hpn hqn hX hpass
  have hpr :=
    pair_level_large_of_all_pass hn ho (Fact.out : p.Prime) (Fact.out : r.Prime) hpn hrn hX hpass
  have hqr :=
    pair_level_large_of_all_pass hn ho (Fact.out : q.Prime) (Fact.out : r.Prime) hqn hrn hX hpass
  exact
    gamma_pair_gap_of_all_pass hsq hnprod hpq hpr hqr hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn
      hpK hqK hrK hvq hvr hx s hs hpass

/-- A strict numerical reversal of the actual Gamma gap yields a rejecting
prime within the cutoff for the squarefree Korselt triple. If no such prime
exists, all small primes pass and the analytic comparison contradicts the
strict inequality. This transfers finite numerical certificates to actual
MR witnesses without an external character hypothesis. -/
theorem exists_prime_reject_of_gamma_gap {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {X x : ℝ} (hx : 2 ≤ x) (s : Finset ℕ)
    (hs : ∀ k ∈ s, (k : ℝ) ≤ X) (hX : 142 ≤ X)
    (hgap :
      (∑' k : ℕ, Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x) +
              2 * (11783423 / 25000000 : ℝ) * (Real.log n) -
            477 / 100 +
          ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
            4 * ∑ k ∈ s, Analysis.gammaResolventMangoldtWeight k) +
          ((7 / 3 : ℝ) * (Real.log n) + 12) / Real.sqrt x +
          (105 / 2 : ℝ) * x ^ (-9 / 16 : ℝ) +
          3 / (x * Real.sqrt x) <
        4 * (∑ k ∈ s, Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x)) :
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  classical
  by_contra h
  have hall (l : ℕ) (hl : l.Prime) (hlX : (l : ℝ) ≤ X) :
    PrimeTest.StrongMillerRabinPass n (l : ZMod n) :=
    Classical.byContradiction (fun hf ↦ h ⟨l, hl, hlX, hf⟩)
  exact
    (not_le_of_gt hgap)
      (gamma_pair_gap_of_cutoff_pass hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
        hqK hrK hvq hvr hx s hs hX hall)

end PseudoPrime.PrimeTestBounds.MillerRabin
