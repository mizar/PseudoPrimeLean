/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleCharacters
public import PseudoPrime.Analysis.GammaSignedEulerSeries
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterFullTriviality

/-! # Coupled three-character Gamma Euler prefix estimate -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Three real sequences bounded individually by one have summable signed Gamma
Euler contributions. If their sum is at least minus one outside a finite prefix
and equals three on it, their combined Euler series is at most total mass minus
four times the prefix mass. Combine individual convergence with the coupled
prefix bound; this retains the actual Gamma weight for the three-character branch. -/
theorem gamma_three_euler_prefix_le (s : Finset ℕ) (a b c : ℕ → ℝ) (ha : ∀ n, |a n| ≤ 1)
    (hb : ∀ n, |b n| ≤ 1) (hc : ∀ n, |c n| ≤ 1) (ht : ∀ n ∉ s, -1 ≤ a n + b n + c n)
    (hp : ∀ n ∈ s, a n + b n + c n = 3) :
    (∑' n,
        ((-a n * Analysis.gammaResolventMangoldtWeight n +
            -b n * Analysis.gammaResolventMangoldtWeight n) +
          -c n * Analysis.gammaResolventMangoldtWeight n)) ≤
      (∑' n, Analysis.gammaResolventMangoldtWeight n) -
        4 * ∑ n ∈ s, Analysis.gammaResolventMangoldtWeight n := by
  apply
    coupled_euler_prefix_bound s _ _ Analysis.summable_gammaResolventMangoldtWeight
      (((Analysis.summable_gamma_signed_euler a ha).add
            (Analysis.summable_gamma_signed_euler b hb)).add
        (Analysis.summable_gamma_signed_euler c hc))
  · intro n hn
    have h := mul_le_mul_of_nonneg_right (ht n hn) (Analysis.gammaResolventMangoldtWeight_nonneg n)
    linarith only [h]
  · intro n hn
    have h := congrArg (fun t : ℝ ↦ t * Analysis.gammaResolventMangoldtWeight n) (hp n hn)
    linarith only [h]

/-- Three actual Dirichlet characters, possibly at different levels, satisfy
the coupled Gamma Euler prefix estimate when their real-part sum has the
simultaneous tail and prefix bounds. Their norm bounds supply convergence
internally. This connects the sequence estimate to original-level characters. -/
theorem gamma_three_character_prefix_le {p q r : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (s : Finset ℕ)
    (ht : ∀ n ∉ s, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hp : ∀ n ∈ s, (a n).re + (b n).re + (c n).re = 3) :
    (∑' n : ℕ,
        ((-(a n).re * Analysis.gammaResolventMangoldtWeight n +
            -(b n).re * Analysis.gammaResolventMangoldtWeight n) +
          -(c n).re * Analysis.gammaResolventMangoldtWeight n)) ≤
      (∑' n : ℕ, Analysis.gammaResolventMangoldtWeight n) -
        4 * ∑ n ∈ s, Analysis.gammaResolventMangoldtWeight n :=
  gamma_three_euler_prefix_le s (fun n ↦ (a n).re) (fun n ↦ (b n).re) (fun n ↦ (c n).re)
    (fun n ↦ (Complex.abs_re_le_norm (a n)).trans (a.norm_le_one n))
    (fun n ↦ (Complex.abs_re_le_norm (b n)).trans (b.norm_le_one n))
    (fun n ↦ (Complex.abs_re_le_norm (c n)).trans (c.norm_le_one n)) ht hp

/-- At three odd pair levels, the simultaneous Jacobi sign bound discharges
the Euler tail condition automatically. A prefix real-part sum of three gives
the fourfold prefix saving for the actual Gamma weight. This is the pair-level
Euler estimate used before constructing the MR no-witness prefix. -/
theorem gamma_pair_character_prefix_le (p q r : ℕ) [NeZero p] [NeZero q] [NeZero r]
    (hpq : Odd (p * q)) (hpr : Odd (p * r)) (hqr : Odd (q * r)) (s : Finset ℕ)
    (hp :
      ∀ n ∈ s,
        (NumberTheory.complexJacobiNumeratorCharacter (p * q) hpq n).re +
            (NumberTheory.complexJacobiNumeratorCharacter (p * r) hpr n).re +
            (NumberTheory.complexJacobiNumeratorCharacter (q * r) hqr n).re =
          3) :
    (∑' n : ℕ,
        ((-(NumberTheory.complexJacobiNumeratorCharacter (p * q) hpq n).re *
              Analysis.gammaResolventMangoldtWeight n +
            -(NumberTheory.complexJacobiNumeratorCharacter (p * r) hpr n).re *
              Analysis.gammaResolventMangoldtWeight n) +
          -(NumberTheory.complexJacobiNumeratorCharacter (q * r) hqr n).re *
            Analysis.gammaResolventMangoldtWeight n)) ≤
      (∑' n : ℕ, Analysis.gammaResolventMangoldtWeight n) -
        4 * ∑ n ∈ s, Analysis.gammaResolventMangoldtWeight n := by
  apply gamma_three_character_prefix_le _ _ _ s _ hp
  intro n _
  simpa only [Int.cast_natCast] using pair_character_sum_ge_neg_one (n : ℤ) p q r hpq hpr hqr

/-- If every prime through a cutoff has character value one, the actual
Gamma Euler prefix on a finite support below that cutoff equals its unsigned
mass. The weighted Mangoldt identity ignores zero Mangoldt terms. This supplies
the finite prefix contribution without assumptions on irrelevant integer values. -/
theorem gamma_euler_prefix_eq_of_prime_one {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → χ p = 1) (s : Finset ℕ) (hs : ∀ n ∈ s, (n : ℝ) ≤ x) :
    (∑ n ∈ s, (χ n).re * Analysis.gammaResolventMangoldtWeight n) =
      ∑ n ∈ s, Analysis.gammaResolventMangoldtWeight n := by
  simpa only [Analysis.gammaResolventMangoldtWeight, mul_assoc] using
    AnalyticNumberTheory.Arithmetic.weighted_sum_re_eq_of_full_prime_trivial χ ht s hs
      (fun n ↦ Analysis.gammaResolventEulerWeight (n : ℝ))

/-- For three characters at independent levels, triviality at every prime
through a cutoff determines each finite Gamma Euler prefix. If their real-part
sum is at least minus one off the prefix, the combined infinite contribution
is at most total mass minus four prefix masses. Combine the three weighted
Mangoldt identities with convergence and the finite-sum prefix bound. -/
theorem gamma_three_prime_one_prefix_le {p q r : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {x : ℝ} (s : Finset ℕ)
    (hs : ∀ n ∈ s, (n : ℝ) ≤ x) (ht : ∀ n ∉ s, -1 ≤ (a n).re + (b n).re + (c n).re)
    (ha : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ x → a l = 1) (hb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ x → b l = 1)
    (hc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ x → c l = 1) :
    (∑' n : ℕ,
        ((-(a n).re * Analysis.gammaResolventMangoldtWeight n +
            -(b n).re * Analysis.gammaResolventMangoldtWeight n) +
          -(c n).re * Analysis.gammaResolventMangoldtWeight n)) ≤
      (∑' n : ℕ, Analysis.gammaResolventMangoldtWeight n) -
        4 * ∑ n ∈ s, Analysis.gammaResolventMangoldtWeight n := by
  apply
    coupled_euler_prefix_sum_bound s _ _ Analysis.summable_gammaResolventMangoldtWeight
      (((Analysis.summable_gamma_signed_euler (fun n ↦ (a n).re)
                (fun n ↦ (Complex.abs_re_le_norm (a n)).trans (a.norm_le_one n))).add
            (Analysis.summable_gamma_signed_euler (fun n ↦ (b n).re)
              (fun n ↦ (Complex.abs_re_le_norm (b n)).trans (b.norm_le_one n)))).add
        (Analysis.summable_gamma_signed_euler (fun n ↦ (c n).re)
          (fun n ↦ (Complex.abs_re_le_norm (c n)).trans (c.norm_le_one n))))
  · intro n hn
    have h := mul_le_mul_of_nonneg_right (ht n hn) (Analysis.gammaResolventMangoldtWeight_nonneg n)
    linarith only [h]
  · have hA := gamma_euler_prefix_eq_of_prime_one a ha s hs
    have hB := gamma_euler_prefix_eq_of_prime_one b hb s hs
    have hC := gamma_euler_prefix_eq_of_prime_one c hc s hs
    simp only [Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib]
    linarith only [hA, hB, hC]

end PseudoPrime.PrimeTestBounds.MillerRabin
