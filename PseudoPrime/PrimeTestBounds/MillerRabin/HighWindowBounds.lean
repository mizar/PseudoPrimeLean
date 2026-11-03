/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighWindowProfiles
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularProfileBounds

/-! # Rejecting-prime bounds from high-window triangular certificates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd composite above one with logarithm at least 120000000000 has a rejecting
prime bounded by the certified coefficient 323 / 1000. Apply the triangular profile. -/
theorem exists_prime_highWindowP0323 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (120000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (323 / 1000 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
  exists_prime_triangularProfile highWindowP0323 hn ho hc hGRH hL

/-- The least rejecting prime satisfies the 323 / 1000 bound under the same assumptions.
Use the generic least-witness theorem for the certified profile. -/
theorem exists_least_highWindowP0323 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (120000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (323 / 1000 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q :=
  exists_least_triangularProfile highWindowP0323 hn ho hc hGRH hL

/-- Under GRH, an odd composite above one with logarithm at least 300000000000 has a rejecting
prime bounded by the certified coefficient 37 / 125. Apply the triangular profile. -/
theorem exists_prime_highWindowP0296 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (300000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (37 / 125 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
  exists_prime_triangularProfile highWindowP0296 hn ho hc hGRH hL

/-- The least rejecting prime satisfies the 37 / 125 bound under the same assumptions.
Use the generic least-witness theorem for the certified profile. -/
theorem exists_least_highWindowP0296 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (300000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (37 / 125 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q :=
  exists_least_triangularProfile highWindowP0296 hn ho hc hGRH hL

/-- Under GRH, an odd composite above one with logarithm at least 600000000000 has a rejecting
prime bounded by the certified coefficient 36 / 125. Apply the triangular profile. -/
theorem exists_prime_highWindowP0288 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (600000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (36 / 125 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
  exists_prime_triangularProfile highWindowP0288 hn ho hc hGRH hL

/-- The least rejecting prime satisfies the 36 / 125 bound under the same assumptions.
Use the generic least-witness theorem for the certified profile. -/
theorem exists_least_highWindowP0288 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (600000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (36 / 125 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q :=
  exists_least_triangularProfile highWindowP0288 hn ho hc hGRH hL

/-- Under GRH, an odd composite above one with logarithm at least 38 billion has a rejecting
prime at most 423/1000 of its squared logarithm. Apply the certified triangular profile. -/
theorem exists_prime_highWindowP0423 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (38000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (423 / 1000 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
  exists_prime_triangularProfile highWindowP0423 hn ho hc hGRH hL

/-- The least rejecting prime satisfies the 423/1000 bound under the same assumptions.
Use the generic least-witness theorem for the certified profile. -/
theorem exists_least_highWindowP0423 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (38000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (423 / 1000 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q :=
  exists_least_triangularProfile highWindowP0423 hn ho hc hGRH hL

/-- Under GRH, an odd composite above one with logarithm at least 45 billion has a rejecting
prime at most two fifths of its squared logarithm. Apply the certified triangular profile. -/
theorem exists_prime_highWindowP040 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (45000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (2 / 5 : ℝ) * Real.log n ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
  exists_prime_triangularProfile highWindowP040 hn ho hc hGRH hL

/-- The least rejecting prime satisfies the two-fifths bound under the same assumptions.
Use the generic least-witness theorem for the certified profile. -/
theorem exists_least_highWindowP040 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (45000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (2 / 5 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q :=
  exists_least_triangularProfile highWindowP040 hn ho hc hGRH hL

/-- Under GRH, an odd composite above one with logarithm at least 60 billion has a rejecting
prime at most 369/1000 of its squared logarithm. Apply the certified triangular profile. -/
theorem exists_prime_highWindowP0369 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (60000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (369 / 1000 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
  exists_prime_triangularProfile highWindowP0369 hn ho hc hGRH hL

/-- The least rejecting prime satisfies the 369/1000 bound under the same assumptions.
Use the generic least-witness theorem for the certified profile. -/
theorem exists_least_highWindowP0369 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (60000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (369 / 1000 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q :=
  exists_least_triangularProfile highWindowP0369 hn ho hc hGRH hL

/-- Under GRH, an odd composite above one with logarithm at least 80 billion has a rejecting
prime at most 173/500 of its squared logarithm. Apply the certified triangular profile. -/
theorem exists_prime_highWindowP0346 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (80000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (173 / 500 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
  exists_prime_triangularProfile highWindowP0346 hn ho hc hGRH hL

/-- The least rejecting prime satisfies the 173/500 bound under the same assumptions.
Use the generic least-witness theorem for the certified profile. -/
theorem exists_least_highWindowP0346 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (80000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (173 / 500 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q :=
  exists_least_triangularProfile highWindowP0346 hn ho hc hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
