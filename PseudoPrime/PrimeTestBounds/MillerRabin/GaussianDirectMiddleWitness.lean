/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK141ResidualEndpoints
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK156ResidualRange
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCriterionTo663
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltFactors

/-! # Direct middle witnesses for uniform Korselt triples -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Use the ordered odd prime factors of a uniform triple in a proof of a
rejecting prime. The local instances serve both middle kernels. -/
public theorem uniform_gaussian_witness_from_factors {n : ℕ} {X : ℝ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n)
    (h :
      ∀ {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] [NeZero n] [Fact p.Prime] [Fact q.Prime]
        [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)],
        n = p * q * r → Odd p → Odd q → Odd r → HasRejectingPrime n X) :
    HasRejectingPrime n X := by
  obtain ⟨p, q, r, hp, hq, hr, _, _, hprod⟩ := uniformKorselt_ordered_factors hu
  have hpO := Odd.of_dvd_nat ho (show p ∣ n from ⟨q * r, hprod.trans (Nat.mul_assoc _ _ _)⟩)
  have hqO := Odd.of_dvd_nat ho (show q ∣ n from ⟨p * r, hprod.trans (by ac_rfl)⟩)
  have hrO := Odd.of_dvd_nat ho (show r ∣ n from ⟨p * q, hprod.trans (by ac_rfl)⟩)
  let : NeZero n := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hn)⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  let : NeZero r := ⟨hr.ne_zero⟩
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact r.Prime := ⟨hr⟩
  let : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (hpO.ne_two_of_dvd_nat dvd_rfl).symm⟩
  let : Fact (2 < q) := ⟨lt_of_le_of_ne hq.two_le (hqO.ne_two_of_dvd_nat dvd_rfl).symm⟩
  let : Fact (2 < r) := ⟨lt_of_le_of_ne hr.two_le (hrO.ne_two_of_dvd_nat dvd_rfl).symm⟩
  exact h hprod hpO hqO hrO

/-- K141 supplies a rejecting prime within the Gaussian cutoff for odd uniform
Korselt triples with logarithm in the first middle interval. -/
public theorem uniform_gaussian_witness_k141 {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (42410 : ℝ) 400000) :
    HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
  have h : HasRejectingPrime n ((gaussianDirectScale * Real.log n) ^ 2) :=
    uniform_gaussian_witness_from_factors hn ho hu
      (fun hprod hp hq hr ↦ middle_k141_direct_witness hGRH hn ho hu hprod hp hq hr hL)
  exact h.mono (gaussian_direct_cutoff hL.1)

/-- The direct Gaussian cutoff contains a rejecting prime for every odd
uniform Korselt triple in the middle input range under GRH. -/
public theorem uniform_gaussian_witness_middle {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (42410 : ℝ) 7000000) :
    HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
  by_cases h : Real.log n ≤ 400000
  · exact uniform_gaussian_witness_k141 hn ho hu hGRH ⟨hL.1, h⟩
  · have hw : HasRejectingPrime n ((gaussianDirectScale * Real.log n) ^ 2) :=
      uniform_gaussian_witness_from_factors hn ho hu
        (fun hprod hp hq hr ↦
          middle_k156_direct_witness hGRH hn ho hu hprod hp hq hr ⟨le_of_not_ge h, hL.2⟩)
    exact hw.mono (gaussian_direct_cutoff hL.1)

end PseudoPrime.PrimeTestBounds.MillerRabin
