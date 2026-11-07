/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaThreeCells

/-! # Uniform-triple transfer for arbitrary Gamma cells -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A strict Gamma gap yields a prime rejecting a uniform Korselt triple at
the given cutoff. Extract the three prime factors and their local data once;
the result can then be applied to every finite or analytic Gamma cell. -/
theorem uniformKorselt_reject_gamma {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X x : ℝ} (hx : 2 ≤ x)
    (s : Finset ℕ) (hs : ∀ k ∈ s, (k : ℝ) ≤ X) (hX : 142 ≤ X)
    (hgap :
      (∑' k : ℕ, Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x) +
              2 * (11783423 / 25000000 : ℝ) * Real.log n -
            477 / 100 +
          ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
            4 * ∑ k ∈ s, Analysis.gammaResolventMangoldtWeight k) +
          ((7 / 3 : ℝ) * Real.log n + 12) / Real.sqrt x +
          (105 / 2 : ℝ) * x ^ (-9 / 16 : ℝ) +
          3 / (x * Real.sqrt x) <
        4 * ∑ k ∈ s, Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x) :
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  obtain ⟨p, q, r, hp, hq, hr, hpq, hqr, hnp⟩ := uniformKorselt_ordered_factors hu
  have hpD : p ∣ n := hnp ▸ dvd_mul_of_dvd_left (dvd_mul_right p q) r
  have hqD : q ∣ n := hnp ▸ dvd_mul_of_dvd_left (dvd_mul_left q p) r
  have hrD : r ∣ n := hnp ▸ dvd_mul_left r (p * q)
  have hpO := Odd.of_dvd_nat ho hpD
  have hqO := Odd.of_dvd_nat ho hqD
  have hrO := Odd.of_dvd_nat ho hrD
  have hp2 := ho.ne_two_of_dvd_nat hpD
  have hq2 := ho.ne_two_of_dvd_nat hqD
  have hr2 := ho.ne_two_of_dvd_nat hrD
  let : NeZero n := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hn)⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  let : NeZero r := ⟨hr.ne_zero⟩
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact r.Prime := ⟨hr⟩
  let : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
  let : Fact (2 < q) := ⟨lt_of_le_of_ne hq.two_le (Ne.symm hq2)⟩
  let : Fact (2 < r) := ⟨lt_of_le_of_ne hr.two_le (Ne.symm hr2)⟩
  have hpqD : p * q ∣ n := ⟨r, hnp⟩
  have hprD : p * r ∣ n := ⟨q, hnp.trans (by ac_rfl)⟩
  have hqrD : q * r ∣ n := ⟨p, hnp.trans (by ac_rfl)⟩
  exact
    exists_prime_reject_of_gamma_gap hu.1 hnp hGRH hn ho hpO hqO hrO hpD hqD hrD hpqD hprD hqrD
      (hu.2.2.1 p hp hpD) (hu.2.2.1 q hq hqD) (hu.2.2.1 r hr hrD) (hu.2.2.2 q p hq hp hqD hpD)
      (hu.2.2.2 r p hr hp hrD hpD) hx s hs hX hgap

end PseudoPrime.PrimeTestBounds.MillerRabin
