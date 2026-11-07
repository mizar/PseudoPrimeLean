/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianScalarWitness
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFirstGap

/-! # Uniform Korselt Gaussian scalar witness -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, the explicit Gaussian scalar comparison yields a rejecting
prime for any odd uniform Korselt triple. Extract the three prime factors and
their divisibility and valuation hypotheses, then apply the actual witness theorem. -/
theorem uniform_reject_of_gaussian_scalar {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x h : ℝ} (hx : 1 ≤ x) (hh : 0 < h) (hh1 : h ≤ 1 / 32) (hX : 50000 ≤ (21 / 10 : ℝ) * x)
    (hscore :
      (20115621 / 25000000 : ℝ) * Real.log n + 683 / 50 - 108 / 25 - 4 * (1129059 / 200000 : ℝ) +
          (1536 / 27 : ℝ) / x +
          (2129 / 2000 : ℝ) * (((7 / 3 : ℝ) * Real.log n + 12) / Real.sqrt x) +
          (1419 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) ≤
        4 *
            (Real.sqrt x * (81470555 / 100000000 : ℝ) -
              (7 / 50 : ℝ) / Real.sqrt x *
                ((32 / 63 : ℝ) * h * ((21 / 10 : ℝ) * x) +
                  (231 / 2500 : ℝ) * (Real.sqrt ((21 / 10 : ℝ) * x) + 1) / h +
                  1839 / 1000) -
              ((231 / 5000 : ℝ) * Real.sqrt ((21 / 10 : ℝ) * x) +
                  (1839 / 1000 : ℝ) * Real.log ((21 / 10 : ℝ) * x) +
                  2) /
                Real.sqrt x) -
          (Real.sqrt x * Real.exp (1 / 16 : ℝ) + 13)) :
    ∃ l : ℕ,
      l.Prime ∧ (l : ℝ) ≤ (21 / 10 : ℝ) * x ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ := Finset.card_eq_three.mp hu.2.1
  have hpMem : p ∈ n.primeFactors := hset ▸ Finset.mem_insert_self p _
  have hqMem : q ∈ n.primeFactors := hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self q _)
  have hrMem : r ∈ n.primeFactors :=
    hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self r))
  have hp := (Nat.mem_primeFactors.mp hpMem).1
  have hq := (Nat.mem_primeFactors.mp hqMem).1
  have hr := (Nat.mem_primeFactors.mp hrMem).1
  have hpD := (Nat.mem_primeFactors.mp hpMem).2.1
  have hqD := (Nat.mem_primeFactors.mp hqMem).2.1
  have hrD := (Nat.mem_primeFactors.mp hrMem).2.1
  have hprod := (Nat.prod_primeFactors_of_squarefree hu.1).symm
  rw [hset] at hprod
  have hnprod : n = p * q * r := by
    simpa only [Finset.prod_insert, Finset.prod_singleton, Finset.mem_insert, Finset.mem_singleton,
      hpq, hpr, hqr, or_self, not_false_eq_true, mul_assoc] using hprod
  have hpO := Odd.of_dvd_nat ho hpD
  have hqO := Odd.of_dvd_nat ho hqD
  have hrO := Odd.of_dvd_nat ho hrD
  have hp2 : p ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hpO)
  have hq2 : q ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hqO)
  have hr2 : r ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hrO)
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
  have hpqD : p * q ∣ n := ⟨r, hnprod⟩
  have hprD : p * r ∣ n := ⟨q, hnprod.trans (by ac_rfl)⟩
  have hqrD : q * r ∣ n := ⟨p, hnprod.trans (by ac_rfl)⟩
  exact
    exists_prime_reject_of_gaussian_scalar hu.1 hnprod hGRH hn ho hpO hqO hrO hpD hqD hrD hpqD hprD
      hqrD (hu.2.2.1 p hp hpD) (hu.2.2.1 q hq hqD) (hu.2.2.1 r hr hrD) (hu.2.2.2 q p hq hp hqD hpD)
      (hu.2.2.2 r p hr hp hrD hpD) hx hh hh1 hX hscore

end PseudoPrime.PrimeTestBounds.MillerRabin
