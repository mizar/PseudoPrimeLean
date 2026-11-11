/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformPrefixSharp
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformPrefixBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformNarrowBounds

/-! # Uniform Korselt witnesses with an arbitrary closed cutoff -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The explicit closed-tail budget combines the conductor term, Gamma and Euler bounds,
and an upper bound for the full principal sum. -/
noncomputable def quarterUniformClosedBudget (X U F H : ℝ) : ℝ :=
  (2 * U) *
          (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
            X ^ (-(27 / 25 : ℝ)) *
            ((21 / 8 : ℝ) + Real.log X) ^ 5) +
        (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 +
        H +
        (3 / 8 : ℝ) * U -
      (3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
    4 * quarterEulerClosedTailCap X +
    F

/-- A closed-tail numerical budget gives a uniform Korselt witness at the given cutoff. -/
theorem quarter_uniform_cell_any {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {X U S F H : ℝ} (hX : 625 ≤ X)
    (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X ≤ H) (t : Finset ℕ)
    (ht : ∀ k ∈ t, (k : ℝ) ≤ X) (hU : Real.log n ≤ U)
    (hS :
      S ≤
        ∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re)
    (hF : (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re ≤ F)
    (hcert :
      quarterUniformClosedBudget X U F H - 3 * quarterGammaFirstCorrection (Real.log X + 21 / 8) -
          4 * ∑ k ∈ t, refinedDualWeight X k ≤
        4 * S) :
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith only [hX])
  have hc :
    0 ≤
      (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) * X ^ (-(27 / 25 : ℝ)) *
        ((21 / 8 : ℝ) + Real.log X) ^ 5) := by
    have hz : 0 ≤ (21 / 8 : ℝ) + Real.log X := by linarith only [hlog]
    exact
      mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num only) (Real.exp_pos _).le)
          (Real.rpow_nonneg (by linarith only [hX]) _))
        (pow_nonneg hz 5)
  have hm := mul_le_mul_of_nonneg_right (show 2 * Real.log n ≤ 2 * U by linarith only [hU]) hc
  have hfirst :=
    quarter_uniform_witness_prefix_closed hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn
      hpK hqK hrK hvq hvr hX hH t ht
  have hw : ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
    apply hfirst
    dsimp only [quarterUniformClosedBudget] at hcert
    linarith only [hm, hU, hF, hS, hcert]
  exact hw

/-- A closed-tail numerical budget gives a uniform Korselt witness at the given cutoff. -/
theorem quarter_uniform_bounds_any {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X U S F H : ℝ} (hX : 625 ≤ X)
    (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X ≤ H) (hU : Real.log n ≤ U)
    (t : Finset ℕ) (ht : ∀ k ∈ t, (k : ℝ) ≤ X)
    (hS :
      S ≤
        ∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re)
    (hF : (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re ≤ F)
    (hcert :
      quarterUniformClosedBudget X U F H - 3 * quarterGammaFirstCorrection (Real.log X + 21 / 8) -
          4 * ∑ k ∈ t, refinedDualWeight X k ≤
        4 * S) :
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
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
    quarter_uniform_cell_any hu.1 hnprod hGRH hn ho hpO hqO hrO hpD hqD hrD hpqD hprD hqrD
      (hu.2.2.1 p hp hpD) (hu.2.2.1 q hq hqD) (hu.2.2.1 r hr hrD) (hu.2.2.2 q p hq hp hqD hpD)
      (hu.2.2.2 r p hr hp hrD hpD) hX hH t ht hU hS hF hcert

end PseudoPrime.PrimeTestBounds.MillerRabin
