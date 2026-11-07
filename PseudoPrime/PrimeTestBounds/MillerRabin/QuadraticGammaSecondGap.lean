/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaSecondCellBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaSecondPrincipal
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030KorseltParameters

/-! # Complete principal input for the second Gamma cell -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The certified second-cell scalar inputs imply the actual Gamma gap once
the principal series is bounded by 17.544153. The logarithmic parameter may vary
through the entire cell up to its rational right endpoint. The remaining
principal bound is discharged separately by the finite sum and tail. -/
theorem gamma_second_gap_of_principal (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaSecondRight : ℝ))
    (hU :
      (∑' k : ℕ,
          Real.exp (-(k : ℝ) / (gammaMainCell1Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell1Scale : ℝ)) ≤
        17544153 / 1000000) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell1Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell1Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 479, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell1Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell1Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell1Scale : ℝ) * Real.sqrt (gammaMainCell1Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 479,
          Real.exp (-(k : ℝ) / (gammaMainCell1Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell1Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 479) (gammaMainCell1Scale : ℝ) L (gammaSecondRight : ℝ)
      (1763 / 100) (397 / 10000) (gammaMainCell1Lower : ℝ) (17544153 / 1000000) (49879 / 12500)
      (by norm_num only [gammaMainCell1Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell1Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaSecondRight, Rat.cast_div, Rat.cast_ofNat]) hL
      gamma_second_power_upper gammaMainCell1_actual_lower hU gamma_second_euler_lower
      (euler_mass_le_12372 hRH)
  norm_num only [gammaSecondRight, gammaMainCell1Scale, gammaMainCell1Lower, Rat.cast_div,
    Rat.cast_ofNat]

/-- Under RH, the second-cell Gamma gap holds up to the rational right endpoint.
The certified finite principal bound and its tail discharge the remaining
numerical hypothesis. This prepares the rejecting-prime extraction. -/
theorem gamma_second_gap (hRH : RiemannHypothesis) {L : ℝ} (hL : L ≤ (gammaSecondRight : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell1Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell1Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 479, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell1Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell1Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell1Scale : ℝ) * Real.sqrt (gammaMainCell1Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 479,
          Real.exp (-(k : ℝ) / (gammaMainCell1Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell1Scale : ℝ) := by
  apply gamma_second_gap_of_principal hRH hL
  simpa only [gammaUpperCell1Scale, gammaMainCell1Scale] using gamma_second_principal_upper

/-- A squarefree uniform Korselt triple in the second Gamma cell has a
prime Miller–Rabin rejecting base at most 0.3 times the squared logarithm.
The actual three-character Gamma gap supplies the rejecting prime at cutoff
479, which lies below the target throughout this interval. -/
theorem gamma_second_cell_reject {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hlo : (3995831160931 / 100000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaSecondRight : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (479 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 3995831160931 / 100000000000)]
  obtain ⟨l, hl, hbound, hreject⟩ :=
    exists_prime_reject_of_gamma_gap (X := (479 : ℝ)) (x := (gammaMainCell1Scale : ℝ)) hsq hnprod
      hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK hvq hvr
      (by norm_num only [gammaMainCell1Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 479)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gamma_second_gap hGRH.riemann hhi)
  exact ⟨l, hl, hbound.trans hcut, hreject⟩

/-- Under GRH, a uniform Korselt triple in the second Gamma cell has a prime
Miller–Rabin rejecting base below the 0.3 cutoff. Extract its three distinct
prime factors from the squarefree factor set and apply the second-cell theorem. -/
theorem uniform_second_cell_reject {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (3995831160931 / 100000000000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (gammaSecondRight : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
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
    gamma_second_cell_reject hu.1 hnprod hGRH hn ho hpO hqO hrO hpD hqD hrD hpqD hprD hqrD
      (hu.2.2.1 p hp hpD) (hu.2.2.1 q hq hqD) (hu.2.2.1 r hr hrD) (hu.2.2.2 q p hq hp hqD hpD)
      (hu.2.2.2 r p hr hp hrD hpD) hlo hhi

end PseudoPrime.PrimeTestBounds.MillerRabin
