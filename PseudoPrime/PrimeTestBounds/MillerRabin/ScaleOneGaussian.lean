/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianRadiusBudget
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianAdaptiveCoefficients

/-! # Relative Gaussian witness at logarithmic scale 25000 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The adaptive Gaussian slope lies between explicit rational bounds from scale 25000.
Bound the reciprocal square-root and reciprocal scale terms at the entrance. -/
theorem scaleOne_gaussian_slope (L : ℝ) (hL : 25000 ≤ L) :
    (36 / 100 : ℝ) ≤ adaptiveGaussianA L ∧ adaptiveGaussianA L ≤ 3715 / 10000 := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have h1 : 0 ≤ (61 / 100 : ℝ) * (28794111 / 12500000) / Real.sqrt L :=
    div_nonneg (by norm_num only) (Real.sqrt_nonneg _)
  have h2 : 0 ≤ (39 : ℝ) / L := div_nonneg (by norm_num only) hL0
  have hs : (158 : ℝ) ≤ Real.sqrt L := by
    apply (Real.le_sqrt (by norm_num only) hL0).2
    nlinarith only [hL]
  have hd :
    (61 / 100 : ℝ) * (28794111 / 12500000) / Real.sqrt L ≤
      (61 / 100 : ℝ) * (28794111 / 12500000) / 158 := by
    apply div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hs
  have he : (39 : ℝ) / L ≤ 39 / 25000 := by
    apply div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hL
  dsimp only [adaptiveGaussianA]
  constructor <;> apply (le_div_iff₀ (by norm_num only)).2 <;> linarith only [h1, h2, hd, he]

/-- Under GRH, an index-four subgroup gives a rejecting prime below the adaptive
Gaussian cutoff from scale 25000. Establish the root and prefix budgets and apply
the radius-based witness; no larger profile entrance is assumed. -/
theorem scaleOne_gaussian_four {n : ℕ} [NeZero n] (hnOdd : Odd n) (hnlarge : 20000 ≤ n)
    (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n)
    (hL : 25000 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ ((21 / 10 : ℝ) * adaptiveGaussianA (Real.log n) ^ 2 * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let L := Real.log n
  let a := adaptiveGaussianA L
  let r := a * L
  have hLpos : 0 < L := by linarith only [hL]
  have ha := scaleOne_gaussian_slope L hL
  change (36 / 100 : ℝ) ≤ a ∧ a ≤ 3715 / 10000 at ha
  have hr : (36 / 100 : ℝ) * L ≤ r := mul_le_mul_of_nonneg_right ha.1 hLpos.le
  have hr500 : (500 : ℝ) ≤ r := by nlinarith only [hr, hL]
  have hs : Real.sqrt r ≤ (61 / 100 : ℝ) * Real.sqrt L := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact mul_nonneg (by norm_num only) (Real.sqrt_nonneg L)
    · have h := mul_le_mul_of_nonneg_right ha.2 hLpos.le
      nlinarith only [h, Real.sq_sqrt hLpos.le]
  have haerr :=
    gaussianRadius_error (n := n) (L := L) (r := r) (by linarith only [hL]) (le_refl _) hr
  have hform :
    (10971611 / 5000000 : ℝ) * a =
      2 * (20115621 / 50000000) + (61 / 100) * (28794111 / 12500000) / Real.sqrt L + 39 / L := by
    dsimp only [a, adaptiveGaussianA]
    ring
  have hgap :
    2 * (20115621 / 50000000 : ℝ) * L + (28794111 / 12500000 : ℝ) * Real.sqrt r + 38 <
      (10971611 / 5000000 : ℝ) * r := by
    have hh : Real.sqrt L ≠ 0 := (Real.sqrt_pos.mpr hLpos).ne'
    have hsquare := Real.sq_sqrt hLpos.le
    have hdiv : L / Real.sqrt L = Real.sqrt L := by
      apply (div_eq_iff hh).2
      nlinarith only [hsquare]
    have he :
      ((61 / 100 : ℝ) * (28794111 / 12500000) / Real.sqrt L) * L =
        (61 / 100 : ℝ) * (28794111 / 12500000) * Real.sqrt L := by
      rw [div_mul_eq_mul_div, mul_div_assoc, hdiv]
    have h39 : (39 : ℝ) / L * L = 39 := div_mul_cancel₀ _ hLpos.ne'
    have hmul := congrArg (fun z : ℝ ↦ z * L) hform
    dsimp only [r]
    nlinarith only [hmul, he, h39, hs]
  obtain ⟨p, hp, hbound, hfail⟩ :=
    gaussianRadius_witness_four hnOdd hnlarge H hi hHpass hGRH hC hr500 haerr hgap
  refine ⟨p, hp, ?_, hfail⟩
  dsimp only [r, a, L] at hbound
  nlinarith only [hbound]

/-- For a uniform Korselt product of three odd primes, the scale-25000 Gaussian
budget supplies an actual rejecting prime under GRH. -/
theorem scaleOne_gaussian_triple {n p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hn : n = p * q * r) (hpdiv : p - 1 ∣ n - 1) (hqdiv : q - 1 ∣ n - 1) (hrdiv : r - 1 ∣ n - 1)
    (hpv : padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hprv : padicValNat 2 (p - 1) = padicValNat 2 (r - 1)) (hnlarge : 20000 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (25000 : ℝ) ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ ((21 / 10 : ℝ) * adaptiveGaussianA (Real.log n) ^ 2) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  have hnOdd : Odd n := hn ▸ (hpOdd.mul hqOdd).mul hrOdd
  have hn1 : 1 < n :=
    hn ▸
      hp.one_lt.trans_le
        ((Nat.le_mul_of_pos_right p hq.pos).trans (Nat.le_mul_of_pos_right (p * q) hr.pos))
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  obtain ⟨H, hi, hpass, hC⟩ :=
    three_prime_korselt_conductor_subgroup_data hp hq hr hpOdd hqOdd hrOdd hpq hpr hqr hn hpdiv
      hqdiv hrdiv hpv hprv
  exact scaleOne_gaussian_four hnOdd hnlarge H hi hpass hGRH hC.le hL

/-- Under GRH, the squarefree uniform three-factor case gives a rejecting prime
within the profile cutoff. -/
theorem scaleOne_gaussian_card {n : ℕ} (hnOdd : Odd n) (hsf : Squarefree n)
    (hc : n.primeFactors.card = 3) (hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1)
    (hU :
      ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hnlarge : 20000 ≤ n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (25000 : ℝ) ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ ((21 / 10 : ℝ) * adaptiveGaussianA (Real.log n) ^ 2) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ := Finset.card_eq_three.mp hc
  have hpMem : p ∈ n.primeFactors := hset ▸ Finset.mem_insert_self p _
  have hqMem : q ∈ n.primeFactors := hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self q _)
  have hrMem : r ∈ n.primeFactors :=
    hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self r))
  have hp := (Nat.mem_primeFactors.mp hpMem).1
  have hq := (Nat.mem_primeFactors.mp hqMem).1
  have hr := (Nat.mem_primeFactors.mp hrMem).1
  have hpn := (Nat.mem_primeFactors.mp hpMem).2.1
  have hqn := (Nat.mem_primeFactors.mp hqMem).2.1
  have hrn := (Nat.mem_primeFactors.mp hrMem).2.1
  have hprod := (Nat.prod_primeFactors_of_squarefree hsf).symm
  rw [hset] at hprod
  have hnprod : n = p * q * r := by
    simpa only [Finset.prod_insert, Finset.prod_singleton, Finset.mem_insert, Finset.mem_singleton,
      hpq, hpr, hqr, or_self, not_false_eq_true, mul_assoc] using hprod
  exact
    scaleOne_gaussian_triple hp hq hr (hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpn))
      (hq.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hqn))
      (hr.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hrn)) hpq hpr hqr hnprod (hK p hp hpn)
      (hK q hq hqn) (hK r hr hrn) (hU p q hp hq hpn hqn) (hU p r hp hr hpn hrn) hnlarge hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
