/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianRelativeTripleBounds
public import PseudoPrime.Analysis.GaussianRelativeProfiles

/-! # Generic relative Gaussian witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an index-four pass-containing subgroup with conductor at most
2 log n yields an actual rejecting prime below C(log n) squared when log n>=T.
Apply the 21/10 relative comparison, the actual 50000 prefix and its scalar contradiction. -/
theorem gaussianProfile_witness_four (f : Analysis.GaussianRelativeProfile) {n : ℕ} [NeZero n]
    (hnOdd : Odd n) (hnlarge : 20000 ≤ n) (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) (hL : f.T ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ f.C * Real.log n ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let L := Real.log n
  let x := (f.C / (21 / 10) * L ^ 2)
  let r := Real.sqrt x
  let s := Real.sqrt r
  let h := (2 / 5 : ℝ) / s
  have hroots := Analysis.gaussianRelativeProfile_roots f hL
  change f.a * L ≤ r ∧ 500 ≤ r ∧ 10 ≤ s ∧ s ≤ (61 / 100 : ℝ) * L / f.v at hroots
  have hrpos : 0 < r := by linarith only [hroots.2.1]
  have hspos : 0 < s := by linarith only [hroots.2.2.1]
  have hx0 : 0 ≤ x := mul_nonneg ((sq_nonneg f.a).trans f.square) (sq_nonneg L)
  have hr2 : r ^ 2 = x := Real.sq_sqrt hx0
  have hs2 : r = s ^ 2 := (Real.sq_sqrt hrpos.le).symm
  have hh : 0 < h := div_pos (by norm_num only) hspos
  have hh1 : h ≤ 1 / 2 := by
    apply (div_le_iff₀ hspos).mpr
    linarith only [hroots.2.2.1]
  have hr500 : (500 : ℝ) ≤ r := hroots.2.1
  have hx : 4 ≤ x := by nlinarith only [hr2, hr500]
  have hX : (50000 : ℝ) ≤ (21 / 10 : ℝ) * x := by nlinarith only [hr2, hr500]
  have hcut : (21 / 10 : ℝ) * x ≤ f.C * Real.log n ^ 2 := by
    dsimp only [x, L]
    exact le_of_eq (by ring)
  have hprefix :
    (489311 / 100000 : ℝ) ≤
      ∑ j ∈ Finset.Ioc 0 50000, Analysis.gaussianResolventMangoldtWeight j := by
    simpa only [Nat.floor_ofNat] using
      LLS.gaussian_prefix50000_seeded hGRH.riemann (le_refl (50000 : ℝ))
  apply
    gaussianRelative_witness hnOdd hnlarge H hHpass hGRH hprefix hh hh1 hx
      (by norm_num only : (0 : ℝ) ≤ 21 / 10) hX hcut
  intro hcmp
  have hindex : (H.index : ℝ) = 4 := by exact_mod_cast hi
  rw [← hr2, Real.sqrt_sq hrpos.le] at hcmp
  have hcmp' :
    (4 * (1 - h) *
            (∫ u in (0 : ℝ)..(21 / 10 : ℝ),
              (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
          Real.exp (1 / 16 : ℝ)) *
        (1 * r) ≤
      Analysis.gaussianMRRefinedConductor * LLS.PaperStatements.subgroupConductorLogSum H +
        4 * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / (1 * r)) * Real.exp (1 / 16 : ℝ)) +
        13 +
        3 * LLS.PaperStatements.gaussianPrefixError (489311 / 100000) n (r ^ 2) := by
    simpa only [hindex, hi, Nat.reduceSub, Nat.cast_ofNat, one_mul] using hcmp
  have hscalar :=
    Analysis.gaussianRelativeFour_scalar hspos hs2 (by norm_num only : (0 : ℝ) < 1)
      (by norm_num only : (0 : ℝ) < 2 / 5) (show h = (2 / 5 : ℝ) / s from rfl) hh1
      LLS.PaperStatements.gaussianGamma_cutoff_gt_target.le Analysis.gaussian_endpoint_exp_le hC
      (by norm_num only [Analysis.gaussianMRRefinedConductor]) hcmp'
  have hA := Analysis.gaussianRelativeProfile_error f hL (le_refl (Real.log n))
  apply Analysis.gaussianRelativeProfile_false f hL hroots.1 hroots.2.1 hroots.2.2.1 hroots.2.2.2 hA
  norm_num only [one_mul, Analysis.gaussianMRRefinedConductor] at hscalar ⊢
  exact hscalar

/-- For an odd uniform three-prime Korselt product, GRH and log n>=T
yield an actual rejecting prime within the coefficient-C cutoff. Construct the
index-four subgroup and retain its conductor-sum saving. -/
theorem gaussianProfile_witness_triple (f : Analysis.GaussianRelativeProfile) {n p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hn : n = p * q * r) (hpdiv : p - 1 ∣ n - 1)
    (hqdiv : q - 1 ∣ n - 1) (hrdiv : r - 1 ∣ n - 1)
    (hpv : padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hprv : padicValNat 2 (p - 1) = padicValNat 2 (r - 1)) (hnlarge : 20000 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : f.T ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ (f.C * Real.log n ^ 2) ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  have hnOdd : Odd n := hn ▸ (hpOdd.mul hqOdd).mul hrOdd
  have hn1 : 1 < n :=
    hn ▸
      hp.one_lt.trans_le
        ((Nat.le_mul_of_pos_right p hq.pos).trans (Nat.le_mul_of_pos_right (p * q) hr.pos))
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  obtain ⟨H, hi, hpass, hC⟩ :=
    three_prime_korselt_conductor_subgroup_data hp hq hr hpOdd hqOdd hrOdd hpq hpr hqr hn hpdiv
      hqdiv hrdiv hpv hprv
  exact gaussianProfile_witness_four f hnOdd hnlarge H hi hpass hGRH hC.le hL

/-- For a squarefree uniform Korselt triple specified by its factor set,
extract the three primes and apply the exact-conductor relative Gaussian comparison.
This restricted interface is internal to the all-input classification. -/
theorem gaussianProfile_witness_card (f : Analysis.GaussianRelativeProfile) {n : ℕ} (hnOdd : Odd n)
    (hsf : Squarefree n) (hc : n.primeFactors.card = 3)
    (hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1)
    (hU :
      ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hnlarge : 20000 ≤ n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : f.T ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ (f.C * Real.log n ^ 2) ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
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
    gaussianProfile_witness_triple f hp hq hr (hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpn))
      (hq.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hqn))
      (hr.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hrn)) hpq hpr hqr hnprod (hK p hp hpn)
      (hK q hq hqn) (hK r hr hrn) (hU p q hp hq hpn hqn) (hU p r hp hr hpn hrn) hnlarge hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
