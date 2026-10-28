/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianLowProfiles
public import PseudoPrime.LLS.GammaPrefixFine
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMR1000WitnessBounds
public import PseudoPrime.Analysis.GaussianSingleFourNumerics
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianRelativeTripleBounds

/-! # Actual Gaussian witnesses with low profile floors -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Every profile cutoff exceeds the common floor needed to cover the 1000 prefix. -/
theorem gaussianLow_cutoff_floor (f : Analysis.GaussianLowProfile) (L : ℝ) :
    (6 / 5 : ℝ) * ((91 / 10) ^ 2) ^ 2 ≤ f.bound L := by
  have hr := f.radius_floor L
  have hs := (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ (91 / 10) ^ 2) (sq_nonneg (f.root L))).mpr hr
  exact mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 6 / 5)

/-- Above logarithmic scale 63, each cutoff exceeds 15 L squared/32.
The linear radius bound covers all local subgroup witness bounds. -/
theorem gaussianLow_bound_lower (f : Analysis.GaussianLowProfile) {L : ℝ} (hL : 63 ≤ L) :
    (15 / 32 : ℝ) * L ^ 2 < f.bound L := by
  have hr := f.radius_linear hL
  have hpos : (0 : ℝ) ≤ (5 / 8) * L := by linarith only [hL]
  have hs := (sq_lt_sq₀ hpos (hpos.trans hr.le)).mpr hr
  change _ < (6 / 5 : ℝ) * f.radius L ^ 2
  nlinarith only [hs]

/-- Each profile prefix is a lower bound for the actual finite resolvent sum.
The three old-prefix profiles use the existing certificate; the two fine profiles
use the refined seed logarithm certificate. -/
theorem gaussianLow_prefix (f : Analysis.GaussianLowProfile)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    f.prefixValue ≤ ∑ j ∈ Finset.Ioc 0 1000, Analysis.gaussianResolventMangoldtWeight j := by
  cases f
  · simpa only [Analysis.GaussianLowProfile.prefixValue, Nat.floor_ofNat] using
      LLS.gaussian_prefix1000_recovered hGRH.riemann (le_refl (1000 : ℝ))
  · simpa only [Analysis.GaussianLowProfile.prefixValue, Nat.floor_ofNat] using
      LLS.gaussian_prefix1000_recovered hGRH.riemann (le_refl (1000 : ℝ))
  · simpa only [Analysis.GaussianLowProfile.prefixValue, Nat.floor_ofNat] using
      LLS.gaussian_prefix1000_recovered hGRH.riemann (le_refl (1000 : ℝ))
  · simpa only [Analysis.GaussianLowProfile.prefixValue, Nat.floor_ofNat] using
      LLS.gaussian_prefix1000_fine hGRH.riemann (le_refl (1000 : ℝ))
  · simpa only [Analysis.GaussianLowProfile.prefixValue, Nat.floor_ofNat] using
      LLS.gaussian_prefix1000_fine hGRH.riemann (le_refl (1000 : ℝ))

/--
Inputs: an odd ambient modulus at least 20000, a pass-containing subgroup of index at least
one billion, GRH, and log n at least 63.
Claim: the recovered-prefix single-root cutoff contains an actual rejecting prime.
Proof: apply the actual relative-prefix comparison and the recovered-prefix
single-root large-index budget.
Role: supplies the large-index branch of the all-input recovered-prefix single-root witness theorem.
-/
theorem gaussianLow_witness_large (f : Analysis.GaussianLowProfile) {n : ℕ} [NeZero n]
    (hnOdd : Odd n) (hnlarge : 20000 ≤ n) (H : Subgroup (ZMod n)ˣ)
    (hi : Analysis.gaussianMR6FifthsIndex ≤ (H.index : ℝ))
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ f.bound (Real.log n) ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_contra hnone
  let L := Real.log n
  let r := f.radius L
  let s := f.root L
  let x := r ^ 2
  let h := Analysis.gaussianMRRefinedWidth / s
  let m : ℝ := H.index
  let t : ℝ := m - 1
  let I : ℝ :=
    ∫ u in (0 : ℝ)..(6 / 5 : ℝ),
      (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u
  let E : ℝ := Real.exp (1 / 16 : ℝ)
  let C : ℝ := LLS.PaperStatements.subgroupConductorLogSum H
  let A : ℝ := LLS.PaperStatements.gaussianPrefixError (f.prefixValue) n x
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 20000) hnlarge
  have hrootSq : s ^ 2 = r := by dsimp only [s, r, Analysis.GaussianLowProfile.radius]
  have hrbound : ((91 / 10 : ℝ) ^ 2) ≤ r := f.radius_floor (Real.log n)
  have hspos : 0 < s := by
    dsimp only [s, L]
    exact f.root_pos _
  have hs14 : (91 / 10 : ℝ) ≤ s := f.signs.1.trans (f.root_floor (Real.log n))
  have hh : h = Analysis.gaussianMRRefinedWidth / s := by rfl
  have hh1 : h ≤ 1 / 2 := by
    rw [hh, div_le_iff₀ hspos]
    norm_num only [Analysis.gaussianMRRefinedWidth]
    linarith only [hs14]
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < (91 / 10 : ℝ) ^ 2) hrbound
  have hsqrtx : Real.sqrt x = r := by
    dsimp only [x]
    exact Real.sqrt_sq hrpos.le
  have hx : 4 ≤ x := by
    dsimp only [x]
    nlinarith only [hrbound]
  have hcut : (6 / 5 : ℝ) * x = f.bound (Real.log n) := by
    dsimp only [Analysis.GaussianLowProfile.bound, Analysis.GaussianLowProfile.radius, r, L, x]
  have hX : ((1000 : ℕ) : ℝ) ≤ (6 / 5 : ℝ) * x := by
    rw [hcut]
    exact
      (by norm_num only : (1000 : ℝ) ≤ (6 / 5) * ((91 / 10) ^ 2) ^ 2).trans
        (gaussianLow_cutoff_floor f (Real.log n))
  have hpass :
    ∀ p : ℕ,
      p.Prime → (p : ℝ) ≤ (6 / 5 : ℝ) * x → PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
    intro p hp hpbound
    rw [hcut] at hpbound
    by_contra hfail
    exact hnone ⟨p, hp, hpbound, hfail⟩
  have hdiv : ∀ p : ℕ, p.Prime → p ∣ n → ⌊(6 / 5 : ℝ) * x⌋₊ < p := by
    intro p hp hpdvd
    apply lt_of_not_ge
    intro hfloor
    have hbound : (p : ℝ) ≤ (6 / 5 : ℝ) * x := (Nat.le_floor_iff' hp.ne_zero).mp hfloor
    exact PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn1 hnOdd hp hpdvd (hpass p hp hbound)
  have hsmall :
    ∀ p : ℕ,
      p.Prime →
        ¬p ∣ n → (p : ℝ) ≤ (6 / 5 : ℝ) * x → LLS.PaperStatements.residueInSubgroup n H p := by
    intro p hp hpdvd hpbound
    obtain ⟨u, huH, hu⟩ := hHpass (p : ZMod n) (hpass p hp hpbound)
    exact ⟨u, huH, hu⟩
  have hwidth : 0 < h := div_pos (by norm_num only [Analysis.gaussianMRRefinedWidth]) hspos
  have prefixActual :
    f.prefixValue ≤ ∑ j ∈ Finset.Ioc 0 1000, Analysis.gaussianResolventMangoldtWeight j :=
    gaussianLow_prefix f hGRH
  have hcmp :=
    LLS.PaperStatements.gaussian_relative_prefix_le prefixActual hnlarge H hGRH hwidth hh1 hx
      (by norm_num only : (0 : ℝ) ≤ 6 / 5) hX hdiv hsmall
  have hcastIndex : ((H.index - 1 : ℕ) : ℝ) = (H.index : ℝ) - 1 := by
    have hidxReal : (1 : ℝ) ≤ (H.index : ℝ) := by
      have hK : (1 : ℝ) ≤ Analysis.gaussianMR6FifthsIndex := by
        norm_num only [Analysis.gaussianMR6FifthsIndex]
      exact hK.trans hi
    have hidxNat : 1 ≤ H.index := by exact_mod_cast hidxReal
    rw [Nat.cast_sub hidxNat, Nat.cast_one]
  rw [hsqrtx, hcastIndex] at hcmp
  have hI : Analysis.gaussianMRRefinedMass ≤ I := by
    dsimp only [I, Analysis.gaussianMRRefinedMass]
    exact Analysis.gaussianMRRefined_mass.le
  have hE : E ≤ Analysis.gaussianMR6FifthsEndpoint := by
    dsimp only [E, Analysis.gaussianMR6FifthsEndpoint]
    exact Analysis.gaussian_endpoint_exp_le
  have hC : C / t ≤ L := by
    have ht : t = (H.index : ℝ) - 1 := by rfl
    have htpos : 0 < t := by
      dsimp only [t, m]
      have hiNat : (1000000000 : ℝ) ≤ (H.index : ℝ) := hi
      linarith only [hiNat]
    have hC' : C ≤ t * L := by
      dsimp only [C, t, m, L]
      exact LLS.PaperStatements.subgroupConductorLogSum_le H
    exact (div_le_iff₀ htpos).2 (by nlinarith only [hC'])
  have hroot :
    Analysis.gaussianMRRefinedD * r ≥
      Analysis.gaussianMRRefinedConductor * L + Analysis.gaussianMRRefinedBeta * s +
        (f.residual) := by
    dsimp only [r, s, L]
    exact f.budget (by linarith only [hL] : 0 ≤ Real.log n)
  have hcmp' :
    (m * (1 - h) * I - E) * r ≤
      Analysis.gaussianMRRefinedConductor * C +
        m * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * E) +
        13 +
        t * A := by
    simpa only [m, t, I, E, C, A, Analysis.gaussianMRRefinedConductor] using hcmp
  have hcoeff := Analysis.gaussianMRRefined_index_coeffs hi
  have hD :
    Analysis.gaussianMRRefinedD ≤
      (m * Analysis.gaussianMRRefinedMass - Analysis.gaussianMR6FifthsEndpoint) / t := by
    simpa only [t] using hcoeff.1
  have hbeta :
    (m / t) *
        (Analysis.gaussianMRRefinedMass * Analysis.gaussianMRRefinedWidth +
          1 / (10 * Analysis.gaussianMRRefinedWidth)) ≤
      Analysis.gaussianMRRefinedBeta := by
    simpa only [t, mul_comm] using hcoeff.2.2
  have hfinish :
    Analysis.gaussianMRRefinedD * r ≤
        Analysis.gaussianMRRefinedConductor * L + Analysis.gaussianMRRefinedBeta * s +
          (m / t) *
            (21 * Analysis.gaussianMR6FifthsEndpoint / (10 * Analysis.gaussianMRRefinedWidth * s) +
              1839 * Analysis.gaussianMR6FifthsEndpoint / (1000 * r)) +
          13 / t +
          A →
      False := by
    intro hbudget
    have ht : t = m - 1 := by rfl
    have hgamma := hcoeff.2.1
    have herr :=
      Analysis.gaussianLow_index_error hspos hrpos hi
        (f.large_cap (f.root_floor L) (f.budget (by linarith only [hL])) (le_refl (Real.log n)))
    change
      (m / (m - 1)) *
            (21 * Analysis.gaussianMR6FifthsEndpoint / (10 * Analysis.gaussianMRRefinedWidth * s) +
              1839 * Analysis.gaussianMR6FifthsEndpoint / (1000 * r)) +
          13 / (m - 1) +
          A <
        (f.residual) at herr
    rw [ht] at hbudget
    linarith only [hbudget, hroot, herr]
  exact
    Analysis.gaussianMR_compare_width (m := m) (t := t) (s := s) (r := r) (A := A) (L := L) (I := I)
      (E := E) (C := C) (h := h) (M := Analysis.gaussianMRRefinedMass) (Ecap :=
      Analysis.gaussianMR6FifthsEndpoint) (conductor := Analysis.gaussianMRRefinedConductor) (D :=
      Analysis.gaussianMRRefinedD) (beta := Analysis.gaussianMRRefinedBeta)
      (by norm_num only [Analysis.gaussianMRRefinedWidth])
      (by
        have hi' : (1000000000 : ℝ) ≤ m := by
          simpa only [m, Analysis.gaussianMR6FifthsIndex] using hi
        linarith only [hi'])
      rfl hspos rfl hh hh1 hI hE hC (by norm_num only [Analysis.gaussianMRRefinedConductor]) hD
      hbeta hcmp' hfinish

/-- Under GRH, an index-four pass-containing subgroup with conductor at most
2 log n has an actual rejecting prime below the recovered one-root cutoff. Scale the comparison
radius by 7559/10000 while retaining width k/s. Both the strict residual and the main-term
budgets use 204/5. -/
theorem gaussianLow_witness_four (f : Analysis.GaussianLowProfile) {n : ℕ} [NeZero n]
    (hnOdd : Odd n) (hnlarge : 20000 ≤ n) (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ f.bound (Real.log n) ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let L := Real.log n
  let r := f.radius L
  let s := f.root L
  let x := ((7559 / 10000 : ℝ) * r) ^ 2
  let h := (2 / 5 : ℝ) / s
  have hr100 : ((91 / 10 : ℝ) ^ 2) ≤ r := f.radius_floor L
  have hs10 : (91 / 10 : ℝ) ≤ s := f.signs.1.trans (f.root_floor L)
  have hrpos : 0 < r := by linarith only [hr100]
  have hspos : 0 < s := by linarith only [hs10]
  have hs2 : r = s ^ 2 := rfl
  have hscaled : 0 ≤ (7559 / 10000 : ℝ) * r := by linarith only [hr100]
  have hh : 0 < h := div_pos (by norm_num only) hspos
  have hh1 : h ≤ 1 / 2 := by
    apply (div_le_iff₀ hspos).mpr
    linarith only [hs10]
  have hx : 4 ≤ x := by
    dsimp only [x]; nlinarith only [hr100]
  have hX : (1000 : ℝ) ≤ (21 / 10 : ℝ) * x := by
    dsimp only [x]
    nlinarith only [hr100]
  have hcut : (21 / 10 : ℝ) * x ≤ f.bound (Real.log n) := by
    change (21 / 10 : ℝ) * (((7559 / 10000 : ℝ) * r) ^ 2) ≤ (6 / 5 : ℝ) * r ^ 2
    nlinarith only [sq_nonneg r]
  have prefixActual :
    f.prefixValue ≤ ∑ j ∈ Finset.Ioc 0 1000, Analysis.gaussianResolventMangoldtWeight j :=
    gaussianLow_prefix f hGRH
  apply
    gaussianRelative_witness hnOdd hnlarge H hHpass hGRH prefixActual hh hh1 hx
      (by norm_num only : (0 : ℝ) ≤ 21 / 10) hX hcut
  intro hcmp
  have hindex : (H.index : ℝ) = 4 := by exact_mod_cast hi
  rw [Real.sqrt_sq hscaled] at hcmp
  have hcmp' :
    (4 * (1 - h) *
            (∫ u in (0 : ℝ)..(21 / 10 : ℝ),
              (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
          Real.exp (1 / 16 : ℝ)) *
        ((7559 / 10000 : ℝ) * r) ≤
      Analysis.gaussianMRRefinedConductor * LLS.PaperStatements.subgroupConductorLogSum H +
        4 *
          (1 / (10 * h) +
            ((21 / (10 * h) + 1839 / 1000) / ((7559 / 10000 : ℝ) * r)) * Real.exp (1 / 16 : ℝ)) +
        13 +
        3 *
          LLS.PaperStatements.gaussianPrefixError f.prefixValue n
            (((7559 / 10000 : ℝ) * r) ^ 2) := by
    simpa only [hindex, hi, Nat.reduceSub, Nat.cast_ofNat] using hcmp
  have hscalar :=
    Analysis.gaussianRelativeFour_scalar hspos hs2 (by norm_num only : (0 : ℝ) < 7559 / 10000)
      (by norm_num only : (0 : ℝ) < 2 / 5) (show h = (2 / 5 : ℝ) / s from rfl) hh1
      LLS.PaperStatements.gaussianGamma_cutoff_gt_target.le Analysis.gaussian_endpoint_exp_le hC
      (by norm_num only [Analysis.gaussianMRRefinedConductor]) hcmp'
  have hG := f.budget (show 0 ≤ L by linarith only [hL])
  have herror := f.four_error (f.root_floor L) hG (le_refl (Real.log n))
  have hmargin := f.four_margin (f.root_floor L)
  norm_num only [Analysis.gaussianMRRefinedConductor, Analysis.gaussianMR6FifthsEndpoint,
    Analysis.gaussianMRRefinedWidth] at hscalar hG herror hmargin
  rw [hs2] at hscalar
  dsimp only [s, r, L, Analysis.GaussianLowProfile.radius] at hscalar hG herror hmargin
  nlinarith only [hscalar, hG, herror, hmargin]

/-- For an odd uniform three-prime Korselt product, GRH and log n>=63
yield an actual rejecting prime within the recovered-prefix single-root cutoff. Construct the
index-four subgroup and retain its conductor-sum saving. -/
theorem gaussianLow_witness_triple (f : Analysis.GaussianLowProfile) {n p q r : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime) (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r) (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) (hn : n = p * q * r) (hpdiv : p - 1 ∣ n - 1) (hqdiv : q - 1 ∣ n - 1)
    (hrdiv : r - 1 ∣ n - 1) (hpv : padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hprv : padicValNat 2 (p - 1) = padicValNat 2 (r - 1)) (hnlarge : 20000 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ f.bound (Real.log n) ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  have hnOdd : Odd n := hn ▸ (hpOdd.mul hqOdd).mul hrOdd
  have hn1 : 1 < n :=
    hn ▸
      hp.one_lt.trans_le
        ((Nat.le_mul_of_pos_right p hq.pos).trans (Nat.le_mul_of_pos_right (p * q) hr.pos))
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  obtain ⟨H, hi, hpass, hC⟩ :=
    three_prime_korselt_conductor_subgroup_data hp hq hr hpOdd hqOdd hrOdd hpq hpr hqr hn hpdiv
      hqdiv hrdiv hpv hprv
  exact gaussianLow_witness_four f hnOdd hnlarge H hi hpass hGRH hC.le hL

/-- For a squarefree uniform Korselt triple specified by its factor set,
extract the three primes and apply the scaled relative index-four comparison.
This restricted interface is internal to the all-input classification. -/
theorem gaussianLow_witness_card (f : Analysis.GaussianLowProfile) {n : ℕ} (hnOdd : Odd n)
    (hsf : Squarefree n) (hc : n.primeFactors.card = 3)
    (hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1)
    (hU :
      ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hnlarge : 20000 ≤ n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 63 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ f.bound (Real.log n) ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
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
    gaussianLow_witness_triple f hp hq hr (hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpn))
      (hq.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hqn))
      (hr.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hrn)) hpq hpr hqr hnprod (hK p hp hpn)
      (hK q hq hqn) (hK r hr hrn) (hU p q hp hq hpn hqn) (hU p r hp hr hpn hrn) hnlarge hGRH hL

/-- For log n>=63 and q squared<=10^9*n, the local subgroup cutoff fits
the recovered-prefix single-root bound. Combine log q<=2 log n/3, the common profile floor and
the quadratic lower bound; keep the ambient passing-residue containment upstream. -/
theorem gaussianLow_local (f : Analysis.GaussianLowProfile) {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
    (hsize : q ^ 2 ≤ 10 ^ 9 * n) (hL : 63 ≤ Real.log n) :
    max (3000 : ℝ) (Real.log q ^ 2) ≤ f.bound (Real.log n) := by
  have hlog := Analysis.mr_local_log_le_of_square_le hn hq hsize
  have hcap : Real.log q ≤ (2 / 3 : ℝ) * Real.log n := by
    linarith only [hlog, hL, Analysis.log_ten_lt_seven_thirds]
  have hpos : (0 : ℝ) ≤ (2 / 3) * Real.log n := by linarith only [hL]
  have hs := (sq_le_sq₀ (Real.log_natCast_nonneg q) hpos).mpr hcap
  have hwide := gaussianLow_bound_lower f hL
  have hcut := gaussianLow_cutoff_floor f (Real.log n)
  exact max_le (by linarith only [hcut]) (by nlinarith only [hs, hwide, sq_nonneg (Real.log n)])

/-- Under GRH, every odd composite with log n>=63 has an actual prime
rejecting strong MR within the recovered-prefix single-root bound. Combine the large-index,
local and uniform-triple branches without public factorization restrictions. -/
theorem exists_prime_gaussianLow (f : Analysis.GaussianLowProfile) {n : ℕ} (ho : Odd n)
    (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ f.bound (Real.log n) ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hnpos : 0 < n := ho.pos
  have hN := gaussian35000_size hnpos hL
  have hn1 : 1 < n := (by norm_num only : 1 < 10 ^ 27).trans_le hN
  have hnlarge : 20000 ≤ n := (by norm_num only : 20000 ≤ 10 ^ 27).trans hN
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  by_cases hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 9
  · have hJ : (10 ^ 9 : ℕ) ^ 3 ≤ n := by
      norm_num only [← pow_mul, Nat.reduceMul]
      exact hN
    rcases
      finite_index_local_subgroup_or_uniform_korselt_triple hn1 ho hc (PrimeTest.fermatSubgroup n)
        le_rfl (by norm_num only : 1 ≤ 10 ^ 9) hJ hi with
      hl | ht
    · obtain ⟨q, hq, hqn, hqsize, K, hK, hpass⟩ := hl
      have hqp : 0 < q := (by norm_num only : 0 < 2).trans_le hq
      let : NeZero q := ⟨hqp.ne'⟩
      obtain ⟨p, hp, hb, hr⟩ :=
        exists_prime_witness_le_local_subgroup_envelope hn1 ho hq hqn K hK hpass hGRH
      exact ⟨p, hp, hb.trans (gaussianLow_local f hnpos hqp hqsize hL), hr⟩
    · obtain ⟨hsf, hcard, hK, hUval⟩ := ht
      exact gaussianLow_witness_card f ho hsf hcard hK hUval hnlarge hGRH hL
  · have hiR : Analysis.gaussianMR6FifthsIndex ≤ ((PrimeTest.fermatSubgroup n).index : ℝ) := by
      norm_num only [Analysis.gaussianMR6FifthsIndex]
      exact_mod_cast (lt_of_not_ge hi).le
    have hpass :
      ∀ z : ZMod n,
        PrimeTest.StrongMillerRabinPass n z →
          ∃ u : (ZMod n)ˣ, u ∈ PrimeTest.fermatSubgroup n ∧ (u : ZMod n) = z := by
      intro z hz
      exact PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn1 ho hz
    exact gaussianLow_witness_large f ho hnlarge (PrimeTest.fermatSubgroup n) hiR hpass hGRH hL

/-- Under the all-input recovered-prefix single-root assumptions, the least rejecting prime
satisfies the same cutoff. Extract it from the actual rejecting-prime theorem;
no squarefreeness, index or prime-factor count condition remains. -/
theorem exists_least_gaussianLow (f : Analysis.GaussianLowProfile) {n : ℕ} (ho : Odd n)
    (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ f.bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨ho.pos.ne'⟩
  exact exists_least_prime_reject_of_exists_prime_reject (exists_prime_gaussianLow f ho hc hGRH hL)

/-- Under GRH and log n at least 63, one least rejecting prime lies under
all three family candidates. Minimality transfers each independent witness bound. -/
theorem exists_least_gaussianLowFamily {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianLowFamily (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hb, hr, hleast⟩ := exists_least_gaussianLow .low ho hc hGRH hL
  obtain ⟨q, hq, hqb, hqr⟩ := exists_prime_gaussianLow .middle ho hc hGRH hL
  obtain ⟨r, hrp, hrb, hrr⟩ := exists_prime_gaussianLow .upper ho hc hGRH hL
  have hpq : (p : ℝ) ≤ q := Nat.cast_le.mpr (hleast q hq hqr)
  have hpr : (p : ℝ) ≤ r := Nat.cast_le.mpr (hleast r hrp hrr)
  exact ⟨p, hp, le_min hb (le_min (hpq.trans hqb) (hpr.trans hrb)), hr, hleast⟩

/-- Under GRH and log n at least 63, one least rejecting prime lies under
all three family candidates. Minimality transfers each independent witness bound. -/
theorem exists_least_gaussianLowOldFamily {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianLowOldFamily (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hb, hr, hleast⟩ := exists_least_gaussianLow .low ho hc hGRH hL
  obtain ⟨q, hq, hqb, hqr⟩ := exists_prime_gaussianLow .middleOld ho hc hGRH hL
  obtain ⟨r, hrp, hrb, hrr⟩ := exists_prime_gaussianLow .upperOld ho hc hGRH hL
  have hpq : (p : ℝ) ≤ q := Nat.cast_le.mpr (hleast q hq hqr)
  have hpr : (p : ℝ) ≤ r := Nat.cast_le.mpr (hleast r hrp hrr)
  exact ⟨p, hp, le_min hb (le_min (hpq.trans hqb) (hpr.trans hrb)), hr, hleast⟩

/-- The certified family cutoff contains an actual rejecting prime for
every odd composite in its logarithmic domain. Extract the common least witness. -/
theorem exists_prime_gaussianLowFamily {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianLowFamily (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
  (exists_least_gaussianLowFamily ho hc hGRH hL).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

/-- The certified family cutoff contains an actual rejecting prime for
every odd composite in its logarithmic domain. Extract the common least witness. -/
theorem exists_prime_gaussianLowOldFamily {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianLowOldFamily (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
  (exists_least_gaussianLowOldFamily ho hc hGRH hL).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
