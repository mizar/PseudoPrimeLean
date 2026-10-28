/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianStarClassification
public import PseudoPrime.Analysis.GaussianMR35000Numerics

/-! # Fixed prime strong-MR witness bound 35000 on 63<=log n<=240 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For an index-four subgroup with conductor sum at most twice log n and log n<=240,
the fixed-scale relative comparison is impossible. Normalize at radius sqrt(87500/3)
and use the certified four-index gap. This helper retains the internal subgroup data. -/
theorem gaussian35000_index_four {n : ℕ} [NeZero n] (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) (hL : Real.log n ≤ 240) :
    let r := Analysis.gaussian35000Radius
    let s := Analysis.gaussian35000Root
    let h := 1 / (3 * s)
    let x := r ^ 2
    ¬(((H.index : ℝ) * (1 - h) *
              (∫ u in (0 : ℝ)..(6 / 5 : ℝ),
                (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
            Real.exp (1 / 16 : ℝ)) *
          Real.sqrt x ≤
        (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
          (H.index : ℝ) *
            (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / Real.sqrt x) * Real.exp (1 / 16 : ℝ)) +
          13 +
          ((H.index - 1 : ℕ) : ℝ) * LLS.PaperStatements.gaussianPrefixError (47 / 10) n x) := by
  intro r s h x hcmp
  have hindex : (H.index : ℝ) = 4 := by exact_mod_cast hi
  let I : ℝ :=
    ∫ u in (0 : ℝ)..(6 / 5 : ℝ),
      (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u
  let E : ℝ := Real.exp (1 / 16 : ℝ)
  have hrpos : 0 < r := by
    have h := Analysis.gaussian35000_radius_lower
    linarith only [h]
  have hspos : 0 < s := by
    have h := Analysis.gaussian35000_root_bounds.1
    linarith only [h]
  have hrootSq : s ^ 2 = r := Analysis.gaussian35000_root_sq
  have hrbound : 170 ≤ r := by
    have h := Analysis.gaussian35000_radius_lower
    linarith only [h]
  have hsbound : 13 ≤ s := Analysis.gaussian35000_root_bounds.1
  have hsqrtx : Real.sqrt x = r := by
    dsimp only [x]
    exact Real.sqrt_sq hrpos.le
  rw [hsqrtx] at hcmp
  have hI : Analysis.gaussianMR6FifthsMass ≤ I := by
    dsimp only [I, Analysis.gaussianMR6FifthsMass]
    exact LLS.PaperStatements.gaussianGamma_cutoff_sixFifths_gt_target.le
  have hE : E ≤ Analysis.gaussianMR6FifthsEndpoint := by
    dsimp only [E, Analysis.gaussianMR6FifthsEndpoint]
    exact Analysis.gaussian_endpoint_exp_le
  have hh : h = 1 / (3 * s) := by rfl
  have hh1 : h ≤ 1 / 2 := by
    rw [hh]
    apply one_div_le_one_div_of_le (by norm_num only)
    nlinarith only [hsbound]
  have hcmp' :
    (4 * (1 - h) * I - E) * r ≤
      (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
        4 * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * Real.exp (1 / 16 : ℝ)) +
        13 +
        3 * LLS.PaperStatements.gaussianPrefixError (47 / 10) n (r ^ 2) := by
    dsimp only [x] at hcmp
    simpa only [hindex, hi, Nat.cast_ofNat, Nat.reduceSub] using hcmp
  have hCscaled : LLS.PaperStatements.subgroupConductorLogSum H / 3 ≤ (2 / 3 : ℝ) * Real.log n := by
    apply (div_le_iff₀ (by norm_num only : (0 : ℝ) < 3)).2
    nlinarith only [hC]
  exact
    Analysis.gaussianMR_relative_comparison_to_scalar (m := 4) (t := 3) (s := s) (r := r) (A :=
      LLS.PaperStatements.gaussianPrefixError (47 / 10) n (r ^ 2)) (L := (2 / 3 : ℝ) * Real.log n)
      (I := I) (E := E) (C := LLS.PaperStatements.subgroupConductorLogSum H) (h := h) (M :=
      Analysis.gaussianMR6FifthsMass) (Ecap := Analysis.gaussianMR6FifthsEndpoint) (conductor :=
      (161 / 400 : ℝ)) (D :=
      (4 * Analysis.gaussianMR6FifthsMass - Analysis.gaussianMR6FifthsEndpoint) / 3) (beta :=
      (4 / 3 : ℝ) * (Analysis.gaussianMR6FifthsMass / 3 + 3 / 10)) (by norm_num only : (4 : ℝ) ≤ 4)
      (by norm_num only : (3 : ℝ) = (4 : ℝ) - 1) hspos hrootSq.symm hh hh1 hI hE hCscaled
      (by norm_num only : (0 : ℝ) ≤ 161 / 400) le_rfl le_rfl hcmp'
      (fun hbudget ↦
        Analysis.gaussian35000_four_absurd hL (Analysis.gaussian35000_ambient hL) hbudget)

/-- An index-four subgroup containing every strong-MR pass yields a rejecting prime
at most 35000 under GRH and log n<=240. A hypothetical absence of witnesses excludes
small prime factors and supplies the prefix comparison; the fixed four-index gap contradicts it. -/
theorem gaussian35000_witness_four {n : ℕ} [NeZero n] (hnOdd : Odd n) (hnlarge : 20000 ≤ n)
    (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) (hL : Real.log n ≤ 240) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (35000 : ℝ) ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_contra hnone
  let r := Analysis.gaussian35000Radius
  let x := r ^ 2
  have hcut : (6 / 5 : ℝ) * x = (35000 : ℝ) := by
    dsimp only [x, r]
    rw [Analysis.gaussian35000_radius_sq]
    norm_num only
  have hX : 35000 ≤ (6 / 5 : ℝ) * x := by rw [hcut]
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
    have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 20000) hnlarge
    exact PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn1 hnOdd hp hpdvd (hpass p hp hbound)
  have hsmall :
    ∀ p : ℕ,
      p.Prime →
        ¬p ∣ n → (p : ℝ) ≤ (6 / 5 : ℝ) * x → LLS.PaperStatements.residueInSubgroup n H p := by
    intro p hp hpdvd hpbound
    obtain ⟨u, huH, hu⟩ := hHpass (p : ZMod n) (hpass p hp hpbound)
    exact ⟨u, huH, hu⟩
  have hrootSq : (Analysis.gaussian35000Root) ^ 2 = r := Analysis.gaussian35000_root_sq
  have hrbound : 170 ≤ r := by
    have h := Analysis.gaussian35000_radius_lower
    linarith only [h]
  have hspos : 0 < Analysis.gaussian35000Root := by
    have hs := Analysis.gaussian35000_root_bounds.1
    linarith only [hs]
  have hsbound : 13 ≤ Analysis.gaussian35000Root := Analysis.gaussian35000_root_bounds.1
  have hwidth : 0 < 1 / (3 * Analysis.gaussian35000Root) :=
    one_div_pos.mpr (mul_pos (by norm_num only) hspos)
  have hwidth1 : 1 / (3 * Analysis.gaussian35000Root) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num only)
    nlinarith only [hsbound]
  have hx : 4 ≤ x := by
    dsimp only [x]
    nlinarith only [hrbound]
  have hprefix :
    (47 / 10 : ℝ) ≤ ∑ n ∈ Finset.Ioc 0 (35000 : ℕ), Analysis.gaussianResolventMangoldtWeight n := by
    have hp := LLS.gaussian_prefix35000_lower hGRH.riemann (le_refl (35000 : ℝ))
    have hf : ⌊(35000 : ℝ)⌋₊ = (35000 : ℕ) := Nat.floor_natCast 35000
    rw [hf] at hp
    exact hp
  have hcmp :=
    LLS.PaperStatements.gaussian_relative_prefix_le_coarse hprefix hnlarge H hGRH hwidth hwidth1 hx
      (by norm_num only : (0 : ℝ) ≤ 6 / 5) hX hdiv hsmall
  exact gaussian35000_index_four H hi hC hL hcmp

/-- For subgroup index at least 10^9 and log n<=240, the fixed Gaussian scale yields
a rejecting prime at most 35000 under GRH. Use the 35000-prefix mass and normalize
the relative comparison before applying the positive large-index gap. -/
theorem gaussian35000_witness_large {n : ℕ} [NeZero n] (hnOdd : Odd n) (hnlarge : 20000 ≤ n)
    (H : Subgroup (ZMod n)ˣ) (hi : Analysis.gaussianMR6FifthsIndex ≤ (H.index : ℝ))
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 240) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (35000 : ℝ) ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_contra hnone
  let L := Real.log n
  let r := Analysis.gaussian35000Radius
  let s := Analysis.gaussian35000Root
  let x := r ^ 2
  let h := 1 / (3 * s)
  let m : ℝ := H.index
  let t : ℝ := m - 1
  let I : ℝ :=
    ∫ u in (0 : ℝ)..(6 / 5 : ℝ),
      (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u
  let E : ℝ := Real.exp (1 / 16 : ℝ)
  let C : ℝ := LLS.PaperStatements.subgroupConductorLogSum H
  let A : ℝ := LLS.PaperStatements.gaussianPrefixError (47 / 10) n x
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 20000) hnlarge
  have hrootSq : s ^ 2 = r := Analysis.gaussian35000_root_sq
  have hrbound : 170 ≤ r := by
    have h := Analysis.gaussian35000_radius_lower
    linarith only [h]
  have hspos : 0 < s := by
    have h := Analysis.gaussian35000_root_bounds.1
    linarith only [h]
  have hs13 : 13 ≤ s := Analysis.gaussian35000_root_bounds.1
  have hh : h = 1 / (3 * s) := by rfl
  have hh1 : h ≤ 1 / 2 := by
    rw [hh]
    apply one_div_le_one_div_of_le (by norm_num only)
    nlinarith only [hs13]
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 170) hrbound
  have hsqrtx : Real.sqrt x = r := by
    dsimp only [x]
    exact Real.sqrt_sq hrpos.le
  have hx : 4 ≤ x := by
    dsimp only [x]
    nlinarith only [hrbound]
  have hcut : (6 / 5 : ℝ) * x = (35000 : ℝ) := by
    dsimp only [x, r]
    rw [Analysis.gaussian35000_radius_sq]
    norm_num only
  have hX : 35000 ≤ (6 / 5 : ℝ) * x := by rw [hcut]
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
  have hwidth : 0 < h := one_div_pos.mpr (mul_pos (by norm_num only) hspos)
  have hprefix :
    (47 / 10 : ℝ) ≤ ∑ n ∈ Finset.Ioc 0 (35000 : ℕ), Analysis.gaussianResolventMangoldtWeight n := by
    have hp := LLS.gaussian_prefix35000_lower hGRH.riemann (le_refl (35000 : ℝ))
    have hf : ⌊(35000 : ℝ)⌋₊ = (35000 : ℕ) := Nat.floor_natCast 35000
    rw [hf] at hp
    exact hp
  have hcmp :=
    LLS.PaperStatements.gaussian_relative_prefix_le_coarse hprefix hnlarge H hGRH hwidth hh1 hx
      (by norm_num only : (0 : ℝ) ≤ 6 / 5) hX hdiv hsmall
  have hcastIndex : ((H.index - 1 : ℕ) : ℝ) = (H.index : ℝ) - 1 := by
    have hidxReal : (1 : ℝ) ≤ (H.index : ℝ) := by
      have hK : (1 : ℝ) ≤ Analysis.gaussianMR6FifthsIndex := by
        norm_num only [Analysis.gaussianMR6FifthsIndex]
      exact hK.trans hi
    have hidxNat : 1 ≤ H.index := by exact_mod_cast hidxReal
    rw [Nat.cast_sub hidxNat, Nat.cast_one]
  rw [hsqrtx, hcastIndex] at hcmp
  have hI : Analysis.gaussianMR6FifthsMass ≤ I := by
    dsimp only [I, Analysis.gaussianMR6FifthsMass]
    exact LLS.PaperStatements.gaussianGamma_cutoff_sixFifths_gt_target.le
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
  have hcmp' :
    (m * (1 - h) * I - E) * r ≤
      Analysis.gaussianMR6FifthsConductor * C +
        m * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * E) +
        13 +
        t * A := by
    simpa only [m, t, I, E, C, A, Analysis.gaussianMR6FifthsConductor] using hcmp
  have hcoeff := Analysis.gaussianMR6Fifths_index_coefficients hi
  have hD :
    Analysis.gaussianMR6FifthsD ≤
      (m * Analysis.gaussianMR6FifthsMass - Analysis.gaussianMR6FifthsEndpoint) / t := by
    simpa only [t] using hcoeff.1
  have hbeta :
    (m / t) * (Analysis.gaussianMR6FifthsMass / 3 + 3 / 10) ≤ Analysis.gaussianMR6FifthsBeta := by
    simpa only [t] using hcoeff.2.2
  have hfinish :
    Analysis.gaussianMR6FifthsD * r ≤
        Analysis.gaussianMR6FifthsConductor * L + Analysis.gaussianMR6FifthsBeta * s +
          (m / t) *
            (63 * Analysis.gaussianMR6FifthsEndpoint / (10 * s) +
              1839 * Analysis.gaussianMR6FifthsEndpoint / (1000 * r)) +
          13 / t +
          A →
      False := by
    intro hbudget
    exact Analysis.gaussian35000_large_absurd hL hi (Analysis.gaussian35000_ambient hL) hbudget
  exact
    Analysis.gaussianMR_relative_comparison_to_scalar (m := m) (t := t) (s := s) (r := r) (A := A)
      (L := L) (I := I) (E := E) (C := C) (h := h) (M := Analysis.gaussianMR6FifthsMass) (Ecap :=
      Analysis.gaussianMR6FifthsEndpoint) (conductor := Analysis.gaussianMR6FifthsConductor) (D :=
      Analysis.gaussianMR6FifthsD) (beta := Analysis.gaussianMR6FifthsBeta)
      (by
        have hi' : (1000000000 : ℝ) ≤ m := by
          simpa only [m, Analysis.gaussianMR6FifthsIndex] using hi
        linarith only [hi'])
      rfl hspos hrootSq.symm hh hh1 hI hE hC
      (by norm_num only [Analysis.gaussianMR6FifthsConductor]) hD hbeta hcmp' hfinish

/-- A uniform three-prime Korselt product with log n<=240 has a prime strong-MR witness
at most 35000 under GRH. Its conductor subgroup has index four and conductor sum 2 log n.
Apply the fixed index-four theorem without adding these data to the public API. -/
theorem gaussian35000_witness_triple {n p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hn : n = p * q * r) (hpdiv : p - 1 ∣ n - 1) (hqdiv : q - 1 ∣ n - 1) (hrdiv : r - 1 ∣ n - 1)
    (hpv : padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hprv : padicValNat 2 (p - 1) = padicValNat 2 (r - 1)) (hnlarge : 20000 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 240) :
    ∃ s : ℕ, s.Prime ∧ (s : ℝ) ≤ (35000 : ℝ) ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  have hnOdd : Odd n := hn ▸ (hpOdd.mul hqOdd).mul hrOdd
  have hn1 : 1 < n :=
    hn ▸
      hp.one_lt.trans_le
        ((Nat.le_mul_of_pos_right p hq.pos).trans (Nat.le_mul_of_pos_right (p * q) hr.pos))
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  obtain ⟨H, hi, hpass, hC⟩ :=
    three_prime_korselt_conductor_subgroup_data hp hq hr hpOdd hqOdd hrOdd hpq hpr hqr hn hpdiv
      hqdiv hrdiv hpv hprv
  exact gaussian35000_witness_four hnOdd hnlarge H hi hpass hGRH hC.le hL

/-- For a squarefree uniform Korselt number with three prime factors, the fixed
35000 witness bound holds under GRH and log n<=240. Extract the three primes from
the factor set and use the index-four subgroup construction. -/
theorem gaussian35000_witness_card_three {n : ℕ} (hnOdd : Odd n) (hsf : Squarefree n)
    (hc : n.primeFactors.card = 3) (hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1)
    (hU :
      ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hnlarge : 20000 ≤ n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ 240) :
    ∃ s : ℕ, s.Prime ∧ (s : ℝ) ≤ (35000 : ℝ) ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
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
    gaussian35000_witness_triple hp hq hr (hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpn))
      (hq.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hqn))
      (hr.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hrn)) hpq hpr hqr hnprod (hK p hp hpn)
      (hK q hq hqn) (hK r hr hrn) (hU p q hp hq hpn hqn) (hU p r hp hr hpn hrn) hnlarge hGRH hL

/-- If n>0 and log n>=63, then 10^27<=n. Compare logarithms using log 10<7/3.
This supplies both the finite-index classification size and n>=20000
without invoking the log240 classification wrapper. -/
theorem gaussian35000_size {n : ℕ} (hn : 0 < n) (hL : 63 ≤ Real.log n) : 10 ^ 27 ≤ n := by
  by_contra h
  have hR : (n : ℝ) ≤ (10 : ℝ) ^ 27 := by exact_mod_cast (lt_of_not_ge h).le
  have hl := Real.log_le_log (Nat.cast_pos.mpr hn) hR
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith only [hl, Analysis.log_ten_lt_seven_thirds, hL]

/-- If q squared is at most 10^9 n and log n<=240, the local witness envelope is
at most 35000. Its logarithm is at most 261/2, whose square is below 35000.
The ambient-rejection transfer remains the responsibility of the local subgroup theorem. -/
theorem gaussian35000_local {n q : ℕ} (hn : 0 < n) (hq : 0 < q) (hsize : q ^ 2 ≤ 10 ^ 9 * n)
    (hU : Real.log n ≤ 240) : max (3000 : ℝ) (Real.log q ^ 2) ≤ 35000 := by
  have hlog := Analysis.mr_local_log_le_of_square_le hn hq hsize
  have hcap : Real.log q ≤ 261 / 2 := by linarith only [hlog, hU, Analysis.log_ten_lt_seven_thirds]
  have hsq :=
    (sq_le_sq₀ (Real.log_natCast_nonneg q) (by norm_num only : (0 : ℝ) ≤ 261 / 2)).mpr hcap
  exact max_le (by norm_num only) (by nlinarith only [hsq])

/-- Under GRH, every odd composite with 63<=log n<=240 has a prime rejecting
strong MR at most 35000. Combine the coefficient-free local classification,
the uniform Korselt triple, and the large Fermat-index fixed-scale comparison. -/
theorem exists_prime_witness_gaussian35000 {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n)
    (hU : Real.log n ≤ 240) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 35000 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
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
      exact ⟨p, hp, hb.trans (gaussian35000_local hnpos hqp hqsize hU), hr⟩
    · obtain ⟨hsf, hcard, hK, hUval⟩ := ht
      exact gaussian35000_witness_card_three ho hsf hcard hK hUval hnlarge hGRH hU
  · have hiR : Analysis.gaussianMR6FifthsIndex ≤ ((PrimeTest.fermatSubgroup n).index : ℝ) := by
      norm_num only [Analysis.gaussianMR6FifthsIndex]
      exact_mod_cast (lt_of_not_ge hi).le
    have hpass :
      ∀ z : ZMod n,
        PrimeTest.StrongMillerRabinPass n z →
          ∃ u : (ZMod n)ˣ, u ∈ PrimeTest.fermatSubgroup n ∧ (u : ZMod n) = z := by
      intro z hz
      exact PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn1 ho hz
    exact gaussian35000_witness_large ho hnlarge (PrimeTest.fermatSubgroup n) hiR hpass hGRH hU

/-- Under the same GRH and logarithmic assumptions, the least prime rejecting
strong MR is at most 35000. Minimize the actual prime-witness theorem with Nat.find.
No squarefree, factor-count, or Fermat-index restriction appears in the conclusion. -/
theorem exists_least_witness_gaussian35000 {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n)
    (hU : Real.log n ≤ 240) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ 35000 ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  classical
  obtain ⟨p, hp, hb, hr⟩ := exists_prime_witness_gaussian35000 ho hc hGRH hL hU
  have hex : ∃ q : ℕ, q.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := ⟨p, hp, hr⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hr⟩)).trans hb, fun q hq hrq ↦
      Nat.find_min' hex ⟨hq, hrq⟩⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
