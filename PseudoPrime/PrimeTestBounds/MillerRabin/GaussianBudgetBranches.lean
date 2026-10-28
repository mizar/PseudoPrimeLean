/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLowFloorBounds

/-! # Generic Gaussian witness branches -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Given an actual N-term Gaussian prefix, a root above 9.1, its quadratic
budget and a strict residual cap for every index at least one billion, obtain
an actual rejecting prime below six fifths of the fourth power of s0. The pass
assumption is imposed at this cutoff before the relative comparison is applied. -/
theorem gaussianBudget_large_witness (N : ℕ) (P D s0 : ℝ) (hs91 : (91 / 10 : ℝ) ≤ s0) {n : ℕ}
    [NeZero n]
    (hbudget :
      Analysis.gaussianMRRefinedConductor * Real.log n + Analysis.gaussianMRRefinedBeta * s0 + D ≤
        Analysis.gaussianMRRefinedD * s0 ^ 2)
    (hprefix : P ≤ ∑ j ∈ Finset.Ioc 0 N, Analysis.gaussianResolventMangoldtWeight j)
    (hN : (N : ℝ) ≤ (6 / 5 : ℝ) * (s0 ^ 2) ^ 2)
    (herror :
      ∀ m : ℝ,
        Analysis.gaussianMR6FifthsIndex ≤ m →
          (m / (m - 1)) *
                (21 * Analysis.gaussianMR6FifthsEndpoint /
                    (10 * Analysis.gaussianMRRefinedWidth * s0) +
                  1839 * Analysis.gaussianMR6FifthsEndpoint / (1000 * s0 ^ 2)) +
              13 / (m - 1) +
              LLS.PaperStatements.gaussianPrefixError P n ((s0 ^ 2) ^ 2) <
            D)
    (hnOdd : Odd n) (hnlarge : 20000 ≤ n) (H : Subgroup (ZMod n)ˣ)
    (hi : Analysis.gaussianMR6FifthsIndex ≤ (H.index : ℝ))
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (6 / 5 : ℝ) * (s0 ^ 2) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_contra hnone
  let L := Real.log n
  let r := s0 ^ 2
  let s := s0
  let x := r ^ 2
  let h := Analysis.gaussianMRRefinedWidth / s
  let m : ℝ := H.index
  let t : ℝ := m - 1
  let I : ℝ :=
    ∫ u in (0 : ℝ)..(6 / 5 : ℝ),
      (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u
  let E : ℝ := Real.exp (1 / 16 : ℝ)
  let C : ℝ := LLS.PaperStatements.subgroupConductorLogSum H
  let A : ℝ := LLS.PaperStatements.gaussianPrefixError (P) n x
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 20000) hnlarge
  have hrootSq : s ^ 2 = r := by dsimp only [s, r]
  have hrbound : ((91 / 10 : ℝ) ^ 2) ≤ r :=
    (sq_le_sq₀ (by norm_num only) (by linarith only [hs91])).mpr hs91
  have hspos : 0 < s := by
    dsimp only [s, L]
    linarith only [hs91]
  have hs14 : (91 / 10 : ℝ) ≤ s := hs91
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
  have hcut : (6 / 5 : ℝ) * x = (6 / 5 : ℝ) * (s0 ^ 2) ^ 2 := by dsimp only [r, x]
  have hX : (N : ℝ) ≤ (6 / 5 : ℝ) * x := hN
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
  have hcmp :=
    LLS.PaperStatements.gaussian_relative_prefix_le hprefix hnlarge H hGRH hwidth hh1 hx
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
      Analysis.gaussianMRRefinedConductor * L + Analysis.gaussianMRRefinedBeta * s + (D) := by
    dsimp only [r, s, L]
    exact hbudget
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
    have herr := herror m hi
    change
      (m / (m - 1)) *
            (21 * Analysis.gaussianMR6FifthsEndpoint / (10 * Analysis.gaussianMRRefinedWidth * s) +
              1839 * Analysis.gaussianMR6FifthsEndpoint / (1000 * r)) +
          13 / (m - 1) +
          A <
        (D) at herr
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

/-- A uniform squarefree Korselt triple is handled by any actual index-four
witness rule with conductor at most twice log n. Extract its three factors,
construct the pass-containing subgroup, and preserve the supplied real cutoff. -/
theorem gaussianBudget_witness_card {n : ℕ} [NeZero n] {B : ℝ} (hnOdd : Odd n) (hsf : Squarefree n)
    (hc : n.primeFactors.card = 3) (hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1)
    (hU :
      ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hfour :
      ∀ H : Subgroup (ZMod n)ˣ,
        H.index = 4 →
          (∀ z : ZMod n,
            PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z) →
          LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n →
          ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    ∃ s : ℕ, s.Prime ∧ (s : ℝ) ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
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
  obtain ⟨H, hi, hpass, hC⟩ :=
    three_prime_korselt_conductor_subgroup_data hp hq hr
      (hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpn))
      (hq.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hqn))
      (hr.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hrn)) hpq hpr hqr hnprod (hK p hp hpn)
      (hK q hq hqn) (hK r hr hrn) (hU p q hp hq hpn hqn) (hU p r hp hr hpn hrn)
  exact hfour H hi hpass hC.le

/-- For an odd composite with log n at least 63, actual large-index and
index-four witness rules and a local cutoff comparison imply an actual
rejecting prime under B. The finite-index classification removes all public
factor-count, squarefreeness and subgroup-index restrictions. -/
theorem exists_prime_gaussianBudget {n : ℕ} [NeZero n] {B : ℝ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n)
    (hlarge :
      ∀ H : Subgroup (ZMod n)ˣ,
        Analysis.gaussianMR6FifthsIndex ≤ (H.index : ℝ) →
          (∀ z : ZMod n,
            PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z) →
          ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n))
    (hfour :
      ∀ H : Subgroup (ZMod n)ˣ,
        H.index = 4 →
          (∀ z : ZMod n,
            PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z) →
          LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n →
          ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n))
    (hlocal : ∀ q : ℕ, 0 < q → q ^ 2 ≤ 10 ^ 9 * n → max (3000 : ℝ) (Real.log q ^ 2) ≤ B) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hnpos : 0 < n := ho.pos
  have hN := gaussian35000_size hnpos hL
  have hn1 : 1 < n := (by norm_num only : 1 < 10 ^ 27).trans_le hN
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
      exact ⟨p, hp, hb.trans (hlocal q hqp hqsize), hr⟩
    · obtain ⟨hsf, hcard, hK, hUval⟩ := ht
      exact gaussianBudget_witness_card ho hsf hcard hK hUval hfour
  · have hiR : Analysis.gaussianMR6FifthsIndex ≤ ((PrimeTest.fermatSubgroup n).index : ℝ) := by
      norm_num only [Analysis.gaussianMR6FifthsIndex]
      exact_mod_cast (lt_of_not_ge hi).le
    have hpass :
      ∀ z : ZMod n,
        PrimeTest.StrongMillerRabinPass n z →
          ∃ u : (ZMod n)ˣ, u ∈ PrimeTest.fermatSubgroup n ∧ (u : ZMod n) = z := by
      intro z hz
      exact PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn1 ho hz
    exact hlarge (PrimeTest.fermatSubgroup n) hiR hpass

end PseudoPrime.PrimeTestBounds.MillerRabin
