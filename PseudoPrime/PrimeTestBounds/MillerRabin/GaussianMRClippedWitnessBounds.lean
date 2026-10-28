/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMRClippedNumerics
public import PseudoPrime.LLS.GaussianClippedPrefix
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMR35000WitnessBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointEvenPolynomial

/-! # All-input Gaussian witness bounds with cutoff floors -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For either clipped profile at log n>=63, an index-four subgroup with conductor
log-sum<=2 log n cannot satisfy the signed Gaussian comparison. Use the common
width lemma, clipped-root inequality and strict triple error/main margins. -/
theorem gaussianClipped_index_four (f : Bool) {n : ℕ} [NeZero n] (H : Subgroup (ZMod n)ˣ)
    (hi : H.index = 4) (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n)
    (hL : 63 ≤ Real.log n) :
    let L := Real.log n
    let r := Analysis.gaussianFloorRadius f L
    let s := Analysis.gaussianFloorRoot f L
    let h := Analysis.gaussianMRRefinedWidth / s
    let x := r ^ 2
    ¬(((H.index : ℝ) * (1 - h) *
              (∫ u in (0 : ℝ)..(6 / 5 : ℝ),
                (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
            Real.exp (1 / 16 : ℝ)) *
          Real.sqrt x ≤
        Analysis.gaussianMRRefinedConductor * LLS.PaperStatements.subgroupConductorLogSum H +
          (H.index : ℝ) *
            (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / Real.sqrt x) * Real.exp (1 / 16 : ℝ)) +
          13 +
          ((H.index - 1 : ℕ) : ℝ) *
            LLS.PaperStatements.gaussianPrefixError (Analysis.gaussianFloorPrefix f) n x) := by
  intro L r s h x hcmp
  have hindex : (H.index : ℝ) = 4 := by exact_mod_cast hi
  let I : ℝ :=
    ∫ u in (0 : ℝ)..(6 / 5 : ℝ),
      (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u
  let E : ℝ := Real.exp (1 / 16 : ℝ)
  have hrpos : 0 < r := by
    dsimp only [r]
    exact sq_pos_of_pos (Analysis.gaussianFloor_root_pos f _)
  have hspos : 0 < s := by
    dsimp only [s]
    exact Analysis.gaussianFloor_root_pos f _
  have hrootSq : s ^ 2 = r := by dsimp only [s, r, Analysis.gaussianFloorRadius]
  have hrbound : (170 : ℝ) ≤ r := Analysis.gaussianFloor_radius_large f (Real.log n)
  have hsbound : (13 : ℝ) ≤ s := Analysis.gaussianFloor_root_thirteen f (Real.log n)
  have hsqrtx : Real.sqrt x = r := by
    dsimp only [x]
    exact Real.sqrt_sq hrpos.le
  rw [hsqrtx] at hcmp
  have hI : Analysis.gaussianMRRefinedMass ≤ I := by
    dsimp only [I, Analysis.gaussianMRRefinedMass]
    exact Analysis.gaussianMRRefined_mass.le
  have hE : E ≤ Analysis.gaussianMR6FifthsEndpoint := by
    dsimp only [E, Analysis.gaussianMR6FifthsEndpoint]
    exact Analysis.gaussian_endpoint_exp_le
  have hh : h = Analysis.gaussianMRRefinedWidth / s := by rfl
  have hh1 : h ≤ 1 / 2 := by
    rw [hh, div_le_iff₀ hspos]
    norm_num only [Analysis.gaussianMRRefinedWidth]
    linarith only [hsbound]
  have hcmp' :
    (4 * (1 - h) * I - E) * r ≤
      Analysis.gaussianMRRefinedConductor * LLS.PaperStatements.subgroupConductorLogSum H +
        4 * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * Real.exp (1 / 16 : ℝ)) +
        13 +
        3 * LLS.PaperStatements.gaussianPrefixError (Analysis.gaussianFloorPrefix f) n (r ^ 2) := by
    dsimp only [x] at hcmp
    simpa only [hindex, hi, Nat.cast_ofNat, Nat.reduceSub] using hcmp
  have hCscaled : LLS.PaperStatements.subgroupConductorLogSum H / 3 ≤ (2 / 3 : ℝ) * Real.log n := by
    apply (div_le_iff₀ (by norm_num only : (0 : ℝ) < 3)).2
    nlinarith only [hC]
  have herror :
    (4 / 3 : ℝ) *
          (21 * Analysis.gaussianMR6FifthsEndpoint / (10 * Analysis.gaussianMRRefinedWidth * s) +
            1839 * Analysis.gaussianMR6FifthsEndpoint / (1000 * r)) +
        13 / 3 +
        LLS.PaperStatements.gaussianPrefixError (Analysis.gaussianFloorPrefix f) n (r ^ 2) <
      11 := by
    exact Analysis.gaussianFloor_triple_error (f := f) hL le_rfl
  exact
    Analysis.gaussianMR_compare_width (m := 4) (t := 3) (s := s) (r := r) (A :=
      LLS.PaperStatements.gaussianPrefixError (Analysis.gaussianFloorPrefix f) n (r ^ 2)) (L :=
      (2 / 3 : ℝ) * Real.log n) (I := I) (E := E) (C :=
      LLS.PaperStatements.subgroupConductorLogSum H) (h := h) (M := Analysis.gaussianMRRefinedMass)
      (Ecap := Analysis.gaussianMR6FifthsEndpoint) (conductor :=
      Analysis.gaussianMRRefinedConductor) (D :=
      (4 * Analysis.gaussianMRRefinedMass - Analysis.gaussianMR6FifthsEndpoint) / 3) (beta :=
      (4 / 3 : ℝ) *
        (Analysis.gaussianMRRefinedMass * Analysis.gaussianMRRefinedWidth +
          1 / (10 * Analysis.gaussianMRRefinedWidth)))
      (by norm_num only [Analysis.gaussianMRRefinedWidth]) (by norm_num only : (4 : ℝ) ≤ 4)
      (by norm_num only : (3 : ℝ) = (4 : ℝ) - 1) hspos hrootSq.symm hh hh1 hI hE hCscaled
      (by norm_num only [Analysis.gaussianMRRefinedConductor] :
        (0 : ℝ) ≤ Analysis.gaussianMRRefinedConductor)
      le_rfl le_rfl hcmp'
      (by
        intro hbudget
        have hnorm :
          ((4 * Analysis.gaussianMRRefinedMass - Analysis.gaussianMR6FifthsEndpoint) / 3) * r ≤
            (2 / 3 : ℝ) * Analysis.gaussianMRRefinedConductor * Real.log n +
              (4 / 3 : ℝ) *
                (Analysis.gaussianMRRefinedMass * Analysis.gaussianMRRefinedWidth +
                  1 / (10 * Analysis.gaussianMRRefinedWidth)) *
                s +
              11 := by
          dsimp only [Analysis.gaussianMRRefinedMass,
            Analysis.gaussianMR6FifthsEndpoint] at hbudget herror ⊢
          nlinarith only [hbudget, herror]
        exact Analysis.gaussianFloor_triple_absurd (f := f) hL hnorm)

/-- Under GRH at log n>=63, an index-four pass-containing subgroup with conductor
log-sum<=2 log n yields an actual rejecting prime within the clipped cutoff.
The cutoff floor contains the chosen certified prefix and every factor base is excluded. -/
theorem gaussianClipped_witness_four (f : Bool) {n : ℕ} [NeZero n] (hnOdd : Odd n)
    (hnlarge : 20000 ≤ n) (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianFloorBound f (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_contra hnone
  let r := Analysis.gaussianFloorRadius f (Real.log n)
  let x := r ^ 2
  have hcut : (6 / 5 : ℝ) * x = Analysis.gaussianFloorBound f (Real.log n) := by
    dsimp only [x, Analysis.gaussianFloorBound, Analysis.gaussianFloorRadius, r]
  have hX : (Analysis.gaussianFloorCutoff f : ℝ) ≤ (6 / 5 : ℝ) * x := by
    rw [hcut]
    exact Analysis.gaussianFloor_cutoff_le f (Real.log n)
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
  have hrootSq : (Analysis.gaussianFloorRoot f (Real.log n)) ^ 2 = r := by
    dsimp only [r, Analysis.gaussianFloorRadius]
  have hrbound : (170 : ℝ) ≤ r := Analysis.gaussianFloor_radius_large f (Real.log n)
  have hspos : 0 < Analysis.gaussianFloorRoot f (Real.log n) := Analysis.gaussianFloor_root_pos f _
  have hsbound : (13 : ℝ) ≤ Analysis.gaussianFloorRoot f (Real.log n) :=
    Analysis.gaussianFloor_root_thirteen f (Real.log n)
  have hwidth : 0 < Analysis.gaussianMRRefinedWidth / Analysis.gaussianFloorRoot f (Real.log n) :=
    div_pos (by norm_num only [Analysis.gaussianMRRefinedWidth]) hspos
  have hwidth1 :
    Analysis.gaussianMRRefinedWidth / Analysis.gaussianFloorRoot f (Real.log n) ≤ 1 / 2 := by
    rw [div_le_iff₀ hspos]
    norm_num only [Analysis.gaussianMRRefinedWidth]
    linarith only [hsbound]
  have hx : 4 ≤ x := by
    dsimp only [x]
    nlinarith only [hrbound]
  have hprefix :
    Analysis.gaussianFloorPrefix f ≤
      ∑ n ∈ Finset.Ioc 0 (Analysis.gaussianFloorCutoff f),
        Analysis.gaussianResolventMangoldtWeight n := by
    cases f
    · simpa only [Analysis.gaussianFloorPrefix, Analysis.gaussianFloorCutoff, Bool.false_eq_true,
        ite_false, ite_true, Nat.floor_ofNat] using
        LLS.gaussian_prefix35000_sharp hGRH.riemann (le_refl (35000 : ℝ))
    · simpa only [Analysis.gaussianFloorPrefix, Analysis.gaussianFloorCutoff, Bool.false_eq_true,
        ite_false, ite_true, Nat.floor_ofNat] using
        LLS.gaussian_prefix50000_lower hGRH.riemann (le_refl (50000 : ℝ))
  have hcmp :=
    LLS.PaperStatements.gaussian_relative_prefix_le hprefix hnlarge H hGRH hwidth hwidth1 hx
      (by norm_num only : (0 : ℝ) ≤ 6 / 5) hX hdiv hsmall
  exact gaussianClipped_index_four f H hi hC hL hcmp

/-- Under GRH at log n>=63, a pass-containing subgroup of index>=10^9 has a
rejecting prime within either clipped cutoff. Reuse the signed Gaussian prefix
comparison with exact conductor coefficient, then contradict the strict residual
bound using d*r>=c*L+beta*s+D. The clipped root is not treated as an equality root. -/
theorem gaussianClipped_witness_large (f : Bool) {n : ℕ} [NeZero n] (hnOdd : Odd n)
    (hnlarge : 20000 ≤ n) (H : Subgroup (ZMod n)ˣ)
    (hi : Analysis.gaussianMR6FifthsIndex ≤ (H.index : ℝ))
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianFloorBound f (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_contra hnone
  let L := Real.log n
  let r := Analysis.gaussianFloorRadius f L
  let s := Analysis.gaussianFloorRoot f L
  let x := r ^ 2
  let h := Analysis.gaussianMRRefinedWidth / s
  let m : ℝ := H.index
  let t : ℝ := m - 1
  let I : ℝ :=
    ∫ u in (0 : ℝ)..(6 / 5 : ℝ),
      (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u
  let E : ℝ := Real.exp (1 / 16 : ℝ)
  let C : ℝ := LLS.PaperStatements.subgroupConductorLogSum H
  let A : ℝ := LLS.PaperStatements.gaussianPrefixError (Analysis.gaussianFloorPrefix f) n x
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 20000) hnlarge
  have hrootSq : s ^ 2 = r := by dsimp only [s, r, Analysis.gaussianFloorRadius]
  have hrbound : (170 : ℝ) ≤ r := Analysis.gaussianFloor_radius_large f (Real.log n)
  have hspos : 0 < s := by
    dsimp only [s, L]
    exact Analysis.gaussianFloor_root_pos f _
  have hs14 : (13 : ℝ) ≤ s := Analysis.gaussianFloor_root_thirteen f (Real.log n)
  have hh : h = Analysis.gaussianMRRefinedWidth / s := by rfl
  have hh1 : h ≤ 1 / 2 := by
    rw [hh, div_le_iff₀ hspos]
    norm_num only [Analysis.gaussianMRRefinedWidth]
    linarith only [hs14]
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 170) hrbound
  have hsqrtx : Real.sqrt x = r := by
    dsimp only [x]
    exact Real.sqrt_sq hrpos.le
  have hx : 4 ≤ x := by
    dsimp only [x]
    nlinarith only [hrbound]
  have hcut : (6 / 5 : ℝ) * x = Analysis.gaussianFloorBound f (Real.log n) := by
    dsimp only [Analysis.gaussianFloorBound, Analysis.gaussianFloorRadius, r, L, x]
  have hX : (Analysis.gaussianFloorCutoff f : ℝ) ≤ (6 / 5 : ℝ) * x := by
    rw [hcut]
    exact Analysis.gaussianFloor_cutoff_le f (Real.log n)
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
  have hprefix :
    Analysis.gaussianFloorPrefix f ≤
      ∑ n ∈ Finset.Ioc 0 (Analysis.gaussianFloorCutoff f),
        Analysis.gaussianResolventMangoldtWeight n := by
    cases f
    · simpa only [Analysis.gaussianFloorPrefix, Analysis.gaussianFloorCutoff, Bool.false_eq_true,
        ite_false, ite_true, Nat.floor_ofNat] using
        LLS.gaussian_prefix35000_sharp hGRH.riemann (le_refl (35000 : ℝ))
    · simpa only [Analysis.gaussianFloorPrefix, Analysis.gaussianFloorCutoff, Bool.false_eq_true,
        ite_false, ite_true, Nat.floor_ofNat] using
        LLS.gaussian_prefix50000_lower hGRH.riemann (le_refl (50000 : ℝ))
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
      Analysis.gaussianMRRefinedConductor * L + Analysis.gaussianMRRefinedBeta * s +
        Analysis.gaussianFloorConstant f := by
    dsimp only [r, s, L]
    exact Analysis.gaussianFloor_equation_le f (by linarith only [hL] : 0 ≤ Real.log n)
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
    have herr := Analysis.gaussianFloor_residual (f := f) (q := n) hL hi le_rfl
    change
      (m / (m - 1)) *
            (21 * Analysis.gaussianMR6FifthsEndpoint / (10 * Analysis.gaussianMRRefinedWidth * s) +
              1839 * Analysis.gaussianMR6FifthsEndpoint / (1000 * r)) +
          13 / (m - 1) +
          A <
        Analysis.gaussianFloorConstant f at herr
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

/-- For an odd uniform three-prime Korselt product, either clipped cutoff bounds a
rejecting prime under GRH from log n>=63. Construct the existing index-four
subgroup with its conductor-sum bound and apply the index-four witness theorem. -/
theorem gaussianClipped_witness_triple (f : Bool) {n p q r : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (hn : n = p * q * r) (hpdiv : p - 1 ∣ n - 1) (hqdiv : q - 1 ∣ n - 1)
    (hrdiv : r - 1 ∣ n - 1) (hpv : padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hprv : padicValNat 2 (p - 1) = padicValNat 2 (r - 1)) (hnlarge : 20000 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianFloorBound f (Real.log n) ∧
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
  exact gaussianClipped_witness_four f hnOdd hnlarge H hi hpass hGRH hC.le hL

/-- For a squarefree uniform Korselt triple specified by its factor set, extract
the three primes and apply the clipped index-four witness theorem.
This branch interface is internal to the all-input classification. -/
theorem gaussianClipped_witness_card (f : Bool) {n : ℕ} (hnOdd : Odd n) (hsf : Squarefree n)
    (hc : n.primeFactors.card = 3) (hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1)
    (hU :
      ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hnlarge : 20000 ≤ n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 63 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianFloorBound f (Real.log n) ∧
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
    gaussianClipped_witness_triple f hp hq hr (hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpn))
      (hq.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hqn))
      (hr.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hrn)) hpq hpr hqr hnprod (hK p hp hpn)
      (hK q hq hqn) (hK r hr hrn) (hU p q hp hq hpn hqn) (hU p r hp hr hpn hrn) hnlarge hGRH hL

/-- For log n>=63 and q^2<=10^9*n, the local subgroup envelope fits either clipped bound.
Use log q<=(2/3)log n, the cutoff floor>=35000 and the bound>(15/32)log(n)^2.
The separate local consumer receives the ambient passing-base containment. -/
theorem gaussianClipped_local (f : Bool) {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
    (hsize : q ^ 2 ≤ 10 ^ 9 * n) (hL : 63 ≤ Real.log n) :
    max (3000 : ℝ) (Real.log q ^ 2) ≤ Analysis.gaussianFloorBound f (Real.log n) := by
  have hlog := Analysis.mr_local_log_le_of_square_le hn hq hsize
  have hcap : Real.log q ≤ (2 / 3 : ℝ) * Real.log n := by
    linarith only [hlog, hL, Analysis.log_ten_lt_seven_thirds]
  have hpos : (0 : ℝ) ≤ (2 / 3) * Real.log n := by linarith only [hL]
  have hs := (sq_le_sq₀ (Real.log_natCast_nonneg q) hpos).mpr hcap
  have hwide := Analysis.gaussianFloor_bound_lower (f := f) hL
  have hN : (35000 : ℝ) ≤ (Analysis.gaussianFloorCutoff f : ℝ) := by
    cases f <;>
      norm_num only [Analysis.gaussianFloorCutoff, Nat.cast_ofNat, Bool.false_eq_true, ite_false,
        ite_true]
  have hcut := hN.trans (Analysis.gaussianFloor_cutoff_le f (Real.log n))
  exact max_le (by linarith only [hcut]) (by nlinarith only [hs, hwide, sq_nonneg (Real.log n)])

/-- Under GRH, every odd composite with log n>=63 has a rejecting prime within
either clipped Gaussian cutoff. Combine the coefficient-free finite-index
classification, the ambient-to-local subgroup transfer, the uniform triple and
large-index comparison. No squarefree or factor-count condition remains. -/
theorem exists_prime_gaussianClipped (f : Bool) {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianFloorBound f (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
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
      exact ⟨p, hp, hb.trans (gaussianClipped_local f hnpos hqp hqsize hL), hr⟩
    · obtain ⟨hsf, hcard, hK, hUval⟩ := ht
      exact gaussianClipped_witness_card f ho hsf hcard hK hUval hnlarge hGRH hL
  · have hiR : Analysis.gaussianMR6FifthsIndex ≤ ((PrimeTest.fermatSubgroup n).index : ℝ) := by
      norm_num only [Analysis.gaussianMR6FifthsIndex]
      exact_mod_cast (lt_of_not_ge hi).le
    have hpass :
      ∀ z : ZMod n,
        PrimeTest.StrongMillerRabinPass n z →
          ∃ u : (ZMod n)ˣ, u ∈ PrimeTest.fermatSubgroup n ∧ (u : ZMod n) = z := by
      intro z hz
      exact PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn1 ho hz
    exact gaussianClipped_witness_large f ho hnlarge (PrimeTest.fermatSubgroup n) hiR hpass hGRH hL

/-- Under the clipped Gaussian assumptions, the least rejecting prime satisfies
the selected profile cutoff. Apply least-prime extraction to the actual witness theorem. -/
theorem exists_least_gaussianClipped (f : Bool) {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianFloorBound f (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨ho.pos.ne'⟩
  exact
    exists_least_prime_reject_of_exists_prime_reject (exists_prime_gaussianClipped f ho hc hGRH hL)

/-- The minimum of the two certified clipped Gaussian cutoffs.
Both all-input witness theorems apply from logarithmic scale 63 with no upper limit. -/
noncomputable def gaussianClippedEnvelope (L : ℝ) : ℝ :=
  min (Analysis.gaussianFloorBound false L) (Analysis.gaussianFloorBound true L)

/-- Under GRH, every odd composite with log n>=63 has a prime rejecting strong MR
within the clipped Gaussian envelope. Select the smaller certified profile
and retain primality, the numerical bound and actual strong-MR rejection. -/
theorem exists_prime_gaussianClippedEnvelope {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gaussianClippedEnvelope (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases h :
    Analysis.gaussianFloorBound false (Real.log n) ≤ Analysis.gaussianFloorBound true (Real.log n)
  · simpa only [gaussianClippedEnvelope, min_eq_left h] using
      exists_prime_gaussianClipped false ho hc hGRH hL
  · simpa only [gaussianClippedEnvelope, min_eq_right (le_of_not_ge h)] using
      exists_prime_gaussianClipped true ho hc hGRH hL

/-- Under the clipped-envelope assumptions, the least rejecting prime is within
the two-profile envelope. Extract it from the actual prime-witness theorem. -/
theorem exists_least_gaussianClippedEnvelope {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gaussianClippedEnvelope (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨ho.pos.ne'⟩
  exact
    exists_least_prime_reject_of_exists_prime_reject
      (exists_prime_gaussianClippedEnvelope ho hc hGRH hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
