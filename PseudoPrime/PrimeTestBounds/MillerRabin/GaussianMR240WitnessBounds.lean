/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianStarClassification
public import PseudoPrime.Analysis.GaussianMR240Numerics

/-! # The unchanged constant-six Gaussian MR bound from logarithmic scale 240 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At logarithmic scale at least 240, the certified 35000 prefix supplies the
constant-six witness bound for this classification branch. Use the signed comparison with
principal error thirteen and the unchanged radius equation. Downstream wrappers remove the
branch data. -/
theorem gaussianMR6_index_four240 {n : ℕ} [NeZero n] (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) (hL : 240 ≤ Real.log n) :
    let L := Real.log n
    let r := Analysis.gaussianMR6Radius L
    let s := Analysis.gaussianMR6Root L
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
  intro L r s h x hcmp
  have hindex : (H.index : ℝ) = 4 := by exact_mod_cast hi
  let I : ℝ :=
    ∫ u in (0 : ℝ)..(6 / 5 : ℝ),
      (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u
  let E : ℝ := Real.exp (1 / 16 : ℝ)
  have hrpos : 0 < r := by
    dsimp only [r]
    exact sq_pos_of_pos (Analysis.gaussianMR6_root_pos _)
  have hspos : 0 < s := by
    dsimp only [s]
    exact Analysis.gaussianMR6_root_pos _
  have hrootSq : s ^ 2 = r := by dsimp only [s, r, Analysis.gaussianMR6Radius]
  have hrbound : 170 ≤ r := by
    dsimp only [r]
    have hr := Analysis.gaussianMR6_radius_lower240 hL
    nlinarith only [hL, hr]
  have hsbound : 13 ≤ s := by
    dsimp only [s]
    exact le_trans (by norm_num only) (Analysis.gaussianMR6_root_lower hL)
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
  have herror :
    (4 / 3 : ℝ) *
          (63 * Analysis.gaussianMR6FifthsEndpoint / (10 * s) +
            1839 * Analysis.gaussianMR6FifthsEndpoint / (1000 * r)) +
        13 / 3 +
        LLS.PaperStatements.gaussianPrefixError (47 / 10) n (r ^ 2) <
      11 := by
    exact Analysis.gaussianMR6_triple_error240 hL le_rfl
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
      (by
        intro hbudget
        have hnorm :
          ((4 * Analysis.gaussianMR6FifthsMass - Analysis.gaussianMR6FifthsEndpoint) / 3) * r ≤
            (161 / 600 : ℝ) * Real.log n +
              (4 / 3 : ℝ) * (Analysis.gaussianMR6FifthsMass / 3 + 3 / 10) * s +
              11 := by
          dsimp only [Analysis.gaussianMR6FifthsMass,
            Analysis.gaussianMR6FifthsEndpoint] at hbudget herror ⊢
          nlinarith only [hbudget, herror]
        exact Analysis.gaussianMR6_triple240 hL hnorm)

/-- At logarithmic scale at least 240, the certified 35000 prefix supplies the
constant-six witness bound for this classification branch. Use the signed comparison with
principal error thirteen and the unchanged radius equation. Downstream wrappers remove the
branch data. -/
theorem gaussianMR6_witness_four240 {n : ℕ} [NeZero n] (hnOdd : Odd n) (hnlarge : 20000 ≤ n)
    (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) (hL : 240 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianMR6Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_contra hnone
  let r := Analysis.gaussianMR6Radius (Real.log n)
  let x := r ^ 2
  have hcut : (6 / 5 : ℝ) * x = Analysis.gaussianMR6Bound (Real.log n) := by
    dsimp only [x, Analysis.gaussianMR6Bound, Analysis.gaussianMR6Radius, r]
  have hX : 35000 ≤ (6 / 5 : ℝ) * x := by
    rw [hcut]
    exact (Analysis.gaussianMR6_prefix35000 hL).le
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
  have hrootSq : (Analysis.gaussianMR6Root (Real.log n)) ^ 2 = r := by
    dsimp only [r, Analysis.gaussianMR6Radius]
  have hrbound : 170 ≤ r := by
    dsimp only [r]
    have hr := Analysis.gaussianMR6_radius_lower240 hL
    nlinarith only [hr, hL]
  have hspos : 0 < Analysis.gaussianMR6Root (Real.log n) := Analysis.gaussianMR6_root_pos _
  have hsbound : 13 ≤ Analysis.gaussianMR6Root (Real.log n) :=
    le_trans (by norm_num only) (Analysis.gaussianMR6_root_lower hL)
  have hwidth : 0 < 1 / (3 * Analysis.gaussianMR6Root (Real.log n)) :=
    one_div_pos.mpr (mul_pos (by norm_num only) hspos)
  have hwidth1 : 1 / (3 * Analysis.gaussianMR6Root (Real.log n)) ≤ 1 / 2 := by
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
  exact gaussianMR6_index_four240 H hi hC hL hcmp

/-- At logarithmic scale at least 240, the certified 35000 prefix supplies the
constant-six witness bound for this classification branch. Use the signed comparison with
principal error thirteen and the unchanged radius equation. Downstream wrappers remove the
branch data. -/
theorem gaussianMR6_witness_large240 {n : ℕ} [NeZero n] (hnOdd : Odd n) (hnlarge : 20000 ≤ n)
    (H : Subgroup (ZMod n)ˣ) (hi : Analysis.gaussianMR6FifthsIndex ≤ (H.index : ℝ))
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 240 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianMR6Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_contra hnone
  let L := Real.log n
  let r := Analysis.gaussianMR6Radius L
  let s := Analysis.gaussianMR6Root L
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
  have hrootSq : s ^ 2 = r := by dsimp only [s, r, Analysis.gaussianMR6Radius]
  have hrbound : 170 ≤ r := by
    dsimp only [r, L]
    have hr := Analysis.gaussianMR6_radius_lower240 hL
    nlinarith only [hL, hr]
  have hspos : 0 < s := by
    dsimp only [s, L]
    exact Analysis.gaussianMR6_root_pos _
  have hs13 : 13 ≤ s := by
    dsimp only [s, L]
    exact le_trans (by norm_num only) (Analysis.gaussianMR6_root_lower hL)
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
  have hcut : (6 / 5 : ℝ) * x = Analysis.gaussianMR6Bound (Real.log n) := by
    dsimp only [Analysis.gaussianMR6Bound, Analysis.gaussianMR6Radius, r, L, x]
  have hX : 35000 ≤ (6 / 5 : ℝ) * x := by
    rw [hcut]
    exact (Analysis.gaussianMR6_prefix35000 hL).le
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
  have hroot :
    Analysis.gaussianMR6FifthsD * r =
      Analysis.gaussianMR6FifthsConductor * L + Analysis.gaussianMR6FifthsBeta * s + 6 := by
    dsimp only [r, s, L]
    exact Analysis.gaussianMR6_equation (by linarith only [hL] : 0 ≤ Real.log n)
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
    have ht : t = m - 1 := by rfl
    have hgamma := hcoeff.2.1
    have herr := Analysis.gaussianMR6_residual240 (q := n) hL le_rfl hi
    change
      (m / (m - 1)) *
            (63 * Analysis.gaussianMR6FifthsEndpoint / (10 * s) +
              1839 * Analysis.gaussianMR6FifthsEndpoint / (1000 * r)) +
          13 / (m - 1) +
          A <
        6 at herr
    rw [ht] at hbudget
    linarith only [hbudget, hroot, herr]
  exact
    Analysis.gaussianMR_relative_comparison_to_scalar (m := m) (t := t) (s := s) (r := r) (A := A)
      (L := L) (I := I) (E := E) (C := C) (h := h) (M := Analysis.gaussianMR6FifthsMass) (Ecap :=
      Analysis.gaussianMR6FifthsEndpoint) (conductor := Analysis.gaussianMR6FifthsConductor) (D :=
      Analysis.gaussianMR6FifthsD) (beta := Analysis.gaussianMR6FifthsBeta)
      (by
        have hi' : (1000000000 : ℝ) ≤ m := by
          simpa only [m, Analysis.gaussianMR6FifthsIndex] using hi
        linarith only [hi'])
      rfl hspos rfl hh hh1 hI hE hC (by norm_num only [Analysis.gaussianMR6FifthsConductor]) hD
      hbeta hcmp' hfinish

/-- At logarithmic scale at least 240, the certified 35000 prefix supplies the
constant-six witness bound for this classification branch. Use the signed comparison with
principal error thirteen and the unchanged radius equation. Downstream wrappers remove the
branch data. -/
theorem gaussianMR6_witness_triple240 {n p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hn : n = p * q * r) (hpdiv : p - 1 ∣ n - 1) (hqdiv : q - 1 ∣ n - 1) (hrdiv : r - 1 ∣ n - 1)
    (hpv : padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hprv : padicValNat 2 (p - 1) = padicValNat 2 (r - 1)) (hnlarge : 20000 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 240 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianMR6Bound (Real.log n) ∧
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
  exact gaussianMR6_witness_four240 hnOdd hnlarge H hi hpass hGRH hC.le hL

/-- At logarithmic scale at least 240, the certified 35000 prefix supplies the
constant-six witness bound for this classification branch. Use the signed comparison with
principal error thirteen and the unchanged radius equation. Downstream wrappers remove the
branch data. -/
theorem gaussianMR6_witness_card_three240 {n : ℕ} (hnOdd : Odd n) (hsf : Squarefree n)
    (hc : n.primeFactors.card = 3) (hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1)
    (hU :
      ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hnlarge : 20000 ≤ n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 240 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianMR6Bound (Real.log n) ∧
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
    gaussianMR6_witness_triple240 hp hq hr (hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpn))
      (hq.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hqn))
      (hr.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hrn)) hpq hpr hqr hnprod (hK p hp hpn)
      (hK q hq hqn) (hK r hr hrn) (hU p q hp hq hpn hqn) (hU p r hp hr hpn hrn) hnlarge hGRH hL

/-- At logarithmic scale at least 240, the certified 35000 prefix supplies the
constant-six witness bound for this classification branch. Use the signed comparison with
principal error thirteen and the unchanged radius equation. Downstream wrappers remove the
branch data. -/
theorem gaussianMR6_witness_small240 {n : ℕ} [NeZero n] (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 9) (hL : 240 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianMR6Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  rcases
    finite_index_witness_or_uniform_korselt_triple_log240 hnOdd hcomp (PrimeTest.fermatSubgroup n)
      le_rfl hi hGRH (by linarith only [hL]) with
    hlocal | htriple
  · obtain ⟨s, hs, hbound, hfail⟩ := hlocal
    have hbound' := Analysis.gaussianMR6_local240 hL
    exact ⟨s, hs, hbound.trans (le_of_lt hbound'), hfail⟩
  · obtain ⟨hsf, hc, hK, hU⟩ := htriple
    have hN27 := Analysis.ten_pow_twentyseven_le_of_log_ge_240 (by linarith only [hL])
    have hnlarge : 20000 ≤ n := by
      have h20000 : 20000 ≤ 10 ^ 27 := by norm_num only
      exact h20000.trans hN27
    exact gaussianMR6_witness_card_three240 hnOdd hsf hc hK hU hnlarge hGRH hL

/-- The Fermat subgroup contains every strong-MR pass. At log n>=240, its index bound
therefore feeds the large-index Gaussian witness theorem. This discharges the subgroup
input without adding it to the public all-composite statement. -/
theorem gaussianMR6_fermat_large240 {n : ℕ} (hn1 : 1 < n) (hnOdd : Odd n)
    (hi : 1000000000 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 240 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianMR6Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  have hnlarge : 20000 ≤ n :=
    (by norm_num only : 20000 ≤ 10 ^ 27).trans (Analysis.ten_pow_twentyseven_le_of_log_ge_240 hL)
  have hiR : Analysis.gaussianMR6FifthsIndex ≤ ((PrimeTest.fermatSubgroup n).index : ℝ) := by
    norm_num only [Analysis.gaussianMR6FifthsIndex]
    exact_mod_cast hi
  have hpass :
    ∀ z : ZMod n,
      PrimeTest.StrongMillerRabinPass n z →
        ∃ u : (ZMod n)ˣ, u ∈ PrimeTest.fermatSubgroup n ∧ (u : ZMod n) = z := by
    intro z hz
    obtain ⟨u, hu, he⟩ := PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn1 hnOdd hz
    exact ⟨u, hu, he⟩
  exact gaussianMR6_witness_large240 hnOdd hnlarge (PrimeTest.fermatSubgroup n) hiR hpass hGRH hL

/-- Under GRH, every odd composite with log n>=240 has a prime rejecting strong MR below
its unchanged constant-six Gaussian bound. Combine the small-index classification,
the index-four Korselt branch and the large Fermat-index branch. -/
theorem exists_prime_witness_gaussianMR6_log240 {n : ℕ} (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 240 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianMR6Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  have hn0 : 0 < n := by
    by_contra hnot
    have hnz : n = 0 := Nat.eq_zero_of_not_pos hnot
    simp only [hnz, Nat.cast_zero, Real.log_zero] at hL
    norm_num only at hL
  have hnlog := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr hn0)
  have hn1 : 1 < n := by
    have hn1R : ((1 : ℕ) : ℝ) < (n : ℝ) := by
      norm_num only [Nat.cast_one]
      linarith only [hL, hnlog]
    exact Nat.cast_lt.mp hn1R
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  by_cases hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 9
  · exact gaussianMR6_witness_small240 hnOdd hcomp hGRH hi hL
  · have hlarge : 1000000000 ≤ (PrimeTest.fermatSubgroup n).index := by
      have h := (lt_of_not_ge hi).le
      norm_num only at h
      exact h
    exact gaussianMR6_fermat_large240 hn1 hnOdd hlarge hGRH hL

/-- Under GRH and log n>=240, the least prime rejecting strong MR obeys the unchanged
constant-six Gaussian bound. Minimize the proved prime-witness existence with Nat.find.
This is the public pointwise least-witness API for the shorter starting range. -/
theorem exists_least_witness_gaussianMR6_log240 {n : ℕ} (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 240 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ Analysis.gaussianMR6Bound (Real.log n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  classical
  obtain ⟨p, hp, hbound, hreject⟩ := exists_prime_witness_gaussianMR6_log240 hnOdd hcomp hGRH hL
  have hex : ∃ q : ℕ, q.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := ⟨p, hp, hreject⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hreject⟩)).trans hbound, fun q hq hreject ↦
      Nat.find_min' hex ⟨hq, hreject⟩⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
