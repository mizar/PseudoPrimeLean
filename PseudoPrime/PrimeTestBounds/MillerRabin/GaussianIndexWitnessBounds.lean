/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.ResidueSubgroup
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMRNumerics
public import PseudoPrime.LLS.GaussianWidthComparison
public import PseudoPrime.LLS.PaperStatements.GammaNonOneRefinedBudgets
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMR6FifthsNumerics
public import PseudoPrime.LLS.PaperStatements.RelativeGaussianSubgroupComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalWitnessBounds

/-! # Gaussian MR witnesses by subgroup index -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a subgroup containing every strong-MR pass yields a prime
witness below the 6/5 Gaussian bound when its index is at least 10^9. -/
theorem gaussian6_5_index_four_contradiction {n : ℕ} [NeZero n] (H : Subgroup (ZMod n)ˣ)
    (hi : H.index = 4) (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n)
    (hL : 500 ≤ Real.log n) :
    let L := Real.log n
    let r := gaussian6FifthsRadius L
    let s := gaussian6FifthsRoot L
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
          ((H.index - 1 : ℕ) : ℝ) * LLS.PaperStatements.gaussianAmbientError n x) := by
  intro L r s h x hcmp
  have hindex : (H.index : ℝ) = 4 := by exact_mod_cast hi
  let I : ℝ :=
    ∫ u in (0 : ℝ)..(6 / 5 : ℝ),
      (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u
  let E : ℝ := Real.exp (1 / 16 : ℝ)
  have hrpos : 0 < r := by
    dsimp only [r]
    exact sq_pos_of_pos (gaussian6FifthsRoot_pos hL)
  have hspos : 0 < s := by
    dsimp only [s]
    exact gaussian6FifthsRoot_pos hL
  have hrootSq : s ^ 2 = r := by dsimp only [s, r, gaussian6FifthsRadius]
  have hrbound : 625 / 2 ≤ r := by
    have hr := gaussian6FifthsRadius_lower hL
    nlinarith only [hr, hL]
  have hsbound : 17 ≤ s := by nlinarith only [hrootSq, hrbound, hspos]
  have hsqrtx : Real.sqrt x = r := by
    dsimp only [x]
    exact Real.sqrt_sq hrpos.le
  rw [hsqrtx] at hcmp
  have hI : gaussian6FifthsMass ≤ I := by
    dsimp only [I, gaussian6FifthsMass]
    exact LLS.PaperStatements.gaussianGamma_cutoff_sixFifths_gt_target.le
  have hE : E ≤ gaussian6FifthsEndpoint := by
    dsimp only [E, gaussian6FifthsEndpoint]
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
        3 * LLS.PaperStatements.gaussianAmbientError n (r ^ 2) := by
    dsimp only [x] at hcmp
    simpa only [hindex, hi, Nat.cast_ofNat, Nat.reduceSub] using hcmp
  have hA : LLS.PaperStatements.gaussianAmbientError n (r ^ 2) ≤ 27 := by
    dsimp only [r, L]
    exact gaussian6Fifths_ambient_error_le hL (le_refl (Real.log n))
  have hCscaled : LLS.PaperStatements.subgroupConductorLogSum H / 3 ≤ (2 / 3 : ℝ) * Real.log n := by
    apply (div_le_iff₀ (by norm_num only : (0 : ℝ) < 3)).2
    nlinarith only [hC]
  have herror :
    (4 / 3 : ℝ) *
          (63 * gaussian6FifthsEndpoint / (10 * s) + 1839 * gaussian6FifthsEndpoint / (1000 * r)) +
        13 / 3 +
        LLS.PaperStatements.gaussianAmbientError n (r ^ 2) <
      33 := by
    have hterm1 :
      63 * gaussian6FifthsEndpoint / (10 * s) ≤ 63 * gaussian6FifthsEndpoint / (10 * 17) := by
      apply div_le_div_of_nonneg_left
      · norm_num only [gaussian6FifthsEndpoint]
      · norm_num only
      · nlinarith only [hsbound]
    have hterm2 :
      1839 * gaussian6FifthsEndpoint / (1000 * r) ≤
        1839 * gaussian6FifthsEndpoint / (1000 * (625 / 2)) := by
      apply div_le_div_of_nonneg_left
      · norm_num only [gaussian6FifthsEndpoint]
      · norm_num only
      · nlinarith only [hrbound]
    rw [gaussian6FifthsEndpoint] at hterm1 hterm2 ⊢
    norm_num only at hterm1 hterm2
    nlinarith only [hterm1, hterm2, hA]
  exact
    LLS.gaussian_compare_width_third (m := 4) (t := 3) (s := s) (r := r) (A :=
      LLS.PaperStatements.gaussianAmbientError n (r ^ 2)) (L := (2 / 3 : ℝ) * Real.log n) (I := I)
      (E := E) (C := LLS.PaperStatements.subgroupConductorLogSum H) (h := h) (M :=
      gaussian6FifthsMass) (Ecap := gaussian6FifthsEndpoint) (conductor := (161 / 400 : ℝ)) (D :=
      (4 * gaussian6FifthsMass - gaussian6FifthsEndpoint) / 3) (beta :=
      (4 / 3 : ℝ) * (gaussian6FifthsMass / 3 + 3 / 10)) (by norm_num only : (4 : ℝ) ≤ 4)
      (by norm_num only : (3 : ℝ) = (4 : ℝ) - 1) hspos hrootSq.symm hh hh1 hI hE hCscaled
      (by norm_num only : (0 : ℝ) ≤ 161 / 400) le_rfl le_rfl hcmp'
      (by
        intro hbudget
        have hnorm' :
          ((4 * gaussian6FifthsMass - gaussian6FifthsEndpoint) / 3) * r ≤
            (161 / 600 : ℝ) * Real.log n + (4 / 3 : ℝ) * (gaussian6FifthsMass / 3 + 3 / 10) * s +
              33 := by
          dsimp only [gaussian6FifthsMass, gaussian6FifthsEndpoint] at hbudget herror ⊢
          nlinarith only [hbudget, herror]
        exact gaussian6Fifths_triple_comparison_impossible hL hnorm')

/-- The prefix-adjusted relative Gaussian comparison is impossible for an
index-four subgroup at the constant-18 radius from logarithmic scale 300. -/
theorem gaussian18_indexFour_relative_false {n : ℕ} [NeZero n] (H : Subgroup (ZMod n)ˣ)
    (hi : H.index = 4) (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n)
    (hL : 300 ≤ Real.log n) :
    let L := Real.log n
    let r := gaussian18Radius L
    let s := gaussian18Root L
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
          ((H.index - 1 : ℕ) : ℝ) * LLS.PaperStatements.gaussianAmbientErrorPrefix n x) := by
  intro L r s h x hcmp
  have hindex : (H.index : ℝ) = 4 := by exact_mod_cast hi
  let I : ℝ :=
    ∫ u in (0 : ℝ)..(6 / 5 : ℝ),
      (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u
  let E : ℝ := Real.exp (1 / 16 : ℝ)
  have hrpos : 0 < r := by
    dsimp only [r]
    exact sq_pos_of_pos (gaussian18Root_pos hL)
  have hspos : 0 < s := by
    dsimp only [s]
    exact gaussian18Root_pos hL
  have hrootSq : s ^ 2 = r := by dsimp only [s, r, gaussian18Radius]
  have hrbound : 455 / 2 ≤ r := by
    dsimp only [r]
    exact gaussian18Radius_lower_455_over_2 hL
  have hsbound : 15 ≤ s := by
    dsimp only [s]
    exact gaussian18Root_lower_15 hL
  have hsqrtx : Real.sqrt x = r := by
    dsimp only [x]
    exact Real.sqrt_sq hrpos.le
  rw [hsqrtx] at hcmp
  have hI : gaussian6FifthsMass ≤ I := by
    dsimp only [I, gaussian6FifthsMass]
    exact LLS.PaperStatements.gaussianGamma_cutoff_sixFifths_gt_target.le
  have hE : E ≤ gaussian6FifthsEndpoint := by
    dsimp only [E, gaussian6FifthsEndpoint]
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
        3 * LLS.PaperStatements.gaussianAmbientErrorPrefix n (r ^ 2) := by
    dsimp only [x] at hcmp
    simpa only [hindex, hi, Nat.cast_ofNat, Nat.reduceSub] using hcmp
  have hA : LLS.PaperStatements.gaussianAmbientErrorPrefix n (r ^ 2) ≤ 27 - 484381 / 50000 := by
    dsimp only [r, L]
    exact gaussian18_ambient_error_prefix_le hL (le_rfl)
  have hCscaled : LLS.PaperStatements.subgroupConductorLogSum H / 3 ≤ (2 / 3 : ℝ) * Real.log n := by
    apply (div_le_iff₀ (by norm_num only : (0 : ℝ) < 3)).2
    nlinarith only [hC]
  have herror :
    (4 / 3 : ℝ) *
          (63 * gaussian6FifthsEndpoint / (10 * s) + 1839 * gaussian6FifthsEndpoint / (1000 * r)) +
        13 / 3 +
        LLS.PaperStatements.gaussianAmbientErrorPrefix n (r ^ 2) <
      23 := by
    have hterm1 :
      63 * gaussian6FifthsEndpoint / (10 * s) ≤ 63 * gaussian6FifthsEndpoint / (10 * 15) := by
      apply div_le_div_of_nonneg_left
      · norm_num only [gaussian6FifthsEndpoint]
      · norm_num only
      · nlinarith only [hsbound]
    have hterm2 :
      1839 * gaussian6FifthsEndpoint / (1000 * r) ≤
        1839 * gaussian6FifthsEndpoint / (1000 * (455 / 2)) := by
      apply div_le_div_of_nonneg_left
      · norm_num only [gaussian6FifthsEndpoint]
      · norm_num only
      · nlinarith only [hrbound]
    rw [gaussian6FifthsEndpoint] at hterm1 hterm2 ⊢
    norm_num only at hterm1 hterm2
    nlinarith only [hterm1, hterm2, hA]
  exact
    LLS.gaussian_compare_width_third (m := 4) (t := 3) (s := s) (r := r) (A :=
      LLS.PaperStatements.gaussianAmbientErrorPrefix n (r ^ 2)) (L := (2 / 3 : ℝ) * Real.log n)
      (I := I) (E := E) (C := LLS.PaperStatements.subgroupConductorLogSum H) (h := h) (M :=
      gaussian6FifthsMass) (Ecap := gaussian6FifthsEndpoint) (conductor := (161 / 400 : ℝ)) (D :=
      (4 * gaussian6FifthsMass - gaussian6FifthsEndpoint) / 3) (beta :=
      (4 / 3 : ℝ) * (gaussian6FifthsMass / 3 + 3 / 10)) (by norm_num only : (4 : ℝ) ≤ 4)
      (by norm_num only : (3 : ℝ) = (4 : ℝ) - 1) hspos hrootSq.symm hh hh1 hI hE hCscaled
      (by norm_num only : (0 : ℝ) ≤ 161 / 400) le_rfl le_rfl hcmp'
      (by
        intro hbudget
        have hnorm :
          ((4 * gaussian6FifthsMass - gaussian6FifthsEndpoint) / 3) * r ≤
            (161 / 600 : ℝ) * Real.log n + (4 / 3 : ℝ) * (gaussian6FifthsMass / 3 + 3 / 10) * s +
              23 := by
          dsimp only [gaussian6FifthsMass, gaussian6FifthsEndpoint] at hbudget herror ⊢
          nlinarith only [hbudget, herror]
        exact gaussian18_triple_comparison_impossible hL hnorm)

/-- An index-four subgroup with the three-character conductor cost yields a
prime witness below the 6/5 Gaussian bound from logarithmic scale 500. -/
theorem gaussian6_5_primeWitness_index_four_GRH {n : ℕ} [NeZero n] (hnOdd : Odd n)
    (hnlarge : 20000 ≤ n) (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) (hL : 500 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gaussian6FifthsBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_contra hnone
  let r := gaussian6FifthsRadius (Real.log n)
  let x := r ^ 2
  have hcut : (6 / 5 : ℝ) * x = gaussian6FifthsBound (Real.log n) := by
    dsimp only [x, gaussian6FifthsBound, gaussian6FifthsRadius, r]
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
      p.Prime → ¬p ∣ n → (p : ℝ) ≤ (6 / 5 : ℝ) * x → NumberTheory.residueInSubgroup n H p := by
    intro p hp hpdvd hpbound
    obtain ⟨u, huH, hu⟩ := hHpass (p : ZMod n) (hpass p hp hpbound)
    exact ⟨u, huH, hu⟩
  have hrootSq : (gaussian6FifthsRoot (Real.log n)) ^ 2 = r := by
    dsimp only [r, gaussian6FifthsRadius]
  have hrbound : 625 / 2 ≤ r := by
    have hrad := gaussian6FifthsRadius_lower hL
    dsimp only [r]
    nlinarith only [hrad, hL]
  have hspos : 0 < gaussian6FifthsRoot (Real.log n) := gaussian6FifthsRoot_pos hL
  have hsbound : 17 ≤ gaussian6FifthsRoot (Real.log n) := by
    nlinarith only [hrootSq, hrbound, hspos]
  have hwidth : 0 < 1 / (3 * gaussian6FifthsRoot (Real.log n)) := by positivity
  have hwidth1 : 1 / (3 * gaussian6FifthsRoot (Real.log n)) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num only)
    nlinarith only [hsbound]
  have hx : 4 ≤ x := by
    dsimp only [x]
    nlinarith only [hrbound]
  have hcmp :=
    LLS.PaperStatements.gaussian_noSmallPrimes_inequality_relative hnlarge H hGRH hwidth hwidth1 hx
      (by norm_num only : (0 : ℝ) ≤ 6 / 5) hdiv hsmall
  exact gaussian6_5_index_four_contradiction H hi hC hL hcmp

/-- An index-four subgroup with conductor cost `2L` yields a prime witness
below the prefix-improved constant-18 Gaussian bound from logarithmic scale 300. -/
theorem exists_prime_gaussian18_indexFour_GRH {n : ℕ} [NeZero n] (hnOdd : Odd n)
    (hnlarge : 20000 ≤ n) (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) (hL : 300 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gaussian18Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_contra hnone
  let r := gaussian18Radius (Real.log n)
  let x := r ^ 2
  have hcut : (6 / 5 : ℝ) * x = gaussian18Bound (Real.log n) := by
    dsimp only [x, gaussian18Bound, gaussian18Radius, r]
  have hX : 50000 ≤ (6 / 5 : ℝ) * x := by
    rw [hcut]
    exact (gaussian18Bound_gt_prefix hL).le
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
      p.Prime → ¬p ∣ n → (p : ℝ) ≤ (6 / 5 : ℝ) * x → NumberTheory.residueInSubgroup n H p := by
    intro p hp hpdvd hpbound
    obtain ⟨u, huH, hu⟩ := hHpass (p : ZMod n) (hpass p hp hpbound)
    exact ⟨u, huH, hu⟩
  have hrootSq : (gaussian18Root (Real.log n)) ^ 2 = r := by dsimp only [r, gaussian18Radius]
  have hrbound : 455 / 2 ≤ r := by
    dsimp only [r]
    exact gaussian18Radius_lower_455_over_2 hL
  have hspos : 0 < gaussian18Root (Real.log n) := gaussian18Root_pos hL
  have hsbound : 15 ≤ gaussian18Root (Real.log n) := gaussian18Root_lower_15 hL
  have hwidth : 0 < 1 / (3 * gaussian18Root (Real.log n)) := by positivity
  have hwidth1 : 1 / (3 * gaussian18Root (Real.log n)) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num only)
    nlinarith only [hsbound]
  have hx : 4 ≤ x := by
    dsimp only [x]
    nlinarith only [hrbound]
  have hcmp :=
    LLS.PaperStatements.gaussian_noSmall_relative50000_GRH hnlarge H hGRH hwidth hwidth1 hx
      (by norm_num only : (0 : ℝ) ≤ 6 / 5) hX hdiv hsmall
  exact gaussian18_indexFour_relative_false H hi hC hL hcmp

/-- Under GRH, a subgroup containing every strong-MR pass yields a prime
witness below the 6/5 Gaussian bound when its index is at least 10^9. -/
theorem gaussian6_5_primeWitness_highIndex_GRH {n : ℕ} [NeZero n] (hnOdd : Odd n)
    (hnlarge : 20000 ≤ n) (H : Subgroup (ZMod n)ˣ) (hi : gaussian6FifthsIndex ≤ (H.index : ℝ))
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 500 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gaussian6FifthsBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_contra hnone
  let L := Real.log n
  let r := gaussian6FifthsRadius L
  let s := gaussian6FifthsRoot L
  let x := r ^ 2
  let h := 1 / (3 * s)
  let m : ℝ := H.index
  let t : ℝ := m - 1
  let I : ℝ :=
    ∫ u in (0 : ℝ)..(6 / 5 : ℝ),
      (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u
  let E : ℝ := Real.exp (1 / 16 : ℝ)
  let C : ℝ := LLS.PaperStatements.subgroupConductorLogSum H
  let A : ℝ := LLS.PaperStatements.gaussianAmbientError n x
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 20000) hnlarge
  have hrootSq : s ^ 2 = r := by dsimp only [s, r, gaussian6FifthsRadius]
  have hrbound : 625 / 2 ≤ r := by
    have hrad := gaussian6FifthsRadius_lower hL
    dsimp only [r, L]
    nlinarith only [hrad, hL]
  have hspos : 0 < s := by
    dsimp only [s, L]
    exact gaussian6FifthsRoot_pos hL
  have hs17 : 17 ≤ s := by nlinarith only [hrootSq, hrbound, hspos]
  have hh : h = 1 / (3 * s) := by rfl
  have hh1 : h ≤ 1 / 2 := by
    rw [hh]
    apply one_div_le_one_div_of_le (by norm_num only)
    nlinarith only [hs17]
  have hrpos : 0 < r := by
    have hscaled := mul_pos (by norm_num only : (0 : ℝ) < 5 / 8) (by linarith only [hL] : 0 < L)
    exact lt_of_lt_of_le hscaled (gaussian6FifthsRadius_lower hL)
  have hsqrtx : Real.sqrt x = r := by
    dsimp only [x]
    exact Real.sqrt_sq hrpos.le
  have hx : 4 ≤ x := by
    dsimp only [x]
    nlinarith only [hrbound]
  have hcut : (6 / 5 : ℝ) * x = gaussian6FifthsBound (Real.log n) := by
    dsimp only [gaussian6FifthsBound, gaussian6FifthsRadius, r, L, x]
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
      p.Prime → ¬p ∣ n → (p : ℝ) ≤ (6 / 5 : ℝ) * x → NumberTheory.residueInSubgroup n H p := by
    intro p hp hpdvd hpbound
    obtain ⟨u, huH, hu⟩ := hHpass (p : ZMod n) (hpass p hp hpbound)
    exact ⟨u, huH, hu⟩
  have hwidth : 0 < h := by
    dsimp only [h]
    exact one_div_pos.mpr (mul_pos (by norm_num only) hspos)
  have hcmp :=
    LLS.PaperStatements.gaussian_noSmallPrimes_inequality_relative hnlarge H hGRH hwidth hh1 hx
      (by norm_num only : (0 : ℝ) ≤ 6 / 5) hdiv hsmall
  have hcastIndex : ((H.index - 1 : ℕ) : ℝ) = (H.index : ℝ) - 1 := by
    have hidxReal : (1 : ℝ) ≤ (H.index : ℝ) := by
      have hK : (1 : ℝ) ≤ gaussian6FifthsIndex := by norm_num only [gaussian6FifthsIndex]
      exact hK.trans hi
    have hidxNat : 1 ≤ H.index := by exact_mod_cast hidxReal
    rw [Nat.cast_sub hidxNat, Nat.cast_one]
  rw [hsqrtx, hcastIndex] at hcmp
  have hI : gaussian6FifthsMass ≤ I := by
    dsimp only [I, gaussian6FifthsMass]
    exact LLS.PaperStatements.gaussianGamma_cutoff_sixFifths_gt_target.le
  have hE : E ≤ gaussian6FifthsEndpoint := by
    dsimp only [E, gaussian6FifthsEndpoint]
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
  have hA : A ≤ 27 := by
    dsimp only [A, x, r, L]
    exact gaussian6Fifths_ambient_error_le hL (le_refl (Real.log n))
  have hroot :
    gaussian6FifthsD * r = gaussian6FifthsConductor * L + gaussian6FifthsBeta * s + 29 := by
    dsimp only [r, s, L]
    exact gaussian6FifthsRadius_equation hL
  have hcmp' :
    (m * (1 - h) * I - E) * r ≤
      gaussian6FifthsConductor * C + m * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * E) +
        13 +
        t * A := by
    simpa only [m, t, I, E, C, A, gaussian6FifthsConductor] using hcmp
  exact
    gaussian6Fifths_relative_comparison_impossible (m := m) (t := t) (s := s) (r := r) (A := A)
      (L := L) (I := I) (E := E) (C := C) (h := h) hi rfl hspos hs17 rfl hrbound hh hh1 hI hE hC hA
      hcmp' hroot

/-- Under GRH, a subgroup containing every strong-MR pass yields a prime
witness below the signed constant-6 Gaussian bound from logarithmic scale 300. -/
theorem exists_prime_gaussian6_largeIndex_GRH {n : ℕ} [NeZero n] (hnOdd : Odd n)
    (hnlarge : 20000 ≤ n) (H : Subgroup (ZMod n)ˣ) (hi : gaussian6FifthsIndex ≤ (H.index : ℝ))
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 300 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gaussian6Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_contra hnone
  let L := Real.log n
  let r := gaussian6Radius L
  let s := gaussian6Root L
  let x := r ^ 2
  let h := 1 / (3 * s)
  let m : ℝ := H.index
  let t : ℝ := m - 1
  let I : ℝ :=
    ∫ u in (0 : ℝ)..(6 / 5 : ℝ),
      (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u
  let E : ℝ := Real.exp (1 / 16 : ℝ)
  let C : ℝ := LLS.PaperStatements.subgroupConductorLogSum H
  let A : ℝ := LLS.PaperStatements.gaussianAmbientErrorPrefixSigned n x
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 20000) hnlarge
  have hrootSq : s ^ 2 = r := by dsimp only [s, r, gaussian6Radius]
  have hrbound : 415 / 2 ≤ r := by
    dsimp only [r, L]
    have hr := gaussian6Radius_lower hL
    nlinarith only [hL, hr]
  have hspos : 0 < s := by
    dsimp only [s, L]
    exact gaussian6Root_pos hL
  have hs14 : 14 ≤ s := by
    dsimp only [s, L]
    exact gaussian6Root_lower_14 hL
  have hh : h = 1 / (3 * s) := by rfl
  have hh1 : h ≤ 1 / 2 := by
    rw [hh]
    apply one_div_le_one_div_of_le (by norm_num only)
    nlinarith only [hs14]
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 415 / 2) hrbound
  have hsqrtx : Real.sqrt x = r := by
    dsimp only [x]
    exact Real.sqrt_sq hrpos.le
  have hx : 4 ≤ x := by
    dsimp only [x]
    nlinarith only [hrbound]
  have hcut : (6 / 5 : ℝ) * x = gaussian6Bound (Real.log n) := by
    dsimp only [gaussian6Bound, gaussian6Radius, r, L, x]
  have hX : 50000 ≤ (6 / 5 : ℝ) * x := by
    rw [hcut]
    exact (gaussian6Bound_gt_prefix hL).le
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
      p.Prime → ¬p ∣ n → (p : ℝ) ≤ (6 / 5 : ℝ) * x → NumberTheory.residueInSubgroup n H p := by
    intro p hp hpdvd hpbound
    obtain ⟨u, huH, hu⟩ := hHpass (p : ZMod n) (hpass p hp hpbound)
    exact ⟨u, huH, hu⟩
  have hwidth : 0 < h := one_div_pos.mpr (mul_pos (by norm_num only) hspos)
  have hcmp :=
    LLS.PaperStatements.gaussian_noSmall_relative50000_signed_GRH hnlarge H hGRH hwidth hh1 hx
      (by norm_num only : (0 : ℝ) ≤ 6 / 5) hX hdiv hsmall
  have hcastIndex : ((H.index - 1 : ℕ) : ℝ) = (H.index : ℝ) - 1 := by
    have hidxReal : (1 : ℝ) ≤ (H.index : ℝ) := by
      have hK : (1 : ℝ) ≤ gaussian6FifthsIndex := by norm_num only [gaussian6FifthsIndex]
      exact hK.trans hi
    have hidxNat : 1 ≤ H.index := by exact_mod_cast hidxReal
    rw [Nat.cast_sub hidxNat, Nat.cast_one]
  rw [hsqrtx, hcastIndex] at hcmp
  have hI : gaussian6FifthsMass ≤ I := by
    dsimp only [I, gaussian6FifthsMass]
    exact LLS.PaperStatements.gaussianGamma_cutoff_sixFifths_gt_target.le
  have hE : E ≤ gaussian6FifthsEndpoint := by
    dsimp only [E, gaussian6FifthsEndpoint]
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
  have hA : A ≤ 27 / 5 := by
    dsimp only [A, x, r, L]
    exact gaussian6_ambient_error_prefix_signed_le hL le_rfl
  have hroot :
    gaussian6FifthsD * r = gaussian6FifthsConductor * L + gaussian6FifthsBeta * s + 6 := by
    dsimp only [r, s, L]
    exact gaussian6Radius_equation hL
  have hcmp' :
    (m * (1 - h) * I - E) * r ≤
      gaussian6FifthsConductor * C + m * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * E) +
        13 +
        t * A := by
    simpa only [m, t, I, E, C, A, gaussian6FifthsConductor] using hcmp
  have hcoeff := gaussian6Fifths_index_coefficients hi
  have hD : gaussian6FifthsD ≤ (m * gaussian6FifthsMass - gaussian6FifthsEndpoint) / t := by
    simpa only [t] using hcoeff.1
  have hbeta : (m / t) * (gaussian6FifthsMass / 3 + 3 / 10) ≤ gaussian6FifthsBeta := by
    simpa only [t] using hcoeff.2.2
  have hfinish :
    gaussian6FifthsD * r ≤
        gaussian6FifthsConductor * L + gaussian6FifthsBeta * s +
          (m / t) *
            (63 * gaussian6FifthsEndpoint / (10 * s) +
              1839 * gaussian6FifthsEndpoint / (1000 * r)) +
          13 / t +
          A →
      False := by
    intro hbudget
    have ht : t = m - 1 := by rfl
    have hgamma := hcoeff.2.1
    exact
      gaussian6_large_index_comparison_impossible hi hs14 hrbound hgamma hA hroot
        (by simpa only [ht] using hbudget)
  exact
    LLS.gaussian_compare_width_third (m := m) (t := t) (s := s) (r := r) (A := A) (L := L) (I := I)
      (E := E) (C := C) (h := h) (M := gaussian6FifthsMass) (Ecap := gaussian6FifthsEndpoint)
      (conductor := gaussian6FifthsConductor) (D := gaussian6FifthsD) (beta := gaussian6FifthsBeta)
      (by
        have hi' : (1000000000 : ℝ) ≤ m := by simpa only [m, gaussian6FifthsIndex] using hi
        linarith only [hi'])
      rfl hspos rfl hh hh1 hI hE hC (by norm_num only [gaussian6FifthsConductor]) hD hbeta hcmp'
      hfinish

/-- The constant-6 witness theorem also implies the older constant-18 bound. -/
theorem exists_prime_gaussian18_largeIndex_GRH {n : ℕ} [NeZero n] (hnOdd : Odd n)
    (hnlarge : 20000 ≤ n) (H : Subgroup (ZMod n)ˣ) (hi : gaussian6FifthsIndex ≤ (H.index : ℝ))
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 300 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gaussian18Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hpbound, hfail⟩ :=
    exists_prime_gaussian6_largeIndex_GRH hnOdd hnlarge H hi hHpass hGRH hL
  exact ⟨p, hp, hpbound.trans (gaussian6Bound_le_gaussian18Bound hL), hfail⟩

/-- The Fermat subgroup supplies pass containment in the 6/5 branch. -/
theorem gaussian6_5_prime_largeFermatIndex_GRH {n : ℕ} (hn1 : 1 < n) (hnOdd : Odd n)
    (hi : 1000000000 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 500 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gaussian6FifthsBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  have hExp10 : (11 : ℝ) ≤ Real.exp 10 := by
    have h := Real.add_one_le_exp (10 : ℝ)
    norm_num only at h
    exact h
  have hpow : (11 : ℝ) ^ 5 ≤ Real.exp 10 ^ 50 := by
    calc
      (11 : ℝ) ^ 5 ≤ (11 : ℝ) ^ 50 := pow_le_pow_right₀ (by norm_num only) (by norm_num only)
      _ ≤ Real.exp 10 ^ 50 := pow_le_pow_left₀ (by norm_num only) hExp10 50
  have hexp : Real.exp (500 : ℝ) = Real.exp 10 ^ 50 := by
    rw [show (500 : ℝ) = (50 : ℕ) * 10 by norm_num only]
    exact Real.exp_nat_mul 10 50
  have hExp500 : (20000 : ℝ) < Real.exp (500 : ℝ) := by
    rw [hexp]
    exact lt_of_lt_of_le (by norm_num only) hpow
  have hlog20000 : Real.log (20000 : ℝ) < 500 :=
    (Real.log_lt_iff_lt_exp (by norm_num only)).2 hExp500
  have hnlarge : 20000 ≤ n := by
    by_contra hnot
    have hnlt : n < 20000 := Nat.lt_of_not_ge hnot
    have hloglt : Real.log (n : ℝ) < Real.log (20000 : ℝ) :=
      Real.log_lt_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))) (Nat.cast_lt.mpr hnlt)
    exact (not_lt_of_ge hL) (hloglt.trans hlog20000)
  let H := PrimeTest.fermatSubgroup n
  have hiR : gaussian6FifthsIndex ≤ (H.index : ℝ) := by
    norm_num only [gaussian6FifthsIndex]
    exact_mod_cast hi
  have hHpass :
    ∀ z : ZMod n,
      PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z := by
    intro z hz
    obtain ⟨u, hu, hz⟩ := PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn1 hnOdd hz
    exact ⟨u, hu, hz⟩
  exact gaussian6_5_primeWitness_highIndex_GRH hnOdd hnlarge H hiR hHpass hGRH hL

/-- The Fermat subgroup supplies pass containment in the constant-6 branch. -/
theorem exists_prime_gaussian6_largeFermat_GRH {n : ℕ} (hn1 : 1 < n) (hnOdd : Odd n)
    (hi : 1000000000 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 300 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gaussian6Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  have hExp10 : (11 : ℝ) ≤ Real.exp 10 := by
    have h := Real.add_one_le_exp (10 : ℝ)
    norm_num only at h
    exact h
  have hpow : (11 : ℝ) ^ 5 ≤ Real.exp 10 ^ 30 := by
    calc
      (11 : ℝ) ^ 5 ≤ (11 : ℝ) ^ 30 := pow_le_pow_right₀ (by norm_num only) (by norm_num only)
      _ ≤ Real.exp 10 ^ 30 := pow_le_pow_left₀ (by norm_num only) hExp10 30
  have hexp : Real.exp (300 : ℝ) = Real.exp 10 ^ 30 := by
    rw [show (300 : ℝ) = (30 : ℕ) * 10 by norm_num only]
    exact Real.exp_nat_mul 10 30
  have hExp300 : (20000 : ℝ) < Real.exp (300 : ℝ) := by
    rw [hexp]
    exact lt_of_lt_of_le (by norm_num only) hpow
  have hlog20000 : Real.log (20000 : ℝ) < 300 :=
    (Real.log_lt_iff_lt_exp (by norm_num only)).2 hExp300
  have hnlarge : 20000 ≤ n := by
    by_contra hnot
    have hnlt : n < 20000 := Nat.lt_of_not_ge hnot
    have hloglt : Real.log (n : ℝ) < Real.log (20000 : ℝ) :=
      Real.log_lt_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))) (Nat.cast_lt.mpr hnlt)
    exact (not_lt_of_ge hL) (hloglt.trans hlog20000)
  let H := PrimeTest.fermatSubgroup n
  have hiR : gaussian6FifthsIndex ≤ (H.index : ℝ) := by
    norm_num only [gaussian6FifthsIndex]
    exact_mod_cast hi
  have hHpass :
    ∀ z : ZMod n,
      PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z := by
    intro z hz
    obtain ⟨u, hu, hz⟩ := PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn1 hnOdd hz
    exact ⟨u, hu, hz⟩
  exact exists_prime_gaussian6_largeIndex_GRH hnOdd hnlarge H hiR hHpass hGRH hL

/-- The constant-6 Fermat-index theorem implies the older constant-18 bound. -/
theorem exists_prime_gaussian18_largeFermat_GRH {n : ℕ} (hn1 : 1 < n) (hnOdd : Odd n)
    (hi : 1000000000 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 300 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gaussian18Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hpbound, hfail⟩ := exists_prime_gaussian6_largeFermat_GRH hn1 hnOdd hi hGRH hL
  exact ⟨p, hp, hpbound.trans (gaussian6Bound_le_gaussian18Bound hL), hfail⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
