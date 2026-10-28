/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianBudgetBranches

/-! # Generic six-fifths Gaussian index-four witness branch -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At index four, a root above thirteen with the normalized error below eleven
and an incompatible main budget contradicts the actual six-fifths Gaussian comparison.
Normalize the exact conductor coefficient and apply the common width comparison. -/
theorem gaussianBudget_four_index (P s0 : ℝ) {n : ℕ} [NeZero n] (H : Subgroup (ZMod n)ˣ)
    (hi : H.index = 4) (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n)
    (hs13 : 13 ≤ s0)
    (herr :
      (4 / 3 : ℝ) *
            (21 * Analysis.gaussianMR6FifthsEndpoint / (10 * Analysis.gaussianMRRefinedWidth * s0) +
              1839 * Analysis.gaussianMR6FifthsEndpoint / (1000 * s0 ^ 2)) +
          13 / 3 +
          LLS.PaperStatements.gaussianPrefixError P n ((s0 ^ 2) ^ 2) <
        11)
    (hnot :
      ¬(Analysis.gaussianMRRefinedTripleD * s0 ^ 2 ≤
          (2 / 3 : ℝ) * Analysis.gaussianMRRefinedConductor * Real.log n +
            Analysis.gaussianMRRefinedTripleBeta * s0 +
            11)) :
    let _L := Real.log n
    let r := s0 ^ 2
    let s := s0
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
          ((H.index - 1 : ℕ) : ℝ) * LLS.PaperStatements.gaussianPrefixError P n x) := by
  intro _L r s h x hcmp
  have hindex : (H.index : ℝ) = 4 := by exact_mod_cast hi
  let I : ℝ :=
    ∫ u in (0 : ℝ)..(6 / 5 : ℝ),
      (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u
  let E : ℝ := Real.exp (1 / 16 : ℝ)
  have hrpos : 0 < r := by
    dsimp only [r]
    exact sq_pos_of_pos (by linarith only [hs13] : (0 : ℝ) < s0)
  have hspos : 0 < s := by
    dsimp only [s]
    exact (by linarith only [hs13] : (0 : ℝ) < s0)
  have hrootSq : s ^ 2 = r := by rfl
  have hsbound : (13 : ℝ) ≤ s := hs13
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
        3 * LLS.PaperStatements.gaussianPrefixError (P) n (r ^ 2) := by
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
        LLS.PaperStatements.gaussianPrefixError (P) n (r ^ 2) <
      11 := by
    exact herr
  exact
    Analysis.gaussianMR_compare_width (m := 4) (t := 3) (s := s) (r := r) (A :=
      LLS.PaperStatements.gaussianPrefixError (P) n (r ^ 2)) (L := (2 / 3 : ℝ) * Real.log n) (I :=
      I) (E := E) (C := LLS.PaperStatements.subgroupConductorLogSum H) (h := h) (M :=
      Analysis.gaussianMRRefinedMass) (Ecap := Analysis.gaussianMR6FifthsEndpoint) (conductor :=
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
        exact hnot hnorm)

/-- An actual finite prefix, cutoff coverage and the two index-four scalar certificates
produce an actual prime rejecting strong MR under the six-fifths cutoff.
Use the generic relative witness consumer to exclude small factors and form subgroup containment. -/
theorem gaussianBudget_four_witness (N : ℕ) (P s0 : ℝ) (hs13 : 13 ≤ s0) {n : ℕ} [NeZero n]
    (hprefix : P ≤ ∑ j ∈ Finset.Ioc 0 N, Analysis.gaussianResolventMangoldtWeight j)
    (hN : (N : ℝ) ≤ (6 / 5 : ℝ) * (s0 ^ 2) ^ 2)
    (herr :
      (4 / 3 : ℝ) *
            (21 * Analysis.gaussianMR6FifthsEndpoint / (10 * Analysis.gaussianMRRefinedWidth * s0) +
              1839 * Analysis.gaussianMR6FifthsEndpoint / (1000 * s0 ^ 2)) +
          13 / 3 +
          LLS.PaperStatements.gaussianPrefixError P n ((s0 ^ 2) ^ 2) <
        11)
    (hnot :
      ¬(Analysis.gaussianMRRefinedTripleD * s0 ^ 2 ≤
          (2 / 3 : ℝ) * Analysis.gaussianMRRefinedConductor * Real.log n +
            Analysis.gaussianMRRefinedTripleBeta * s0 +
            11))
    (ho : Odd n) (hnlarge : 20000 ≤ n) (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (6 / 5 : ℝ) * (s0 ^ 2) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hs : 0 < s0 := by linarith only [hs13]
  have hh : Analysis.gaussianMRRefinedWidth / s0 ≤ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ hs]
    norm_num only [Analysis.gaussianMRRefinedWidth]
    linarith only [hs13]
  have hx : (4 : ℝ) ≤ (s0 ^ 2) ^ 2 := by
    have h2 := (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 13) hs.le).mpr hs13
    nlinarith only [h2, sq_nonneg (s0 ^ 2 - 169)]
  exact
    gaussianRelative_witness ho hnlarge H hHpass hGRH hprefix
      (div_pos (by norm_num only [Analysis.gaussianMRRefinedWidth]) hs) hh hx
      (by norm_num only : (0 : ℝ) ≤ 6 / 5) hN le_rfl
      (gaussianBudget_four_index P s0 H hi hC hs13 herr hnot)

end PseudoPrime.PrimeTestBounds.MillerRabin
