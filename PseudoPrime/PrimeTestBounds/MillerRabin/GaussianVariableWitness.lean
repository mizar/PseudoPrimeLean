/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSurplusWitness

/-! # Index-four Gaussian witness with variable relative width -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an index-four pass-containing subgroup yields a rejecting prime
within the Gaussian cutoff for any positive width coefficient `k` satisfying
the width, prefix, budget, and residual conditions. The general relative
comparison retains the `k`-dependent square-root and inverse-width losses. -/
theorem gaussian_variable_witness_four {n : ℕ} [NeZero n] (hnOdd : Odd n) (hnlarge : 20000 ≤ n)
    (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) {P R r k : ℝ} {N : ℕ}
    (hr : 130 ≤ r) (hk : 0 < k) (hkmax : k ≤ Real.sqrt r / 2)
    (hprefix : P ≤ ∑ j ∈ Finset.Ioc 0 N, Analysis.gaussianResolventMangoldtWeight j)
    (hcut : (N : ℝ) ≤ (21 / 10 : ℝ) * r ^ 2)
    (hbudget :
      (20115621 / 25000000 : ℝ) * Real.log n + R +
          4 * ((81470555 / 100000000 : ℝ) * k + 1 / (10 * k)) * Real.sqrt r ≤
        (10971611 / 5000000 : ℝ) * r)
    (hres :
      4 *
            (21 * (2129 / 2000 : ℝ) / (10 * k * Real.sqrt r) +
              1839 * (2129 / 2000 : ℝ) / (1000 * r)) +
          13 +
          3 * LLS.PaperStatements.gaussianPrefixError P n (r ^ 2) <
        R) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (21 / 10 : ℝ) * r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let s := Real.sqrt r
  let h := k / s
  have hrpos : 0 < r := by linarith only [hr]
  have hspos : 0 < s := Real.sqrt_pos.2 hrpos
  have hs2 : r = s ^ 2 := (Real.sq_sqrt hrpos.le).symm
  have hh : 0 < h := div_pos hk hspos
  have hh1 : h ≤ 1 / 2 := by
    apply (div_le_iff₀ hspos).mpr
    linarith only [hkmax]
  have hx : (4 : ℝ) ≤ r ^ 2 := by nlinarith only [hr]
  apply
    gaussianRelative_witness hnOdd hnlarge H hHpass hGRH hprefix hh hh1 hx
      (by norm_num only : (0 : ℝ) ≤ 21 / 10) hcut (le_refl _)
  intro hcmp
  have hindex : (H.index : ℝ) = 4 := by exact_mod_cast hi
  rw [Real.sqrt_sq hrpos.le] at hcmp
  have hcmp' :
    (4 * (1 - h) *
            (∫ u in (0 : ℝ)..(21 / 10 : ℝ),
              (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
          Real.exp (1 / 16 : ℝ)) *
        (1 * r) ≤
      gaussianMRRefinedConductor * LLS.PaperStatements.subgroupConductorLogSum H +
        4 * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / (1 * r)) * Real.exp (1 / 16 : ℝ)) +
        13 +
        3 * LLS.PaperStatements.gaussianPrefixError P n (r ^ 2) := by
    simpa only [hindex, hi, Nat.reduceSub, Nat.cast_ofNat, one_mul] using hcmp
  have hscalar :=
    LLS.gaussianRelativeFour_scalar hspos hs2 (by norm_num only : (0 : ℝ) < 1) hk
      (show h = k / s from rfl) hh1 LLS.PaperStatements.gaussianGamma_cutoff_gt_target.le
      Analysis.gaussian_endpoint_exp_le hC (by norm_num only [gaussianMRRefinedConductor]) hcmp'
  norm_num only [one_mul, gaussianMRRefinedConductor] at hscalar
  dsimp only [s] at hscalar
  ring_nf at hscalar hbudget hres
  linarith only [hscalar, hbudget, hres]

/-- Under GRH, the variable-width index-four witness specializes to the
coefficient `7/20`. Its exact square-root loss is `1598411439/700000000`;
the inverse-width residual remains explicit for the 5250-scale certificate. -/
theorem gaussian_seven_twentieths_witness {n : ℕ} [NeZero n] (hnOdd : Odd n) (hnlarge : 20000 ≤ n)
    (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) {P R r : ℝ} {N : ℕ}
    (hr : 130 ≤ r) (hprefix : P ≤ ∑ j ∈ Finset.Ioc 0 N, Analysis.gaussianResolventMangoldtWeight j)
    (hcut : (N : ℝ) ≤ (21 / 10 : ℝ) * r ^ 2)
    (hbudget :
      (20115621 / 25000000 : ℝ) * Real.log n + R + (1598411439 / 700000000 : ℝ) * Real.sqrt r ≤
        (10971611 / 5000000 : ℝ) * r)
    (hres :
      4 *
            (21 * (2129 / 2000 : ℝ) / (10 * (7 / 20 : ℝ) * Real.sqrt r) +
              1839 * (2129 / 2000 : ℝ) / (1000 * r)) +
          13 +
          3 * LLS.PaperStatements.gaussianPrefixError P n (r ^ 2) <
        R) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (21 / 10 : ℝ) * r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hs : (10 : ℝ) ≤ Real.sqrt r := by
    apply (Real.le_sqrt (by norm_num only) (by linarith only [hr])).mpr
    norm_num only
    linarith only [hr]
  apply
    gaussian_variable_witness_four hnOdd hnlarge H hi hHpass hGRH hC hr
      (by norm_num only : (0 : ℝ) < 7 / 20) (k := 7 / 20) (by linarith only [hs]) hprefix hcut
  · norm_num only at hbudget ⊢
    exact hbudget
  · exact hres

end PseudoPrime.PrimeTestBounds.MillerRabin
