/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianRelativeHighNumerics
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianRelativeTripleBounds

/-! # Radius-based relative Gaussian witness budget -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The actual index-four Gaussian scalar comparison contradicts a strict radius gap
when the radius, fourth root and prefix error satisfy the stated bounds. The explicit
residual is less than 38; no profile-specific entrance is used. -/
theorem gaussianRadius_scalar_false {L r s A : ℝ} (hr : 500 ≤ r) (hs : 10 ≤ s)
    (hA : A ≤ (12871 / 1000 : ℝ) - 2 * (489311 / 100000) + 4 + 273 / 1000)
    (hgap :
      2 * (20115621 / 50000000 : ℝ) * L + (28794111 / 12500000 : ℝ) * s + 38 <
        (10971611 / 5000000 : ℝ) * r)
    (hcmp :
      (10971611 / 5000000 : ℝ) * r ≤
        2 * (20115621 / 50000000 : ℝ) * L + (28794111 / 12500000 : ℝ) * s +
          4 *
            (21 * (2129 / 2000 : ℝ) / (10 * (2 / 5 : ℝ) * s) +
              1839 * (2129 / 2000 : ℝ) / (1000 * r)) +
          13 +
          3 * A) :
    False := by
  have hspos : 0 < s := by linarith only [hs]
  have hrpos : 0 < r := by linarith only [hr]
  have hleft : 21 * (2129 / 2000 : ℝ) / (10 * (2 / 5 : ℝ) * s) ≤ 21 * (2129 / 2000 : ℝ) / 40 := by
    apply (div_le_iff₀ (mul_pos (by norm_num only) hspos)).mpr
    nlinarith only [hs]
  have hright : 1839 * (2129 / 2000 : ℝ) / (1000 * r) ≤ 1839 * (2129 / 2000 : ℝ) / 500000 := by
    apply (div_le_iff₀ (mul_pos (by norm_num only) hrpos)).mpr
    nlinarith only [hr]
  linarith only [hgap, hcmp, hA, hleft, hright]

/-- Under GRH, an index-four subgroup yields an actual rejecting prime inside the
radius cutoff when the explicit prefix error and scalar gap hold. The existing
50000-prefix and relative Gaussian comparison provide the analytic input. -/
theorem gaussianRadius_witness_four {n : ℕ} [NeZero n] (hnOdd : Odd n) (hnlarge : 20000 ≤ n)
    (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) {r : ℝ} (hr : 500 ≤ r)
    (hA :
      LLS.PaperStatements.gaussianPrefixError (489311 / 100000) n (r ^ 2) ≤
        (12871 / 1000 : ℝ) - 2 * (489311 / 100000) + 4 + 273 / 1000)
    (hgap :
      2 * (20115621 / 50000000 : ℝ) * Real.log n + (28794111 / 12500000 : ℝ) * Real.sqrt r + 38 <
        (10971611 / 5000000 : ℝ) * r) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (21 / 10 : ℝ) * r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let s := Real.sqrt r
  let h := (2 / 5 : ℝ) / s
  have hrpos : 0 < r := by linarith only [hr]
  have hs10 : 10 ≤ s := by
    apply (Real.le_sqrt (by norm_num only) hrpos.le).mpr
    norm_num only
    linarith only [hr]
  have hspos : 0 < s := by linarith only [hs10]
  have hs2 : r = s ^ 2 := (Real.sq_sqrt hrpos.le).symm
  have hh : 0 < h := div_pos (by norm_num only) hspos
  have hh1 : h ≤ 1 / 2 := by
    apply (div_le_iff₀ hspos).mpr
    linarith only [hs10]
  have hx : (4 : ℝ) ≤ r ^ 2 := by nlinarith only [hr]
  have hX : (50000 : ℝ) ≤ (21 / 10 : ℝ) * r ^ 2 := by nlinarith only [hr]
  have hprefix :
    (489311 / 100000 : ℝ) ≤
      ∑ j ∈ Finset.Ioc 0 50000, Analysis.gaussianResolventMangoldtWeight j := by
    simpa only [Nat.floor_ofNat] using
      LLS.gaussian_prefix50000_seeded hGRH.riemann (le_refl (50000 : ℝ))
  apply
    gaussianRelative_witness hnOdd hnlarge H hHpass hGRH hprefix hh hh1 hx
      (by norm_num only : (0 : ℝ) ≤ 21 / 10) hX (le_refl _)
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
        3 * LLS.PaperStatements.gaussianPrefixError (489311 / 100000) n (r ^ 2) := by
    simpa only [hindex, hi, Nat.reduceSub, Nat.cast_ofNat, one_mul] using hcmp
  have hscalar :=
    LLS.gaussianRelativeFour_scalar hspos hs2 (by norm_num only : (0 : ℝ) < 1)
      (by norm_num only : (0 : ℝ) < 2 / 5) (show h = (2 / 5 : ℝ) / s from rfl) hh1
      LLS.PaperStatements.gaussianGamma_cutoff_gt_target.le Analysis.gaussian_endpoint_exp_le hC
      (by norm_num only [gaussianMRRefinedConductor]) hcmp'
  apply gaussianRadius_scalar_false hr hs10 hA hgap
  norm_num only [one_mul, gaussianMRRefinedConductor] at hscalar ⊢
  exact hscalar

/-- Above scale 4000, a radius at least 0.36 times the scale satisfies the explicit
Gaussian prefix-error budget. Bound the pole term and reuse the existing tail estimate. -/
theorem gaussianRadius_error {n : ℕ} {L r : ℝ} (hL : 4000 ≤ L) (hn : Real.log n ≤ L)
    (hr : (36 / 100 : ℝ) * L ≤ r) :
    LLS.PaperStatements.gaussianPrefixError (489311 / 100000) n (r ^ 2) ≤
      (12871 / 1000 : ℝ) - 2 * (489311 / 100000) + 4 + 273 / 1000 := by
  have hr500 : (500 : ℝ) ≤ r := by nlinarith only [hr, hL]
  have hrpos : 0 < r := by linarith only [hr500]
  have hpole : (2129 / 2000 : ℝ) * (((7 / 6 : ℝ) * Real.log n + 4) / r) ≤ 4 := by
    rw [← mul_div_assoc, div_le_iff₀ hrpos]
    nlinarith only [hr, hL, hn]
  have ht := gaussian1000_tail (show 100 ≤ r by linarith only [hr500])
  dsimp only [LLS.PaperStatements.gaussianPrefixError]
  rw [Real.sqrt_sq hrpos.le]
  change
    (12871 / 1000 : ℝ) - 2 * (489311 / 100000) + (512 / 27) / r ^ 2 +
        (2129 / 2000) * (((7 / 6) * Real.log n + 4) / r) +
        (473 / 10) * (r ^ 2) ^ (-9 / 16 : ℝ) ≤
      _
  linarith only [hpole, ht.1, ht.2]

end PseudoPrime.PrimeTestBounds.MillerRabin
