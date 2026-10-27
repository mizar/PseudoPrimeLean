/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GaussianSubgroupComparison
public import PseudoPrime.LLS.GaussianConstantSubgroupComparison
public import PseudoPrime.LLS.RelativeGaussianSubgroupComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaComparison

/-! # Gaussian comparison under universal strong prime-base passage

Prime divisors fail the strong test, so universal passage removes the finite
modulus loss. A supplied pass-containing subgroup obeys the actual Gaussian comparison.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If every prime base up to X passes the strong test for odd n>1, every
prime divisor exceeds floor(X). A prime divisor would fail by nonunitness.
This removes the finite principal-level loss from the Gaussian comparison. -/
private theorem prime_divisor_gt_cutoff_of_strong_pass {n : ℕ} (hn : 1 < n) (hnOdd : Odd n) {X : ℝ}
    (hpass : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    ∀ p : ℕ, p.Prime → p ∣ n → ⌊X⌋₊ < p := by
  intro p hp hdiv
  apply lt_of_not_ge
  intro hle
  have hX : (p : ℝ) ≤ X := (Nat.le_floor_iff' hp.ne_zero).mp hle
  exact PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn hnOdd hp hdiv (hpass p hp hX)

/-- Under GRH for odd n≥20000 and scale x≥4, universal prime-base passage
up to lambda*x forces the actual Gaussian comparison for any supplied subgroup
containing all strong passes. Prime divisors exceed the cutoff, and the signed
subgroup average retains its exact conductor-log sum and numerical errors. -/
theorem gaussian_inequality_of_prime_passes_in_subgroup {n : ℕ} [NeZero n] (hnlarge : 20000 ≤ n)
    (hnOdd : Odd n) (H : Subgroup (ZMod n)ˣ)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x lambda : ℝ} (hx : 4 ≤ x)
    (hl : 0 ≤ lambda)
    (hpass :
      ∀ p : ℕ, p.Prime → (p : ℝ) ≤ lambda * x → PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    ((H.index : ℝ) *
            (∫ u in (0 : ℝ)..lambda,
              (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
          Real.exp (1 / 16 : ℝ)) *
        Real.sqrt x ≤
      (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
        14 * ((H.index : ℝ) + 1) * x ^ (1 / 4 : ℝ) +
        ((H.index - 1 : ℕ) : ℝ) * LLS.PaperStatements.gaussianAmbientError n x := by
  have hn : 1 < n := by linarith only [hnlarge]
  apply
    LLS.PaperStatements.gaussian_noSmallPrimes_explicit_inequality_of_no_small_divisor hnlarge H
      hGRH hx hl
  · exact prime_divisor_gt_cutoff_of_strong_pass hn hnOdd hpass
  · intro p hp _ hpX
    exact hHpass (p : ZMod n) (hpass p hp hpX)

/-- Under GRH, if every prime base through lambda*x passes and lambda*x reaches
50000, the Gaussian subgroup comparison uses the transferred prefix error. -/
theorem gaussian_inequality_of_prime_passes_in_subgroup_prefix_gain {n : ℕ} [NeZero n]
    (hnlarge : 20000 ≤ n) (hnOdd : Odd n) (H : Subgroup (ZMod n)ˣ)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x lambda : ℝ} (hx : 4 ≤ x)
    (hX : 50000 ≤ lambda * x)
    (hpass :
      ∀ p : ℕ, p.Prime → (p : ℝ) ≤ lambda * x → PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    ((H.index : ℝ) *
            (∫ u in (0 : ℝ)..lambda,
              (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
          Real.exp (1 / 16 : ℝ)) *
        Real.sqrt x ≤
      (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
        14 * ((H.index : ℝ) + 1) * x ^ (1 / 4 : ℝ) +
        ((H.index - 1 : ℕ) : ℝ) * LLS.PaperStatements.gaussianAmbientErrorPrefix n x := by
  have hn : 1 < n := by linarith only [hnlarge]
  apply
    LLS.PaperStatements.gaussian_noSmallPrimes_explicit_inequality_prefix_gain hnlarge H hGRH hx hX
  · exact prime_divisor_gt_cutoff_of_strong_pass hn hnOdd hpass
  · intro p hp _ hpX
    exact hHpass (p : ZMod n) (hpass p hp hpX)

/-- Under GRH, universal prime-base passage through a 50000 prefix forces the
Gaussian comparison with the signed left-contour remainder. -/
theorem gaussian_inequality_of_prime_passes_in_subgroup_prefix_gain_signed {n : ℕ} [NeZero n]
    (hnlarge : 20000 ≤ n) (hnOdd : Odd n) (H : Subgroup (ZMod n)ˣ)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x lambda : ℝ} (hx : 4 ≤ x)
    (hX : 50000 ≤ lambda * x)
    (hpass :
      ∀ p : ℕ, p.Prime → (p : ℝ) ≤ lambda * x → PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    ((H.index : ℝ) *
            (∫ u in (0 : ℝ)..lambda,
              (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
          Real.exp (1 / 16 : ℝ)) *
        Real.sqrt x ≤
      (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
        14 * ((H.index : ℝ) + 1) * x ^ (1 / 4 : ℝ) +
        ((H.index - 1 : ℕ) : ℝ) * LLS.PaperStatements.gaussianAmbientErrorPrefixSigned n x := by
  have hn : 1 < n := by linarith only [hnlarge]
  apply
    LLS.PaperStatements.gaussian_noSmallPrimes_explicit_inequality_prefix_gain_signed hnlarge H hGRH
      hx hX
  · exact prime_divisor_gt_cutoff_of_strong_pass hn hnOdd hpass
  · intro p hp _ hpX
    exact hHpass (p : ZMod n) (hpass p hp hpX)

/-- Under GRH, relative-width Gaussian comparison and a 50000 prefix bound,
universal prime-base passage forces the signed left-contour estimate. -/
theorem gaussian_inequality_of_prime_passes_in_subgroup_relative_prefix_gain_signed {n : ℕ}
    [NeZero n] (hnlarge : 20000 ≤ n) (hnOdd : Odd n) (H : Subgroup (ZMod n)ˣ)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {h x lambda : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1 / 2) (hx : 4 ≤ x) (hl : 0 ≤ lambda) (hX : 50000 ≤ lambda * x)
    (hpass :
      ∀ p : ℕ, p.Prime → (p : ℝ) ≤ lambda * x → PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    ((H.index : ℝ) * (1 - h) *
            (∫ u in (0 : ℝ)..lambda,
              (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
          Real.exp (1 / 16 : ℝ)) *
        Real.sqrt x ≤
      (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
        (H.index : ℝ) *
          (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / Real.sqrt x) * Real.exp (1 / 16 : ℝ)) +
        13 +
        ((H.index - 1 : ℕ) : ℝ) * LLS.PaperStatements.gaussianAmbientErrorPrefixSigned n x := by
  have hn : 1 < n := by linarith only [hnlarge]
  apply
    LLS.PaperStatements.gaussian_noSmallPrimes_inequality_relative_prefix_gain_signed hnlarge H hGRH
      hh hh1 hx hl hX
  · exact prime_divisor_gt_cutoff_of_strong_pass hn hnOdd hpass
  · intro p hp _ hpX
    exact hHpass (p : ZMod n) (hpass p hp hpX)

/-- Under GRH for odd n≥20000 and scale x≥4, universal prime-base passage
up to lambda*x forces the actual Gaussian comparison for any supplied subgroup
containing all strong passes. Prime divisors exceed the cutoff, and the signed
subgroup average retains its exact conductor-log sum and numerical errors. -/
theorem gaussian_inequality_of_prime_passes_constant_principal {n : ℕ} [NeZero n]
    (hnlarge : 20000 ≤ n) (hnOdd : Odd n) (H : Subgroup (ZMod n)ˣ)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x lambda : ℝ} (hx : 4 ≤ x)
    (hl : 0 ≤ lambda)
    (hpass :
      ∀ p : ℕ, p.Prime → (p : ℝ) ≤ lambda * x → PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    ((H.index : ℝ) *
            (∫ u in (0 : ℝ)..lambda,
              (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
          Real.exp (1 / 16 : ℝ)) *
        Real.sqrt x ≤
      (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
        14 * (H.index : ℝ) * x ^ (1 / 4 : ℝ) +
        13 +
        ((H.index - 1 : ℕ) : ℝ) * LLS.PaperStatements.gaussianAmbientError n x := by
  have hn : 1 < n := by linarith only [hnlarge]
  apply
    LLS.PaperStatements.gaussian_noSmallPrimes_explicit_inequality_constant_principal hnlarge H hGRH
      hx hl
  · exact prime_divisor_gt_cutoff_of_strong_pass hn hnOdd hpass
  · intro p hp _ hpX
    exact hHpass (p : ZMod n) (hpass p hp hpX)

end PseudoPrime.PrimeTestBounds.MillerRabin
