/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianEulerCutoffTransfer
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186EulerTail
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186EulerTail

/-! # Fixed K186 Euler tail envelopes -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The H18 majorant at the lower cutoff controls all weighted K186
deficits beyond a larger cutoff. This avoids comparing the analytic envelopes. -/
public theorem k186_weighted_tail_from (hRH : RiemannHypothesis) {A X : ℝ} (hA : 0 < A)
    (ha : 30 ≤ Real.log A) (hAX : A ≤ X) (α : ℕ → ℝ) (hα : ∀ n, α n ∈ Set.Icc 0 4) :
    (∑' n : { n : ℕ // ⌊X⌋₊ < n },
        α n.val *
          (ArithmeticFunction.vonMangoldt n.val * (n.val : ℝ) ^ (-(13 / 4) : ℝ) *
            k186MassPoly.eval (Real.log n.val))) ≤
      4 * k186TailCost A := by
  refine
    euler_weighted_tail_from
      (fun n ↦
        ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(13 / 4) : ℝ) *
          k186MassPoly.eval (Real.log n))
      hAX ?_ α hα
  intro β hβ
  have h :=
    euler_trace_tail_rh k186MassPoly (σ := 13 / 4) (by norm_num only) hRH (k186_cutoff_ge hA ha)
      ((by norm_num only : (1 : ℝ) ≤ 30).trans ha)
      (fun z hz ↦ (k186_mass_real_signs (k186_mass_poly_signs (ha.trans hz))).1)
      (fun z hz ↦ (k186_mass_real_signs (k186_mass_poly_signs (ha.trans hz))).2) β hβ
  have hd : (13 / 4 : ℝ) - 1 = 9 / 4 := by norm_num only
  have hh : (13 / 4 : ℝ) - 1 / 2 = 11 / 4 := by norm_num only
  simpa only [hd, hh, k186TailCost] using h

/-- The K186 zero upper bound at the tested cutoff can use an Euler tail
budget evaluated at any fixed admissible lower cutoff. -/
public theorem k186_zero_upper_from {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] [NeZero n]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n) (hprod : n = p * q * r) (hp : Odd p)
    (hq : Odd q) (hr : Odd r) (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {A X : ℝ}
    (hA : 0 < A) (ha : 30 ≤ Real.log A) (hAX : A ≤ X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr);
    -(∑' ρ : ℂ, HighGaussianKernel.k186.zeroTerm a X ρ).re -
        (∑' ρ : ℂ, HighGaussianKernel.k186.zeroTerm b X ρ).re -
        (∑' ρ : ℂ, HighGaussianKernel.k186.zeroTerm c X ρ).re ≤
      3 / 8 * Real.log n - 94173 / 1250 + 3 * HighGaussianKernel.k186.xiMass.re +
        4 * k186TailCost A := by
  intro a b c
  have h :=
    high_gaussian_zero_upper_of_pass .k186 hn ho hu hprod hp hq hr hg (hA.trans_le hAX) hpass
  have ht :=
    k186_weighted_tail_from hg.riemann hA ha hAX (fun m ↦ 3 - ((a m).re + (b m).re + (c m).re))
      (pair_deficit_mem hp hq hr)
  have hw : ((125564 / 10000 : ℚ) : ℝ) < (HighGaussianKernel.k186.massPole : ℝ) :=
    Rat.cast_lt.mpr gaussian_k186_mass_pole_bounds.1
  have he : -(HighGaussianKernel.k186.pole : ℝ) - 1 / 2 = -(13 / 4 : ℝ) := by
    norm_num only [HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat]
  simp only [Rat.cast_div, Rat.cast_ofNat] at hw
  dsimp only at h
  simp only [he, k186MassPoly, Polynomial.eval_map, mul_assoc, mul_left_comm] at h ht
  linarith only [h, ht, hw]

end PseudoPrime.PrimeTestBounds.MillerRabin
