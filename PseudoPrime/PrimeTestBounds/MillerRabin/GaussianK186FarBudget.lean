/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186DirectComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186TailBudget

/-! # The far K186 comparison with a fixed Euler budget -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On the far half-line, the remaining forward and base loss estimates
imply a rejecting prime. The right Euler cost is supplied by the fixed
logarithmic cutoff 53 and requires no further numerical input. -/
theorem uniform_k186_far_of_base_costs {n : ℕ} {α : ℝ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 10 ^ 12 ≤ Real.log n) (hα : 0.7216056623106 ≤ α)
    (hf :
      let y := gaussianK186FarScale * Real.log n
      α * y ≤ k186ForwardValue (y ^ 2))
    (hc :
      let y := gaussianK186FarScale * Real.log n
      k186DirectBaseLoss (Real.log n) (y ^ 2) + 1 / 10 ^ 8 ≤ 61 / 1000 * Real.log y ^ 2 + 500) :
    HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
  let L := Real.log n
  let X := (gaussianK186FarScale * L) ^ 2
  have hL' := (by norm_num only : (7000000 : ℝ) ≤ 10 ^ 12).trans hL
  have hd := k186_direct_cutoff_domain hL'
  have hz : (profileCorrectionStart .k186 : ℝ) ≤ 5 + Real.log X := by
    simp only [profileCorrectionStart, Rat.cast_ofNat, X, L]
    linarith only [hd.2]
  have hw : HasRejectingPrime n X := by
    apply uniform_gaussian_witness_from_factors hn ho hu
    intro p q r _ _ _ _ _ _ _ _ _ _ hprod hp hq hr
    by_contra h
    have hpass (l : ℕ) (hl : l.Prime) (hle : (l : ℝ) ≤ X) :
      PrimeTest.StrongMillerRabinPass n (l : ZMod n) :=
      Classical.byContradiction (fun hf ↦ h ⟨l, hl, hle, hf⟩)
    have hupp :=
      k186_direct_inequality_from hGRH hn ho hu hprod hp hq hr hd.1 (Real.exp_pos 53)
        (by
          rw [Real.log_exp]; norm_num only)
        (k186_far_tail_anchor hL) hz hpass
    have hc' := gaussian_k186_far_comparison hα hL hc
    dsimp only at hf hc'
    linarith only [hf, hc', hupp, k186_far_tail_budget]
  exact hw.mono (gaussian_k186_far_cutoff ((by norm_num only : (2000000 : ℝ) ≤ 7000000).trans hL'))

end PseudoPrime.PrimeTestBounds.MillerRabin
