/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDirectMiddleWitness
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131TailWitness

/-! # Gaussian uniform witnesses through the direct middle range -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The verified Gaussian prefix and direct middle interval supply a
rejecting prime for every odd uniform triple with logarithm from 663 to seven million. -/
theorem uniform_gaussian_through_middle {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (663 : ℝ) 7000000) :
    HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
  exact
    uniform_gaussian_to_k131_cutoff hn ho hu hL.1 hGRH
      (fun _ hlo ↦ uniform_gaussian_witness_middle hn ho hu hGRH ⟨hlo.le, hL.2⟩)

end PseudoPrime.PrimeTestBounds.MillerRabin
