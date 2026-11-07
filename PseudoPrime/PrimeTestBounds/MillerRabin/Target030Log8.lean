/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Gaussian030ScalarGap
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaAnalyticBridgeCombined

/-! # GRH rejecting-prime bound with coefficient 3/10 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a uniform Korselt triple at logarithmic scale at least 1000 has
    a rejecting prime bounded by three tenths of the squared logarithm. The
    certified Gaussian scalar gap supplies the witness. -/
theorem uniform_reject_03_log1000 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 1000 ≤ Real.log n) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hp := gaussian030_parameters hL
  obtain ⟨l, hl, hcut, hfail⟩ :=
    uniform_reject_of_gaussian_scalar hn ho hu hGRH hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1
      (gaussian030_scalar_gap hL).le
  exact ⟨l, hl, hcut.trans hp.2.2.2.2, hfail⟩

/-- Under GRH, every odd composite with logarithm at least 8 has a prime
    Miller--Rabin witness bounded by three tenths of the squared logarithm.
    Combine the certified bounded range with the uniform and nonuniform cases. -/
theorem exists_prime_reject_03_log8 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases hsmall : Real.log n ≤ 1000
  · exact exists_reject_03_analytic1000 hn ho hc hGRH hL hsmall
  · by_cases hu : UniformKorseltTriple n
    · exact uniform_reject_03_log1000 hn ho hu hGRH (le_of_not_ge hsmall)
    · exact exists_prime_reject_03_nonuniform_log8 hn ho hc hu hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
