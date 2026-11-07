/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPolePaperRoot

/-! # Conditional paper-root witness for the three-prime branch -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH and the uniform three-prime Korselt hypotheses, a residual certificate
at the paper root yields a prime Miller--Rabin witness bounded by `B_K(log n)`.
The root equation contradicts the scalar necessary condition if every prime passes. -/
theorem refined_pair_root_witness {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {K : ℝ} (hL : 1000 ≤ Real.log n)
    (hK : 0 ≤ K)
    (hres :
      refinedPaperResidual (Real.log n) (refinedPaperRoot (Real.log n) K ^ 2) ≤
        (27 / 25 : ℝ) ^ 5 * K) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ refinedPaperBound (Real.log n) K ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  classical
  have hL0 : 0 ≤ Real.log n := by linarith only [hL]
  have hroot := refined_root_lower hL0 hK
  have hR : (522 : ℝ) ≤ refinedPaperRoot (Real.log n) K ^ 2 := by nlinarith only [hroot, hL]
  by_contra h
  have hall :
    ∀ l : ℕ,
      l.Prime →
        (l : ℝ) ≤ (refinedPaperRoot (Real.log n) K ^ 2) ^ 2 →
        PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
    intro l hl hlR
    have hbound : (l : ℝ) ≤ refinedPaperBound (Real.log n) K := by
      dsimp only [refinedPaperBound]
      simpa only [← pow_mul] using hlR
    exact Classical.byContradiction (fun hf ↦ h ⟨l, hl, hbound, hf⟩)
  have hn' :=
    refined_pair_scalar_necessary hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK
      hrK hvq hvr hR hall
  exact refined_root_scalar_excludes hL0 hK hres hn'

end PseudoPrime.PrimeTestBounds.MillerRabin
