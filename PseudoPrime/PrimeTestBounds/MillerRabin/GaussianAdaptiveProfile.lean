/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianAdaptiveCoefficients
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianRelativeProfileBounds

/-! # Adaptive relative Gaussian profile and its triple witness -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At every logarithmic scale at least two trillion, construct a relative Gaussian
profile whose entrance is that scale. Its slope includes a strict margin of 39;
the square-root parameter and coefficient satisfy the existing profile conditions. -/
noncomputable def adaptiveGaussianProfile (L : ℝ) (hL : 2000000000000 ≤ L) :
    GaussianRelativeProfile where
  C := (21 / 10) * adaptiveGaussianA L ^ 2
  T := L
  a := adaptiveGaussianA L
  v := Real.sqrt L
  entry := by linarith only [hL]
  root := adaptiveGaussianA_lower L hL
  square := by
    ring_nf
    exact le_rfl
  upper := by
    have ha := adaptiveGaussianA_lower L hL
    have hb := adaptiveGaussianA_upper L hL
    have hs := pow_le_pow_left₀ (show 0 ≤ adaptiveGaussianA L by linarith only [ha]) hb 2
    nlinarith only [hs]
  fourth := by
    have hp : 0 < L := by linarith only [hL]
    exact ⟨Real.sqrt_pos.2 hp, (Real.sq_sqrt hp.le).le⟩
  margin := by
    have hp : 0 < L := by linarith only [hL]
    have hs : 0 < Real.sqrt L := Real.sqrt_pos.2 hp
    dsimp only [adaptiveGaussianA]
    field_simp [hp.ne', hs.ne']
    nlinarith only [hp, hs]

/-- At scale at least two trillion, the adaptive Gaussian coefficient is strictly
below the previous coefficient `1411811 / 5000000`. The rational slope upper bound
provides an interval-wide comparison rather than a numerical sample. -/
theorem adaptiveGaussian_coefficient_lt (L : ℝ) (hL : 2000000000000 ≤ L) :
    (21 / 10 : ℝ) * adaptiveGaussianA L ^ 2 < 1411811 / 5000000 := by
  have ha := adaptiveGaussianA_lower L hL
  have hb := adaptiveGaussianA_upper L hL
  have hs := pow_le_pow_left₀ (show 0 ≤ adaptiveGaussianA L by linarith only [ha]) hb 2
  nlinarith only [hs]

/-- Under GRH, an odd squarefree uniform Korselt triple above logarithmic scale two
trillion has a rejecting prime under the adaptive Gaussian coefficient. Construct
the profile at the input's logarithm and apply the existing index-four comparison. -/
theorem adaptiveGaussian_witness_card {n : ℕ} (hnOdd : Odd n) (hsf : Squarefree n)
    (hc : n.primeFactors.card = 3) (hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1)
    (hU :
      ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hnlarge : 20000 ≤ n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (2000000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ ((21 / 10 : ℝ) * adaptiveGaussianA (Real.log n) ^ 2) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  exact
    gaussianProfile_witness_card (adaptiveGaussianProfile (Real.log n) hL) hnOdd hsf hc hK hU
      hnlarge hGRH le_rfl

end PseudoPrime.PrimeTestBounds.MillerRabin
