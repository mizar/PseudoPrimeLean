/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.FullEndpointEvenPolynomial
public import PseudoPrime.LLS.FullEndpointEightNinthsRange
public import PseudoPrime.LLS.FullEndpointEightyOneRange
public import PseudoPrime.LLS.MidscaleEndpointRadius

/-! # Witness bounds from the exact even endpoint shift -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For `log q <= 523/50`, the exact even endpoint polynomial at radius eight
gives a non-one prime at most 61. The radius-eight finite check removes 62–64. -/
theorem exists_prime_ne_one_le_sixty_one_exact_even {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (heven : χ.Even) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log q ≤ 523 / 50) : ∃ p : ℕ, p.Prime ∧ p ≤ 61 ∧ χ p ≠ 1 := by
  obtain ⟨p, hp, hb, hv⟩ :=
    exists_prime_ne_one_of_exact_even_endpoint_polynomial χ hne heven hGRH
      (by norm_num only : (8 : ℝ) ≤ 8)
      (fullEndpoint_polynomial_pos_at_eight (by linarith only [hL]))
  have hp64 : p ≤ 64 := by exact_mod_cast hb
  have hsmall : ∀ p ∈ Finset.range 65, p.Prime → p ≤ 61 := by decide +kernel
  exact ⟨p, hp, hsmall p (Finset.mem_range.mpr (Nat.lt_succ_of_le hp64)) hp, hv⟩

/-- On the translated interval `523/50 <= log q <= 2171/100`, use the
`8/9` radius and the exact even endpoint criterion. -/
theorem exists_prime_ne_one_le_sixtyFourEightyFirst_shifted_log_sq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (heven : χ.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hLlo : 523 / 50 ≤ Real.log q)
    (hLhi : Real.log q ≤ 2171 / 100) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (64 / 81 : ℝ) * (Real.log q - 73 / 50) ^ 2 ∧ χ p ≠ 1 := by
  let L := Real.log q - 73 / 50
  have hL9 : 9 ≤ L := by
    dsimp only [L]; linarith only [hLlo]
  have hL21 : L ≤ 81 / 4 := by
    dsimp only [L]; linarith only [hLhi]
  have hy : (8 : ℝ) ≤ (8 / 9 : ℝ) * L := by nlinarith only [hL9]
  obtain ⟨p, hp, hb, hv⟩ :=
    exists_prime_ne_one_of_exact_even_endpoint_polynomial χ hne heven hGRH hy
      (fullEndpoint_polynomial_pos_eightNinths_log_interval hL9 hL21)
  refine ⟨p, hp, ?_, hv⟩
  dsimp only [L] at hb ⊢
  nlinarith only [hb]

/-- On `523/50 <= log q <= 1373/50`, the `9/10` radius yields the
coefficient-`81/100` shifted quadratic witness bound. -/
theorem exists_prime_ne_one_le_eightyOne_shifted_log_sq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (heven : χ.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hLlo : 523 / 50 ≤ Real.log q)
    (hLhi : Real.log q ≤ 1373 / 50) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (81 / 100 : ℝ) * (Real.log q - 73 / 50) ^ 2 ∧ χ p ≠ 1 := by
  let L := Real.log q - 73 / 50
  have hL9 : 9 ≤ L := by
    dsimp only [L]; linarith only [hLlo]
  have hL26 : L ≤ 26 := by
    dsimp only [L]; linarith only [hLhi]
  have hy : (8 : ℝ) ≤ (9 / 10 : ℝ) * L := by nlinarith only [hL9]
  obtain ⟨p, hp, hb, hv⟩ :=
    exists_prime_ne_one_of_exact_even_endpoint_polynomial χ hne heven hGRH hy
      (fullEndpoint_polynomial_pos_eightyOne_log_interval hL9 hL26)
  refine ⟨p, hp, ?_, hv⟩
  dsimp only [L] at hb ⊢
  nlinarith only [hb]

/-- For `log q <= 706/25`, radius 24 and the exact even endpoint criterion
give a prime at most 576. -/
theorem exists_prime_ne_one_le_576_exact_even {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (heven : χ.Even) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log q ≤ 706 / 25) : ∃ p : ℕ, p.Prime ∧ p ≤ 576 ∧ χ p ≠ 1 := by
  have hlevel : Real.log q - 73 / 50 ≤ 1339 / 50 := by linarith only [hL]
  obtain ⟨p, hp, hb, hv⟩ :=
    exists_prime_ne_one_of_exact_even_endpoint_polynomial χ hne heven hGRH
      (by norm_num only : (8 : ℝ) ≤ 24)
      (fullEndpoint_polynomial_pos_at_twentyFour_of_level_le hlevel)
  have hp576 : p ≤ 576 := by exact_mod_cast hb
  exact ⟨p, hp, hp576, hv⟩

/-- On the translated midscale interval, the certified radius function gives
the exact even endpoint witness bound without rebuilding its affine certificates. -/
theorem exists_prime_ne_one_le_shifted_midscale_radius_sq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (heven : χ.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hLlo : 706 / 25 ≤ Real.log q)
    (hLhi : Real.log q ≤ 5283 / 20) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (midscaleEndpointRadius (Real.log q - 73 / 50)) ^ 2 ∧ χ p ≠ 1 := by
  let L := Real.log q - 73 / 50
  have hLlo' : 1339 / 50 ≤ L := by
    dsimp only [L]; linarith only [hLlo]
  have hLhi' : L ≤ 26269 / 100 := by
    dsimp only [L]; linarith only [hLhi]
  obtain ⟨hy, hpoly⟩ := midscaleEndpointRadius_data hLlo' hLhi'
  obtain ⟨p, hp, hb, hv⟩ :=
    exists_prime_ne_one_of_exact_even_endpoint_polynomial χ hne heven hGRH (by linarith only [hy])
      hpoly
  exact ⟨p, hp, hb, hv⟩

end PseudoPrime.LLS.PaperStatements
