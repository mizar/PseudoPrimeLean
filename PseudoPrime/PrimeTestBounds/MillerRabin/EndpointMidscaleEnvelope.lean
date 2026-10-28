/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LeastWitnessBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointExactEvenPolynomial
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointEvenPolynomial
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointGammaEnvelope

/-! # Endpoint bounds and their two-step minimum on the midscale -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The applicable 7/4-shifted endpoint candidate, selected by its certified upper range.
The input L is a logarithmic scale; witness claims are restricted to 43/4<=L<=13517/100.
This base retains the fixed and affine endpoint ranges. -/
noncomputable def endpointMidscaleBase (L : ℝ) : ℝ :=
  if L ≤ 22 then (64 / 81 : ℝ) * (L - 7 / 4) ^ 2
  else
    if L ≤ 111 / 4 then (81 / 100 : ℝ) * (L - 7 / 4) ^ 2
    else if L ≤ 144 / 5 then 576 else LLS.PaperStatements.midscaleEndpointRadius (L - 7 / 4) ^ 2

/-- The endpoint base with the two-step cutoff included whenever L>=23/2.
Both candidates are bounds for all odd composites in their certified range.
This conditional minimum keeps the full application range of the two-step theorem. -/
noncomputable def endpointMidscaleEnvelope (L : ℝ) : ℝ :=
  if 23 / 2 ≤ L then
    min (endpointMidscaleBase L) (LLS.PaperStatements.fullEndpointEvenTwoStepCutoff L)
  else endpointMidscaleBase L

/-- Under GRH and 43/4<=log n<=13517/100, the endpoint base bounds the least rejecting prime.
Select the applicable endpoint theorem and reorder its conjunctions.
The conclusion retains primality, strong-MR rejection, and minimality. -/
theorem exists_least_endpointMidscaleBase {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 43 / 4 ≤ Real.log n) (hU : Real.log n ≤ 13517 / 100) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ endpointMidscaleBase (Real.log n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  by_cases h8 : Real.log n ≤ 22
  · obtain ⟨p, hp, hb, hr, hm⟩ :=
      exists_least_prime_reject_le_7over4_shifted_eightNinths_log_sq hn ho hc hGRH hL h8
    refine ⟨p, hp, hr, ?_, hm⟩
    simpa only [endpointMidscaleBase, ite_eq_left h8] using hb
  · by_cases h9 : Real.log n ≤ 111 / 4
    · obtain ⟨p, hp, hb, hr, hm⟩ :=
        exists_least_prime_reject_le_7over4_shifted_eightyOne_log_sq hn ho hc hGRH hL h9
      refine ⟨p, hp, hr, ?_, hm⟩
      simpa only [endpointMidscaleBase, ite_eq_right h8, ite_eq_left h9] using hb
    · by_cases hf : Real.log n ≤ 144 / 5
      · obtain ⟨p, hp, hb, hr, hm⟩ := exists_least_prime_reject_le_576_exact_even hn ho hc hGRH hf
        refine ⟨p, hp, hr, ?_, hm⟩
        simpa only [endpointMidscaleBase, ite_eq_right h8, ite_eq_right h9, ite_eq_left hf] using
          (show (p : ℝ) ≤ 576 by exact_mod_cast hb)
      · obtain ⟨p, hp, hb, hr, hm⟩ :=
          exists_least_prime_reject_le_7over4_shifted_midscale_radius_sq hn ho hc hGRH
            (le_of_not_ge hf) hU
        refine ⟨p, hp, hr, ?_, hm⟩
        simpa only [endpointMidscaleBase, ite_eq_right h8, ite_eq_right h9, ite_eq_right hf] using
          hb

/-- Under GRH in the endpoint range, the conditional minimum bounds the least rejecting prime.
Use the two-step theorem exactly when log n>=23/2 and combine least-witness bounds.
No squarefree or subgroup-index premise is introduced. -/
theorem exists_least_endpointMidscale {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 43 / 4 ≤ Real.log n)
    (hU : Real.log n ≤ 13517 / 100) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ endpointMidscaleEnvelope (Real.log n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  have hbase := exists_least_endpointMidscaleBase hn ho hc hGRH hL hU
  by_cases h2 : 23 / 2 ≤ Real.log n
  · obtain ⟨p, hp, hb, hr, hm⟩ := exists_least_prime_reject_le_even_twoStep_cutoff hn ho hc hGRH h2
    simpa only [endpointMidscaleEnvelope, ite_eq_left h2] using
      least_prime_witness_bound_min hbase ⟨p, hp, hr, hb, hm⟩
  · simpa only [endpointMidscaleEnvelope, ite_eq_right h2] using hbase

/-- The three expressions used in the comparison interval 74/5<L<=111/4.
Select the 73/50-shifted 64/81 and 81/100 quadratics, then the fixed value 576.
This definition is only a comparison baseline, not a separate witness theorem. -/
noncomputable def endpointLegacyBound (L : ℝ) : ℝ :=
  if L ≤ 2171 / 100 then (64 / 81 : ℝ) * (L - 73 / 50) ^ 2
  else if L ≤ 1373 / 50 then (81 / 100 : ℝ) * (L - 73 / 50) ^ 2 else 576

/-- For L>=43/4, the 7/4-shifted square is strictly below the 73/50-shifted square.
Compare the nonnegative bases before squaring. This supports the endpoint interval comparison. -/
theorem shift_sq_strict {L : ℝ} (hL : 43 / 4 ≤ L) : (L - 7 / 4) ^ 2 < (L - 73 / 50) ^ 2 := by
  apply
    (sq_lt_sq₀ (by linarith only [hL] : 0 ≤ L - 7 / 4)
        (by linarith only [hL] : 0 ≤ L - 73 / 50)).mpr
  linarith only

/-- For 74/5<L<=111/4, the endpoint base strictly improves the comparison baseline.
Split at the certified endpoint ranges, use the strict shift comparison, and bound the final square.
This proves improvement on a continuous interval rather than at sampled points. -/
theorem endpoint_base_lt_legacy {L : ℝ} (hL : 74 / 5 < L) (hU : L ≤ 111 / 4) :
    endpointMidscaleBase L < endpointLegacyBound L := by
  have h43 : 43 / 4 ≤ L := by linarith only [hL]
  have hs := shift_sq_strict h43
  by_cases h1 : L ≤ 2171 / 100
  · simp only [endpointMidscaleBase, ite_eq_left (by linarith only [h1] : L ≤ 22),
      endpointLegacyBound, ite_eq_left h1]
    exact mul_lt_mul_of_pos_left hs (by norm_num only : (0 : ℝ) < 64 / 81)
  · by_cases h8 : L ≤ 22
    · simp only [endpointMidscaleBase, ite_eq_left h8, endpointLegacyBound, ite_eq_right h1,
        ite_eq_left (by linarith only [h8] : L ≤ 1373 / 50)]
      have hscaled := mul_lt_mul_of_pos_left hs (by norm_num only : (0 : ℝ) < 64 / 81)
      nlinarith only [hscaled, sq_nonneg (L - 73 / 50)]
    · simp only [endpointMidscaleBase, ite_eq_right h8, ite_eq_left hU]
      by_cases h9 : L ≤ 1373 / 50
      · simp only [endpointLegacyBound, ite_eq_right h1, ite_eq_left h9]
        exact mul_lt_mul_of_pos_left hs (by norm_num only : (0 : ℝ) < 81 / 100)
      · simp only [endpointLegacyBound, ite_eq_right h1, ite_eq_right h9]
        have hsq :=
          (sq_le_sq₀ (by linarith only [h43] : 0 ≤ L - 7 / 4) (by norm_num only : (0 : ℝ) ≤ 26)).mpr
            (by linarith only [hU])
        nlinarith only [hsq]

/-- For 74/5<L<=111/4, the endpoint minimum strictly improves the baseline.
The minimum is at most its base, whose strict comparison is already proved.
The result keeps the two-step candidate without assuming it is the minimizer. -/
theorem endpoint_midscale_lt_legacy {L : ℝ} (hL : 74 / 5 < L) (hU : L ≤ 111 / 4) :
    endpointMidscaleEnvelope L < endpointLegacyBound L := by
  have h2 : 23 / 2 ≤ L := by linarith only [hL]
  exact
    lt_of_le_of_lt
      (by
        simp only [endpointMidscaleEnvelope, ite_eq_left h2]
        exact min_le_left _ _)
      (endpoint_base_lt_legacy hL hU)

/-- For 56/5<L<23/2, the endpoint minimum is below the 73/50-shifted quadratic.
The two-step guard is inactive and the strict shift comparison applies.
This covers the low interval preceding the two-step entrance. -/
theorem endpoint_midscale_lt_low {L : ℝ} (hL : 56 / 5 < L) (hU : L < 23 / 2) :
    endpointMidscaleEnvelope L < (64 / 81 : ℝ) * (L - 73 / 50) ^ 2 := by
  simp only [endpointMidscaleEnvelope, ite_eq_right (not_le.mpr hU), endpointMidscaleBase,
    ite_eq_left (by linarith only [hU] : L ≤ 22)]
  exact mul_lt_mul_of_pos_left (shift_sq_strict (by linarith only [hL])) (by norm_num only)

/-- The endpoint-Gamma overlap minimum with the two-step cutoff included.
It is used on 120<=L<=122, where all three witness bounds apply.
No unproved crossing point is selected. -/
noncomputable def endpointGammaMidscale (L : ℝ) : ℝ :=
  min (endpointGammaEnvelope L) (LLS.PaperStatements.fullEndpointEvenTwoStepCutoff L)

/-- Under GRH and 120<=log n<=122, the overlap minimum bounds the least rejecting prime.
Combine the existing endpoint-Gamma theorem with the full-range two-step theorem.
The conclusion includes actual strong-MR rejection and minimality. -/
theorem exists_least_endpointGammaMidscale {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 120 ≤ Real.log n) (hU : Real.log n ≤ 122) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ endpointGammaMidscale (Real.log n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hb, hr, hm⟩ :=
    exists_least_prime_reject_le_even_twoStep_cutoff hn ho hc hGRH (by linarith only [hL])
  exact
    least_prime_witness_bound_min
      (exists_least_prime_witness_le_endpointGammaEnvelope ho hc hGRH hL hU) ⟨p, hp, hr, hb, hm⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
