/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointMidscaleEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointFixed61
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaRefinedEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMR35000WitnessBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMRWitnessEnvelopes
/-! # All-input MR witness envelope with certified improvements through log n=240 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The minimum of the certified 35000-prefix and refined 1000-prefix Gamma bounds.
Both apply to all odd composites under GRH from logarithmic scale 120.
The definition makes no numerical crossing assumption. -/
noncomputable def gammaLowEnvelope (L : ℝ) : ℝ :=
  min (gamma35000Bound L) (gamma1000RefinedBound L)

/-- Under GRH and log n>=120, the least rejecting prime obeys the two-prefix minimum.
Combine the two actual witness theorems with the common minimum lemma.
The conclusion includes primality, strong-MR rejection, and minimality. -/
theorem exists_least_gammaLowEnvelope {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 120 ≤ Real.log n) :
    ∃ p : ℕ, p.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
      (p : ℝ) ≤ gammaLowEnvelope (Real.log n) ∧
      ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hb, hr, hm⟩ := exists_least_gamma35000 hn ho hc hGRH hL
  obtain ⟨q, hq, hqb, hqr, hqm⟩ := exists_least_gamma1000Refined hn ho hc hGRH hL
  exact least_prime_witness_bound_min ⟨p, hp, hr, hb, hm⟩ ⟨q, hq, hqr, hqb, hqm⟩

/-- The analytic base for the public envelope, selected only within certified ranges.
Use 61 through 286/25, the 7/4 endpoint candidates below 120, their Gamma overlap
through 122, the two-prefix Gamma minimum below 240, and the Gaussian envelope thereafter. -/
noncomputable def mrAnalyticBase (n : ℕ) : ℝ :=
  let L := Real.log n
  if L ≤ 286 / 25 then 61
  else if L < 120 then endpointMidscaleBase L
  else if L ≤ 122 then min (endpointMidscaleBase L) (gammaLowEnvelope L)
  else if L < 240 then gammaLowEnvelope L
  else gaussianMRWitnessEnvelope n

/-- For every odd composite n>1 under GRH, the analytic base bounds the least rejecting prime.
Split at each certified logarithmic boundary and use the corresponding endpoint, Gamma,
or Gaussian witness theorem. No factorization premise is exposed. -/
theorem exists_least_mrAnalyticBase {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
      (p : ℝ) ≤ mrAnalyticBase n ∧
      ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  by_cases h61 : Real.log n ≤ 286 / 25
  · obtain ⟨p, hp, hb, hr, hm⟩ := exists_least_endpoint61 hn ho hc hGRH h61
    refine ⟨p, hp, hr, ?_, hm⟩
    simpa only [mrAnalyticBase, ite_eq_left h61] using hb
  · have hlow : 43 / 4 ≤ Real.log n := by linarith only [lt_of_not_ge h61]
    by_cases he : Real.log n < 120
    · have h := exists_least_endpointMidscaleBase hn ho hc hGRH hlow
        (by linarith only [he])
      simpa only [mrAnalyticBase, ite_eq_right h61, ite_eq_left he] using h
    · have hg := exists_least_gammaLowEnvelope hn ho hc hGRH (le_of_not_gt he)
      by_cases h122 : Real.log n ≤ 122
      · have hb := exists_least_endpointMidscaleBase hn ho hc hGRH hlow
          (by linarith only [h122])
        simpa only [mrAnalyticBase, ite_eq_right h61, ite_eq_right he,
          ite_eq_left h122] using least_prime_witness_bound_min hb hg
      · by_cases h240 : Real.log n < 240
        · simpa only [mrAnalyticBase, ite_eq_right h61, ite_eq_right he,
            ite_eq_right h122, ite_eq_left h240] using hg
        · simpa only [mrAnalyticBase, ite_eq_right h61, ite_eq_right he,
            ite_eq_right h122, ite_eq_right h240] using
            exists_least_witness_gaussianMR_envelope ho hc hGRH (le_of_not_gt h240)

/-- The analytic base with exact finite bounds two and three for inputs below 2047 and 3000.
The integer guards are evaluated before analytic bounds. This preserves the small
input conventions while supporting a single least-witness theorem. -/
noncomputable def mrLowBase (n : ℕ) : ℝ :=
  if n < 2047 then 2 else if n < 3000 then 3 else mrAnalyticBase n

/-- For odd composite 1<n<3000, one of the primes two and three rejects strong MR.
Transfer the existing Boolean rejection certificate to the canonical pass predicate.
This theorem needs no GRH and is used only in the finite base. -/
theorem exists_prime_small_three {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hN : n < 3000) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 3 ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  rcases PrimeTest.base_two_or_three_rejects_of_lt_3000 hn ho hc hN with h2 | h3
  · exact ⟨2, Nat.prime_two, by norm_num only,
      PrimeTest.strongMillerRabinWithBase_eq_false_iff_not_pass.mp h2⟩
  · exact ⟨3, Nat.prime_three, by norm_num only,
      PrimeTest.strongMillerRabinWithBase_eq_false_iff_not_pass.mp h3⟩

/-- For every odd composite n>1 under GRH, the finite-plus-analytic base bounds the least witness.
Use base two below 2047, the two-or-three certificate below 3000, and the analytic
base elsewhere. The least-prime extraction preserves actual rejection. -/
theorem exists_least_mrLowBase {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
      (p : ℝ) ≤ mrLowBase n ∧
      ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  by_cases h2 : n < 2047
  · have hfail : ¬PrimeTest.StrongMillerRabinPass n (2 : ZMod n) := by
      intro hp
      exact hc ((PrimeTest.base_two_decides_prime_of_lt_2047 hn ho h2).mp
        (PrimeTest.strongMillerRabinWithBase_eq_true_iff_pass.mpr hp))
    obtain ⟨p, hp, hb, hr, hm⟩ := exists_least_prime_reject_of_exists_prime_reject
      (show ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) from
        ⟨2, Nat.prime_two, by norm_num only, hfail⟩)
    exact ⟨p, hp, hr, by simpa only [mrLowBase, ite_eq_left h2] using hb, hm⟩
  · by_cases h3 : n < 3000
    · obtain ⟨p, hp, hb, hr, hm⟩ := exists_least_prime_reject_of_exists_prime_reject
        (exists_prime_small_three hn ho hc h3)
      refine ⟨p, hp, hr, ?_, hm⟩
      simpa only [mrLowBase, ite_eq_right h2, ite_eq_left h3] using hb
    · simpa only [mrLowBase, ite_eq_right h2, ite_eq_right h3] using
        exists_least_mrAnalyticBase hn ho hc hGRH

/-- Include the two-step cutoff in the finite-plus-analytic base when 23/2<=log n<=240.
The two-step theorem itself has no upper logarithmic limit; the guard restricts
this envelope update to the designated low and middle target region. -/
noncomputable def mrTwoStepEnvelope (n : ℕ) : ℝ :=
  if 23 / 2 ≤ Real.log n ∧ Real.log n ≤ 240 then
    min (mrLowBase n) (LLS.PaperStatements.fullEndpointEvenTwoStepCutoff (Real.log n))
  else mrLowBase n

/-- The public MR envelope with fixed 35000 included when 63<=log n<=240.
It also contains the conditional two-step cutoff, refined endpoint and Gamma bounds,
and the exact finite branches. Above 240 it agrees with the Gaussian envelope. -/
noncomputable def midscaleWitnessEnvelope (n : ℕ) : ℝ :=
  if 63 ≤ Real.log n ∧ Real.log n ≤ 240 then min (mrTwoStepEnvelope n) 35000
  else mrTwoStepEnvelope n

/-- For every odd composite n>1 under GRH, the conditional two-step envelope bounds
the least rejecting prime. Add the full-range two-step theorem only when its lower
threshold and the envelope update upper guard both hold. -/
theorem exists_least_mrTwoStepEnvelope {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
      (p : ℝ) ≤ mrTwoStepEnvelope n ∧
      ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  have hb := exists_least_mrLowBase hn ho hc hGRH
  by_cases h : 23 / 2 ≤ Real.log n ∧ Real.log n ≤ 240
  · obtain ⟨p, hp, hb2, hr, hm⟩ :=
      exists_least_prime_reject_le_even_twoStep_cutoff hn ho hc hGRH h.1
    simpa only [mrTwoStepEnvelope, ite_eq_left h] using
      least_prime_witness_bound_min hb ⟨p, hp, hr, hb2, hm⟩
  · simpa only [mrTwoStepEnvelope, ite_eq_right h] using hb

/-- For every odd composite n>1 under GRH, the public midscale envelope bounds
the least prime rejecting strong MR. Add the fixed Gaussian theorem only for
63<=log n<=240. All local and conductor classifications remain internal. -/
theorem exists_least_midscaleWitness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
      (p : ℝ) ≤ midscaleWitnessEnvelope n ∧
      ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  have hb := exists_least_mrTwoStepEnvelope hn ho hc hGRH
  by_cases h : 63 ≤ Real.log n ∧ Real.log n ≤ 240
  · simpa only [midscaleWitnessEnvelope, ite_eq_left h] using
      least_prime_witness_bound_min hb (exists_least_witness_gaussian35000 ho hc hGRH h.1 h.2)
  · simpa only [midscaleWitnessEnvelope, ite_eq_right h] using hb

/-- For every odd composite n>1 under GRH, a prime rejecting strong MR is at most
the public midscale envelope. Project the prime, bound, and rejection fields
from the least-witness theorem. -/
theorem exists_prime_midscaleWitness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ midscaleWitnessEnvelope n ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hr, hb, _⟩ := exists_least_midscaleWitness hn ho hc hGRH
  exact ⟨p, hp, hb, hr⟩

/-- For each input, the public midscale envelope is at most its finite-plus-analytic base.
Each conditional addition is a numerical minimum. This comparison requires no GRH
and transfers strict base comparisons to the final envelope. -/
theorem midscaleWitnessEnvelope_le_base (n : ℕ) :
    midscaleWitnessEnvelope n ≤ mrLowBase n := by
  have hbase : mrTwoStepEnvelope n ≤ mrLowBase n := by
    dsimp only [mrTwoStepEnvelope]
    split_ifs
    · exact min_le_left _ _
    · exact le_rfl
  dsimp only [midscaleWitnessEnvelope]
  split_ifs
  · exact (min_le_left _ _).trans hbase
  · exact hbase

/-- A positive natural number with logarithm at least eleven is at least 3000.
Otherwise its logarithm is bounded above by log 46000<11. This removes the finite
branches in purely numerical interval comparisons. -/
theorem midscale_large_of_log {n : ℕ} (hn : 0 < n) (hL : 11 ≤ Real.log n) :
    3000 ≤ n := by
  by_contra h
  have hN : (n : ℝ) ≤ 46000 := by
    exact_mod_cast ((lt_of_not_ge h).le.trans (by norm_num only : 3000 ≤ 46000))
  have hl := Real.log_le_log (Nat.cast_pos.mpr hn) hN
  linarith only [hl, Analysis.log_46000_lt_eleven, hL]

/-- For n>1 and 74/5<log n<=111/4, the public envelope strictly improves the
73/50-shifted endpoint baseline. Simplify the finite and fixed-cutoff guards and
apply the continuous endpoint comparison. No GRH is required for this formula comparison. -/
theorem midscaleWitnessEnvelope_lt_endpoint {n : ℕ} (hn : 1 < n)
    (hL : 74 / 5 < Real.log n) (hU : Real.log n ≤ 111 / 4) :
    midscaleWitnessEnvelope n < endpointLegacyBound (Real.log n) := by
  have hN := midscale_large_of_log (Nat.zero_lt_of_lt hn) (by linarith only [hL])
  have h2 : ¬n < 2047 := not_lt.mpr ((by norm_num only : 2047 ≤ 3000).trans hN)
  have h3 : ¬n < 3000 := not_lt.mpr hN
  have h61 : ¬Real.log n ≤ 286 / 25 := by linarith only [hL]
  have he : Real.log n < 120 := by linarith only [hU]
  have hguard : 23 / 2 ≤ Real.log n ∧ Real.log n ≤ 240 :=
    ⟨by linarith only [hL], by linarith only [hU]⟩
  have hfixed : ¬(63 ≤ Real.log n ∧ Real.log n ≤ 240) := by
    intro h
    linarith only [h.1, hU]
  simpa only [midscaleWitnessEnvelope, ite_eq_right hfixed, mrTwoStepEnvelope,
    ite_eq_left hguard, mrLowBase, ite_eq_right h2, ite_eq_right h3, mrAnalyticBase,
    ite_eq_right h61, ite_eq_left he, endpointMidscaleEnvelope,
    ite_eq_left hguard.1] using endpoint_midscale_lt_legacy hL hU

/-- For n>1 and 122<=log n<240, the public envelope is strictly below the clipped
Gamma baseline. Its base is at most the refined two-prefix minimum, and the
413/100-credit branch is strictly smaller on this whole interval. -/
theorem midscaleWitnessEnvelope_lt_gamma {n : ℕ} (hn : 1 < n)
    (hL : 122 ≤ Real.log n) (hU : Real.log n < 240) :
    midscaleWitnessEnvelope n < gammaClippedUpper (Real.log n) := by
  have hN := midscale_large_of_log (Nat.zero_lt_of_lt hn) (by linarith only [hL])
  have h2 : ¬n < 2047 := not_lt.mpr ((by norm_num only : 2047 ≤ 3000).trans hN)
  have h3 : ¬n < 3000 := not_lt.mpr hN
  have h61 : ¬Real.log n ≤ 286 / 25 := by linarith only [hL]
  have he : ¬Real.log n < 120 := by linarith only [hL]
  have hb : mrLowBase n ≤ gammaLowEnvelope (Real.log n) := by
    simp only [mrLowBase, ite_eq_right h2, ite_eq_right h3, mrAnalyticBase,
      ite_eq_right h61, ite_eq_right he, ite_eq_left hU]
    split_ifs
    · exact min_le_right _ _
    · exact le_rfl
  exact lt_of_le_of_lt ((midscaleWitnessEnvelope_le_base n).trans
    (hb.trans (min_le_right _ _)))
    (prefix1000Refined_lt_upper (by linarith only [hL]) hU.le)

/-- For n>1 and 56/5<log n<=286/25, the public envelope improves the endpoint baseline.
Its analytic base is 61, below the 73/50-shifted quadratic on this interval.
This connects the fixed-radius extension to a continuous strict comparison. -/
theorem midscaleWitnessEnvelope_lt_low {n : ℕ} (hn : 1 < n)
    (hL : 56 / 5 < Real.log n) (hU : Real.log n ≤ 286 / 25) :
    midscaleWitnessEnvelope n < (64 / 81 : ℝ) * (Real.log n - 73 / 50) ^ 2 := by
  have hN := midscale_large_of_log (Nat.zero_lt_of_lt hn) (by linarith only [hL])
  have h2 : ¬n < 2047 := not_lt.mpr ((by norm_num only : 2047 ≤ 3000).trans hN)
  have h3 : ¬n < 3000 := not_lt.mpr hN
  have hb : midscaleWitnessEnvelope n ≤ 61 := by
    simpa only [mrLowBase, ite_eq_right h2, ite_eq_right h3, mrAnalyticBase,
      ite_eq_left hU] using midscaleWitnessEnvelope_le_base n
  have hs : (9 : ℝ) ^ 2 < (Real.log n - 73 / 50) ^ 2 := by
    exact (sq_lt_sq₀ (by norm_num only)
      (by linarith only [hL] : 0 ≤ Real.log n - 73 / 50)).mpr (by linarith only [hL])
  exact hb.trans_lt (by nlinarith only [hs])

/-- For 63<=log n<=240, the public envelope is at most 35000.
The fixed-cutoff guard selects a minimum containing 35000. This algebraic statement
is separate from the GRH witness theorem and its all-input classification. -/
theorem midscaleWitnessEnvelope_le_35000 {n : ℕ}
    (hL : 63 ≤ Real.log n) (hU : Real.log n ≤ 240) :
    midscaleWitnessEnvelope n ≤ 35000 := by
  simp only [midscaleWitnessEnvelope, ite_eq_left (And.intro hL hU)]
  exact min_le_right _ _

/-- For n>1 and 56/5<log n<23/2, the public envelope improves the endpoint baseline.
Use the fixed-61 comparison through 286/25 and the strict 7/4-shift comparison
thereafter. This covers the entire interval preceding the two-step entrance. -/
theorem midscaleWitnessEnvelope_lt_preTwoStep {n : ℕ} (hn : 1 < n)
    (hL : 56 / 5 < Real.log n) (hU : Real.log n < 23 / 2) :
    midscaleWitnessEnvelope n < (64 / 81 : ℝ) * (Real.log n - 73 / 50) ^ 2 := by
  by_cases h61 : Real.log n ≤ 286 / 25
  · exact midscaleWitnessEnvelope_lt_low hn hL h61
  · have hN := midscale_large_of_log (Nat.zero_lt_of_lt hn) (by linarith only [hL])
    have h2 : ¬n < 2047 := not_lt.mpr ((by norm_num only : 2047 ≤ 3000).trans hN)
    have h3 : ¬n < 3000 := not_lt.mpr hN
    have he : Real.log n < 120 := by linarith only [hU]
    have hb : midscaleWitnessEnvelope n ≤ endpointMidscaleBase (Real.log n) := by
      simpa only [mrLowBase, ite_eq_right h2, ite_eq_right h3, mrAnalyticBase,
        ite_eq_right h61, ite_eq_left he] using midscaleWitnessEnvelope_le_base n
    apply hb.trans_lt
    simp only [endpointMidscaleBase, ite_eq_left (by linarith only [hU] : Real.log n ≤ 22)]
    exact mul_lt_mul_of_pos_left (shift_sq_strict (by linarith only [hL])) (by norm_num only)

/-- For every L, the 35000-prefix bound is at least 35000.
Its radius includes the square root of the scaled prefix floor. Square that
nonnegative lower bound to recover the exact floor. -/
theorem gamma35000_floor (L : ℝ) : (35000 : ℝ) ≤ gamma35000Bound L := by
  have hs := Real.sq_sqrt (by norm_num only : (0 : ℝ) ≤ (40 / 99) * 35000)
  have hr : Real.sqrt ((40 / 99 : ℝ) * 35000) ≤
      gammaClippedPrefixRadius L 35000 (11147 / 2000) := le_max_left _ _
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans hr)).mpr hr
  change (35000 : ℝ) ≤
    (99 / 40 : ℝ) * gammaClippedPrefixRadius L 35000 (11147 / 2000) ^ 2
  linarith only [hs, hsq]

/-- For 209<=L<=240, the fixed value 35000 is below the clipped Gamma baseline.
Use the prefix floor followed by the strict 35000-prefix comparison.
This certifies the fixed Gaussian branch improvement below its upper endpoint. -/
theorem fixed35000_lt_gamma {L : ℝ} (hL : 209 ≤ L) (hU : L ≤ 240) :
    (35000 : ℝ) < gammaClippedUpper L := by
  exact (gamma35000_floor L).trans_lt (prefix35000_lt_upper hL hU)

/-- At log n=240, the public envelope is strictly below B6.
The fixed 35000 candidate is present, and the B6 lower comparison is strict.
The old Gaussian envelope equality remains unchanged for its original definition. -/
theorem midscaleWitnessEnvelope_lt_at240 {n : ℕ} (hL : Real.log n = 240) :
    midscaleWitnessEnvelope n < Analysis.gaussianMR6Bound (Real.log n) := by
  have hb := midscaleWitnessEnvelope_le_35000 (by linarith only [hL]) (by linarith only [hL])
  exact hb.trans_lt (Analysis.gaussianMR6_prefix35000 (by linarith only [hL]))

/-- For n>1 and log n>240, the public midscale envelope equals the Gaussian envelope.
Both low-region addition guards are inactive and the analytic base selects its
Gaussian branch. This preserves every existing high-range value. -/
theorem midscaleWitnessEnvelope_eq_high {n : ℕ} (hn : 1 < n) (hL : 240 < Real.log n) :
    midscaleWitnessEnvelope n = gaussianMRWitnessEnvelope n := by
  have hN := midscale_large_of_log (Nat.zero_lt_of_lt hn) (by linarith only [hL])
  have h2 : ¬n < 2047 := not_lt.mpr ((by norm_num only : 2047 ≤ 3000).trans hN)
  have h3 : ¬n < 3000 := not_lt.mpr hN
  have h61 : ¬Real.log n ≤ 286 / 25 := by linarith only [hL]
  have he : ¬Real.log n < 120 := by linarith only [hL]
  have h122 : ¬Real.log n ≤ 122 := by linarith only [hL]
  have h240 : ¬Real.log n < 240 := by linarith only [hL]
  have h2g : ¬(23 / 2 ≤ Real.log n ∧ Real.log n ≤ 240) := by
    intro h
    linarith only [h.2, hL]
  have hfg : ¬(63 ≤ Real.log n ∧ Real.log n ≤ 240) := by
    intro h
    linarith only [h.2, hL]
  simp only [midscaleWitnessEnvelope, ite_eq_right hfg, mrTwoStepEnvelope,
    ite_eq_right h2g, mrLowBase, ite_eq_right h2, ite_eq_right h3, mrAnalyticBase,
    ite_eq_right h61, ite_eq_right he, ite_eq_right h122, ite_eq_right h240]

/-- For n>1 and 23/2<=log n<=74/5, the public envelope equals the two-step cutoff.
The fixed Gaussian guard is inactive and the two-step candidate is below F8.
This certifies the single-expression row of the public interval table. -/
theorem midscaleWitnessEnvelope_eq_twoStep {n : ℕ} (hn : 1 < n)
    (hL : 23 / 2 ≤ Real.log n) (hU : Real.log n ≤ 74 / 5) :
    midscaleWitnessEnvelope n = LLS.PaperStatements.fullEndpointEvenTwoStepCutoff
      (Real.log n) := by
  have hN := midscale_large_of_log (Nat.zero_lt_of_lt hn) (by linarith only [hL])
  have h2 : ¬n < 2047 := not_lt.mpr ((by norm_num only : 2047 ≤ 3000).trans hN)
  have h3 : ¬n < 3000 := not_lt.mpr hN
  have h61 : ¬Real.log n ≤ 286 / 25 := by linarith only [hL]
  have he : Real.log n < 120 := by linarith only [hU]
  have h22 : Real.log n ≤ 22 := by linarith only [hU]
  have h2g : 23 / 2 ≤ Real.log n ∧ Real.log n ≤ 240 :=
    ⟨hL, by linarith only [hU]⟩
  have hfg : ¬(63 ≤ Real.log n ∧ Real.log n ≤ 240) := by
    intro h
    linarith only [h.1, hU]
  simp only [midscaleWitnessEnvelope, ite_eq_right hfg, mrTwoStepEnvelope,
    ite_eq_left h2g, mrLowBase, ite_eq_right h2, ite_eq_right h3, mrAnalyticBase,
    ite_eq_right h61, ite_eq_left he, endpointMidscaleBase, ite_eq_left h22]
  exact min_eq_right
    (LLS.PaperStatements.fullEndpointEvenTwoStepCutoff_lt_shifted_sevenFourths hL hU).le

/-- At log n=240, the public envelope equals the minimum of the two-step cutoff and 35000.
The B6 candidate is strictly larger than 35000, so it drops out of the minimum.
This identifies the endpoint value while preserving the Gaussian definition. -/
theorem midscaleWitnessEnvelope_eq_at240 {n : ℕ} (hn : 1 < n) (hL : Real.log n = 240) :
    midscaleWitnessEnvelope n = min
      (LLS.PaperStatements.fullEndpointEvenTwoStepCutoff (Real.log n)) 35000 := by
  have hN := midscale_large_of_log (Nat.zero_lt_of_lt hn) (by linarith only [hL])
  have h2 : ¬n < 2047 := not_lt.mpr ((by norm_num only : 2047 ≤ 3000).trans hN)
  have h3 : ¬n < 3000 := not_lt.mpr hN
  have h61 : ¬Real.log n ≤ 286 / 25 := by linarith only [hL]
  have he : ¬Real.log n < 120 := by linarith only [hL]
  have h122 : ¬Real.log n ≤ 122 := by linarith only [hL]
  have h240 : ¬Real.log n < 240 := by linarith only [hL]
  have h2g : 23 / 2 ≤ Real.log n ∧ Real.log n ≤ 240 :=
    ⟨by linarith only [hL], by linarith only [hL]⟩
  have hfg : 63 ≤ Real.log n ∧ Real.log n ≤ 240 :=
    ⟨by linarith only [hL], by linarith only [hL]⟩
  simp only [midscaleWitnessEnvelope, ite_eq_left hfg, mrTwoStepEnvelope,
    ite_eq_left h2g, mrLowBase, ite_eq_right h2, ite_eq_right h3, mrAnalyticBase,
    ite_eq_right h61, ite_eq_right he, ite_eq_right h122, ite_eq_right h240,
    gaussianMRWitnessEnvelope_eq240 (by linarith only [hL]) (by linarith only [hL])]
  rw [min_assoc, min_left_comm,
    min_eq_right (Analysis.gaussianMR6_prefix35000 (by linarith only [hL])).le]

end PseudoPrime.PrimeTestBounds.MillerRabin
