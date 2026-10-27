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
public import PseudoPrime.PrimeTestBounds.MillerRabin.ReciprocalGapEvenAmbient

/-! # Miller-Rabin witnesses from the parity-refined endpoint polynomial -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A positive exact even-endpoint gap at the ambient logarithmic scale gives a
strong Miller--Rabin rejecting prime through the squared radius. -/
theorem exists_prime_reject_of_even_exact_endpoint_gap_pos {N : ℕ} [NeZero N] (hn : 1 < N)
    (ho : Odd N) (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {y : ℝ} (hy : 8 ≤ y)
    (hgap :
      0 <
        LLS.PaperStatements.fullEndpointEvenExactComparisonGap (Real.log N) (2096 / 1831) y
          (Real.log y)) :
    let (s, a) := Nat.maxPowDvdDiv 2 (N - 1)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ y ^ 2 ∧
        (p : ZMod N) ^ a ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod N) ^ (2 ^ j * a) ≠ -1 := by
  obtain ⟨χ, hne, hpass⟩ := exists_character_trivial_on_pass hn ho hc
  have heven := character_even_of_trivial_on_pass hn ho hpass
  obtain ⟨p, hp, hpx, hv⟩ :=
    LLS.PaperStatements.exists_prime_ne_one_of_positive_exact_even_endpoint_gap χ hne heven hGRH hy
      hgap
  refine ⟨p, hp, hpx, ?_⟩
  exact PrimeTest.not_strongMillerRabinPass_iff.mp (fun ha ↦ hv (hpass p ha))

/-- For an odd composite `N > 1` under GRH, a positive shifted endpoint
polynomial at a radius `y >= 8` gives a rejecting prime at most `y^2`. Choose a
character trivial on passing residues; its evenness follows because `-1` passes. -/
theorem exists_prime_reject_of_even_shifted_endpoint_polynomial_pos {N : ℕ} [NeZero N] (hn : 1 < N)
    (ho : Odd N) (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {y : ℝ} (hy : 8 ≤ y)
    (hpoly :
      0 <
        LLS.PaperStatements.fullEndpointPolynomial (Real.log N - 9 / 8) (2096 / 1831) y
          (Real.log y)) :
    let (s, a) := Nat.maxPowDvdDiv 2 (N - 1)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ y ^ 2 ∧
        (p : ZMod N) ^ a ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod N) ^ (2 ^ j * a) ≠ -1 := by
  have hgap :
    0 <
      LLS.PaperStatements.fullEndpointEvenExactComparisonGap (Real.log N) (2096 / 1831) y
        (Real.log y) := by
    by_cases hy128 : y ≤ 128
    · have hpolyTransfer :=
        LLS.PaperStatements.fullEndpointPolynomial_lt_even_star_shift_7over4_of_radius_range hy
          hy128 (L := Real.log N - 9 / 8) (P := (2096 / 1831 : ℝ))
      have hstar :
        0 <
          LLS.PaperStatements.fullEndpointEvenStarShiftPolynomial (Real.log N - 9 / 8 + 29 / 100)
            (2096 / 1831) y (Real.log y) :=
        lt_trans hpoly hpolyTransfer
      have hshift : Real.log N + 5 / 8 - 73 / 50 = Real.log N - 9 / 8 + 29 / 100 := by ring
      have hbridge :=
        LLS.PaperStatements.fullEndpointEvenStarShiftPolynomial_le_exact_comparison_gap (L :=
          Real.log N + 5 / 8) (P := (2096 / 1831 : ℝ)) (y := y) (z := Real.log y)
          (by linarith only [hy] : y ≠ 0) (Real.log_nonneg (by linarith only [hy] : (1 : ℝ) ≤ y))
          (by norm_num only : (9 / 8 : ℝ) ≤ 2096 / 1831)
      rw [hshift] at hbridge
      have hgapShifted :
        0 <
          LLS.PaperStatements.fullEndpointEvenExactComparisonGap (Real.log N + 5 / 8) (2096 / 1831)
            y (Real.log y) :=
        lt_of_lt_of_le hstar hbridge
      have hmono :=
        LLS.PaperStatements.fullEndpointEvenExactComparisonGap_antitone_level (L := Real.log N)
          (K := Real.log N + 5 / 8) (P := (2096 / 1831 : ℝ)) (y := y) (z := Real.log y)
          (by linarith only [hy]) (Real.log_nonneg (by linarith only [hy] : (1 : ℝ) ≤ y))
          (by linarith only : Real.log N ≤ Real.log N + 5 / 8)
      exact lt_of_lt_of_le hgapShifted hmono
    · have hpolyTransfer :=
        LLS.PaperStatements.fullEndpointPolynomial_lt_even_star_shift hy (L := Real.log N - 9 / 8)
          (P := (2096 / 1831 : ℝ))
      have hstar := lt_trans hpoly hpolyTransfer
      have hshift : Real.log N + 67 / 200 - 73 / 50 = Real.log N - 9 / 8 := by ring
      have hbridge :=
        LLS.PaperStatements.fullEndpointEvenStarShiftPolynomial_le_exact_comparison_gap (L :=
          Real.log N + 67 / 200) (P := (2096 / 1831 : ℝ)) (y := y) (z := Real.log y)
          (by linarith only [hy] : y ≠ 0) (Real.log_nonneg (by linarith only [hy] : (1 : ℝ) ≤ y))
          (by norm_num only : (9 / 8 : ℝ) ≤ 2096 / 1831)
      rw [hshift] at hbridge
      have hgapShifted :
        0 <
          LLS.PaperStatements.fullEndpointEvenExactComparisonGap (Real.log N + 67 / 200)
            (2096 / 1831) y (Real.log y) :=
        lt_of_lt_of_le hstar hbridge
      have hmono :=
        LLS.PaperStatements.fullEndpointEvenExactComparisonGap_antitone_level (L := Real.log N)
          (K := Real.log N + 67 / 200) (P := (2096 / 1831 : ℝ)) (y := y) (z := Real.log y)
          (by linarith only [hy]) (Real.log_nonneg (by linarith only [hy] : (1 : ℝ) ≤ y))
          (by linarith only : Real.log N ≤ Real.log N + 67 / 200)
      exact lt_of_lt_of_le hgapShifted hmono
  exact exists_prime_reject_of_even_exact_endpoint_gap_pos hn ho hc hGRH hy hgap

/-- Across the shifted five-piece middle range, an odd composite has a rejecting
prime below the square of the existing affine radius evaluated at `log N - 9/8`.
The parity-refined reciprocal endpoint cap makes this radius valid without any
squarefreeness or Fermat subgroup-index condition. -/
theorem exists_prime_reject_le_even_shifted_midscale_radius_sq {N : ℕ} [NeZero N] (hn : 1 < N)
    (ho : Odd N) (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : 5581 / 200 ≤ Real.log N) (hhi : Real.log N ≤ 52763 / 200) :
    let L := Real.log N - 9 / 8
    let y := LLS.PaperStatements.midscaleEndpointRadius L
    let (s, a) := Nat.maxPowDvdDiv 2 (N - 1)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ y ^ 2 ∧
        (p : ZMod N) ^ a ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod N) ^ (2 ^ j * a) ≠ -1 := by
  let L := Real.log N - 9 / 8
  let y := LLS.PaperStatements.midscaleEndpointRadius L
  have hLlo : (1339 / 50 : ℝ) ≤ L := by
    dsimp only [L]; nlinarith only [hlo]
  have hLhi : L ≤ 26269 / 100 := by
    dsimp only [L]; nlinarith only [hhi]
  have hdata := LLS.PaperStatements.midscaleEndpointRadius_data hLlo hLhi
  have hy : 8 ≤ y := by
    dsimp only [y]; linarith only [hdata.1]
  dsimp only [L, y]
  exact exists_prime_reject_of_even_shifted_endpoint_polynomial_pos hn ho hc hGRH hy hdata.2

/-- For `log N <= 56/5`, the direct endpoint gap at radius eight gives
a rejecting prime at most 64. This is the fixed-radius bridge into the improved
logarithmic branches. -/
theorem exists_prime_reject_le_even_shifted_sixty_four {N : ℕ} [NeZero N] (hn : 1 < N) (ho : Odd N)
    (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log N ≤ 56 / 5) :
    let (s, a) := Nat.maxPowDvdDiv 2 (N - 1)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 64 ∧ (p : ZMod N) ^ a ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod N) ^ (2 ^ j * a) ≠ -1 := by
  have hgap :
    0 <
      LLS.PaperStatements.fullEndpointEvenExactComparisonGap (Real.log N) (2096 / 1831) 8
        (Real.log 8) :=
    LLS.PaperStatements.fullEndpointEvenExactComparisonGap_pos_at_eight hL
  obtain ⟨p, hp, hpx, hpow, hall⟩ :=
    exists_prime_reject_of_even_exact_endpoint_gap_pos hn ho hc hGRH (by norm_num only) hgap
  refine ⟨p, hp, ?_, hpow, hall⟩
  nlinarith only [hpx]

/-- Up to `log N = 144/5`, radius 24 certifies a rejecting prime at most
576 using the shifted even endpoint. This fixed branch overlaps the shifted
logarithmic bounds and reaches the entrance of the five-piece radius. -/
theorem exists_prime_reject_le_even_shifted_fiveHundredSeventySix {N : ℕ} [NeZero N] (hn : 1 < N)
    (ho : Odd N) (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log N ≤ 144 / 5) :
    let (s, a) := Nat.maxPowDvdDiv 2 (N - 1)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 576 ∧
        (p : ZMod N) ^ a ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod N) ^ (2 ^ j * a) ≠ -1 := by
  have hgap :
    0 <
      LLS.PaperStatements.fullEndpointEvenExactComparisonGap (Real.log N) (2096 / 1831) 24
        (Real.log 24) :=
    LLS.PaperStatements.fullEndpointEvenExactComparisonGap_pos_at_twentyFour hL
  obtain ⟨p, hp, hpx, hpow, hall⟩ :=
    exists_prime_reject_of_even_exact_endpoint_gap_pos hn ho hc hGRH (by norm_num only) hgap
  refine ⟨p, hp, ?_, hpow, hall⟩
  nlinarith only [hpx]

/-- On `81/8 <= log N <= 171/8`, a shifted radius `8/9` times the level
improves the corresponding unshifted endpoint bound. The estimate applies to all
odd composites and carries no squarefree or Fermat-index hypothesis. -/
theorem exists_prime_reject_le_even_shifted_eightNinths_sq {N : ℕ} [NeZero N] (hn : 1 < N)
    (ho : Odd N) (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hLlo : 81 / 8 ≤ Real.log N) (hLhi : Real.log N ≤ 171 / 8) :
    let (s, a) := Nat.maxPowDvdDiv 2 (N - 1)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (64 / 81 : ℝ) * (Real.log N - 9 / 8) ^ 2 ∧
        (p : ZMod N) ^ a ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod N) ^ (2 ^ j * a) ≠ -1 := by
  let L := Real.log N - 9 / 8
  have hL9 : 9 ≤ L := by
    dsimp only [L]; nlinarith only [hLlo]
  have hLhi' : L ≤ 81 / 4 := by
    dsimp only [L]; nlinarith only [hLhi]
  let y := (8 / 9 : ℝ) * L
  have hy : 8 ≤ y := by
    dsimp only [y]; nlinarith only [hL9]
  have hpoly := LLS.PaperStatements.fullEndpoint_polynomial_pos_eightNinths_log_interval hL9 hLhi'
  obtain ⟨p, hp, hpx, hpow, hall⟩ :=
    exists_prime_reject_of_even_shifted_endpoint_polynomial_pos hn ho hc hGRH hy hpoly
  refine ⟨p, hp, ?_, hpow, hall⟩
  have heq : y ^ 2 = (64 / 81 : ℝ) * (Real.log N - 9 / 8) ^ 2 := by
    dsimp only [y, L]
    ring
  rw [heq] at hpx
  exact hpx

/-- On `81/8 <= log N <= 217/8`, a shifted radius `9/10` times the level
gives a second all-input endpoint bound. It overlaps the tighter `8/9` branch,
which remains the envelope through `171/8`. -/
theorem exists_prime_reject_le_even_shifted_nineTenths_sq {N : ℕ} [NeZero N] (hn : 1 < N)
    (ho : Odd N) (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hLlo : 81 / 8 ≤ Real.log N) (hLhi : Real.log N ≤ 217 / 8) :
    let (s, a) := Nat.maxPowDvdDiv 2 (N - 1)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (81 / 100 : ℝ) * (Real.log N - 9 / 8) ^ 2 ∧
        (p : ZMod N) ^ a ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod N) ^ (2 ^ j * a) ≠ -1 := by
  let L := Real.log N - 9 / 8
  have hL9 : 9 ≤ L := by
    dsimp only [L]; nlinarith only [hLlo]
  have hL26 : L ≤ 26 := by
    dsimp only [L]; nlinarith only [hLhi]
  let y := (9 / 10 : ℝ) * L
  have hy : 8 ≤ y := by
    dsimp only [y]; nlinarith only [hL9]
  have hpoly := LLS.PaperStatements.fullEndpoint_polynomial_pos_eightyOne_log_interval hL9 hL26
  obtain ⟨p, hp, hpx, hpow, hall⟩ :=
    exists_prime_reject_of_even_shifted_endpoint_polynomial_pos hn ho hc hGRH hy hpoly
  refine ⟨p, hp, ?_, hpow, hall⟩
  have heq : y ^ 2 = (81 / 100 : ℝ) * (Real.log N - 9 / 8) ^ 2 := by
    dsimp only [y, L]
    ring
  rw [heq] at hpx
  exact hpx

/-- A bounded rejecting prime yields a least rejecting prime with the same
bound. This bridge lets the endpoint witness theorems expose minimum-witness
results without repeating the `Nat.find` argument. -/
theorem exists_least_prime_reject_of_exists_prime_reject {N : ℕ} [NeZero N] {B : ℝ}
    (h : ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass N (p : ZMod N)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ B ∧
        ¬PrimeTest.StrongMillerRabinPass N (p : ZMod N) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass N (q : ZMod N) → p ≤ q := by
  classical
  let hex : ∃ q : ℕ, q.Prime ∧ ¬PrimeTest.StrongMillerRabinPass N (q : ZMod N) := by
    exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2.2⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, ?_, (Nat.find_spec hex).2, ?_⟩
  · exact
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨h.choose_spec.1, h.choose_spec.2.2⟩)).trans
        h.choose_spec.2.1
  · intro q hq hf
    exact Nat.find_min' hex ⟨hq, hf⟩

/-- For every odd composite with logarithmic scale at least `23/2`, the two-step
endpoint correction gives a rejecting prime below the square of its second
corrected radius. -/
theorem exists_prime_reject_le_even_twoStep_cutoff {N : ℕ} [NeZero N] (hn : 1 < N) (ho : Odd N)
    (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 23 / 2 ≤ Real.log N) :
    let (s, a) := Nat.maxPowDvdDiv 2 (N - 1)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ LLS.PaperStatements.fullEndpointEvenTwoStepCutoff (Real.log N) ∧
        (p : ZMod N) ^ a ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod N) ^ (2 ^ j * a) ≠ -1 := by
  have ha8 : 8 ≤ LLS.PaperStatements.fullEndpointEvenCorrectionFirstRadius (Real.log N) := by
    unfold LLS.PaperStatements.fullEndpointEvenCorrectionFirstRadius
    exact le_max_left _ _
  have hab := LLS.PaperStatements.fullEndpointEvenCorrectionSecondRadius_gt_first hL
  have hy : 8 ≤ LLS.PaperStatements.fullEndpointEvenCorrectionSecondRadius (Real.log N) :=
    le_trans ha8 hab.le
  have hgap := LLS.PaperStatements.fullEndpointEvenTwoStepGap_pos hL
  dsimp only [LLS.PaperStatements.fullEndpointEvenTwoStepCutoff]
  exact exists_prime_reject_of_even_exact_endpoint_gap_pos hn ho hc hGRH hy hgap

/-- Least-prime form of the two-step endpoint cutoff. -/
theorem exists_least_prime_reject_le_even_twoStep_cutoff {N : ℕ} [NeZero N] (hn : 1 < N)
    (ho : Odd N) (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 23 / 2 ≤ Real.log N) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ LLS.PaperStatements.fullEndpointEvenTwoStepCutoff (Real.log N) ∧
        ¬PrimeTest.StrongMillerRabinPass N (p : ZMod N) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass N (q : ZMod N) → p ≤ q := by
  obtain ⟨p, hp, hb, hpow, hrest⟩ := exists_prime_reject_le_even_twoStep_cutoff hn ho hc hGRH hL
  apply exists_least_prime_reject_of_exists_prime_reject
  refine ⟨p, hp, hb, ?_⟩
  exact PrimeTest.not_strongMillerRabinPass_iff.mpr ⟨hpow, hrest⟩

/-- Pointwise minimum of the two-step endpoint cutoff and the earlier
73/50-shifted quadratic on their common interval. -/
noncomputable def evenTwoStepEndpointEnvelope (L : ℝ) : ℝ :=
  min (LLS.PaperStatements.fullEndpointEvenTwoStepCutoff L) ((64 / 81 : ℝ) * (L - 73 / 50) ^ 2)

/-- On `23/2 ≤ log N ≤ 74/5`, the least rejecting prime is bounded by the
minimum of the two-step endpoint cutoff and its overlapping `73/50`-shifted
quadratic. The two-step comparison proves that this minimum equals the new
cutoff throughout the interval. -/
theorem exists_least_prime_reject_le_evenTwoStepEndpointEnvelope {N : ℕ} [NeZero N] (hn : 1 < N)
    (ho : Odd N) (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hLlo : 23 / 2 ≤ Real.log N) (hLhi : Real.log N ≤ 74 / 5) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ evenTwoStepEndpointEnvelope (Real.log N) ∧
        ¬PrimeTest.StrongMillerRabinPass N (p : ZMod N) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass N (q : ZMod N) → p ≤ q := by
  obtain ⟨p, hp, hb, hreject, hmin⟩ :=
    exists_least_prime_reject_le_even_twoStep_cutoff hn ho hc hGRH hLlo
  have hcmp :=
    LLS.PaperStatements.fullEndpointEvenTwoStepCutoff_lt_shifted_eightNinths hLlo
      (by linarith only [hLhi] : Real.log N ≤ 428 / 25)
  refine ⟨p, hp, ?_, hreject, hmin⟩
  rw [evenTwoStepEndpointEnvelope, min_eq_left (le_of_lt hcmp)]
  exact hb

/-- Least-prime version of the shifted eight-ninths endpoint bound. -/
theorem exists_least_prime_reject_le_even_shifted_eightNinths_sq {N : ℕ} [NeZero N] (hn : 1 < N)
    (ho : Odd N) (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hLlo : 81 / 8 ≤ Real.log N) (hLhi : Real.log N ≤ 171 / 8) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (64 / 81 : ℝ) * (Real.log N - 9 / 8) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass N (p : ZMod N) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass N (q : ZMod N) → p ≤ q := by
  obtain ⟨p, hp, hb, hpow, hrest⟩ :=
    exists_prime_reject_le_even_shifted_eightNinths_sq hn ho hc hGRH hLlo hLhi
  apply exists_least_prime_reject_of_exists_prime_reject
  refine ⟨p, hp, hb, ?_⟩
  exact PrimeTest.not_strongMillerRabinPass_iff.mpr ⟨hpow, hrest⟩

/-- Least-prime version of the shifted nine-tenths endpoint bound. -/
theorem exists_least_prime_reject_le_even_shifted_nineTenths_sq {N : ℕ} [NeZero N] (hn : 1 < N)
    (ho : Odd N) (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hLlo : 81 / 8 ≤ Real.log N) (hLhi : Real.log N ≤ 217 / 8) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (81 / 100 : ℝ) * (Real.log N - 9 / 8) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass N (p : ZMod N) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass N (q : ZMod N) → p ≤ q := by
  obtain ⟨p, hp, hb, hpow, hrest⟩ :=
    exists_prime_reject_le_even_shifted_nineTenths_sq hn ho hc hGRH hLlo hLhi
  apply exists_least_prime_reject_of_exists_prime_reject
  refine ⟨p, hp, hb, ?_⟩
  exact PrimeTest.not_strongMillerRabinPass_iff.mpr ⟨hpow, hrest⟩

/-- Least-prime version of the fixed radius-24 endpoint bound. -/
theorem exists_least_prime_reject_le_even_shifted_fiveHundredSeventySix {N : ℕ} [NeZero N]
    (hn : 1 < N) (ho : Odd N) (hc : ¬N.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log N ≤ 144 / 5) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 576 ∧
        ¬PrimeTest.StrongMillerRabinPass N (p : ZMod N) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass N (q : ZMod N) → p ≤ q := by
  obtain ⟨p, hp, hb, hpow, hrest⟩ :=
    exists_prime_reject_le_even_shifted_fiveHundredSeventySix hn ho hc hGRH hL
  apply exists_least_prime_reject_of_exists_prime_reject
  refine ⟨p, hp, hb, ?_⟩
  exact PrimeTest.not_strongMillerRabinPass_iff.mpr ⟨hpow, hrest⟩

/-- Least-prime version of the shifted five-piece endpoint radius bound. -/
theorem exists_least_prime_reject_le_even_shifted_midscale_radius_sq {N : ℕ} [NeZero N] (hn : 1 < N)
    (ho : Odd N) (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : 5581 / 200 ≤ Real.log N) (hhi : Real.log N ≤ 52763 / 200) :
    let y := LLS.PaperStatements.midscaleEndpointRadius (Real.log N - 9 / 8)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ y ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass N (p : ZMod N) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass N (q : ZMod N) → p ≤ q := by
  dsimp only
  obtain ⟨p, hp, hb, hpow, hrest⟩ :=
    exists_prime_reject_le_even_shifted_midscale_radius_sq hn ho hc hGRH hlo hhi
  apply exists_least_prime_reject_of_exists_prime_reject
  refine ⟨p, hp, hb, ?_⟩
  exact PrimeTest.not_strongMillerRabinPass_iff.mpr ⟨hpow, hrest⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
