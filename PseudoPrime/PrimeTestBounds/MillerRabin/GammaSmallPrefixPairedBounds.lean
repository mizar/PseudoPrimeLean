/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaSeedPairedBounds
public import PseudoPrime.LLS.GammaCheckpoint1000
public import PseudoPrime.LLS.GammaSmallPrefixPairedNumerics
public import PseudoPrime.LLS.GammaSignedVariationPrincipalBounds
public import PseudoPrime.LLS.GammaPairedPolynomialSeparation

/-! # MR prime rejecting witnesses with a retained analytic Euler prefix -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Input: RH, L >= 215 and log(n) <= L. Claim: the exact MR budget with
prefix 1000 is below mu*log(n)+101/20. Use the analytic prefix lower bound
203/50 and the retained common cost 541/50. Role: remove the cutoff-50000
restriction without adding a prime-power certificate. -/
theorem gammaSignedPrefixMRBudget_small_prefix_lt_nearSquare (hRH : RiemannHypothesis) {L : ℝ}
    (hL : 215 ≤ L) {n : ℕ} (hlog : Real.log n ≤ L) :
    gammaSignedPrefixMRBudget n n ((2 / 5 : ℝ) * L ^ 2) 1000 <
      (11783423 / 25000000 : ℝ) * Real.log n + 101 / 20 := by
  let x := (2 / 5 : ℝ) * L ^ 2
  have hL0 : 0 < L := by linarith only [hL]
  have hx : 1 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (L - 215)]
  have hx0 := zero_lt_one.trans_le hx
  have hs := Real.sqrt_pos.mpr hx0
  have hroot : (79 / 125 : ℝ) * L ≤ Real.sqrt x := by
    apply (Real.le_sqrt (mul_nonneg (by norm_num only) hL0.le) hx0.le).mpr
    dsimp only [x]
    nlinarith only [sq_nonneg L]
  have hd :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 1) (by norm_num only)
      (by
        norm_num only; exact hx)
  simp only [one_mul] at hd
  have hl : 43 * x ^ (-9 / 16 : ℝ) ≤ 8 / 25 := by
    have hm := mul_le_mul_of_nonneg_left hd (by norm_num only : (0 : ℝ) ≤ 43)
    have hh : 43 * (1 / Real.sqrt x) ≤ (8 / 25 : ℝ) := by
      rw [mul_one_div, div_le_iff₀ hs]
      linarith only [hroot, hL]
    exact hm.trans hh
  have hp : ((7 / 6 : ℝ) * Real.log n + 4) / Real.sqrt x ≤ 2 := by
    rw [div_le_iff₀ hs]
    linarith only [hlog, hroot, hL]
  have hu := gammaSignedPrefixMRBudget_lt_precise_common_cost hRH n n x 1000
  norm_num only [Nat.floor_ofNat] at hu
  have hseed := LLS.gamma_prefix1000_lower_halfline hRH (le_refl (1000 : ℝ))
  norm_num only [Nat.floor_ofNat] at hseed
  linarith only [hu, hl, hp, hseed]

/-- Input: GRH, odd composite n and log(n) >= 215. Claim: a prime MR rejecting
base is at most (99/100)log(n)^2 and strictly below log(n)^2. Combine the retained
Euler prefix with the paired ramp bounds on the whole half-line.
Role: improve the previous log-400 analytic entrance without finite input checks. -/
theorem exists_prime_witness_le_even_paired_nearSquare_gamma_log_215 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 215 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (99 / 100 : ℝ) * (Real.log n) ^ 2 ∧
        (p : ℝ) < (Real.log n) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨hnOdd.pos.ne'⟩
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hnOdd.pos
  have ht := Real.log_le_sub_one_of_pos hn0
  have hn : 1 < n := by exact_mod_cast (show (1 : ℝ) < n by linarith only [ht, hL])
  have hq : 20000 ≤ n := by
    by_contra hq
    have hnR : (n : ℝ) ≤ 46000 := by
      exact_mod_cast (show n ≤ 46000 by linarith only [lt_of_not_ge hq])
    have hl := Real.log_le_log hn0 hnR
    linarith only [hl, Analysis.log_46000_lt_eleven, hL]
  let x := (2 / 5 : ℝ) * (Real.log n) ^ 2
  have hx : 2 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (Real.log n - 215)]
  have hx1 : 1 ≤ x := le_trans (by norm_num only) hx
  have he := LLS.gamma_small_prefix_nearSquare_budgets hL
  have hP := LLS.gamma_level_one_sum_upper_signed_variation hGRH.riemann hx1
  have hT := LLS.gamma_ramp_sum_lower_paired hGRH.riemann hx1
  have hu := gammaSignedPrefixMRBudget_small_prefix_lt_nearSquare hGRH.riemann hL (le_refl _)
  have hgap :
    gammaSignedPrefixMRBudget n n x 1000 <
      2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
        (∑' k : ℕ,
            LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re := by
    nlinarith only [hu, hP, hT, he.1, he.2.1, he.2.2, hL]
  obtain ⟨p, hp, hb, hf⟩ :=
    exists_prime_witness_of_signed_prefix_gap hn hnOdd hnComposite hGRH hq (le_refl n) hx
      (by norm_num only : (0 : ℝ) ≤ 1000)
      (show (1000 : ℝ) ≤ (99 / 40 : ℝ) * x by
        dsimp only [x]
        nlinarith only [hL, sq_nonneg (Real.log n - 215)])
      hgap
  have hsq : 0 < (Real.log n) ^ 2 := sq_pos_of_pos (by linarith only [hL])
  dsimp only [x] at hb
  refine ⟨p, hp, ?_, ?_, hf⟩
  · nlinarith only [hb]
  · nlinarith only [hb, hsq]

/-- Under the same GRH, odd-composite and log(n) >= 215 hypotheses, a least
prime MR rejecting base satisfies the displayed bound. Minimize the unbounded
prime rejection predicate. Role: expose a least-witness version of the half-line bound. -/
theorem exists_least_prime_witness_le_even_paired_nearSquare_gamma_log_215 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 215 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ (99 / 100 : ℝ) * (Real.log n) ^ 2 ∧
        ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → p ≤ r := by
  classical
  obtain ⟨p, hp, hb, _, hf⟩ :=
    exists_prime_witness_le_even_paired_nearSquare_gamma_log_215 hnOdd hnComposite hGRH hL
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := ⟨p, hp, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hf⟩)).trans hb, fun r hr hf ↦
      Nat.find_min' hex ⟨hr, hf⟩⟩

/-- Under the same hypotheses, a prime below the stated bound fails the initial
power equality and every negative-one equality in the standard binary decomposition
of n-1. Apply the characterization of MR rejection. Role: expose the actual power tests. -/
theorem exists_prime_rejecting_powers_le_even_paired_nearSquare_gamma_log_215 {n : ℕ}
    (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 215 ≤ Real.log n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1);
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (99 / 100 : ℝ) * (Real.log n) ^ 2 ∧
        (p : ZMod n) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ -1 := by
  obtain ⟨p, hp, hb, _, hf⟩ :=
    exists_prime_witness_le_even_paired_nearSquare_gamma_log_215 hnOdd hnComposite hGRH hL
  exact ⟨p, hp, hb, PrimeTest.not_strongMillerRabinPass_iff.mp hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Input: RH, log(n) <= L, scale x >= 1, any prefix lower bound C and
positive scalar polynomial data. Claim: the exact MR budget is below the
actual ramp-principal gap. Use the common Gamma cost and signed principal
upper bound. Role: connect arbitrary polynomial bounds to MR witnesses. -/
theorem gammaSignedPrefixMRBudget_lt_gap_of_polynomial (hRH : RiemannHypothesis) {n : ℕ}
    {L x b C R u : ℝ} (hlogn : Real.log n ≤ L) (hx : 1 ≤ x)
    (hprefix : C ≤ ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)
    (hroot : Real.sqrt x ≤ R) (hlog : Real.log ((101 / 40 : ℝ) * x) ≤ u)
    (hcoef : 0 ≤ (11783423 / 25000000 : ℝ) * L + 541 / 50 - 2 * C + 328051 / 197600)
    (hpoly :
      0 <
        ((83125234337 / 100000000000 : ℝ) - 231 / 24700) * x -
          ((11783423 / 25000000 : ℝ) * L + 541 / 50 - 2 * C + 328051 / 197600) * R -
          (38017647 / 988000 : ℝ) * u -
          (7 / 6 : ℝ) * L -
          14082763 / 197600) :
    gammaSignedPrefixMRBudget n n x b <
      2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
        (∑' k : ℕ,
            LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re := by
  have hs := Real.sqrt_pos.mpr (zero_lt_one.trans_le hx)
  have hu := gammaSignedPrefixMRBudget_lt_precise_common_cost hRH n n x b
  have hpole :=
    div_le_div_of_nonneg_right
      (show (7 / 6 : ℝ) * Real.log n + 4 ≤ (7 / 6 : ℝ) * L + 4 by linarith only [hlogn]) hs.le
  have hcost := LLS.gamma_paired_scalar_lt_gap hx hroot hlog hcoef hpoly
  have hP := LLS.gamma_level_one_sum_upper_signed_variation hRH hx
  have hT := LLS.gamma_ramp_sum_lower_paired hRH hx
  dsimp only [LLS.gammaSignedVariationPrincipalCap] at hcost
  nlinarith only [hu, hprefix, hlogn, hpole, hcost, hP, hT]

end PseudoPrime.PrimeTestBounds.MillerRabin

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Input: RH, L >= 205 and log(n) <= L. Claim: the exact prefix-1000 MR
budget is below the actual ramp-principal gap. Supply the proved tangent
polynomial profile and analytic prefix. Role: lower the whole-half-line
MR entrance without new prime-power or interval certificates. -/
theorem gammaSignedPrefixMRBudget_gap_of_log_ge_205 (hRH : RiemannHypothesis) {n : ℕ} {L : ℝ}
    (hL : 205 ≤ L) (hlog : Real.log n ≤ L) :
    gammaSignedPrefixMRBudget n n ((2 / 5 : ℝ) * L ^ 2) 1000 <
      2 *
          (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum ((2 / 5 : ℝ) * L ^ 2) /
            Real.sqrt ((2 / 5 : ℝ) * L ^ 2)) -
        (∑' k : ℕ,
            LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1)
              ((2 / 5 : ℝ) * L ^ 2) k).re := by
  obtain ⟨hroot, hlogx, hpoly⟩ := LLS.gamma_paired_polynomial_profile_of_log_ge_205 hL
  have hx : 1 ≤ (2 / 5 : ℝ) * L ^ 2 := by nlinarith only [hL, sq_nonneg (L - 205)]
  have hp := LLS.gamma_prefix1000_lower_halfline hRH (le_refl (1000 : ℝ))
  exact
    gammaSignedPrefixMRBudget_lt_gap_of_polynomial hRH hlog hx hp hroot hlogx
      (by linarith only [hL]) hpoly

end PseudoPrime.PrimeTestBounds.MillerRabin

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Input: GRH, odd composite n and log(n) >= 205. Claim: a prime MR rejecting
base is at most (99/100)log(n)^2 and strictly below log(n)^2. Combine the retained
Euler prefix with the paired ramp bounds on the whole half-line.
Role: improve the previous log-400 analytic entrance without finite input checks. -/
theorem exists_prime_witness_le_even_paired_nearSquare_gamma_log_205 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 205 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (99 / 100 : ℝ) * (Real.log n) ^ 2 ∧
        (p : ℝ) < (Real.log n) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨hnOdd.pos.ne'⟩
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hnOdd.pos
  have ht := Real.log_le_sub_one_of_pos hn0
  have hn : 1 < n := by exact_mod_cast (show (1 : ℝ) < n by linarith only [ht, hL])
  have hq : 20000 ≤ n := by
    by_contra hq
    have hnR : (n : ℝ) ≤ 46000 := by
      exact_mod_cast (show n ≤ 46000 by linarith only [lt_of_not_ge hq])
    have hl := Real.log_le_log hn0 hnR
    linarith only [hl, Analysis.log_46000_lt_eleven, hL]
  let x := (2 / 5 : ℝ) * (Real.log n) ^ 2
  have hx : 2 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (Real.log n - 205)]
  have hgap := gammaSignedPrefixMRBudget_gap_of_log_ge_205 hGRH.riemann hL (le_refl _)
  obtain ⟨p, hp, hb, hf⟩ :=
    exists_prime_witness_of_signed_prefix_gap hn hnOdd hnComposite hGRH hq (le_refl n) hx
      (by norm_num only : (0 : ℝ) ≤ 1000)
      (show (1000 : ℝ) ≤ (99 / 40 : ℝ) * x by
        dsimp only [x]
        nlinarith only [hL, sq_nonneg (Real.log n - 205)])
      hgap
  have hsq : 0 < (Real.log n) ^ 2 := sq_pos_of_pos (by linarith only [hL])
  dsimp only [x] at hb
  refine ⟨p, hp, ?_, ?_, hf⟩
  · nlinarith only [hb]
  · nlinarith only [hb, hsq]

/-- Under the same GRH, odd-composite and log(n) >= 205 hypotheses, a least
prime MR rejecting base satisfies the displayed bound. Minimize the unbounded
prime rejection predicate. Role: expose a least-witness version of the half-line bound. -/
theorem exists_least_prime_witness_le_even_paired_nearSquare_gamma_log_205 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 205 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ (99 / 100 : ℝ) * (Real.log n) ^ 2 ∧
        ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → p ≤ r := by
  classical
  obtain ⟨p, hp, hb, _, hf⟩ :=
    exists_prime_witness_le_even_paired_nearSquare_gamma_log_205 hnOdd hnComposite hGRH hL
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := ⟨p, hp, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hf⟩)).trans hb, fun r hr hf ↦
      Nat.find_min' hex ⟨hr, hf⟩⟩

/-- Under the same hypotheses, a prime below the stated bound fails the initial
power equality and every negative-one equality in the standard binary decomposition
of n-1. Apply the characterization of MR rejection. Role: expose the actual power tests. -/
theorem exists_prime_rejecting_powers_le_even_paired_nearSquare_gamma_log_205 {n : ℕ}
    (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 205 ≤ Real.log n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1);
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (99 / 100 : ℝ) * (Real.log n) ^ 2 ∧
        (p : ZMod n) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ -1 := by
  obtain ⟨p, hp, hb, _, hf⟩ :=
    exists_prime_witness_le_even_paired_nearSquare_gamma_log_205 hnOdd hnComposite hGRH hL
  exact ⟨p, hp, hb, PrimeTest.not_strongMillerRabinPass_iff.mp hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
