/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaEvenPairedBounds
public import PseudoPrime.LLS.RiemannOneSidedCheckpoint
public import PseudoPrime.LLS.GammaSeedPairedNumerics
public import PseudoPrime.LLS.GammaRetainedCommonCostBounds

/-! # MR prime rejecting witnesses from log 225 with a retained Euler prefix -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, the exact common Euler and even Gamma cost gives fixed allowance
541/50, retaining any finite prefix. Role: supply a sharper MR scalar budget
without changing the contour or subgroup comparison. -/
theorem gammaSignedPrefixMRBudget_lt_precise_common_cost (hRH : RiemannHypothesis) (n Q : ℕ)
    (x b : ℝ) :
    gammaSignedPrefixMRBudget n Q x b <
      (11783423 / 25000000 : ℝ) * Real.log n + 541 / 50 -
          2 * (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  have h :=
    LLS.gamma_even_common_cost_lt_precise hRH
      AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even
  have hf : (1 : DirichletCharacter ℂ 1).gammaFactor = Complex.Gammaℝ :=
    funext AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even.gammaFactor_def
  rw [hf] at h
  dsimp only [gammaSignedPrefixMRBudget]
  linarith only [h]

/-- Input: RH, L >= 225 and log(n) <= L. Claim: the MR budget at x=(2/5)L^2
and prefix 50000 is less than mu*log(n)+7/4. Retain the analytic Euler prefix
28493/5000, even Gamma gain, and pole and contour bounds. Role: lower the analytic
entrance without new arithmetic certificates. -/
theorem gammaSignedPrefixMRBudget_seed_lt_even_nearSquare (hRH : RiemannHypothesis) {L : ℝ}
    (hL : 225 ≤ L) {n : ℕ} (hlog : Real.log n ≤ L) :
    gammaSignedPrefixMRBudget n n ((2 / 5 : ℝ) * L ^ 2) 50000 <
      (11783423 / 25000000 : ℝ) * Real.log n + 7 / 4 := by
  let x := (2 / 5 : ℝ) * L ^ 2
  have hL0 : 0 < L := by linarith only [hL]
  have hx : 1 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (L - 225)]
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
  have hl : 43 * x ^ (-9 / 16 : ℝ) ≤ 31 / 100 := by
    have hm := mul_le_mul_of_nonneg_left hd (by norm_num only : (0 : ℝ) ≤ 43)
    have hh : 43 * (1 / Real.sqrt x) ≤ (31 / 100 : ℝ) := by
      rw [mul_one_div, div_le_iff₀ hs]
      linarith only [hroot, hL]
    exact hm.trans hh
  have hp : ((7 / 6 : ℝ) * Real.log n + 4) / Real.sqrt x ≤ 2 := by
    rw [div_le_iff₀ hs]
    linarith only [hlog, hroot, hL]
  have hu := gammaSignedPrefixMRBudget_lt_precise_common_cost hRH n n x 50000
  norm_num only [Nat.floor_ofNat] at hu
  have hseed := LLS.gamma_prefix50000_lower_asymmetric hRH (le_refl (50000 : ℝ))
  norm_num only [Nat.floor_ofNat] at hseed
  linarith only [hu, hl, hp, hseed]

/-- Input: GRH, odd composite n and log(n) >= 225. Claim: a prime MR rejecting
base is at most (99/100)log(n)^2 and strictly below log(n)^2. Combine the retained
Euler prefix with the paired ramp bounds on the whole half-line.
Role: improve the previous log-400 analytic entrance without finite input checks. -/
theorem exists_prime_witness_le_even_paired_nearSquare_gamma_log_225 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 225 ≤ Real.log n) :
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
    nlinarith only [hL, sq_nonneg (Real.log n - 225)]
  have hx1 : 1 ≤ x := le_trans (by norm_num only) hx
  have he := LLS.gamma_seed_paired_nearSquare_budgets hL
  have hP := LLS.gamma_level_one_sum_upper_variable hGRH.riemann hx1
  have hT := LLS.gamma_ramp_sum_lower_paired hGRH.riemann hx1
  have hu := gammaSignedPrefixMRBudget_seed_lt_even_nearSquare hGRH.riemann hL (le_refl _)
  have hgap :
    gammaSignedPrefixMRBudget n n x 50000 <
      2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
        (∑' k : ℕ,
            LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re := by
    nlinarith only [hu, hP, hT, he.1, he.2.1, he.2.2, hL]
  obtain ⟨p, hp, hb, hf⟩ :=
    exists_prime_witness_of_signed_prefix_gap hn hnOdd hnComposite hGRH hq (le_refl n) hx
      (by norm_num only : (0 : ℝ) ≤ 50000)
      (show (50000 : ℝ) ≤ (99 / 40 : ℝ) * x by
        dsimp only [x]
        nlinarith only [hL, sq_nonneg (Real.log n - 225)])
      hgap
  have hsq : 0 < (Real.log n) ^ 2 := sq_pos_of_pos (by linarith only [hL])
  dsimp only [x] at hb
  refine ⟨p, hp, ?_, ?_, hf⟩
  · nlinarith only [hb]
  · nlinarith only [hb, hsq]

/-- Under the same GRH, odd-composite and log(n) >= 225 hypotheses, a least
prime MR rejecting base satisfies the displayed bound. Minimize the unbounded
prime rejection predicate. Role: expose a least-witness version of the half-line bound. -/
theorem exists_least_prime_witness_le_even_paired_nearSquare_gamma_log_225 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 225 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ (99 / 100 : ℝ) * (Real.log n) ^ 2 ∧
        ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → p ≤ r := by
  classical
  obtain ⟨p, hp, hb, _, hf⟩ :=
    exists_prime_witness_le_even_paired_nearSquare_gamma_log_225 hnOdd hnComposite hGRH hL
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := ⟨p, hp, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hf⟩)).trans hb, fun r hr hf ↦
      Nat.find_min' hex ⟨hr, hf⟩⟩

/-- Under the same hypotheses, a prime below the stated bound fails the initial
power equality and every negative-one equality in the standard binary decomposition
of n-1. Apply the characterization of MR rejection. Role: expose the actual power tests. -/
theorem exists_prime_rejecting_powers_le_even_paired_nearSquare_gamma_log_225 {n : ℕ}
    (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 225 ≤ Real.log n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1);
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (99 / 100 : ℝ) * (Real.log n) ^ 2 ∧
        (p : ZMod n) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ -1 := by
  obtain ⟨p, hp, hb, _, hf⟩ :=
    exists_prime_witness_le_even_paired_nearSquare_gamma_log_225 hnOdd hnComposite hGRH hL
  exact ⟨p, hp, hb, PrimeTest.not_strongMillerRabinPass_iff.mp hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
