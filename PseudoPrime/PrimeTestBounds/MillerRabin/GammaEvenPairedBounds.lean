/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaPrincipalPairedBounds
public import PseudoPrime.LLS.GammaEvenPairedNumerics

/-! # Even signed-prefix budgets and MR witnesses from log 400 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Input: RH, arbitrary levels, scale x and prefix endpoint b.
Claim: the signed MR prefix budget is below mu log n + 11 minus twice its prefix and contour costs.
Proof: combine the certified even Gamma gain and principal Euler mass below 25/2.
Role: preserve prefix gain with an explicit constant for future finite-scale comparisons. -/
theorem gammaSignedPrefixMRBudget_lt_principal_even (hRH : RiemannHypothesis) (n Q : ℕ) (x b : ℝ) :
    gammaSignedPrefixMRBudget n Q x b <
      (11783423 / 25000000 : ℝ) * Real.log n + 11 -
          2 * (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  have hg :=
    AnalyticNumberTheory.DirichletLFunction.gammaResolvent_gammaFactor_0_le
      AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even
  have hf : (1 : DirichletCharacter ℂ 1).gammaFactor = Complex.Gammaℝ :=
    funext AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even.gammaFactor_def
  rw [hf] at hg
  have he := AnalyticNumberTheory.DirichletLFunction.gammaResolvent_euler_lt_twelve_half hRH
  dsimp only [gammaSignedPrefixMRBudget, LLS.PaperStatements.gammaSignedGammaCost]
  linarith only [hg, he]

/-- Input: RH, L >= 400 and log n <= L.
Claim: the empty-prefix MR budget at x=(2/5)L squared is below mu log n + 66/5.
Proof: retain the even zero cost 11 and bound pole and left costs by 2 and 1/5.
Role: supply the uniform upper input for a closed MR separation on the whole half-line. -/
theorem gammaSignedPrefixMRBudget_zero_lt_even_nearSquare (hRH : RiemannHypothesis) {L : ℝ}
    (hL : 400 ≤ L) {n : ℕ} (hlog : Real.log n ≤ L) :
    gammaSignedPrefixMRBudget n n ((2 / 5 : ℝ) * L ^ 2) 0 <
      (11783423 / 25000000 : ℝ) * Real.log n + 66 / 5 := by
  let x := (2 / 5 : ℝ) * L ^ 2
  have hL0 : 0 < L := by linarith only [hL]
  have hx : 1 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (L - 400)]
  have hx0 := zero_lt_one.trans_le hx
  have hs := Real.sqrt_pos.mpr hx0
  have hroot : (63 / 100 : ℝ) * L ≤ Real.sqrt x := by
    apply (Real.le_sqrt (mul_nonneg (by norm_num only) hL0.le) hx0.le).mpr
    dsimp only [x]
    nlinarith only [sq_nonneg L]
  have hd :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 1) (by norm_num only)
      (by
        norm_num only; exact hx)
  simp only [one_mul] at hd
  have hl : 43 * x ^ (-9 / 16 : ℝ) ≤ 1 / 5 := by
    have hm := mul_le_mul_of_nonneg_left hd (by norm_num only : (0 : ℝ) ≤ 43)
    have hh : 43 * (1 / Real.sqrt x) ≤ (1 / 5 : ℝ) := by
      rw [mul_one_div, div_le_iff₀ hs]
      linarith only [hroot, hL]
    exact hm.trans hh
  have hp : ((7 / 6 : ℝ) * Real.log n + 4) / Real.sqrt x ≤ 2 := by
    rw [div_le_iff₀ hs]
    linarith only [hlog, hroot, hL]
  have hu := gammaSignedPrefixMRBudget_lt_principal_even hRH n n x 0
  simp only [Nat.floor_zero, Finset.Ioc_self, Finset.sum_empty, mul_zero, sub_zero] at hu
  linarith only [hu, hl, hp]

/-- Input: GRH, an odd composite n and log n >= 400.
Claim: a prime MR rejecting base is at most (99/100)(log n) squared.
It is strictly below (log n) squared.
Proof: every strong-pass annihilator is even; the signed-prefix extraction and paired errors close.
Role: improve the unconditional analytic entrance within the GRH theorem. -/
theorem exists_prime_witness_le_even_paired_nearSquare_gamma_log_400 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 400 ≤ Real.log n) :
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
    nlinarith only [hL, sq_nonneg (Real.log n - 400)]
  have hx1 : 1 ≤ x := le_trans (by norm_num only) hx
  have he := LLS.gamma_even_paired_nearSquare_budgets hL
  have hP := LLS.gamma_level_one_sum_upper_variable hGRH.riemann hx1
  have hT := LLS.gamma_ramp_sum_lower_paired hGRH.riemann hx1
  have hu := gammaSignedPrefixMRBudget_zero_lt_even_nearSquare hGRH.riemann hL (le_refl _)
  have hgap :
    gammaSignedPrefixMRBudget n n x 0 <
      2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
        (∑' k : ℕ,
            LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re := by
    nlinarith only [hu, hP, hT, he.1, he.2.1, he.2.2, hL]
  obtain ⟨p, hp, hb, hf⟩ :=
    exists_prime_witness_of_signed_prefix_gap hn hnOdd hnComposite hGRH hq (le_refl n) hx
      (by norm_num only : (0 : ℝ) ≤ 0) (show (0 : ℝ) ≤ (99 / 40 : ℝ) * x by linarith only [hx]) hgap
  have hsq : 0 < (Real.log n) ^ 2 := sq_pos_of_pos (by linarith only [hL])
  dsimp only [x] at hb
  refine ⟨p, hp, ?_, ?_, hf⟩
  · nlinarith only [hb]
  · nlinarith only [hb, hsq]

/-- Under GRH, an odd composite input with log n at least 400 has a least
prime rejecting base through (99/100)(log n) squared.
Minimize the unbounded rejection predicate and compare with the constructed
witness. Minimality ranges over every prime rejecting base. -/
theorem exists_least_prime_witness_le_even_paired_nearSquare_gamma_log_400 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 400 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ (99 / 100 : ℝ) * (Real.log n) ^ 2 ∧
        ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → p ≤ r := by
  classical
  obtain ⟨p, hp, hb, _, hf⟩ :=
    exists_prime_witness_le_even_paired_nearSquare_gamma_log_400 hnOdd hnComposite hGRH hL
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := ⟨p, hp, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hf⟩)).trans hb, fun r hr hf ↦
      Nat.find_min' hex ⟨hr, hf⟩⟩

/-- Under GRH for odd composite n with log n at least 400, the canonical
decomposition n-1=2^s d has a prime base through the coefficient-99/100
cutoff whose d-th power is not one and whose tested doubled powers are not
minus one. Apply the exact rejection equivalence to the proved witness. -/
theorem exists_prime_rejecting_powers_le_even_paired_nearSquare_gamma_log_400 {n : ℕ}
    (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 400 ≤ Real.log n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1);
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (99 / 100 : ℝ) * (Real.log n) ^ 2 ∧
        (p : ZMod n) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ -1 := by
  obtain ⟨p, hp, hb, _, hf⟩ :=
    exists_prime_witness_le_even_paired_nearSquare_gamma_log_400 hnOdd hnComposite hGRH hL
  exact ⟨p, hp, hb, PrimeTest.not_strongMillerRabinPass_iff.mp hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
