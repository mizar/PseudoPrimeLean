/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaSignedPrefixBounds
public import PseudoPrime.LLS.GammaNearSquareNumerics
public import PseudoPrime.LLS.PaperStatements.GammaNearSquareBounds

/-! # Coefficient 99/100 Miller-Rabin witnesses from logarithmic scale 1000 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every odd composite n with log n ≥ 1000 has a prime
rejecting base p ≤ (99/100)(log n)², hence p < (log n)².
Combine the uniform nonprincipal upper bound with exact-principal index
reduction and certified principal/ramp errors. No numerical-gap assumption
or input-factorization restriction remains. -/
theorem exists_prime_witness_le_nearSquare_gamma_log_1000 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 1000 ≤ Real.log n) :
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
  have hx : 1 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (Real.log n - 1000)]
  have hx0 := zero_lt_one.trans_le hx
  have he := LLS.PaperStatements.nearSquare_gamma_error_budgets hL
  have hP := LLS.gamma_level_one_sum_upper_variable hGRH.riemann hx
  have hT := LLS.gamma_ramp_sum_lower_variable hGRH.riemann hx
  have hgap :
    (11783423 / 25000000 : ℝ) * Real.log n + 217 / 10 <
      2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
        (∑' k : ℕ,
            LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re := by
    nlinarith only [hP, hT, he.2.1, he.2.2.1, he.2.2.2.2, hL]
  obtain ⟨p, hp, hb, hf⟩ :=
    exists_prime_witness_of_common_primitive_upper hn hnOdd hnComposite hx0
      (fun χ hχ ↦ LLS.PaperStatements.gamma_primitiveCharacter_sum_re_le_nearSquare hq χ hχ hGRH hL)
      hgap
  have hsq : 0 < (Real.log n) ^ 2 := sq_pos_of_pos (by linarith only [hL])
  dsimp only [x] at hb
  refine ⟨p, hp, ?_, ?_, hf⟩
  · nlinarith only [hb]
  · nlinarith only [hb, hsq]

end PseudoPrime.PrimeTestBounds.MillerRabin
