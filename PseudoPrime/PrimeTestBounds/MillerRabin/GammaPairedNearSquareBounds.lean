/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaSignedPrefixBounds
public import PseudoPrime.LLS.GammaPairedNearSquareNegativeBounds

/-! # Prime MR rejecting witnesses from log 700 with paired ramp errors -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH at q at least 20000 and log q at least 700, every nonprincipal
primitive Gamma sum at x=(2/5)(log q) squared is at most M log q+22.
Enlarge the actual conductor in the paired upper bound only after the
primitive comparison. This supplies a common upper bound for MR extraction. -/
theorem gamma_primitiveCharacter_sum_re_le_paired_nearSquare {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 700 ≤ Real.log q) :
    let x := (2 / 5 : ℝ) * (Real.log q) ^ 2;
    (∑' k : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x k).re ≤
      (11783423 / 25000000 : ℝ) * Real.log q + 22 := by
  have hu :=
    gamma_primitiveCharacter_sum_re_le_paired_nearSquare_conductor hq χ hne hGRH hL
      (by linarith only : Real.log q ≤ Real.log q + 7 / 5)
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hf : (0 : ℝ) < χ.conductor := by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hmqR : (χ.conductor : ℝ) ≤ q := by exact_mod_cast hmq
  have hlead :=
    mul_le_mul_of_nonneg_left (Real.log_le_log hf hmqR)
      (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
  linarith only [hu, hlead]

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every odd composite n with log n ≥ 700 has a prime
rejecting base p ≤ (99/100)(log n)², hence p < (log n)².
Combine the uniform nonprincipal upper bound with exact-principal index
reduction and certified principal/ramp errors. No numerical-gap assumption
or input-factorization restriction remains. -/
theorem exists_prime_witness_le_paired_nearSquare_gamma_log_700 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 700 ≤ Real.log n) :
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
    nlinarith only [hL, sq_nonneg (Real.log n - 700)]
  have hx0 := zero_lt_one.trans_le hx
  have he := LLS.gamma_paired_nearSquare_budgets hL
  have hP := LLS.gamma_level_one_sum_upper_variable hGRH.riemann hx
  have hT := LLS.gamma_ramp_sum_lower_paired hGRH.riemann hx
  have hgap :
    (11783423 / 25000000 : ℝ) * Real.log n + 22 <
      2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
        (∑' k : ℕ,
            LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re := by
    nlinarith only [hP, hT, he.1, he.2.1, he.2.2, hL]
  obtain ⟨p, hp, hb, hf⟩ :=
    exists_prime_witness_of_common_primitive_upper hn hnOdd hnComposite hx0
      (fun χ hχ ↦
        LLS.PaperStatements.gamma_primitiveCharacter_sum_re_le_paired_nearSquare hq χ hχ hGRH hL)
      hgap
  have hsq : 0 < (Real.log n) ^ 2 := sq_pos_of_pos (by linarith only [hL])
  dsimp only [x] at hb
  refine ⟨p, hp, ?_, ?_, hf⟩
  · nlinarith only [hb]
  · nlinarith only [hb, hsq]

/-- Under GRH, an odd composite input with log n at least 700 has a least
prime rejecting base through (99/100)(log n) squared.
Minimize the unbounded rejection predicate and compare with the constructed
witness. Minimality ranges over every prime rejecting base. -/
theorem exists_least_prime_witness_le_paired_nearSquare_gamma_log_700 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 700 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ (99 / 100 : ℝ) * (Real.log n) ^ 2 ∧
        ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → p ≤ r := by
  classical
  obtain ⟨p, hp, hb, _, hf⟩ :=
    exists_prime_witness_le_paired_nearSquare_gamma_log_700 hnOdd hnComposite hGRH hL
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := ⟨p, hp, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hf⟩)).trans hb, fun r hr hf ↦
      Nat.find_min' hex ⟨hr, hf⟩⟩

/-- Under GRH for odd composite n with log n at least 700, the canonical
decomposition n-1=2^s d has a prime base through the coefficient-99/100
cutoff whose d-th power is not one and whose tested doubled powers are not
minus one. Apply the exact rejection equivalence to the proved witness. -/
theorem exists_prime_rejecting_powers_le_paired_nearSquare_gamma_log_700 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 700 ≤ Real.log n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1);
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (99 / 100 : ℝ) * (Real.log n) ^ 2 ∧
        (p : ZMod n) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ -1 := by
  obtain ⟨p, hp, hb, _, hf⟩ :=
    exists_prime_witness_le_paired_nearSquare_gamma_log_700 hnOdd hnComposite hGRH hL
  exact ⟨p, hp, hb, PrimeTest.not_strongMillerRabinPass_iff.mp hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
