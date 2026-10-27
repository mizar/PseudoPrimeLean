/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SignedHalfPowerWitnessBounds
public import PseudoPrime.PseudoSquare.Bounds.RefinedConductorRadicalWitnessBounds

/-! # Conditional quadratic witness bounds from signed half-scale estimates -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Under RH and fixed power parameters, all sufficiently large odd nonsquares n
have a negative odd-prime Jacobi witness through C(log(4n))^a if the canonical
primitive character satisfies the signed-window input with exclusion 4n.
Use E(4n)≤log(4n), the uniform LLS transfer and quadratic reciprocity. -/
theorem eventually_exists_prime_neg_one_of_signed_half_power_window {a δ C θ C₁ C₂ : ℝ} (ha : 1 < a)
    (hδ : 1 - δ < a / 2) (hC : 0 < C) (hθ : 0 < θ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hRH : RiemannHypothesis) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (hn : Odd n),
        ¬IsSquare n →
          LLS.PaperStatements.SignedHalfPowerWindow (NumberTheory.primitiveQuadraticCharacter n hn)
            (4 * n) (Real.log ((4 * n : ℕ) : ℝ)) a δ C θ C₁ C₂ →
          ∃ p : ℕ,
            p.Prime ∧
              Odd p ∧ jacobiSym n p = -1 ∧ (p : ℝ) ≤ C * (Real.log ((4 * n : ℕ) : ℝ)) ^ a := by
  have h :=
    LLS.eventually_exists_unit_prime_of_signed_half_power_window (Cₘ := 1) ha hδ hC hθ hC₁ hC₂ hRH
  have hlog :
    Filter.Tendsto (fun n : ℕ ↦ Real.log ((4 * n : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
    have hm := tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num only : (0 : ℝ) < 4)
    simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat] using
      Real.tendsto_log_atTop.comp hm
  filter_upwards [hlog.eventually h] with n hL
  intro hn _ hw
  let : NeZero (4 * n) := ⟨mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hE := AnalyticNumberTheory.Arithmetic.sum_log_primeFactors_le_log (NeZero.ne (4 * n))
  have hE' : (∑ p ∈ (4 * n).primeFactors, Real.log p) ≤ (1 : ℝ) * Real.log ((4 * n : ℕ) : ℝ) := by
    simpa only [one_mul] using hE
  obtain ⟨p, hp, hb, hd, hv⟩ := hL (4 * n) (NumberTheory.complexQuadraticCharacter n hn) hE' hw
  have hmem := NumberTheory.primeNegOneWitness_mem_of_complexQuadraticCharacter_ne_one n hn hp hd hv
  exact ⟨p, hp, hmem.2.1, hmem.2.2, hb⟩

/-- Under RH and fixed power parameters, the primitive signed-window input
bounds the least negative odd-prime witness by C(log(4n))^a for every sufficiently
large odd nonsquare n. Apply leastness to the actual prime; no finite range is claimed. -/
theorem eventually_primeNegOneWitness_le_of_signed_half_power_window {a δ C θ C₁ C₂ : ℝ}
    (ha : 1 < a) (hδ : 1 - δ < a / 2) (hC : 0 < C) (hθ : 0 < θ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hRH : RiemannHypothesis) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (hn : Odd n),
        ¬IsSquare n →
          LLS.PaperStatements.SignedHalfPowerWindow (NumberTheory.primitiveQuadraticCharacter n hn)
            (4 * n) (Real.log ((4 * n : ℕ) : ℝ)) a δ C θ C₁ C₂ →
          ∀ hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty,
            (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ C * (Real.log ((4 * n : ℕ) : ℝ)) ^ a := by
  have h := eventually_exists_prime_neg_one_of_signed_half_power_window ha hδ hC hθ hC₁ hC₂ hRH
  filter_upwards [h] with n hn
  intro ho hns hphase hw
  obtain ⟨p, hp, hpo, hj, hb⟩ := hn ho hns hphase
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, hpo, hj⟩)).trans hb

/-- Under RH and fixed power parameters, the primitive signed-window input
bounds the least non-one odd-prime witness by C(log(4n))^a for sufficiently large
odd nonsquare n. A negative Jacobi value is non-one, so the actual prime supplies
membership and leastness. The analytic signed-window input remains unproved. -/
theorem eventually_primeNeOneWitness_le_of_signed_half_power_window {a δ C θ C₁ C₂ : ℝ} (ha : 1 < a)
    (hδ : 1 - δ < a / 2) (hC : 0 < C) (hθ : 0 < θ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hRH : RiemannHypothesis) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (hn : Odd n),
        ¬IsSquare n →
          LLS.PaperStatements.SignedHalfPowerWindow (NumberTheory.primitiveQuadraticCharacter n hn)
            (4 * n) (Real.log ((4 * n : ℕ) : ℝ)) a δ C θ C₁ C₂ →
          ∀ hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty,
            (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ C * (Real.log ((4 * n : ℕ) : ℝ)) ^ a := by
  have h := eventually_exists_prime_neg_one_of_signed_half_power_window ha hδ hC hθ hC₁ hC₂ hRH
  filter_upwards [h] with n hn
  intro ho hns hphase hw
  obtain ⟨p, hp, hpo, hj, hb⟩ := hn ho hns hphase
  have hv : jacobiSym n p ≠ 1 := by
    rw [hj]; norm_num only
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, hpo, hv⟩)).trans hb

/-- For 0<ε<min(2δ,1), RH and fixed nonnegative phase constants, the explicit
primitive signed-window input implies a least-negative-witness bound
C(log(4n))^(2-ε) for sufficiently large odd nonsquares n. Specialize the general
power transfer. This is conditional on the named analytic input, not a GRH-only improvement. -/
theorem eventually_primeNegOneWitness_le_subquadratic_of_signed_half_window {ε δ C θ C₁ C₂ : ℝ}
    (hε : 0 < ε ∧ ε < min (2 * δ) 1) (hC : 0 < C) (hθ : 0 < θ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hRH : RiemannHypothesis) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (hn : Odd n),
        ¬IsSquare n →
          LLS.PaperStatements.SignedHalfPowerWindow (NumberTheory.primitiveQuadraticCharacter n hn)
            (4 * n) (Real.log ((4 * n : ℕ) : ℝ)) (2 - ε) δ C θ C₁ C₂ →
          ∀ hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty,
            (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
              C * (Real.log ((4 * n : ℕ) : ℝ)) ^ (2 - ε) := by
  have he := Analysis.signed_half_exponents_of_epsilon hε
  exact eventually_primeNegOneWitness_le_of_signed_half_power_window he.1 he.2.1 hC hθ hC₁ hC₂ hRH

end PseudoPrime.PseudoSquare
