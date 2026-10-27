/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteSignedPhaseTransport
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.FiniteSignedResolvent
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PoissonNumericalBounds

/-! # Explicit zero-mass cost of logarithmic phase transport -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a primitive nonprincipal character under individual RH, the unit
resolvent zero mass is at most log(m)/2+38/5. Use the exact one-node Poisson identity,
the Gamma-factor correction 8/5 and the ordinary derivative upper bound six at 3/2. -/
theorem unit_resolvent_zeroMass_le {m : ℕ} [NeZero m] (hm : 2 ≤ m) {χ : DirichletCharacter ℂ m}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * (1 / (1 + ρ.im ^ 2))) ≤
      Real.log m / 2 + 38 / 5 := by
  have ha : ∀ ab ∈ ([(1, 1)] : List (ℚ × ℚ)), (1 / 2 : ℚ) < ab.1 := by
    intro ab hab
    rw [List.mem_singleton] at hab
    rw [hab]
    norm_num only
  have he := finiteSignedResolvent_zeroMass_eq_nodes hm hRH hp hne hinv [(1, 1)] ha
  simp only [Analysis.finiteSignedResolvent, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Rat.cast_one, one_mul, one_pow, add_zero] at he
  norm_num only [← Complex.ofReal_add] at he
  have hf :=
    abs_re_logDeriv_gammaFactor_le_eight_fifths χ (by norm_num only : (1 : ℝ) ≤ 3 / 2)
      (by norm_num only : (3 / 2 : ℝ) ≤ 15 / 2)
  have ho := norm_logDeriv_real_le_inv_gap χ (by norm_num only : (1 : ℝ) < 3 / 2)
  norm_num only at ho
  have hfo := le_abs_self (logDeriv χ.gammaFactor ((3 / 2 : ℝ) : ℂ)).re
  have hoo := Complex.re_le_norm (logDeriv χ.LFunction ((3 / 2 : ℝ) : ℂ))
  linarith only [he, hf, ho, hfo, hoo]

/-- Under individual RH and positive original nodes, adjoining (1,2*delta)
adds exactly twice delta times the unit-resolvent zero mass. Prove summability before
splitting the full zero series. This preserves the original arithmetic budget. -/
theorem logarithmicPhaseExtension_zeroMass_eq {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    {χ : DirichletCharacter ℂ m} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (l : List (ℚ × ℚ)) (hl : ∀ ab ∈ l, (0 : ℚ) < ab.1) (δ : ℚ) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.finiteSignedResolvent (Analysis.logarithmicPhaseExtension l δ) ρ.im) =
      (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            Analysis.finiteSignedResolvent l ρ.im) +
        2 * (δ : ℝ) *
          (∑' ρ : ℂ,
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
              (1 / (1 + ρ.im ^ 2))) := by
  have hs := summable_finiteSignedResolvent_terms hm hRH hp hne hinv l hl
  have hu := summable_completed_resolvent_terms hm hRH hp hne hinv (by norm_num only : (0 : ℝ) < 1)
  simp only [one_pow] at hu
  calc
    _ =
        ∑' ρ : ℂ,
          ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
              Analysis.finiteSignedResolvent l ρ.im +
            2 * (δ : ℝ) *
              ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
                (1 / (1 + ρ.im ^ 2)))) :=
      by
      apply tsum_congr
      intro ρ
      rw [Analysis.finiteSignedResolvent_logarithmicPhaseExtension]
      ring
    _ = _ := by rw [hs.tsum_add (hu.mul_left _), tsum_mul_left]

/-- Under the same hypotheses and nonnegative delta, the extended zero mass
is at most the original plus delta*(log(m)+76/5). Apply the unit-node estimate to
the exact splitting. This quantifies scale transport without new Euler data. -/
theorem logarithmicPhaseExtension_zeroMass_le {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    {χ : DirichletCharacter ℂ m} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (l : List (ℚ × ℚ)) (hl : ∀ ab ∈ l, (0 : ℚ) < ab.1) {δ : ℚ}
    (hd : 0 ≤ δ) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.finiteSignedResolvent (Analysis.logarithmicPhaseExtension l δ) ρ.im) ≤
      (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            Analysis.finiteSignedResolvent l ρ.im) +
        (δ : ℝ) * (Real.log m + 76 / 5) := by
  rw [logarithmicPhaseExtension_zeroMass_eq hm hRH hp hne hinv l hl δ]
  have h :=
    mul_le_mul_of_nonneg_left (unit_resolvent_zeroMass_le hm hRH hp hne hinv)
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) ((Rat.cast_nonneg (K := ℝ)).mpr hd))
  linarith only [h]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
