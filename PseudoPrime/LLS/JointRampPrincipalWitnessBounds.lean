/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.JointRampPrincipalBounds
public import PseudoPrime.LLS.TwoPolePrincipalCapBounds

/-! # Three witness comparisons retaining joint ramp-principal errors -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The common-error witness gap: the joint lower bound for twice the ramp minus the principal
sum, less the two-pole character upper budget. This keeps the shared arithmetic error combined
rather than inserting independent ramp and principal caps. -/
noncomputable def jointRampPrincipalGap (A : ℕ) (C x : ℝ) : ℝ :=
  jointRampPrincipalLower x - twoPoleConstantUpper A C x

/-- At every positive scale, the joint gap equals the signed-principal gap plus the displayed
explicit saving. Expand the error budgets, cancel the common increment cost and normalize the
square-root quotient. This exact comparison certifies improvement without numerical sampling. -/
theorem jointRampPrincipalGap_eq_signed {A : ℕ} {C x : ℝ} (hx : 0 < x) :
    jointRampPrincipalGap A C x =
      twoPoleSignedVariationGap A C x + 2029 / 16000 +
        ((42297 / 12500 : ℝ) * Real.log x + (23907 / 10000 : ℝ) * Real.log (99 / 40 : ℝ) +
            8757 / 3200) /
          Real.sqrt x := by
  have hs := (Real.sqrt_pos.mpr hx).ne'
  let D :=
    2 * gammaRampPairedErrorNumerator x +
        (Real.sqrt x / 20 + (5517 / 4000 : ℝ) * Real.log x + 2469 / 800) -
      jointRampPrincipalErrorNumerator x
  have he :
    D =
      (2029 / 16000 : ℝ) * Real.sqrt x + (42297 / 12500 : ℝ) * Real.log x +
        (23907 / 10000 : ℝ) * Real.log (99 / 40 : ℝ) +
        8757 / 3200 := by
    dsimp only [D, gammaRampPairedErrorNumerator, jointRampPrincipalErrorNumerator]
    rw [Real.log_mul hx.ne' (by norm_num only : (99 / 40 : ℝ) ≠ 0)]
    ring
  have hg : jointRampPrincipalGap A C x = twoPoleSignedVariationGap A C x + D / Real.sqrt x := by
    dsimp only [jointRampPrincipalGap, jointRampPrincipalLower, twoPoleSignedVariationGap,
      twoPolePrincipalCapGap, gammaSignedVariationPrincipalCap, D]
    ring
  have hd :
    D / Real.sqrt x =
      2029 / 16000 +
        ((42297 / 12500 : ℝ) * Real.log x + (23907 / 10000 : ℝ) * Real.log (99 / 40 : ℝ) +
            8757 / 3200) /
          Real.sqrt x := by
    rw [he]
    calc
      _ =
          (2029 / 16000 : ℝ) * (Real.sqrt x / Real.sqrt x) +
            ((42297 / 12500 : ℝ) * Real.log x + (23907 / 10000 : ℝ) * Real.log (99 / 40 : ℝ) +
                8757 / 3200) /
              Real.sqrt x :=
        by ring
      _ = _ := by
        rw [div_self hs]; ring
  rw [hg, hd]
  ring

/-- For every scale at least one, the joint gap exceeds the signed-principal gap by more than
one eighth. All remaining logarithmic terms in the exact saving are nonnegative and its constant
term is positive. This transfers previously certified margins to the common-error comparison. -/
theorem jointRampPrincipalGap_gt_signed {A : ℕ} {C x : ℝ} (hx : 1 ≤ x) :
    twoPoleSignedVariationGap A C x + 1 / 8 < jointRampPrincipalGap A C x := by
  rw [jointRampPrincipalGap_eq_signed (zero_lt_one.trans_le hx)]
  have hn :
    0 <
      (42297 / 12500 : ℝ) * Real.log x + (23907 / 10000 : ℝ) * Real.log (99 / 40 : ℝ) +
        8757 / 3200 := by
    linarith only [Real.log_nonneg hx, Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 99 / 40)]
  have ht := div_pos hn (Real.sqrt_pos.mpr (zero_lt_one.trans_le hx))
  linarith only [ht]

/-- For a nonprincipal character under GRH, a retained Euler-prefix saving and positive joint
gap exclude triviality on all primes below the cutoff. Use the actual joint principal bound in
the general ramp comparison. This is the character input for improved MR rejecting witnesses. -/
theorem prime_trivial_false_of_jointRampPrincipal_prefix {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C g : ℝ} (hx : 2 ≤ x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (S : Finset ℕ) (hS : ∀ n ∈ S, (n : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hg : g ≤ 2 * twoPoleEulerPrefixMass S) (hgap : 0 < jointRampPrincipalGap A (C - g) x) :
    ¬(∀ p : ℕ, p.Prime → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) := by
  intro ht
  have ht' : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ.primitiveCharacter p = 1 :=
    fun p hp hb ↦ PaperStatements.primitiveCharacter_apply_one_of_apply_one χ (ht p hp hb)
  have he :=
    AnalyticNumberTheory.Arithmetic.pairedEulerPrefix_eq_twice_of_coprime_support
      χ.primitiveCharacter S hS (fun n _ ↦ Nat.coprime_one_right n) (fun p hp hb _ ↦ ht' p hp hb)
  have hd :
    g ≤
      ∑ n ∈ S,
        (1 + (χ.primitiveCharacter n).re) *
          AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) n := by
    rw [he]
    exact hg
  have hb := gamma_primitive_re_le_twoPoleConstant_of_prefix χ hne hqA hGRH hx hC S hd
  have hx0 : 0 < x := by linarith only [hx]
  have hl :=
    gammaLocalCorrection_nonpos_of_level_primes_above χ hx0
      (fun p hp ↦ (level_prime_above_cutoff_of_all_prime_trivial χ ht hp).le)
  have hJ := jointRampPrincipalLower_le_actual hGRH.riemann (by linarith only [hx] : 1 ≤ x)
  have hN := gamma_ramp_no_witness_comparison_general χ hx0 (fun p hp _ hb0 ↦ ht p hp hb0)
  dsimp only [jointRampPrincipalGap, twoPoleConstantUpper] at hgap hb
  dsimp only [signedTwoPoleUpper] at hgap hb
  linarith only [hb, hl, hJ, hN, hgap]

/-- For a quadratic nonprincipal character of even level under GRH, an odd Euler prefix and a
joint gap above the prime-two allowance yield an odd non-one prime. Combine the actual joint
principal bound with the odd-prime comparison. This preserves common-error cancellation in the
Jacobi non-one argument. -/
theorem exists_odd_prime_ne_one_of_jointRampPrincipal_prefix {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (h2 : 2 ∣ q) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C g : ℝ} (hx : 2 ≤ x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (S : Finset ℕ) (hS : ∀ n ∈ S, (n : ℝ) ≤ (99 / 40 : ℝ) * x) (hodd : ∀ n ∈ S, Odd n)
    (hg : g ≤ 2 * twoPoleEulerPrefixMass S)
    (hgap :
      (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x <
        jointRampPrincipalGap A (C - g) x) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p ≠ 1 := by
  classical
  by_contra hnone
  have ht : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1 := fun p hp ho hb ↦
    Classical.byContradiction (fun hv ↦ hnone ⟨p, hp, ho, hb, hv⟩)
  have ht' :
    ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (99 / 40 : ℝ) * x → Nat.Coprime p 2 → χ.primitiveCharacter p = 1 :=
    fun p hp hb hc ↦
    PaperStatements.primitiveCharacter_apply_one_of_apply_one χ
      (ht p hp (Nat.coprime_two_right.mp hc) hb)
  have he :=
    AnalyticNumberTheory.Arithmetic.pairedEulerPrefix_eq_twice_of_coprime_support
      χ.primitiveCharacter S hS (fun n hn ↦ Nat.coprime_two_right.mpr (hodd n hn)) ht'
  have hd :
    g ≤
      ∑ n ∈ S,
        (1 + (χ.primitiveCharacter n).re) *
          AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) n := by
    rw [he]
    exact hg
  have hb := gamma_primitive_re_le_twoPoleConstant_of_prefix χ hne hqA hGRH hx hC S hd
  have hx0 : 0 < x := by linarith only [hx]
  have hN :=
    gamma_ramp_no_odd_ne_one_comparison_log_budget χ hquad h2 hx0
      (by linarith only [hx] : 1 ≤ (99 / 40 : ℝ) * x) ht
  have hJ := jointRampPrincipalLower_le_actual hGRH.riemann (by linarith only [hx] : 1 ≤ x)
  dsimp only [jointRampPrincipalGap, twoPoleConstantUpper, signedTwoPoleUpper] at hgap hb
  linarith only [hb, hN, hJ, hgap]

/-- Under GRH and an admissible conductor allocation, a full Euler-prefix saving and a joint
gap above the level-prime ramp cost yield a unit-prime witness of value minus one. Combine the
conductor-cancelled arithmetic bound with the actual joint principal lower bound, then use
quadraticity. No sampled or implicit uniform exclusion condition is introduced. -/
theorem exists_prime_neg_one_of_jointRampPrincipal_conductor_prefix {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C Y g a d : ℝ} (hx : 2 ≤ x)
    (hY : 1 ≤ Y) (ha : 0 ≤ a) (hd : 0 ≤ d) (hscale : 1 ≤ (1 / 2 - a) * Real.sqrt x)
    (hprime :
      ∀ p : ℕ,
        p.Prime →
          AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) p ≤
            a * Real.log p + if p = 2 then d else 0)
    (hYcut : ∀ n ∈ Finset.Ioc 0 ⌊Y⌋₊, (n : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (hg : g ≤ twoPoleEulerPrefixMass (Finset.Ioc 0 ⌊Y⌋₊) - d)
    (hgap :
      (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x <
        jointRampPrincipalGap A (C - g) x) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p = -1 := by
  classical
  have hex : ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p ≠ 1 := by
    by_contra hnone
    have ht : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1 := fun p hp hd hb ↦
      Classical.byContradiction (fun hv ↦ hnone ⟨p, hp, hd, hb, hv⟩)
    have hb :=
      gamma_primitive_add_local_le_of_parameterized_conductor_prefix χ hquad hne hqA hGRH hx hY ha
        hd hscale hprime hYcut hC ht
    have hJ := jointRampPrincipalLower_le_actual hGRH.riemann (by linarith only [hx] : 1 ≤ x)
    have hN := gamma_ramp_no_witness_comparison χ hquad (by linarith only [hx] : 0 < x) ht
    dsimp only [jointRampPrincipalGap, twoPoleConstantUpper, signedTwoPoleUpper] at hgap hb
    linarith only [hb, hJ, hN, hgap, hg]
  obtain ⟨p, hp, hd, hb, hv⟩ := hex
  have hz : χ p ≠ 0 :=
    MulChar.apply_ne_zero_iff.mpr
      ((ZMod.isUnit_iff_coprime p q).mpr (hp.coprime_iff_not_dvd.mpr hd))
  refine ⟨p, hp, hd, hb, ?_⟩
  rcases hquad (p : ZMod q) with h0 | h1 | hm
  · exact False.elim (hz h0)
  · exact False.elim (hv h1)
  · exact hm

end PseudoPrime.LLS
