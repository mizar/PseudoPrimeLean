/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.LogShiftRampPrincipalBounds
public import PseudoPrime.LLS.ReflectedSplitConductorBounds

/-! # Three witness comparisons retaining the logarithmic correction -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The witness separation gap at scale x with stencil width h.
Subtract the character upper budget from the variable-width joint principal lower cap.
Positivity, with the relevant exclusion cost, yields the three prime witness types. -/
noncomputable def logShiftRampPrincipalGap (A : ℕ) (C x h : ℝ) : ℝ :=
  logShiftRampPrincipalLower x h - reflectedSplitUpper A C x

/-- For a nonprincipal character under GRH, a retained Euler-prefix saving and positive joint
gap exclude triviality on all primes below the cutoff. Use the actual joint principal bound in
the general ramp comparison. This is the character input for improved MR rejecting witnesses. -/
theorem prime_trivial_false_of_logShiftRampPrincipal_prefix {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C g h : ℝ} (hx : 2 ≤ x)
    (hh : 0 < h) (hhx : h ≤ x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (S : Finset ℕ) (hS : ∀ n ∈ S, (n : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hg : g ≤ 2 * twoPoleEulerPrefixMass S) (hgap : 0 < logShiftRampPrincipalGap A (C - g) x h) :
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
  have hb := gamma_primitive_re_le_reflectedSplit_of_prefix χ hne hqA hGRH hx hC S hd
  have hx0 : 0 < x := by linarith only [hx]
  have hl :=
    gammaLocalCorrection_nonpos_of_level_primes_above χ hx0
      (fun p hp ↦ (level_prime_above_cutoff_of_all_prime_trivial χ ht hp).le)
  have hJ :=
    logShiftRampPrincipalLower_le_actual hGRH.riemann (by linarith only [hx] : 1 ≤ x) hh hhx
  have hN := gamma_ramp_no_witness_comparison_general χ hx0 (fun p hp _ hb0 ↦ ht p hp hb0)
  dsimp only [logShiftRampPrincipalGap, reflectedSplitUpper] at hgap hb
  linarith only [hb, hl, hJ, hN, hgap]

/-- For a quadratic nonprincipal character of even level under GRH, an odd Euler prefix and a
joint gap above the prime-two allowance yield an odd non-one prime. Combine the actual joint
principal bound with the odd-prime comparison. This preserves common-error cancellation in the
Jacobi non-one argument. -/
theorem exists_odd_prime_ne_one_of_logShiftRampPrincipal_prefix {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (h2 : 2 ∣ q) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C g h : ℝ} (hx : 2 ≤ x)
    (hh : 0 < h) (hhx : h ≤ x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (S : Finset ℕ) (hS : ∀ n ∈ S, (n : ℝ) ≤ (99 / 40 : ℝ) * x) (hodd : ∀ n ∈ S, Odd n)
    (hg : g ≤ 2 * twoPoleEulerPrefixMass S)
    (hgap :
      (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x <
        logShiftRampPrincipalGap A (C - g) x h) :
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
  have hb := gamma_primitive_re_le_reflectedSplit_of_prefix χ hne hqA hGRH hx hC S hd
  have hx0 : 0 < x := by linarith only [hx]
  have hN :=
    gamma_ramp_no_odd_ne_one_comparison_log_budget χ hquad h2 hx0
      (by linarith only [hx] : 1 ≤ (99 / 40 : ℝ) * x) ht
  have hJ :=
    logShiftRampPrincipalLower_le_actual hGRH.riemann (by linarith only [hx] : 1 ≤ x) hh hhx
  dsimp only [logShiftRampPrincipalGap, reflectedSplitUpper] at hgap hb
  linarith only [hb, hN, hJ, hgap]

/-- Under GRH and an admissible conductor allocation, a full Euler-prefix saving and a joint
gap above the level-prime ramp cost yield a unit-prime witness of value minus one. Combine the
conductor-cancelled arithmetic bound with the actual joint principal lower bound, then use
quadraticity. No sampled or implicit uniform exclusion condition is introduced. -/
theorem exists_prime_neg_one_of_logShiftRampPrincipal_conductor_prefix {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C Y g a d h : ℝ} (hx : 2 ≤ x)
    (hh : 0 < h) (hhx : h ≤ x) (hY : 1 ≤ Y) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hscale : 1 ≤ (1 / 2 - a) * Real.sqrt x)
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
        logShiftRampPrincipalGap A (C - g) x h) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p = -1 := by
  classical
  have hex : ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p ≠ 1 := by
    by_contra hnone
    have ht : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1 := fun p hp hd hb ↦
      Classical.byContradiction (fun hv ↦ hnone ⟨p, hp, hd, hb, hv⟩)
    have hb :=
      gamma_primitive_add_local_le_reflectedSplit_conductor_prefix χ hquad hne hqA hGRH hx hY ha hd
        hscale hprime hYcut hC ht
    have hJ :=
      logShiftRampPrincipalLower_le_actual hGRH.riemann (by linarith only [hx] : 1 ≤ x) hh hhx
    have hN := gamma_ramp_no_witness_comparison χ hquad (by linarith only [hx] : 0 < x) ht
    dsimp only [logShiftRampPrincipalGap, reflectedSplitUpper] at hgap hb
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

/-- For every scale and width, mass 133/160 bounds the corrected principal cap
from below with the actual corrected error budget. Multiply the certified mass
by the nonnegative square root. This is the explicit anchor consumer input. -/
theorem logShiftRampPrincipalLower_ge_133_160 (x h : ℝ) :
    (133 / 160 : ℝ) * Real.sqrt x - logShiftRampPrincipalErrorNumerator x h / Real.sqrt x ≤
      logShiftRampPrincipalLower x h := by
  have hm :=
    mul_le_mul_of_nonneg_right Analysis.ramp_mass_coefficient_ge_133_160 (Real.sqrt_nonneg x)
  dsimp only [logShiftRampPrincipalLower]
  linarith only [hm]

/-- Under GRH, a quadratic nonprincipal character has a negative unit-prime witness when
the explicit variable-width gap exceeds its level-prime cost. Assume x at least 25, an
admissible width, and an Euler cutoff b at least 128 below the witness cutoff. Use the
certified anchor, the prime cost 3/10 with its prime-two allowance, and the mass 133/160.
This removes all unverified prefix and conductor-allocation premises from the consumer. -/
theorem exists_prime_neg_one_of_logShift_anchor128_mass133 {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C b h : ℝ} (hx : 25 ≤ x)
    (hh : 0 < h) (hhx : h ≤ x) (hb : 128 ≤ b) (hcut : b ≤ (99 / 40 : ℝ) * x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (hgap :
      (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x <
        (133 / 160 : ℝ) * Real.sqrt x - logShiftRampPrincipalErrorNumerator x h / Real.sqrt x -
              reflectedSplitUpper A C x +
            ((3643 / 1000 : ℝ) - 5 * b ^ (-1 / 4 : ℝ)) -
          (1 / 5 : ℝ) * Real.log 2) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p = -1 := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hs : 5 ≤ Real.sqrt x := by nlinarith only [hx, Real.sq_sqrt hx0, Real.sqrt_nonneg x]
  have hp := pairedEulerPrefix_ge_anchor128 hGRH.riemann hb
  have hl := logShiftRampPrincipalLower_ge_133_160 x h
  apply
    exists_prime_neg_one_of_logShiftRampPrincipal_conductor_prefix χ hquad hne hqA hGRH
      (by linarith only [hx]) hh hhx (Y := b) (by linarith only [hb]) (a := 3 / 10) (d :=
      (1 / 5 : ℝ) * Real.log 2) (by norm_num only)
      (mul_nonneg (by norm_num only) (Real.log_natCast_nonneg 2)) (by linarith only [hs])
      (fun p hp ↦
        AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight_prime_upper_three_tenths hp)
      (fun n hn ↦
        (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans
          ((Nat.floor_le (by linarith only [hb] : 0 ≤ b)).trans hcut))
      hC (g := (3643 / 1000 : ℝ) - 5 * b ^ (-1 / 4 : ℝ) - (1 / 5 : ℝ) * Real.log 2)
      (by linarith only [hp])
  dsimp only [logShiftRampPrincipalGap, reflectedSplitUpper]
  dsimp only [reflectedSplitUpper] at hgap
  linarith only [hgap, hl]

end PseudoPrime.LLS
