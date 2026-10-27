/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ParameterizedConductorPrefixBounds
public import PseudoPrime.LLS.GammaPrincipalCapComparison

/-! # Principal-cap inputs shared by all two-pole witness comparisons -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Given ambient level A, Gamma cost C, scale x and an upper cap P on the actual principal
Gamma sum, define twice the paired ramp lower bound minus P and the character upper budget.
This isolates the principal input so sharper arithmetic bounds can be inserted without changing
conductor or Euler-prefix arguments. -/
noncomputable def twoPolePrincipalCapGap (A : ℕ) (C x P : ℝ) : ℝ :=
  2 *
      ((∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) * Real.sqrt x -
        gammaRampPairedErrorNumerator x / Real.sqrt x) -
    P -
    twoPoleConstantUpper A C x

/-- The two-pole comparison gap using the signed-variation upper cap for the principal Gamma
sum. This replaces the older variable-scale principal cap while retaining the same ramp and
character terms. It is the common numerical gap for all three witness types. -/
noncomputable def twoPoleSignedVariationGap (A : ℕ) (C x : ℝ) : ℝ :=
  twoPolePrincipalCapGap A C x (gammaSignedVariationPrincipalCap x)

/-- At every positive scale, the signed-variation gap equals the previous gap plus the
explicit positive principal saving. Expand the two principal caps and cancel the square-root
quotient. This exact identity permits rational numerator bounds without repeating the analysis. -/
theorem twoPoleSignedVariationGap_eq_saved {A : ℕ} {C x : ℝ} (hx : 0 < x) :
    twoPoleSignedVariationGap A C x =
      twoPoleConstantGap A C x + 3 / 40 +
        ((1839 / 800 : ℝ) * Real.log x + 18123 / 4000) / Real.sqrt x := by
  have hs := (Real.sqrt_pos.mpr hx).ne'
  have he :
    (Real.sqrt x +
          (Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) / Real.sqrt x) -
        gammaSignedVariationPrincipalCap x =
      (3 / 40 : ℝ) * (Real.sqrt x / Real.sqrt x) +
        ((1839 / 800 : ℝ) * Real.log x + 18123 / 4000) / Real.sqrt x := by
    dsimp only [gammaSignedVariationPrincipalCap]
    ring
  rw [div_self hs] at he
  dsimp only [twoPoleSignedVariationGap, twoPolePrincipalCapGap, twoPoleConstantGap,
    signedTwoPoleGap, twoPoleConstantUpper] at *
  linarith only [he]

/-- For x at least one, the signed-variation gap exceeds the previous gap by more than three
fortieths. The remaining logarithmic numerator is positive. This proves uniform improvement
independently of GRH, which is needed only when applying the principal arithmetic cap. -/
theorem twoPoleSignedVariationGap_gt_constant {A : ℕ} {C x : ℝ} (hx : 1 ≤ x) :
    twoPoleConstantGap A C x + 3 / 40 < twoPoleSignedVariationGap A C x := by
  rw [twoPoleSignedVariationGap_eq_saved (zero_lt_one.trans_le hx)]
  have hn : 0 < (1839 / 800 : ℝ) * Real.log x + 18123 / 4000 := by
    linarith only [Real.log_nonneg hx]
  exact lt_add_of_pos_right _ (div_pos hn (Real.sqrt_pos.mpr (zero_lt_one.trans_le hx)))

/-- For a nonprincipal character under GRH, retain a principal Euler-prefix saving g and an
arbitrary valid upper cap P on the actual principal sum. A positive cap-dependent gap excludes
triviality on every prime below the cutoff. Apply the primitive prefix bound and the general
ramp comparison. This is the common character input for MR prime witnesses. -/
theorem prime_trivial_false_of_twoPolePrincipalCap_prefix {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C g P : ℝ} (hx : 2 ≤ x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (S : Finset ℕ) (hS : ∀ n ∈ S, (n : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hg : g ≤ 2 * twoPoleEulerPrefixMass S)
    (hP :
      (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re ≤ P)
    (hgap : 0 < twoPolePrincipalCapGap A (C - g) x P) :
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
  have hT := gamma_ramp_sum_lower_paired hGRH.riemann (by linarith only [hx] : 1 ≤ x)
  have hN := gamma_ramp_no_witness_comparison_general χ hx0 (fun p hp _ hb0 ↦ ht p hp hb0)
  dsimp only [twoPolePrincipalCapGap, twoPoleConstantUpper] at hgap hb
  dsimp only [signedTwoPoleUpper] at hgap hb
  linarith only [hb, hl, hP, hT, hN, hgap]

/-- For a quadratic nonprincipal character of even level under GRH, retain an odd Euler
prefix and any valid principal upper cap. If the resulting gap exceeds the prime-two allowance,
an odd non-one prime exists through the cutoff. Keep the exact principal cap in the ramp
contradiction. This supplies the improved non-one Jacobi interface. -/
theorem exists_odd_prime_ne_one_of_twoPolePrincipalCap_prefix {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (h2 : 2 ∣ q) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C g P : ℝ} (hx : 2 ≤ x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (S : Finset ℕ) (hS : ∀ n ∈ S, (n : ℝ) ≤ (99 / 40 : ℝ) * x) (hodd : ∀ n ∈ S, Odd n)
    (hg : g ≤ 2 * twoPoleEulerPrefixMass S)
    (hP :
      (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re ≤ P)
    (hgap :
      (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x <
        twoPolePrincipalCapGap A (C - g) x P) :
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
  have hT := gamma_ramp_sum_lower_paired hGRH.riemann (by linarith only [hx] : 1 ≤ x)
  dsimp only [twoPolePrincipalCapGap, twoPoleConstantUpper, signedTwoPoleUpper] at hgap hb
  linarith only [hb, hN, hP, hT, hgap]

/-- For a nonprincipal quadratic character under GRH with admissible conductor allocation,
full Euler prefix and valid principal upper cap, the saved gap exceeding the level-prime ramp
cost yields a unit prime of value minus one. Combine the parameterized conductor cancellation
with the cap-dependent principal comparison and exclude zero and one. This transfers sharper
principal estimates to negative witnesses without reintroducing a prefix exclusion hypothesis. -/
theorem exists_prime_neg_one_of_twoPolePrincipalCap_conductor_prefix {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C Y g a d P : ℝ} (hx : 2 ≤ x)
    (hY : 1 ≤ Y) (ha : 0 ≤ a) (hd : 0 ≤ d) (hscale : 1 ≤ (1 / 2 - a) * Real.sqrt x)
    (hprime :
      ∀ p : ℕ,
        p.Prime →
          AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) p ≤
            a * Real.log p + if p = 2 then d else 0)
    (hYcut : ∀ n ∈ Finset.Ioc 0 ⌊Y⌋₊, (n : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (hg : g ≤ twoPoleEulerPrefixMass (Finset.Ioc 0 ⌊Y⌋₊) - d)
    (hP :
      (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re ≤ P)
    (hgap :
      (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x <
        twoPolePrincipalCapGap A (C - g) x P) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p = -1 := by
  classical
  have hex : ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p ≠ 1 := by
    by_contra hnone
    have ht : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1 := fun p hp hd hb ↦
      Classical.byContradiction (fun hv ↦ hnone ⟨p, hp, hd, hb, hv⟩)
    have hb :=
      gamma_primitive_add_local_le_of_parameterized_conductor_prefix χ hquad hne hqA hGRH hx hY ha
        hd hscale hprime hYcut hC ht
    have hT := gamma_ramp_sum_lower_paired hGRH.riemann (by linarith only [hx] : 1 ≤ x)
    have hN := gamma_ramp_no_witness_comparison χ hquad (by linarith only [hx] : 0 < x) ht
    dsimp only [twoPolePrincipalCapGap, twoPoleConstantUpper, signedTwoPoleUpper] at hgap hb
    linarith only [hb, hP, hT, hN, hgap, hg]
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
