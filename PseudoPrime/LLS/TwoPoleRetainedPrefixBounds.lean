/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleRetainedScaleBounds
public import PseudoPrime.LLS.PairedEulerExcludedBounds
public import PseudoPrime.LLS.TwoPoleSmallPrefixSavings
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TwoPoleRetainedPrefixBounds

/-! # Retained real-axis Euler prefixes in signed two-pole witness comparisons -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The principal Euler prefix mass on a finite support S at the two fixed real-axis exponents.
This nonnegative finite sum records the zero-mass saving without discarding it before the
witness comparison. -/
noncomputable def twoPoleEulerPrefixMass (S : Finset ℕ) : ℝ :=
  ∑ n ∈ S, AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) n

/-- For a nonprincipal character under GRH, a lower bound d on its primitive paired prefix
subtracts d from the ambient arithmetic upper bound. Apply the retained-prefix explicit formula
and enlarge the conductor logarithm. No prime-triviality condition is needed once the prefix
lower bound is supplied. -/
theorem gamma_primitive_re_le_twoPoleConstant_of_prefix {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C d : ℝ} (hx : 2 ≤ x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (S : Finset ℕ)
    (hd :
      d ≤
        ∑ n ∈ S,
          (1 + (χ.primitiveCharacter n).re) *
            AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) n) :
    (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand χ.primitiveCharacter x n).re ≤
      twoPoleConstantUpper A C x - d := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hp := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmA := (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level).trans hqA
  have hb :=
    PaperStatements.gamma_primitive_sum_re_le_twoPole_constant (le_max_left 20000 A) hm
      (hmA.trans (le_max_right 20000 A)) hGRH hp hnp (inv_ne_one.mpr hnp) hx hC S S
  have he :=
    AnalyticNumberTheory.Arithmetic.paired_euler_prefixes_eq_weight χ.primitiveCharacter (5 / 4)
      (11 / 4) (3 / 4) S
  have hl :=
    Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero χ.conductor_ne_zero))
      (Nat.cast_le.mpr hmA)
  dsimp only [twoPoleConstantUpper, signedTwoPoleUpper]
  linarith only [hb, he, hd, hl]

/-- For a quadratic nonprincipal character under GRH, retain a paired-prefix saving while adding
the local correction. Absorb the conductor gap and charge only the original level-prime ramp
cost. This keeps the Euler saving separate from the negative-witness exclusion budget. -/
theorem gamma_primitive_add_local_le_twoPoleConstant_of_prefix {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C d : ℝ} (hx : 4 ≤ x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (S : Finset ℕ)
    (hd :
      d ≤
        ∑ n ∈ S,
          (1 + (χ.primitiveCharacter n).re) *
            AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) n) :
    (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand χ.primitiveCharacter x n).re +
        gammaQuadraticLocalCorrection χ x ≤
      twoPoleConstantUpper A C x - d +
        (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hp := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmA := (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level).trans hqA
  have hb :=
    PaperStatements.gamma_primitive_sum_re_le_twoPole_constant (le_max_left 20000 A) hm
      (hmA.trans (le_max_right 20000 A)) hGRH hp hnp (inv_ne_one.mpr hnp)
      (by linarith only [hx] : 2 ≤ x) hC S S
  have he :=
    AnalyticNumberTheory.Arithmetic.paired_euler_prefixes_eq_weight χ.primitiveCharacter (5 / 4)
      (11 / 4) (3 / 4) S
  have hx0 : 0 < x := by linarith only [hx]
  have hs : 2 ≤ Real.sqrt x := by nlinarith only [Real.sq_sqrt hx0.le, Real.sqrt_nonneg x, hx]
  have hl :=
    gammaQuadraticLocalCorrection_absorb_conductor χ hquad hx0
      (by linarith only [hx] : 1 ≤ (99 / 40 : ℝ) * x)
      (show 1 ≤ (1 / 2 : ℝ) * Real.sqrt x by linarith only [hs])
  have hlog :=
    Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))) (Nat.cast_le.mpr hqA)
  dsimp only [twoPoleConstantUpper, signedTwoPoleUpper]
  linarith only [hb, he, hd, hl, hlog]

/-- For a nonprincipal character under GRH, a principal prefix saving g and positive gap with
Gamma cost C-g exclude triviality on all small primes. Primitive prime values are one under the
contradiction, so the paired prefix has no excluded defect. This supplies the improved MR
criterion. -/
theorem prime_trivial_false_of_twoPoleConstant_prefix {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C g : ℝ} (hx : 2 ≤ x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (S : Finset ℕ) (hS : ∀ n ∈ S, (n : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hg : g ≤ 2 * twoPoleEulerPrefixMass S) (hgap : 0 < twoPoleConstantGap A (C - g) x) :
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
  have hP := gamma_level_one_sum_upper_variable hGRH.riemann (by linarith only [hx] : 1 ≤ x)
  have hT := gamma_ramp_sum_lower_paired hGRH.riemann (by linarith only [hx] : 1 ≤ x)
  have hN := gamma_ramp_no_witness_comparison_general χ hx0 (fun p hp _ hb0 ↦ ht p hp hb0)
  dsimp only [twoPoleConstantGap, signedTwoPoleGap, twoPoleConstantUpper] at hgap hb
  dsimp only [signedTwoPoleUpper] at hgap hb
  linarith only [hb, hl, hP, hT, hN, hgap]

/-- For a quadratic nonprincipal character of even level under GRH, odd finite support yields an
odd non-one prime when the saved gap exceeds the prime-two allowance. Use prime triviality on
odd primes and support coprime to two to retain the prefix saving. The level-prime correction
remains bounded separately. -/
theorem exists_odd_prime_ne_one_of_twoPoleConstant_prefix {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (h2 : 2 ∣ q) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C g : ℝ} (hx : 2 ≤ x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (S : Finset ℕ) (hS : ∀ n ∈ S, (n : ℝ) ≤ (99 / 40 : ℝ) * x) (hodd : ∀ n ∈ S, Odd n)
    (hg : g ≤ 2 * twoPoleEulerPrefixMass S)
    (hgap :
      (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x < twoPoleConstantGap A (C - g) x) :
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
  have hP := gamma_level_one_sum_upper_variable hGRH.riemann (by linarith only [hx] : 1 ≤ x)
  have hT := gamma_ramp_sum_lower_paired hGRH.riemann (by linarith only [hx] : 1 ≤ x)
  dsimp only [twoPoleConstantGap, signedTwoPoleGap, twoPoleConstantUpper,
    signedTwoPoleUpper] at hgap hb
  linarith only [hb, hN, hP, hT, hgap]

/-- For a quadratic nonprincipal character under GRH, the saved gap exceeding the structural
prefix exclusion and local ramp costs excludes triviality on unit primes. Keep the quadratic
excluded budget at the primitive conductor and original exclusion level. This prevents applying
the MR cost cancellation to negative witnesses. -/
theorem unit_prime_trivial_false_of_twoPoleConstant_prefix {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C : ℝ} (hx : 4 ≤ x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (S : Finset ℕ) (hS : ∀ n ∈ S, (n : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hgap :
      AnalyticNumberTheory.Arithmetic.quadraticExcludedBudget χ.conductor q S
            (AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4)) +
          (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x <
        twoPoleConstantGap A C x + 2 * twoPoleEulerPrefixMass S) :
    ¬(∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) := by
  intro ht
  have ht' :
    ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (99 / 40 : ℝ) * x → Nat.Coprime p q → χ.primitiveCharacter p = 1 :=
    fun p hp hb hc ↦
    PaperStatements.primitiveCharacter_apply_one_of_apply_one χ
      (ht p hp (hp.coprime_iff_not_dvd.mp hc) hb)
  have hd :=
    AnalyticNumberTheory.Arithmetic.paired_weighted_sum_ge_quadratic_budget χ.primitiveCharacter
      (NumberTheory.isQuadratic_primitiveCharacter χ hquad) S
      (AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4)) hS
      (fun n _ hn ↦
        AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight_eq_zero_of_mangoldt_eq_zero _ _ _
          hn)
      (fun n _ ↦
        AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight_nonneg _ _ (by norm_num only) n)
      ht'
  have hb := gamma_primitive_add_local_le_twoPoleConstant_of_prefix χ hquad hne hqA hGRH hx hC S hd
  have hP := gamma_level_one_sum_upper_variable hGRH.riemann (by linarith only [hx] : 1 ≤ x)
  have hT := gamma_ramp_sum_lower_paired hGRH.riemann (by linarith only [hx] : 1 ≤ x)
  have hN := gamma_ramp_no_witness_comparison χ hquad (by linarith only [hx] : 0 < x) ht
  dsimp only [twoPoleConstantGap, signedTwoPoleGap, twoPoleConstantUpper,
    twoPoleEulerPrefixMass] at hgap hb
  linarith only [hb, hP, hT, hN, hgap]

/-- Under the preceding saved-gap and exclusion hypotheses, extract a prime not dividing the
level with character value minus one. First obtain a non-one unit prime, then use quadraticity
to exclude zero and one. This connects the retained-prefix comparison to negative prime
witnesses. -/
theorem exists_prime_neg_one_of_twoPoleConstant_prefix {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C : ℝ} (hx : 4 ≤ x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (S : Finset ℕ) (hS : ∀ n ∈ S, (n : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hgap :
      AnalyticNumberTheory.Arithmetic.quadraticExcludedBudget χ.conductor q S
            (AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4)) +
          (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x <
        twoPoleConstantGap A C x + 2 * twoPoleEulerPrefixMass S) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p = -1 := by
  classical
  have hex : ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p ≠ 1 := by
    by_contra h
    apply unit_prime_trivial_false_of_twoPoleConstant_prefix χ hquad hne hqA hGRH hx hC S hS hgap
    intro p hp hd hb
    exact Classical.byContradiction (fun hv ↦ h ⟨p, hp, hd, hb, hv⟩)
  obtain ⟨p, hp, hd, hb, hv⟩ := hex
  have hz : χ p ≠ 0 :=
    MulChar.apply_ne_zero_iff.mpr
      ((ZMod.isUnit_iff_coprime p q).mpr (hp.coprime_iff_not_dvd.mpr hd))
  refine ⟨p, hp, hd, hb, ?_⟩
  rcases hquad (p : ZMod q) with h0 | h1 | hm
  · exact False.elim (hz h0)
  · exact False.elim (hv h1)
  · exact hm

/-- For an even quadratic nonprincipal character of even level under GRH, an ambient
logarithmic level at least 500 yields an odd non-one prime at the affine cutoff with constant
eleven. Retain the Euler saving 7/8 from the odd support consisting of three and five, while
charging the prime-two allowance separately. This supplies the explicit Jacobi bound. -/
theorem exists_odd_prime_ne_one_le_twoPolePrefix_even {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (heven : χ.Even) (hne : χ ≠ 1) (h2 : 2 ∣ q)
    (hqA : q ≤ A) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 500 ≤ Real.log A) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * ((500 / 821 : ℝ) * Real.log A + 11) ^ 2 ∧ χ p ≠ 1 := by
  let x := ((500 / 821 : ℝ) * Real.log A + 11) ^ 2
  have hd := twoPolePrefix_root_data hL
  have hx4 : 4 ≤ x := hd.2.1
  have hc :=
    AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant_le_signed_of_even
      χ.primitiveCharacter ((NumberTheory.primitiveCharacter_even_iff χ).mpr heven)
  have hm := twoPolePrefix_gap_margin hL (C := 112 / 25 - 7 / 8) (by norm_num only)
  have hl := twoPolePrefix_prime_two_allowance hL
  apply
    exists_odd_prime_ne_one_of_twoPoleConstant_prefix χ hquad hne h2 hqA hGRH
      (by linarith only [hx4] : 2 ≤ x) hc ({3,5} : Finset ℕ)
  · intro n hn
    have hs : ∀ m ∈ ({3,5} : Finset ℕ), m ≤ 5 := by decide
    exact (Nat.cast_le.mpr (hs n hn)).trans (by linarith only [hx4])
  · exact (by decide : ∀ n ∈ ({3,5} : Finset ℕ), Odd n)
  · exact AnalyticNumberTheory.Arithmetic.pairedEuler_prefix_35_saving
  · linarith only [hm, hl]

end PseudoPrime.LLS
