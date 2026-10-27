/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaUniformSubgroupComparison

/-! # Independent scales for the uniform Gamma subgroup bound

The ramp scale need not equal the logarithm of the modulus. The leading character
term retains log q, while the contour budgets and prime cutoff use an independent T.
A strict scalar budget converts this comparison into a prime witness.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, q ≥ 20000, T ≥ 35000 and log q ≤ T+2, the primitive Gamma
sum of any nonprincipal character at x=(32/99)T² is at most M log q+2755/90.
Bound the conductor by the ambient level and use the common contour budgets at T.
This separates the analytic scale from the logarithm of the level. -/
theorem gamma_primitiveCharacter_sum_re_le_uniform_scale {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {T : ℝ} (hT : 35000 ≤ T)
    (hambient : Real.log q ≤ T + 2) :
    let x := (32 / 99 : ℝ) * T ^ 2;
    (∑' n : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x n).re ≤
      (11783423 / 25000000 : ℝ) * Real.log q + 2755 / 90 := by
  let x := (32 / 99 : ℝ) * T ^ 2
  have hxlarge := Analysis.common_nonOne_ramp_scale_large hT
  have hx : 1 ≤ x := (by norm_num only : (1 : ℝ) ≤ (17 / 5) ^ 16).trans hxlarge
  have hs := Analysis.ramp_scale_sqrt_lower (show (0 : ℝ) ≤ T by linarith only [hT])
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hfpos : (0 : ℝ) < χ.conductor := by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hmqR : (χ.conductor : ℝ) ≤ q := by exact_mod_cast hmq
  have hlogf := Real.log_le_log hfpos hmqR
  have hf0 : 0 ≤ Real.log χ.conductor :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr χ.conductor_ne_zero)
  have hpole := common_nonOne_pole_budget hT hs hambient
  have hleft :=
    common_nonOne_left_budget hT hxlarge hs hf0
      (show Real.log χ.conductor ≤ T + 2 by linarith only [hlogf, hambient])
  have hlead := mul_le_mul_of_nonneg_left hlogf (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
  have hu :=
    gamma_primitiveCharacter_sum_re_le_variable_prefix_scale hq χ hne hGRH hx 32
      Analysis.gammaResolvent_thirtyTwo_error_lt
  linarith only [hu, hpole, hleft, hlead]

/-- Under GRH and the common scale entrance, a finite character subgroup has
primitive average at most sqrt x+3/20 plus M log q+2755/90 per nonidentity character.
Separate the principal character and apply the scale-dependent character bound.
This is the upper side for a shifted logarithmic cutoff. -/
theorem gamma_primitive_average_re_le_uniform_scale {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (S : Subgroup (DirichletCharacter ℂ q)) [Fintype S]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {T : ℝ} (hT : 35000 ≤ T)
    (hambient : Real.log q ≤ T + 2) :
    let x := (32 / 99 : ℝ) * T ^ 2;
    (∑ χ : S, ∑' n : ℕ, gammaMellinKernel.summand χ.val.primitiveCharacter x n).re ≤
      Real.sqrt x + 3 / 20 +
        ((Fintype.card S - 1 : ℕ) : ℝ) * ((11783423 / 25000000 : ℝ) * Real.log q + 2755 / 90) := by
  classical
  let x := (32 / 99 : ℝ) * T ^ 2
  have hxlarge := Analysis.common_nonOne_ramp_scale_large hT
  have hx : 1 ≤ x := (by norm_num only : (1 : ℝ) ≤ (17 / 5) ^ 16).trans hxlarge
  have hs0 := Real.sqrt_pos.mpr (zero_lt_one.trans_le hx)
  let F := fun χ : S ↦ (∑' n : ℕ, gammaMellinKernel.summand χ.val.primitiveCharacter x n).re
  have hP := PseudoPrime.LLS.gamma_level_one_sum_upper_variable hGRH.riemann hx
  have he := (div_le_iff₀ hs0).mpr (Analysis.common_nonOne_exponential_error hT)
  have hprincipal :
    (∑' n : ℕ, gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re ≤
      Real.sqrt x + 3 / 20 := by
    linarith only [hP, he]
  have h1 : F 1 ≤ Real.sqrt x + 3 / 20 := by
    dsimp only [F]
    rw [Subgroup.coe_one,
      tsum_congr
        (MellinKernel.principal_primitive_summand_eq_level_one gammaMellinKernel (q := q) x)]
    exact hprincipal
  have hrest :
    ∑ χ ∈ Finset.univ.erase (1 : S), F χ ≤
      ((Finset.univ.erase (1 : S)).card : ℝ) *
        ((11783423 / 25000000 : ℝ) * Real.log q + 2755 / 90) := by
    calc
      _ ≤ ∑ _χ ∈ Finset.univ.erase (1 : S), ((11783423 / 25000000 : ℝ) * Real.log q + 2755 / 90) :=
        by
        apply Finset.sum_le_sum
        intro χ hχ
        exact
          gamma_primitiveCharacter_sum_re_le_uniform_scale hq χ.val
            (fun he ↦ (Finset.mem_erase.mp hχ).1 (Subtype.ext he)) hGRH hT hambient
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_erase_of_mem (Finset.mem_univ (1 : S)), Finset.card_univ] at hrest
  have heq := Finset.sum_erase_eq_sub (f := F) (Finset.mem_univ (1 : S))
  change
    Complex.reCLM (∑ χ : S, ∑' n : ℕ, gammaMellinKernel.summand χ.val.primitiveCharacter x n) ≤ _
  rw [map_sum]
  change (∑ χ : S, F χ) ≤ _
  linarith only [h1, hrest, heq]

/-- Under GRH, q ≥ 20000, T ≥ 35000 and log q ≤ T+2, absence of eligible
outside primes through (4/5)T² forces the displayed main-term and local-loss inequality.
Combine the primitive average and actual ramp lower bound, then reduce the index to two.
The level logarithm remains in the character term while the cutoff uses T. -/
theorem gamma_ramp_subgroup_comparison_uniform_scale {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {T : ℝ} (hT : 35000 ≤ T)
    (hambient : Real.log q ≤ T + 2)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (4 / 5 : ℝ) * T ^ 2 → residueInSubgroup q H p) :
    let x := (32 / 99 : ℝ) * T ^ 2;
    (2 * (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) - 1) * Real.sqrt x ≤
      (11783423 / 25000000 : ℝ) * Real.log q + 40159 / 900 +
        2 *
          (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x ((99 / 40 : ℝ) * x) q /
            Real.sqrt x) := by
  classical
  let x := (32 / 99 : ℝ) * T ^ 2
  have hxlarge := Analysis.common_nonOne_ramp_scale_large hT
  have hx : 1 ≤ x := (by norm_num only : (1 : ℝ) ≤ (17 / 5) ^ 16).trans hxlarge
  have hs0 := Real.sqrt_pos.mpr (zero_lt_one.trans_le hx)
  have hs : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → residueInSubgroup q H p := by
    intro p hp hd hc
    apply hsmall p hp hd
    convert hc using 1
    dsimp only [x]
    ring
  have hu :=
    gamma_primitive_average_re_le_uniform_scale hq (NumberTheory.subgroupAnnihilator H) hGRH hT
      hambient
  rw [NumberTheory.card_subgroupAnnihilator] at hu
  change
    Complex.reCLM
        (∑ χ : NumberTheory.subgroupAnnihilator H,
          ∑' n : ℕ, gammaMellinKernel.summand χ.val.primitiveCharacter x n) ≤
      _ at hu
  rw [map_sum] at hu
  change
    (∑ χ : NumberTheory.subgroupAnnihilator H,
        (∑' n : ℕ, gammaMellinKernel.summand χ.val.primitiveCharacter x n).re) ≤
      Real.sqrt x + 3 / 20 +
        ((H.index - 1 : ℕ) : ℝ) * ((11783423 / 25000000 : ℝ) * Real.log q + 2755 / 90) at hu
  have hr := gamma_ramp_subgroup_comparison H (zero_lt_one.trans_le hx) hs
  have hramp := PseudoPrime.LLS.gamma_ramp_sum_lower_variable hGRH.riemann hx
  have he := (div_le_iff₀ hs0).mpr (Analysis.common_nonOne_ramp_error_numerator hT)
  have hlow :
    (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) * Real.sqrt x - 693 / 100 ≤
      AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x := by
    linarith only [hramp, he]
  have hm := mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg H.index)
  have hi := Subgroup.one_lt_index_of_ne_top hH
  have hiR : (2 : ℝ) ≤ H.index := by exact_mod_cast hi
  rw [Nat.cast_sub hi.le, Nat.cast_one] at hu
  have hI : (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) ≤ 1 := by
    rw [Analysis.exponentialRampWeight_integral]
    have he := Real.exp_le_exp.mpr (show -(99 / 40 : ℝ) ≤ -(247 / 100 : ℝ) by norm_num only)
    have hd := div_nonneg (sub_nonneg.mpr he) (by norm_num only : (0 : ℝ) ≤ 1 / 200)
    linarith only [hd]
  have hD :
    0 ≤
      AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x ((99 / 40 : ℝ) * x) q /
        Real.sqrt x := by
    apply div_nonneg _ (Real.sqrt_nonneg x)
    unfold AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum
    exact
      Finset.sum_nonneg
        (fun n _ ↦ mul_nonneg (Real.exp_pos _).le ArithmeticFunction.vonMangoldt_nonneg)
  apply gamma_uniform_index_two_scalar hiR hI (Real.sqrt_nonneg x) hD
  linarith only [hm, hr, hu]

/-- Under GRH and the common scale entrance, a strict scalar budget gives a
prime coprime to q outside any proper unit subgroup through (4/5)T².
Contradict the uniform ramp comparison using the certified main-term gap.
The scale may be larger or smaller than log q when the stated budget holds. -/
theorem exists_prime_outside_le_gamma_four_fifths_scale {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {T : ℝ} (hT : 35000 ≤ T)
    (hambient : Real.log q ≤ T + 2)
    (hbudget :
      (11783423 / 25000000 : ℝ) * Real.log q + 40159 / 900 +
          2 *
            (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum ((32 / 99 : ℝ) * T ^ 2)
                ((4 / 5 : ℝ) * T ^ 2) q /
              Real.sqrt ((32 / 99 : ℝ) * T ^ 2)) <
        (11783423 / 25000000 + 1 / 795 : ℝ) * T) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ ¬residueInSubgroup q H p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * T ^ 2 := by
  classical
  by_contra hn
  have hsmall (p : ℕ) (hp : p.Prime) (hd : ¬p ∣ q) (hb : (p : ℝ) ≤ (4 / 5 : ℝ) * T ^ 2) :
    residueInSubgroup q H p := by
    by_contra hout
    exact hn ⟨p, hp, hd, hout, hb⟩
  have hc := gamma_ramp_subgroup_comparison_uniform_scale hq H hH hGRH hT hambient hsmall
  have he : (99 / 40 : ℝ) * ((32 / 99 : ℝ) * T ^ 2) = (4 / 5 : ℝ) * T ^ 2 := by ring
  dsimp only at hc
  rw [he] at hc
  have hm := Analysis.nonOne_main_term_gap (show 0 < T by linarith only [hT])
  linarith only [hc, hbudget, hm]

end PseudoPrime.LLS.PaperStatements
