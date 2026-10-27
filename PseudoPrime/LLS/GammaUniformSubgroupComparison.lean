/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaNonOneCommonNumerics
public import PseudoPrime.LLS.GammaVariablePrefixCharacterBounds
public import PseudoPrime.LLS.GammaVariablePrincipalBounds
public import PseudoPrime.LLS.GammaSubgroupComparison
public import PseudoPrime.LLS.GammaUniformLocalBounds

/-! # Uniform Gamma ramp comparison for proper subgroups

The thirty-two-term zero certificate and variable contour bounds apply to every
nonprincipal character. A signed primitive average and the exact nonunit loss
give a scalar comparison uniform in the subgroup index.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, q ≥ 20000 and log q ≥ 35000, every nonprincipal character's
primitive Gamma sum at x=(32/99)(log q)^2 is at most M log q + 2755/90.
Use the thirty-two-term certificate and common pole and left-contour budgets.
This upper bound requires neither quadraticity nor a conductor restriction. -/
theorem gamma_primitiveCharacter_sum_re_le_uniform_thirtyTwo {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 35000 ≤ Real.log q) :
    let x := (32 / 99 : ℝ) * (Real.log q) ^ 2;
    (∑' n : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x n).re ≤
      (11783423 / 25000000 : ℝ) * Real.log q + 2755 / 90 := by
  let x := (32 / 99 : ℝ) * (Real.log q) ^ 2
  have hxlarge := Analysis.common_nonOne_ramp_scale_large hL
  have hx : 1 ≤ x := (by norm_num only : (1 : ℝ) ≤ (17 / 5) ^ 16).trans hxlarge
  have hs := Analysis.ramp_scale_sqrt_lower (show (0 : ℝ) ≤ Real.log q by linarith only [hL])
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hfpos : (0 : ℝ) < χ.conductor := by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hmqR : (χ.conductor : ℝ) ≤ q := by exact_mod_cast hmq
  have hlogf := Real.log_le_log hfpos hmqR
  have hf0 : 0 ≤ Real.log χ.conductor :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr χ.conductor_ne_zero)
  have hpole := common_nonOne_pole_budget hL hs (show Real.log q ≤ Real.log q + 2 by linarith only)
  have hleft :=
    common_nonOne_left_budget hL hxlarge hs hf0
      (show Real.log χ.conductor ≤ Real.log q + 2 by linarith only [hlogf])
  have hlead := mul_le_mul_of_nonneg_left hlogf (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
  have hu :=
    gamma_primitiveCharacter_sum_re_le_variable_prefix_scale hq χ hne hGRH hx 32
      Analysis.gammaResolvent_thirtyTwo_error_lt
  linarith only [hu, hpole, hleft, hlead]

/-- Under GRH at q ≥ 20000 and log q ≥ 35000, the primitive average over
a finite character subgroup is at most sqrt x + 3/20 plus one common nonprincipal
budget per nonidentity element. Separate the identity and sum the character bounds.
This is the analytic upper side of the uniform proper-subgroup comparison. -/
theorem gamma_primitive_average_re_le_uniform_thirtyTwo {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (S : Subgroup (DirichletCharacter ℂ q)) [Fintype S]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 35000 ≤ Real.log q) :
    let x := (32 / 99 : ℝ) * (Real.log q) ^ 2;
    (∑ χ : S, ∑' n : ℕ, gammaMellinKernel.summand χ.val.primitiveCharacter x n).re ≤
      Real.sqrt x + 3 / 20 +
        ((Fintype.card S - 1 : ℕ) : ℝ) * ((11783423 / 25000000 : ℝ) * Real.log q + 2755 / 90) := by
  classical
  let x := (32 / 99 : ℝ) * (Real.log q) ^ 2
  have hxlarge := Analysis.common_nonOne_ramp_scale_large hL
  have hx : 1 ≤ x := (by norm_num only : (1 : ℝ) ≤ (17 / 5) ^ 16).trans hxlarge
  have hs0 := Real.sqrt_pos.mpr (zero_lt_one.trans_le hx)
  let F := fun χ : S ↦ (∑' n : ℕ, gammaMellinKernel.summand χ.val.primitiveCharacter x n).re
  have hP := PseudoPrime.LLS.gamma_level_one_sum_upper_variable hGRH.riemann hx
  have he := (div_le_iff₀ hs0).mpr (Analysis.common_nonOne_exponential_error hL)
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
          gamma_primitiveCharacter_sum_re_le_uniform_thirtyTwo hq χ.val
            (fun he ↦ (Finset.mem_erase.mp hχ).1 (Subtype.ext he)) hGRH hL
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_erase_of_mem (Finset.mem_univ (1 : S)), Finset.card_univ] at hrest
  have heq := Finset.sum_erase_eq_sub (f := F) (Finset.mem_univ (1 : S))
  change
    Complex.reCLM (∑ χ : S, ∑' n : ℕ, gammaMellinKernel.summand χ.val.primitiveCharacter x n) ≤ _
  rw [map_sum]
  change (∑ χ : S, F χ) ≤ _
  linarith only [h1, hrest, heq]

/-- At x > 0, the normalized finite ramp Mangoldt sum is at most the finite
level-one Gamma sum through (99/40)x. Compare the weights at each positive index.
This transfers the ramp lower side to the existing finite subgroup interface. -/
theorem gamma_ramp_le_finite_exponential {x : ℝ} (hx : 0 < x) :
    AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(99 / 40 : ℝ) * x⌋₊,
        (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re := by
  rw [gamma_level_one_sum_eq_exponential hx]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg x)
  unfold AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum
    AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
  simp only [Nat.cast_zero, neg_zero, zero_div, Real.exp_zero, ArithmeticFunction.map_zero,
    mul_zero, zero_add]
  rw [mul_comm x (99 / 40 : ℝ)]
  apply Finset.sum_le_sum
  intro n _
  exact
    (mul_le_mul_of_nonneg_left (Analysis.exponentialRampWeight_bounds ((n : ℝ) / x)).2
          ArithmeticFunction.vonMangoldt_nonneg).trans_eq
      (by rw [neg_div, mul_comm])

/-- For nonzero q and x > 0, if all eligible primes through (99/40)x lie in H,
the index multiple of the normalized ramp sum is at most the primitive aggregate
plus the index multiple of the exact nonunit loss. Compare ramp and exponential
weights, then use the signed primitive-average comparison. -/
theorem gamma_ramp_subgroup_comparison {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) {x : ℝ}
    (hx : 0 < x)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → residueInSubgroup q H p) :
    (H.index : ℝ) * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) ≤
      ∑ χ : NumberTheory.subgroupAnnihilator H,
          (∑' n : ℕ, gammaMellinKernel.summand χ.val.primitiveCharacter x n).re +
        (H.index : ℝ) *
          (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x ((99 / 40 : ℝ) * x) q /
            Real.sqrt x) := by
  have hr := gamma_ramp_le_finite_exponential hx
  have hd := gamma_principal_sum_level_difference (q := q) (y := (99 / 40 : ℝ) * x) hx
  have hu :=
    MellinKernel.principal_sum_le_primitive_average_of_noSmallPrimes gammaMellinKernel H hx hsmall
  have he : Finset.Icc 1 ⌊(99 / 40 : ℝ) * x⌋₊ = Finset.Ioc 0 ⌊(99 / 40 : ℝ) * x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Nat.succ_le_iff]
  rw [he] at hu
  have hm := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg H.index)
  nlinarith only [hd, hu, hm]

/-- For h ≥ 2, ramp mass I ≤ 1, scale root s ≥ 0 and local loss D ≥ 0,
the displayed index comparison implies the index-two scalar budget.
Expand the inequalities and use (h-2)(1-I)s ≥ 0 and (h-2)D ≥ 0.
This proves that index two is the worst case for the uniform comparison. -/
theorem gamma_uniform_index_two_scalar {h I s A D : ℝ} (hh : 2 ≤ h) (hI : I ≤ 1) (hs : 0 ≤ s)
    (hD : 0 ≤ D) (hb : h * (I * s - 693 / 100) ≤ s + 3 / 20 + (h - 1) * (A + 2755 / 90) + h * D) :
    (2 * I - 1) * s ≤ A + 40159 / 900 + 2 * D := by
  have hp := mul_nonneg (mul_nonneg (sub_nonneg.mpr hh) (sub_nonneg.mpr hI)) hs
  have hd := mul_nonneg (sub_nonneg.mpr hh) hD
  by_contra hn
  have hg := mul_pos (show 0 < h - 1 by linarith only [hh]) (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith only [hp, hd, hg, hb, hh]

/-- Under GRH, q ≥ 20000, log q ≥ 35000 and H proper, absence of eligible
outside primes through (4/5)(log q)^2 forces the displayed scalar budget.
Combine the actual ramp lower bound and thirty-two-term primitive upper average,
then reduce every subgroup index to the worst case two. The local loss is retained. -/
theorem gamma_ramp_subgroup_comparison_uniform {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 35000 ≤ Real.log q)
    (hsmall :
      ∀ p : ℕ,
        p.Prime → ¬p ∣ q → (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q) ^ 2 → residueInSubgroup q H p) :
    let x := (32 / 99 : ℝ) * (Real.log q) ^ 2;
    (2 * (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) - 1) * Real.sqrt x ≤
      (11783423 / 25000000 : ℝ) * Real.log q + 40159 / 900 +
        2 *
          (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x ((99 / 40 : ℝ) * x) q /
            Real.sqrt x) := by
  classical
  let x := (32 / 99 : ℝ) * (Real.log q) ^ 2
  have hxlarge := Analysis.common_nonOne_ramp_scale_large hL
  have hx : 1 ≤ x := (by norm_num only : (1 : ℝ) ≤ (17 / 5) ^ 16).trans hxlarge
  have hs0 := Real.sqrt_pos.mpr (zero_lt_one.trans_le hx)
  have hs : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → residueInSubgroup q H p := by
    intro p hp hd hc
    apply hsmall p hp hd
    convert hc using 1
    dsimp only [x]
    ring
  have hu :=
    gamma_primitive_average_re_le_uniform_thirtyTwo hq (NumberTheory.subgroupAnnihilator H) hGRH hL
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
  have hT := PseudoPrime.LLS.gamma_ramp_sum_lower_variable hGRH.riemann hx
  have he := (div_le_iff₀ hs0).mpr (Analysis.common_nonOne_ramp_error_numerator hL)
  have hlow :
    (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) * Real.sqrt x - 693 / 100 ≤
      AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x := by
    linarith only [hT, he]
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

end PseudoPrime.LLS.PaperStatements
