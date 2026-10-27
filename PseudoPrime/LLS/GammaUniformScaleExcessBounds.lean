/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaUniformScaleBounds

/-! # Uniform Gamma bounds without a scale-to-level restriction

An explicit positive-part contour error allows the scale T to differ arbitrarily
from log q. Signed logarithmic and constant corrections enter through T, without
assuming that either correction is positive.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For ambient logarithm L and scale T, define the additional contour error
needed when L exceeds T+2. It is the positive excess times the pole and left-line
coefficients at x=(32/99)T². No sign restriction is imposed on L-T.
This quantity permits negative logarithmic and constant corrections. -/
noncomputable def gammaScaleExcess (L T : ℝ) : ℝ :=
  let x := (32 / 99 : ℝ) * T ^ 2;
  ((7 / 6 : ℝ) / Real.sqrt x + (16 / 5 : ℝ) * x ^ (-9 / 16 : ℝ)) * max 0 (L - T - 2)

/-- Under GRH, q ≥ 20000 and T ≥ 35000, every nonprincipal primitive Gamma
sum at x=(32/99)T² is at most M log q+2755/90 plus the explicit scale excess.
Bound the conductor by q and split each contour term at ambient value T+2.
This upper bound does not require log q ≤ T+2. -/
theorem gamma_primitiveCharacter_sum_re_le_signed_scale {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {T : ℝ} (hT : 35000 ≤ T) :
    let x := (32 / 99 : ℝ) * T ^ 2;
    (∑' n : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x n).re ≤
      (11783423 / 25000000 : ℝ) * Real.log q + 2755 / 90 + gammaScaleExcess (Real.log q) T := by
  let x := (32 / 99 : ℝ) * T ^ 2
  have hxlarge := Analysis.common_nonOne_ramp_scale_large hT
  have hx : 1 ≤ x := (by norm_num only : (1 : ℝ) ≤ (17 / 5) ^ 16).trans hxlarge
  have hs := Analysis.ramp_scale_sqrt_lower (show (0 : ℝ) ≤ T by linarith only [hT])
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hfpos : (0 : ℝ) < χ.conductor := by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hmqR : (χ.conductor : ℝ) ≤ q := by exact_mod_cast hmq
  have hlogf := Real.log_le_log hfpos hmqR
  have hs0 := Real.sqrt_pos.mpr (zero_lt_one.trans_le hx)
  let D := max 0 (Real.log q - T - 2)
  have hdelta : Real.log q - T - 2 ≤ D := le_max_right _ _
  have hpole0 := common_nonOne_pole_budget hT hs (le_refl (T + 2))
  have hpnum : (7 / 6 : ℝ) * Real.log q + 4 ≤ (7 / 6 : ℝ) * (T + 2) + 4 + (7 / 6 : ℝ) * D := by
    linarith only [hdelta]
  have hpole :
    ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x ≤ 21 / 10 + ((7 / 6 : ℝ) * D) / Real.sqrt x := by
    calc
      _ ≤ ((7 / 6 : ℝ) * (T + 2) + 4 + (7 / 6 : ℝ) * D) / Real.sqrt x :=
        div_le_div_of_nonneg_right hpnum hs0.le
      _ = ((7 / 6 : ℝ) * (T + 2) + 4) / Real.sqrt x + ((7 / 6 : ℝ) * D) / Real.sqrt x :=
        add_div _ _ _
      _ ≤ _ := add_le_add_left hpole0 _
  have hleft0 :=
    common_nonOne_left_budget hT hxlarge hs (show 0 ≤ T + 2 by linarith only [hT]) (le_refl (T + 2))
  have hlnum :
    (16 / 5 : ℝ) * (Real.log χ.conductor + 283) + 5 / 3 ≤
      (16 / 5 : ℝ) * (T + 2 + 283) + 5 / 3 + (16 / 5 : ℝ) * D := by
    linarith only [hdelta, hlogf]
  have hleft :
    x ^ (-9 / 16 : ℝ) * ((16 / 5 : ℝ) * (Real.log χ.conductor + 283) + 5 / 3) ≤
      17 / 10 + x ^ (-9 / 16 : ℝ) * ((16 / 5 : ℝ) * D) := by
    calc
      _ ≤ x ^ (-9 / 16 : ℝ) * ((16 / 5 : ℝ) * (T + 2 + 283) + 5 / 3 + (16 / 5 : ℝ) * D) :=
        mul_le_mul_of_nonneg_left hlnum (Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) _).le
      _ =
          x ^ (-9 / 16 : ℝ) * ((16 / 5 : ℝ) * (T + 2 + 283) + 5 / 3) +
            x ^ (-9 / 16 : ℝ) * ((16 / 5 : ℝ) * D) :=
        mul_add _ _ _
      _ ≤ _ := add_le_add_left hleft0 _
  have hlead := mul_le_mul_of_nonneg_left hlogf (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
  have hu :=
    gamma_primitiveCharacter_sum_re_le_variable_prefix_scale hq χ hne hGRH hx 32
      Analysis.gammaResolvent_thirtyTwo_error_lt
  have he :
    gammaScaleExcess (Real.log q) T =
      ((7 / 6 : ℝ) * D) / Real.sqrt x + x ^ (-9 / 16 : ℝ) * ((16 / 5 : ℝ) * D) := by
    dsimp only [gammaScaleExcess, D, x]
    ring
  rw [he]
  linarith only [hu, hpole, hleft, hlead]

/-- Under GRH and the scale entrance, the primitive average over a finite
character subgroup has the common principal allowance and one nonprincipal
allowance including the scale excess per nonidentity element.
Split the identity from the finite sum and apply the signed-scale character bound.
This supplies the upper side for unrestricted signed corrections. -/
theorem gamma_primitive_average_re_le_signed_scale {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (S : Subgroup (DirichletCharacter ℂ q)) [Fintype S]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {T : ℝ} (hT : 35000 ≤ T) :
    let x := (32 / 99 : ℝ) * T ^ 2;
    (∑ χ : S, ∑' n : ℕ, gammaMellinKernel.summand χ.val.primitiveCharacter x n).re ≤
      Real.sqrt x + 3 / 20 +
        ((Fintype.card S - 1 : ℕ) : ℝ) *
          ((11783423 / 25000000 : ℝ) * Real.log q + gammaScaleExcess (Real.log q) T +
            2755 / 90) := by
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
        ((11783423 / 25000000 : ℝ) * Real.log q + gammaScaleExcess (Real.log q) T + 2755 / 90) := by
    calc
      _ ≤
          ∑ _χ ∈ Finset.univ.erase (1 : S),
            ((11783423 / 25000000 : ℝ) * Real.log q + gammaScaleExcess (Real.log q) T +
              2755 / 90) :=
        by
        apply Finset.sum_le_sum
        intro χ hχ
        have hc :=
          gamma_primitiveCharacter_sum_re_le_signed_scale hq χ.val
            (fun he ↦ (Finset.mem_erase.mp hχ).1 (Subtype.ext he)) hGRH hT
        linarith only [hc]
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_erase_of_mem (Finset.mem_univ (1 : S)), Finset.card_univ] at hrest
  have heq := Finset.sum_erase_eq_sub (f := F) (Finset.mem_univ (1 : S))
  change
    Complex.reCLM (∑ χ : S, ∑' n : ℕ, gammaMellinKernel.summand χ.val.primitiveCharacter x n) ≤ _
  rw [map_sum]
  change (∑ χ : S, F χ) ≤ _
  linarith only [h1, hrest, heq]

/-- Under GRH, q ≥ 20000 and T ≥ 35000, absence of eligible outside primes
through (4/5)T² forces the displayed scalar comparison with the scale excess.
Combine the actual ramp lower bound and signed primitive average, reducing the index to two.
No comparison between T and log q is required. -/
theorem gamma_ramp_subgroup_comparison_signed_scale {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {T : ℝ} (hT : 35000 ≤ T)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (4 / 5 : ℝ) * T ^ 2 → residueInSubgroup q H p) :
    let x := (32 / 99 : ℝ) * T ^ 2;
    (2 * (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) - 1) * Real.sqrt x ≤
      (11783423 / 25000000 : ℝ) * Real.log q + gammaScaleExcess (Real.log q) T + 40159 / 900 +
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
    gamma_primitive_average_re_le_signed_scale hq (NumberTheory.subgroupAnnihilator H) hGRH hT
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
        ((H.index - 1 : ℕ) : ℝ) *
          ((11783423 / 25000000 : ℝ) * Real.log q + gammaScaleExcess (Real.log q) T +
            2755 / 90) at hu
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

/-- Under GRH, q ≥ 20000 and T ≥ 35000, the displayed strict budget yields
a prime coprime to q outside any proper unit subgroup through (4/5)T².
Contradict the signed-scale comparison and certified main-term gap.
This interface accepts any real logarithmic or constant corrections satisfying the budget. -/
theorem exists_prime_outside_le_gamma_four_fifths_signed_scale {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {T : ℝ} (hT : 35000 ≤ T)
    (hbudget :
      (11783423 / 25000000 : ℝ) * Real.log q + gammaScaleExcess (Real.log q) T + 40159 / 900 +
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
  have hc := gamma_ramp_subgroup_comparison_signed_scale hq H hH hGRH hT hsmall
  have he : (99 / 40 : ℝ) * ((32 / 99 : ℝ) * T ^ 2) = (4 / 5 : ℝ) * T ^ 2 := by ring
  dsimp only at hc
  rw [he] at hc
  have hm := Analysis.nonOne_main_term_gap (show 0 < T by linarith only [hT])
  linarith only [hc, hbudget, hm]

end PseudoPrime.LLS.PaperStatements
