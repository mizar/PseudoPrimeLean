/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaConductorFreeNonOneBounds
public import PseudoPrime.LLS.GammaUniformSubgroupComparison

/-! # Conductor-free subgroup Gamma comparison from log scale 30000 -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a finite real family, one distinguished bound A and a common
bound B elsewhere give A+(card-1)B for the total. No signs of A or B
are required. Split off the distinguished point and bound its complement.
This is the reusable finite-average step for primitive character sums. -/
theorem sum_le_distinguished_and_common {ι : Type*} [Fintype ι] (a : ι) (f : ι → ℝ) {A B : ℝ}
    (ha : f a ≤ A) (hb : ∀ i, i ≠ a → f i ≤ B) :
    (∑ i, f i) ≤ A + ((Fintype.card ι : ℝ) - 1) * B := by
  classical
  have hrest : (∑ i ∈ Finset.univ.erase a, f i) ≤ ((Finset.univ.erase a).card : ℝ) * B := by
    calc
      _ ≤ ∑ _i ∈ Finset.univ.erase a, B :=
        Finset.sum_le_sum (fun i hi ↦ hb i (Finset.mem_erase.mp hi).1)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : 1 ≤ Fintype.card ι := Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ⟨a⟩)
  rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Nat.cast_sub hcard,
    Nat.cast_one] at hrest
  have he := Finset.sum_erase_add Finset.univ f (Finset.mem_univ a)
  linarith only [ha, hrest, he]

/-- For h ≥ 2 and I ≤ 1, a nonnegative scale root, principal error P,
ramp error R and local loss D, the displayed index comparison implies
(2I-1)s ≤ A+P+2R+2D. Subtract the index-two comparison and keep the
nonnegative excess terms. This isolates index reduction from all analytic constants. -/
theorem gamma_index_two_scalar_general {h I s A P R D : ℝ} (hh : 2 ≤ h) (hI : I ≤ 1) (hs : 0 ≤ s)
    (hP : 0 ≤ P) (hR : 0 ≤ R) (hD : 0 ≤ D) (hb : h * (I * s - R) ≤ s + P + (h - 1) * A + h * D) :
    (2 * I - 1) * s ≤ A + P + 2 * R + 2 * D := by
  have hp := mul_nonneg (mul_nonneg (sub_nonneg.mpr hh) (sub_nonneg.mpr hI)) hs
  have he := mul_nonneg (sub_nonneg.mpr hh) (add_nonneg (add_nonneg hP hR) hD)
  by_contra hn
  have hg := mul_pos (show 0 < h - 1 by linarith only [hh]) (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith only [hp, he, hg, hb, hh]

/-- Under GRH at q ≥ 20000 and log q ≥ 30000, every nonprincipal primitive
Gamma sum at x=(32/99)(log q)² is at most M log q+2181/100.
Use the thirty-two-term zero certificate, conductor-free remainder and common
pole/left budgets. Quadraticity is not required, so all annihilator characters qualify. -/
theorem gamma_primitiveCharacter_sum_re_le_conductor_free_uniform {q : ℕ} [NeZero q]
    (hq : 20000 ≤ q) (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 30000 ≤ Real.log q) :
    let x := (32 / 99 : ℝ) * (Real.log q) ^ 2;
    (∑' k : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x k).re ≤
      (11783423 / 25000000 : ℝ) * Real.log q + 2181 / 100 := by
  let x := (32 / 99 : ℝ) * (Real.log q) ^ 2
  have hx : 2 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (Real.log q - 30000)]
  have hx1 : 1 ≤ x := le_trans (by norm_num only : (1 : ℝ) ≤ 2) hx
  have hs := Analysis.ramp_scale_sqrt_lower (show 0 ≤ Real.log q by linarith only [hL])
  have hl := Analysis.conductor_free_nonOne_cutoff_log hL
  have he := conductor_free_nonOne_error_budgets hL hx1 hs hl
  have hpole :=
    gamma_tail_pole_budget (show (15000 : ℝ) ≤ Real.log q by linarith only [hL]) hs
      (show Real.log q ≤ Real.log q + 2 by linarith only)
  have hu :=
    gamma_primitiveCharacter_sum_re_le_conductor_free_prefix hq χ hne hGRH hx 32
      Analysis.gammaResolvent_thirtyTwo_error_lt
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hf : (0 : ℝ) < χ.conductor := by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hmqR : (χ.conductor : ℝ) ≤ q := by exact_mod_cast hmq
  have hlead :=
    mul_le_mul_of_nonneg_left (Real.log_le_log hf hmqR)
      (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
  linarith only [hu, hpole, he.1, hlead]

/-- For a finite character subgroup under GRH, q ≥ 20000 and log q ≥ 30000,
the actual primitive aggregate is at most sqrt(x)+3/20 plus M log q+2181/100
for each nonidentity character. Apply the generic finite-family bound and
separate the principal primitive character. This supplies the subgroup upper side. -/
theorem gamma_primitive_average_re_le_conductor_free_uniform {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (S : Subgroup (DirichletCharacter ℂ q)) [Fintype S]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 30000 ≤ Real.log q) :
    let x := (32 / 99 : ℝ) * (Real.log q) ^ 2;
    (∑ χ : S, ∑' k : ℕ, gammaMellinKernel.summand χ.val.primitiveCharacter x k).re ≤
      Real.sqrt x + 3 / 20 +
        ((Fintype.card S : ℝ) - 1) * ((11783423 / 25000000 : ℝ) * Real.log q + 2181 / 100) := by
  let x := (32 / 99 : ℝ) * (Real.log q) ^ 2
  have hx : 1 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (Real.log q - 30000)]
  have hs := Analysis.ramp_scale_sqrt_lower (show 0 ≤ Real.log q by linarith only [hL])
  have he :=
    conductor_free_nonOne_error_budgets hL hx hs (Analysis.conductor_free_nonOne_cutoff_log hL)
  let F := fun χ : S ↦ (∑' k : ℕ, gammaMellinKernel.summand χ.val.primitiveCharacter x k).re
  have hp := PseudoPrime.LLS.gamma_level_one_sum_upper_variable hGRH.riemann hx
  have h1 : F 1 ≤ Real.sqrt x + 3 / 20 := by
    dsimp only [F]
    rw [Subgroup.coe_one,
      tsum_congr
        (MellinKernel.principal_primitive_summand_eq_level_one gammaMellinKernel (q := q) x)]
    linarith only [hp, he.2.1]
  have hrest : ∀ χ : S, χ ≠ 1 → F χ ≤ (11783423 / 25000000 : ℝ) * Real.log q + 2181 / 100 := by
    intro χ hχ
    exact
      gamma_primitiveCharacter_sum_re_le_conductor_free_uniform hq χ.val
        (fun heq ↦ hχ (Subtype.ext heq)) hGRH hL
  have hsum := sum_le_distinguished_and_common (1 : S) F h1 hrest
  change
    Complex.reCLM (∑ χ : S, ∑' k : ℕ, gammaMellinKernel.summand χ.val.primitiveCharacter x k) ≤ _
  rw [map_sum]
  exact hsum

/-- Under GRH, q ≥ 20000, log q ≥ 30000 and a proper unit subgroup,
absence of outside primes through (4/5)(log q)² forces the conductor-free
scalar budget M log q+899/25 plus twice the exact nonunit loss.
Use the actual primitive average, ramp lower bound and generic index reduction.
The retained nonunit loss can be removed in the Miller-Rabin no-witness branch. -/
theorem gamma_ramp_subgroup_comparison_conductor_free {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 30000 ≤ Real.log q)
    (hsmall :
      ∀ p : ℕ,
        p.Prime → ¬p ∣ q → (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q) ^ 2 → residueInSubgroup q H p) :
    let x := (32 / 99 : ℝ) * (Real.log q) ^ 2;
    (2 * (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) - 1) * Real.sqrt x ≤
      (11783423 / 25000000 : ℝ) * Real.log q + 899 / 25 +
        2 *
          (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x ((99 / 40 : ℝ) * x) q /
            Real.sqrt x) := by
  classical
  let x := (32 / 99 : ℝ) * (Real.log q) ^ 2
  have hx : 1 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (Real.log q - 30000)]
  have hs : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → residueInSubgroup q H p := by
    intro p hp hd hc
    apply hsmall p hp hd
    convert hc using 1
    dsimp only [x]
    ring
  have hu :=
    gamma_primitive_average_re_le_conductor_free_uniform hq (NumberTheory.subgroupAnnihilator H)
      hGRH hL
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
        ((H.index : ℝ) - 1) * ((11783423 / 25000000 : ℝ) * Real.log q + 2181 / 100) at hu
  have hr := gamma_ramp_subgroup_comparison H (zero_lt_one.trans_le hx) hs
  have hT := PseudoPrime.LLS.gamma_ramp_sum_lower_variable hGRH.riemann hx
  have he :=
    (conductor_free_nonOne_error_budgets hL hx
        (Analysis.ramp_scale_sqrt_lower (show 0 ≤ Real.log q by linarith only [hL]))
        (Analysis.conductor_free_nonOne_cutoff_log hL)).2.2.1
  have hlow :
    (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) * Real.sqrt x - 7 ≤
      AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x := by
    linarith only [hT, he]
  have hm := mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg H.index)
  have hi := Subgroup.one_lt_index_of_ne_top hH
  have hiR : (2 : ℝ) ≤ H.index := by exact_mod_cast hi
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
  have hb :
    (H.index : ℝ) *
        ((∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) * Real.sqrt x - 7) ≤
      Real.sqrt x + 3 / 20 +
        ((H.index : ℝ) - 1) * ((11783423 / 25000000 : ℝ) * Real.log q + 2181 / 100) +
        (H.index : ℝ) *
          (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x ((99 / 40 : ℝ) * x) q /
            Real.sqrt x) := by
    linarith only [hm, hr, hu]
  have hc :=
    gamma_index_two_scalar_general hiR hI (Real.sqrt_nonneg x) (by norm_num only : (0 : ℝ) ≤ 3 / 20)
      (by norm_num only : (0 : ℝ) ≤ 7) hD hb
  linarith only [hc]

end PseudoPrime.LLS.PaperStatements
