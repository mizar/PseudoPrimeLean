/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PoissonMassFiveHalves
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PoissonZeroSum
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorMultiplicityBridge
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorVerticalGrowth
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.Analysis.Meromorphic.Divisor

/-! # Explicit inverse-square tail for Dirichlet zeros -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- If `H > 0` and `|y| > H`, an inverse square is at most `2 / H` times the
Poisson weight at height `H`. Compare positive denominators using `H² ≤ y²`.
This transfers full Poisson mass bounds to high-zero tails. -/
theorem inv_sq_le_poisson {H y : ℝ} (hH : 0 < H) (hy : H < |y|) :
    1 / y ^ 2 ≤ (2 / H) * (H / (H ^ 2 + y ^ 2)) := by
  have hy0 : 0 < y ^ 2 :=
    sq_pos_of_ne_zero
      (by
        intro e
        rw [e, abs_zero] at hy
        linarith only [hH, hy])
  have hden : 0 < H ^ 2 + y ^ 2 := add_pos (sq_pos_of_pos hH) hy0
  have hsq : H ^ 2 ≤ y ^ 2 := by
    have ha := sq_abs y
    have hb := sq_nonneg (|y| - H)
    nlinarith only [ha, hb, hy, hH]
  have he : (2 / H) * (H / (H ^ 2 + y ^ 2)) = 2 / (H ^ 2 + y ^ 2) := by
    rw [div_mul_div_comm, mul_comm H (H ^ 2 + y ^ 2), mul_div_mul_right _ _ (ne_of_gt hH)]
  rw [he, div_le_div_iff₀ hy0 hden]
  nlinarith only [hsq]

/-- Under individual GRH, the divisor-weighted Poisson term at a real parameter is
the same as the expression in the ordinate alone. A nonzero divisor is supported
on the critical line; a zero divisor makes both expressions vanish. This allows
the height-tail comparison without assuming conjugate symmetry of the zeros. -/
theorem poisson_term_eq_ordinate {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (ρ : ℂ) (H : ℝ) :
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        (H / Complex.normSq ((((H + 1 / 2 : ℝ) : ℂ)) - ρ)) =
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * (H / (H ^ 2 + ρ.im ^ 2)) := by
  by_cases hd : MeromorphicOn.divisor χ.completedLFunction Set.univ ρ = 0
  · simp only [hd, Int.cast_zero, zero_mul]
  · have hr :=
      completed_zero_re_eq_half_of_RH hRH hp hinv (completed_zero_of_divisor_ne_zero hne hd)
    congr 2
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, hr, zero_sub]
    ring

/-- Under the hypotheses of the inverse-square tail bound, the multiplicity-weighted
high-zero series is summable. Dominate it by the summable full Poisson mass.
This allows kernel-weighted tails and finite-to-infinite zero-sum transfers. -/
theorem summable_completed_invSq_tail {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) {H : ℝ}
    (hH : 2 ≤ H) :
    Summable
      (fun ρ : ℂ ↦
        if H < |ρ.im| then (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) / ρ.im ^ 2
        else 0) := by
  have hinv : χ⁻¹ ≠ 1 := inv_ne_one.mpr hne
  have hH0 : 0 < H := by linarith only [hH]
  let D : ℂ → ℝ := fun ρ ↦ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ)
  let P : ℂ → ℝ := fun ρ ↦ D ρ * (H / Complex.normSq ((((H + 1 / 2 : ℝ) : ℂ)) - ρ))
  let T : ℂ → ℝ := fun ρ ↦ if H < |ρ.im| then D ρ / ρ.im ^ 2 else 0
  have ha : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hd (ρ : ℂ) : 0 ≤ D ρ := by
    dsimp only [D]
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ
  have hp0 (ρ : ℂ) : 0 ≤ P ρ := by
    exact mul_nonneg (hd ρ) (div_nonneg hH0.le (Complex.normSq_nonneg _))
  have ht0 (ρ : ℂ) : 0 ≤ T ρ := by
    dsimp only [T]
    split_ifs
    · exact div_nonneg (hd ρ) (sq_nonneg ρ.im)
    · exact le_refl 0
  have hcmp (ρ : ℂ) : T ρ ≤ (2 / H) * P ρ := by
    dsimp only [T]
    split_ifs with hρ
    · have hc := inv_sq_le_poisson hH0 hρ
      have hh := mul_le_mul_of_nonneg_left hc (hd ρ)
      dsimp only [P]
      rw [poisson_term_eq_ordinate hRH hp hne hinv ρ H]
      change D ρ / ρ.im ^ 2 ≤ (2 / H) * (D ρ * (H / (H ^ 2 + ρ.im ^ 2)))
      simpa only [div_eq_mul_inv, one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm] using hh
    · exact mul_nonneg (div_nonneg (by norm_num only) hH0.le) (hp0 ρ)
  have hs : Summable P := by
    have h :=
      summable_completed_poisson_terms hq hRH hp hne hinv (s := (((H + 1 / 2 : ℝ) : ℂ)))
        (by
          simp only [Complex.ofReal_re]
          linarith only [hH])
    simpa only [Complex.ofReal_re, add_sub_cancel_right] using h
  have ht : Summable T := Summable.of_nonneg_of_le ht0 hcmp (hs.mul_left (2 / H))
  exact ht

/-- For a primitive nonprincipal character satisfying individual GRH and real `H ≥ 2`,
the divisor-weighted sum of `1 / ρ.im²` over completed zeros with `|ρ.im| > H` is
strictly less than `log (q * H) / H`. The divisor retains multiplicity, both signs
of the ordinate are included, and a central zero contributes nothing to the tail.
The proof compares each tail term with the full Poisson mass and uses its explicit bound. -/
theorem completed_zero_invSq_tail_lt {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) {H : ℝ}
    (hH : 2 ≤ H) :
    (∑' ρ : ℂ,
        if H < |ρ.im| then (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) / ρ.im ^ 2
        else 0) <
      Real.log ((q : ℝ) * H) / H := by
  have hinv : χ⁻¹ ≠ 1 := inv_ne_one.mpr hne
  have hH0 : 0 < H := by linarith only [hH]
  let D : ℂ → ℝ := fun ρ ↦ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ)
  let P : ℂ → ℝ := fun ρ ↦ D ρ * (H / Complex.normSq ((((H + 1 / 2 : ℝ) : ℂ)) - ρ))
  let T : ℂ → ℝ := fun ρ ↦ if H < |ρ.im| then D ρ / ρ.im ^ 2 else 0
  have ha : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hd (ρ : ℂ) : 0 ≤ D ρ := by
    dsimp only [D]
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ
  have hp0 (ρ : ℂ) : 0 ≤ P ρ := by
    exact mul_nonneg (hd ρ) (div_nonneg hH0.le (Complex.normSq_nonneg _))
  have ht0 (ρ : ℂ) : 0 ≤ T ρ := by
    dsimp only [T]
    split_ifs
    · exact div_nonneg (hd ρ) (sq_nonneg ρ.im)
    · exact le_refl 0
  have hcmp (ρ : ℂ) : T ρ ≤ (2 / H) * P ρ := by
    dsimp only [T]
    split_ifs with hρ
    · have hc := inv_sq_le_poisson hH0 hρ
      have hh := mul_le_mul_of_nonneg_left hc (hd ρ)
      dsimp only [P]
      rw [poisson_term_eq_ordinate hRH hp hne hinv ρ H]
      change D ρ / ρ.im ^ 2 ≤ (2 / H) * (D ρ * (H / (H ^ 2 + ρ.im ^ 2)))
      simpa only [div_eq_mul_inv, one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm] using hh
    · exact mul_nonneg (div_nonneg (by norm_num only) hH0.le) (hp0 ρ)
  have hs : Summable P := by
    have h :=
      summable_completed_poisson_terms hq hRH hp hne hinv (s := (((H + 1 / 2 : ℝ) : ℂ)))
        (by
          simp only [Complex.ofReal_re]
          linarith only [hH])
    simpa only [Complex.ofReal_re, add_sub_cancel_right] using h
  have ht : Summable T := Summable.of_nonneg_of_le ht0 hcmp (hs.mul_left (2 / H))
  have hsum := Summable.tsum_le_tsum hcmp ht (hs.mul_left (2 / H))
  rw [tsum_mul_left] at hsum
  have hm := completed_poissonMass_lt_log hq hRH hp hne hinv hH
  change (∑' ρ : ℂ, P ρ) < _ at hm
  have hc : 0 < 2 / H := div_pos (by norm_num only) hH0
  have hm' := mul_lt_mul_of_pos_left hm hc
  have he : (2 / H) * (Real.log ((q : ℝ) * H) / 2) = Real.log ((q : ℝ) * H) / H := by ring
  change (∑' ρ : ℂ, T ρ) < _
  rw [← he]
  exact hsum.trans_lt hm'

/-- For a primitive nonprincipal character satisfying individual GRH and `H ≥ 2`,
the inverse-square tail of the nontrivial zeros of the ordinary Dirichlet L-function
is strictly below `log (q * H) / H`. The analytic order counts multiplicity and
the critical-line filter includes both signs of the ordinate. The nonvanishing gamma
factor identifies ordinary and completed multiplicities on the critical line. -/
theorem L_zero_invSq_tail_lt {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) {H : ℝ}
    (hH : 2 ≤ H) :
    (∑' ρ : ℂ,
        if ρ.re = 1 / 2 ∧ H < |ρ.im| then (analyticOrderNatAt χ.LFunction ρ : ℝ) / ρ.im ^ 2
        else 0) <
      Real.log ((q : ℝ) * H) / H := by
  have hinv : χ⁻¹ ≠ 1 := inv_ne_one.mpr hne
  have heq (ρ : ℂ) :
    (if ρ.re = 1 / 2 ∧ H < |ρ.im| then (analyticOrderNatAt χ.LFunction ρ : ℝ) / ρ.im ^ 2 else 0) =
      (if H < |ρ.im| then (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) / ρ.im ^ 2
      else 0) := by
    by_cases ht : H < |ρ.im|
    · by_cases hr : ρ.re = 1 / 2
      · have hg :=
          gammaFactor_ne_zero_of_re_pos χ (s := ρ)
            (by
              rw [hr]; norm_num only)
        have hm := zeroMultiplicity_divisor_gamma_ne hne hg
        have hm' :
          (analyticOrderNatAt χ.LFunction ρ : ℝ) =
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) := by
          exact_mod_cast hm
        simp only [hr, ht, and_self, ↓reduceIte, hm']
      · have hd : MeromorphicOn.divisor χ.completedLFunction Set.univ ρ = 0 := by
          by_contra hn
          exact
            hr
              (completed_zero_re_eq_half_of_RH hRH hp hinv
                (completed_zero_of_divisor_ne_zero hne hn))
        simp only [hr, ht, false_and, ↓reduceIte, hd, Int.cast_zero, zero_div]
    · simp only [ht, and_false, ↓reduceIte]
  rw [tsum_congr heq]
  exact completed_zero_invSq_tail_lt hq hRH hp hne hH

/-- A kernel bounded by `B / ρ.im²` above height `H ≥ 2` has a completed-zero tail
of norm at most `B * log (q * H) / H`, for `B ≥ 0`. The zeros are counted with
multiplicity. Domination by the inverse-square tail supplies summability and the
triangle inequality. This is the one-character interface for joint zero sums. -/
theorem norm_completed_zero_tail_le {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) {H B : ℝ}
    (hH : 2 ≤ H) (hB : 0 ≤ B) (K : ℂ → ℂ) (hK : ∀ ρ : ℂ, H < |ρ.im| → ‖K ρ‖ ≤ B / ρ.im ^ 2) :
    ‖∑' ρ : ℂ,
          if H < |ρ.im| then (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) * K ρ
          else 0‖ ≤
      B * (Real.log ((q : ℝ) * H) / H) := by
  let D : ℂ → ℝ := fun ρ ↦ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ)
  let T : ℂ → ℝ := fun ρ ↦ if H < |ρ.im| then D ρ / ρ.im ^ 2 else 0
  let W : ℂ → ℂ := fun ρ ↦
    if H < |ρ.im| then (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) * K ρ else 0
  have ha : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hd (ρ : ℂ) : 0 ≤ D ρ := by
    dsimp only [D]
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ
  have hcmp (ρ : ℂ) : ‖W ρ‖ ≤ B * T ρ := by
    dsimp only [W, T]
    split_ifs with hρ
    · rw [norm_mul, ← Complex.ofReal_intCast, Complex.norm_of_nonneg (hd ρ)]
      have hk := mul_le_mul_of_nonneg_left (hK ρ hρ) (hd ρ)
      simpa only [D, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hk
    · simp only [norm_zero, mul_zero, le_refl]
  have ht : Summable T := summable_completed_invSq_tail hq hRH hp hne hH
  have hb : Summable (fun ρ ↦ B * T ρ) := ht.mul_left B
  have hw : Summable W := Summable.of_norm_bounded hb hcmp
  have hh := (norm_tsum_le_tsum_norm hw.norm).trans (Summable.tsum_le_tsum hcmp hw.norm hb)
  rw [tsum_mul_left] at hh
  have htbound := completed_zero_invSq_tail_lt hq hRH hp hne hH
  change (∑' ρ : ℂ, T ρ) < _ at htbound
  exact hh.trans (mul_le_mul_of_nonneg_left htbound.le hB)

/-- For a finite family of primitive nonprincipal characters, individual GRH and a
`B i / ρ.im²` bound for each kernel give the sum of the explicit one-character tail
budgets. The moduli and kernels may vary with the index. Apply the finite triangle
inequality and the one-character inverse-square tail estimate term by term.
This is the finite-family interface for joint zero-sum truncation. -/
theorem norm_joint_completed_zero_tail_le {ι : Type*} (S : Finset ι) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (χ : ∀ i, DirichletCharacter ℂ (q i)) (hq : ∀ i ∈ S, 2 ≤ q i)
    (hRH : ∀ i, GRH.DirichletRiemannHypothesis (χ i)) (hp : ∀ i, (χ i).IsPrimitive)
    (hne : ∀ i, χ i ≠ 1) {H : ℝ} (hH : 2 ≤ H) (B : ι → ℝ) (hB : ∀ i ∈ S, 0 ≤ B i) (u : ι → ℝ)
    (K : ι → ℂ → ℂ) (hK : ∀ i ∈ S, ∀ ρ : ℂ, H < |ρ.im| → ‖K i ρ‖ ≤ B i / ρ.im ^ 2) :
    ‖∑ i ∈ S,
          (u i : ℂ) *
            (∑' ρ : ℂ,
              if H < |ρ.im| then
                (MeromorphicOn.divisor (χ i).completedLFunction Set.univ ρ : ℂ) * K i ρ
              else 0)‖ ≤
      ∑ i ∈ S, |u i| * (B i * (Real.log ((q i : ℝ) * H) / H)) := by
  apply (norm_sum_le S _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact
    mul_le_mul_of_nonneg_left
      (norm_completed_zero_tail_le (hq i hi) (hRH i) (hp i) (hne i) hH (hB i hi) (K i) (hK i hi))
      (abs_nonneg (u i))

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
