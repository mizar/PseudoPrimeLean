/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaSignedPrefixCharacterBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaConductorFreeBounds
public import PseudoPrime.PrimeTest.MillerRabin.SignSubgroupIndex

/-! # Exact signed Euler-prefix budgets for Miller-Rabin witnesses -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For h ≥ 2 and T ≤ P, the aggregate comparison hT ≤ P+(h-1)U
implies 2T ≤ P+U. The actual principal and ramp quantities may be retained,
without replacing them by main terms and variation errors.
This scalar lemma reduces an arbitrary proper-subgroup index to two. -/
theorem gamma_index_two_exact_principal {h T P U : ℝ} (hh : 2 ≤ h) (hTP : T ≤ P)
    (hb : h * T ≤ P + (h - 1) * U) : 2 * T ≤ P + U := by
  have hp := mul_nonneg (sub_nonneg.mpr hh) (sub_nonneg.mpr hTP)
  by_contra hn
  have hg := mul_pos (show 0 < h - 1 by linarith only [hh]) (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith only [hp, hg, hb, hh]

/-- For an index at least four, the aggregate comparison `hT ≤ P + (h-1)U`
and the principal cap `T ≤ P` imply `4T ≤ P + 3U`. If `T ≤ U`, combine
the two caps directly. Otherwise multiply `h-4 ≥ 0` by `T-U > 0` and retain
the full index-four saving. This is the scalar input for the sharper Gamma
branch on all moduli whose passing subgroup has index at least four. -/
theorem gamma_index_four_exact_principal {h T P U : ℝ} (hh : 4 ≤ h) (hTP : T ≤ P)
    (hb : h * T ≤ P + (h - 1) * U) : 4 * T ≤ P + 3 * U := by
  by_cases hTU : T ≤ U
  · nlinarith only [hTP, hTU]
  · have hgap : 0 ≤ (h - 4) * (T - U) :=
      mul_nonneg (sub_nonneg.mpr hh) (sub_nonneg.mpr (le_of_lt (lt_of_not_ge hTU)))
    nlinarith only [hh, hTP, hb, hgap]

/-- At every positive scale, the normalized finite ramp sum is at most
the actual full level-one Gamma sum. Compare with the finite exponential
sum, then use nonnegative summands and absolute convergence.
No RH or large-scale hypothesis is required. -/
theorem gamma_ramp_le_full_principal {x : ℝ} (hx : 0 < x) :
    AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x ≤
      (∑' k : ℕ, gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re := by
  have hs := MellinKernel.summable_summand gammaMellinKernel (1 : DirichletCharacter ℂ 1) hx
  have ht :=
    (Complex.reCLM.summable hs).sum_le_tsum (Finset.Ioc 0 ⌊(99 / 40 : ℝ) * x⌋₊)
      (fun k _ ↦ MellinKernel.principal_summand_re_nonneg gammaMellinKernel hx k)
  have he := (Complex.reCLM.map_tsum hs).symm
  exact (gamma_ramp_le_finite_exponential hx).trans (ht.trans_eq he)

/-- Any annihilator character takes value one at a natural residue in H.
Unpack its unit representative and the annihilator membership criterion.
No primality or analytic hypothesis is required; this transfers a no-witness
subgroup condition to the common Euler-prefix character bound. -/
theorem annihilator_apply_one_of_residue_mem {q k : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (χ : NumberTheory.subgroupAnnihilator H) (hk : residueInSubgroup q H k) : χ.val k = 1 := by
  obtain ⟨u, hu, he⟩ := hk
  rw [← he]
  exact (NumberTheory.mem_subgroupAnnihilator_iff H χ.val).mp χ.property u hu

/-- With Q ≥ max(20000,q), GRH, x ≥ 2 and b ≥ 0, if all primes through b
belong to H, its primitive aggregate is bounded by the exact principal sum
plus the signed prefix budget and contour costs for every nonidentity character.
Use the common nonnegative Euler weight and retain twice the full finite prefix.
No logarithmic entrance or numerical Gamma-parity cap is assumed. -/
theorem gamma_primitive_average_re_le_signed_prime_prefix {q Q : ℕ} [NeZero q] (hQ : 20000 ≤ Q)
    (hqQ : q ≤ Q) (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 0 ≤ b) (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → residueInSubgroup q H p) :
    (∑ χ : NumberTheory.subgroupAnnihilator H,
        (∑' k : ℕ, gammaMellinKernel.summand χ.val.primitiveCharacter x k).re) ≤
      (∑' k : ℕ, gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re +
        ((H.index : ℝ) - 1) *
          (gammaSignedPrefixBudget q b + ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x +
            43 * x ^ (-9 / 16 : ℝ)) := by
  let F := fun χ : NumberTheory.subgroupAnnihilator H ↦
    (∑' k : ℕ, gammaMellinKernel.summand χ.val.primitiveCharacter x k).re
  have h1 : F 1 ≤ (∑' k : ℕ, gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re := by
    dsimp only [F]
    rw [Subgroup.coe_one,
      tsum_congr
        (MellinKernel.principal_primitive_summand_eq_level_one gammaMellinKernel (q := q) x)]
  have hrest :
    ∀ χ : NumberTheory.subgroupAnnihilator H,
      χ ≠ 1 →
        F χ ≤
          gammaSignedPrefixBudget q b + ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x +
            43 * x ^ (-9 / 16 : ℝ) := by
    intro χ hχ
    exact
      gamma_primitiveCharacter_sum_re_le_signed_prime_prefix_ambient hQ hqQ χ.val
        (fun he ↦ hχ (Subtype.ext he)) hGRH hx hb
        (fun p hp hpb ↦ annihilator_apply_one_of_residue_mem H χ (hsmall p hp hpb))
  have h := sum_le_distinguished_and_common (1 : NumberTheory.subgroupAnnihilator H) F h1 hrest
  rw [NumberTheory.card_subgroupAnnihilator] at h
  exact h

/-- If all annihilator characters are even, the primitive average uses the
exact even Gamma cost rather than the parity maximum. The original and
ambient pole levels remain independent. Apply the even prime-prefix character
bound and the same generic finite sum, retaining the exact principal sum. -/
theorem gamma_primitive_average_re_le_even_prime_prefix {q Q : ℕ} [NeZero q] (hQ : 20000 ≤ Q)
    (hqQ : q ≤ Q) (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (heven : ∀ χ : NumberTheory.subgroupAnnihilator H, χ.val.Even) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 0 ≤ b) (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → residueInSubgroup q H p) :
    (∑ χ : NumberTheory.subgroupAnnihilator H,
        (∑' k : ℕ, gammaMellinKernel.summand χ.val.primitiveCharacter x k).re) ≤
      (∑' k : ℕ, gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re +
        ((H.index : ℝ) - 1) *
          ((11783423 / 25000000 : ℝ) * Real.log q + gammaSignedGammaCost Complex.Gammaℝ +
                (∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
              2 * (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k) +
            ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x +
            43 * x ^ (-9 / 16 : ℝ)) := by
  let F := fun χ : NumberTheory.subgroupAnnihilator H ↦
    (∑' k : ℕ, gammaMellinKernel.summand χ.val.primitiveCharacter x k).re
  have h1 : F 1 ≤ (∑' k : ℕ, gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re := by
    dsimp only [F]
    rw [Subgroup.coe_one,
      tsum_congr
        (MellinKernel.principal_primitive_summand_eq_level_one gammaMellinKernel (q := q) x)]
  have hrest :
    ∀ χ : NumberTheory.subgroupAnnihilator H,
      χ ≠ 1 →
        F χ ≤
          (11783423 / 25000000 : ℝ) * Real.log q + gammaSignedGammaCost Complex.Gammaℝ +
                (∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
              2 * (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k) +
            ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x +
            43 * x ^ (-9 / 16 : ℝ) := by
    intro χ hχ
    exact
      gamma_primitiveCharacter_sum_re_le_even_signed_prime_prefix hQ hqQ χ.val
        (fun he ↦ hχ (Subtype.ext he)) (heven χ) hGRH hx hb
        (fun p hp hpb ↦ annihilator_apply_one_of_residue_mem H χ (hsmall p hp hpb))
  have h := sum_le_distinguished_and_common (1 : NumberTheory.subgroupAnnihilator H) F h1 hrest
  rw [NumberTheory.card_subgroupAnnihilator] at h
  exact h

end PseudoPrime.LLS.PaperStatements
