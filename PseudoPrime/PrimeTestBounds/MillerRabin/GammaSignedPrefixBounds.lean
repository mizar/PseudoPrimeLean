/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaSignedPrefixCharacterBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaConductorFreeBounds
public import PseudoPrime.PrimeTest.MillerRabin.SignSubgroupIndex
public import PseudoPrime.LLS.PaperStatements.GammaSignedPrefixBounds

/-! # Exact signed Euler-prefix budgets for Miller-Rabin witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Every annihilator character of a subgroup containing all strong passes
is even for odd n>1. Minus one passes the canonical test at the initial
minus-one branch; its unit representative lies in H. The annihilator is one
there, forcing even parity. This removes the odd Gamma branch from the MR budget. -/
theorem annihilator_even_of_containing_strong_passes {n : ℕ} [NeZero n] (hn : 1 < n) (hnOdd : Odd n)
    (H : Subgroup (ZMod n)ˣ)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (χ : NumberTheory.subgroupAnnihilator H) : χ.val.Even := by
  have hd := PrimeTest.odd_sub_canonical_decomp hn hnOdd
  have hneg : PrimeTest.StrongMillerRabinPass n (-1 : ZMod n) := by
    apply Or.inr
    refine ⟨0, hd.1, ?_⟩
    simpa only [pow_zero, one_mul] using
      (hd.2.1.neg_one_pow : (-1 : ZMod n) ^ Nat.divMaxPow (n - 1) 2 = -1)
  obtain ⟨u, hu, he⟩ := hHpass (-1) hneg
  change χ.val (-1) = 1
  rw [← he]
  exact (NumberTheory.mem_subgroupAnnihilator_iff H χ.val).mp χ.property u hu

/-- Actual signed-prefix upper budget at input level n, independent ambient
pole level Q, real scale x and prefix endpoint b. The exact even Gamma cost,
full Euler mass and twice the prefix are retained, with the pole and left costs.
The following theorem states the hypotheses needed to use this numerical quantity. -/
noncomputable def gammaSignedPrefixMRBudget (n Q : ℕ) (x b : ℝ) : ℝ :=
  (11783423 / 25000000 : ℝ) * Real.log n + LLS.PaperStatements.gammaSignedGammaCost Complex.Gammaℝ +
        (∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
      2 * (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k) +
    ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x +
    43 * x ^ (-9 / 16 : ℝ)

/-- For odd composite n>1 under GRH, Q ≥ max(20000,n), x ≥ 2 and
0 ≤ b ≤ 99x/40, a strict gap between the signed-prefix budget and the
actual ramp-minus-principal quantity gives a prime strong-test rejecting base
through 99x/40. The no-witness hypothesis makes every prefix character value
one and eliminates finite nonunit loss. Only the explicit scalar gap remains. -/
theorem exists_prime_witness_of_signed_prefix_gap {n Q : ℕ} (hn : 1 < n) (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hQ : 20000 ≤ Q) (hnQ : n ≤ Q) {x b : ℝ} (hx : 2 ≤ x) (hb : 0 ≤ b) (hbX : b ≤ (99 / 40 : ℝ) * x)
    (hgap :
      gammaSignedPrefixMRBudget n Q x b <
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨hnOdd.pos.ne'⟩
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx
  by_contra hnone
  have hpass :
    ∀ p : ℕ,
      p.Prime → (p : ℝ) ≤ (99 / 40 : ℝ) * x → PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
    intro p hp hb
    by_contra hf
    exact hnone ⟨p, hp, hb, hf⟩
  obtain ⟨H, hH, hHpass⟩ :=
    PrimeTest.exists_proper_subgroup_containing_strongMillerRabinPass hn hnOdd hnComposite
  have hsmall :
    ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (99 / 40 : ℝ) * x → LLS.PaperStatements.residueInSubgroup n H p :=
    fun p hp hpb ↦ hHpass (p : ZMod n) (hpass p hp hpb)
  have hu :=
    LLS.PaperStatements.gamma_primitive_average_re_le_even_prime_prefix hQ hnQ H hGRH
      (annihilator_even_of_containing_strong_passes hn hnOdd H hHpass) hx hb
      (fun p hp hpb ↦ hsmall p hp (hpb.trans hbX))
  have hr :=
    LLS.PaperStatements.gamma_ramp_subgroup_comparison H hx0 (fun p hp _ hpb ↦ hsmall p hp hpb)
  have hz := commonFactorExponentialSum_eq_zero_of_prime_passes hn hnOdd hpass x
  rw [hz, zero_div, mul_zero, add_zero] at hr
  have hi : (2 : ℝ) ≤ H.index := by exact_mod_cast Subgroup.one_lt_index_of_ne_top hH
  have hc :=
    LLS.PaperStatements.gamma_index_two_exact_principal hi
      (LLS.PaperStatements.gamma_ramp_le_full_principal hx0) (hr.trans hu)
  dsimp only [gammaSignedPrefixMRBudget] at hgap
  linarith only [hc, hgap]

/-- For an odd modulus at least 20000, retain a supplied passing subgroup of
index at least four. If the signed-prefix budget is below one third of the
index-four ramp-minus-principal margin, some prime through `99x/40` rejects
the strong test. The subgroup is supplied so the analytic consumer can be
reused for the index-four classification of odd composites. -/
theorem exists_prime_witness_of_signed_prefix_gap_index_four {n : ℕ} [NeZero n] (hn : 1 < n)
    (hnOdd : Odd n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hQ : 20000 ≤ n)
    (H : Subgroup (ZMod n)ˣ) (hi : 4 ≤ H.index)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    {x b : ℝ} (hx : 2 ≤ x) (hb : 0 ≤ b) (hbX : b ≤ (99 / 40 : ℝ) * x)
    (hgap :
      gammaSignedPrefixMRBudget n n x b <
        (4 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
            (∑' k : ℕ,
                LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x
                  k).re) /
          3) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_contra hnone
  have hpass :
    ∀ p : ℕ,
      p.Prime → (p : ℝ) ≤ (99 / 40 : ℝ) * x → PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
    intro p hp hbound
    by_contra hfail
    exact hnone ⟨p, hp, hbound, hfail⟩
  have hsmall :
    ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (99 / 40 : ℝ) * x → LLS.PaperStatements.residueInSubgroup n H p :=
    fun p hp hpb ↦ hHpass (p : ZMod n) (hpass p hp hpb)
  have hu :=
    LLS.PaperStatements.gamma_primitive_average_re_le_even_prime_prefix hQ le_rfl H hGRH
      (fun χ ↦ annihilator_even_of_containing_strong_passes hn hnOdd H hHpass χ) hx hb
      (fun p hp hpb ↦ hsmall p hp (hpb.trans hbX))
  have hx0 : 0 < x := by linarith only [hx]
  have hr :=
    LLS.PaperStatements.gamma_ramp_subgroup_comparison H hx0 (fun p hp _ hpb ↦ hsmall p hp hpb)
  have hz := commonFactorExponentialSum_eq_zero_of_prime_passes hn hnOdd hpass x
  rw [hz, zero_div, mul_zero, add_zero] at hr
  have hidx : (4 : ℝ) ≤ H.index := by exact_mod_cast hi
  have hc :=
    LLS.PaperStatements.gamma_index_four_exact_principal hidx
      (LLS.PaperStatements.gamma_ramp_le_full_principal hx0) (hr.trans hu)
  dsimp only [gammaSignedPrefixMRBudget] at hgap
  nlinarith only [hc, hgap]

/-- For odd composite n other than 9, the arithmetic classification supplies a
pass-containing subgroup of index at least four. A signed-prefix gap below one
third of the index-four ramp margin then yields a prime rejecting base through
`99x/40`, with no subgroup-index hypothesis in the resulting interface. -/
theorem exists_prime_witness_of_signed_prefix_gap_all_inputs {n : ℕ} [NeZero n] (hn : 1 < n)
    (hnOdd : Odd n) (hnComposite : ¬n.Prime) (hn9 : n ≠ 9)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hQ : 20000 ≤ n) {x b : ℝ}
    (hx : 2 ≤ x) (hb : 0 ≤ b) (hbX : b ≤ (99 / 40 : ℝ) * x)
    (hgap :
      gammaSignedPrefixMRBudget n n x b <
        (4 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
            (∑' k : ℕ,
                LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x
                  k).re) /
          3) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨H, hi, hHpass⟩ :=
    PrimeTest.exists_index_ge_four_subgroup_containing_strongMillerRabinPass hn hnOdd hnComposite
      hn9
  exact
    exists_prime_witness_of_signed_prefix_gap_index_four hn hnOdd hGRH hQ H hi hHpass hx hb hbX hgap

/-- For odd composite n>1, any common upper bound U for all nonprincipal
primitive Gamma sums at positive x yields a prime MR witness through 99x/40
when U is strictly below the actual ramp-minus-principal quantity.
The proof is purely arithmetic once the upper bound is supplied: average over
a pass-containing subgroup and eliminate finite nonunit loss.
This allows new analytic estimates without rebuilding the MR reduction. -/
theorem exists_prime_witness_of_common_primitive_upper {n : ℕ} (hn : 1 < n) (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) {x U : ℝ} (hx : 0 < x)
    (hU :
      ∀ χ : DirichletCharacter ℂ n,
        χ ≠ 1 →
          (∑' k : ℕ, LLS.PaperStatements.gammaMellinKernel.summand χ.primitiveCharacter x k).re ≤ U)
    (hgap :
      U <
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨hnOdd.pos.ne'⟩
  by_contra hnone
  have hpass :
    ∀ p : ℕ,
      p.Prime → (p : ℝ) ≤ (99 / 40 : ℝ) * x → PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
    intro p hp hb
    by_contra hf
    exact hnone ⟨p, hp, hb, hf⟩
  obtain ⟨H, hH, hHpass⟩ :=
    PrimeTest.exists_proper_subgroup_containing_strongMillerRabinPass hn hnOdd hnComposite
  let F := fun χ : NumberTheory.subgroupAnnihilator H ↦
    (∑' k : ℕ, LLS.PaperStatements.gammaMellinKernel.summand χ.val.primitiveCharacter x k).re
  have h1 :
    F 1 ≤
      (∑' k : ℕ,
          LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re := by
    dsimp only [F]
    rw [Subgroup.coe_one,
      tsum_congr
        (LLS.PaperStatements.MellinKernel.principal_primitive_summand_eq_level_one
          LLS.PaperStatements.gammaMellinKernel (q := n) x)]
  have hu :=
    LLS.PaperStatements.sum_le_distinguished_and_common (1 : NumberTheory.subgroupAnnihilator H) F
      h1 (fun χ hχ ↦ hU χ.val (fun he ↦ hχ (Subtype.ext he)))
  rw [NumberTheory.card_subgroupAnnihilator] at hu
  have hr :=
    LLS.PaperStatements.gamma_ramp_subgroup_comparison H hx
      (fun p hp _ hpb ↦ hHpass (p : ZMod n) (hpass p hp hpb))
  have hz := commonFactorExponentialSum_eq_zero_of_prime_passes hn hnOdd hpass x
  rw [hz, zero_div, mul_zero, add_zero] at hr
  have hi : (2 : ℝ) ≤ H.index := by exact_mod_cast Subgroup.one_lt_index_of_ne_top hH
  have hc :=
    LLS.PaperStatements.gamma_index_two_exact_principal hi
      (LLS.PaperStatements.gamma_ramp_le_full_principal hx) (hr.trans hu)
  linarith only [hc, hgap]

end PseudoPrime.PrimeTestBounds.MillerRabin
