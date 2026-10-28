/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaReflectedResolventComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaSignedPrefixBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaSeedPairedBounds

/-! # Reflected signed-prefix MR budgets and all-input gap consumers -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The signed even-prefix MR budget with reflected tail. Inputs are the
original level n, ambient pole level Q, Mellin scale x and real prefix endpoint b.
Keep the actual even Gamma cost, total Euler mass and twice the prefix; replace
only the contour tail by (35/2)x^(-9/16)+1/(x sqrt x). -/
noncomputable def gammaReflectedMRBudget (n Q : ℕ) (x b : ℝ) : ℝ :=
  (11783423 / 25000000 : ℝ) * Real.log n + LLS.PaperStatements.gammaSignedGammaCost Complex.Gammaℝ +
        (∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
      2 * (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k) +
    ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x +
    (35 / 2 : ℝ) * x ^ (-9 / 16 : ℝ) +
    1 / (x * Real.sqrt x)

/-- Under GRH for an odd n>=20000, a supplied pass-containing subgroup of
index at least four and a strict reflected-budget gap yield an actual rejecting
prime through 99x/40. Retain the exact principal sum and index-four averaging;
no transfer through the older, larger contour budget is used. -/
theorem exists_prime_reflected_gap_four {n : ℕ} [NeZero n] (hn : 1 < n) (hnOdd : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hQ : 20000 ≤ n)
    (H : Subgroup (ZMod n)ˣ) (hi : 4 ≤ H.index)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    {x b : ℝ} (hx : 2 ≤ x) (hb : 0 ≤ b) (hbX : b ≤ (99 / 40 : ℝ) * x)
    (hgap :
      gammaReflectedMRBudget n n x b <
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
    LLS.PaperStatements.gamma_even_reflected_average hQ le_rfl H hGRH
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
  dsimp only [gammaReflectedMRBudget] at hgap
  nlinarith only [hc, hgap]

/-- Under GRH for an odd composite n>=20000, a strict reflected signed-prefix
gap below the index-four margin yields an actual rejecting prime through 99x/40.
Use the existing pass-containing subgroup classification and expose no index
restriction in the resulting all-input interface. -/
theorem exists_prime_reflected_gap_all {n : ℕ} [NeZero n] (hn : 1 < n) (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hn9 : n ≠ 9)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hQ : 20000 ≤ n) {x b : ℝ}
    (hx : 2 ≤ x) (hb : 0 ≤ b) (hbX : b ≤ (99 / 40 : ℝ) * x)
    (hgap :
      gammaReflectedMRBudget n n x b <
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
  exact exists_prime_reflected_gap_four hn hnOdd hGRH hQ H hi hHpass hx hb hbX hgap

/-- Under RH, the reflected MR budget is strictly below the precise common
cost with allowance 541/50, retaining the entire finite prefix and new tail.
The strict common-cost estimate supplies strictness even at a scalar gap root. -/
theorem gammaReflectedBudget_lt_common (hRH : RiemannHypothesis) (n Q : ℕ) (x b : ℝ) :
    gammaReflectedMRBudget n Q x b <
      (11783423 / 25000000 : ℝ) * Real.log n + 541 / 50 -
          2 * (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x +
        (35 / 2 : ℝ) * x ^ (-9 / 16 : ℝ) +
        1 / (x * Real.sqrt x) := by
  have h :=
    LLS.gamma_even_common_cost_lt_precise hRH
      AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even
  have hf : (1 : DirichletCharacter ℂ 1).gammaFactor = Complex.Gammaℝ :=
    funext AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even.gammaFactor_def
  rw [hf] at h
  dsimp only [gammaReflectedMRBudget]
  linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
