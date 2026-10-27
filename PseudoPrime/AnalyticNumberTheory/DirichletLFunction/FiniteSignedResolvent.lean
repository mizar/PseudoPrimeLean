/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SignedResolventEulerBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaSignedEulerIdentity

/-! # Exact signed finite-resolvent zero mass and Euler prefix -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Input: primitive nonprincipal character, individual RH and positive rational nodes.
Claim: every signed node's zero series is summable.
Proof: scale the established Poisson summability theorem.
Role: interchange the finite node list with the zero sum. -/
theorem summable_finiteSignedResolvent_nodes {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (l : List (ℚ × ℚ)) (ha : ∀ ab ∈ l, (0 : ℚ) < ab.1) :
    ∀ ab ∈ l,
      Summable
        (fun ρ : ℂ ↦
          (ab.2 : ℝ) *
            ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
              ((ab.1 : ℝ) / ((ab.1 : ℝ) ^ 2 + ρ.im ^ 2)))) := by
  intro ab hab
  exact
    (summable_completed_resolvent_terms hq hRH hp hne hinv (by exact_mod_cast ha ab hab)).mul_left
      (ab.2 : ℝ)

/-- Input: primitive nonprincipal character, RH and positive nodes.
Claim: the combined signed resolvent zero series is summable.
Proof: sum the finitely many summable nodes. Role: compare one-sided spectral majorants. -/
theorem summable_finiteSignedResolvent_terms {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (l : List (ℚ × ℚ)) (ha : ∀ ab ∈ l, (0 : ℚ) < ab.1) :
    Summable
      (fun ρ : ℂ ↦
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.finiteSignedResolvent l ρ.im) := by
  exact
    (Analysis.summable_list_sum l _
          (summable_finiteSignedResolvent_nodes hq hRH hp hne hinv l ha)).congr
      (fun ρ ↦
        (Analysis.mul_finiteSignedResolvent l
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) ρ.im).symm)

/-- Input: primitive nonprincipal character, RH and nodes exceeding one half.
Claim: the zero mass equals the signed real logarithmic-derivative expression.
Proof: interchange the finite list and apply the exact Poisson identity at each node.
Role: preserve conductor and archimedean terms before bounding. -/
theorem finiteSignedResolvent_zeroMass_eq_nodes {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (l : List (ℚ × ℚ)) (ha : ∀ ab ∈ l, (1 / 2 : ℚ) < ab.1) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.finiteSignedResolvent l ρ.im) =
      (l.map
          (fun ab ↦
            (ab.2 : ℝ) *
              (Real.log q / 2 + (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re +
                (logDeriv χ.LFunction (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re))).sum := by
  have ha0 : ∀ ab ∈ l, (0 : ℚ) < ab.1 := fun ab hab ↦
    lt_trans (by norm_num only : (0 : ℚ) < 1 / 2) (ha ab hab)
  have hs := summable_finiteSignedResolvent_nodes hq hRH hp hne hinv l ha0
  rw [tsum_congr
      (fun ρ ↦
        Analysis.mul_finiteSignedResolvent l
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) ρ.im),
    Analysis.tsum_list_sum l _ hs]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab hab
  rw [tsum_mul_left]
  apply congrArg (fun y : ℝ ↦ (ab.2 : ℝ) * y)
  rw [tsum_congr (fun ρ ↦ completed_resolventTerm_eq_poisson hRH hp hne hinv (ab.1 : ℝ) ρ)]
  have hσ : 1 < (1 / 2 : ℝ) + (ab.1 : ℝ) := by
    have h : ((1 / 2 : ℚ) : ℝ) < (ab.1 : ℝ) := Rat.cast_lt.mpr (ha ab hab)
    norm_num only at h
    linarith only [h]
  have hn : (1 / 2 : ℝ) + (ab.1 : ℝ) - 1 / 2 = ab.1 := by ring
  have he := completed_poissonSum_eq_signed_ordinary hq hRH hp hne hinv hσ
  rw [hn] at he
  simpa only [Complex.ofReal_add] using he

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Input: a character and rational nodes exceeding one half.
Claim: the ordinary logarithmic derivatives equal the signed common Mangoldt series.
Proof: use the real Euler identity and finite/infinite interchange.
Role: keep the common weight before using positivity. -/
theorem finiteSignedResolvent_ordinary_eq_euler {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (l : List (ℚ × ℚ)) (ha : ∀ ab ∈ l, (1 / 2 : ℚ) < ab.1) :
    (l.map (fun ab ↦ (ab.2 : ℝ) * (logDeriv χ.LFunction (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum =
      ∑' n : ℕ, -(χ n).re * Analysis.finiteSignedMangoldtWeight l n := by
  let f := fun (ab : ℚ × ℚ) (n : ℕ) ↦
    (ab.2 : ℝ) *
      (-((χ n).re * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ ((1 / 2 : ℝ) + (ab.1 : ℝ))))
  have hσ (ab : ℚ × ℚ) (hab : ab ∈ l) : 1 < (1 / 2 : ℝ) + (ab.1 : ℝ) := by
    have h : ((1 / 2 : ℚ) : ℝ) < (ab.1 : ℝ) := Rat.cast_lt.mpr (ha ab hab)
    norm_num only at h
    linarith only [h]
  have hs (ab : ℚ × ℚ) (hab : ab ∈ l) : Summable (f ab) :=
    ((summable_real_twistedMangoldt χ (hσ ab hab)).neg).mul_left (ab.2 : ℝ)
  have he (n : ℕ) :
    -(χ n).re * Analysis.finiteSignedMangoldtWeight l n = (l.map (fun ab ↦ f ab n)).sum := by
    dsimp only [f, Analysis.finiteSignedMangoldtWeight, Analysis.finiteSignedEulerWeight]
    rw [← mul_assoc, ← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro ab _
    rw [Real.rpow_neg (Nat.cast_nonneg n)]
    ring
  rw [tsum_congr he, Analysis.tsum_list_sum l f hs]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab hab
  dsimp only [f]
  rw [← Complex.ofReal_add, re_logDeriv_eq_signed_Mangoldt_tsum χ (hσ ab hab), tsum_mul_left,
    tsum_neg]

/-- Input: a primitive nonprincipal character under RH and nodes exceeding one half.
Claim: exact conductor, gamma-factor and Euler decomposition of the signed zero mass.
Proof: substitute the ordinary Euler identity in the node formula.
Role: supply the arithmetic side of phase-sensitive estimates. -/
theorem finiteSignedResolvent_zeroMass_eq_euler {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (l : List (ℚ × ℚ)) (ha : ∀ ab ∈ l, (1 / 2 : ℚ) < ab.1) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.finiteSignedResolvent l ρ.im) =
      (l.map (fun ab ↦ (ab.2 : ℝ))).sum * (Real.log q / 2) +
        (l.map
            (fun ab ↦
              (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
        ∑' n : ℕ, -(χ n).re * Analysis.finiteSignedMangoldtWeight l n := by
  rw [finiteSignedResolvent_zeroMass_eq_nodes hq hRH hp hne hinv l ha]
  simp only [mul_add, List.sum_map_add, List.sum_map_mul_right]
  rw [finiteSignedResolvent_ordinary_eq_euler χ l ha]

/-- Input: a primitive nonprincipal character under RH, admissible nodes and a finite prefix.
Claim: exact zero-mass decomposition retaining both prefix defect and paired tail.
Proof: apply the signed-weight identity to the Euler series.
Role: preserve the nonnegative prime-power savings. -/
theorem finiteSignedResolvent_zeroMass_eq_prefix_tail {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (l : List (ℚ × ℚ)) (ha : ∀ ab ∈ l, (1 / 2 : ℚ) < ab.1)
    (B : Finset ℕ) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.finiteSignedResolvent l ρ.im) =
      (l.map (fun ab ↦ (ab.2 : ℝ))).sum * (Real.log q / 2) +
              (l.map
                  (fun ab ↦
                    (ab.2 : ℝ) *
                      (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
              (∑' n : ℕ, Analysis.finiteSignedMangoldtWeight l n) -
            2 * (∑ n ∈ B, Analysis.finiteSignedMangoldtWeight l n) +
          (∑ n ∈ B, (1 - (χ n).re) * Analysis.finiteSignedMangoldtWeight l n) -
        Analysis.pairedWeightTail (Analysis.finiteSignedMangoldtWeight l) (fun n ↦ (χ n).re) B := by
  have hc (n : ℕ) : |(χ n).re| ≤ 1 := (Complex.abs_re_le_norm (χ n)).trans (χ.norm_le_one n)
  have he :=
    Analysis.signed_weight_eq_prefix_sub_paired_tail (Analysis.finiteSignedMangoldtWeight l)
      (fun n ↦ (χ n).re) (Analysis.summable_finiteSignedMangoldtWeight l ha) hc B
  rw [finiteSignedResolvent_zeroMass_eq_euler hq hRH hp hne hinv l ha, he]
  ring

/-- Input: the exact zero-mass hypotheses and nonnegative common Mangoldt weights.
Claim: the prefix budget bounds the zero mass above.
Proof: remove the nonnegative paired tail. Role: obtain a quantitative spectral upper bound. -/
theorem finiteSignedResolvent_zeroMass_le_prefix {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (l : List (ℚ × ℚ)) (ha : ∀ ab ∈ l, (1 / 2 : ℚ) < ab.1)
    (hW : ∀ n, 0 ≤ Analysis.finiteSignedMangoldtWeight l n) (B : Finset ℕ) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.finiteSignedResolvent l ρ.im) ≤
      (l.map (fun ab ↦ (ab.2 : ℝ))).sum * (Real.log q / 2) +
            (l.map
                (fun ab ↦
                  (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
            (∑' n : ℕ, Analysis.finiteSignedMangoldtWeight l n) -
          2 * (∑ n ∈ B, Analysis.finiteSignedMangoldtWeight l n) +
        ∑ n ∈ B, (1 - (χ n).re) * Analysis.finiteSignedMangoldtWeight l n := by
  rw [finiteSignedResolvent_zeroMass_eq_prefix_tail hq hRH hp hne hinv l ha B]
  have hn :=
    Analysis.pairedWeightTail_nonneg (Analysis.finiteSignedMangoldtWeight l) (fun n ↦ (χ n).re)
      (Analysis.summable_finiteSignedMangoldtWeight l ha) hW
      (fun n ↦ (Complex.abs_re_le_norm (χ n)).trans (χ.norm_le_one n)) B
  linarith only [hn]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Input: a character, rational node-coefficient pairs and a finite prime-power prefix.
Output: conductor and gamma-factor contributions plus Euler total minus twice the prefix
and its character defect. Role: package the exact one-sided spectral budget. -/
noncomputable def finiteSignedPrefixBudget {q : ℕ} (χ : DirichletCharacter ℂ q) (l : List (ℚ × ℚ))
    (B : Finset ℕ) : ℝ :=
  (l.map (fun ab ↦ (ab.2 : ℝ))).sum * (Real.log q / 2) +
        (l.map
            (fun ab ↦
              (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
        (∑' n : ℕ, Analysis.finiteSignedMangoldtWeight l n) -
      2 * (∑ n ∈ B, Analysis.finiteSignedMangoldtWeight l n) +
    ∑ n ∈ B, (1 - (χ n).re) * Analysis.finiteSignedMangoldtWeight l n

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
