/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RealAxisDifferenceWeights
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.RealPairedEuler

/-! # Retained paired Euler differences and signed rational-kernel zero mass -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For any complex character and ordered real exponents, each paired Euler term
decreases with the exponent. At index zero both terms vanish; otherwise compare
positive real powers and use the nonnegative paired Mangoldt coefficient.
No RH, primitivity or convergence assumption is needed for this pointwise bound. -/
theorem realPairedEulerTerm_antitone {q : ℕ} (χ : DirichletCharacter ℂ q) {σ τ : ℝ} (hst : σ ≤ τ)
    (m : ℕ) : realPairedEulerTerm χ τ m ≤ realPairedEulerTerm χ σ m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp only [realPairedEulerTerm, ArithmeticFunction.map_zero, mul_zero, zero_div, le_refl]
  · have hm1 : 1 ≤ (m : ℝ) := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hm)
    have hc := (abs_le.mp ((Complex.abs_re_le_norm (χ m)).trans (χ.norm_le_one m))).1
    exact
      div_le_div_of_nonneg_left
        (mul_nonneg (by linarith only [hc]) ArithmeticFunction.vonMangoldt_nonneg)
        (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)) σ)
        (Real.rpow_le_rpow_of_exponent_le hm1 hst)

/-- For 1<sigma<=tau, any finite prefix of the paired Euler difference is at most
the difference of the convergent full sums. The difference terms are nonnegative.
This retains two real-axis evaluations together before estimating the tail. -/
theorem realPairedEuler_difference_prefix_le {q : ℕ} (χ : DirichletCharacter ℂ q) {σ τ : ℝ}
    (hs : 1 < σ) (hst : σ ≤ τ) (B : Finset ℕ) :
    (∑ m ∈ B, (realPairedEulerTerm χ σ m - realPairedEulerTerm χ τ m)) ≤
      (∑' m : ℕ, realPairedEulerTerm χ σ m) - ∑' m : ℕ, realPairedEulerTerm χ τ m := by
  have ht := summable_realPairedEulerTerm χ (hs.trans_le hst)
  have hsum :=
    ((summable_realPairedEulerTerm χ hs).sub ht).sum_le_tsum B
      (fun m _ ↦ sub_nonneg.mpr (realPairedEulerTerm_antitone χ hst m))
  rw [(summable_realPairedEulerTerm χ hs).tsum_sub ht] at hsum
  exact hsum

/-- For a nonzero level and 1<sigma<=tau, a finite paired Euler-difference prefix
bounds the difference of the paired principal and character logarithmic derivatives
below. Substitute the two exact absolutely convergent Euler identities.
This needs neither RH nor primitivity. -/
theorem real_logDeriv_pair_difference_prefix_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ τ : ℝ} (hs : 1 < σ) (hst : σ ≤ τ) (B : Finset ℕ) :
    (∑ m ∈ B, (realPairedEulerTerm χ σ m - realPairedEulerTerm χ τ m)) ≤
      (-(logDeriv (1 : DirichletCharacter ℂ 1).LFunction (σ : ℂ)).re -
          (logDeriv χ.LFunction (σ : ℂ)).re) -
        (-(logDeriv (1 : DirichletCharacter ℂ 1).LFunction (τ : ℂ)).re -
          (logDeriv χ.LFunction (τ : ℂ)).re) := by
  rw [neg_real_logDeriv_pair_eq_euler χ hs, neg_real_logDeriv_pair_eq_euler χ (hs.trans_le hst)]
  exact realPairedEuler_difference_prefix_le χ hs hst B

/-- For every character, natural index and real endpoint pair, the logarithm-weighted
right-endpoint term times the exponent gap is at most the paired term difference.
Multiply the scalar secant inequality by the nonnegative Mangoldt coefficient.
The zero index vanishes. No differentiation of an infinite sum is invoked. -/
theorem realPairedEulerTerm_log_weight_le_difference {q : ℕ} (χ : DirichletCharacter ℂ q) (σ τ : ℝ)
    (m : ℕ) :
    (τ - σ) * Real.log m * realPairedEulerTerm χ τ m ≤
      realPairedEulerTerm χ σ m - realPairedEulerTerm χ τ m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp only [realPairedEulerTerm, ArithmeticFunction.map_zero, mul_zero, zero_div, mul_zero,
      sub_zero, le_refl]
  · have hc := (abs_le.mp ((Complex.abs_re_le_norm (χ m)).trans (χ.norm_le_one m))).1
    have hA : 0 ≤ (1 + (χ m).re) * ArithmeticFunction.vonMangoldt m :=
      mul_nonneg (by linarith only [hc]) ArithmeticFunction.vonMangoldt_nonneg
    have h :=
      mul_le_mul_of_nonneg_left
        (Analysis.log_weight_le_rpow_difference (σ := σ) (τ := τ)
          (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)))
        hA
    dsimp only [realPairedEulerTerm]
    convert h using 1 <;> ring

/-- For 1<sigma<=tau, the exponent gap times any finite log-weighted right prefix
is at most the difference of the full paired Euler sums. Sum the pointwise secant
lower bound and discard only nonnegative difference terms in the complementary
support. This supplies a stable positive gain for nearby real-axis nodes. -/
theorem realPairedEuler_log_prefix_le_difference {q : ℕ} (χ : DirichletCharacter ℂ q) {σ τ : ℝ}
    (hs : 1 < σ) (hst : σ ≤ τ) (B : Finset ℕ) :
    (τ - σ) * (∑ m ∈ B, Real.log m * realPairedEulerTerm χ τ m) ≤
      (∑' m : ℕ, realPairedEulerTerm χ σ m) - ∑' m : ℕ, realPairedEulerTerm χ τ m := by
  have h :=
    Finset.sum_le_sum (fun m (_ : m ∈ B) ↦ realPairedEulerTerm_log_weight_le_difference χ σ τ m)
  rw [Finset.mul_sum]
  simp only [mul_assoc] at h
  exact h.trans (realPairedEuler_difference_prefix_le χ hs hst B)

/-- For a nonzero level and 1<sigma<=tau, the character logarithmic-derivative
difference is bounded above by the opposite principal difference minus the finite
paired Euler-difference gain. Rearrange the paired identity without separate norm
bounds. This is the arithmetic input to the completed zero-mass comparison. -/
theorem real_logDeriv_difference_le_paired_prefix {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ τ : ℝ} (hs : 1 < σ) (hst : σ ≤ τ) (B : Finset ℕ) :
    (logDeriv χ.LFunction (σ : ℂ)).re - (logDeriv χ.LFunction (τ : ℂ)).re ≤
      (logDeriv (1 : DirichletCharacter ℂ 1).LFunction (τ : ℂ)).re -
        (logDeriv (1 : DirichletCharacter ℂ 1).LFunction (σ : ℂ)).re -
        ∑ m ∈ B, (realPairedEulerTerm χ σ m - realPairedEulerTerm χ τ m) := by
  have h := real_logDeriv_pair_difference_prefix_le χ hs hst B
  linarith only [h]

/-- For primitive nonprincipal individual-RH data and 1<sigma<=tau, the difference
of the two actual Poisson zero masses is at most the Gamma difference plus the
opposite principal derivative difference minus the finite paired Euler gain.
Use the exact signed Poisson identities; the conductor contributions cancel. -/
theorem completed_poissonSum_difference_le_paired_prefix {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {σ τ : ℝ} (hs : 1 < σ) (hst : σ ≤ τ) (B : Finset ℕ) :
    (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ((σ - 1 / 2) / Complex.normSq ((σ : ℂ) - ρ))) -
        (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ((τ - 1 / 2) / Complex.normSq ((τ : ℂ) - ρ))) ≤
      (logDeriv χ.gammaFactor (σ : ℂ)).re - (logDeriv χ.gammaFactor (τ : ℂ)).re +
          (logDeriv (1 : DirichletCharacter ℂ 1).LFunction (τ : ℂ)).re -
        (logDeriv (1 : DirichletCharacter ℂ 1).LFunction (σ : ℂ)).re -
        ∑ m ∈ B, (realPairedEulerTerm χ σ m - realPairedEulerTerm χ τ m) := by
  rw [completed_poissonSum_eq_signed_ordinary hq hRH hp hne hinv hs,
    completed_poissonSum_eq_signed_ordinary hq hRH hp hne hinv (hs.trans_le hst)]
  have h := real_logDeriv_difference_le_paired_prefix χ hs hst B
  linarith only [h]

/-- For the same primitive individual-RH data, retain the exponent gap times a finite
log-weighted right-endpoint Euler prefix in the Poisson zero-mass difference.
Use the secant lower bound in the exact Euler and Poisson identities. This avoids
both derivative estimates at the series level and independent endpoint norms. -/
theorem completed_poissonSum_difference_le_paired_log_prefix {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {σ τ : ℝ} (hs : 1 < σ) (hst : σ ≤ τ) (B : Finset ℕ) :
    (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ((σ - 1 / 2) / Complex.normSq ((σ : ℂ) - ρ))) -
        (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ((τ - 1 / 2) / Complex.normSq ((τ : ℂ) - ρ))) ≤
      (logDeriv χ.gammaFactor (σ : ℂ)).re - (logDeriv χ.gammaFactor (τ : ℂ)).re +
          (logDeriv (1 : DirichletCharacter ℂ 1).LFunction (τ : ℂ)).re -
        (logDeriv (1 : DirichletCharacter ℂ 1).LFunction (σ : ℂ)).re -
        (τ - σ) * (∑ m ∈ B, Real.log m * realPairedEulerTerm χ τ m) := by
  have h := realPairedEuler_log_prefix_le_difference χ hs hst B
  rw [← neg_real_logDeriv_pair_eq_euler χ hs, ←
    neg_real_logDeriv_pair_eq_euler χ (hs.trans_le hst)] at h
  rw [completed_poissonSum_eq_signed_ordinary hq hRH hp hne hinv hs,
    completed_poissonSum_eq_signed_ordinary hq hRH hp hne hinv (hs.trans_le hst)]
  linarith only [h]

/-- For primitive nonprincipal individual-RH data, 1<sigma<=tau and 0<=v<=u,
bound u times the first Poisson mass minus v times the second. Decompose it into
(u-v) times the first mass and v times the mass difference, retaining independent
ordinary and log-weighted finite prefixes. This handles a negative node coefficient
without replacing it by its absolute value. -/
theorem completed_poissonSum_signed_pair_le_retained_prefixes {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {σ τ u v : ℝ} (hs : 1 < σ) (hst : σ ≤ τ) (hv : 0 ≤ v)
    (hvu : v ≤ u) (A B : Finset ℕ) :
    u *
          (∑' ρ : ℂ,
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
              ((σ - 1 / 2) / Complex.normSq ((σ : ℂ) - ρ))) -
        v *
          (∑' ρ : ℂ,
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
              ((τ - 1 / 2) / Complex.normSq ((τ : ℂ) - ρ))) ≤
      (u - v) *
          (Real.log q / 2 + (logDeriv χ.gammaFactor (σ : ℂ)).re -
            (logDeriv (1 : DirichletCharacter ℂ 1).LFunction (σ : ℂ)).re -
            ∑ m ∈ A, realPairedEulerTerm χ σ m) +
        v *
          ((logDeriv χ.gammaFactor (σ : ℂ)).re - (logDeriv χ.gammaFactor (τ : ℂ)).re +
              (logDeriv (1 : DirichletCharacter ℂ 1).LFunction (τ : ℂ)).re -
            (logDeriv (1 : DirichletCharacter ℂ 1).LFunction (σ : ℂ)).re -
            (τ - σ) * (∑ m ∈ B, Real.log m * realPairedEulerTerm χ τ m)) := by
  have hbase := realPairedEuler_prefix_le_logDeriv χ hs A
  have he := completed_poissonSum_eq_signed_ordinary hq hRH hp hne hinv hs
  have hb :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          ((σ - 1 / 2) / Complex.normSq ((σ : ℂ) - ρ))) ≤
      Real.log q / 2 + (logDeriv χ.gammaFactor (σ : ℂ)).re -
        (logDeriv (1 : DirichletCharacter ℂ 1).LFunction (σ : ℂ)).re -
        ∑ m ∈ A, realPairedEulerTerm χ σ m := by
    linarith only [hbase, he]
  have hd := completed_poissonSum_difference_le_paired_log_prefix hq hRH hp hne hinv hs hst B
  have h :=
    add_le_add (mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hvu)) (mul_le_mul_of_nonneg_left hd hv)
  convert h using 1
  ring

/-- For primitive nonprincipal individual-RH data and both nodes right of one half,
the actual zero-mass series for the signed two-profile weight equals the signed
combination of Poisson sums, for arbitrary real coefficients. Existing resolvent
summability justifies subtraction and scalar extraction; RH identifies ordinates
with the real-axis Poisson denominators. No unsigned-tail estimate is introduced. -/
theorem completed_poissonDifferenceWeight_tsum_eq {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {σ τ : ℝ} (hs : 1 / 2 < σ) (ht : 1 / 2 < τ) (u v : ℝ) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.poissonDifferenceWeight (σ - 1 / 2) (τ - 1 / 2) u v ρ.im) =
      u *
          (∑' ρ : ℂ,
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
              ((σ - 1 / 2) / Complex.normSq ((σ : ℂ) - ρ))) -
        v *
          (∑' ρ : ℂ,
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
              ((τ - 1 / 2) / Complex.normSq ((τ : ℂ) - ρ))) := by
  have hS := summable_completed_resolvent_terms hq hRH hp hne hinv (sub_pos.mpr hs)
  have hT := summable_completed_resolvent_terms hq hRH hp hne hinv (sub_pos.mpr ht)
  have he (r : ℝ) (ρ : ℂ) :
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        ((r - 1 / 2) / ((r - 1 / 2) ^ 2 + ρ.im ^ 2)) =
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        ((r - 1 / 2) / Complex.normSq ((r : ℂ) - ρ)) := by
    have h := completed_resolventTerm_eq_poisson hRH hp hne hinv (r - 1 / 2) ρ
    rw [← Complex.ofReal_add, show (1 / 2 : ℝ) + (r - 1 / 2) = r by ring] at h
    exact h
  calc
    _ =
        ∑' ρ : ℂ,
          (u *
              ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
                ((σ - 1 / 2) / ((σ - 1 / 2) ^ 2 + ρ.im ^ 2))) -
            v *
              ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
                ((τ - 1 / 2) / ((τ - 1 / 2) ^ 2 + ρ.im ^ 2)))) :=
      by
      apply tsum_congr
      intro ρ
      unfold Analysis.poissonDifferenceWeight
      ring
    _ = _ := by
      rw [(hS.mul_left u).tsum_sub (hT.mul_left v), tsum_mul_left, tsum_mul_left]
      rw [tsum_congr (he σ), tsum_congr (he τ)]

/-- For primitive nonprincipal individual-RH data, 1<sigma<=tau and 0<=v<=u,
the signed rational-kernel zero mass obeys the retained two-prefix upper bound.
First identify the convergent kernel series with the two Poisson sums, then apply
the coupled real-axis estimate. This is the kernel-level interface for choosing
certified scales and coefficients in later witness-bound comparisons. -/
theorem completed_poissonDifferenceWeight_mass_le_retained_prefixes {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {σ τ u v : ℝ} (hs : 1 < σ) (hst : σ ≤ τ) (hv : 0 ≤ v)
    (hvu : v ≤ u) (A B : Finset ℕ) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.poissonDifferenceWeight (σ - 1 / 2) (τ - 1 / 2) u v ρ.im) ≤
      (u - v) *
          (Real.log q / 2 + (logDeriv χ.gammaFactor (σ : ℂ)).re -
            (logDeriv (1 : DirichletCharacter ℂ 1).LFunction (σ : ℂ)).re -
            ∑ m ∈ A, realPairedEulerTerm χ σ m) +
        v *
          ((logDeriv χ.gammaFactor (σ : ℂ)).re - (logDeriv χ.gammaFactor (τ : ℂ)).re +
              (logDeriv (1 : DirichletCharacter ℂ 1).LFunction (τ : ℂ)).re -
            (logDeriv (1 : DirichletCharacter ℂ 1).LFunction (σ : ℂ)).re -
            (τ - σ) * (∑ m ∈ B, Real.log m * realPairedEulerTerm χ τ m)) := by
  have hs0 : 1 / 2 < σ := lt_trans (by norm_num only) hs
  rw [completed_poissonDifferenceWeight_tsum_eq hq hRH hp hne hinv hs0 (hs0.trans_le hst) u v]
  exact completed_poissonSum_signed_pair_le_retained_prefixes hq hRH hp hne hinv hs hst hv hvu A B

/-- For primitive nonprincipal individual-RH data and two nodes right of one half,
the divisor-weighted signed Poisson-difference kernel is summable for arbitrary
real coefficients. Combine the two known summable resolvent series and distribute
the weights. This supplies convergence for comparisons with new Mellin kernels. -/
theorem summable_completed_poissonDifferenceWeight {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {σ τ : ℝ} (hs : 1 / 2 < σ) (ht : 1 / 2 < τ) (u v : ℝ) :
    Summable
      (fun ρ : ℂ ↦
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.poissonDifferenceWeight (σ - 1 / 2) (τ - 1 / 2) u v ρ.im) := by
  have hS := summable_completed_resolvent_terms hq hRH hp hne hinv (sub_pos.mpr hs)
  have hT := summable_completed_resolvent_terms hq hRH hp hne hinv (sub_pos.mpr ht)
  apply ((hS.mul_left u).sub (hT.mul_left v)).congr
  intro ρ
  unfold Analysis.poissonDifferenceWeight
  ring

/-- For primitive individual-RH data, 1<sigma<=tau and 0<=v<=u, let a nonnegative
height kernel K be pointwise dominated by the signed Poisson-difference profile.
Then its actual divisor-weighted zero series is summable and bounded by the retained
ordinary and log-weighted Euler prefixes. Analyticity makes divisor multiplicities
nonnegative; transfer domination to the summable rational kernel before summing.
This isolates the remaining kernel-majorant and numerical parameter certificates. -/
theorem zeroMass_le_of_poissonDifferenceWeight_majorant {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {σ τ u v : ℝ} (hs : 1 < σ) (hst : σ ≤ τ) (hv : 0 ≤ v)
    (hvu : v ≤ u) (A B : Finset ℕ) (K : ℝ → ℝ) (hK : ∀ t, 0 ≤ K t)
    (hmajorant : ∀ t, K t ≤ Analysis.poissonDifferenceWeight (σ - 1 / 2) (τ - 1 / 2) u v t) :
    Summable (fun ρ : ℂ ↦ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * K ρ.im) ∧
      (∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * K ρ.im) ≤
        (u - v) *
            (Real.log q / 2 + (logDeriv χ.gammaFactor (σ : ℂ)).re -
              (logDeriv (1 : DirichletCharacter ℂ 1).LFunction (σ : ℂ)).re -
              ∑ m ∈ A, realPairedEulerTerm χ σ m) +
          v *
            ((logDeriv χ.gammaFactor (σ : ℂ)).re - (logDeriv χ.gammaFactor (τ : ℂ)).re +
                (logDeriv (1 : DirichletCharacter ℂ 1).LFunction (τ : ℂ)).re -
              (logDeriv (1 : DirichletCharacter ℂ 1).LFunction (σ : ℂ)).re -
              (τ - σ) * (∑ m ∈ B, Real.log m * realPairedEulerTerm χ τ m)) := by
  have hs0 : 1 / 2 < σ := lt_trans (by norm_num only) hs
  have hsum :=
    summable_completed_poissonDifferenceWeight hq hRH hp hne hinv hs0 (hs0.trans_le hst) u v
  have hAn : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hn (ρ : ℂ) : (0 : ℝ) ≤ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn ρ
  have hdom (ρ : ℂ) :
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * K ρ.im ≤
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        Analysis.poissonDifferenceWeight (σ - 1 / 2) (τ - 1 / 2) u v ρ.im :=
    mul_le_mul_of_nonneg_left (hmajorant ρ.im) (hn ρ)
  have hk := hsum.of_nonneg_of_le (fun ρ ↦ mul_nonneg (hn ρ) (hK ρ.im)) hdom
  exact
    ⟨hk,
      (hk.tsum_le_tsum hdom hsum).trans
        (completed_poissonDifferenceWeight_mass_le_retained_prefixes hq hRH hp hne hinv hs hst hv
          hvu A B)⟩

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
