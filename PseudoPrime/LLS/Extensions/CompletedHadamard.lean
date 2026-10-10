/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.OrdinaryEndpoint
public import PseudoPrime.AnalyticNumberTheory.Gamma.ResolventSeries
public import PseudoPrime.AnalyticNumberTheory.Gamma.EulerLogSeries

/-!
# Completed Hadamard expansion on the zero-free half-plane

The zero mass controls the genus-one series away from the critical line.
Subtracting two expansions separates ordinary logarithmic derivatives into zero and gamma terms.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- For admissible RH data and Re s > 1/2, the completed genus-one series is absolutely summable.
The explicit inverse-square majorant reduces convergence to the completed zero mass. -/
theorem summable_genus_terms_of_admissible (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (fun ρ : ℂ ↦ (analyticOrderNatAt f.completed ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)) := by
  have hsub :
    Summable
      (fun ρ : f.Zero ↦
        (analyticOrderNatAt f.completed (ρ : ℂ) : ℂ) * (1 / (s - (ρ : ℂ)) + 1 / (ρ : ℂ))) := by
    apply
      Summable.of_norm_bounded
        ((summable_zeroMassTerm_of_admissible f hf hRH).mul_left (‖s‖ * (1 + ‖s‖ / (s.re - 1 / 2))))
    intro ρ
    rw [norm_mul, norm_natCast]
    have h :=
      mul_le_mul_of_nonneg_left
        (AnalyticNumberTheory.General.norm_genusTerm_le_inverseSquare (hRH ρ) hs)
        (Nat.cast_nonneg (analyticOrderNatAt f.completed (ρ : ℂ)) : (0 : ℝ) ≤ _)
    exact
      h.trans_eq
        (by
          unfold zeroMassTerm; ring)
  apply
    (Subtype.val_injective.summable_iff (f := fun ρ : ℂ ↦
          (analyticOrderNatAt f.completed ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)) ?_).mp
      hsub
  intro ρ hρ
  have hn : f.completed ρ ≠ 0 := fun hz ↦ hρ ⟨⟨ρ, hz⟩, rfl⟩
  have ho : analyticOrderNatAt f.completed ρ = 0 := by
    rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hn), ENat.toNat_zero]
  change (analyticOrderNatAt f.completed ρ : ℂ) * _ = 0
  rw [ho, Nat.cast_zero, zero_mul]

/-- For admissible RH data, the centered completed logarithmic derivative has its genus-one
Hadamard expansion throughout Re s > 1/2. Growth and mass convergence supply all hypotheses. -/
theorem centered_logDeriv_completed_eq_genusSum (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) :
    logDeriv f.completed s - logDeriv f.completed 0 =
      ∑' ρ : ℂ, (analyticOrderNatAt f.completed ρ : ℂ) * (1 / (s - ρ) + 1 / ρ) := by
  have hF : Differentiable ℂ f.completed := hf.2.2.2.2.2.2.2.1
  have h0 : f.completed 0 ≠ 0 :=
    completed_ne_zero_of_re_ne_half hRH (by norm_num only [Complex.zero_re])
  have hne : f.completed s ≠ 0 := completed_ne_zero_of_re_ne_half hRH hs.ne'
  obtain ⟨C, hC, hg⟩ :=
    AnalyticNumberTheory.General.exists_global_exponential_bound_of_orderAtMostOne hF.continuous
      hf.2.2.2.2.2.2.2.2.1 (show (1 : ℝ) < 3 / 2 by norm_num only)
  exact
    AnalyticNumberTheory.General.centered_logDeriv_eq_genusSum hF h0 hC
      (show (0 : ℝ) ≤ 3 / 2 by norm_num only) (show (3 / 2 : ℝ) < 2 by norm_num only) hg hne
      (summable_genus_terms_of_admissible f hf hRH hs)

/-- For admissible RH data and two points to the right of the critical line, the difference
of completed logarithmic derivatives is the convergent difference of zero resolvents.
Subtract the two genus-one expansions to cancel the center and reciprocal-zero terms. -/
theorem logDeriv_completed_sub_eq_zeroSeries (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {s t : ℂ} (hs : 1 / 2 < s.re) (ht : 1 / 2 < t.re) :
    logDeriv f.completed s - logDeriv f.completed t =
      ∑' ρ : ℂ, (analyticOrderNatAt f.completed ρ : ℂ) * (1 / (s - ρ) - 1 / (t - ρ)) := by
  have he :
    logDeriv f.completed s - logDeriv f.completed t =
      (logDeriv f.completed s - logDeriv f.completed 0) -
        (logDeriv f.completed t - logDeriv f.completed 0) := by
    ring
  rw [he, centered_logDeriv_completed_eq_genusSum f hf hRH hs,
    centered_logDeriv_completed_eq_genusSum f hf hRH ht, ←
    (summable_genus_terms_of_admissible f hf hRH hs).tsum_sub
      (summable_genus_terms_of_admissible f hf hRH ht)]
  exact tsum_congr (fun ρ ↦ by ring)

/-- For admissible RH data and two points to the right of the critical line, the ordinary
logarithmic derivative difference is the zero-resolvent sum minus the completion-factor difference.
Combine the completed Hadamard expansion with the completion product rule. -/
theorem logDeriv_ordinary_sub_eq_zeroSeries_sub_gamma (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {s t : ℂ} (hs : 1 / 2 < s.re) (ht : 1 / 2 < t.re) :
    logDeriv f.L s - logDeriv f.L t =
      (∑' ρ : ℂ, (analyticOrderNatAt f.completed ρ : ℂ) * (1 / (s - ρ) - 1 / (t - ρ))) -
        (logDeriv f.completionFactor s - logDeriv f.completionFactor t) := by
  have hcs :=
    logDeriv_completed_eq_completionFactor_add f hf
      (lt_trans (by norm_num only : (0 : ℝ) < 1 / 2) hs)
      (completed_ne_zero_of_re_ne_half hRH hs.ne')
  have hct :=
    logDeriv_completed_eq_completionFactor_add f hf
      (lt_trans (by norm_num only : (0 : ℝ) < 1 / 2) ht)
      (completed_ne_zero_of_re_ne_half hRH ht.ne')
  have he := logDeriv_completed_sub_eq_zeroSeries f hf hRH hs ht
  rw [hcs, hct] at he
  linear_combination he

/-- For admissible data and positive real parts, the difference of completion logarithmic
derivatives is half the finite digamma difference sum. The conductor and pi constants cancel. -/
theorem logDeriv_completionFactor_sub_eq_digammaSum (f : GeneralLFunction) (hf : f.IsAdmissible)
    {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re) :
    logDeriv f.completionFactor s - logDeriv f.completionFactor t =
      (∑ j : Fin f.degree,
          (Complex.digamma ((s + f.shift j) / 2) - Complex.digamma ((t + f.shift j) / 2))) /
        2 := by
  rw [logDeriv_completionFactor_of_re_pos f hf hs, logDeriv_completionFactor_of_re_pos f hf ht,
    Finset.sum_sub_distrib, Complex.digamma_def]
  ring

/-- For admissible data and Re s > 0, every shifted gamma argument has positive real part.
Add the nonnegative real part of the complex shift to Re s and divide by two.
This verifies the domain condition for the digamma recurrence and resolvent series. -/
theorem digammaArgument_re_pos (f : GeneralLFunction) (hf : f.IsAdmissible) {s : ℂ} (hs : 0 < s.re)
    (j : Fin f.degree) : 0 < ((s + f.shift j) / 2).re := by
  rw [Complex.div_ofNat_re, Complex.add_re]
  exact div_pos (lt_of_lt_of_le hs (le_add_of_nonneg_right (hf.2.2.2.1 j))) (by norm_num only)

/-- For admissible data, Re s > 0, Re t > 0, and a natural cutoff n, the difference
of logarithmic derivatives of the completion factor equals half the sum of
the translated digamma differences minus the finite reciprocal differences.
Apply the digamma recurrence at each shifted argument; this separates the finite
resolvent sum from the translated remainder. -/
theorem logDeriv_completionFactor_sub_eq_partial_resolvent (f : GeneralLFunction)
    (hf : f.IsAdmissible) {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re) (n : ℕ) :
    logDeriv f.completionFactor s - logDeriv f.completionFactor t =
      (∑ j : Fin f.degree,
          ((Complex.digamma (((s + f.shift j) / 2) + n) -
              Complex.digamma (((t + f.shift j) / 2) + n)) -
            ∑ k ∈ Finset.range n,
              (1 / (((s + f.shift j) / 2) + k) - 1 / (((t + f.shift j) / 2) + k)))) /
        2 := by
  rw [logDeriv_completionFactor_sub_eq_digammaSum f hf hs ht]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have h :=
    AnalyticNumberTheory.Gamma.digamma_sub_add_nat_eq_partial_resolvent
      (digammaArgument_re_pos f hf hs j) (digammaArgument_re_pos f hf ht j) n
  linear_combination -h

/-- For admissible data at two points with positive real parts, the difference of
logarithmic derivatives of the completion factor is half the finite sum of
convergent gamma reciprocal difference series. Apply the digamma series identity
to each shifted argument. This represents the gamma contribution to the ordinary
L-function logarithmic derivative difference. -/
theorem logDeriv_completionFactor_sub_eq_resolventSeries (f : GeneralLFunction)
    (hf : f.IsAdmissible) {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re) :
    logDeriv f.completionFactor s - logDeriv f.completionFactor t =
      (∑ j : Fin f.degree,
          ∑' n : ℕ, (1 / (((t + f.shift j) / 2) + n) - 1 / (((s + f.shift j) / 2) + n))) /
        2 := by
  rw [logDeriv_completionFactor_sub_eq_digammaSum f hf hs ht]
  congr 1
  exact
    Finset.sum_congr rfl
      (fun j _ ↦
        AnalyticNumberTheory.Gamma.digamma_sub_eq_resolventSeries (digammaArgument_re_pos f hf hs j)
          (digammaArgument_re_pos f hf ht j))

end PseudoPrime.LLS.Extensions.GeneralLFunction
