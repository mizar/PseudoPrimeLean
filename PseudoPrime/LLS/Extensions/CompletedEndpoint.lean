/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.EntireHadamard
public import PseudoPrime.AnalyticNumberTheory.General.ShiftedZeroBounds
public import PseudoPrime.LLS.Extensions.CompletedZeroMass

/-!
# Completed logarithmic derivative at one

The admissible growth condition gives the genus-one Hadamard expansion. RH identifies
its value at one with the zero mass; the functional equation determines the real endpoint.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- Under RH, multiplicity times the genus-one term at one equals the completed zero mass.
This identifies the Hadamard series with the mass used in the general L-value formula. -/
theorem genus_one_term_eq_zeroMassTerm (f : GeneralLFunction) (hRH : f.RiemannHypothesis)
    (ρ : f.Zero) :
    (analyticOrderNatAt f.completed (ρ : ℂ) : ℂ) * (1 / (1 - (ρ : ℂ)) + 1 / (ρ : ℂ)) =
      (f.zeroMassTerm ρ : ℂ) := by
  rw [AnalyticNumberTheory.General.genus_one_eq_inverseSquare_of_re_half (hRH ρ)]
  simp only [zeroMassTerm, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_pow,
    Complex.ofReal_one]
  ring

/-- Admissibility and RH imply absolute convergence of the genus-one series at one.
The zero-mass series supplies convergence; the terms outside the zero subtype vanish. -/
theorem summable_genus_one_terms_of_admissible (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) :
    Summable (fun ρ : ℂ ↦ (analyticOrderNatAt f.completed ρ : ℂ) * (1 / (1 - ρ) + 1 / ρ)) := by
  have hs : Summable (fun ρ : f.Zero ↦ (f.zeroMassTerm ρ : ℂ)) :=
    (Complex.hasSum_ofReal.mpr (summable_zeroMassTerm_of_admissible f hf hRH).hasSum).summable
  have hsub :
    Summable
      (fun ρ : f.Zero ↦
        (analyticOrderNatAt f.completed (ρ : ℂ) : ℂ) * (1 / (1 - (ρ : ℂ)) + 1 / (ρ : ℂ))) :=
    hs.congr (fun ρ ↦ (genus_one_term_eq_zeroMassTerm f hRH ρ).symm)
  apply
    (Subtype.val_injective.summable_iff (f := fun ρ : ℂ ↦
          (analyticOrderNatAt f.completed ρ : ℂ) * (1 / (1 - ρ) + 1 / ρ)) ?_).mp
      hsub
  intro ρ hρ
  have hn : f.completed ρ ≠ 0 := fun hz ↦ hρ ⟨⟨ρ, hz⟩, rfl⟩
  have ho : analyticOrderNatAt f.completed ρ = 0 := by
    rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hn), ENat.toNat_zero]
  change (analyticOrderNatAt f.completed ρ : ℂ) * _ = 0
  rw [ho, Nat.cast_zero, zero_mul]

/-- For an admissible RH function, the difference of completed logarithmic derivatives at
one and zero is the zero mass. The entire Hadamard identity and absolute convergence
justify replacing the full plane sum by the sum over actual completed zeros. -/
theorem centered_logDeriv_completed_one_eq_zeroMass (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) :
    logDeriv f.completed 1 - logDeriv f.completed 0 = (f.zeroMass : ℂ) := by
  have hF : Differentiable ℂ f.completed := hf.2.2.2.2.2.2.2.1
  have h0 : f.completed 0 ≠ 0 :=
    completed_ne_zero_of_re_ne_half hRH (by norm_num only [Complex.zero_re])
  have h1 : f.completed 1 ≠ 0 :=
    completed_ne_zero_of_re_ne_half hRH (by norm_num only [Complex.one_re])
  obtain ⟨C, hC, hg⟩ :=
    AnalyticNumberTheory.General.exists_global_exponential_bound_of_orderAtMostOne hF.continuous
      hf.2.2.2.2.2.2.2.2.1 (show (1 : ℝ) < 3 / 2 by norm_num only)
  rw [AnalyticNumberTheory.General.centered_logDeriv_eq_genusSum hF h0 hC
      (show (0 : ℝ) ≤ 3 / 2 by norm_num only) (show (3 / 2 : ℝ) < 2 by norm_num only) hg h1
      (summable_genus_one_terms_of_admissible f hf hRH)]
  have he :
    (∑' ρ : f.Zero,
        (analyticOrderNatAt f.completed (ρ : ℂ) : ℂ) * (1 / (1 - (ρ : ℂ)) + 1 / (ρ : ℂ))) =
      (f.zeroMass : ℂ) := by
    simp only [genus_one_term_eq_zeroMassTerm f hRH]
    exact (Complex.hasSum_ofReal.mpr (summable_zeroMassTerm_of_admissible f hf hRH).hasSum).tsum_eq
  rw [← he]
  apply (Subtype.val_injective.tsum_eq ?_).symm
  intro ρ hρ
  by_contra hn
  have hFρ : f.completed ρ ≠ 0 := fun hz ↦ hn ⟨⟨ρ, hz⟩, rfl⟩
  have ho : analyticOrderNatAt f.completed ρ = 0 := by
    rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hFρ), ENat.toNat_zero]
  exact
    hρ
      (by
        change (analyticOrderNatAt f.completed ρ : ℂ) * _ = 0
        rw [ho, Nat.cast_zero, zero_mul])

/-- The conjugate functional equation relates the completed logarithmic derivatives at
one and zero. Differentiating the conjugate-reflected entire function removes the
constant root number. This relation supplies the endpoint normalization. -/
theorem logDeriv_completed_one_eq_neg_conj_zero (f : GeneralLFunction) (hf : f.IsAdmissible) :
    logDeriv f.completed 1 = -(starRingEnd ℂ) (logDeriv f.completed 0) := by
  have hF : Differentiable ℂ f.completed := hf.2.2.2.2.2.2.2.1
  obtain ⟨ε, hε, he⟩ := hf.2.2.2.2.2.2.2.2.2
  have hε0 : ε ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hε
    exact zero_ne_one hε
  have hc := (hF 0).hasDerivAt.conj_conj
  simp only [map_zero] at hc
  have hc' :
    HasDerivAt (fun z : ℂ ↦ (starRingEnd ℂ) (f.completed ((starRingEnd ℂ) z)))
      ((starRingEnd ℂ) (deriv f.completed 0)) (1 - (1 : ℂ)) := by
    simpa only [sub_self, Function.comp_def] using hc
  have hd := hc'.comp 1 ((hasDerivAt_id (1 : ℂ)).const_sub 1)
  simp only [Function.comp_def] at hd
  have hv :
    (fun z : ℂ ↦ ε * (starRingEnd ℂ) (f.completed (1 - (starRingEnd ℂ) z))) =
      (fun z : ℂ ↦ ε * (starRingEnd ℂ) (f.completed ((starRingEnd ℂ) (1 - z)))) := by
    funext z
    rw [map_sub, map_one]
  have hfun :
    f.completed = (fun z : ℂ ↦ ε * (starRingEnd ℂ) (f.completed ((starRingEnd ℂ) (1 - z)))) :=
    (funext he).trans hv
  calc
    logDeriv f.completed 1 =
        logDeriv (fun z : ℂ ↦ (starRingEnd ℂ) (f.completed ((starRingEnd ℂ) (1 - z)))) 1 :=
      by conv_lhs => rw [hfun, logDeriv_const_mul 1 ε hε0]
    _ = _ := by
      rw [logDeriv_apply, hd.deriv]
      simp only [sub_self, map_zero, mul_neg_one, neg_div, logDeriv_apply, map_div₀]

/-- For an admissible RH function, the real completed logarithmic derivative at one is
half its zero mass. Combine the centered Hadamard identity with the functional equation. -/
theorem re_logDeriv_completed_one_eq_half_zeroMass (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) : (logDeriv f.completed 1).re = f.zeroMass / 2 := by
  have hc := congrArg Complex.re (centered_logDeriv_completed_one_eq_zeroMass f hf hRH)
  have he := congrArg Complex.re (logDeriv_completed_one_eq_neg_conj_zero f hf)
  simp only [Complex.sub_re, Complex.ofReal_re] at hc
  simp only [Complex.neg_re, Complex.conj_re] at he
  linarith only [hc, he]

end PseudoPrime.LLS.Extensions.GeneralLFunction
