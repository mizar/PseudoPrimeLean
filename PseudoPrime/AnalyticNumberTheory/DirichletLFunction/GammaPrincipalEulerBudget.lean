/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.SignedResolventBounds
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.GammaSignedEulerBounds

/-! # Principal Euler budgets for signed primitive Gamma zero masses -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Input: an even character and a positive real argument.
Claim: its real Gamma logarithmic derivative is (Re digamma(sigma/2)-log pi)/2.
Proof: use the regular-point Gamma formula and take real parts.
Role: transport rational digamma bounds to the actual character Gamma factor. -/
theorem re_gammaFactor_even {q : ℕ} {χ : DirichletCharacter ℂ q} (he : χ.Even) {σ : ℝ}
    (hs : 0 < σ) :
    (logDeriv χ.gammaFactor (σ : ℂ)).re =
      ((Complex.digamma ((σ / 2 : ℝ) : ℂ)).re - Real.log Real.pi) / 2 := by
  have hh : ∀ m : ℕ, (σ : ℂ) / 2 ≠ -(m : ℂ) := by
    simpa only [Complex.ofReal_zero, add_zero] using
      half_add_ne_neg_nat_of_re_pos hs (le_refl (0 : ℝ))
  rw [logDeriv_gammaFactor_eq_of_even_of_half_ne_neg_nat he hh]
  rw [show (σ : ℂ) / 2 = ((σ / 2 : ℝ) : ℂ) from (Complex.ofReal_div σ 2).symm]
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.neg_re, Complex.log_re,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  ring

/-- Input: an odd character and a positive real argument.
Claim: its real Gamma logarithmic derivative has digamma argument (sigma+1)/2.
Proof: use the odd regular-point formula and take real parts.
Role: transport the shifted rational digamma bounds to odd characters. -/
theorem re_gammaFactor_odd {q : ℕ} {χ : DirichletCharacter ℂ q} (he : χ.Odd) {σ : ℝ} (hs : 0 < σ) :
    (logDeriv χ.gammaFactor (σ : ℂ)).re =
      ((Complex.digamma (((σ + 1) / 2 : ℝ) : ℂ)).re - Real.log Real.pi) / 2 := by
  have hh : ∀ m : ℕ, ((σ : ℂ) + 1) / 2 ≠ -(m : ℂ) := by
    simpa only [Complex.ofReal_one] using
      half_add_ne_neg_nat_of_re_pos hs (show (0 : ℝ) ≤ 1 by norm_num only)
  rw [logDeriv_gammaFactor_eq_of_odd_of_half_ne_neg_nat he hh]
  rw [show ((σ : ℂ) + 1) / 2 = (((σ + 1) / 2 : ℝ) : ℂ) from by
      simp only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_ofNat]]
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.neg_re, Complex.log_re,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  ring

/-- Input: an even character.
Claim: its signed Gamma contribution is at most -3/2.
Proof: identify each node with the certified even digamma combination.
Role: improve the fixed zero-mass cost for quadratic even characters. -/
theorem gammaResolvent_gammaFactor_0_le {q : ℕ} {χ : DirichletCharacter ℂ q} (he : χ.Even) :
    (Analysis.gammaResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum ≤
      -3 / 2 := by
  have ht := Gamma.signed_digamma_0_le
  have hm :
    (Analysis.gammaResolventCoefficients.map
        (fun ab ↦ (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)) =
      (Analysis.gammaResolventCoefficients.map
        (fun ab ↦
          (ab.2 : ℝ) *
            (((Complex.digamma ((((1 / 2 : ℝ) + (ab.1 : ℝ) + 0) / 2) : ℂ)).re - Real.log Real.pi) /
              2))) := by
    apply List.map_congr_left
    intro ab hab
    have ha :=
      Rat.cast_lt (K := ℝ) |>.mpr
        (List.forall_iff_forall_mem.mp Analysis.gammaResolvent_scales_gt_half ab hab)
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at ha
    have hh := re_gammaFactor_even he (show (0 : ℝ) < 1 / 2 + (ab.1 : ℝ) by linarith only [ha])
    simpa only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      Complex.ofReal_zero, add_zero] using congrArg (fun z : ℝ ↦ (ab.2 : ℝ) * z) hh
  rw [hm]
  exact ht

/-- Input: an odd character.
Claim: its signed Gamma contribution is at most -4/5.
Proof: identify each node with the certified odd digamma combination.
Role: retain a negative archimedean gain for odd characters. -/
theorem gammaResolvent_gammaFactor_1_le {q : ℕ} {χ : DirichletCharacter ℂ q} (he : χ.Odd) :
    (Analysis.gammaResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum ≤
      -4 / 5 := by
  have ht := Gamma.signed_digamma_1_le
  have hm :
    (Analysis.gammaResolventCoefficients.map
        (fun ab ↦ (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)) =
      (Analysis.gammaResolventCoefficients.map
        (fun ab ↦
          (ab.2 : ℝ) *
            (((Complex.digamma ((((1 / 2 : ℝ) + (ab.1 : ℝ) + 1) / 2) : ℂ)).re - Real.log Real.pi) /
              2))) := by
    apply List.map_congr_left
    intro ab hab
    have ha :=
      Rat.cast_lt (K := ℝ) |>.mpr
        (List.forall_iff_forall_mem.mp Analysis.gammaResolvent_scales_gt_half ab hab)
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at ha
    have hh := re_gammaFactor_odd he (show (0 : ℝ) < 1 / 2 + (ab.1 : ℝ) by linarith only [ha])
    simpa only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using congrArg (fun z : ℝ ↦ (ab.2 : ℝ) * z) hh
  rw [hm]
  exact ht

/-- Input: any complex Dirichlet character.
Claim: its signed Gamma contribution is at most -4/5.
Proof: split by parity and apply the two signed bounds.
Role: supply a parity-uniform primitive zero-mass estimate. -/
theorem gammaResolvent_gammaFactor_le {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (Analysis.gammaResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum ≤
      -4 / 5 := by
  rcases χ.even_or_odd with he | ho
  · exact (gammaResolvent_gammaFactor_0_le he).trans (by norm_num only)
  · exact gammaResolvent_gammaFactor_1_le ho

/-- Input: RH.
Claim: the common nonnegative Gamma Euler mass is strictly below 25/2.
Proof: xi positivity bounds it by poles plus the even Gamma contribution.
Role: remove the unresolved large finite-prefix input from this mass bound. -/
theorem gammaResolvent_euler_lt_twelve_half (hRH : RiemannHypothesis) :
    (∑' n : ℕ, Analysis.gammaResolventMangoldtWeight n) < 25 / 2 := by
  have he := RiemannXi.gammaResolvent_euler_lt_fourteen_add_gamma hRH
  have hg := gammaResolvent_gammaFactor_0_le principal_modulus_one_even
  linarith only [he, hg]

/-- Input: individual character RH, Riemann RH, primitive nonprincipal data and Gamma cap A.
Claim: the resolvent zero mass is below mu log q + 25/2 + A.
Proof: combine the empty-prefix character comparison with the principal Euler bound.
Role: expose a reusable signed mass interface for both parity cases. -/
theorem gammaResolvent_zeroMass_lt_principal_budget {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ)
    (hRiemann : RiemannHypothesis) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {A : ℝ}
    (hA :
      (Analysis.gammaResolventCoefficients.map
            (fun ab ↦
              (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum ≤
        A) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.gammaResolventMajorant ρ.im) <
      (11783423 / 25000000 : ℝ) * Real.log q + (25 / 2 + A) := by
  have hz := gammaResolvent_zeroMass_le_signed_prefix hq hRH hp hne hinv ∅
  simp only [Finset.sum_empty, mul_zero, sub_zero, add_zero] at hz
  have he := gammaResolvent_euler_lt_twelve_half hRiemann
  linarith only [hz, he, hA]

/-- Input: primitive nonprincipal even character, individual RH and Riemann RH.
Claim: the actual resolvent zero mass is below mu log q + 11.
Proof: retain the signed even Gamma gain in the principal Euler budget.
Role: lower the fixed analytic cost for negative quadratic witness comparisons. -/
theorem gammaResolvent_zeroMass_lt_principal_even {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ)
    (hRiemann : RiemannHypothesis) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (he : χ.Even) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.gammaResolventMajorant ρ.im) <
      (11783423 / 25000000 : ℝ) * Real.log q + 11 := by
  have h :=
    gammaResolvent_zeroMass_lt_principal_budget hq hRH hRiemann hp hne hinv
      (gammaResolvent_gammaFactor_0_le he)
  norm_num only at h
  exact h

/-- Input: primitive nonprincipal character, individual RH and Riemann RH.
Claim: its resolvent zero mass is below mu log q + 117/10.
Proof: use the parity-uniform negative Gamma cap.
Role: lower the fixed analytic cost for general witness comparisons. -/
theorem gammaResolvent_zeroMass_lt_principal_uniform {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ)
    (hRiemann : RiemannHypothesis) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.gammaResolventMajorant ρ.im) <
      (11783423 / 25000000 : ℝ) * Real.log q + 117 / 10 := by
  have h :=
    gammaResolvent_zeroMass_lt_principal_budget hq hRH hRiemann hp hne hinv
      (gammaResolvent_gammaFactor_le χ)
  norm_num only at h
  exact h

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
