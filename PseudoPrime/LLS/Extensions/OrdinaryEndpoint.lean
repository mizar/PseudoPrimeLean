/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.CompletedEndpoint

/-!
# Ordinary logarithmic derivative at one

The admissible completion identity gives analyticity in the right half-plane and
identifies the real endpoint derivative with the zero mass and gamma contribution.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- For complex gamma shifts with nonnegative real parts and `Re s > 0`, each
argument `(s + shift j)/2` avoids every nonpositive integer. Taking real parts gives a
strictly positive real part. This excludes gamma poles when differentiating the completion. -/
theorem gammaArgument_not_neg_nat (f : GeneralLFunction) (hκ : ∀ j, 0 ≤ (f.shift j).re) {s : ℂ}
    (hs : 0 < s.re) (j : Fin f.degree) (m : ℕ) : (s + f.shift j) / 2 ≠ -(m : ℂ) := by
  intro he
  have hr := congrArg Complex.re he
  simp only [Complex.div_ofNat_re, Complex.add_re, Complex.neg_re, Complex.natCast_re] at hr
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith only [hs, hκ j, hr, hm]

/-- The archimedean factor is nonzero on the right half-plane when every shift has
nonnegative real part. Each gamma factor and the complex power are nonzero. -/
theorem gammaFactor_ne_zero_of_re_pos (f : GeneralLFunction) (hκ : ∀ j, 0 ≤ (f.shift j).re) {s : ℂ}
    (hs : 0 < s.re) : f.gammaFactor s ≠ 0 := by
  unfold gammaFactor
  apply mul_ne_zero
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  · exact
      Finset.prod_ne_zero_iff.mpr
        (fun j _ ↦ Complex.Gamma_ne_zero (gammaArgument_not_neg_nat f hκ hs j))

/-- For complex shifts with nonnegative real parts and `Re s > 0`, the archimedean factor
is complex differentiable at `s`. Differentiate its complex power and finite gamma product;
the positive real parts of the gamma arguments exclude poles. This permits differentiation
of the completion identity. -/
theorem differentiableAt_gammaFactor_of_re_pos (f : GeneralLFunction) (hκ : ∀ j, 0 ≤ (f.shift j).re)
    {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ f.gammaFactor s := by
  have he : DifferentiableAt ℂ (fun z : ℂ ↦ -((f.degree : ℂ) * z) / 2) s :=
    ((differentiableAt_const (f.degree : ℂ)).mul differentiableAt_id).neg.div_const 2
  refine (he.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).mul ?_
  apply DifferentiableAt.fun_finsetProd
  intro j _
  exact
    (Complex.differentiableAt_Gamma _ (gammaArgument_not_neg_nat f hκ hs j)).comp s
      ((differentiableAt_id.add_const (f.shift j)).div_const 2)

/-- For complex shifts with nonnegative real parts and `Re s > 0`, the archimedean logarithmic
derivative equals `-degree * log π / 2` plus half the finite digamma sum.
The nonzero gamma factors justify the logarithmic product rule, and their affine arguments
give the factor one half. This isolates the gamma contribution from the ordinary L-function. -/
theorem logDeriv_gammaFactor_of_re_pos (f : GeneralLFunction) (hκ : ∀ j, 0 ≤ (f.shift j).re) {s : ℂ}
    (hs : 0 < s.re) :
    logDeriv f.gammaFactor s =
      -(f.degree : ℂ) * Complex.log Real.pi / 2 +
        (∑ j : Fin f.degree, logDeriv Complex.Gamma ((s + f.shift j) / 2)) / 2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have he : HasDerivAt (fun z : ℂ ↦ -((f.degree : ℂ) * z) / 2) (-(f.degree : ℂ) / 2) s := by
    simpa only [mul_one, Pi.neg_apply, id_eq] using
      ((hasDerivAt_id s).const_mul (f.degree : ℂ)).neg.div_const 2
  have hp : (∏ j : Fin f.degree, Complex.Gamma ((s + f.shift j) / 2)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr
      (fun j _ ↦ Complex.Gamma_ne_zero (gammaArgument_not_neg_nat f hκ hs j))
  have hg (j : Fin f.degree) :
    DifferentiableAt ℂ (fun z : ℂ ↦ Complex.Gamma ((z + f.shift j) / 2)) s :=
    (Complex.differentiableAt_Gamma _ (gammaArgument_not_neg_nat f hκ hs j)).comp s
      ((differentiableAt_id.add_const (f.shift j)).div_const 2)
  have hpc :
    logDeriv (fun z : ℂ ↦ (Real.pi : ℂ) ^ (-((f.degree : ℂ) * z) / 2)) s =
      -(f.degree : ℂ) * Complex.log Real.pi / 2 := by
    rw [logDeriv_apply, (he.const_cpow (Or.inl hpi)).deriv]
    field_simp [Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)]
  have ht :
    logDeriv (fun z : ℂ ↦ ∏ j : Fin f.degree, Complex.Gamma ((z + f.shift j) / 2)) s =
      (∑ j : Fin f.degree, logDeriv Complex.Gamma ((s + f.shift j) / 2)) / 2 := by
    rw [show
        (fun z : ℂ ↦ ∏ j : Fin f.degree, Complex.Gamma ((z + f.shift j) / 2)) =
          ∏ j : Fin f.degree, (fun z : ℂ ↦ Complex.Gamma ((z + f.shift j) / 2))
        by
        funext z
        rw [Finset.prod_apply]]
    rw [logDeriv_prod (f := fun j : Fin f.degree ↦ fun z : ℂ ↦ Complex.Gamma ((z + f.shift j) / 2))
        (x := s) (fun j _ ↦ Complex.Gamma_ne_zero (gammaArgument_not_neg_nat f hκ hs j))
        (fun j _ ↦ hg j)]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    have hj := (hasDerivAt_id s).add_const (f.shift j) |>.div_const 2
    simp only [id_eq] at hj
    rw [show
        (fun z : ℂ ↦ Complex.Gamma ((z + f.shift j) / 2)) =
          Complex.Gamma ∘ (fun z : ℂ ↦ (z + f.shift j) / 2)
        from rfl,
      logDeriv_comp (f := Complex.Gamma) (g := fun z : ℂ ↦ (z + f.shift j) / 2) (x := s)
        (Complex.differentiableAt_Gamma _ (gammaArgument_not_neg_nat f hκ hs j))
        hj.differentiableAt,
      hj.deriv]
    ring
  change
    logDeriv
        ((fun z : ℂ ↦ (Real.pi : ℂ) ^ (-((f.degree : ℂ) * z) / 2)) *
          (fun z : ℂ ↦ ∏ j : Fin f.degree, Complex.Gamma ((z + f.shift j) / 2)))
        s =
      _
  rw [logDeriv_mul (f := fun z : ℂ ↦ (Real.pi : ℂ) ^ (-((f.degree : ℂ) * z) / 2)) (g := fun z : ℂ ↦
      ∏ j : Fin f.degree, Complex.Gamma ((z + f.shift j) / 2)) s
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)) hp (he.const_cpow (Or.inl hpi)).differentiableAt
      (DifferentiableAt.fun_finsetProd (fun j _ ↦ hg j)),
    hpc, ht]

/-- For general data `f` and any complex `s`, define the completion multiplier
`conductor^(s/2) * gammaFactor s`, with complex powers and totalized gamma values.
For admissible data on `Re s > 0`, it is nonzero and its product with `L s` equals the
completed function. These facts allow the ordinary logarithmic derivative to be recovered
from the completed and archimedean derivatives. -/
noncomputable def completionFactor (f : GeneralLFunction) (s : ℂ) : ℂ :=
  (f.conductor : ℂ) ^ (s / 2) * f.gammaFactor s

/-- Admissibility makes the completion multiplier nonzero on the right half-plane.
The positive conductor and pole-free gamma product justify division by this factor. -/
theorem completionFactor_ne_zero_of_re_pos (f : GeneralLFunction) (hf : f.IsAdmissible) {s : ℂ}
    (hs : 0 < s.re) : f.completionFactor s ≠ 0 := by
  exact
    mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hf.2.1.ne')))
      (gammaFactor_ne_zero_of_re_pos f hf.2.2.2.1 hs)

/-- The completion multiplier is differentiable on the right half-plane for admissible
functions. This supplies the product and quotient rules for ordinary L-functions. -/
theorem differentiableAt_completionFactor_of_re_pos (f : GeneralLFunction) (hf : f.IsAdmissible)
    {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ f.completionFactor s := by
  exact
    ((differentiableAt_id.div_const (2 : ℂ)).const_cpow
          (Or.inl (Nat.cast_ne_zero.mpr hf.2.1.ne'))).mul
      (differentiableAt_gammaFactor_of_re_pos f hf.2.2.2.1 hs)

/-- On the right half-plane the ordinary L-function is the entire completion divided
by the nonzero completion multiplier. This follows from the admissibility identity. -/
theorem ordinary_eq_completed_div_of_re_pos (f : GeneralLFunction) (hf : f.IsAdmissible) {s : ℂ}
    (hs : 0 < s.re) : f.L s = f.completed s / f.completionFactor s := by
  exact
    (eq_div_iff (completionFactor_ne_zero_of_re_pos f hf hs)).mpr
      ((mul_comm _ _).trans (hf.2.2.2.2.2.2.1 s hs).symm)

/-- Admissibility implies that the ordinary L-function is differentiable on the right
half-plane. Locally it is the quotient of the entire completion by a nonzero factor. -/
theorem differentiableAt_ordinary_of_re_pos (f : GeneralLFunction) (hf : f.IsAdmissible) {s : ℂ}
    (hs : 0 < s.re) : DifferentiableAt ℂ f.L s := by
  have he : f.L =ᶠ[nhds s] (fun z ↦ f.completed z / f.completionFactor z) := by
    filter_upwards [Complex.continuous_re.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hs)] with z
      hz
    exact ordinary_eq_completed_div_of_re_pos f hf hz
  exact
    he.differentiableAt_iff.mpr
      ((hf.2.2.2.2.2.2.2.1 s).div (differentiableAt_completionFactor_of_re_pos f hf hs)
        (completionFactor_ne_zero_of_re_pos f hf hs))

/-- For admissible data and `Re s > 0`, the completion multiplier has logarithmic derivative
`(log conductor - degree * log π)/2` plus half the finite digamma sum.
Differentiate the nonzero conductor power and gamma product. This supplies the deterministic
archimedean term in the ordinary logarithmic derivative. -/
theorem logDeriv_completionFactor_of_re_pos (f : GeneralLFunction) (hf : f.IsAdmissible) {s : ℂ}
    (hs : 0 < s.re) :
    logDeriv f.completionFactor s =
      (Complex.log f.conductor - f.degree * Complex.log Real.pi) / 2 +
        (∑ j : Fin f.degree, logDeriv Complex.Gamma ((s + f.shift j) / 2)) / 2 := by
  have hc : (f.conductor : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hf.2.1.ne'
  have hd := (hasDerivAt_id s).div_const (2 : ℂ)
  simp only [id_eq] at hd
  have hp : logDeriv (fun z : ℂ ↦ (f.conductor : ℂ) ^ (z / 2)) s = Complex.log f.conductor / 2 := by
    rw [logDeriv_apply, (hd.const_cpow (Or.inl hc)).deriv]
    field_simp [Complex.cpow_ne_zero_iff.mpr (Or.inl hc)]
  change logDeriv ((fun z : ℂ ↦ (f.conductor : ℂ) ^ (z / 2)) * f.gammaFactor) s = _
  rw [logDeriv_mul (f := fun z : ℂ ↦ (f.conductor : ℂ) ^ (z / 2)) (g := f.gammaFactor) s
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hc)) (gammaFactor_ne_zero_of_re_pos f hf.2.2.2.1 hs)
      (hd.const_cpow (Or.inl hc)).differentiableAt
      (differentiableAt_gammaFactor_of_re_pos f hf.2.2.2.1 hs),
    hp, logDeriv_gammaFactor_of_re_pos f hf.2.2.2.1 hs]
  ring

/-- At one, the real logarithmic derivative of the completion multiplier equals the
normalized gamma contribution used in the general L-value formula. -/
theorem re_logDeriv_completionFactor_one (f : GeneralLFunction) (hf : f.IsAdmissible) :
    (logDeriv f.completionFactor 1).re = f.gammaLogDerivativeAtOne := by
  rw [logDeriv_completionFactor_of_re_pos f hf
      (show (0 : ℝ) < (1 : ℂ).re by norm_num only [Complex.one_re])]
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.log_ofReal_re, Complex.re_sum,
    ← Complex.ofReal_natCast]
  unfold gammaLogDerivativeAtOne
  rw [Real.log_div (Nat.cast_ne_zero.mpr hf.2.1.ne') (pow_ne_zero _ Real.pi_ne_zero), Real.log_pow]

/-- At a nonzero completed value in the right half-plane, the completed logarithmic
derivative splits into the completion-factor and ordinary logarithmic derivatives.
The local admissibility identity and product rule give the split. -/
theorem logDeriv_completed_eq_completionFactor_add (f : GeneralLFunction) (hf : f.IsAdmissible)
    {s : ℂ} (hs : 0 < s.re) (hne : f.completed s ≠ 0) :
    logDeriv f.completed s = logDeriv f.completionFactor s + logDeriv f.L s := by
  have hL : f.L s ≠ 0 := by
    intro hz
    apply hne
    rw [hf.2.2.2.2.2.2.1 s hs, hz, mul_zero]
  have he : f.completed =ᶠ[nhds s] f.completionFactor * f.L := by
    filter_upwards [Complex.continuous_re.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hs)] with z
      hz
    exact hf.2.2.2.2.2.2.1 z hz
  have hl : logDeriv f.completed s = logDeriv (f.completionFactor * f.L) s := by
    rw [logDeriv_apply, logDeriv_apply, he.deriv_eq, he.eq_of_nhds]
  rw [hl,
    logDeriv_mul s (completionFactor_ne_zero_of_re_pos f hf hs) hL
      (differentiableAt_completionFactor_of_re_pos f hf hs)
      (differentiableAt_ordinary_of_re_pos f hf hs)]

/-- For an admissible RH function, the real ordinary logarithmic derivative at one is
half the completed zero mass minus the gamma contribution. The completed endpoint
identity and the product decomposition remove any separate endpoint assumption. -/
theorem re_logDeriv_ordinary_one_eq_half_zeroMass_sub_gamma (f : GeneralLFunction)
    (hf : f.IsAdmissible) (hRH : f.RiemannHypothesis) :
    (logDeriv f.L 1).re = f.zeroMass / 2 - f.gammaLogDerivativeAtOne := by
  have he :=
    congrArg Complex.re
      (logDeriv_completed_eq_completionFactor_add f hf
        (show (0 : ℝ) < (1 : ℂ).re by norm_num only [Complex.one_re])
        (completed_ne_zero_of_re_ne_half hRH (by norm_num only [Complex.one_re])))
  rw [Complex.add_re, re_logDeriv_completed_one_eq_half_zeroMass f hf hRH,
    re_logDeriv_completionFactor_one f hf] at he
  linarith only [he]

end PseudoPrime.LLS.Extensions.GeneralLFunction
