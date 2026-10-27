/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.EntireCanonicalFactors
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HadamardLimit
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.LocalZeroCounting
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.CompletedGenusZeroSums
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.LocalZeroTuran
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.Counting

/-! # Higher derivative bounds for canonical remainders -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/--
Inputs: a primitive nontrivial character, a zero-free circle of radius $R$, a finite-radius
Hadamard factorization, a lower bound on the radius, and a positive derivative order.
Claim: the higher derivatives at the center of the canonical factor's logarithmic derivative have
an explicit bound in terms of the conductor and height.
Content: transfer the centered difference estimate to the closed disk of radius $R/4$ and apply
Cauchy's estimate to the function with its center value subtracted.
Role: bounds the analytic-factor error separated from the local zero sum.
-/
theorem norm_iteratedDeriv_ecanonicalDecomp_logDeriv_le {N : ℕ} [NeZero N] (hN1 : 1 < N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {R : ℝ}
    (hR : 1 ≤ R) {g : ℂ → ℂ}
    (D : Complex.ECanonicalDecomp (DirichletCharacter.completedLFunction χ) g R)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → DirichletCharacter.completedLFunction χ ρ ≠ 0) (n : ℕ) (hn : 0 < n) :
    ‖iteratedDeriv n (logDeriv g) 0‖ ≤
      n.factorial *
          (192 * (R / 4) *
              |(4 * (N : ℝ) + 3) * (R + 3) * Real.log (R + 3) -
                    Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
                  1| /
            R ^ 2) /
        (R / 4) ^ n := by
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) hR
  have hrpos : 0 < R / 4 := div_pos hRpos (by norm_num only)
  have hrle : R / 4 ≤ R := by linarith only [hR]
  have hsubset : Metric.closedBall (0 : ℂ) (R / 4) ⊆ Metric.closedBall 0 R := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz ⊢
    exact hz.trans hrle
  have hf : AnalyticOnNhd ℂ g (Metric.closedBall 0 (R / 4)) := by
    intro z hz
    exact D.analyticOnNhd z (hsubset hz)
  have hgn : ∀ z ∈ Metric.closedBall 0 (R / 4), g z ≠ 0 := by
    intro z hz
    exact D.ne_zero z (hsubset hz)
  have hloganalytic : AnalyticOnNhd ℂ (logDeriv g) (Metric.closedBall 0 (R / 4)) := by
    intro z hz
    have hfun : logDeriv g = fun w => deriv g w / g w := by
      funext w
      exact logDeriv_apply g w
    rw [hfun]
    exact (hf z hz).deriv.div (hf z hz) (hgn z hz)
  let A : ℝ :=
    (4 * (N : ℝ) + 3) * (R + 3) * Real.log (R + 3) -
        Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
      1
  let C : ℝ := 192 * (R / 4) * |A| / R ^ 2
  have hC : ∀ z ∈ Metric.closedBall (0 : ℂ) (R / 4), ‖logDeriv g z - logDeriv g 0‖ ≤ C := by
    intro z hz
    have hzNorm : ‖z‖ ≤ R / 4 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    have hzHalf : ‖z‖ ≤ R / 2 := by linarith only [hzNorm, hR]
    have hv := norm_logDeriv_ecanonicalDecomp_sub_le hN1 hprimitive hne hinv hR D hzf hzHalf
    have hA : A ≤ |A| := le_abs_self A
    have hden : 0 < R ^ 2 := pow_pos hRpos 2
    calc
      ‖logDeriv g z - logDeriv g 0‖ ≤ 192 * ‖z‖ * A / R ^ 2 := hv
      _ ≤ 192 * ‖z‖ * |A| / R ^ 2 := by
        apply (div_le_div_iff_of_pos_right hden).2
        exact mul_le_mul_of_nonneg_left hA (by positivity)
      _ ≤ 192 * (R / 4) * |A| / R ^ 2 := by
        apply (div_le_div_iff_of_pos_right hden).2
        exact
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzNorm (by positivity))
            (abs_nonneg A)
      _ = C := rfl
  change ‖iteratedDeriv n (logDeriv g) 0‖ ≤ n.factorial * C / (R / 4) ^ n
  exact norm_iteratedDeriv_le_of_forall_ball_norm_sub_center_le n hn hrpos hloganalytic hC

/--
Inputs: a nonzero point $u$ in the disk of positive radius $R$ and a derivative order $n$.
Claim: the centered iterated derivative of the canonical factor's logarithmic derivative is the
difference of inverse-distance powers at $u$ and its reflection $R^2/\overline{u}$.
Content: split the logarithmic derivative into two simple reciprocals and use
`iteratedDeriv_sub_const_inv`.
Role: separates higher derivatives of a finite Hadamard product into a local zero sum and a
boundary correction.
-/
theorem iteratedDeriv_logDeriv_canonicalFactor_at_zero {R : ℝ} {u : ℂ}
    (hu : u ∈ Metric.ball (0 : ℂ) R) (hu0 : u ≠ 0) (n : ℕ) :
    iteratedDeriv n (logDeriv (Complex.canonicalFactor R u)) 0 =
      (-1 : ℂ) ^ n * (n.factorial : ℂ) *
          ((0 : ℂ) - (R : ℂ) ^ 2 / (starRingEnd ℂ u)) ^ (-1 - n : ℤ) -
        (-1 : ℂ) ^ n * (n.factorial : ℂ) * ((0 : ℂ) - u) ^ (-1 - n : ℤ) := by
  have hRpos : 0 < R := Metric.pos_of_mem_ball hu
  have huNormpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  let δ : ℝ := min R ‖u‖ / 2
  have hδpos : 0 < δ := div_pos (lt_min hRpos huNormpos) (by norm_num only)
  let v : ℂ := (R : ℂ) ^ 2 / (starRingEnd ℂ u)
  have hstar : starRingEnd ℂ u ≠ 0 := star_ne_zero.mpr hu0
  have hv0 : v ≠ 0 := div_ne_zero (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hRpos.ne')) hstar
  have hpoint :
    ∀ z ∈ Metric.ball (0 : ℂ) δ,
      logDeriv (Complex.canonicalFactor R u) z = (z - v)⁻¹ - (z - u)⁻¹ := by
    intro z hz
    have hzNorm : ‖z‖ < δ := by
      rw [Metric.mem_ball, dist_zero_right] at hz
      exact hz
    have hδR : δ ≤ R := by
      dsimp [δ]
      calc
        min R ‖u‖ / 2 ≤ R / 2 := div_le_div_of_nonneg_right (min_le_left R ‖u‖) (by norm_num)
        _ ≤ R := by linarith only [hRpos]
    have hzclosed : z ∈ Metric.closedBall (0 : ℂ) R := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hzNorm.le.trans hδR
    have hδu : δ ≤ ‖u‖ / 2 := by
      dsimp [δ]
      exact div_le_div_of_nonneg_right (min_le_right R ‖u‖) (by norm_num)
    have hzu : z ≠ u := by
      intro h
      rw [h] at hzNorm
      linarith only [hzNorm, hδu, norm_nonneg u]
    have hcfne := Complex.canonicalFactor_ne_zero hu hzclosed hzu
    rw [Complex.canonicalFactor_apply] at hcfne
    have hNne := (div_ne_zero_iff.mp hcfne).1
    have hden : (R : ℂ) ^ 2 - (starRingEnd ℂ u) * z = -(starRingEnd ℂ u) * (z - v) := by
      dsimp [v]
      field_simp [hstar]
      ring
    have hzv : z ≠ v := by
      intro h
      apply hNne
      rw [hden, h]
      simp only [sub_self, mul_zero]
    have hfirst : -(starRingEnd ℂ u) / ((R : ℂ) ^ 2 - (starRingEnd ℂ u) * z) = (z - v)⁻¹ := by
      rw [hden]
      field_simp [hstar, hzv]
    rw [General.logDeriv_canonicalFactor hu hzclosed hzu, hfirst]
    simp only [one_div]
  have hEq :
    logDeriv (Complex.canonicalFactor R u) =ᶠ[nhds (0 : ℂ)] (fun z => (z - v)⁻¹ - (z - u)⁻¹) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hδpos] with z hz
    exact hpoint z hz
  have hderivEq := hEq.iteratedDeriv n
  have hcenter := Filter.EventuallyEq.eq_of_nhds hderivEq
  have hV : AnalyticAt ℂ (fun z : ℂ => (z - v)⁻¹) 0 :=
    (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr (Ne.symm hv0))
  have hU : AnalyticAt ℂ (fun z : ℂ => (z - u)⁻¹) 0 :=
    (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr (Ne.symm hu0))
  rw [hcenter]
  change iteratedDeriv n ((fun z : ℂ => (z - v)⁻¹) - (fun z : ℂ => (z - u)⁻¹)) 0 = _
  rw [iteratedDeriv_sub hV.contDiffAt hU.contDiffAt]
  rw [iteratedDeriv_sub_const_inv v n, iteratedDeriv_sub_const_inv u n]

/--
Inputs: a finitely supported coefficient function $m$, a family $f_u$ analytic at the center on
the support of $m$, and a derivative order $n$.
Claim: iterated derivatives of the weighted `finsum` distribute over its terms.
Content: rewrite the finitely supported sum as a finite sum and apply `iteratedDeriv_fun_sum` and
the constant-multiple formula.
Role: distributes canonical-factor terms over the finite divisor support in higher Hadamard
identities.
-/
theorem iteratedDeriv_finsum_const_mul {m : ℂ → ℂ} {f : ℂ → ℂ → ℂ}
    (hm : (Function.support m).Finite) (n : ℕ)
    (hf : ∀ u ∈ Function.support m, AnalyticAt ℂ (f u) 0) :
    iteratedDeriv n (fun z => ∑ᶠ u, m u * f u z) 0 = ∑ᶠ u, m u * iteratedDeriv n (f u) 0 := by
  let s := hm.toFinset
  have hleft : (fun z : ℂ => ∑ᶠ u, m u * f u z) = ∑ u ∈ s, fun w : ℂ => m u * f u w := by
    funext z
    rw [finsum_eq_sum_of_support_subset _ (s := s)]
    · simp only [Finset.sum_apply]
    · intro u hu
      simp only [Function.mem_support] at hu
      have hmu : m u ≠ 0 := by
        intro h
        apply hu
        simp only [h, zero_mul]
      have hmem : u ∈ Function.support m := by
        simp only [Function.mem_support]
        exact hmu
      simpa only [s, Finset.mem_coe] using (Set.Finite.mem_toFinset hm).mpr hmem
  have hright : (∑ u ∈ s, m u * iteratedDeriv n (f u) 0) = ∑ᶠ u, m u * iteratedDeriv n (f u) 0 := by
    symm
    rw [finsum_eq_sum_of_support_subset _ (s := s)]
    intro u hu
    simp only [Function.mem_support] at hu
    have hmu : m u ≠ 0 := by
      intro h
      apply hu
      simp only [h, zero_mul]
    have hmem : u ∈ Function.support m := by
      simp only [Function.mem_support]
      exact hmu
    simpa only [s, Finset.mem_coe] using (Set.Finite.mem_toFinset hm).mpr hmem
  have hSumFun : (∑ u ∈ s, fun z : ℂ => m u * f u z) = (fun z => ∑ u ∈ s, m u * f u z) := by
    funext z
    simp only [Finset.sum_apply]
  have hsmooth : ∀ u ∈ s, ContDiffAt ℂ n (fun z => m u * f u z) 0 := by
    intro u hu
    have hmem : u ∈ Function.support m := by simpa only [s] using (Set.Finite.mem_toFinset hm).mp hu
    exact (analyticAt_const.mul (hf u hmem)).contDiffAt
  calc
    iteratedDeriv n (fun z => ∑ᶠ u, m u * f u z) 0 =
        iteratedDeriv n (∑ u ∈ s, fun z => m u * f u z) 0 :=
      by rw [hleft]
    _ = ∑ u ∈ s, m u * iteratedDeriv n (f u) 0 := by
      rw [hSumFun, iteratedDeriv_fun_sum hsmooth]
      apply Finset.sum_congr rfl
      intro u hu
      have hmem : u ∈ Function.support m := by
        simpa only [s] using (Set.Finite.mem_toFinset hm).mp hu
      exact iteratedDeriv_const_mul (m u) (hf u hmem).contDiffAt
    _ = ∑ᶠ u, m u * iteratedDeriv n (f u) 0 := hright

/--
Inputs: a finitely supported coefficient function and a family analytic at the center on its
support.
Claim: the associated finite weighted `finsum` is analytic at the center.
Content: rewrite the finitely supported sum as a finite sum and apply analyticity of finite sums.
Role: supplies the regularity needed to differentiate the Hadamard center identity repeatedly.
-/
theorem analyticAt_finsum_const_mul {m : ℂ → ℂ} {f : ℂ → ℂ → ℂ} (hm : (Function.support m).Finite)
    (hf : ∀ u ∈ Function.support m, AnalyticAt ℂ (f u) 0) :
    AnalyticAt ℂ (fun z => ∑ᶠ u, m u * f u z) 0 := by
  let s := hm.toFinset
  have hleft : (fun z : ℂ => ∑ᶠ u, m u * f u z) = ∑ u ∈ s, fun w : ℂ => m u * f u w := by
    funext z
    rw [finsum_eq_sum_of_support_subset _ (s := s)]
    · simp only [Finset.sum_apply]
    · intro u hu
      simp only [Function.mem_support] at hu
      have hmu : m u ≠ 0 := by
        intro h
        apply hu
        simp only [h, zero_mul]
      have hmem : u ∈ Function.support m := by
        simp only [Function.mem_support]
        exact hmu
      simpa only [s, Finset.mem_coe] using (Set.Finite.mem_toFinset hm).mpr hmem
  rw [hleft]
  apply Finset.analyticAt_sum s
  intro u hu
  have hmem : u ∈ Function.support m := by simpa only [s] using (Set.Finite.mem_toFinset hm).mp hu
  exact (analyticAt_const.mul (hf u hmem))

/--
Inputs: a finitely supported coefficient function, nonvanishing of the canonical factors on its
support, a positive radius, and a derivative order.
Claim: the centered iterated derivative of the weighted `finsum` of canonical-factor logarithmic
derivatives equals the sum of the termwise derivatives.
Content: establish analyticity and nonvanishing at the center for each supported factor, then
interchange differentiation with the finite sum.
Role: computes the zero term in higher Hadamard identities with divisor multiplicities.
-/
theorem iteratedDeriv_finsum_canonicalFactor_logDeriv {R : ℝ} {m : ℂ → ℂ}
    (hm : (Function.support m).Finite) (hR : 0 < R)
    (hsupport : ∀ u ∈ Function.support m, u ∈ Metric.ball (0 : ℂ) R ∧ u ≠ 0) (n : ℕ) :
    iteratedDeriv n (fun z => ∑ᶠ u, m u * logDeriv (Complex.canonicalFactor R u) z) 0 =
      ∑ᶠ u, m u * iteratedDeriv n (logDeriv (Complex.canonicalFactor R u)) 0 := by
  apply iteratedDeriv_finsum_const_mul hm n
  intro u hu
  obtain ⟨huball, hu0⟩ := hsupport u hu
  have hcan : AnalyticAt ℂ (Complex.canonicalFactor R u) 0 :=
    Complex.analyticOnNhd_canonicalFactor R u 0 (Ne.symm hu0)
  have h0closed : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_self]
    exact hR.le
  have hcanne : Complex.canonicalFactor R u 0 ≠ 0 :=
    Complex.canonicalFactor_ne_zero huball h0closed (Ne.symm hu0)
  have hfun :
    logDeriv (Complex.canonicalFactor R u) = fun w =>
      deriv (Complex.canonicalFactor R u) w / Complex.canonicalFactor R u w := by
    funext w
    exact logDeriv_apply (Complex.canonicalFactor R u) w
  rw [hfun]
  exact hcan.deriv.div hcan hcanne

/--
Inputs: a primitive nontrivial character, a positive finite Hadamard radius, and a derivative
order.
Claim: the centered iterated derivative of the canonical-factor logarithmic-derivative sum in the
finite-radius Hadamard factorization can be computed term by term.
Content: use nonvanishing of the completed L-function at the center to show that the divisor
support avoids the center, then apply the finite-support interchange lemma.
Role: connects local inverse-distance zero sums to higher identities from the Hadamard
factorization.
-/
theorem iteratedDeriv_divisor_canonicalFactor_logDeriv_at_zero {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (h0 : F 0 ≠ 0) {R : ℝ} (hR : 0 < R) (n : ℕ) :
    iteratedDeriv n
        (fun z =>
          ∑ᶠ u : ℂ,
            ((-MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R) u : ℤ) : ℂ) *
              logDeriv (Complex.canonicalFactor R u) z)
        0 =
      ∑ᶠ u : ℂ,
        ((-MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R) u : ℤ) : ℂ) *
          iteratedDeriv n (logDeriv (Complex.canonicalFactor R u)) 0 := by
  let m : ℂ → ℂ := fun u => ((-MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R) u : ℤ) : ℂ)
  have hanalyticClosed : AnalyticOnNhd ℂ F (Metric.closedBall 0 R) := fun z _ => hF.analyticAt z
  have hfin := hanalyticClosed.meromorphicOn.divisor_ball_support_finite
  have hdfin :
    (Function.support fun u : ℂ => -MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R) u).Finite := by
    have hset :
      Function.support (fun u : ℂ => -MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R) u) =
        Function.support (MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R)) := by
      ext u
      simp only [Function.mem_support]
      constructor
      · intro h hz
        apply h
        rw [hz, neg_zero]
      · intro h hz
        apply h
        exact neg_eq_zero.mp hz
    rw [hset]
    exact hfin
  have hm : (Function.support m).Finite := by
    apply hdfin.subset
    intro u hu
    have hdiv : MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R) u ≠ 0 := by
      have hu' : m u ≠ 0 := by simpa only [Function.mem_support] using hu
      intro hz
      apply hu'
      change ((-MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R) u : ℤ) : ℂ) = 0
      rw [hz]
      simp only [Int.cast_zero, neg_zero]
    change u ∈ Function.support (fun v : ℂ => -MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R) v)
    change -MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R) u ≠ 0
    exact neg_ne_zero.mpr hdiv
  have hsupport : ∀ u ∈ Function.support m, u ∈ Metric.ball (0 : ℂ) R ∧ u ≠ 0 := by
    intro u hu
    have hdiv : MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R) u ≠ 0 := by
      have hu' : m u ≠ 0 := by simpa only [Function.mem_support] using hu
      intro hz
      apply hu'
      change ((-MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R) u : ℤ) : ℂ) = 0
      rw [hz]
      simp only [Int.cast_zero, neg_zero]
    have huball := (MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R)).supportWithinDomain hdiv
    exact
      ⟨huball,
        AnalyticNumberTheory.General.ne_of_mem_divisorBallSupport_of_entire_value_ne_zero
          hF hdiv h0⟩
  change
    iteratedDeriv n (fun z => ∑ᶠ u, m u * logDeriv (Complex.canonicalFactor R u) z) 0 =
      ∑ᶠ u, m u * iteratedDeriv n (logDeriv (Complex.canonicalFactor R u)) 0
  exact iteratedDeriv_finsum_canonicalFactor_logDeriv hm hR hsupport n

/--
Inputs: a primitive nontrivial character, a positive finite Hadamard radius, and a derivative
order.
Claim: the centered iterated derivative of the canonical-factor logarithmic-derivative sum is a
divisor-multiplicity-weighted inverse-distance power sum plus a reflection correction sum.
Content: rewrite termwise differentiation on the finite support using the higher centered formula
for each canonical factor.
Role: expresses the zero term of the Hadamard factorization as the higher zero sum used in the
log-free density estimate.
-/
theorem iteratedDeriv_divisor_canonicalFactorSum_formula_at_zero {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) {R : ℝ} (hR : 0 < R) (n : ℕ) :
    iteratedDeriv n
        (fun z =>
          ∑ᶠ u : ℂ,
            ((-MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R) u : ℤ) : ℂ) *
              logDeriv (Complex.canonicalFactor R u) z)
        0 =
      ∑ᶠ u : ℂ,
        ((-MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R) u : ℤ) : ℂ) *
          (((-1 : ℂ) ^ n * (n.factorial : ℂ) *
              ((0 : ℂ) - (R : ℂ) ^ 2 / starRingEnd ℂ u) ^ (-1 - n : ℤ)) -
            (-1 : ℂ) ^ n * (n.factorial : ℂ) * ((0 : ℂ) - u) ^ (-1 - n : ℤ)) := by
  rw [iteratedDeriv_divisor_canonicalFactor_logDeriv_at_zero hF h0 hR n]
  apply finsum_congr
  intro u
  let c : ℂ := ((-MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R) u : ℤ) : ℂ)
  change
    c * iteratedDeriv n (logDeriv (Complex.canonicalFactor R u)) 0 =
      c *
        (((-1 : ℂ) ^ n * (n.factorial : ℂ) *
            ((0 : ℂ) - (R : ℂ) ^ 2 / starRingEnd ℂ u) ^ (-1 - n : ℤ)) -
          (-1 : ℂ) ^ n * (n.factorial : ℂ) * ((0 : ℂ) - u) ^ (-1 - n : ℤ))
  by_cases hc : c = 0
  · rw [hc, zero_mul, zero_mul]
  · have hdiv : MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R) u ≠ 0 := by
      intro hz
      apply hc
      dsimp [c]
      rw [hz]
      simp only [Int.cast_zero, neg_zero]
    have hu0 :=
      PseudoPrime.AnalyticNumberTheory.General.ne_of_mem_divisorBallSupport_of_entire_value_ne_zero
        hF hdiv h0
    have huball := (MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R)).supportWithinDomain hdiv
    rw [iteratedDeriv_logDeriv_canonicalFactor_at_zero huball hu0 n]

/--
Inputs: a primitive nontrivial character, a zero-free finite Hadamard boundary, a factorization
of positive radius, and a positive derivative order.
Claim: a higher centered derivative of the completed L-function's logarithmic derivative splits
into a divisor-weighted inverse-distance sum, a reflection correction, and an analytic-factor term.
Content: differentiate the centered Hadamard identity repeatedly near the center and substitute
the established formula for the canonical-factor sum.
Role: connects the finite-radius analytic remainder estimate to the Turán lower bound for a zero
power sum.
-/
theorem iteratedDeriv_ecanonicalDecomp_logDeriv_at_zero_of_entire {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (D : Complex.ECanonicalDecomp F g R) (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → F ρ ≠ 0) (n : ℕ) (hn : 0 < n) :
    iteratedDeriv n (logDeriv F) 0 =
      (∑ᶠ u : ℂ,
          ((-MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R) u : ℤ) : ℂ) *
            (((-1 : ℂ) ^ n * (n.factorial : ℂ) *
                ((0 : ℂ) - (R : ℂ) ^ 2 / starRingEnd ℂ u) ^ (-1 - n : ℤ)) -
              (-1 : ℂ) ^ n * (n.factorial : ℂ) * ((0 : ℂ) - u) ^ (-1 - n : ℤ))) +
        iteratedDeriv n (logDeriv g) 0 := by
  let m : ℂ → ℂ := fun u => ((-MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R) u : ℤ) : ℂ)
  let S : ℂ → ℂ := fun z => ∑ᶠ u : ℂ, m u * logDeriv (Complex.canonicalFactor R u) z
  let G : ℂ → ℂ := logDeriv g
  let c : ℂ := logDeriv F 0 - (S 0 + G 0)
  have hFanalytic : AnalyticAt ℂ F 0 := hF.analyticAt 0
  have h0closed : (0 : ℂ) ∈ Metric.closedBall 0 R := by
    rw [Metric.mem_closedBall, dist_self]
    exact hR.le
  have h0ne : F 0 ≠ 0 := h0
  have hanalyticClosed : AnalyticOnNhd ℂ F (Metric.closedBall (0 : ℂ) R) := fun z _ =>
    hF.analyticAt z
  have hfin := hanalyticClosed.meromorphicOn.divisor_ball_support_finite
  have hdfin :
    (Function.support fun u : ℂ => -MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R) u).Finite := by
    have hset :
      Function.support (fun u : ℂ => -MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R) u) =
        Function.support (MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R)) := by
      ext u
      simp only [Function.mem_support]
      constructor
      · intro h hz
        apply h
        rw [hz, neg_zero]
      · intro h hz
        apply h
        exact neg_eq_zero.mp hz
    rw [hset]
    exact hfin
  have hm : (Function.support m).Finite := by
    apply hdfin.subset
    intro u hu
    have hdiv : MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R) u ≠ 0 := by
      have hu' : m u ≠ 0 := by simpa only [Function.mem_support] using hu
      intro hz
      apply hu'
      change ((-MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R) u : ℤ) : ℂ) = 0
      rw [hz]
      simp only [Int.cast_zero, neg_zero]
    change u ∈ Function.support (fun v : ℂ => -MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R) v)
    change -MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R) u ≠ 0
    exact neg_ne_zero.mpr hdiv
  have hsupport : ∀ u ∈ Function.support m, u ∈ Metric.ball (0 : ℂ) R ∧ u ≠ 0 := by
    intro u hu
    have hdiv : MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R) u ≠ 0 := by
      have hu' : m u ≠ 0 := by simpa only [Function.mem_support] using hu
      intro hz
      apply hu'
      change ((-MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R) u : ℤ) : ℂ) = 0
      rw [hz]
      simp only [Int.cast_zero, neg_zero]
    have huball := (MeromorphicOn.divisor F (Metric.ball (0 : ℂ) R)).supportWithinDomain hdiv
    exact
      ⟨huball,
        AnalyticNumberTheory.General.ne_of_mem_divisorBallSupport_of_entire_value_ne_zero
          hF hdiv h0ne⟩
  have hSanalytic : AnalyticAt ℂ S 0 := by
    change AnalyticAt ℂ (fun z => ∑ᶠ u : ℂ, m u * logDeriv (Complex.canonicalFactor R u) z) 0
    apply analyticAt_finsum_const_mul hm
    intro u hu
    obtain ⟨huball, hu0⟩ := hsupport u hu
    have hcan : AnalyticAt ℂ (Complex.canonicalFactor R u) 0 :=
      Complex.analyticOnNhd_canonicalFactor R u 0 (Ne.symm hu0)
    have hcanne : Complex.canonicalFactor R u 0 ≠ 0 :=
      Complex.canonicalFactor_ne_zero huball h0closed (Ne.symm hu0)
    have hfun :
      logDeriv (Complex.canonicalFactor R u) = fun w =>
        deriv (Complex.canonicalFactor R u) w / Complex.canonicalFactor R u w := by
      funext w
      exact logDeriv_apply (Complex.canonicalFactor R u) w
    rw [hfun]
    exact hcan.deriv.div hcan hcanne
  have hGanalytic : AnalyticAt ℂ G 0 := by
    change AnalyticAt ℂ (logDeriv g) 0
    have hg : AnalyticAt ℂ g 0 := D.analyticOnNhd 0 h0closed
    have hgne : g 0 ≠ 0 := D.ne_zero 0 h0closed
    have hfun : logDeriv g = fun w => deriv g w / g w := by
      funext w
      exact logDeriv_apply g w
    rw [hfun]
    exact hg.deriv.div hg hgne
  have hEq : logDeriv F =ᶠ[nhds (0 : ℂ)] (fun z => S z + G z + c) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hR,
      hFanalytic.continuousAt.eventually_ne h0ne] with z hzball hzne
    have hzclosed : z ∈ Metric.closedBall (0 : ℂ) R := Metric.ball_subset_closedBall hzball
    have hcenter :=
      AnalyticNumberTheory.General.ecanonicalDecomp_centered_logDeriv_eq h0 hF hR D hzf
        hzclosed hzne
    change logDeriv F z = S z + G z + c
    linear_combination hcenter
  have hderivEq := hEq.iteratedDeriv n
  have hcenter := Filter.EventuallyEq.eq_of_nhds hderivEq
  have hadd := iteratedDeriv_add (n := n) hSanalytic.contDiffAt hGanalytic.contDiffAt
  calc
    iteratedDeriv n (logDeriv F) 0 = iteratedDeriv n (fun z => S z + G z + c) 0 := hcenter
    _ = iteratedDeriv n S 0 + iteratedDeriv n G 0 := by
      rw [show (fun z => S z + G z + c) = fun z => c + (S z + G z) from by
          funext z
          ring]
      rw [iteratedDeriv_const_add hn]
      change iteratedDeriv n (S + G) 0 = _
      exact hadd
    _ = _ := by rw [iteratedDeriv_divisor_canonicalFactorSum_formula_at_zero hF h0 hR n]

/--
Inputs: a primitive nontrivial character, a zero-free finite Hadamard boundary, a factorization
of positive radius, and a positive derivative order.
Claim: a higher centered derivative of the completed L-function's logarithmic derivative splits
into a divisor-weighted inverse-distance sum, a reflection correction, and an analytic-factor term.
Content: apply the centered identity for entire functions to the completed L-function.
Role: connects the finite-radius analytic remainder estimate to the Turán lower bound for a zero
power sum.
-/
theorem iteratedDeriv_ecanonicalDecomp_logDeriv_at_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) {R : ℝ} (hR : 0 < R)
    {g : ℂ → ℂ} (D : Complex.ECanonicalDecomp (DirichletCharacter.completedLFunction χ) g R)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → DirichletCharacter.completedLFunction χ ρ ≠ 0) (n : ℕ) (hn : 0 < n) :
    iteratedDeriv n (logDeriv (DirichletCharacter.completedLFunction χ)) 0 =
      (∑ᶠ u : ℂ,
          ((-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R)
                    u :
                ℤ) :
              ℂ) *
            (((-1 : ℂ) ^ n * (n.factorial : ℂ) *
                ((0 : ℂ) - (R : ℂ) ^ 2 / starRingEnd ℂ u) ^ (-1 - n : ℤ)) -
              (-1 : ℂ) ^ n * (n.factorial : ℂ) * ((0 : ℂ) - u) ^ (-1 - n : ℤ))) +
        iteratedDeriv n (logDeriv g) 0 := by
  have hF := DirichletCharacter.differentiable_completedLFunction hne
  have h0 := dirichletCompletedLFunction_zero_ne_zero_of_primitive hprimitive hne
  exact iteratedDeriv_ecanonicalDecomp_logDeriv_at_zero_of_entire hF h0 hR D hzf n hn

/--
Inputs: a primitive nontrivial character, a zero-free Hadamard boundary, a positive derivative
order, and a lower bound for a completed L-function logarithmic derivative.
Claim: the derivative lower bound gives a lower bound for the difference between the inverse-
distance power sums over disk zeros and their reflected corrections.
Content: combine the center identity for the canonical factorization with the existing Cauchy
bound for the analytic factor using the norm triangle inequality.
Role: connects local Turán detection to the zero sum from the global Hadamard factorization.
-/
theorem norm_ecanonicalDecomp_zero_difference_sum_lower_bound {N : ℕ} [NeZero N] (hN1 : 1 < N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {R : ℝ}
    (hR : 1 ≤ R) {g : ℂ → ℂ}
    (D : Complex.ECanonicalDecomp (DirichletCharacter.completedLFunction χ) g R)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → DirichletCharacter.completedLFunction χ ρ ≠ 0) (n : ℕ) (hn : 0 < n)
    (lower : ℝ)
    (hlower : lower ≤ ‖iteratedDeriv n (logDeriv (DirichletCharacter.completedLFunction χ)) 0‖) :
    (lower -
          n.factorial *
              (192 * (R / 4) *
                  |(4 * (N : ℝ) + 3) * (R + 3) * Real.log (R + 3) -
                        Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
                      1| /
                R ^ 2) /
            (R / 4) ^ n) /
        (n.factorial : ℝ) ≤
      ‖∑ᶠ u : ℂ,
          ((-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R)
                    u :
                ℤ) :
              ℂ) *
            (((0 : ℂ) - (R : ℂ) ^ 2 / starRingEnd ℂ u) ^ (-1 - n : ℤ) -
              ((0 : ℂ) - u) ^ (-1 - n : ℤ))‖ := by
  let a : ℂ := (-1 : ℂ) ^ n * (n.factorial : ℂ)
  let m : ℂ → ℂ := fun u =>
    ((-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) u :
        ℤ) :
      ℂ)
  let f : ℂ → ℂ := fun u => ((0 : ℂ) - (R : ℂ) ^ 2 / starRingEnd ℂ u) ^ (-1 - n : ℤ)
  let k : ℂ → ℂ := fun u => ((0 : ℂ) - u) ^ (-1 - n : ℤ)
  let S : ℂ := ∑ᶠ u : ℂ, m u * (f u - k u)
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num only) hR
  have hzeroFactor : (∑ᶠ u : ℂ, m u * (a * f u - a * k u)) = a * S := by
    calc
      _ = ∑ᶠ u : ℂ, a * (m u * (f u - k u)) := by
        apply finsum_congr
        intro u
        ring
      _ = _ := by rw [← mul_finsum]
  have hdecomp := iteratedDeriv_ecanonicalDecomp_logDeriv_at_zero hprimitive hne hRpos D hzf n hn
  change
    iteratedDeriv n (logDeriv (DirichletCharacter.completedLFunction χ)) 0 =
      (∑ᶠ u : ℂ, m u * (a * f u - a * k u)) + iteratedDeriv n (logDeriv g) 0 at hdecomp
  rw [hzeroFactor] at hdecomp
  have herror :=
    norm_iteratedDeriv_ecanonicalDecomp_logDeriv_le hN1 hprimitive hne hinv hR D hzf n hn
  have hnorm := norm_zero_sum_lower_bound_of_derivative_decomposition hdecomp hlower herror
  simpa only [S, m, f, k] using hnorm

/--
Inputs: a positive reflection radius, a point in the disk, and an inverse-power order.
Claim: the inverse-power norm at the reflected point is at most $R^{-(n+1)}$.
Content: show that the reflected point has norm at least $R$, then use monotonicity of reciprocal
powers.
Role: bounds reflected zero terms before applying Jensen's zero-count estimate.
-/
theorem norm_reflected_inverse_zpow_le {R : ℝ} {u : ℂ} (n : ℕ) (hR : 0 < R) (hu : ‖u‖ ≤ R) :
    ‖((0 : ℂ) - (R : ℂ) ^ 2 / starRingEnd ℂ u) ^ (-1 - (n : ℤ) : ℤ)‖ ≤ (1 / R) ^ (n + 1) := by
  by_cases hu0 : u = 0
  · subst u
    rw [show (-1 - (n : ℤ)) = Int.negSucc n by omega]
    simp only [map_zero, div_zero, sub_zero, zpow_negSucc]
    rw [zero_pow (Nat.succ_ne_zero n), inv_zero, norm_zero]
    exact pow_nonneg (le_of_lt (one_div_pos.mpr hR)) _
  · rw [zpow_neg_one_sub_nat_eq_inv_pow, norm_pow]
    have huPos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    have hpoint : ‖(0 : ℂ) - (R : ℂ) ^ 2 / starRingEnd ℂ u‖ = R ^ 2 / ‖u‖ := by
      rw [norm_sub_rev, sub_zero]
      change ‖(R : ℂ) ^ 2 / star u‖ = _
      rw [norm_div, norm_pow, Complex.norm_real, norm_star]
      simp only [Real.norm_eq_abs, abs_of_pos hR]
    have hpointLower : R ≤ ‖(0 : ℂ) - (R : ℂ) ^ 2 / starRingEnd ℂ u‖ := by
      rw [hpoint]
      exact (le_div_iff₀ huPos).2 (by nlinarith only [hR, hu])
    have hinv : ‖((0 : ℂ) - (R : ℂ) ^ 2 / starRingEnd ℂ u)⁻¹‖ ≤ 1 / R := by
      rw [norm_inv, inv_eq_one_div]
      exact one_div_le_one_div_of_le hR hpointLower
    exact pow_le_pow_left₀ (norm_nonneg _) hinv _

/--
Inputs: a primitive nontrivial character, a positive reflection radius, and a higher inverse-power
order.
Claim: the reflection correction sum over zeros of a completed L-function in a disk has an
explicit upper bound in terms of the function's growth bound.
Content: rewrite the finite divisor-support sum as a finite sum, bound each reflected term
uniformly, and apply Jensen's zero-count estimate.
Role: removes the reflection correction from the ordinary zero-power-sum lower bound obtained
from the canonical factorization.
-/
/-
Inputs: an entire function nonzero at the origin, a unit-circle boundary bound, and an inverse
power index.

Claim: the reflected inverse-power sum over zeros in the open unit disk is bounded by Jensen's
logarithmic zero count.

Proof: convert the finitely supported divisor sum to a finite sum, bound each reflected kernel by
one, and compare the open-disk multiplicity sum with the closed-disk Jensen count.

Role: supplies the correction-term estimate needed to transfer a canonical-factor remainder to a
local zero-factor remainder for scaled ordinary $L$ functions.
-/
theorem norm_reflection_sum_le_of_boundary_bound {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (h0 : F 0 ≠ 0) {M : ℝ} (hM : 1 ≤ M) (hbound : ∀ z ∈ Metric.sphere (0 : ℂ) 2, ‖F z‖ ≤ M)
    (n : ℕ) :
    ‖∑ᶠ u : ℂ,
          ((-MeromorphicOn.divisor F (Metric.ball (0 : ℂ) 1) u : ℤ) : ℂ) *
            ((0 : ℂ) - (1 : ℂ) ^ 2 / starRingEnd ℂ u) ^ (-1 - (n : ℤ) : ℤ)‖ ≤
      Real.log (M / ‖F 0‖) / Real.log 2 := by
  let d : ℂ → ℤ := MeromorphicOn.divisor F (Metric.ball (0 : ℂ) 1)
  let m : ℂ → ℂ := fun u => ((-d u : ℤ) : ℂ)
  let f : ℂ → ℂ := fun u => ((0 : ℂ) - (1 : ℂ) ^ 2 / starRingEnd ℂ u) ^ (-1 - (n : ℤ) : ℤ)
  have hanalyticClosed : AnalyticOnNhd ℂ F (Metric.closedBall (0 : ℂ) 1) := fun z _ =>
    hF.analyticAt z
  have hanalyticBall : AnalyticOnNhd ℂ F (Metric.ball (0 : ℂ) 1) := fun z _ => hF.analyticAt z
  have hfiniteD : d.support.Finite := by
    dsimp only [d]
    exact hanalyticClosed.meromorphicOn.divisor_ball_support_finite
  have hfiniteM : m.support.Finite := by
    apply hfiniteD.subset
    intro u hu
    simp only [Function.mem_support] at hu ⊢
    change ((-d u : ℤ) : ℂ) ≠ 0 at hu
    exact neg_ne_zero.mp (Int.cast_ne_zero.mp hu)
  let s := hfiniteM.toFinset
  have hsum : (∑ᶠ u : ℂ, m u * f u) = ∑ u ∈ s, m u * f u := by
    rw [finsum_eq_sum_of_support_subset _ (s := s)]
    intro u hu
    simp only [Function.mem_support] at hu
    have hm : m u ≠ 0 := by
      intro hz
      apply hu
      simp only [hz, zero_mul]
    exact (Set.Finite.mem_toFinset hfiniteM).mpr (by simpa only [Function.mem_support] using hm)
  have hnonneg : ∀ u, 0 ≤ d u := by
    intro u
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalyticBall u
  have hterm : ∀ u ∈ s, ‖m u * f u‖ ≤ (d u : ℝ) := by
    intro u hu
    have hm : m u ≠ 0 := by
      intro hz
      exact
        ((Set.Finite.mem_toFinset hfiniteM).mp (by simpa only [s] using hu))
          (by simpa only [Function.mem_support] using hz)
    have hd : d u ≠ 0 := by
      intro hz
      apply hm
      simp only [m, hz, Int.neg_zero, Int.cast_zero]
    have huBall := (MeromorphicOn.divisor F (Metric.ball (0 : ℂ) 1)).supportWithinDomain hd
    have huNorm : ‖u‖ < 1 := by
      rw [Metric.mem_ball, dist_zero_right] at huBall
      exact huBall
    have hcoef : ‖m u‖ = (d u : ℝ) := by
      dsimp only [m]
      rw [Complex.norm_intCast]
      simp only [Int.cast_neg, abs_neg]
      exact_mod_cast abs_of_nonneg (hnonneg u)
    have hkernel : ‖f u‖ ≤ 1 := by
      change ‖((0 : ℂ) - (1 : ℂ) ^ 2 / starRingEnd ℂ u) ^ (-1 - (n : ℤ) : ℤ)‖ ≤ 1
      calc
        ‖((0 : ℂ) - (1 : ℂ) ^ 2 / starRingEnd ℂ u) ^ (-1 - (n : ℤ) : ℤ)‖ ≤ (1 / 1) ^ (n + 1) :=
          norm_reflected_inverse_zpow_le n (by norm_num only) huNorm.le
        _ = 1 := by rw [one_div_one, one_pow]
    calc
      ‖m u * f u‖ = ‖m u‖ * ‖f u‖ := norm_mul _ _
      _ ≤ (d u : ℝ) * 1 := by
        rw [hcoef]
        exact mul_le_mul_of_nonneg_left hkernel (by exact_mod_cast hnonneg u)
      _ = (d u : ℝ) := by ring
  have hsumBound : ‖∑ᶠ u : ℂ, m u * f u‖ ≤ ∑ u ∈ s, (d u : ℝ) := by
    rw [hsum]
    calc
      ‖∑ u ∈ s, m u * f u‖ ≤ ∑ u ∈ s, ‖m u * f u‖ := norm_sum_le _ _
      _ ≤ ∑ u ∈ s, (d u : ℝ) :=
        Finset.sum_le_sum
          (by
            intro u hu
            exact hterm u hu)
  have hopenClosed : ∀ u ∈ s, d u = MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) 1) u := by
    intro u hu
    have hm : m u ≠ 0 := by exact (Set.Finite.mem_toFinset hfiniteM).mp (by simpa only [s] using hu)
    have hd : d u ≠ 0 := by
      intro hz
      apply hm
      simp only [m, hz, Int.neg_zero, Int.cast_zero]
    have huBall := (MeromorphicOn.divisor F (Metric.ball (0 : ℂ) 1)).supportWithinDomain hd
    have huNorm : ‖u‖ < 1 := by
      rw [Metric.mem_ball, dist_zero_right] at huBall
      exact huBall
    have huClosed : u ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact huNorm.le
    change
      MeromorphicOn.divisor F (Metric.ball (0 : ℂ) 1) u =
        MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) 1) u
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hanalyticBall huBall,
      MeromorphicOn.AnalyticOnNhd.divisor_apply hanalyticClosed huClosed]
  have hsumOpen :
    (∑ u ∈ s, (d u : ℝ)) ≤ ∑ᶠ u : ℂ, (MeromorphicOn.divisor F (Metric.closedBall 0 1) u : ℝ) := by
    calc
      (∑ u ∈ s, (d u : ℝ)) = ∑ u ∈ s, (MeromorphicOn.divisor F (Metric.closedBall 0 1) u : ℝ) := by
        apply Finset.sum_congr rfl
        intro u hu
        exact_mod_cast hopenClosed u hu
      _ ≤ _ := PseudoPrime.AnalyticNumberTheory.General.sum_divisor_le_finsum hF 1 s
  have hbound' : ∀ z ∈ Metric.sphere (0 : ℂ) (2 * 1), ‖F z‖ ≤ M := by
    intro z hz
    apply hbound z
    simpa only [mul_one] using hz
  have hJensen :=
    PseudoPrime.AnalyticNumberTheory.General.finsum_divisor_closedBall_le_of_sphere_bound hF h0
      (R := 1) (M := M) (by norm_num only) hM hbound'
  calc
    ‖∑ᶠ u : ℂ, m u * f u‖ ≤ ∑ u ∈ s, (d u : ℝ) := hsumBound
    _ ≤ Real.log (M / ‖F 0‖) / Real.log 2 := hsumOpen.trans hJensen

/-
Inputs: an entire function with an ECanonicalDecomp on the unit disk, a bound for the canonical
factor's logarithmic derivative, and bounds for the reflected inverse-power sums.
Claim: the analytic factor in the local linear zero factorization has a derivative bound equal to
the global canonical-factor bound plus the reflected-sum error.
Proof: compare the global and local logarithmic-derivative decompositions at the center; the
direct zero sums cancel, leaving only the reflected correction.
Role: transfers the Jensen reflection estimate to the zero-free analytic factor used by local
Turán detection.
-/
theorem norm_local_logDeriv_remainder_le_of_ecanonical_of_local_decomposition {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) {g : ℂ → ℂ} (D : Complex.ECanonicalDecomp F g 1) (h0 : F 0 ≠ 0)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = 1 → F ρ ≠ 0) (n : ℕ) (gLocal : ℂ → ℂ)
    (hLocalEq :
      iteratedDeriv n (logDeriv F) 0 =
        (∑ᶠ u : ℂ,
            ((MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |(1 : ℝ)|) u : ℤ) : ℂ) *
              ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (0 - u) ^ (-1 - (n : ℤ) : ℤ))) +
          iteratedDeriv n (logDeriv gLocal) 0)
    {K E : ℕ → ℝ} (hglobal : ∀ n, 0 < n → ‖iteratedDeriv n (logDeriv g) 0‖ ≤ K n)
    (hreflect :
      ∀ n : ℕ,
        ‖∑ᶠ u : ℂ,
              ((-MeromorphicOn.divisor F (Metric.ball (0 : ℂ) 1) u : ℤ) : ℂ) *
                ((0 : ℂ) - (1 : ℂ) ^ 2 / starRingEnd ℂ u) ^ (-1 - (n : ℤ) : ℤ)‖ ≤
          E n)
    (hn : 0 < n) : ‖iteratedDeriv n (logDeriv gLocal) 0‖ ≤ K n + n.factorial * E n := by
  let d : ℂ → ℤ := MeromorphicOn.divisor F (Metric.ball (0 : ℂ) 1)
  let m : ℂ → ℂ := fun u => ((-d u : ℤ) : ℂ)
  let ref : ℂ → ℂ := fun u => ((0 : ℂ) - (1 : ℂ) ^ 2 / starRingEnd ℂ u) ^ (-1 - (n : ℤ) : ℤ)
  let direct : ℂ → ℂ := fun u => ((0 : ℂ) - u) ^ (-1 - (n : ℤ) : ℤ)
  let a : ℂ := (-1 : ℂ) ^ n * (n.factorial : ℂ)
  have habs : |(1 : ℝ)| = 1 := abs_of_pos (by norm_num only)
  have hLocalEq0 := hLocalEq
  rw [habs] at hLocalEq0
  have hLocalEq' :
    iteratedDeriv n (logDeriv F) 0 =
      (∑ᶠ u : ℂ, ((d u : ℤ) : ℂ) * (a * direct u)) + iteratedDeriv n (logDeriv gLocal) 0 := by
    simpa only [d, a, direct] using hLocalEq0
  have hGlobalEq :=
    iteratedDeriv_ecanonicalDecomp_logDeriv_at_zero_of_entire hF h0 (R := 1)
      (by norm_num only : (0 : ℝ) < 1) D hzf n hn
  have hcastOne : ((1 : ℝ) : ℂ) = (1 : ℂ) := Complex.ofReal_one
  rw [hcastOne] at hGlobalEq
  have hGlobalEq' :
    iteratedDeriv n (logDeriv F) 0 =
      (∑ᶠ u : ℂ, m u * (a * (ref u - direct u))) + iteratedDeriv n (logDeriv g) 0 := by
    calc
      iteratedDeriv n (logDeriv F) 0 =
          (∑ᶠ u : ℂ,
              m u *
                (((-1 : ℂ) ^ n * (n.factorial : ℂ) *
                    ((0 : ℂ) - (1 : ℂ) ^ 2 / starRingEnd ℂ u) ^ (-1 - (n : ℤ) : ℤ)) -
                  (-1 : ℂ) ^ n * (n.factorial : ℂ) * ((0 : ℂ) - u) ^ (-1 - (n : ℤ) : ℤ))) +
            iteratedDeriv n (logDeriv g) 0 :=
        by simpa only [m, d, Int.cast_neg] using hGlobalEq
      _ = _ := by
        congr 1
        apply finsum_congr
        intro u
        dsimp only [m, d, ref, direct, a]
        ring
  have hfiniteD : d.support.Finite := by
    have hAn : AnalyticOnNhd ℂ F (Metric.closedBall (0 : ℂ) 1) := fun z _ => hF.analyticAt z
    dsimp only [d]
    exact hAn.meromorphicOn.divisor_ball_support_finite
  let s := hfiniteD.toFinset
  have hsum (f : ℂ → ℂ) : (∑ᶠ u : ℂ, m u * f u) = ∑ u ∈ s, m u * f u := by
    rw [finsum_eq_sum_of_support_subset _ (s := s)]
    intro u hu
    simp only [Function.mem_support] at hu
    have hmu : m u ≠ 0 := by
      intro hm
      apply hu
      simp only [hm, zero_mul]
    have hnegd : -d u ≠ 0 := by
      intro hz
      apply hmu
      simp only [m, hz, Int.cast_zero]
    have hd : d u ≠ 0 := by
      intro hz
      apply hnegd
      rw [hz]
      simp only [neg_zero]
    exact (Set.Finite.mem_toFinset hfiniteD).mpr (by simpa only [Function.mem_support] using hd)
  have hsumD (f : ℂ → ℂ) : (∑ᶠ u : ℂ, ((d u : ℤ) : ℂ) * f u) = ∑ u ∈ s, ((d u : ℤ) : ℂ) * f u := by
    rw [finsum_eq_sum_of_support_subset _ (s := s)]
    intro u hu
    simp only [Function.mem_support] at hu
    have hd : d u ≠ 0 := by
      intro hz
      apply hu
      simp only [hz, Int.cast_zero, zero_mul]
    exact (Set.Finite.mem_toFinset hfiniteD).mpr (by simpa only [Function.mem_support] using hd)
  have hGlobalSplit :
    (∑ᶠ u : ℂ, m u * (a * (ref u - direct u))) =
      (∑ᶠ u : ℂ, m u * (a * ref u)) + (∑ᶠ u : ℂ, ((d u : ℤ) : ℂ) * (a * direct u)) := by
    rw [hsum, hsum, hsumD]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    dsimp only [m]
    simp only [Int.cast_neg]
    ring
  have hRemEq :
    iteratedDeriv n (logDeriv gLocal) 0 =
      iteratedDeriv n (logDeriv g) 0 + ∑ᶠ u : ℂ, m u * (a * ref u) := by
    rw [hGlobalEq', hGlobalSplit] at hLocalEq'
    have hc :
      (∑ᶠ u : ℂ, ((d u : ℤ) : ℂ) * (a * direct u)) +
          ((∑ᶠ u : ℂ, m u * (a * ref u)) + iteratedDeriv n (logDeriv g) 0) =
        (∑ᶠ u : ℂ, ((d u : ℤ) : ℂ) * (a * direct u)) + iteratedDeriv n (logDeriv gLocal) 0 := by
      calc
        _ =
            (∑ᶠ u : ℂ, m u * (a * ref u)) + (∑ᶠ u : ℂ, ((d u : ℤ) : ℂ) * (a * direct u)) +
              iteratedDeriv n (logDeriv g) 0 :=
          by ac_rfl
        _ = _ := hLocalEq'
    have hc' := add_left_cancel hc
    calc
      iteratedDeriv n (logDeriv gLocal) 0 =
          (∑ᶠ u : ℂ, m u * (a * ref u)) + iteratedDeriv n (logDeriv g) 0 :=
        hc'.symm
      _ = _ := by ac_rfl
  have hscale : (n.factorial : ℝ) * ‖∑ᶠ u : ℂ, m u * ref u‖ ≤ (n.factorial : ℝ) * E n := by
    exact mul_le_mul_of_nonneg_left (hreflect n) (by positivity)
  have hfac : ‖a‖ = (n.factorial : ℝ) := by
    dsimp only [a]
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast, one_mul]
  have hfactor : ‖∑ᶠ u : ℂ, m u * (a * ref u)‖ = (n.factorial : ℝ) * ‖∑ᶠ u : ℂ, m u * ref u‖ := by
    rw [show (fun u : ℂ => m u * (a * ref u)) = fun u => a * (m u * ref u)
        by
        funext u
        ring,
      ← mul_finsum, norm_mul, hfac]
  have hnorm :
    ‖iteratedDeriv n (logDeriv gLocal) 0‖ ≤
      ‖iteratedDeriv n (logDeriv g) 0‖ + ‖∑ᶠ u : ℂ, m u * (a * ref u)‖ := by
    rw [hRemEq]
    exact norm_add_le _ _
  calc
    ‖iteratedDeriv n (logDeriv gLocal) 0‖ ≤
        ‖iteratedDeriv n (logDeriv g) 0‖ + ‖∑ᶠ u : ℂ, m u * (a * ref u)‖ :=
      hnorm
    _ = ‖iteratedDeriv n (logDeriv g) 0‖ + (n.factorial : ℝ) * ‖∑ᶠ u : ℂ, m u * ref u‖ := by
      rw [hfactor]
    _ ≤ K n + (n.factorial : ℝ) * E n := by exact add_le_add (hglobal n hn) hscale

/--
Inputs: a zero-factor decomposition on the disk, together with derivative bounds for the global
canonical factor and the reflection sum.
Claim: there is an analytic factor whose higher logarithmic derivatives are bounded by the sum of
the global estimate and the reflection error.
Content: construct the local factorization and apply the estimate for an arbitrary local
factorization.
Role: provides an existential error bound for local Turán detection.
-/
theorem norm_local_logDeriv_remainder_le_of_ecanonical {F : ℂ → ℂ}
    (hFglobal : AnalyticOnNhd ℂ F Set.univ) (hF : Differentiable ℂ F) {g : ℂ → ℂ}
    (D : Complex.ECanonicalDecomp F g 1) (h0 : F 0 ≠ 0) (hzf : ∀ ρ : ℂ, ‖ρ‖ = 1 → F ρ ≠ 0)
    {K E : ℕ → ℝ} (hglobal : ∀ n, 0 < n → ‖iteratedDeriv n (logDeriv g) 0‖ ≤ K n)
    (hreflect :
      ∀ n : ℕ,
        ‖∑ᶠ u : ℂ,
              ((-MeromorphicOn.divisor F (Metric.ball (0 : ℂ) 1) u : ℤ) : ℂ) *
                ((0 : ℂ) - (1 : ℂ) ^ 2 / starRingEnd ℂ u) ^ (-1 - (n : ℤ) : ℤ)‖ ≤
          E n)
    (n : ℕ) (hn : 0 < n) :
    ∃ gLocal : ℂ → ℂ,
      AnalyticOnNhd ℂ gLocal (Metric.ball (0 : ℂ) 1) ∧
        (∀ u : Metric.ball (0 : ℂ) 1, gLocal u ≠ 0) ∧
        ‖iteratedDeriv n (logDeriv gLocal) 0‖ ≤ K n + n.factorial * E n := by
  obtain ⟨gLocal, hLocal, hLocalNe, hLocalEq⟩ :=
    exists_analytic_local_iterated_logDeriv_decomposition_at_center hFglobal 0 h0 (R := 1)
      (by norm_num only : (0 : ℝ) < |(1 : ℝ)|) h0 n
  refine ⟨gLocal, ?_, ?_, ?_⟩
  · simpa only [abs_of_pos (by norm_num only : (0 : ℝ) < 1)] using hLocal
  · intro u
    have hu : u.1 ∈ Metric.ball (0 : ℂ) |(1 : ℝ)| := by
      simpa only [abs_of_pos (by norm_num only : (0 : ℝ) < 1)] using u.2
    exact hLocalNe ⟨u.1, hu⟩
  · exact
      norm_local_logDeriv_remainder_le_of_ecanonical_of_local_decomposition hF D h0 hzf n gLocal
        hLocalEq hglobal hreflect hn

/--
Inputs: the center identity for the local Turán decomposition on the unit disk.
Claim: the identity can be rewritten as a local factorization with the zero coefficients multiplied
directly by inverse integer powers.
Content: use the inverse-power identity and factor a constant out of the `finsum`.
Role: enables the global reflection-sum bound to be applied to the analytic factor in the local
Turán decomposition.
-/
theorem iteratedDeriv_local_equation_of_turan_decomposition_at_zero {F : ℂ → ℂ} (g : ℂ → ℂ)
    (M l : ℕ)
    (hcenter :
      iteratedDeriv (M + l) (logDeriv F) 0 =
        ((-1 : ℂ) ^ (M + l) * ((M + l).factorial : ℂ)) *
            (∑ᶠ u : ℂ,
              ((MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |(1 : ℝ)|) u : ℤ) : ℂ) *
                (0 - u)⁻¹ ^ (M + 1 + l)) +
          iteratedDeriv (M + l) (logDeriv g) 0) :
    iteratedDeriv (M + l) (logDeriv F) 0 =
      (∑ᶠ u : ℂ,
          ((MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |(1 : ℝ)|) u : ℤ) : ℂ) *
            (((-1 : ℂ) ^ (M + l) * ((M + l).factorial : ℂ)) * (0 - u) ^ (-1 - (M + l : ℕ) : ℤ))) +
        iteratedDeriv (M + l) (logDeriv g) 0 := by
  let d : ℂ → ℤ := MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |(1 : ℝ)|)
  let m : ℂ → ℂ := fun u => (d u : ℂ)
  let a : ℂ := (-1 : ℂ) ^ (M + l) * ((M + l).factorial : ℂ)
  have hpower :
    (∑ᶠ u : ℂ, m u * (0 - u) ^ (-1 - (M + l : ℕ) : ℤ)) =
      ∑ᶠ u : ℂ, m u * (0 - u)⁻¹ ^ (M + 1 + l) := by
    apply finsum_congr
    intro u
    rw [zpow_neg_one_sub_add_eq_inv_pow]
  have hfactor :
    (∑ᶠ u : ℂ, m u * (a * (0 - u) ^ (-1 - (M + l : ℕ) : ℤ))) =
      a * (∑ᶠ u : ℂ, m u * (0 - u) ^ (-1 - (M + l : ℕ) : ℤ)) := by
    calc
      _ = ∑ᶠ u : ℂ, a * (m u * (0 - u) ^ (-1 - (M + l : ℕ) : ℤ)) := by
        apply finsum_congr
        intro u
        ring
      _ = _ := (mul_finsum _ _).symm
  calc
    _ = a * (∑ᶠ u : ℂ, m u * (0 - u)⁻¹ ^ (M + 1 + l)) + iteratedDeriv (M + l) (logDeriv g) 0 := by
      dsimp only [a, m, d]
      exact hcenter
    _ =
        a * (∑ᶠ u : ℂ, m u * (0 - u) ^ (-1 - (M + l : ℕ) : ℤ)) +
          iteratedDeriv (M + l) (logDeriv g) 0 :=
      by rw [← hpower]
    _ = _ := by rw [← hfactor]

theorem norm_ecanonicalDecomp_reflection_sum_le {N : ℕ} [NeZero N] (hN1 : 1 < N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {R : ℝ}
    (hR : 0 < R) (n : ℕ) :
    ‖∑ᶠ u : ℂ,
          ((-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R)
                    u :
                ℤ) :
              ℂ) *
            ((0 : ℂ) - (R : ℂ) ^ 2 / starRingEnd ℂ u) ^ (-1 - (n : ℤ) : ℤ)‖ ≤
      (1 / R) ^ (n + 1) *
        (Real.log
            (max 1
                (PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedLFunctionBallBound N
                  (2 * R)) /
              ‖DirichletCharacter.completedLFunction χ 0‖) /
          Real.log 2) := by
  let F := DirichletCharacter.completedLFunction χ
  let U := Metric.ball (0 : ℂ) R
  let d := MeromorphicOn.divisor F U
  let m : ℂ → ℂ := fun u => ((-d u : ℤ) : ℂ)
  let f : ℂ → ℂ := fun u => ((0 : ℂ) - (R : ℂ) ^ 2 / starRingEnd ℂ u) ^ (-1 - (n : ℤ) : ℤ)
  have hfiniteD0 := completedLFunction_local_zero_support_finite χ hne 0 R
  have hfiniteD : d.support.Finite := by
    dsimp only [d, F, U]
    rw [← abs_of_pos hR]
    exact hfiniteD0
  have hfiniteM : m.support.Finite := by
    apply hfiniteD.subset
    intro u hu
    simp only [Function.mem_support] at hu ⊢
    change ((-d u : ℤ) : ℂ) ≠ 0 at hu
    exact neg_ne_zero.mp (Int.cast_ne_zero.mp hu)
  let s := hfiniteM.toFinset
  have hsum : (∑ᶠ u : ℂ, m u * f u) = ∑ u ∈ s, m u * f u := by
    rw [finsum_eq_sum_of_support_subset _ (s := s)]
    intro u hu
    simp only [Function.mem_support] at hu
    have hmu : m u ≠ 0 := by
      intro hz
      apply hu
      simp only [hz, zero_mul]
    exact (Set.Finite.mem_toFinset hfiniteM).mpr (by simpa only [Function.mem_support] using hmu)
  have hAnBall : AnalyticOnNhd ℂ F U := by
    intro z hz
    exact (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hdNonneg : ∀ u, 0 ≤ d u := by
    intro u
    exact_mod_cast (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAnBall u)
  have hterm : ∀ u ∈ s, ‖m u * f u‖ ≤ (d u : ℝ) * (1 / R) ^ (n + 1) := by
    intro u hu
    have hum : m u ≠ 0 := by
      intro h
      exact
        ((Set.Finite.mem_toFinset hfiniteM).mp (by simpa only [s] using hu))
          (by simpa only [Function.mem_support] using h)
    have huDneq : d u ≠ 0 := by
      intro h
      apply hum
      simp only [m, h, Int.neg_zero, Int.cast_zero]
    have huBall : u ∈ U := d.supportWithinDomain huDneq
    have huNorm : ‖u‖ ≤ R := by
      rw [Metric.mem_ball, dist_zero_right] at huBall
      exact le_of_lt huBall
    have hcoef : ‖m u‖ = (d u : ℝ) := by
      dsimp only [m]
      rw [Complex.norm_intCast]
      simp only [Int.cast_neg, abs_neg]
      exact_mod_cast abs_of_nonneg (hdNonneg u)
    calc
      ‖m u * f u‖ = ‖m u‖ * ‖f u‖ := norm_mul _ _
      _ ≤ (d u : ℝ) * (1 / R) ^ (n + 1) := by
        rw [hcoef]
        exact
          mul_le_mul_of_nonneg_left (norm_reflected_inverse_zpow_le n hR huNorm)
            (by exact_mod_cast hdNonneg u)
  have hsumBound : ‖∑ᶠ u : ℂ, m u * f u‖ ≤ (∑ u ∈ s, (d u : ℝ)) * (1 / R) ^ (n + 1) := by
    rw [hsum]
    calc
      ‖∑ u ∈ s, m u * f u‖ ≤ ∑ u ∈ s, ‖m u * f u‖ := norm_sum_le _ _
      _ ≤ ∑ u ∈ s, (d u : ℝ) * (1 / R) ^ (n + 1) :=
        Finset.sum_le_sum
          (by
            intro u hu
            exact hterm u hu)
      _ = _ := by rw [Finset.sum_mul]
  have hsumD : (∑ u ∈ s, d u : ℤ) = ∑ᶠ u : ℂ, d u := by
    symm
    apply finsum_eq_finsetSum_of_support_subset
    intro u hu
    simp only [Function.mem_support] at hu
    have hm : m u ≠ 0 := by
      simp only [m]
      exact_mod_cast neg_ne_zero.mpr hu
    exact (Set.Finite.mem_toFinset hfiniteM).mpr (by simpa only [Function.mem_support] using hm)
  have hsumDcast : ((∑ u ∈ s, d u : ℤ) : ℝ) = ∑ u ∈ s, (d u : ℝ) := by
    push_cast
    ring
  have hJensen :=
    PseudoPrime.AnalyticNumberTheory.DirichletLFunction.finsum_divisor_ball_completedLFunction_le
      hN1 hprimitive hne hinv hR
  rw [← hsumDcast, hsumD] at hsumBound
  calc
    ‖∑ᶠ u : ℂ, m u * f u‖ ≤ (↑(∑ᶠ u : ℂ, d u) : ℝ) * (1 / R) ^ (n + 1) := hsumBound
    _ ≤
        (Real.log
              (max 1
                  (PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedLFunctionBallBound N
                    (2 * R)) /
                ‖DirichletCharacter.completedLFunction χ 0‖) /
            Real.log 2) *
          (1 / R) ^ (n + 1) :=
      mul_le_mul_of_nonneg_right hJensen (pow_nonneg (le_of_lt (one_div_pos.mpr hR)) _)
    _ = _ := by ring

/--
Inputs: the hypotheses of `norm_ecanonicalDecomp_zero_difference_sum_lower_bound` and an upper
bound for the reflection correction sum.
Claim: the inverse-distance power sum over disk zeros has a lower bound after subtracting the
derivative error and reflection correction.
Content: split the difference sum over the finite divisor support and remove the reflection term
using the triangle inequality.
Role: converts the global Hadamard identity into the ordinary zero-detection power sum.
-/
theorem norm_ecanonicalDecomp_direct_zero_sum_lower_bound {N : ℕ} [NeZero N] (hN1 : 1 < N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {R : ℝ}
    (hR : 1 ≤ R) {g : ℂ → ℂ}
    (D : Complex.ECanonicalDecomp (DirichletCharacter.completedLFunction χ) g R)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → DirichletCharacter.completedLFunction χ ρ ≠ 0) (n : ℕ) (hn : 0 < n)
    (lower reflectionBound : ℝ)
    (hlower : lower ≤ ‖iteratedDeriv n (logDeriv (DirichletCharacter.completedLFunction χ)) 0‖)
    (hreflection :
      ‖∑ᶠ u : ℂ,
            ((-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                      (Metric.ball (0 : ℂ) R) u :
                  ℤ) :
                ℂ) *
              ((0 : ℂ) - (R : ℂ) ^ 2 / starRingEnd ℂ u) ^ (-1 - n : ℤ)‖ ≤
        reflectionBound) :
    (lower -
            n.factorial *
                (192 * (R / 4) *
                    |(4 * (N : ℝ) + 3) * (R + 3) * Real.log (R + 3) -
                          Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
                        1| /
                  R ^ 2) /
              (R / 4) ^ n) /
          (n.factorial : ℝ) -
        reflectionBound ≤
      ‖∑ᶠ u : ℂ,
          ((-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R)
                    u :
                ℤ) :
              ℂ) *
            ((0 : ℂ) - u) ^ (-1 - n : ℤ)‖ := by
  let m : ℂ → ℂ := fun u =>
    ((-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) u :
        ℤ) :
      ℂ)
  let f : ℂ → ℂ := fun u => ((0 : ℂ) - (R : ℂ) ^ 2 / starRingEnd ℂ u) ^ (-1 - n : ℤ)
  let k : ℂ → ℂ := fun u => ((0 : ℂ) - u) ^ (-1 - n : ℤ)
  let Sdiff : ℂ := ∑ᶠ u : ℂ, m u * (f u - k u)
  let Sreflect : ℂ := ∑ᶠ u : ℂ, m u * f u
  let Sdirect : ℂ := ∑ᶠ u : ℂ, m u * k u
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num only) hR
  have hfiniteD := completedLFunction_local_zero_support_finite χ hne 0 R
  have hfiniteD' :
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.ball (0 : ℂ) R)).support.Finite := by
    rw [abs_of_pos hRpos] at hfiniteD
    exact hfiniteD
  have hfiniteM : m.support.Finite := by
    apply hfiniteD'.subset
    intro u hu
    simp only [Function.mem_support] at hu ⊢
    change
      ((-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R) u :
            ℤ) :
          ℂ) ≠
        0 at hu
    exact neg_ne_zero.mp (Int.cast_ne_zero.mp hu)
  let s := hfiniteM.toFinset
  have hsum (v : ℂ → ℂ) : (∑ᶠ u : ℂ, m u * v u) = ∑ u ∈ s, m u * v u := by
    rw [finsum_eq_sum_of_support_subset _ (s := s)]
    intro u hu
    simp only [Function.mem_support] at hu
    have hmu : m u ≠ 0 := by
      intro hz
      apply hu
      simp only [hz, zero_mul]
    exact (Set.Finite.mem_toFinset hfiniteM).mpr (by simpa only [Function.mem_support] using hmu)
  have hsplit : Sdiff = Sreflect - Sdirect := by
    dsimp only [Sdiff, Sreflect, Sdirect]
    rw [hsum (fun u => f u - k u), hsum f, hsum k]
    calc
      (∑ u ∈ s, m u * (f u - k u)) = ∑ u ∈ s, (m u * f u - m u * k u) := by
        apply Finset.sum_congr rfl
        intro u hu
        ring
      _ = (∑ u ∈ s, m u * f u) - ∑ u ∈ s, m u * k u := by rw [Finset.sum_sub_distrib]
  have hdiff :=
    norm_ecanonicalDecomp_zero_difference_sum_lower_bound hN1 hprimitive hne hinv hR D hzf n hn
      lower hlower
  have hdiff' :
    (lower -
          n.factorial *
              (192 * (R / 4) *
                  |(4 * (N : ℝ) + 3) * (R + 3) * Real.log (R + 3) -
                        Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
                      1| /
                R ^ 2) /
            (R / 4) ^ n) /
        (n.factorial : ℝ) ≤
      ‖Sdiff‖ := by
    simpa only [Sdiff, m, f, k] using hdiff
  rw [hsplit] at hdiff'
  have htriangle : ‖Sreflect - Sdirect‖ ≤ ‖Sreflect‖ + ‖Sdirect‖ := norm_sub_le Sreflect Sdirect
  linarith only [hdiff', hreflection, htriangle]

/--
Inputs: a canonical Hadamard factorization, a zero-free boundary circle, and a lower bound for a
higher derivative at the center.
Claim: Jensen's zero-count estimate gives an explicit lower bound for the inverse-distance power
sum over ordinary zeros in the disk.
Content: bound the reflection correction with `norm_ecanonicalDecomp_reflection_sum_le` and apply
the theorem that removes the reflected terms from the difference sum.
Role: connects the derivative lower bound from local zero detection to the ordinary zero sum.
-/
theorem norm_ecanonicalDecomp_direct_zero_sum_lower_bound_of_jensen {N : ℕ} [NeZero N] (hN1 : 1 < N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {R : ℝ}
    (hR : 1 ≤ R) {g : ℂ → ℂ}
    (D : Complex.ECanonicalDecomp (DirichletCharacter.completedLFunction χ) g R)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → DirichletCharacter.completedLFunction χ ρ ≠ 0) (n : ℕ) (hn : 0 < n)
    (lower : ℝ)
    (hlower : lower ≤ ‖iteratedDeriv n (logDeriv (DirichletCharacter.completedLFunction χ)) 0‖) :
    (lower -
            n.factorial *
                (192 * (R / 4) *
                    |(4 * (N : ℝ) + 3) * (R + 3) * Real.log (R + 3) -
                          Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
                        1| /
                  R ^ 2) /
              (R / 4) ^ n) /
          (n.factorial : ℝ) -
        (1 / R) ^ (n + 1) *
          (Real.log
              (max 1
                  (PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedLFunctionBallBound N
                    (2 * R)) /
                ‖DirichletCharacter.completedLFunction χ 0‖) /
            Real.log 2) ≤
      ‖∑ᶠ u : ℂ,
          ((-MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball (0 : ℂ) R)
                    u :
                ℤ) :
              ℂ) *
            ((0 : ℂ) - u) ^ (-1 - n : ℤ)‖ := by
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) hR
  exact
    norm_ecanonicalDecomp_direct_zero_sum_lower_bound hN1 hprimitive hne hinv hR D hzf n hn lower
      ((1 / R) ^ (n + 1) *
        (Real.log
            (max 1
                (PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedLFunctionBallBound N
                  (2 * R)) /
              ‖DirichletCharacter.completedLFunction χ 0‖) /
          Real.log 2))
      hlower
      (by
        simpa only [show (-1 - n : ℤ) = -1 - (n : ℤ) by rfl] using
          norm_ecanonicalDecomp_reflection_sum_le hN1 hprimitive hne hinv hRpos n)

/--
Inputs: an entire function nonzero at the center, a zero-free Hadamard factorization on the disk
of radius $R$, an exponential boundary bound, and a positive derivative order.
Claim: the higher centered derivative of the analytic factor's logarithmic derivative has an
explicit bound from the boundary estimate.
Content: use a Borel-Carathéodory estimate to bound the centered difference on the disk of radius
$R/2$, then apply Cauchy's estimate at radius $R/4$.
Role: supplies a higher-derivative analytic remainder bound that also applies to translated
completed L-functions.
-/
theorem norm_iteratedDeriv_ecanonicalDecomp_logDeriv_le_of_boundary_bound {F g : ℂ → ℂ}
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) {R M : ℝ} (hR : 1 ≤ R)
    (D : Complex.ECanonicalDecomp F g R) (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → F ρ ≠ 0)
    (hbound : ∀ ρ : ℂ, ‖ρ‖ = R → ‖F ρ‖ ≤ Real.exp M) (n : ℕ) (hn : 0 < n) :
    ‖iteratedDeriv n (logDeriv g) 0‖ ≤
      n.factorial * (192 * (R / 4) * (M - Real.log ‖F 0‖ + 1) / R ^ 2) / (R / 4) ^ n := by
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) hR
  have hrpos : 0 < R / 4 := div_pos hRpos (by norm_num only)
  have hrle : R / 4 ≤ R := by linarith only [hR]
  have hsubset : Metric.closedBall (0 : ℂ) (R / 4) ⊆ Metric.closedBall 0 R := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz ⊢
    exact hz.trans hrle
  have hg : AnalyticOnNhd ℂ g (Metric.closedBall 0 (R / 4)) := by
    intro z hz
    exact D.analyticOnNhd z (hsubset hz)
  have hgn : ∀ z ∈ Metric.closedBall 0 (R / 4), g z ≠ 0 := by
    intro z hz
    exact D.ne_zero z (hsubset hz)
  have hloganalytic : AnalyticOnNhd ℂ (logDeriv g) (Metric.closedBall 0 (R / 4)) := by
    intro z hz
    have hfun : logDeriv g = fun w => deriv g w / g w := by
      funext w
      exact logDeriv_apply g w
    rw [hfun]
    exact (hg z hz).deriv.div (hg z hz) (hgn z hz)
  let A : ℝ := M - Real.log ‖F 0‖ + 1
  have hA : 0 ≤ A := by
    have h0closed : (0 : ℂ) ∈ Metric.closedBall 0 R := by
      rw [Metric.mem_closedBall, dist_self]
      exact hRpos.le
    have hosc :=
      PseudoPrime.AnalyticNumberTheory.General.canonical_factor_log_oscillation_le hF h0 hRpos D hzf
        hbound h0closed
    dsimp only [A]
    linarith only [hosc]
  have hden : 0 < R ^ 2 := pow_pos hRpos 2
  have hC :
    ∀ z ∈ Metric.closedBall (0 : ℂ) (R / 4),
      ‖logDeriv g z - logDeriv g 0‖ ≤ 192 * (R / 4) * A / R ^ 2 := by
    intro z hz
    have hzNorm : ‖z‖ ≤ R / 4 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    have hzHalf : ‖z‖ ≤ R / 2 := by linarith only [hzNorm, hR]
    have hv :=
      PseudoPrime.AnalyticNumberTheory.General.norm_centered_logDeriv_canonical_factor_le hF h0 hR D
        hzf hbound hzHalf
    calc
      ‖logDeriv g z - logDeriv g 0‖ ≤ 192 * ‖z‖ * A / R ^ 2 := hv
      _ ≤ 192 * (R / 4) * A / R ^ 2 := by
        apply (div_le_div_iff_of_pos_right hden).2
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzNorm (by positivity)) hA
  exact norm_iteratedDeriv_le_of_forall_ball_norm_sub_center_le n hn hrpos hloganalytic hC

/--
Inputs: boundary bounds on the circles of radii 1 and 2, a canonical factorization on the unit
disk, a nonzero center value, and a radius-2 bound at least 1.
Claim: the higher derivatives of the zero-free analytic factor in the local linear zero
factorization have an explicit bound from both boundary estimates.
Content: use the radius-1 bound for the Cauchy estimate of the global canonical factor and the
radius-2 bound with Jensen's estimate for the reflection correction.
Role: supplies the analytic-factor error required by local Turán detection.
-/
theorem exists_local_logDeriv_remainder_le_of_two_sphere_bounds {F g : ℂ → ℂ}
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (D : Complex.ECanonicalDecomp F g 1)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = 1 → F ρ ≠ 0) {M₁ M₂ : ℝ} (hM₂ : 1 ≤ M₂)
    (hbound₁ : ∀ ρ : ℂ, ‖ρ‖ = 1 → ‖F ρ‖ ≤ Real.exp M₁)
    (hbound₂ : ∀ z ∈ Metric.sphere (0 : ℂ) 2, ‖F z‖ ≤ M₂) (n : ℕ) (hn : 0 < n) :
    ∃ gLocal : ℂ → ℂ,
      AnalyticOnNhd ℂ gLocal (Metric.ball (0 : ℂ) 1) ∧
        (∀ u : Metric.ball (0 : ℂ) 1, gLocal u ≠ 0) ∧
        ‖iteratedDeriv n (logDeriv gLocal) 0‖ ≤
          n.factorial * (192 * (1 / 4) * (M₁ - Real.log ‖F 0‖ + 1) / 1 ^ 2) / (1 / 4) ^ n +
            n.factorial * (Real.log (M₂ / ‖F 0‖) / Real.log 2) := by
  let K : ℕ → ℝ := fun k =>
    k.factorial * (192 * (1 / 4) * (M₁ - Real.log ‖F 0‖ + 1) / 1 ^ 2) / (1 / 4) ^ k
  have hFglobal : AnalyticOnNhd ℂ F Set.univ := fun z _ => hF.analyticAt z
  have hglobal : ∀ k, 0 < k → ‖iteratedDeriv k (logDeriv g) 0‖ ≤ K k := by
    intro k hk
    simpa only [K] using
      norm_iteratedDeriv_ecanonicalDecomp_logDeriv_le_of_boundary_bound hF h0
        (by norm_num only : (1 : ℝ) ≤ 1) D hzf hbound₁ k hk
  have hreflect :
    ∀ k : ℕ,
      ‖∑ᶠ u : ℂ,
            ((-MeromorphicOn.divisor F (Metric.ball (0 : ℂ) 1) u : ℤ) : ℂ) *
              ((0 : ℂ) - (1 : ℂ) ^ 2 / starRingEnd ℂ u) ^ (-1 - (k : ℤ) : ℤ)‖ ≤
        Real.log (M₂ / ‖F 0‖) / Real.log 2 := by
    intro k
    exact norm_reflection_sum_le_of_boundary_bound hF h0 hM₂ hbound₂ k
  obtain ⟨gLocal, hLocal, hLocalNe, hLocalBound⟩ :=
    norm_local_logDeriv_remainder_le_of_ecanonical hFglobal hF D h0 hzf hglobal hreflect n hn
  refine ⟨gLocal, hLocal, hLocalNe, ?_⟩
  simpa only [K] using hLocalBound

/--
Inputs: boundary bounds on the circles of radii 1 and 2, a canonical factorization, and the center
identity for the local analytic factor returned by the Turán decomposition.
Claim: the higher logarithmic derivatives of this local factor are bounded by the canonical-factor
estimate plus the Jensen reflection error.
Content: rewrite the Turán center identity as a local factorization equation and apply the general
local remainder estimate.
Role: connects the boundary estimates to the derivative lower bound used for zero detection.
-/
theorem norm_turan_local_logDeriv_remainder_le_of_two_sphere_bounds {F g : ℂ → ℂ}
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (D : Complex.ECanonicalDecomp F g 1)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = 1 → F ρ ≠ 0) {M₁ M₂ : ℝ} (hM₂ : 1 ≤ M₂)
    (hbound₁ : ∀ ρ : ℂ, ‖ρ‖ = 1 → ‖F ρ‖ ≤ Real.exp M₁)
    (hbound₂ : ∀ z ∈ Metric.sphere (0 : ℂ) 2, ‖F z‖ ≤ M₂) (M l : ℕ) (hn : 0 < M + l)
    (gLocal : ℂ → ℂ)
    (hcenter :
      iteratedDeriv (M + l) (logDeriv F) 0 =
        ((-1 : ℂ) ^ (M + l) * ((M + l).factorial : ℂ)) *
            (∑ᶠ u : ℂ,
              ((MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |(1 : ℝ)|) u : ℤ) : ℂ) *
                (0 - u)⁻¹ ^ (M + 1 + l)) +
          iteratedDeriv (M + l) (logDeriv gLocal) 0) :
    ‖iteratedDeriv (M + l) (logDeriv gLocal) 0‖ ≤
      (M + l).factorial * (192 * (1 / 4) * (M₁ - Real.log ‖F 0‖ + 1) / 1 ^ 2) / (1 / 4) ^ (M + l) +
        (M + l).factorial * (Real.log (M₂ / ‖F 0‖) / Real.log 2) := by
  let K : ℕ → ℝ := fun k =>
    k.factorial * (192 * (1 / 4) * (M₁ - Real.log ‖F 0‖ + 1) / 1 ^ 2) / (1 / 4) ^ k
  let E : ℕ → ℝ := fun _ => Real.log (M₂ / ‖F 0‖) / Real.log 2
  have hglobal : ∀ k, 0 < k → ‖iteratedDeriv k (logDeriv g) 0‖ ≤ K k := by
    intro k hk
    simpa only [K] using
      norm_iteratedDeriv_ecanonicalDecomp_logDeriv_le_of_boundary_bound hF h0
        (by norm_num only : (1 : ℝ) ≤ 1) D hzf hbound₁ k hk
  have hreflect :
    ∀ k : ℕ,
      ‖∑ᶠ u : ℂ,
            ((-MeromorphicOn.divisor F (Metric.ball (0 : ℂ) 1) u : ℤ) : ℂ) *
              ((0 : ℂ) - (1 : ℂ) ^ 2 / starRingEnd ℂ u) ^ (-1 - (k : ℤ) : ℤ)‖ ≤
        E k := by
    intro k
    exact norm_reflection_sum_le_of_boundary_bound hF h0 hM₂ hbound₂ k
  have hlocal := iteratedDeriv_local_equation_of_turan_decomposition_at_zero gLocal M l hcenter
  have hrem :=
    norm_local_logDeriv_remainder_le_of_ecanonical_of_local_decomposition hF D h0 hzf (M + l) gLocal
      hlocal hglobal hreflect hn
  simpa only [K, E] using hrem

/--
Inputs: a translated ordinary L-function centered in the half-plane with real part at least 1, a
zero-free unit circle, a canonical factorization, and the Turán center identity.
Claim: the derivative of the local analytic factor returned by the Turán decomposition has an
explicit bound in terms of the conductor, center, and radius.
Content: apply the right-half-plane bound for the ordinary L-function on circles of radii 1 and 2,
then use the general remainder estimate.
Role: supplies the analytic-factor error needed to obtain a local Turán bound for ordinary L
functions from completed zeros.
-/
theorem norm_turan_scaled_LFunction_local_remainder_le {q : ℕ} [NeZero q] (hq : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c : ℂ} {R : ℝ} (hR : 0 < R) (hRle : R ≤ 1 / 4)
    (hcRe : 1 ≤ c.re) {g : ℂ → ℂ}
    (D :
      Complex.ECanonicalDecomp (fun z : ℂ => DirichletCharacter.LFunction χ (z * (R : ℂ) + c)) g 1)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = 1 → DirichletCharacter.LFunction χ (ρ * (R : ℂ) + c) ≠ 0) (M l : ℕ)
    (hn : 0 < M + l) (gLocal : ℂ → ℂ)
    (hcenter :
      iteratedDeriv (M + l)
          (logDeriv (fun z : ℂ => DirichletCharacter.LFunction χ (z * (R : ℂ) + c))) 0 =
        ((-1 : ℂ) ^ (M + l) * ((M + l).factorial : ℂ)) *
            (∑ᶠ u : ℂ,
              ((MeromorphicOn.divisor
                      (fun z : ℂ => DirichletCharacter.LFunction χ (z * (R : ℂ) + c))
                      (Metric.ball (0 : ℂ) |(1 : ℝ)|) u :
                    ℤ) :
                  ℂ) *
                (0 - u)⁻¹ ^ (M + 1 + l)) +
          iteratedDeriv (M + l) (logDeriv gLocal) 0) :
    ‖iteratedDeriv (M + l) (logDeriv gLocal) 0‖ ≤
      (M + l).factorial *
            (192 * (1 / 4) *
                (Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + R))) -
                    Real.log ‖DirichletCharacter.LFunction χ c‖ +
                  1) /
              1 ^ 2) /
          (1 / 4) ^ (M + l) +
        (M + l).factorial *
          (Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + 2 * R)) / ‖DirichletCharacter.LFunction χ c‖) /
            Real.log 2) := by
  let F : ℂ → ℂ := fun z => DirichletCharacter.LFunction χ (z * (R : ℂ) + c)
  let M₁ : ℝ := Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + R)))
  let M₂ : ℝ := max 1 (2 * (q : ℝ) * (‖c‖ + 2 * R))
  have hF : Differentiable ℂ F := by
    exact
      (DirichletCharacter.differentiable_LFunction hχ).comp
        ((differentiable_id.mul_const (R : ℂ)).add_const c)
  have h0 : F 0 ≠ 0 := by
    simpa only [F, zero_mul, zero_add] using
      (show DirichletCharacter.LFunction χ c ≠ 0 from
        DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hcRe)
  have hzfF : ∀ ρ : ℂ, ‖ρ‖ = 1 → F ρ ≠ 0 := by
    intro ρ hρ
    exact hzf ρ hρ
  have hM₂ : 1 ≤ M₂ := by
    dsimp only [M₂]
    exact le_max_left _ _
  have hbound₁ : ∀ ρ : ℂ, ‖ρ‖ = 1 → ‖F ρ‖ ≤ Real.exp M₁ := by
    intro ρ hρ
    have hL :=
      norm_lFunction_le_two_mul hq hχ
        (by
          simpa only [F] using
            (show (1 / 2 : ℝ) ≤ (ρ * (R : ℂ) + c).re from by
              have hreal : -R ≤ (ρ * (R : ℂ)).re := by
                have hnorm : ‖ρ * (R : ℂ)‖ = R := by
                  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, hρ]
                  ring
                have habs := Complex.abs_re_le_norm (ρ * (R : ℂ))
                rw [abs_le, hnorm] at habs
                exact habs.1
              rw [Complex.add_re]
              linarith only [hcRe, hRle, hreal]))
    have hnorm : ‖ρ * (R : ℂ)‖ = R := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, hρ]
      ring
    have hsum : ‖ρ * (R : ℂ) + c‖ ≤ ‖c‖ + R := by
      calc
        ‖ρ * (R : ℂ) + c‖ ≤ ‖ρ * (R : ℂ)‖ + ‖c‖ := norm_add_le _ _
        _ = ‖c‖ + R := by
          rw [hnorm]; ring
    have hpoly : ‖F ρ‖ ≤ 2 * (q : ℝ) * (‖c‖ + R) := by
      dsimp only [F]
      exact hL.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
    have hMpos : 0 < max 1 (2 * (q : ℝ) * (‖c‖ + R)) :=
      lt_of_lt_of_le (by norm_num only) (le_max_left _ _)
    calc
      ‖F ρ‖ ≤ max 1 (2 * (q : ℝ) * (‖c‖ + R)) := le_trans hpoly (le_max_right _ _)
      _ = Real.exp M₁ := by
        dsimp only [M₁]
        exact (Real.exp_log hMpos).symm
  have hbound₂ : ∀ z ∈ Metric.sphere (0 : ℂ) 2, ‖F z‖ ≤ M₂ := by
    intro z hz
    have hzNorm : ‖z‖ = 2 := by
      rw [Metric.mem_sphere, dist_zero_right] at hz
      exact hz
    have hscale : ‖z * (R : ℂ)‖ = 2 * R := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, hzNorm]
    have hreal : -(2 * R) ≤ (z * (R : ℂ)).re := by
      have habs := Complex.abs_re_le_norm (z * (R : ℂ))
      rw [abs_le, hscale] at habs
      exact habs.1
    have hcircle : (1 / 2 : ℝ) ≤ (z * (R : ℂ) + c).re := by
      rw [Complex.add_re]
      nlinarith only [hcRe, hRle, hreal]
    have hL := norm_lFunction_le_two_mul hq hχ hcircle
    have hsum : ‖z * (R : ℂ) + c‖ ≤ ‖c‖ + 2 * R := by
      calc
        ‖z * (R : ℂ) + c‖ ≤ ‖z * (R : ℂ)‖ + ‖c‖ := norm_add_le _ _
        _ = ‖c‖ + 2 * R := by
          rw [hscale]; ring
    have hpoly : ‖F z‖ ≤ 2 * (q : ℝ) * (‖c‖ + 2 * R) := by
      dsimp only [F]
      exact hL.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
    calc
      ‖F z‖ ≤ 2 * (q : ℝ) * (‖c‖ + 2 * R) := hpoly
      _ ≤ M₂ := le_max_right _ _
  simpa only [F, M₁, M₂, zero_mul, zero_add] using
    norm_turan_local_logDeriv_remainder_le_of_two_sphere_bounds hF h0 D hzfF hM₂ hbound₁ hbound₂ M l
      hn gLocal hcenter

/--
Inputs: a nonzero center value and a zero inside the unit disk for a translated ordinary L-function.
Claim: the zero belongs to the support of the scaled function's local divisor.
Content: establish finite analytic order at the center and propagate finiteness throughout the
connected complex plane.
Role: converts an ordinary L-function zero into the local support input required by Turán detection.
-/
theorem scaled_LFunction_zero_mem_local_divisor_support {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c : ℂ} {R : ℝ} {z : ℂ}
    (hc : DirichletCharacter.LFunction χ c ≠ 0)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = 1 → DirichletCharacter.LFunction χ (ρ * (R : ℂ) + c) ≠ 0) (hz : ‖z‖ < 1)
    (hzero : DirichletCharacter.LFunction χ (z * (R : ℂ) + c) = 0) :
    z ∈
      (MeromorphicOn.divisor (fun w : ℂ => DirichletCharacter.LFunction χ (w * (R : ℂ) + c))
          (Metric.ball (0 : ℂ) |(1 : ℝ)|)).support := by
  let F : ℂ → ℂ := fun w => DirichletCharacter.LFunction χ (w * (R : ℂ) + c)
  let U : Set ℂ := Metric.ball (0 : ℂ) |(1 : ℝ)|
  have hF : Differentiable ℂ F := by
    exact
      (DirichletCharacter.differentiable_LFunction hχ).comp
        ((differentiable_id.mul_const (R : ℂ)).add_const c)
  have hFglobal : AnalyticOnNhd ℂ F Set.univ := fun w _ => hF.analyticAt w
  have h0 : F 0 ≠ 0 := by simpa only [F, zero_mul, zero_add] using hc
  have h1norm : ‖(1 : ℂ)‖ = 1 := norm_one
  have h1nz : F 1 ≠ 0 := hzf 1 h1norm
  have hz₀Order : analyticOrderAt F 1 ≠ ⊤ := by
    rw [(hFglobal 1 trivial).analyticOrderAt_eq_zero.mpr h1nz]
    exact ENat.natCast_ne_top 0
  have horder (w : ℂ) : analyticOrderAt F w ≠ ⊤ :=
    hFglobal.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ trivial trivial hz₀Order
  have hnotTop (u : Metric.ball (0 : ℂ) |(1 : ℝ)|) : meromorphicOrderAt F u ≠ ⊤ := by
    rw [(hFglobal u.1 trivial).meromorphicOrderAt_eq]
    intro hu
    exact horder u.1 (ENat.map_eq_top_iff.mp hu)
  have hFanalytic : AnalyticOnNhd ℂ F U := fun w _ => hFglobal w trivial
  have hnormal : MeromorphicNFOn F U := hFanalytic.meromorphicNFOn
  have hmem : z ∈ U ∩ F ⁻¹' {0} := by
    refine ⟨?_, ?_⟩
    · change z ∈ Metric.ball (0 : ℂ) |(1 : ℝ)|
      rw [Metric.mem_ball, dist_zero_right]
      simpa only [abs_of_pos (by norm_num only : (0 : ℝ) < 1)] using hz
    · simpa only [Set.mem_preimage, Set.mem_singleton_iff, F] using hzero
  rw [hnormal.zero_set_eq_divisor_support hnotTop] at hmem
  change z ∈ (MeromorphicOn.divisor F U).support
  exact hmem

/--
Inputs: a translated ordinary L-function centered in the right half-plane, a zero in the unit disk,
and a canonical factorization.
Claim: a Turán local decomposition around the zero yields an explicit lower bound for an ordinary
L-function derivative.
Content: subtract the local-factor error obtained from the radius-1 and radius-2 boundary bounds,
then transfer the resulting lower bound to the derivative by the triangle inequality.
Role: passes zero detection for a scaled ordinary L-function to the family log-free
density estimate.
-/
theorem exists_scaled_LFunction_turan_derivative_lower_bound {q : ℕ} [NeZero q] (hq : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c : ℂ} {R : ℝ} (hR : 0 < R) (hRle : R ≤ 1 / 4)
    (hcRe : 1 ≤ c.re) (hc : DirichletCharacter.LFunction χ c ≠ 0) {g : ℂ → ℂ}
    (D :
      Complex.ECanonicalDecomp (fun z : ℂ => DirichletCharacter.LFunction χ (z * (R : ℂ) + c)) g 1)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = 1 → DirichletCharacter.LFunction χ (ρ * (R : ℂ) + c) ≠ 0) {z : ℂ}
    (hz : ‖z‖ < 1) (hzero : DirichletCharacter.LFunction χ (z * (R : ℂ) + c) = 0) (M : ℕ)
    (hM : 0 < M) :
    ∃ s : Finset ℂ,
      ∃ l ∈ Finset.range s.card,
        ∃ gLocal : ℂ → ℂ,
          (∀ u,
              u ∈ s ↔
                (MeromorphicOn.divisor
                      (fun z : ℂ => DirichletCharacter.LFunction χ (z * (R : ℂ) + c))
                      (Metric.ball (0 : ℂ) |(1 : ℝ)|))
                    u ≠
                  0) ∧
            0 < s.card ∧
            (∀ u ∈ s,
              u ∈ Metric.ball (0 : ℂ) |(1 : ℝ)| ∧
                (MeromorphicOn.divisor
                      (fun z : ℂ => DirichletCharacter.LFunction χ (z * (R : ℂ) + c))
                      (Metric.ball (0 : ℂ) |(1 : ℝ)|))
                    u ≠
                  0) ∧
            AnalyticOnNhd ℂ gLocal (Metric.ball (0 : ℂ) |(1 : ℝ)|) ∧
            (∀ u : Metric.ball (0 : ℂ) |(1 : ℝ)|, gLocal u ≠ 0) ∧
            ((‖∑ v ∈ s,
                        ((MeromorphicOn.divisor
                              (fun z : ℂ => DirichletCharacter.LFunction χ (z * (R : ℂ) + c))
                              (Metric.ball (0 : ℂ) |(1 : ℝ)|) v :
                            ℤ) :
                          ℂ)‖ /
                    (∑ k ∈ Finset.range s.card, (Nat.choose (k + M) k : ℝ) * 2 ^ k)) *
                  ((M + l).factorial : ℝ) -
                ((M + l).factorial : ℝ) *
                    (192 * (1 / 4) *
                        (Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + R))) -
                            Real.log ‖DirichletCharacter.LFunction χ c‖ +
                          1) /
                      1 ^ 2) /
                  (1 / 4) ^ (M + l) -
                ((M + l).factorial : ℝ) *
                  (Real.log
                      (max 1 (2 * (q : ℝ) * (‖c‖ + 2 * R)) / ‖DirichletCharacter.LFunction χ c‖) /
                    Real.log 2)) ≤
              ‖iteratedDeriv (M + l)
                  (logDeriv (fun z : ℂ => DirichletCharacter.LFunction χ (z * (R : ℂ) + c)))
                  0‖ := by
  let F : ℂ → ℂ := fun z => DirichletCharacter.LFunction χ (z * (R : ℂ) + c)
  have hF : Differentiable ℂ F := by
    exact
      (DirichletCharacter.differentiable_LFunction hχ).comp
        ((differentiable_id.mul_const (R : ℂ)).add_const c)
  have hFglobal : AnalyticOnNhd ℂ F Set.univ := fun z _ => hF.analyticAt z
  have h0 : F 0 ≠ 0 := by simpa only [F, zero_mul, zero_add] using hc
  have h1norm : ‖(1 : ℂ)‖ = 1 := norm_one
  have h1nz : F 1 ≠ 0 := hzf 1 h1norm
  have hzeros : ∃ u, u ∈ (MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |(1 : ℝ)|)).support :=
    ⟨z, scaled_LFunction_zero_mem_local_divisor_support χ hχ hc hzf hz hzero⟩
  obtain ⟨s, l, hl, gLocal, hs, hspos, hdomain, hg, hgn, hsumBound, hcenter⟩ :=
    exists_analytic_local_zero_turan_derivative_decomposition hFglobal 1 h1nz (R := 1)
      (by norm_num only : 0 < |(1 : ℝ)|) (by norm_num only : |(1 : ℝ)| ≤ 1) h0 hzeros M
  let d : ℂ → ℤ := MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |(1 : ℝ)|)
  have hden : 0 < ∑ k ∈ Finset.range s.card, (Nat.choose (k + M) k : ℝ) * 2 ^ k :=
    PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.turan_factor_pos s.card M
      hspos
  have hsumLower :
    ‖∑ v ∈ s, ((d v : ℤ) : ℂ)‖ / (∑ k ∈ Finset.range s.card, (Nat.choose (k + M) k : ℝ) * 2 ^ k) ≤
      ‖∑ᶠ u,
          ((MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |(1 : ℝ)|) u : ℤ) : ℂ) *
            (0 - u)⁻¹ ^ (M + 1 + l)‖ := by
    simpa only [d] using hsumBound
  have hrem :=
    norm_turan_scaled_LFunction_local_remainder_le hq χ hχ hR hRle hcRe D hzf M l
      (Nat.add_pos_left hM l) gLocal hcenter
  have hderiv := norm_derivative_lower_bound_of_zero_sum_decomposition hcenter hsumLower hrem
  refine ⟨s, l, hl, gLocal, ?_, hspos, ?_, hg, hgn, ?_⟩
  · intro v
    simpa only [d, F] using hs v
  · intro v hv
    simpa only [d, F] using hdomain v hv
  · linarith only [hderiv]

/--
Inputs: a positive natural multiplicity and a nonnegative real error coefficient.
Claim: beyond some exponent, the scaled power with base `80 / 3` strictly exceeds the sum of
`48 * A * 4^n` and the constant error `B`.
Proof: factor out `4^n` and use that `(20 / 3)^n` tends to infinity.
Role: supplies the exponent threshold needed to absorb both errors in the shifted derivative bound.
-/
theorem exists_nat_ge_scaled_power_margin {m : ℕ} (hm : 0 < m) {A B : ℝ} (hB : 0 ≤ B) :
    ∃ K : ℕ,
      ∀ n : ℕ, K ≤ n → 48 * A * (4 : ℝ) ^ n + B < (1 / (4 * (m : ℝ))) * (80 / 3 : ℝ) ^ (n + 1) := by
  let α : ℝ := (1 / (4 * (m : ℝ))) * (80 / 3 : ℝ)
  have hmR : 0 < (m : ℝ) := by exact Nat.cast_pos.mpr hm
  have hα : 0 < α := by
    exact
      mul_pos (div_pos zero_lt_one (mul_pos (by norm_num only : (0 : ℝ) < 4) hmR))
        (by norm_num only : (0 : ℝ) < 80 / 3)
  have hx : 1 < (20 / 3 : ℝ) := by norm_num only
  have hpow : Filter.Tendsto (fun n : ℕ => (20 / 3 : ℝ) ^ n) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hx
  have hscaled : Filter.Tendsto (fun n : ℕ => α * (20 / 3 : ℝ) ^ n) Filter.atTop Filter.atTop :=
    hpow.const_mul_atTop hα
  let C : ℝ := 48 * A + B + 1
  have hev := hscaled.eventually_ge_atTop C
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hev
  refine ⟨K, fun n hn => ?_⟩
  have hlarge : C ≤ α * (20 / 3 : ℝ) ^ n := hK n hn
  have hmargin : 48 * A + B < α * (20 / 3 : ℝ) ^ n := by linarith only [hlarge]
  have hpow4 : 1 ≤ (4 : ℝ) ^ n := by exact one_le_pow₀ (by norm_num only : (1 : ℝ) ≤ 4)
  have hBpow : B ≤ B * (4 : ℝ) ^ n := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow4 hB
  have hleft : 48 * A * (4 : ℝ) ^ n + B ≤ (48 * A + B) * (4 : ℝ) ^ n := by linarith only [hBpow]
  have hmain : (48 * A + B) * (4 : ℝ) ^ n < (α * (20 / 3 : ℝ) ^ n) * (4 : ℝ) ^ n := by
    exact mul_lt_mul_of_pos_right hmargin (pow_pos (by norm_num only : (0 : ℝ) < 4) n)
  calc
    48 * A * (4 : ℝ) ^ n + B ≤ (48 * A + B) * (4 : ℝ) ^ n := hleft
    _ < (α * (20 / 3 : ℝ) ^ n) * (4 : ℝ) ^ n := hmain
    _ = α * ((20 / 3 : ℝ) ^ n * (4 : ℝ) ^ n) := by ring
    _ = α * (80 / 3 : ℝ) ^ n := by
      rw [← mul_pow]; norm_num only
    _ = (1 / (4 * (m : ℝ))) * (80 / 3 : ℝ) ^ (n + 1) := by
      dsimp only [α]
      rw [pow_succ]
      ring

/--
Inputs: a translated ordinary `L`-function with a zero near the center of its unit disk, a
canonical factorization with a zero-free boundary, and a block scale of at least two.
Claim: one shifted power-block derivative has an explicit lower bound after subtracting the
canonical-factor and reflection remainders.
Proof: use the near-zero block decomposition, rewrite its center identity in the canonical
factorization form, and apply the existing two-sphere remainder estimate.
Role: gives an explicit scaled-`L` detection bound that no longer takes the local remainder as an
unproved input.
-/
theorem exists_scaled_LFunction_shifted_block_derivative_lower_bound {q : ℕ} [NeZero q] (hq : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c : ℂ} {R : ℝ} (hR : 0 < R) (hRle : R ≤ 1 / 4)
    (hcRe : 1 ≤ c.re) (hc : DirichletCharacter.LFunction χ c ≠ 0) {g : ℂ → ℂ}
    (D :
      Complex.ECanonicalDecomp (fun z : ℂ => DirichletCharacter.LFunction χ (z * (R : ℂ) + c)) g 1)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = 1 → DirichletCharacter.LFunction χ (ρ * (R : ℂ) + c) ≠ 0) {z : ℂ}
    (hz : ‖z‖ ≤ 3 / 80) (hzero : DirichletCharacter.LFunction χ (z * (R : ℂ) + c) = 0) (K : ℕ)
    (hK : 2 ≤ K) :
    ∃ s : Finset ℂ,
      (∀ v,
          v ∈ s ↔
            (MeromorphicOn.divisor (fun z : ℂ => DirichletCharacter.LFunction χ (z * (R : ℂ) + c))
                  (Metric.ball (0 : ℂ) |(1 : ℝ)|))
                v ≠
              0) ∧
        ∃ n : ℕ,
          K ≤ n + 1 ∧
            n + 1 ≤
              K *
                (∑ v ∈ s,
                  (MeromorphicOn.divisor
                      (fun z : ℂ => DirichletCharacter.LFunction χ (z * (R : ℂ) + c))
                      (Metric.ball (0 : ℂ) |(1 : ℝ)|) v).toNat) ∧
            (1 /
                    (4 *
                      ((∑ v ∈ s,
                            (MeromorphicOn.divisor
                                (fun z : ℂ => DirichletCharacter.LFunction χ (z * (R : ℂ) + c))
                                (Metric.ball (0 : ℂ) |(1 : ℝ)|) v).toNat :
                          ℕ) :
                        ℝ))) *
                  (80 / 3 : ℝ) ^ (n + 1) *
                  (n.factorial : ℝ) -
                (n.factorial : ℝ) *
                    (192 * (1 / 4) *
                        (Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + R))) -
                            Real.log ‖DirichletCharacter.LFunction χ c‖ +
                          1) /
                      1 ^ 2) /
                  (1 / 4) ^ n -
                (n.factorial : ℝ) *
                  (Real.log
                      (max 1 (2 * (q : ℝ) * (‖c‖ + 2 * R)) / ‖DirichletCharacter.LFunction χ c‖) /
                    Real.log 2) ≤
              ‖iteratedDeriv n
                  (logDeriv (fun z : ℂ => DirichletCharacter.LFunction χ (z * (R : ℂ) + c)))
                  0‖ := by
  let F : ℂ → ℂ := fun w => DirichletCharacter.LFunction χ (w * (R : ℂ) + c)
  have hF : Differentiable ℂ F := by
    exact
      (DirichletCharacter.differentiable_LFunction hχ).comp
        ((differentiable_id.mul_const (R : ℂ)).add_const c)
  have hFglobal : AnalyticOnNhd ℂ F Set.univ := fun w _ => hF.analyticAt w
  have h1nz : F 1 ≠ 0 := hzf 1 norm_one
  have hρraw : z ∈ (MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |(1 : ℝ)|)).support := by
    simpa only [F] using
      scaled_LFunction_zero_mem_local_divisor_support χ hχ hc hzf (lt_of_le_of_lt hz (by norm_num))
        hzero
  have hρ : z ∈ (MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |(1 : ℝ)|)).support := by exact hρraw
  have hclose : ‖(0 : ℂ) - z‖ ≤ 3 * (1 / 80 : ℝ) := by
    calc
      ‖(0 : ℂ) - z‖ = ‖z‖ := by simp only [zero_sub, norm_neg]
      _ ≤ 3 * (1 / 80 : ℝ) := by nlinarith only [hz]
      _ = 3 * (1 / 80 : ℝ) := by ring
  have hRdisk : |80 * (1 / 80 : ℝ)| = 1 := by norm_num
  have hRdisk' : |80 * (1 / 80 : ℝ)| = |(1 : ℝ)| := by norm_num
  have hρ' : MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |80 * (1 / 80 : ℝ)|) z ≠ 0 := by
    have hρ' : z ∈ (MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |80 * (1 / 80 : ℝ)|)).support := by
      rw [hRdisk']
      exact hρ
    simpa only [Function.mem_support] using hρ'
  obtain ⟨s, hs, hρmem, hdomain, n, hnK, hnMass, hsumLower, gLocal, hg, hgn, hdecomp⟩ :=
    exists_analytic_local_zero_power_sum_block_derivative_decomposition_of_near hFglobal 1 h1nz
      (by norm_num only : (0 : ℝ) < 1 / 80) (by simpa only [F, zero_mul, zero_add] using hc) z hρ'
      hclose K (by omega)
  let d : ℂ → ℤ := MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |80 * (1 / 80 : ℝ)|)
  let m : ℂ → ℂ := fun v => (d v : ℂ)
  have hpower : (∑ᶠ v, m v * (0 - v) ^ (-1 - (n : ℕ) : ℤ)) = ∑ᶠ v, m v * (0 - v)⁻¹ ^ (n + 1) := by
    apply finsum_congr
    intro v
    rw [zpow_neg_one_sub_nat_eq_inv_pow]
  have hcenter :
    iteratedDeriv n (logDeriv F) 0 =
      ((-1 : ℂ) ^ n * (n.factorial : ℂ)) * (∑ᶠ v, m v * (0 - v)⁻¹ ^ (n + 1)) +
        iteratedDeriv n (logDeriv gLocal) 0 := by
    have hfactor :
      (∑ᶠ v, m v * (((-1 : ℂ) ^ n * (n.factorial : ℂ)) * (0 - v) ^ (-1 - (n : ℕ) : ℤ))) =
        ((-1 : ℂ) ^ n * (n.factorial : ℂ)) * (∑ᶠ v, m v * (0 - v) ^ (-1 - (n : ℕ) : ℤ)) := by
      calc
        _ = ∑ᶠ v, ((-1 : ℂ) ^ n * (n.factorial : ℂ)) * (m v * (0 - v) ^ (-1 - (n : ℕ) : ℤ)) := by
          apply finsum_congr
          intro v
          calc
            _ = (m v * ((-1 : ℂ) ^ n * (n.factorial : ℂ))) * (0 - v) ^ (-1 - (n : ℕ) : ℤ) :=
              (mul_assoc _ _ _).symm
            _ = (((-1 : ℂ) ^ n * (n.factorial : ℂ)) * m v) * (0 - v) ^ (-1 - (n : ℕ) : ℤ) := by
              rw [mul_comm (m v)]
            _ = _ := mul_assoc _ _ _
        _ = _ := (mul_finsum _ _).symm
    rw [hdecomp, hfactor, hpower]
  have hcenter' :
    iteratedDeriv n (logDeriv F) 0 =
      ((-1 : ℂ) ^ n * (n.factorial : ℂ)) *
          (∑ᶠ v,
            ((MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |(1 : ℝ)|) v : ℤ) : ℂ) *
              (0 - v)⁻¹ ^ (n + 1)) +
        iteratedDeriv n (logDeriv gLocal) 0 := by
    have hcenter'' := hcenter
    simp only [d, m] at hcenter''
    rw [hRdisk'] at hcenter''
    exact hcenter''
  have hnpos : 0 < n := by omega
  have hc' : DirichletCharacter.LFunction χ c ≠ 0 := hc
  have hrem :=
    norm_turan_scaled_LFunction_local_remainder_le hq χ hχ hR hRle hcRe D hzf n 0 hnpos gLocal
      hcenter'
  have hsumLower' := hsumLower
  rw [hRdisk'] at hsumLower'
  have hderiv := norm_derivative_lower_bound_of_zero_sum_decomposition hcenter' hsumLower' hrem
  have hs' : ∀ v, v ∈ s ↔ (MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |(1 : ℝ)|)) v ≠ 0 := by
    have hs'' := hs
    rw [hRdisk'] at hs''
    exact hs''
  have hnMass' :
    n + 1 ≤ K * (∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |(1 : ℝ)|) v).toNat) := by
    have hnMass'' := hnMass
    rw [hRdisk'] at hnMass''
    exact hnMass''
  have hderiv' :
    (1 /
            (4 *
              ((∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |(1 : ℝ)|) v).toNat : ℕ) :
                ℝ))) *
          (80 / 3 : ℝ) ^ (n + 1) *
          (n.factorial : ℝ) -
        (n.factorial : ℝ) *
            (192 * (1 / 4) *
                (Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + R))) -
                    Real.log ‖DirichletCharacter.LFunction χ c‖ +
                  1) /
              1 ^ 2) /
          (1 / 4) ^ n -
        (n.factorial : ℝ) *
          (Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + 2 * R)) / ‖DirichletCharacter.LFunction χ c‖) /
            Real.log 2) ≤
      ‖iteratedDeriv n (logDeriv F) 0‖ := by
    have hbase : 1 / (3 * (1 / 80 : ℝ)) = (80 / 3 : ℝ) := by norm_num
    have hderiv'' := hderiv
    rw [hbase] at hderiv''
    simp only [Nat.add_zero] at hderiv''
    have hderiv''' :
      (1 /
              (4 *
                ((∑ v ∈ s, (MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |(1 : ℝ)|) v).toNat : ℕ) :
                  ℝ))) *
            (80 / 3 : ℝ) ^ (n + 1) *
            (n.factorial : ℝ) -
          (n.factorial : ℝ) *
              (192 * (1 / 4) *
                  (Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + R))) -
                      Real.log ‖DirichletCharacter.LFunction χ c‖ +
                    1) /
                1 ^ 2) /
            (1 / 4) ^ n -
          (n.factorial : ℝ) *
            (Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + 2 * R)) / ‖DirichletCharacter.LFunction χ c‖) /
              Real.log 2) ≤
        ‖iteratedDeriv n (logDeriv F) 0‖ := by
      linarith only [hderiv'']
    simpa only [F, Nat.add_zero] using hderiv'''
  refine ⟨s, hs', n, hnK, hnMass', ?_⟩
  simpa only [F] using hderiv'

/--
Inputs: the same shifted ordinary `L`-function data as the explicit block derivative theorem.
Claim: some derivative selected from a sufficiently late near-zero power block is nonzero.
Proof: use the total local zero multiplicity to choose a block beyond the error-absorption
threshold.
Role: turns the explicit derivative lower bound into a positive zero-detection statement.
-/
theorem exists_scaled_LFunction_shifted_block_derivative_pos {q : ℕ} [NeZero q] (hq : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c : ℂ} {R : ℝ} (hR : 0 < R) (hRle : R ≤ 1 / 4)
    (hcRe : 1 ≤ c.re) (hc : DirichletCharacter.LFunction χ c ≠ 0) {g : ℂ → ℂ}
    (D :
      Complex.ECanonicalDecomp (fun z : ℂ => DirichletCharacter.LFunction χ (z * (R : ℂ) + c)) g 1)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = 1 → DirichletCharacter.LFunction χ (ρ * (R : ℂ) + c) ≠ 0) {z : ℂ}
    (hz : ‖z‖ ≤ 3 / 80) (hzero : DirichletCharacter.LFunction χ (z * (R : ℂ) + c) = 0) :
    ∃ n : ℕ,
      0 <
        ‖iteratedDeriv n (logDeriv (fun w : ℂ => DirichletCharacter.LFunction χ (w * (R : ℂ) + c)))
            0‖ := by
  let F : ℂ → ℂ := fun w => DirichletCharacter.LFunction χ (w * (R : ℂ) + c)
  have hF : Differentiable ℂ F := by
    exact
      (DirichletCharacter.differentiable_LFunction hχ).comp
        ((differentiable_id.mul_const (R : ℂ)).add_const c)
  have hFglobal : AnalyticOnNhd ℂ F Set.univ := fun w _ => hF.analyticAt w
  obtain ⟨s, hs, _, _, _, _⟩ :=
    exists_scaled_LFunction_shifted_block_derivative_lower_bound hq χ hχ hR hRle hcRe hc D hzf hz
      hzero 2 (by norm_num only)
  let d : ℂ → ℤ := MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |(1 : ℝ)|)
  have hρraw : z ∈ d.support := by
    dsimp only [d]
    simpa only [F] using
      scaled_LFunction_zero_mem_local_divisor_support χ hχ hc hzf (lt_of_le_of_lt hz (by norm_num))
        hzero
  have hρdiv : d z ≠ 0 := Function.mem_support.mp hρraw
  have hρmem : z ∈ s := (hs z).mpr hρdiv
  have hρnonneg : 0 ≤ d z := by
    dsimp only [d]
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun w _ => hF.analyticAt w) z
  have hρpos : 0 < d z := lt_of_le_of_ne hρnonneg (Ne.symm hρdiv)
  let m : ℕ := ∑ v ∈ s, (d v).toNat
  have hm : 0 < m := by
    dsimp only [m]
    have hcast : ((d z).toNat : ℤ) = d z := Int.toNat_of_nonneg (le_of_lt hρpos)
    have hρmult : 0 < (d z).toNat := by exact_mod_cast hcast.symm ▸ hρpos
    have hsingle : (d z).toNat ≤ ∑ v ∈ s, (d v).toNat :=
      Finset.single_le_sum (fun v hv => Nat.zero_le ((d v).toNat)) hρmem
    omega
  have hnormL : 0 < ‖DirichletCharacter.LFunction χ c‖ := norm_pos_iff.mpr hc
  have hL := norm_lFunction_le_two_mul hq hχ (by linarith only [hcRe] : (1 / 2 : ℝ) ≤ c.re)
  have hU2 : ‖DirichletCharacter.LFunction χ c‖ ≤ max 1 (2 * (q : ℝ) * (‖c‖ + 2 * R)) := by
    calc
      ‖DirichletCharacter.LFunction χ c‖ ≤ 2 * (q : ℝ) * ‖c‖ := hL
      _ ≤ 2 * (q : ℝ) * (‖c‖ + 2 * R) := by
        apply mul_le_mul_of_nonneg_left
        · linarith only [hR]
        · exact mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) (Nat.cast_nonneg q)
      _ ≤ max 1 (2 * (q : ℝ) * (‖c‖ + 2 * R)) := le_max_right _ _
  have hratio : 1 ≤ max 1 (2 * (q : ℝ) * (‖c‖ + 2 * R)) / ‖DirichletCharacter.LFunction χ c‖ :=
    (le_div_iff₀ hnormL).2 (by simpa only [one_mul] using hU2)
  let A : ℝ :=
    Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + R))) - Real.log ‖DirichletCharacter.LFunction χ c‖ + 1
  let B : ℝ :=
    Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + 2 * R)) / ‖DirichletCharacter.LFunction χ c‖) / Real.log 2
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact div_nonneg (Real.log_nonneg hratio) (Real.log_pos (by norm_num only : (1 : ℝ) < 2)).le
  obtain ⟨Kpos, hKpos⟩ := exists_nat_ge_scaled_power_margin (A := A) (B := B) hm hB
  let Kblock : ℕ := max 2 (Kpos + 1)
  have hKblock : 2 ≤ Kblock := le_max_left _ _
  obtain ⟨s', hs', n, hnK, _, hderiv⟩ :=
    exists_scaled_LFunction_shifted_block_derivative_lower_bound hq χ hχ hR hRle hcRe hc D hzf hz
      hzero Kblock hKblock
  have hsEq : s' = s := by
    apply Finset.ext
    intro v
    exact (hs' v).trans (hs v).symm
  have hn : Kpos ≤ n := by
    dsimp only [Kblock] at hnK
    omega
  have hmargin := hKpos n hn
  have hmassEq :
    (∑ v ∈ s', (MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |(1 : ℝ)|) v).toNat) = m := by
    simp only [m, d, hsEq]
  have hpow : ((1 * (4 : ℝ)⁻¹) ^ n)⁻¹ = (4 : ℝ) ^ n := by
    rw [← inv_pow]
    norm_num only
  have hbracket : 0 < (1 / (4 * (m : ℝ))) * (80 / 3 : ℝ) ^ (n + 1) - 48 * A * (4 : ℝ) ^ n - B := by
    linarith only [hmargin]
  have hfact : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hpos := mul_pos hfact hbracket
  have hrewrite :
    (1 /
            (4 *
              ((∑ v ∈ s', (MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |(1 : ℝ)|) v).toNat : ℕ) :
                ℝ))) *
          (80 / 3 : ℝ) ^ (n + 1) *
          (n.factorial : ℝ) -
        (n.factorial : ℝ) *
            (192 * (1 / 4) *
                (Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + R))) -
                    Real.log ‖DirichletCharacter.LFunction χ c‖ +
                  1) /
              1 ^ 2) /
          (1 / 4 : ℝ) ^ n -
        (n.factorial : ℝ) *
          (Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + 2 * R)) / ‖DirichletCharacter.LFunction χ c‖) /
            Real.log 2) =
      (n.factorial : ℝ) *
        ((1 / (4 * (m : ℝ))) * (80 / 3 : ℝ) ^ (n + 1) - 48 * A * (4 : ℝ) ^ n - B) := by
    rw [hmassEq]
    dsimp only [A, B]
    simp only [div_eq_mul_inv, one_pow]
    rw [hpow]
    ring
  have hboundPos :
    0 <
      (1 /
            (4 *
              ((∑ v ∈ s', (MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |(1 : ℝ)|) v).toNat : ℕ) :
                ℝ))) *
          (80 / 3 : ℝ) ^ (n + 1) *
          (n.factorial : ℝ) -
        (n.factorial : ℝ) *
            (192 * (1 / 4) *
                (Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + R))) -
                    Real.log ‖DirichletCharacter.LFunction χ c‖ +
                  1) /
              1 ^ 2) /
          (1 / 4 : ℝ) ^ n -
        (n.factorial : ℝ) *
          (Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + 2 * R)) / ‖DirichletCharacter.LFunction χ c‖) /
            Real.log 2) := by
    rw [hrewrite]
    exact hpos
  refine ⟨n, ?_⟩
  have hderivPos : 0 < ‖iteratedDeriv n (logDeriv F) 0‖ := lt_of_lt_of_le hboundPos hderiv
  simpa only [F] using hderivPos

/--
Inputs: a nontrivial character, a circle whose translated points have real part at least $1/2$,
and a translated L-function with no zeros on that circle.
Claim: the canonical factor's logarithmic-derivative derivatives on that circle have bounds in terms
of the conductor, center, radius, and center value.
Content: apply the right-half-plane bound for the ordinary L-function to the translated circle and
use the general remainder estimate.
Role: provides the explicit analytic-factor remainder needed by the explicit-center Turán
decomposition.
-/
theorem norm_iteratedDeriv_scaled_LFunction_factor_le {q : ℕ} [NeZero q] (hq : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c : ℂ} {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (D :
      Complex.ECanonicalDecomp (fun z : ℂ => DirichletCharacter.LFunction χ (z * (R : ℂ) + c)) g 1)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = 1 → DirichletCharacter.LFunction χ (ρ * (R : ℂ) + c) ≠ 0)
    (hcircle : ∀ ρ : ℂ, ‖ρ‖ = 1 → (1 / 2 : ℝ) ≤ (ρ * (R : ℂ) + c).re)
    (hc : DirichletCharacter.LFunction χ c ≠ 0) (n : ℕ) (hn : 0 < n) :
    ‖iteratedDeriv n (logDeriv g) 0‖ ≤
      n.factorial *
          (192 * (1 / 4) *
              (Real.log (max (1 : ℝ) (2 * (q : ℝ) * (‖c‖ + R))) -
                  Real.log ‖DirichletCharacter.LFunction χ c‖ +
                1) /
            1 ^ 2) /
        (1 / 4) ^ n := by
  let F : ℂ → ℂ := fun z => DirichletCharacter.LFunction χ (z * (R : ℂ) + c)
  let M : ℝ := Real.log (max (1 : ℝ) (2 * (q : ℝ) * (‖c‖ + R)))
  have hF : Differentiable ℂ F := by
    exact
      (DirichletCharacter.differentiable_LFunction hχ).comp
        ((differentiable_id.mul_const (R : ℂ)).add_const c)
  have h0 : F 0 ≠ 0 := by simpa only [F, zero_mul, zero_add] using hc
  have hMpos : 0 < max (1 : ℝ) (2 * (q : ℝ) * (‖c‖ + R)) :=
    lt_of_lt_of_le (by norm_num only) (le_max_left _ _)
  have hbound : ∀ ρ : ℂ, ‖ρ‖ = 1 → ‖F ρ‖ ≤ Real.exp M := by
    intro ρ hρ
    have hL := norm_lFunction_le_two_mul hq hχ (hcircle ρ hρ)
    have hscaled : ‖ρ * (R : ℂ)‖ = R := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, hρ]
      ring
    have hρnorm : ‖ρ * (R : ℂ) + c‖ ≤ ‖c‖ + R := by
      calc
        ‖ρ * (R : ℂ) + c‖ ≤ ‖ρ * (R : ℂ)‖ + ‖c‖ := norm_add_le _ _
        _ = ‖c‖ + R := by
          rw [hscaled]; ring
    have hpoly : ‖F ρ‖ ≤ 2 * (q : ℝ) * (‖c‖ + R) := by
      dsimp only [F]
      exact hL.trans (mul_le_mul_of_nonneg_left hρnorm (by positivity))
    calc
      ‖F ρ‖ ≤ max (1 : ℝ) (2 * (q : ℝ) * (‖c‖ + R)) := le_trans hpoly (le_max_right _ _)
      _ = Real.exp M := by
        dsimp only [M]
        exact (Real.exp_log hMpos).symm
  have hzfF : ∀ ρ : ℂ, ‖ρ‖ = 1 → F ρ ≠ 0 := by
    intro ρ hρ
    simpa only [F] using hzf ρ hρ
  simpa only [F, M, zero_mul, zero_add] using
    norm_iteratedDeriv_ecanonicalDecomp_logDeriv_le_of_boundary_bound hF h0
      (by norm_num only : (1 : ℝ) ≤ 1) D hzfF hbound n hn

/--
Inputs: a nontrivial character and an arbitrary center.
Claim: there is a radius between $1/8$ and $1/4$ whose circle avoids the zeros of the translated
ordinary L-function.
Content: the zeros in the closed disk are finite, so choose a radius different from all their
distances to the center.
Role: provides a larger disk containing the local zeros on which the canonical-factor estimate
can be applied.
-/
theorem exists_shifted_LFunction_zeroFree_sphere_radius {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (c : ℂ) :
    ∃ R : ℝ,
      1 / 8 < R ∧ R < 1 / 4 ∧ ∀ ρ : ℂ, ‖ρ‖ = R → DirichletCharacter.LFunction χ (c + ρ) ≠ 0 := by
  classical
  have hfin :=
    finite_dirichletLFunction_zerosOn χ hχ (isCompact_closedBall (x := c) (r := (1 / 4 : ℝ)))
  have hnormfin :
    ((fun u : ℂ => ‖u - c‖) ''
        (Metric.closedBall c (1 / 4 : ℝ) ∩ DirichletCharacter.LFunction χ ⁻¹' {0})).Finite :=
    hfin.image _
  have hinterval : (Set.Ioo (1 / 8 : ℝ) (1 / 4 : ℝ)).Infinite := Set.Ioo_infinite (by norm_num only)
  obtain ⟨R, hRmem, hRnotin⟩ := hinterval.exists_notMem_finite hnormfin
  refine ⟨R, hRmem.1, hRmem.2, ?_⟩
  intro ρ hρ hzero
  apply hRnotin
  refine ⟨c + ρ, ?_, ?_⟩
  · constructor
    · rw [Metric.mem_closedBall, dist_eq_norm]
      rw [show c + ρ - c = ρ by simp only [add_sub_cancel_left], hρ]
      exact le_of_lt hRmem.2
    · simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hzero
  · simpa only [add_sub_cancel_left] using hρ

/--
Inputs: a nontrivial character, a nonzero ordinary L-value at the center, and a center with real
part at least $5/6$.
Claim: a zero-free circle with radius between $1/8$ and $1/4$ and a derivative bound for its
canonical factor are available.
Content: choose a circle avoiding the finite zero set and apply the right-half-plane polynomial
bound for the ordinary L-function to the canonical factorization.
Role: supplies a uniform bound for the analytic-factor term in the explicit-center Turán
decomposition.
-/
theorem exists_scaled_LFunction_canonical_remainder {q : ℕ} [NeZero q] (hq : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (c : ℂ) (hc : DirichletCharacter.LFunction χ c ≠ 0)
    (hcRe : 1 ≤ c.re) :
    ∃ R : ℝ,
      1 / 8 < R ∧
        R < 1 / 4 ∧
        ∃ g : ℂ → ℂ,
          Complex.ECanonicalDecomp (fun z : ℂ => DirichletCharacter.LFunction χ (z * (R : ℂ) + c)) g
              1 ∧
            (∀ ρ : ℂ, ‖ρ‖ = 1 → DirichletCharacter.LFunction χ (ρ * (R : ℂ) + c) ≠ 0) ∧
            (∀ ρ : ℂ, ‖ρ‖ = 1 → (1 / 2 : ℝ) ≤ (ρ * (R : ℂ) + c).re) ∧
            ∀ n : ℕ,
              0 < n →
                ‖iteratedDeriv n (logDeriv g) 0‖ ≤
                  n.factorial *
                      (192 * (1 / 4) *
                          (Real.log (max (1 : ℝ) (2 * (q : ℝ) * (‖c‖ + R))) -
                              Real.log ‖DirichletCharacter.LFunction χ c‖ +
                            1) /
                        1 ^ 2) /
                    (1 / 4) ^ n := by
  obtain ⟨R, hRlo, hRhi, hzfActual⟩ := exists_shifted_LFunction_zeroFree_sphere_radius χ hχ c
  have hRpos : 0 < R := lt_trans (by norm_num only : (0 : ℝ) < 1 / 8) hRlo
  have hF : Differentiable ℂ (fun z : ℂ => DirichletCharacter.LFunction χ (z * (R : ℂ) + c)) := by
    exact
      (DirichletCharacter.differentiable_LFunction hχ).comp
        ((differentiable_id.mul_const (R : ℂ)).add_const c)
  have h0 : DirichletCharacter.LFunction χ (0 * (R : ℂ) + c) ≠ 0 := by
    simpa only [zero_mul, zero_add] using hc
  obtain ⟨g, D⟩ :=
    PseudoPrime.AnalyticNumberTheory.General.exists_ecanonicalDecomp_of_entire hF h0 1
  have hzf : ∀ ρ : ℂ, ‖ρ‖ = 1 → DirichletCharacter.LFunction χ (ρ * (R : ℂ) + c) ≠ 0 := by
    intro ρ hρ
    have hscale : ‖ρ * (R : ℂ)‖ = R := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos, hρ]
      ring
    simpa only [add_comm] using hzfActual (ρ * (R : ℂ)) hscale
  have hcircle : ∀ ρ : ℂ, ‖ρ‖ = 1 → (1 / 2 : ℝ) ≤ (ρ * (R : ℂ) + c).re := by
    intro ρ hρ
    have hscale : ‖ρ * (R : ℂ)‖ = R := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos, hρ]
      ring
    have hreal : -R ≤ (ρ * (R : ℂ)).re := by
      have habs := Complex.abs_re_le_norm (ρ * (R : ℂ))
      rw [abs_le, hscale] at habs
      exact habs.1
    rw [Complex.add_re]
    nlinarith only [hcRe, hRhi, hreal]
  refine ⟨R, hRlo, hRhi, g, D, hzf, hcircle, ?_⟩
  intro n hn
  exact norm_iteratedDeriv_scaled_LFunction_factor_le hq χ hχ hRpos D hzf hcircle hc n hn

/--
Inputs: a zero with `29/30 ≤ σ ≤ 1`, its explicit center, and a scaling radius `R > 1/15`.
Claim: a completed L-function zero becomes a zero of the scaled ordinary L-function inside the
unit disk.
Content: use the matching imaginary parts and the real-part bounds to construct a point in the
disk, then transfer the zero in the right half-plane.
Role: passes zeros counted for the completed function to the Turán power-sum input for the
ordinary L-function.
-/
theorem completed_zero_enters_scaled_LFunction_disk {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} {ρ c : ℂ} {R : ℝ} (hσlower : (29 / 30 : ℝ) ≤ σ) (hσupper : σ ≤ 1) (hρlower : σ ≤ ρ.re)
    (hρupper : ρ.re ≤ 1) (hcre : c.re = 2 - σ) (hcim : c.im = ρ.im) (hR : 1 / 15 < R)
    (hzero : DirichletCharacter.completedLFunction χ ρ = 0) :
    ∃ z : ℂ, ‖z‖ < 1 ∧ DirichletCharacter.LFunction χ (z * (R : ℂ) + c) = 0 := by
  classical
  have hRpos : 0 < R := lt_trans (by norm_num only : (0 : ℝ) < 1 / 15) hR
  have hρc_nonpos : ρ.re - c.re ≤ 0 := by
    rw [hcre]
    nlinarith only [hρupper, hσupper]
  have hdist : ‖ρ - c‖ = c.re - ρ.re := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.sub_re, Complex.sub_im, hcim, sub_self,
      zero_pow (by norm_num only : (2 : ℕ) ≠ 0), add_zero, Real.sqrt_sq_eq_abs,
      abs_of_nonpos hρc_nonpos]
    ring
  have hdist_bound : ‖ρ - c‖ ≤ 1 / 15 := by
    rw [hdist, hcre]
    nlinarith only [hσlower, hρlower]
  let z : ℂ := (ρ - c) / (R : ℂ)
  have hnormz : ‖z‖ = ‖ρ - c‖ / R := by
    dsimp only [z]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos]
  have hsmall : (1 / 15 : ℝ) < R := hR
  have hznorm : ‖z‖ < 1 := by
    rw [hnormz]
    exact (div_le_div_of_nonneg_right hdist_bound hRpos.le).trans_lt ((div_lt_one hRpos).2 hsmall)
  have hRcomplex : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hRpos.ne'
  have hcoord : z * (R : ℂ) + c = ρ := by
    dsimp only [z]
    rw [div_mul_cancel₀ _ hRcomplex]
    exact sub_add_cancel _ _
  have hLzero :=
    (completedLFunction_zero_iff_LFunction_of_re_pos χ
          (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 29 / 30) (le_trans hσlower hρlower))).mp
      hzero
  exact
    ⟨z, hznorm, by
      rw [hcoord]; exact hLzero⟩

/--
Inputs: a nontrivial primitive character, a positive completed-zero count, `29/30 ≤ σ ≤ 1`, and
`q > 1`.
Claim: a counted zero gives a zero of the ordinary L-function inside the unit disk together with a
canonical-factor remainder bound.
Content: construct the explicit center and connect the completed/ordinary zero equivalence to the
scaled remainder theorem.
Role: passes the zero count to the Turán-detection stage of the unconditional log-free family
density argument.
-/
theorem exists_scaled_LFunction_data_of_completedZeroCount {q : ℕ} [NeZero q] (hq : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ T : ℝ} (hσlower : (29 / 30 : ℝ) ≤ σ)
    (hσupper : σ ≤ 1) (hT : 0 ≤ T)
    (hcount : 0 < PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ hχ σ T) :
    ∃ ρ : ℂ,
      σ ≤ ρ.re ∧
        ρ.re ≤ 1 ∧
        -T ≤ ρ.im ∧
        ρ.im ≤ T ∧
        DirichletCharacter.completedLFunction χ ρ = 0 ∧
        ∃ c : ℂ,
          c.re = 2 - σ ∧
            c.im = ρ.im ∧
            DirichletCharacter.LFunction χ c ≠ 0 ∧
            ∃ R : ℝ,
              1 / 8 < R ∧
                R < 1 / 4 ∧
                ∃ z : ℂ,
                  ‖z‖ < 1 ∧
                    DirichletCharacter.LFunction χ (z * (R : ℂ) + c) = 0 ∧
                    ∃ g : ℂ → ℂ,
                      Complex.ECanonicalDecomp
                          (fun w : ℂ => DirichletCharacter.LFunction χ (w * (R : ℂ) + c)) g 1 ∧
                        (∀ w : ℂ, ‖w‖ = 1 → DirichletCharacter.LFunction χ (w * (R : ℂ) + c) ≠ 0) ∧
                        (∀ w : ℂ, ‖w‖ = 1 → (1 / 2 : ℝ) ≤ (w * (R : ℂ) + c).re) ∧
                        ∀ n : ℕ,
                          0 < n →
                            ‖iteratedDeriv n (logDeriv g) 0‖ ≤
                              n.factorial *
                                  (192 * (1 / 4) *
                                      (Real.log (max (1 : ℝ) (2 * (q : ℝ) * (‖c‖ + R))) -
                                          Real.log ‖DirichletCharacter.LFunction χ c‖ +
                                        1) /
                                    1 ^ 2) /
                                (1 / 4) ^ n := by
  classical
  obtain
    ⟨ρ, hρσ, hρone, hρlower, hρupper, hzero, c, Rlocal, hRlocaldef, hRlocal, hRlocalle, hcre, hcim,
      hccompleted, _⟩ :=
    exists_completedZeroCount_explicit_local_support_of_pos χ hχ
      (le_trans (by norm_num only : (3 / 4 : ℝ) ≤ 29 / 30) hσlower) hσupper hT hcount
  have hcRe : 1 ≤ c.re := by
    rw [hcre]
    linarith only [hσupper]
  have hcL : DirichletCharacter.LFunction χ c ≠ 0 := by
    intro hcLzero
    have hcRePos : 0 < c.re := lt_of_lt_of_le (by norm_num only) hcRe
    have hcompletedZero := (completedLFunction_zero_iff_LFunction_of_re_pos χ hcRePos).2 hcLzero
    exact hccompleted hcompletedZero
  obtain ⟨R, hRlo, hRhi, g, hD, hzf, hcircle, hrem⟩ :=
    exists_scaled_LFunction_canonical_remainder hq χ hχ c hcL hcRe
  obtain ⟨z, hz, hLzero⟩ :=
    completed_zero_enters_scaled_LFunction_disk χ hσlower hσupper hρσ hρone hcre hcim
      (lt_trans (by norm_num only : (1 / 15 : ℝ) < 1 / 8) hRlo) hzero
  exact
    ⟨ρ, hρσ, hρone, hρlower, hρupper, hzero, c, hcre, hcim, hcL, R, hRlo, hRhi, z, hz, hLzero, g,
      hD, hzf, hcircle, hrem⟩

/--
Inputs: a nontrivial character, `29/30 ≤ σ ≤ 1`, and a positive completed-zero count up to the
given height.
Claim: at the corresponding explicit center, the ordinary L-value has a lower bound when
`1 - σ` is below the zeta-neighborhood constant `ε`.
Content: use that the zero has real part less than 1 to obtain `1 - σ > 0`, then apply the existing
uniform center-value estimate.
Role: provides a lower bound for the center value used in the canonical-factor remainder.
-/
theorem exists_completedZeroCount_center_LFunction_lower_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ T : ℝ} (hσlower : (29 / 30 : ℝ) ≤ σ)
    (hσupper : σ ≤ 1) (hT : 0 ≤ T)
    (hcount : 0 < PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ hχ σ T) :
    ∃ ρ : ℂ,
      σ ≤ ρ.re ∧
        ρ.re ≤ 1 ∧
        -T ≤ ρ.im ∧
        ρ.im ≤ T ∧
        DirichletCharacter.completedLFunction χ ρ = 0 ∧
        ∃ c : ℂ,
          c.re = 2 - σ ∧
            c.im = ρ.im ∧
            ‖c‖ ≤ T + 4 / 3 ∧
            ∃ C ε : ℝ,
              0 < C ∧
                0 < ε ∧
                ε ≤ 1 ∧
                ∀ (_ : 0 < 1 - σ),
                  1 - σ < ε → (1 - σ) / (2 * (q : ℝ) * C) ≤ ‖DirichletCharacter.LFunction χ c‖ := by
  obtain
    ⟨ρ, hρσ, hρone, hρlower, hρupper, hzero, c, Rlocal, hRlocaldef, hRlocal, hRlocalle, hcre, hcim,
      hccompleted, _⟩ :=
    exists_completedZeroCount_explicit_local_support_of_pos χ hχ
      (le_trans (by norm_num only : (3 / 4 : ℝ) ≤ 29 / 30) hσlower) hσupper hT hcount
  have hρlt :=
    PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedLFunction_zero_re_lt_one hχ hzero
  have hσlt : σ < 1 := lt_of_le_of_lt hρσ hρlt
  have hcReNonneg : 0 ≤ c.re := by
    rw [hcre]
    linarith only [hσupper]
  have hcReTight : c.re ≤ 31 / 30 := by
    rw [hcre]
    linarith only [hσlower]
  have hcimAbs : |c.im| ≤ T := by
    rw [hcim]
    exact abs_le.mpr ⟨hρlower, hρupper⟩
  have hcNorm : ‖c‖ ≤ T + 4 / 3 := by
    have hnorm := Complex.norm_le_abs_re_add_abs_im c
    rw [abs_of_nonneg hcReNonneg] at hnorm
    calc
      ‖c‖ ≤ c.re + |c.im| := hnorm
      _ ≤ 31 / 30 + T := add_le_add hcReTight hcimAbs
      _ ≤ T + 4 / 3 := by nlinarith only
  obtain ⟨C, ε, hC, hε, hεle, hbound⟩ := exists_norm_LFunction_lower_bound_one_add (N := q) χ
  have hcenter : c = 1 + (((1 - σ : ℝ) : ℂ)) + Complex.I * ρ.im := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_self, add_zero]
      rw [hcre]
      ring
    · simp only [Complex.add_im, Complex.one_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, mul_zero, one_mul, add_zero, zero_add]
      exact hcim
  refine ⟨ρ, hρσ, hρone, hρlower, hρupper, hzero, c, hcre, hcim, hcNorm, C, ε, hC, hε, hεle, ?_⟩
  intro hx hxε
  have hvalue := hbound (1 - σ) ρ.im hx hxε
  rw [← hcenter] at hvalue
  exact hvalue

/--
Inputs: a scaled ordinary-L canonical decomposition, a center-value lower bound, and a size bound
for the translated disk.
Claim: the factor derivative remainder is bounded using only the conductor, height, and lower
bound parameter.
Proof: apply the boundary estimate, use monotonicity of `log` on both terms, then factor out the
positive derivative coefficient.
Role: supplies the quantitative analytic error needed by a local Turán argument.
-/
theorem norm_iteratedDeriv_scaled_LFunction_factor_le_of_center_lower_bound {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c : ℂ} {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (D :
      Complex.ECanonicalDecomp (fun z : ℂ => DirichletCharacter.LFunction χ (z * (R : ℂ) + c)) g 1)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = 1 → DirichletCharacter.LFunction χ (ρ * (R : ℂ) + c) ≠ 0)
    (hcircle : ∀ ρ : ℂ, ‖ρ‖ = 1 → (1 / 2 : ℝ) ≤ (ρ * (R : ℂ) + c).re)
    (hc : DirichletCharacter.LFunction χ c ≠ 0) {x T C : ℝ} (hx : 0 < x) (hT : 0 ≤ T) (hC : 0 < C)
    (hsize : ‖c‖ + R ≤ T + 2) (hlower : x / (2 * (q : ℝ) * C) ≤ ‖DirichletCharacter.LFunction χ c‖)
    (n : ℕ) (hn : 0 < n) :
    ‖iteratedDeriv n (logDeriv g) 0‖ ≤
      n.factorial *
          (192 * (1 / 4) *
              (Real.log (2 * (q : ℝ) * (T + 2)) - Real.log (x / (2 * (q : ℝ) * C)) + 1) /
            1 ^ 2) /
        (1 / 4) ^ n := by
  let A : ℝ :=
    Real.log (max (1 : ℝ) (2 * (q : ℝ) * (‖c‖ + R))) - Real.log ‖DirichletCharacter.LFunction χ c‖ +
      1
  let B : ℝ := Real.log (2 * (q : ℝ) * (T + 2)) - Real.log (x / (2 * (q : ℝ) * C)) + 1
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (lt_trans (by norm_num only : 0 < 1) hq)
  have hqone : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hTtwo : 2 ≤ T + 2 := by linarith only [hT]
  have hprod : 2 ≤ (q : ℝ) * (T + 2) := by
    calc
      2 ≤ (q : ℝ) * 2 := by nlinarith only [hqone]
      _ ≤ (q : ℝ) * (T + 2) := mul_le_mul_of_nonneg_left hTtwo hqpos.le
  have hupper : max (1 : ℝ) (2 * (q : ℝ) * (‖c‖ + R)) ≤ 2 * (q : ℝ) * (T + 2) := by
    apply max_le
    · nlinarith only [hprod]
    · exact mul_le_mul_of_nonneg_left hsize (by positivity)
  have hlogupper :
    Real.log (max (1 : ℝ) (2 * (q : ℝ) * (‖c‖ + R))) ≤ Real.log (2 * (q : ℝ) * (T + 2)) := by
    apply Real.log_le_log
    · exact lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) (le_max_left _ _)
    · exact hupper
  have hlowerpos : 0 < x / (2 * (q : ℝ) * C) := by
    apply div_pos hx
    positivity
  have hloglower :
    Real.log (x / (2 * (q : ℝ) * C)) ≤ Real.log ‖DirichletCharacter.LFunction χ c‖ := by
    apply Real.log_le_log hlowerpos hlower
  have hAB : A ≤ B := by
    dsimp only [A, B]
    linarith only [hlogupper, hloglower]
  let K : ℝ := n.factorial * (192 * (1 / 4) / 1 ^ 2) / (1 / 4) ^ n
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hbase := norm_iteratedDeriv_scaled_LFunction_factor_le hq χ hχ hR D hzf hcircle hc n hn
  have hbase' : ‖iteratedDeriv n (logDeriv g) 0‖ ≤ K * A := by
    calc
      ‖iteratedDeriv n (logDeriv g) 0‖ ≤ n.factorial * (192 * (1 / 4) * A / 1 ^ 2) / (1 / 4) ^ n :=
        by simpa only [A] using hbase
      _ = K * A := by
        dsimp only [K]; ring
  calc
    ‖iteratedDeriv n (logDeriv g) 0‖ ≤ K * A := hbase'
    _ ≤ K * B := mul_le_mul_of_nonneg_left hAB hK
    _ =
        n.factorial *
            (192 * (1 / 4) *
                (Real.log (2 * (q : ℝ) * (T + 2)) - Real.log (x / (2 * (q : ℝ) * C)) + 1) /
              1 ^ 2) /
          (1 / 4) ^ n :=
      by
      dsimp only [K, B]; ring

/--
Inputs: a positive completed-zero count with `29/30 ≤ σ ≤ 1` and conductor `q > 1`.
Claim: the selected zero has a scaled ordinary-L canonical decomposition whose remainder is
explicitly bounded whenever `1-σ` lies in the zeta neighborhood.
Content: combine zero transfer, the polynomial right-half-plane bound, and the height-uniform
center-value estimate.
Role: provides the local analytic input for the unconditional log-free density argument.
-/
theorem exists_completedZeroCount_scaled_LFunction_canonical_remainder_bound {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ T : ℝ} (hσlower : (29 / 30 : ℝ) ≤ σ)
    (hσupper : σ ≤ 1) (hT : 0 ≤ T)
    (hcount : 0 < PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ hχ σ T) :
    ∃ ρ : ℂ,
      σ ≤ ρ.re ∧
        ρ.re ≤ 1 ∧
        -T ≤ ρ.im ∧
        ρ.im ≤ T ∧
        DirichletCharacter.completedLFunction χ ρ = 0 ∧
        ∃ c : ℂ,
          c.re = 2 - σ ∧
            c.im = ρ.im ∧
            DirichletCharacter.LFunction χ c ≠ 0 ∧
            ∃ R : ℝ,
              1 / 8 < R ∧
                R < 1 / 4 ∧
                ∃ z : ℂ,
                  ‖z‖ < 1 ∧
                    DirichletCharacter.LFunction χ (z * (R : ℂ) + c) = 0 ∧
                    ∃ g : ℂ → ℂ,
                      Complex.ECanonicalDecomp
                          (fun w : ℂ => DirichletCharacter.LFunction χ (w * (R : ℂ) + c)) g 1 ∧
                        (∀ w : ℂ, ‖w‖ = 1 → DirichletCharacter.LFunction χ (w * (R : ℂ) + c) ≠ 0) ∧
                        (∀ w : ℂ, ‖w‖ = 1 → (1 / 2 : ℝ) ≤ (w * (R : ℂ) + c).re) ∧
                        ∃ C ε : ℝ,
                          0 < C ∧
                            0 < ε ∧
                            ε ≤ 1 ∧
                            ∀ (_ : 0 < 1 - σ),
                              1 - σ < ε →
                                ∀ n : ℕ,
                                  0 < n →
                                    ‖iteratedDeriv n (logDeriv g) 0‖ ≤
                                      n.factorial *
                                          (192 * (1 / 4) *
                                              (Real.log (2 * (q : ℝ) * (T + 2)) -
                                                  Real.log ((1 - σ) / (2 * (q : ℝ) * C)) +
                                                1) /
                                            1 ^ 2) /
                                        (1 / 4) ^ n := by
  obtain
    ⟨ρ, hρσ, hρone, hρlower, hρupper, hzero, c, hcre, hcim, hcNorm, C, ε, hC, hε, hεle,
      hcenterLower⟩ :=
    exists_completedZeroCount_center_LFunction_lower_bound χ hχ hσlower hσupper hT hcount
  have hcRe : 1 ≤ c.re := by
    rw [hcre]
    linarith only [hσupper]
  have hcReOne : 1 ≤ c.re := by
    rw [hcre]
    linarith only [hσupper]
  have hcCompleted : DirichletCharacter.completedLFunction χ c ≠ 0 :=
    PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedLFunction_ne_zero_of_one_le_re hχ
      hcReOne
  have hcL : DirichletCharacter.LFunction χ c ≠ 0 := by
    intro hcLzero
    have hcRePos : 0 < c.re := lt_of_lt_of_le (by norm_num only) hcRe
    exact hcCompleted ((completedLFunction_zero_iff_LFunction_of_re_pos χ hcRePos).2 hcLzero)
  obtain ⟨R, hRlo, hRhi, g, hD, hzf, hcircle, hrem⟩ :=
    exists_scaled_LFunction_canonical_remainder hq χ hχ c hcL hcRe
  obtain ⟨z, hz, hLzero⟩ :=
    completed_zero_enters_scaled_LFunction_disk χ hσlower hσupper hρσ hρone hcre hcim
      (lt_trans (by norm_num only : (1 / 15 : ℝ) < 1 / 8) hRlo) hzero
  have hRpos : 0 < R := lt_trans (by norm_num only : (0 : ℝ) < 1 / 8) hRlo
  have hsize : ‖c‖ + R ≤ T + 2 := by
    calc
      ‖c‖ + R ≤ T + 4 / 3 + R := add_le_add_left hcNorm R
      _ ≤ T + 2 := by linarith only [hRhi]
  refine
    ⟨ρ, hρσ, hρone, hρlower, hρupper, hzero, c, hcre, hcim, hcL, R, hRlo, hRhi, z, hz, hLzero, g,
      hD, hzf, hcircle, C, ε, hC, hε, hεle, ?_⟩
  intro hx hxε n hn
  exact
    norm_iteratedDeriv_scaled_LFunction_factor_le_of_center_lower_bound hq χ hχ hRpos hD hzf hcircle
      hcL hx hT hC hsize (hcenterLower hx hxε) n hn

/--
Inputs: a differentiable complex-valued function and an affine map with slope `R`.
Claim: the logarithmic derivative of the composition is `R` times the composed logarithmic
derivative.
Proof: apply `logDeriv_comp` and compute the derivative of the affine map.
Role: isolates the first chain-rule step for converting scaled local derivative bounds to bounds
for the original Dirichlet L-function.
-/
theorem logDeriv_comp_mul_add {f : ℂ → ℂ} (hf : Differentiable ℂ f) (R c : ℂ) :
    logDeriv (fun z : ℂ => f (z * R + c)) = fun z => R * logDeriv f (z * R + c) := by
  funext z
  have hfun : (fun w : ℂ => f (w * R + c)) = f ∘ (fun w : ℂ => R * w + c) := by
    funext w
    congr 1
    ring
  rw [hfun]
  let g : ℂ → ℂ := fun w => R * w + c
  have hg : DifferentiableAt ℂ g z := by fun_prop
  have h := logDeriv_comp (hf (g z)) hg
  have hderiv : deriv g z = R := by
    dsimp only [g]
    rw [deriv_add_const, deriv_const_mul_field, deriv_id'']
    simp only [mul_one]
  simpa only [Function.comp_def, g, hderiv, mul_comm] using h

/--
Inputs: a function analytic on a closed disk, a center, and a contraction of the disk.
Claim: the `n`th derivative of the scaled translate at the origin is the `n`th derivative at the
center multiplied by the scale to the power `n`.
Proof: apply the within-disk chain rule on the open disk, then identify within-derivatives with
ordinary derivatives at the origin using analyticity.
Role: converts local derivatives in a scaled coordinate to derivatives at the original center.
-/
theorem iteratedDeriv_affine_at_of_analytic {f : ℂ → ℂ} {c R : ℂ} {δ : ℝ} (n : ℕ) (hδ : 0 < δ)
    (hR : ‖R‖ ≤ 1) (hf : AnalyticOnNhd ℂ f (Metric.closedBall c δ)) :
    iteratedDeriv n (fun z : ℂ => f (c + R * z)) 0 = R ^ n * iteratedDeriv n f c := by
  let s := Metric.ball (0 : ℂ) δ
  let g : ℂ → ℂ := fun z => f (c + z)
  have hg : AnalyticOnNhd ℂ g s := by
    intro z hz
    have hz' : ‖z‖ < δ := by simpa only [s, Metric.mem_ball, dist_zero_right] using hz
    have hc'z : c + z ∈ Metric.closedBall c δ := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have heq : c + z - c = z := by abel
      rw [heq]
      exact le_of_lt hz'
    have htrans : AnalyticAt ℂ (fun w : ℂ => c + w) z := by fun_prop
    exact (hf (c + z) hc'z).comp htrans
  have hU : UniqueDiffOn ℂ s := Metric.isOpen_ball.uniqueDiffOn
  have hgC : ContDiffOn ℂ n g s := hg.contDiffOn hU
  have hmap : Set.MapsTo (fun z : ℂ => R * z) s s := by
    intro z hz
    have hz' : ‖z‖ < δ := by simpa only [s, Metric.mem_ball, dist_zero_right] using hz
    have hnorm : ‖R * z‖ < δ := by
      calc
        ‖R * z‖ = ‖R‖ * ‖z‖ := norm_mul _ _
        _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hR (norm_nonneg z)
        _ < δ := by simpa only [one_mul] using hz'
    simpa only [s, Metric.mem_ball, dist_zero_right] using hnorm
  have h0 : (0 : ℂ) ∈ s := Metric.mem_ball_self hδ
  have hR0 : R * 0 ∈ s := hmap h0
  have hchain := iteratedDerivWithin_comp_const_smul h0 hU hgC R hmap
  have hg0 : ContDiffAt ℂ n g 0 := (hg 0 h0).contDiffAt
  have hlin : AnalyticAt ℂ (fun z : ℂ => R * z) 0 := by fun_prop
  have hscaledA : AnalyticAt ℂ (fun z : ℂ => g (R * z)) 0 := (hg (R * 0) hR0).comp hlin
  have hscaledC : ContDiffAt ℂ n (fun z : ℂ => g (R * z)) 0 := hscaledA.contDiffAt
  have hchain' : iteratedDeriv n (fun z : ℂ => g (R * z)) 0 = R ^ n * iteratedDeriv n g 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hU hscaledC h0] at hchain
    rw [mul_zero, iteratedDerivWithin_eq_iteratedDeriv hU hg0 h0] at hchain
    simpa only [smul_eq_mul] using hchain
  have hshift : iteratedDeriv n g 0 = iteratedDeriv n f c := by
    dsimp only [g]
    simp only [iteratedDeriv_comp_const_add, add_zero]
  simpa only [g, hshift] using hchain'

/--
Inputs: a nontrivial Dirichlet character, a center to the right of `1`, and a closed disk staying
strictly to the right of `1`.
Claim: the logarithmic derivative of the ordinary Dirichlet L-function is analytic on that disk.
Proof: the L-function is analytic and has no zeros there, so its logarithmic derivative is
analytic at every point of the disk.
Role: supplies the local regularity hypothesis for converting scaled derivatives to central ones.
-/
theorem analyticOnNhd_logDeriv_LFunction_closedBall {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {c : ℂ} {δ : ℝ} (hcδ : δ < c.re - 1) :
    AnalyticOnNhd ℂ (logDeriv (DirichletCharacter.LFunction χ)) (Metric.closedBall c δ) := by
  intro z hz
  have hdist : ‖z - c‖ ≤ δ := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hreal : (z - c).re = z.re - c.re := Complex.sub_re z c
  have hlow : c.re - ‖z - c‖ ≤ z.re := by
    have habs := Complex.abs_re_le_norm (z - c)
    rw [hreal, abs_le] at habs
    linarith only [habs.1]
  have hre : 1 ≤ z.re := by
    have hstrict : 1 < c.re - δ := by linarith only [hcδ]
    have hbridge : c.re - δ ≤ c.re - ‖z - c‖ := by linarith only [hdist]
    exact le_of_lt (lt_of_lt_of_le hstrict (le_trans hbridge hlow))
  have hnonzero := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hre
  exact
    analyticAt_logDeriv_of_ne_zero ((DirichletCharacter.differentiable_LFunction hχ).analyticAt z)
      hnonzero

/--
Inputs: a differentiable function, an affine scale, and analyticity of its logarithmic derivative
near the center.
Claim: the `n`th derivative of the scaled logarithmic derivative at the origin equals the original
central derivative multiplied by the scale to the power `n + 1`.
Proof: use the logarithmic-derivative chain rule, pull out the constant scale, and apply the local
iterated-derivative scaling formula.
Role: converts the Turán lower bound in scaled coordinates to a lower bound at the ordinary
Dirichlet L-function center.
-/
theorem iteratedDeriv_logDeriv_scaled_affine_of_analytic {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {c R : ℂ} {δ : ℝ} (n : ℕ) (hδ : 0 < δ) (hR : ‖R‖ ≤ 1)
    (hlog : AnalyticOnNhd ℂ (logDeriv f) (Metric.closedBall c δ)) :
    iteratedDeriv n (logDeriv (fun z : ℂ => f (z * R + c))) 0 =
      R ^ (n + 1) * iteratedDeriv n (logDeriv f) c := by
  have hcomp := logDeriv_comp_mul_add hf R c
  have hcomp' : logDeriv (fun z : ℂ => f (z * R + c)) = fun z => R * logDeriv f (c + R * z) := by
    rw [hcomp]
    funext z
    congr 2
    ring
  rw [hcomp']
  rw [iteratedDeriv_const_mul_field]
  rw [iteratedDeriv_affine_at_of_analytic n hδ hR hlog]
  ring

/--
Inputs: a nontrivial character, a positive completed-zero count in the high-real-part range, and a
positive base derivative order.
Claim: some counted zero gives scaled ordinary-L-function Turán data, an explicit derivative lower
bound, and the identity converting that derivative to the original center.
Proof: obtain the zero, center, scale, and canonical factor from the completed-zero-count theorem,
then apply the scaled local Turán derivative estimate.
Role: connects completed zero counts to the large-value family estimate for logarithmic derivatives.
-/
theorem exists_completedZeroCount_scaled_turan_derivative_lower_bound {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ T : ℝ} (hσlower : (29 / 30 : ℝ) ≤ σ)
    (hσupper : σ ≤ 1) (hT : 0 ≤ T)
    (hcount : 0 < PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ hχ σ T)
    (M : ℕ) (hM : 0 < M) :
    ∃ (ρ c : ℂ) (R : ℝ) (z : ℂ) (s : Finset ℂ) (l : ℕ) (gLocal : ℂ → ℂ),
      σ ≤ ρ.re ∧
        ρ.re ≤ 1 ∧
        -T ≤ ρ.im ∧
        ρ.im ≤ T ∧
        DirichletCharacter.completedLFunction χ ρ = 0 ∧
        c.re = 2 - σ ∧
        c.im = ρ.im ∧
        (1 / 8 : ℝ) < R ∧
        R < (1 / 4 : ℝ) ∧
        ‖z‖ < 1 ∧
        DirichletCharacter.LFunction χ (z * (R : ℂ) + c) = 0 ∧
        l ∈ Finset.range s.card ∧
        0 < s.card ∧
        (∀ u,
          u ∈ s ↔
            (MeromorphicOn.divisor (fun w : ℂ => DirichletCharacter.LFunction χ (w * (R : ℂ) + c))
                  (Metric.ball (0 : ℂ) |(1 : ℝ)|))
                u ≠
              0) ∧
        (∀ u ∈ s,
          u ∈ Metric.ball (0 : ℂ) |(1 : ℝ)| ∧
            (MeromorphicOn.divisor (fun w : ℂ => DirichletCharacter.LFunction χ (w * (R : ℂ) + c))
                  (Metric.ball (0 : ℂ) |(1 : ℝ)|))
                u ≠
              0) ∧
        AnalyticOnNhd ℂ gLocal (Metric.ball (0 : ℂ) |(1 : ℝ)|) ∧
        (∀ u : Metric.ball (0 : ℂ) |(1 : ℝ)|, gLocal u ≠ 0) ∧
        ((‖∑ v ∈ s,
                    ((MeromorphicOn.divisor
                          (fun w : ℂ => DirichletCharacter.LFunction χ (w * (R : ℂ) + c))
                          (Metric.ball (0 : ℂ) |(1 : ℝ)|) v :
                        ℤ) :
                      ℂ)‖ /
                (∑ k ∈ Finset.range s.card, (Nat.choose (k + M) k : ℝ) * 2 ^ k)) *
              ((M + l).factorial : ℝ) -
            ((M + l).factorial : ℝ) *
                (192 * (1 / 4 : ℝ) *
                    (Real.log (max (1 : ℝ) (2 * (q : ℝ) * (‖c‖ + R))) -
                        Real.log ‖DirichletCharacter.LFunction χ c‖ +
                      1) /
                  1 ^ 2) /
              (1 / 4 : ℝ) ^ (M + l) -
            ((M + l).factorial : ℝ) *
              (Real.log
                  (max (1 : ℝ) (2 * (q : ℝ) * (‖c‖ + 2 * R)) / ‖DirichletCharacter.LFunction χ c‖) /
                Real.log 2)) ≤
          ‖iteratedDeriv (M + l)
              (logDeriv (fun w : ℂ => DirichletCharacter.LFunction χ (w * (R : ℂ) + c))) 0‖ ∧
        iteratedDeriv (M + l)
            (logDeriv (fun w : ℂ => DirichletCharacter.LFunction χ (w * (R : ℂ) + c))) 0 =
          (R : ℂ) ^ (M + l + 1) *
            iteratedDeriv (M + l) (logDeriv (DirichletCharacter.LFunction χ)) c := by
  obtain
    ⟨ρ, hρσ, hρone, hρlower, hρupper, hzero, c, hcre, hcim, hcL, R, hRlo, hRhi, z, hz, hLzero, g,
      hD, hzf, hcircle, hrem⟩ :=
    exists_scaled_LFunction_data_of_completedZeroCount hq χ hχ hσlower hσupper hT hcount
  have hcRe : 1 ≤ c.re := by
    rw [hcre]
    linarith only [hσupper]
  have hRpos : 0 < R := lt_trans (by norm_num only : (0 : ℝ) < 1 / 8) hRlo
  obtain ⟨s, l, hl, gLocal, hs, hspos, hdomain, hg, hgn, hbound⟩ :=
    exists_scaled_LFunction_turan_derivative_lower_bound hq χ hχ hRpos (le_of_lt hRhi) hcRe hcL hD
      hzf hz hLzero M hM
  have hρlt :=
    PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedLFunction_zero_re_lt_one hχ hzero
  have hσlt : σ < 1 := lt_of_le_of_lt hρσ hρlt
  have hcReGt : 1 < c.re := by
    rw [hcre]
    linarith only [hσlt]
  let δ : ℝ := (c.re - 1) / 2
  have hδpos : 0 < δ := by
    dsimp only [δ]
    linarith only [hcReGt]
  have hδlt : δ < c.re - 1 := by
    dsimp only [δ]
    linarith only [hcReGt]
  have hRnorm : ‖(R : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos]
    exact le_trans (le_of_lt hRhi) (by norm_num only)
  have hlog := analyticOnNhd_logDeriv_LFunction_closedBall χ hχ hδlt
  have hscale :=
    iteratedDeriv_logDeriv_scaled_affine_of_analytic
      (DirichletCharacter.differentiable_LFunction hχ) (c := c) (R := (R : ℂ)) (n := M + l) hδpos
      hRnorm hlog
  exact
    ⟨ρ, c, R, z, s, l, gLocal, hρσ, hρone, hρlower, hρupper, hzero, hcre, hcim, hRlo, hRhi, hz,
      hLzero, hl, hspos, hs, hdomain, hg, hgn, hbound, hscale⟩

/--
Inputs: one occurrence in the primitive-family zero ledger, a real-part threshold in the Turán
range, and a positive base derivative order.

Claim: its character yields a scaled ordinary-L-function zero through the completed-count Turán
estimate, while retaining the positive count and primitive-modulus conditions.

Proof: recover the positive character count from the occurrence ledger and apply the existing
scaled Turán derivative theorem.

Role: connects multiplicity-indexed family zero data to the local zero selected by Turán detection.
-/
theorem exists_primitiveFamilyOccurrence_scaled_LFunction_zero {Q : ℕ} {σ : ℝ} {n : ℕ}
    (hσlower : (29 / 30 : ℝ) ≤ σ) (hσupper : σ ≤ 1)
    {x :
      Σ q : Fin Q,
        Σ χ : DirichletCharacter ℂ (q.val + 1),
          Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)}
    (hx : x ∈ primitiveCharacterFamilyZeroOccurrenceLedger Q σ n) (M : ℕ) (hM : 0 < M) :
    ∃ q : Fin Q,
      ∃ χ : DirichletCharacter ℂ (q.val + 1),
        ∃ hχ : χ ≠ 1,
          χ.IsPrimitive ∧
            1 < q.val + 1 ∧
            0 < completedZeroCount χ hχ σ (n : ℝ) ∧
            ∃ ρ c R z,
              DirichletCharacter.completedLFunction χ ρ = 0 ∧
                c.re = 2 - σ ∧
                c.im = ρ.im ∧
                (1 / 8 : ℝ) < R ∧
                R < (1 / 4 : ℝ) ∧
                ‖z‖ < 1 ∧ DirichletCharacter.LFunction χ (z * (R : ℂ) + c) = 0 := by
  obtain ⟨q, χ, hχ, hprim, hmod, ρ₀, i, hxEq, hcount⟩ :=
    primitiveCharacterFamilyZeroOccurrenceLedger_mem_positive_count hx
  subst x
  obtain
    ⟨ρ, c, R, z, s, l, gLocal, hρσ, hρone, hρlower, hρupper, hzero, hcre, hcim, hRlo, hRhi, hz,
      hLzero, hrest⟩ :=
    @exists_completedZeroCount_scaled_turan_derivative_lower_bound (q.val + 1)
      ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hmod)⟩ hmod χ hχ σ (n : ℝ) hσlower hσupper
      (by exact_mod_cast Nat.zero_le n) hcount M hM
  exact ⟨q, χ, hχ, hprim, hmod, hcount, ρ, c, R, z, hzero, hcre, hcim, hRlo, hRhi, hz, hLzero⟩

/--
Inputs: one primitive-family zero occurrence, a real-part threshold in the Turán range, and a
positive base derivative order.

Claim: the occurrence's character admits a selected derivative order with the explicit scaled
Turán lower bound, together with the identity returning the derivative to the original center.

Proof: obtain a positive completed-zero count from the ledger, apply the scaled Turán estimate,
and retain its lower-bound and affine-scaling conclusions.

Role: provides the derivative data needed to transfer family zero occurrences to finite-height
large-derivative counts.
-/
theorem exists_primitiveFamilyOccurrence_scaled_turan_derivative_bound {Q : ℕ} {σ : ℝ} {n : ℕ}
    (hσlower : (29 / 30 : ℝ) ≤ σ) (hσupper : σ ≤ 1)
    {x :
      Σ q : Fin Q,
        Σ χ : DirichletCharacter ℂ (q.val + 1),
          Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)}
    (hx : x ∈ primitiveCharacterFamilyZeroOccurrenceLedger Q σ n) (M : ℕ) (hM : 0 < M) :
    ∃ q : Fin Q,
      ∃ χ : DirichletCharacter ℂ (q.val + 1),
        ∃ hχ : χ ≠ 1,
          χ.IsPrimitive ∧
            1 < q.val + 1 ∧
            0 < completedZeroCount χ hχ σ (n : ℝ) ∧
            ∃ ρ c R z,
              ∃ s : Finset ℂ,
                ∃ l : ℕ,
                  DirichletCharacter.completedLFunction χ ρ = 0 ∧
                    -(n : ℝ) ≤ ρ.im ∧
                    ρ.im ≤ n ∧
                    c.re = 2 - σ ∧
                    1 < c.re ∧
                    c.im = ρ.im ∧
                    (1 / 8 : ℝ) < R ∧
                    R < (1 / 4 : ℝ) ∧
                    ‖z‖ < 1 ∧
                    DirichletCharacter.LFunction χ (z * (R : ℂ) + c) = 0 ∧
                    l ∈ Finset.range s.card ∧
                    0 < s.card ∧
                    ((‖∑ v ∈ s,
                                ((MeromorphicOn.divisor
                                      (fun w : ℂ =>
                                        DirichletCharacter.LFunction χ (w * (R : ℂ) + c))
                                      (Metric.ball (0 : ℂ) |(1 : ℝ)|) v :
                                    ℤ) :
                                  ℂ)‖ /
                            (∑ k ∈ Finset.range s.card, (Nat.choose (k + M) k : ℝ) * 2 ^ k)) *
                          ((M + l).factorial : ℝ) -
                        ((M + l).factorial : ℝ) *
                            (192 * (1 / 4 : ℝ) *
                                (Real.log (max (1 : ℝ) (2 * ((q.val + 1 : ℕ) : ℝ) * (‖c‖ + R))) -
                                    Real.log ‖DirichletCharacter.LFunction χ c‖ +
                                  1) /
                              1 ^ 2) /
                          (1 / 4 : ℝ) ^ (M + l) -
                        ((M + l).factorial : ℝ) *
                          (Real.log
                              (max (1 : ℝ) (2 * ((q.val + 1 : ℕ) : ℝ) * (‖c‖ + 2 * R)) /
                                ‖DirichletCharacter.LFunction χ c‖) /
                            Real.log 2)) ≤
                      ‖iteratedDeriv (M + l)
                          (logDeriv (fun w : ℂ => DirichletCharacter.LFunction χ (w * (R : ℂ) + c)))
                          0‖ ∧
                    iteratedDeriv (M + l)
                        (logDeriv (fun w : ℂ => DirichletCharacter.LFunction χ (w * (R : ℂ) + c)))
                        0 =
                      (R : ℂ) ^ (M + l + 1) *
                        iteratedDeriv (M + l) (logDeriv (DirichletCharacter.LFunction χ)) c := by
  obtain ⟨q, χ, hχ, hprim, hmod, ρ₀, i, hxEq, hcount⟩ :=
    primitiveCharacterFamilyZeroOccurrenceLedger_mem_positive_count hx
  subst x
  obtain
    ⟨ρ, c, R, z, s, l, gLocal, hρσ, hρone, hρlower, hρupper, hzero, hcre, hcim, hRlo, hRhi, hz,
      hLzero, hrest⟩ :=
    @exists_completedZeroCount_scaled_turan_derivative_lower_bound (q.val + 1)
      ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hmod)⟩ hmod χ hχ σ (n : ℝ) hσlower hσupper
      (by exact_mod_cast Nat.zero_le n) hcount M hM
  rcases hrest with ⟨hl, hspos, _, _, _, _, hbound, hscale⟩
  have hρlt :=
    PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedLFunction_zero_re_lt_one hχ hzero
  have hσlt : σ < 1 := lt_of_le_of_lt hρσ hρlt
  have hcReGt : 1 < c.re := by
    rw [hcre]
    linarith only [hσlt]
  exact
    ⟨q, χ, hχ, hprim, hmod, hcount, ρ, c, R, z, s, l, hzero, hρlower, hρupper, hcre, hcReGt, hcim,
      hRlo, hRhi, hz, hLzero, hl, hspos, hbound, hscale⟩

/--
Inputs: a nontrivial character and nested disks in the right half-plane.
Claim: the completed-function zero mass in the closed inner disk is at most the ordinary
L-function zero mass in the larger open disk, with both sums counted by analytic multiplicity.
Proof: the two functions have equal analytic orders at points with positive real part; disk
containment and nonnegativity then compare the finite divisor sums.
Role: transfers short-strip completed-zero counts to the local zero mass appearing in the Turán
lower bound.
-/
theorem completed_local_divisor_mass_le_LFunction_openBall_mass {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (c : ℂ) {r R : ℝ} (hrR : r < R)
    (hinner : ∀ u ∈ Metric.closedBall c r, 0 < u.re) :
    ((∑ᶠ u : ℂ,
            MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall c r)
              u :
          ℤ) :
        ℝ) ≤
      ((∑ᶠ u : ℂ, MeromorphicOn.divisor (DirichletCharacter.LFunction χ) (Metric.ball c R) u : ℤ) :
        ℝ) := by
  let Fc : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  let Fl : ℂ → ℂ := DirichletCharacter.LFunction χ
  let Uc : Set ℂ := Metric.closedBall c r
  let Ul : Set ℂ := Metric.ball c R
  let dC : ℂ → ℤ := MeromorphicOn.divisor Fc Uc
  let dL : ℂ → ℤ := MeromorphicOn.divisor Fl Ul
  have hFc : AnalyticOnNhd ℂ Fc Uc := by
    intro u hu
    exact (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt u
  have hFlClosed : AnalyticOnNhd ℂ Fl (Metric.closedBall c R) := by
    intro u hu
    exact (DirichletCharacter.differentiable_LFunction hχ).analyticAt u
  have hFl : AnalyticOnNhd ℂ Fl Ul := by
    intro u hu
    exact (DirichletCharacter.differentiable_LFunction hχ).analyticAt u
  have hfiniteC : (dC.support).Finite := by
    exact (MeromorphicOn.divisor Fc Uc).finiteSupport (isCompact_closedBall (x := c) (r := r))
  have hfiniteL : (dL.support).Finite := by
    exact hFlClosed.meromorphicOn.divisor_ball_support_finite
  have hpoint : ∀ u, (dC u : ℝ) ≤ (dL u : ℝ) := by
    intro u
    by_cases hu : u ∈ Uc
    · have huDist : dist u c ≤ r := by
        change u ∈ Metric.closedBall c r at hu
        exact Metric.mem_closedBall.mp hu
      have huL : u ∈ Ul := by
        change dist u c < R
        exact lt_of_le_of_lt huDist hrR
      have horder := completedLFunction_analyticOrderAt_eq_LFunction_of_re_pos χ hχ (hinner u hu)
      have hdiv : dC u = dL u := by
        rw [show dC = MeromorphicOn.divisor Fc Uc from rfl,
          show dL = MeromorphicOn.divisor Fl Ul from rfl,
          MeromorphicOn.AnalyticOnNhd.divisor_apply hFc hu,
          MeromorphicOn.AnalyticOnNhd.divisor_apply hFl huL]
        exact congrArg (fun v : ℕ∞ => (ENat.map (Nat.cast : ℕ → ℤ) v).untop₀) horder
      rw [hdiv]
    · have hzeroC : dC u = 0 := by
        rw [show dC = MeromorphicOn.divisor Fc Uc from rfl,
          (MeromorphicOn.divisor Fc Uc).apply_eq_zero_of_notMem hu]
      rw [hzeroC]
      exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hFl u
  have hsub : Function.support (fun u : ℂ => (dC u : ℝ)) ⊆ (hfiniteL.toFinset : Set ℂ) := by
    intro u hu
    change (dC u : ℝ) ≠ 0 at hu
    apply hfiniteL.mem_toFinset.mpr
    by_contra hnL
    have hz : dL u = 0 := by
      by_contra hne
      exact hnL (by simpa only [Function.mem_support] using hne)
    apply hu
    have hCnonneg : 0 ≤ (dC u : ℝ) := by
      by_cases huC : u ∈ Uc
      · exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hFc u
      · rw [show dC = MeromorphicOn.divisor Fc Uc from rfl,
          (MeromorphicOn.divisor Fc Uc).apply_eq_zero_of_notMem huC]
        norm_num only
    have hCle : (dC u : ℝ) ≤ 0 := by
      have h := hpoint u
      simpa only [hz, Int.cast_zero] using h
    exact le_antisymm hCle hCnonneg
  have hsumC : (∑ᶠ u : ℂ, (dC u : ℝ)) = ∑ u ∈ hfiniteL.toFinset, (dC u : ℝ) := by
    rw [finsum_eq_sum_of_support_subset _ hsub]
  have hsubL : Function.support (fun u : ℂ => (dL u : ℝ)) ⊆ (hfiniteL.toFinset : Set ℂ) := by
    intro u hu
    apply hfiniteL.mem_toFinset.mpr
    by_contra hnL
    have hz : dL u = 0 := by
      by_contra hne
      exact hnL (by simpa only [Function.mem_support] using hne)
    exact hu (by simp only [hz, Int.cast_zero])
  have hsumL : (∑ᶠ u : ℂ, (dL u : ℝ)) = ∑ u ∈ hfiniteL.toFinset, (dL u : ℝ) := by
    rw [finsum_eq_sum_of_support_subset _ hsubL]
  have hcastC : (Int.castRingHom ℝ) (∑ᶠ u : ℂ, dC u) = ∑ᶠ u : ℂ, (dC u : ℝ) :=
    map_finsum (Int.castRingHom ℝ) hfiniteC
  have hcastL : (Int.castRingHom ℝ) (∑ᶠ u : ℂ, dL u) = ∑ᶠ u : ℂ, (dL u : ℝ) :=
    map_finsum (Int.castRingHom ℝ) hfiniteL
  change (Int.castRingHom ℝ) (∑ᶠ u : ℂ, dC u) ≤ (Int.castRingHom ℝ) (∑ᶠ u : ℂ, dL u)
  rw [hcastC, hcastL]
  calc
    ∑ᶠ u : ℂ, (dC u : ℝ) = ∑ u ∈ hfiniteL.toFinset, (dC u : ℝ) := hsumC
    _ ≤ ∑ u ∈ hfiniteL.toFinset, (dL u : ℝ) := by
      apply Finset.sum_le_sum
      intro u hu
      exact hpoint u
    _ = ∑ᶠ u : ℂ, (dL u : ℝ) := hsumL.symm

/--
Inputs: a completed zero rectangle of half-height at most `1/16` and an ordinary `L`-function
center whose real part is `2 - σ`.
Claim: the analytic-multiplicity zero count in this short height slab is at most the ordinary
`L`-function divisor mass in a local open disk of radius greater than `1/8`.
Proof: the real and imaginary coordinate bounds place the rectangle inside the closed disk of
radius `1/8`; transfer its completed divisor mass to the ordinary `L`-function on the larger disk.
Role: connects short-slab family zero counts to the multiplicity weight retained by the local
Turán derivative bound.
-/
theorem completedZeroMultiplicityCountInShortSlab_le_scaledLFunction_openBall_mass {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ t v R : ℝ} (hσlower : (29 / 30 : ℝ) ≤ σ)
    (hσupper : σ ≤ 1) (hv : 0 ≤ v) (hvsmall : v ≤ 1 / 16) (hR : 1 / 8 < R) (c : ℂ)
    (hcre : c.re = 2 - σ) (hcim : c.im = t) :
    completedZeroMultiplicityCountInRectangle χ hχ (⟨σ, t - v⟩ : ℂ) (⟨1, t + v⟩ : ℂ) ≤
      ((∑ᶠ u : ℂ, MeromorphicOn.divisor (DirichletCharacter.LFunction χ) (Metric.ball c R) u : ℤ) :
        ℝ) := by
  have hyord : t - v ≤ t + v := by nlinarith only [hv]
  have hcoord :
    ∀ x ∈ Set.uIcc (⟨σ, t - v⟩ : ℂ).re (⟨1, t + v⟩ : ℂ).re,
      ∀ y ∈ Set.uIcc (⟨σ, t - v⟩ : ℂ).im (⟨1, t + v⟩ : ℂ).im,
        (x - c.re) ^ 2 + (y - c.im) ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := by
    intro x hx y hy
    have hx' : σ ≤ x ∧ x ≤ 1 := by simpa only [Set.uIcc_of_le hσupper, Set.mem_Icc] using hx
    have hy' : t - v ≤ y ∧ y ≤ t + v := by simpa only [Set.uIcc_of_le hyord, Set.mem_Icc] using hy
    have hxl : -(1 / 15 : ℝ) ≤ x - c.re := by
      rw [hcre]
      nlinarith only [hx'.1, hσlower]
    have hxu : x - c.re ≤ 1 / 15 := by
      rw [hcre]
      nlinarith only [hx'.2, hσupper]
    have hyl : -(1 / 16 : ℝ) ≤ y - c.im := by
      rw [hcim]
      linarith only [hy'.1, hvsmall]
    have hyu : y - c.im ≤ 1 / 16 := by
      rw [hcim]
      linarith only [hy'.2, hvsmall]
    nlinarith only [hxl, hxu, hyl, hyu]
  have hcount :=
    completedZeroMultiplicityCountInRectangle_le_ball_divisor_sum_of_coordinates χ hχ _ _ c (1 / 8)
      (by norm_num only) hcoord
  have hcRe : 1 ≤ c.re := by
    rw [hcre]
    linarith only [hσupper]
  have hinner : ∀ u ∈ Metric.closedBall c (1 / 8 : ℝ), 0 < u.re := by
    intro u hu
    have hdist : dist u c ≤ (1 / 8 : ℝ) := Metric.mem_closedBall.mp hu
    have hnorm : ‖u - c‖ ≤ (1 / 8 : ℝ) := by
      rw [dist_eq_norm] at hdist
      exact hdist
    have hreal := Complex.abs_re_le_norm (u - c)
    rw [Complex.sub_re, abs_le] at hreal
    linarith only [hreal.1, hcRe, hnorm]
  have hmass :=
    completed_local_divisor_mass_le_LFunction_openBall_mass (r := (1 / 8 : ℝ)) (R := R) χ hχ c hR
      hinner
  exact hcount.trans hmass

/--
Inputs: a derivative order and normalized main-term and error parameters satisfying `D ≥ 1`,
`A ≥ 1`, and `B ≥ 0`.
Claim: the lower-bound expression obtained by retaining only one zero in the Turán numerator is
strictly negative.
Proof: `D⁻¹ ≤ 1`, `A * 4^n ≥ 1`, and the error term is nonnegative, so the parenthesized term is
at most `-47`.
Role: records why the one-zero weakening of the existing Turán estimate cannot provide a positive
large-value threshold; the live theorem's stronger multiplicity numerator requires a separate
quantitative upper bound before drawing the same conclusion for its full output.
-/
theorem single_zero_turan_lower_bound_is_negative (n : ℕ) {D A B : ℝ} (hD : 1 ≤ D) (hA : 1 ≤ A)
    (hB : 0 ≤ B) : (n.factorial : ℝ) * (D⁻¹ - 48 * A * (4 : ℝ) ^ n - B) < 0 := by
  have hfrac : (1 : ℝ) / D ≤ 1 / 1 := one_div_le_one_div_of_le (by norm_num only) hD
  have hinv' : D⁻¹ ≤ (1 : ℝ)⁻¹ := by simpa only [one_div] using hfrac
  have hinv : D⁻¹ ≤ 1 := by
    rw [show (1 : ℝ)⁻¹ = 1 by norm_num only] at hinv'
    exact hinv'
  have hpow : 1 ≤ (4 : ℝ) ^ n := one_le_pow₀ (by norm_num only)
  have hApos : 0 ≤ A := le_trans (by norm_num only) hA
  have hprod : 1 ≤ A * (4 : ℝ) ^ n := by
    simpa only [one_mul] using mul_le_mul hA hpow (by norm_num only) hApos
  have hinner : D⁻¹ - 48 * A * (4 : ℝ) ^ n - B ≤ -47 := by nlinarith only [hinv, hprod, hB]
  have hfact : 0 < (n.factorial : ℝ) := by positivity
  nlinarith only [hinner, hfact]

/--
Inputs: a nontrivial Dirichlet character, a center in the right half-plane, a positive scale, a
nonzero center value, and a denominator at least one.
Claim: the normalized Turán lower-bound expression obtained from the one-zero contribution is
strictly negative for every derivative order.
Proof: the unconditional bound `norm_lFunction_le_two_mul` makes the first logarithmic error at
least one and the reflection error nonnegative; apply the arithmetic sign lemma above.
Role: verifies the failure of the one-zero threshold using the live unconditional L-function bound.
The mass-retaining output of the full Turán theorem is stronger and needs a separate upper bound on
the local divisor mass before this sign conclusion can be transferred to that full output.
-/
theorem scaled_LFunction_single_zero_turan_bound_negative {q : ℕ} [NeZero q] (hq : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c : ℂ} {R : ℝ} (hR : 0 < R) (hcRe : 1 ≤ c.re)
    (hc : DirichletCharacter.LFunction χ c ≠ 0) (n : ℕ) (D : ℝ) (hD : 1 ≤ D) :
    (n.factorial : ℝ) *
        (D⁻¹ -
          48 *
            (Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + R))) -
                Real.log ‖DirichletCharacter.LFunction χ c‖ +
              1) *
            (4 : ℝ) ^ n -
          Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + 2 * R)) / ‖DirichletCharacter.LFunction χ c‖) /
            Real.log 2) <
      0 := by
  have hnormL : 0 < ‖DirichletCharacter.LFunction χ c‖ := norm_pos_iff.mpr hc
  have hL := norm_lFunction_le_two_mul hq hχ (by linarith only [hcRe] : (1 / 2 : ℝ) ≤ c.re)
  have hU1 : ‖DirichletCharacter.LFunction χ c‖ ≤ max 1 (2 * (q : ℝ) * (‖c‖ + R)) := by
    calc
      ‖DirichletCharacter.LFunction χ c‖ ≤ 2 * (q : ℝ) * ‖c‖ := hL
      _ ≤ 2 * (q : ℝ) * (‖c‖ + R) := by
        apply mul_le_mul_of_nonneg_left
        · linarith only [hR]
        · positivity
      _ ≤ max 1 (2 * (q : ℝ) * (‖c‖ + R)) := le_max_right _ _
  have hlog1 :
    Real.log ‖DirichletCharacter.LFunction χ c‖ ≤ Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + R))) :=
    Real.log_le_log hnormL hU1
  let A : ℝ :=
    Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + R))) - Real.log ‖DirichletCharacter.LFunction χ c‖ + 1
  have hA : 1 ≤ A := by
    dsimp only [A]
    linarith only [hlog1]
  have hU2 : ‖DirichletCharacter.LFunction χ c‖ ≤ max 1 (2 * (q : ℝ) * (‖c‖ + 2 * R)) := by
    calc
      ‖DirichletCharacter.LFunction χ c‖ ≤ 2 * (q : ℝ) * ‖c‖ := hL
      _ ≤ 2 * (q : ℝ) * (‖c‖ + 2 * R) := by
        apply mul_le_mul_of_nonneg_left
        · linarith only [hR]
        · positivity
      _ ≤ max 1 (2 * (q : ℝ) * (‖c‖ + 2 * R)) := le_max_right _ _
  have hratio : 1 ≤ max 1 (2 * (q : ℝ) * (‖c‖ + 2 * R)) / ‖DirichletCharacter.LFunction χ c‖ := by
    rw [le_div_iff₀ hnormL]
    simpa only [one_mul] using hU2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  let B : ℝ :=
    Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + 2 * R)) / ‖DirichletCharacter.LFunction χ c‖) / Real.log 2
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact div_nonneg (Real.log_nonneg hratio) hlog2.le
  exact single_zero_turan_lower_bound_is_negative n hD hA hB

/--
Inputs: a nontrivial Dirichlet character, a scaled center with real part at least one, a scale at
most `1/4`, and a nonzero center value.

Claim: the total analytic multiplicity of zeros of the scaled ordinary `L`-function in the open
unit disk is bounded by its logarithmic Jensen ratio at radius two.

Proof: bound the scaled function on the radius-two circle with `norm_lFunction_le_two_mul`, then
compare the open-ball divisor sum with the closed-ball Jensen sum.

Role: bounds the retained multiplicity in the full Turán derivative lower bound.
-/
theorem scaled_LFunction_openBall_divisor_mass_le {q : ℕ} [NeZero q] (hq : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c : ℂ} {R : ℝ} (hR : 0 < R) (hRle : R ≤ 1 / 4)
    (hcRe : 1 ≤ c.re) (hc : DirichletCharacter.LFunction χ c ≠ 0) :
    ((∑ᶠ u : ℂ,
            MeromorphicOn.divisor (fun z : ℂ => DirichletCharacter.LFunction χ (z * (R : ℂ) + c))
              (Metric.ball (0 : ℂ) 1) u :
          ℤ) :
        ℝ) ≤
      Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + 2 * R)) / ‖DirichletCharacter.LFunction χ c‖) /
        Real.log 2 := by
  let F : ℂ → ℂ := fun z => DirichletCharacter.LFunction χ (z * (R : ℂ) + c)
  let dOpen : ℂ → ℤ := MeromorphicOn.divisor F (Metric.ball (0 : ℂ) 1)
  have hF : Differentiable ℂ F := by
    exact
      (DirichletCharacter.differentiable_LFunction hχ).comp
        ((differentiable_id.mul_const (R : ℂ)).add_const c)
  have h0 : F 0 ≠ 0 := by simpa only [F, zero_mul, zero_add] using hc
  let U : ℝ := max 1 (2 * (q : ℝ) * (‖c‖ + 2 * R))
  have hU : 1 ≤ U := by
    dsimp only [U]; exact le_max_left _ _
  have hbound : ∀ z ∈ Metric.sphere (0 : ℂ) (2 : ℝ), ‖F z‖ ≤ U := by
    intro z hz
    have hzNorm : ‖z‖ = 2 := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
    have hscaled : ‖z * (R : ℂ)‖ = 2 * R := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, hzNorm]
    have hreal : -(2 * R) ≤ (z * (R : ℂ)).re := by
      have habs := Complex.abs_re_le_norm (z * (R : ℂ))
      rw [abs_le] at habs
      rw [hscaled] at habs
      exact habs.1
    have hhalf : (1 / 2 : ℝ) ≤ (z * (R : ℂ) + c).re := by
      rw [Complex.add_re]
      nlinarith only [hcRe, hRle, hreal]
    have hL := norm_lFunction_le_two_mul hq hχ hhalf
    have hnorm : ‖z * (R : ℂ) + c‖ ≤ ‖c‖ + 2 * R := by
      calc
        ‖z * (R : ℂ) + c‖ ≤ ‖z * (R : ℂ)‖ + ‖c‖ := norm_add_le _ _
        _ = ‖c‖ + 2 * R := by
          rw [hscaled]; ring
    have hpoly : ‖F z‖ ≤ 2 * (q : ℝ) * (‖c‖ + 2 * R) := by
      dsimp only [F]
      exact hL.trans (mul_le_mul_of_nonneg_left hnorm (by positivity))
    exact hpoly.trans (le_max_right _ _)
  have hbound' : ∀ z ∈ Metric.sphere (0 : ℂ) (2 * 1), ‖F z‖ ≤ U := by
    intro z hz
    apply hbound z
    simpa only [mul_one] using hz
  have hJensen :=
    PseudoPrime.AnalyticNumberTheory.General.finsum_divisor_closedBall_le_of_sphere_bound hF h0
      (R := 1) (M := U) (by norm_num only) hU hbound'
  have hanalyticClosed : AnalyticOnNhd ℂ F (Metric.closedBall (0 : ℂ) 1) := fun z _ =>
    hF.analyticAt z
  have hanalyticOpen : AnalyticOnNhd ℂ F (Metric.ball (0 : ℂ) 1) := fun z _ => hF.analyticAt z
  have hfinite : dOpen.support.Finite := by
    dsimp only [dOpen]
    exact hanalyticClosed.meromorphicOn.divisor_ball_support_finite
  let S := hfinite.toFinset
  have hsub : Function.support (fun u : ℂ => (dOpen u : ℝ)) ⊆ (S : Set ℂ) := by
    intro u hu
    change (dOpen u : ℝ) ≠ 0 at hu
    apply hfinite.mem_toFinset.mpr
    intro hz
    apply hu
    simp only [hz, Int.cast_zero]
  have hopen : (∑ᶠ u : ℂ, (dOpen u : ℝ)) = ∑ u ∈ S, (dOpen u : ℝ) :=
    finsum_eq_sum_of_support_subset _ hsub
  have hcompare : ∀ u ∈ S, dOpen u = MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) 1) u := by
    intro u hu
    have hne : dOpen u ≠ 0 := by
      intro hz
      apply (Set.Finite.mem_toFinset hfinite).mp hu
      simp only [dOpen, hz]
    have huOpen := (MeromorphicOn.divisor F (Metric.ball (0 : ℂ) 1)).supportWithinDomain hne
    have huClosed : u ∈ Metric.closedBall (0 : ℂ) 1 := by
      exact Metric.mem_closedBall.mpr (Metric.mem_ball.mp huOpen).le
    rw [show dOpen = MeromorphicOn.divisor F (Metric.ball (0 : ℂ) 1) from rfl,
      MeromorphicOn.AnalyticOnNhd.divisor_apply hanalyticOpen huOpen,
      MeromorphicOn.AnalyticOnNhd.divisor_apply hanalyticClosed huClosed]
  have hcast : ((∑ᶠ u : ℂ, dOpen u : ℤ) : ℝ) = ∑ᶠ u : ℂ, (dOpen u : ℝ) :=
    (Int.castRingHom ℝ).toAddMonoidHom.map_finsum hfinite
  have hclosed := PseudoPrime.AnalyticNumberTheory.General.sum_divisor_le_finsum hF 1 S
  have hlogpos : 0 < ‖DirichletCharacter.LFunction χ c‖ := norm_pos_iff.mpr hc
  calc
    ((∑ᶠ u : ℂ, dOpen u : ℤ) : ℝ) = ∑ᶠ u : ℂ, (dOpen u : ℝ) := hcast
    _ = ∑ u ∈ S, (dOpen u : ℝ) := hopen
    _ = ∑ u ∈ S, (MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) 1) u : ℝ) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [hcompare u hu]
    _ ≤ ∑ᶠ u : ℂ, (MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) 1) u : ℝ) := hclosed
    _ ≤ Real.log (U / ‖F 0‖) / Real.log 2 := hJensen
    _ = Real.log (U / ‖DirichletCharacter.LFunction χ c‖) / Real.log 2 := by
      congr 2
      simp only [F, zero_mul, zero_add]
    _ =
        Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + 2 * R)) / ‖DirichletCharacter.LFunction χ c‖) /
          Real.log 2 :=
      by rfl

/-!
## Sign of the current Turán lower-bound expression
-/

/--
Inputs: an entire function and a finite set containing every nonzero value of its divisor on the
open unit disk.
Claim: the norm of the sum of the divisor values on that set is at most the total divisor mass.
Proof: analytic divisor values are nonnegative; compare the finite sum with the finitely supported
sum over the disk.
Role: transfers Jensen's bound for total zero multiplicity to the numerator used in the Turán
estimate.
-/
theorem norm_sum_local_divisor_le_finsum {F : ℂ → ℂ} (hFglobal : AnalyticOnNhd ℂ F Set.univ)
    (s : Finset ℂ)
    (hs : ∀ u, u ∈ s ↔ (MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |(1 : ℝ)|)) u ≠ 0) :
    ‖∑ u ∈ s, ((MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |(1 : ℝ)|) u : ℤ) : ℂ)‖ ≤
      ((∑ᶠ u : ℂ, MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |(1 : ℝ)|) u : ℤ) : ℝ) := by
  let d : ℂ → ℤ := MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |(1 : ℝ)|)
  have hFopen : AnalyticOnNhd ℂ F (Metric.ball (0 : ℂ) |(1 : ℝ)|) := fun z _ => hFglobal z trivial
  have hFclosed : AnalyticOnNhd ℂ F (Metric.closedBall (0 : ℂ) |(1 : ℝ)|) := fun z _ =>
    hFglobal z trivial
  have hfinite : d.support.Finite := by
    dsimp only [d]
    exact hFclosed.meromorphicOn.divisor_ball_support_finite
  have hsub : Function.support (fun u : ℂ => (d u : ℝ)) ⊆ (s : Set ℂ) := by
    intro u hu
    change (d u : ℝ) ≠ 0 at hu
    exact (hs u).2 (Int.cast_ne_zero.mp hu)
  have hfiniteSum : (∑ᶠ u : ℂ, (d u : ℝ)) = ∑ u ∈ s, (d u : ℝ) :=
    finsum_eq_sum_of_support_subset _ hsub
  have hcast : ((∑ᶠ u : ℂ, d u : ℤ) : ℝ) = ∑ᶠ u : ℂ, (d u : ℝ) :=
    (Int.castRingHom ℝ).toAddMonoidHom.map_finsum hfinite
  have hnonneg : ∀ u, 0 ≤ (d u : ℝ) := by
    intro u
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hFopen u
  calc
    ‖∑ u ∈ s, ((d u : ℤ) : ℂ)‖ ≤ ∑ u ∈ s, ‖((d u : ℤ) : ℂ)‖ := norm_sum_le _ _
    _ = ∑ u ∈ s, (d u : ℝ) := by
      apply Finset.sum_congr rfl
      intro u hu
      simp only [Complex.norm_intCast, abs_of_nonneg (hnonneg u)]
    _ = ∑ᶠ u : ℂ, (d u : ℝ) := hfiniteSum.symm
    _ = ((∑ᶠ u : ℂ, d u : ℤ) : ℝ) := hcast.symm

/--
Inputs: a zero in the scaled L-function disk, its canonical factorization, and a positive base
derivative order.
Claim: the normalized lower-bound expression produced by the local Turán estimate is strictly
negative for the selected zero list and derivative order.
Proof: Jensen's zero-mass bound controls the divisor numerator, the Turán denominator is at least
one, and the `48 A 4^n` term dominates after subtracting the matching reflection error.
Role: confirms that the existing formula cannot provide a positive zero-detection threshold.
-/
theorem exists_scaled_LFunction_turan_lower_bound_is_negative {q : ℕ} [NeZero q] (hq : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c : ℂ} {R : ℝ} (hR : 0 < R) (hRle : R ≤ 1 / 4)
    (hcRe : 1 ≤ c.re) (hc : DirichletCharacter.LFunction χ c ≠ 0) {g : ℂ → ℂ}
    (D :
      Complex.ECanonicalDecomp (fun z : ℂ => DirichletCharacter.LFunction χ (z * (R : ℂ) + c)) g 1)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = 1 → DirichletCharacter.LFunction χ (ρ * (R : ℂ) + c) ≠ 0) {z : ℂ}
    (hz : ‖z‖ < 1) (hzero : DirichletCharacter.LFunction χ (z * (R : ℂ) + c) = 0) (M : ℕ)
    (hM : 0 < M) :
    ∃ s : Finset ℂ,
      ∃ l ∈ Finset.range s.card,
        ((M + l).factorial : ℝ) *
            (‖∑ v ∈ s,
                    ((MeromorphicOn.divisor
                          (fun w : ℂ => DirichletCharacter.LFunction χ (w * (R : ℂ) + c))
                          (Metric.ball (0 : ℂ) |(1 : ℝ)|) v :
                        ℤ) :
                      ℂ)‖ /
                (∑ k ∈ Finset.range s.card, (Nat.choose (k + M) k : ℝ) * 2 ^ k) -
              48 *
                (Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + R))) -
                    Real.log ‖DirichletCharacter.LFunction χ c‖ +
                  1) *
                (4 : ℝ) ^ (M + l) -
              Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + 2 * R)) / ‖DirichletCharacter.LFunction χ c‖) /
                Real.log 2) <
          0 := by
  let F : ℂ → ℂ := fun w => DirichletCharacter.LFunction χ (w * (R : ℂ) + c)
  have hF : Differentiable ℂ F := by
    exact
      (DirichletCharacter.differentiable_LFunction hχ).comp
        ((differentiable_id.mul_const (R : ℂ)).add_const c)
  have hFglobal : AnalyticOnNhd ℂ F Set.univ := fun w _ => hF.analyticAt w
  obtain ⟨s, l, hl, gLocal, hs, hspos, _, _, _, _⟩ :=
    exists_scaled_LFunction_turan_derivative_lower_bound hq χ hχ hR hRle hcRe hc D hzf hz hzero M hM
  have hRadius : Metric.ball (0 : ℂ) |(1 : ℝ)| = Metric.ball (0 : ℂ) 1 := by
    congr 1
    norm_num only [abs_of_pos (by norm_num only : (0 : ℝ) < 1)]
  let d : ℂ → ℤ := MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |(1 : ℝ)|)
  have hsum :=
    norm_sum_local_divisor_le_finsum hFglobal s
      (by
        intro u
        exact hs u)
  have hmass := scaled_LFunction_openBall_divisor_mass_le hq χ hχ hR hRle hcRe hc
  have hmass' :
    ((∑ᶠ u : ℂ, MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |(1 : ℝ)|) u : ℤ) : ℝ) ≤
      Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + 2 * R)) / ‖DirichletCharacter.LFunction χ c‖) /
        Real.log 2 := by
    calc
      ((∑ᶠ u : ℂ, MeromorphicOn.divisor F (Metric.ball (0 : ℂ) |(1 : ℝ)|) u : ℤ) : ℝ) =
          ((∑ᶠ u : ℂ, MeromorphicOn.divisor F (Metric.ball (0 : ℂ) 1) u : ℤ) : ℝ) :=
        by rw [hRadius]
      _ ≤ _ := by simpa only [F] using hmass
  have hnum :
    ‖∑ v ∈ s, ((d v : ℤ) : ℂ)‖ ≤
      Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + 2 * R)) / ‖DirichletCharacter.LFunction χ c‖) /
        Real.log 2 := by
    exact hsum.trans hmass'
  have hnormL : 0 < ‖DirichletCharacter.LFunction χ c‖ := norm_pos_iff.mpr hc
  have hL := norm_lFunction_le_two_mul hq hχ (by linarith only [hcRe] : (1 / 2 : ℝ) ≤ c.re)
  have hU1 : ‖DirichletCharacter.LFunction χ c‖ ≤ max 1 (2 * (q : ℝ) * (‖c‖ + R)) := by
    calc
      ‖DirichletCharacter.LFunction χ c‖ ≤ 2 * (q : ℝ) * ‖c‖ := hL
      _ ≤ 2 * (q : ℝ) * (‖c‖ + R) := by
        apply mul_le_mul_of_nonneg_left
        · linarith only [hR]
        · positivity
      _ ≤ max 1 (2 * (q : ℝ) * (‖c‖ + R)) := le_max_right _ _
  have hA :
    1 ≤
      Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + R))) - Real.log ‖DirichletCharacter.LFunction χ c‖ +
        1 := by
    have hlog := Real.log_le_log hnormL hU1
    linarith only [hlog]
  have hden : 1 ≤ ∑ k ∈ Finset.range s.card, (Nat.choose (k + M) k : ℝ) * 2 ^ k := by
    have hzeroMem : 0 ∈ Finset.range s.card := Finset.mem_range.mpr hspos
    have hterm : (Nat.choose (0 + M) 0 : ℝ) * (2 : ℝ) ^ 0 = 1 := by
      simp only [Nat.zero_add, Nat.choose_zero_right, Nat.cast_one, one_mul, pow_zero]
    rw [← hterm]
    exact
      Finset.single_le_sum
        (fun k hk => show 0 ≤ (Nat.choose (k + M) k : ℝ) * (2 : ℝ) ^ k by positivity) hzeroMem
  have hratio :
    ‖∑ v ∈ s, ((d v : ℤ) : ℂ)‖ / (∑ k ∈ Finset.range s.card, (Nat.choose (k + M) k : ℝ) * 2 ^ k) ≤
      Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + 2 * R)) / ‖DirichletCharacter.LFunction χ c‖) /
        Real.log 2 := by
    calc
      _ ≤ ‖∑ v ∈ s, ((d v : ℤ) : ℂ)‖ := div_le_self (norm_nonneg _) hden
      _ ≤ _ := hnum
  have hpow : 1 ≤ (4 : ℝ) ^ (M + l) := one_le_pow₀ (by norm_num only)
  have hprod :
    1 ≤
      (Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + R))) - Real.log ‖DirichletCharacter.LFunction χ c‖ +
          1) *
        (4 : ℝ) ^ (M + l) := by
    simpa only [one_mul] using
      mul_le_mul hA hpow (by norm_num only) (le_trans (by norm_num only) hA)
  have hinner :
    ‖∑ v ∈ s, ((d v : ℤ) : ℂ)‖ / (∑ k ∈ Finset.range s.card, (Nat.choose (k + M) k : ℝ) * 2 ^ k) -
        48 *
          (Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + R))) -
              Real.log ‖DirichletCharacter.LFunction χ c‖ +
            1) *
          (4 : ℝ) ^ (M + l) -
        Real.log (max 1 (2 * (q : ℝ) * (‖c‖ + 2 * R)) / ‖DirichletCharacter.LFunction χ c‖) /
          Real.log 2 ≤
      -48 := by
    nlinarith only [hratio, hprod]
  have hfact : (0 : ℝ) < ((M + l).factorial : ℝ) := by positivity
  refine ⟨s, l, hl, ?_⟩
  nlinarith only [hinner, hfact]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
