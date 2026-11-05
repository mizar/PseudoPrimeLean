/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.TriangularScaleOneSharp
public import PseudoPrime.LLS.PaperStatements.TriangularJointCutoffBounds
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # One-sided Chebyshev control of the joint Abel integrand -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under RH, from 16 to the cutoff in triangular support, the joint Abel integrand
is bounded by the negative derivative of the explicit lower-bound primitive.
The derivative is nonpositive, so the Chebyshev lower estimate has the correct sign. -/
theorem joint_abel_integrand_le (hRH : RiemannHypothesis) {x t : ℝ} (hx : 1 ≤ x)
    (hu : x ≤ Real.exp 36) (ht : 16 ≤ t) (htx : t ≤ x) :
    t ^ (-3 / 2 : ℝ) * ((Real.log x + Real.log t) / 2 - 55) * Chebyshev.psi t ≤
      -(t ^ (-1 / 2 : ℝ) * ((110 - Real.log x - Real.log t) / 2) -
            (19 / 30 : ℝ) * (t ^ (-3 / 4 : ℝ) * ((110 - Real.log x - Real.log t) / 2)) -
            (63 / 10 : ℝ) * (t ^ (-5 / 4 : ℝ) * ((110 - Real.log x - Real.log t) / 2)) +
          (1839 / 1000 : ℝ) * (t ^ (-3 / 2 : ℝ) * ((Real.log x + Real.log t) / 2 - 55))) := by
  have hp : 0 < t := by linarith only [ht]
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hlx := Real.log_le_log hxp hu
  rw [Real.log_exp] at hlx
  have hlt := Real.log_le_log hp htx
  have hd : t ^ (-3 / 2 : ℝ) * ((Real.log x + Real.log t) / 2 - 55) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hp.le _) (by linarith only [hlx, hlt])
  have hm := mul_le_mul_of_nonpos_left (scaleOne_psi_lower hRH ht) hd
  have h1 : t ^ (-3 / 2 : ℝ) * t = t ^ (-1 / 2 : ℝ) := by
    have he := Real.rpow_add hp (-3 / 2) 1
    norm_num only [Real.rpow_one] at he
    simpa only [neg_div] using he.symm
  have h34 : t ^ (-3 / 2 : ℝ) * t ^ (3 / 4 : ℝ) = t ^ (-3 / 4 : ℝ) := by
    rw [← Real.rpow_add hp]
    congr 1
    norm_num only
  have h14 : t ^ (-3 / 2 : ℝ) * t ^ (1 / 4 : ℝ) = t ^ (-5 / 4 : ℝ) := by
    rw [← Real.rpow_add hp]
    congr 1
    norm_num only
  have he :
    (t ^ (-3 / 2 : ℝ) * ((Real.log x + Real.log t) / 2 - 55)) *
        (t - (19 / 30 : ℝ) * t ^ (3 / 4 : ℝ) - (63 / 10 : ℝ) * t ^ (1 / 4 : ℝ) - 1839 / 1000) =
      -(t ^ (-1 / 2 : ℝ) * ((110 - Real.log x - Real.log t) / 2) -
            (19 / 30 : ℝ) * (t ^ (-3 / 4 : ℝ) * ((110 - Real.log x - Real.log t) / 2)) -
            (63 / 10 : ℝ) * (t ^ (-5 / 4 : ℝ) * ((110 - Real.log x - Real.log t) / 2)) +
          (1839 / 1000 : ℝ) * (t ^ (-3 / 2 : ℝ) * ((Real.log x + Real.log t) / 2 - 55))) := by
    calc
      _ =
          -((t ^ (-3 / 2 : ℝ) * t) * ((110 - Real.log x - Real.log t) / 2) -
                (19 / 30 : ℝ) *
                  ((t ^ (-3 / 2 : ℝ) * t ^ (3 / 4 : ℝ)) * ((110 - Real.log x - Real.log t) / 2)) -
                (63 / 10 : ℝ) *
                  ((t ^ (-3 / 2 : ℝ) * t ^ (1 / 4 : ℝ)) * ((110 - Real.log x - Real.log t) / 2)) +
              (1839 / 1000 : ℝ) * (t ^ (-3 / 2 : ℝ) * ((Real.log x + Real.log t) / 2 - 55))) :=
        by ring
      _ = _ := by rw [h1, h34, h14]
  exact hm.trans_eq he

/-- Under RH, bound the joint Abel integral by the explicit primitive evaluated at
16 and the cutoff. The integral below 16 has the required nonpositive sign, while
the relative Chebyshev bound controls the remaining interval. -/
theorem joint_abel_integral_le (hRH : RiemannHypothesis) {x : ℝ} (hx : 16 ≤ x)
    (hu : x ≤ Real.exp 36) :
    (∫ t in (1 : ℝ)..x, t ^ (-3 / 2 : ℝ) * ((Real.log x + Real.log t) / 2 - 55) * Chebyshev.psi t) ≤
      triangular18_jointPrimitive x 16 - triangular18_jointPrimitive x x := by
  let d := fun t : ℝ ↦ t ^ (-3 / 2 : ℝ) * ((Real.log x + Real.log t) / 2 - 55)
  let p := fun t : ℝ ↦
    t ^ (-1 / 2 : ℝ) * ((110 - Real.log x - Real.log t) / 2) -
        (19 / 30 : ℝ) * (t ^ (-3 / 4 : ℝ) * ((110 - Real.log x - Real.log t) / 2)) -
        (63 / 10 : ℝ) * (t ^ (-5 / 4 : ℝ) * ((110 - Real.log x - Real.log t) / 2)) +
      (1839 / 1000 : ℝ) * d t
  have hx1 : (1 : ℝ) ≤ x := by linarith only [hx]
  have hxpos : 0 < x := by linarith only [hx]
  have hlogx : Real.log x ≤ 36 := by
    have h := Real.log_le_log hxpos hu
    simpa only [Real.log_exp] using h
  have hdcont {a b : ℝ} (ha : 1 ≤ a) : ContinuousOn d (Set.Icc a b) := by
    intro t ht
    have hp : 0 < t := by linarith only [ha, ht.1]
    exact
      ((Real.continuousAt_rpow_const t (-3 / 2) (Or.inl hp.ne')).mul
          (((continuousAt_const.add (Real.continuousAt_log hp.ne')).div_const 2).sub
            continuousAt_const)).continuousWithinAt
  have hint {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t ↦ d t * Chebyshev.psi t) MeasureTheory.volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    have h :=
      integrableOn_mul_sum_Icc ArithmeticFunction.vonMangoldt (m := 0) (by linarith only [ha])
        (hdcont (a := a) (b := b) ha).integrableOn_Icc
    simp only [← Chebyshev.psi_eq_sum_Icc] at h
    exact h.mono_set Set.Ioc_subset_Icc_self
  have hcont : ContinuousOn p (Set.Icc 16 x) := by
    intro t ht
    have hp : 0 < t := by linarith only [ht.1]
    have hr (r : ℝ) := Real.continuousAt_rpow_const t r (Or.inl hp.ne')
    have hl := Real.continuousAt_log hp.ne'
    have hk : ContinuousAt (fun z : ℝ ↦ (110 - Real.log x - Real.log z) / 2) t :=
      ((continuousAt_const.sub hl).div_const 2)
    have hdt : ContinuousAt d t :=
      (hr (-3 / 2)).mul (((continuousAt_const.add hl).div_const 2).sub continuousAt_const)
    exact
      ((((hr (-1 / 2)).mul hk).sub (((hr (-3 / 4)).mul hk).const_mul (19 / 30))).sub
            (((hr (-5 / 4)).mul hk).const_mul (63 / 10)) |>.add
          (hdt.const_mul (1839 / 1000))).continuousWithinAt
  have hpint : IntervalIntegrable p MeasureTheory.volume 16 x := hcont.intervalIntegrable_of_Icc hx
  have hprim :
    (∫ t in (16 : ℝ)..x, p t) =
      triangular18_jointPrimitive x x - triangular18_jointPrimitive x 16 := by
    apply
      intervalIntegral.integral_eq_sub_of_hasDerivAt (f := triangular18_jointPrimitive x) (f' := p)
    · intro t ht
      rw [Set.uIcc_of_le hx] at ht
      exact triangular18_jointPrimitive_deriv (by linarith only [ht.1])
    · exact hpint
  have hlo : (∫ t in (1 : ℝ)..16, d t * Chebyshev.psi t) ≤ 0 := by
    have hm :=
      intervalIntegral.integral_mono_on (by norm_num only : (1 : ℝ) ≤ 16)
        (hint (by norm_num only) (by norm_num only)) intervalIntegrable_const
        (fun t ht ↦
          show d t * Chebyshev.psi t ≤ (0 : ℝ)
            by
            have hp : 0 < t := by linarith only [ht.1]
            have hl := Real.log_le_log hp (ht.2.trans hx)
            have hd : d t ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hp.le _)
                (by linarith only [hlogx, hl])
            exact mul_nonpos_of_nonpos_of_nonneg hd (Chebyshev.psi_nonneg t))
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_zero] using hm
  have hhi : (∫ t in (16 : ℝ)..x, d t * Chebyshev.psi t) ≤ -(∫ t in (16 : ℝ)..x, p t) := by
    have hm :=
      intervalIntegral.integral_mono_on hx (hint (by norm_num only) hx) hpint.neg
        (fun t ht ↦ joint_abel_integrand_le hRH hx1 hu ht.1 ht.2)
    change (∫ t in (16 : ℝ)..x, d t * Chebyshev.psi t) ≤ ∫ t in (16 : ℝ)..x, -p t at hm
    rw [intervalIntegral.integral_neg] at hm
    exact hm
  have hsum :=
    intervalIntegral.integral_add_adjacent_intervals
      (hint (by norm_num only) (by norm_num only : (1 : ℝ) ≤ 16)) (hint (by norm_num only) hx)
  rw [hprim] at hhi
  change (∫ t in (1 : ℝ)..x, d t * Chebyshev.psi t) ≤ _
  linarith only [hlo, hhi, hsum]

/-- Evaluate the joint primitive at the lower integration endpoint 16. -/
theorem joint_primitive_sixteen (x : ℝ) :
    triangular18_jointPrimitive x 16 =
      (876653 / 1000 : ℝ) - (98717 / 12000) * (Real.log x + Real.log 16) := by
  have hhalf : (16 : ℝ) ^ (1 / 2 : ℝ) = 4 := by norm_num only
  have hquarter : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by norm_num only
  have hquarterInv : (16 : ℝ) ^ (-1 / 4 : ℝ) = 1 / 2 := by
    rw [neg_div, Real.rpow_neg (by norm_num only), hquarter]
    norm_num only
  have hhalfInv : (16 : ℝ) ^ (-1 / 2 : ℝ) = 1 / 4 := by
    rw [neg_div, Real.rpow_neg (by norm_num only), hhalf]
    norm_num only
  dsimp only [triangular18_jointPrimitive]
  rw [hhalf, hquarter, hquarterInv, hhalfInv]
  ring

/-- At the upper endpoint, combine the Chebyshev lower expression with the joint
primitive. The constant-error terms cancel and the three explicit powers remain. -/
theorem joint_primitive_endpoint {x : ℝ} (hx : 0 < x) :
    ((108 - 2 * Real.log x) * x ^ (-1 / 2 : ℝ)) *
          (x - (19 / 30 : ℝ) * x ^ (3 / 4 : ℝ) - (63 / 10 : ℝ) * x ^ (1 / 4 : ℝ) - 1839 / 1000) +
        triangular18_jointPrimitive x x =
      (220 - 4 * Real.log x) * Real.sqrt x -
          (1064 / 5 - (19 / 5 : ℝ) * Real.log x) * x ^ (1 / 4 : ℝ) +
        (3276 / 5 - (63 / 5 : ℝ) * Real.log x) * x ^ (-1 / 4 : ℝ) := by
  have h1 : x ^ (-1 / 2 : ℝ) * x = Real.sqrt x := by
    have h := Real.rpow_add hx (-1 / 2) 1
    norm_num only [Real.rpow_one] at h
    simpa only [neg_div, Real.sqrt_eq_rpow] using h.symm
  have h2 : x ^ (-1 / 2 : ℝ) * x ^ (3 / 4 : ℝ) = x ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hx]
    congr 1
    norm_num only
  have h3 : x ^ (-1 / 2 : ℝ) * x ^ (1 / 4 : ℝ) = x ^ (-1 / 4 : ℝ) := by
    rw [← Real.rpow_add hx]
    congr 1
    norm_num only
  calc
    _ =
        (108 - 2 * Real.log x) * (x ^ (-1 / 2 : ℝ) * x) + (112 - 2 * Real.log x) * Real.sqrt x -
          (19 / 30 : ℝ) *
            ((108 - 2 * Real.log x) * (x ^ (-1 / 2 : ℝ) * x ^ (3 / 4 : ℝ)) +
              (228 - 4 * Real.log x) * x ^ (1 / 4 : ℝ)) -
          (63 / 10 : ℝ) *
            ((108 - 2 * Real.log x) * (x ^ (-1 / 2 : ℝ) * x ^ (1 / 4 : ℝ)) +
              (-212 + 4 * Real.log x) * x ^ (-1 / 4 : ℝ)) :=
      by
      dsimp only [triangular18_jointPrimitive]
      rw [← Real.sqrt_eq_rpow]
      ring
    _ = _ := by
      rw [h1, h2, h3]; ring

/-- Under RH, the combined finite triangular principal sum satisfies the explicit
joint lower bound from 16 to exp 36. The Abel endpoints, relative Chebyshev error,
and nonnegative inverse-fourth-root remainder are retained before simplification. -/
theorem triangular18_joint_lower (hRH : RiemannHypothesis) {x : ℝ} (hx : 16 ≤ x)
    (hu : x ≤ Real.exp 36) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    (220 - 4 * Real.log x) * Real.sqrt x -
        (1064 / 5 - (19 / 5 : ℝ) * Real.log x) * x ^ (1 / 4 : ℝ) -
        855 ≤
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) x n).re) +
        2 * (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) 1 n).re) := by
  have hx1 : (1 : ℝ) ≤ x := by linarith only [hx]
  have hxpos : 0 < x := by linarith only [hx]
  have hlog : Real.log x ≤ 36 := by
    have h := Real.log_le_log hxpos hu
    simpa only [Real.log_exp] using h
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlog16 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 16 4 32 (27 / 10) 3 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog16
  have hw : 0 ≤ (108 - 2 * Real.log x) * x ^ (-1 / 2 : ℝ) :=
    mul_nonneg (by linarith only [hlog]) (Real.rpow_nonneg hxpos.le _)
  have hpsi := mul_le_mul_of_nonneg_left (scaleOne_psi_lower hRH hx) hw
  have hint := joint_abel_integral_le hRH hx hu
  have he := joint_primitive_endpoint hxpos
  have he16 := joint_primitive_sixteen x
  have hrest : 0 ≤ (3276 / 5 - (63 / 5 : ℝ) * Real.log x) * x ^ (-1 / 4 : ℝ) :=
    mul_nonneg (by linarith only [hlog]) (Real.rpow_nonneg hxpos.le _)
  dsimp only
  rw [triangular18_joint_sum_abel hx1 hu, ← intervalIntegral.integral_of_le hx1]
  nlinarith only [hpsi, hint, he, he16, hlog16, hlog0, hrest]

/-- Under GRH inside the triangular support, a strict joint gap yields an actual
prime dividing the level or lying outside the subgroup. The signed Gamma contribution
is nonpositive and the combined Abel lower bound closes the comparison. -/
theorem exists_prime_joint_interior {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 16 ≤ x)
    (hu : x ≤ Real.exp 36) (hi : 1 ≤ (H.index : ℝ))
    (hgap :
      300000000 * (Real.sqrt x + Real.sqrt x⁻¹) +
          1300000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
          602600000 +
          ((H.index : ℝ) - 1) * ((72 - Real.log x) * Real.log q) <
        (H.index : ℝ) *
          ((220 - 4 * Real.log x) * Real.sqrt x -
            (1064 / 5 - (19 / 5 : ℝ) * Real.log x) * x ^ (1 / 4 : ℝ) -
            855)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ (p ∣ q ∨ ¬NumberTheory.residueInSubgroup q H p) := by
  classical
  by_contra hnone
  have hlarge (p : ℕ) (hp : p.Prime) (hd : p ∣ q) : x < (p : ℝ) := by
    by_contra h
    exact hnone ⟨p, hp, le_of_not_gt h, Or.inl hd⟩
  have hsmall (p : ℕ) (hp : p.Prime) (_ : ¬p ∣ q) (hle : (p : ℝ) ≤ x) :
    NumberTheory.residueInSubgroup q H p := by
    by_contra hout
    exact hnone ⟨p, hp, hle, Or.inr hout⟩
  have hx1 : (1 : ℝ) ≤ x := by linarith only [hx]
  have hlog : Real.log x ≤ 36 := by
    have h := Real.log_le_log (by linarith only [hx]) hu
    simpa only [Real.log_exp] using h
  have hlower := triangular18_joint_lower hGRH.riemann hx hu
  have hl := mul_le_mul_of_nonneg_left hlower (Nat.cast_nonneg H.index)
  have hc := triangular18_joint_interior H hGRH hx1 hlog hlarge hsmall
  have hneg : ((H.index : ℝ) - 1) * (-81 + (3 / 2) * Real.log x) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith only [hi]) (by linarith only [hlog])
  dsimp only at hl hc
  nlinarith only [hl, hc, hneg, hgap]

end PseudoPrime.LLS.PaperStatements
