/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapGammaSeries
public import PseudoPrime.LLS.ResolventLaplaceWeights

/-! # Scalar Laplace densities and signed Gamma series for adjustable reciprocal kernels -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The real compact inverse profile at positive Mellin scale x, written as
sqrt(1/x)*max(1-(1/x)^h,0)/h. Its clamp retains support without case distinctions.
This is the baseline density for the adjustable reciprocal kernel. -/
noncomputable def reciprocalGapProfile (h x : ℝ) : ℝ :=
  Real.sqrt x⁻¹ * max (1 - x⁻¹ ^ h) 0 / h

/-- For positive gap h and any real scale, the real compact profile is nonnegative.
Use nonnegativity of the square root and clamp. This supplies positivity of the scalar density. -/
theorem reciprocalGapProfile_nonneg {h : ℝ} (hh : 0 < h) (x : ℝ) :
    0 ≤ reciprocalGapProfile h x := by
  exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (le_max_right _ _)) hh.le

/-- For positive gap and scale, the normalized central integral is the real compact profile.
Apply inverse Mellin inversion and the clamped two-pole weight formula.
This identifies the scalar baseline in the signed Gamma series. -/
theorem reciprocalGap_central_weight_integral_eq_real_profile {h x : ℝ} (hh : 0 < h) (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, reciprocalGapCentralWeight h x t) =
      (reciprocalGapProfile h x : ℂ) := by
  rw [reciprocalGap_central_weight_integral_eq_profile hh hx,
    AnalyticNumberTheory.General.twoPoleMellinWeight_eq_clamped hh (inv_pos.mpr hx)]
  rw [← Real.sqrt_eq_rpow]
  rfl

/-- For positive scale and arbitrary real parameters, multiplying the central weight by the
Laplace phase shifts the scale to x*exp(-r/2) and leaves the real factor exp(-c*r).
Expand the complex powers using positive real logarithms.
This evaluates the inner Mellin integral without restrictions on pole coincidences. -/
theorem reciprocalGap_laplace_mul_weight_eq_shift {x : ℝ} (hx : 0 < x) (h c r t : ℝ) :
    Complex.exp (-((c : ℂ) + Complex.I * (t : ℂ) / 2) * (r : ℂ)) *
        reciprocalGapCentralWeight h x t =
      (Real.exp (-c * r) : ℂ) * reciprocalGapCentralWeight h (x * Real.exp (-r / 2)) t := by
  have hs : 0 < x * Real.exp (-r / 2) := mul_pos hx (Real.exp_pos _)
  unfold reciprocalGapCentralWeight
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hs.ne'), ← Complex.ofReal_log hx.le, ←
    Complex.ofReal_log hs.le, Real.log_mul hx.ne' (Real.exp_ne_zero _), Real.log_exp]
  simp only [Complex.ofReal_add, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_div, Complex.ofReal_ofNat]
  have he :
    -((c : ℂ) + Complex.I * (t : ℂ) / 2) * (r : ℂ) + (Real.log x : ℂ) * (Complex.I * (t : ℂ)) =
      -(c : ℂ) * (r : ℂ) + ((Real.log x : ℂ) + -(r : ℂ) / 2) * (Complex.I * (t : ℂ)) := by
    ring
  calc
    _ =
        Analysis.reciprocalGapFunction h (Complex.I * (t : ℂ)) *
          (Complex.exp (-((c : ℂ) + Complex.I * (t : ℂ) / 2) * (r : ℂ)) *
            Complex.exp ((Real.log x : ℂ) * (Complex.I * (t : ℂ)))) :=
      by ring
    _ = _ := by
      rw [← Complex.exp_add, he, Complex.exp_add]; ring

/-- The real scalar density exp(-c*r) times the compact profile at x*exp(-r/2).
For positive h it is nonnegative and its support on the positive half-line is bounded.
Its integral represents the resolvent even when the rational poles coincide. -/
noncomputable def reciprocalGapResolventDensity (h c x r : ℝ) : ℝ :=
  Real.exp (-c * r) * reciprocalGapProfile h (x * Real.exp (-r / 2))

/-- For positive gap and scale, the normalized inner Laplace-weighted Mellin integral equals
the real scalar density at every real c and r. Shift the scale and use inverse Mellin
inversion. This discharges the inner evaluation in the absolute Fubini representation. -/
theorem reciprocalGap_laplace_inner_integral_eq_density {h x : ℝ} (hh : 0 < h) (hx : 0 < x)
    (c r : ℝ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          Complex.exp (-((c : ℂ) + Complex.I * (t : ℂ) / 2) * (r : ℂ)) *
            reciprocalGapCentralWeight h x t) =
      (reciprocalGapResolventDensity h c x r : ℂ) := by
  have hI :
    (∫ t : ℝ,
        Complex.exp (-((c : ℂ) + Complex.I * (t : ℂ) / 2) * (r : ℂ)) *
          reciprocalGapCentralWeight h x t) =
      (Real.exp (-c * r) : ℂ) *
        (∫ t : ℝ, reciprocalGapCentralWeight h (x * Real.exp (-r / 2)) t) := by
    rw [← MeasureTheory.integral_const_mul]
    exact
      MeasureTheory.integral_congr_ae
        (MeasureTheory.ae_of_all _ (fun t ↦ reciprocalGap_laplace_mul_weight_eq_shift hx h c r t))
  rw [hI, mul_left_comm,
    reciprocalGap_central_weight_integral_eq_real_profile hh (mul_pos hx (Real.exp_pos _))]
  simp only [reciprocalGapResolventDensity, Complex.ofReal_mul]

/-- For positive gap, resolvent coordinate and scale, the normalized reciprocal-weighted
Mellin integral equals the scalar density integrated over the positive half-line.
Apply the kernel-independent absolute Fubini theorem and the evaluated inner integral.
No noncoincidence hypothesis on the rational poles is required. -/
theorem reciprocalGap_resolvent_integral_eq_scalar {h c x : ℝ} (hh : 0 < h) (hc : 0 < c)
    (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, (1 / ((c : ℂ) + Complex.I * (t : ℂ) / 2)) * reciprocalGapCentralWeight h x t) =
      ∫ r : ℝ in Set.Ioi 0, (reciprocalGapResolventDensity h c x r : ℂ) := by
  rw [resolvent_integral_eq_laplace_weight hc (reciprocalGapCentralWeight h x)
      (continuous_reciprocalGapCentralWeight hh hx) (integrable_reciprocalGapCentralWeight hh hx),
    ← MeasureTheory.integral_const_mul]
  exact
    MeasureTheory.integral_congr_ae
      (MeasureTheory.ae_of_all _
        (fun r ↦ reciprocalGap_laplace_inner_integral_eq_density hh hx c r))

/-- For positive gap the scalar resolvent density is nonnegative for all real c,x,r.
Multiply the positive exponential by the nonnegative profile.
This preserves individual resolvent signs in subsequent Gamma comparisons. -/
theorem reciprocalGapResolventDensity_nonneg {h : ℝ} (hh : 0 < h) (c x r : ℝ) :
    0 ≤ reciprocalGapResolventDensity h c x r := by
  exact mul_nonneg (Real.exp_pos _).le (reciprocalGapProfile_nonneg hh _)

/-- For positive gap, coordinate and scale, the scalar density is integrable on the positive
half-line. Take the real part of the absolutely integrable product's inner integral and
use the exact density evaluation. No scalar integrability assumption remains. -/
theorem integrableOn_reciprocalGapResolventDensity {h c x : ℝ} (hh : 0 < h) (hc : 0 < c)
    (hx : 0 < x) :
    MeasureTheory.IntegrableOn (reciprocalGapResolventDensity h c x) (Set.Ioi 0) := by
  have hInt :=
    ((integrable_resolvent_laplace_mul_weight hc (reciprocalGapCentralWeight h x)
            (continuous_reciprocalGapCentralWeight hh hx)
            (integrable_reciprocalGapCentralWeight hh hx)).integral_prod_left.const_mul
        (((1 / (2 * Real.pi) : ℝ) : ℂ))).re
  exact
    hInt.congr
      (MeasureTheory.ae_of_all _
        (fun r ↦ by
          change
            (((1 / (2 * Real.pi) : ℝ) : ℂ) *
                  (∫ t : ℝ,
                    Complex.exp (-((c : ℂ) + Complex.I * (t : ℂ) / 2) * (r : ℂ)) *
                      reciprocalGapCentralWeight h x t)).re =
              reciprocalGapResolventDensity h c x r
          rw [reciprocalGap_laplace_inner_integral_eq_density hh hx c r]
          exact Complex.ofReal_re _))

/-- The normalized resolvent integral is the real density integral embedded in the complex
numbers, for positive gap, coordinate and scale. Commute the real embedding with integration.
This allows real integral inequalities to be used in the Gamma-series comparison. -/
theorem reciprocalGap_resolvent_integral_eq_real {h c x : ℝ} (hh : 0 < h) (hc : 0 < c)
    (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, (1 / ((c : ℂ) + Complex.I * (t : ℂ) / 2)) * reciprocalGapCentralWeight h x t) =
      ((∫ r : ℝ in Set.Ioi 0, reciprocalGapResolventDensity h c x r) : ℝ) := by
  rw [reciprocalGap_resolvent_integral_eq_scalar hh hc hx, ← integral_complex_ofReal]

/-- For positive gap, coordinate and scale, the actual reciprocal-weighted central kernel
is integrable. Subtract the already integrable reciprocal difference from the constant
multiple of the central weight. This justifies splitting each signed difference integral. -/
theorem integrable_reciprocalGapCentralReciprocalWeight {h c x : ℝ} (hh : 0 < h) (hc : 0 < c)
    (hx : 0 < x) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        (1 / ((c : ℂ) + Complex.I * (t : ℂ) / 2)) * reciprocalGapCentralWeight h x t) := by
  have hD :=
    (quadratic_weight_vertical_resolvent_integral_bound hc (reciprocalGapCentralWeight h x)
        (continuous_reciprocalGapCentralWeight hh hx)
        (norm_reciprocalGapCentralWeight_le hh.le hx)).1
  have hW := (integrable_reciprocalGapCentralWeight hh hx).const_mul (1 / (c : ℂ))
  exact
    (hW.sub hD).congr
      (MeasureTheory.ae_of_all _
        (fun t ↦ by
          simp only [Pi.sub_apply]
          ring))

/-- For positive parameters, each normalized reciprocal-difference integral equals the real
profile divided by c minus the scalar density integral. Split only integrable terms and
use both exact inverse formulas. This is the signed scalar summand of the Gamma series. -/
theorem reciprocalGap_resolvent_difference_integral_eq_real {h c x : ℝ} (hh : 0 < h) (hc : 0 < c)
    (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (1 / (c : ℂ) - 1 / ((c : ℂ) + Complex.I * (t : ℂ) / 2)) *
            reciprocalGapCentralWeight h x t) =
      ((reciprocalGapProfile h x / c - ∫ r : ℝ in Set.Ioi 0, reciprocalGapResolventDensity h c x r :
          ℝ) :
        ℂ) := by
  have hE (t : ℝ) :
    (1 / (c : ℂ) - 1 / ((c : ℂ) + Complex.I * (t : ℂ) / 2)) * reciprocalGapCentralWeight h x t =
      (1 / (c : ℂ)) * reciprocalGapCentralWeight h x t -
        (1 / ((c : ℂ) + Complex.I * (t : ℂ) / 2)) * reciprocalGapCentralWeight h x t := by
    ring
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hE),
    MeasureTheory.integral_sub ((integrable_reciprocalGapCentralWeight hh hx).const_mul _)
      (integrable_reciprocalGapCentralReciprocalWeight hh hc hx),
    MeasureTheory.integral_const_mul, mul_sub, mul_left_comm _ (1 / (c : ℂ)) _,
    reciprocalGap_central_weight_integral_eq_real_profile hh hx,
    reciprocalGap_resolvent_integral_eq_real hh hc hx]
  simp only [Complex.ofReal_sub, div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv, mul_one,
    mul_comm]

/-- For positive gap and scale at most one, the compact profile vanishes.
The inverse scale has h-th power at least one, so the clamp is zero.
This identifies the finite support of the resolvent density. -/
theorem reciprocalGapProfile_eq_zero_of_le_one {h x : ℝ} (hh : 0 < h) (hx : 0 < x) (hx1 : x ≤ 1) :
    reciprocalGapProfile h x = 0 := by
  have hi : (1 : ℝ) ≤ x⁻¹ := by
    have hi' : (1 : ℝ) ≤ 1 / x := (le_div_iff₀ hx).mpr (by simpa only [one_mul] using hx1)
    simpa only [one_div] using hi'
  rw [reciprocalGapProfile, max_eq_right (sub_nonpos.mpr (Real.one_le_rpow hi hh.le)), mul_zero,
    zero_div]

/-- For positive gap and scale, the scalar density vanishes when log(x)<=r/2.
The shifted scale is then at most one. This cuts off the half-line convolution at 2 log(x). -/
theorem reciprocalGapResolventDensity_eq_zero_of_log_le_half {h x : ℝ} (hh : 0 < h) (hx : 0 < x)
    (c r : ℝ) (hr : Real.log x ≤ r / 2) : reciprocalGapResolventDensity h c x r = 0 := by
  have hpos : 0 < x * Real.exp (-r / 2) := mul_pos hx (Real.exp_pos _)
  have hl : Real.log (x * Real.exp (-r / 2)) ≤ 0 := by
    rw [Real.log_mul hx.ne' (Real.exp_ne_zero _), Real.log_exp]
    linarith only [hr]
  have he := Real.exp_le_exp.mpr hl
  rw [Real.exp_log hpos, Real.exp_zero] at he
  rw [reciprocalGapResolventDensity, reciprocalGapProfile_eq_zero_of_le_one hh hpos he, mul_zero]

/-- For every character, a parity base b in [1/4,1] expresses the real central Gamma integral
at all positive gaps and scales as its real compact baseline plus half the scalar series.
Replace each reciprocal integral by its real density and commute the real embedding with
the convergent sum. This preserves cancellations instead of taking absolute values. -/
theorem reciprocalGap_central_gammaIntegral_re_eq_scalar_series {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    ∃ b : ℝ,
      1 / 4 ≤ b ∧
        b ≤ 1 ∧
        ∀ {h x : ℝ},
          0 < h →
            0 < x →
            (((1 / (2 * Real.pi) : ℝ) : ℂ) *
                  (∫ t : ℝ,
                    logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
                      reciprocalGapCentralWeight h x t)).re =
              ((-Complex.log Real.pi + Complex.digamma (b : ℂ)) / 2).re * reciprocalGapProfile h x +
                (1 / 2 : ℝ) *
                  ∑' n : ℕ,
                    (reciprocalGapProfile h x / (b + n) -
                      ∫ r : ℝ in Set.Ioi 0, reciprocalGapResolventDensity h (b + n) x r) := by
  obtain ⟨b, hb, hb1, h⟩ := reciprocalGap_central_gammaIntegral_eq_resolvent_series χ
  refine ⟨b, hb, hb1, ?_⟩
  intro hGap x hh hx
  have hb0 : 0 < b := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1 / 4) hb
  let C : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  let J := fun n : ℕ ↦
    ∫ t : ℝ,
      (1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) *
        reciprocalGapCentralWeight hGap x t
  let F := fun n : ℕ ↦
    reciprocalGapProfile hGap x / (b + n) -
      ∫ r : ℝ in Set.Ioi 0, reciprocalGapResolventDensity hGap (b + n) x r
  have hJ : C * (∑' n : ℕ, J n) = ((∑' n : ℕ, F n) : ℝ) := by
    rw [← tsum_mul_left, Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    simpa only [C, J, F, mul_div_assoc] using
      reciprocalGap_resolvent_difference_integral_eq_real hh
        (add_pos_of_pos_of_nonneg hb0 (Nat.cast_nonneg n)) hx
  have he := h hh hx
  rw [← reciprocalGap_central_weight_integral_eq_profile hh hx,
    reciprocalGap_central_weight_integral_eq_real_profile hh hx] at he
  have he' :
    C *
        (∫ t : ℝ,
          logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * reciprocalGapCentralWeight hGap x t) =
      ((-Complex.log Real.pi + Complex.digamma (b : ℂ)) / 2) * (reciprocalGapProfile hGap x : ℂ) +
        (1 / 2 : ℂ) * (C * (∑' n : ℕ, J n)) := by
    rw [he]
    dsimp only [C, J]
    ring
  rw [he', hJ]
  norm_num only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re, Complex.one_im, zero_div,
    div_self (by norm_num only : (2 : ℝ) ≠ 0)]
  rfl

/-- For a character of nonzero level and scales at least one, the real completed remainder
minus its pole and left contributions has the exact signed scalar Gamma series.
Rewrite the proved central-line identity and apply the scalar decomposition.
This connects the coincident-pole-safe representation to the actual witness remainder. -/
theorem reciprocalGap_remainder_sub_pole_left_re_eq_scalar_series {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ∃ b : ℝ,
      1 / 4 ≤ b ∧
        b ≤ 1 ∧
        ∀ {h x : ℝ} (hh : 0 < h),
          1 ≤ x →
            (reciprocalGapCompletedRemainder h hh χ x -
                  MellinKernel.weightedResidue (reciprocalGapMellinKernel h hh)
                    (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2) -
                  reciprocalGapLeftIntegral h hh χ x).re =
              ((-Complex.log Real.pi + Complex.digamma (b : ℂ)) / 2).re * reciprocalGapProfile h x +
                (1 / 2 : ℝ) *
                  ∑' n : ℕ,
                    (reciprocalGapProfile h x / (b + n) -
                      ∫ r : ℝ in Set.Ioi 0, reciprocalGapResolventDensity h (b + n) x r) := by
  obtain ⟨b, hb, hb1, hseries⟩ := reciprocalGap_central_gammaIntegral_re_eq_scalar_series χ
  refine ⟨b, hb, hb1, ?_⟩
  intro h x hh hx
  rw [reciprocalGap_remainder_sub_pole_left_eq_central_gamma hh χ hx]
  exact hseries hh (zero_lt_one.trans_le hx)

/-- For positive scale, rewrite the scalar density using explicit real exponentials and a
clamp, isolating the decay c-1/4 and the gap h. Factor the inverse shifted scale and square
root and simplify its h-th power. This prepares finite-interval scalar estimates. -/
theorem reciprocalGapResolventDensity_eq_exp_clamped {h x : ℝ} (hx : 0 < x) (c r : ℝ) :
    reciprocalGapResolventDensity h c x r =
      Real.sqrt x⁻¹ * Real.exp (-(c - 1 / 4) * r) * max (1 - x⁻¹ ^ h * Real.exp (h * r / 2)) 0 /
        h := by
  have hE : (Real.exp (-r / 2))⁻¹ = Real.exp (r / 2) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have hS : Real.sqrt (Real.exp (r / 2)) = Real.exp (r / 4) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
    congr 1
    ring
  have hpow : Real.exp (r / 2) ^ h = Real.exp (h * r / 2) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  unfold reciprocalGapResolventDensity reciprocalGapProfile
  rw [mul_inv, hE, Real.sqrt_mul (inv_pos.mpr hx).le, hS,
    Real.mul_rpow (inv_pos.mpr hx).le (Real.exp_pos _).le, hpow]
  have he : -c * r + r / 4 = -(c - 1 / 4) * r := by ring
  calc
    _ =
        Real.sqrt x⁻¹ * (Real.exp (-c * r) * Real.exp (r / 4)) *
            max (1 - x⁻¹ ^ h * Real.exp (h * r / 2)) 0 /
          h :=
      by ring
    _ = _ := by rw [← Real.exp_add, he]

/-- For positive gap, base and scale, the real signed scalar differences form a summable
series. The exact scalar inverse formula identifies their absolute values with normalized
complex integral norms, bounded by the already summable integrated absolute norms.
This makes convergence of the final real Gamma series explicit. -/
theorem summable_reciprocalGap_scalar_resolvent_difference {h b x : ℝ} (hh : 0 < h) (hb : 0 < b)
    (hx : 0 < x) :
    Summable
      (fun n : ℕ ↦
        reciprocalGapProfile h x / (b + n) -
          ∫ r : ℝ in Set.Ioi 0, reciprocalGapResolventDensity h (b + n) x r) := by
  have hs :=
    summable_quadratic_weight_resolvent_integral_norm hb (reciprocalGapCentralWeight h x)
      (continuous_reciprocalGapCentralWeight hh hx) (norm_reciprocalGapCentralWeight_le hh.le hx)
  apply Summable.of_norm_bounded hs
  intro n
  have he :=
    congrArg norm
      (reciprocalGap_resolvent_difference_integral_eq_real hh
        (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg n)) hx)
  have hd : ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos zero_lt_one (mul_pos (by norm_num only : (0 : ℝ) < 2) Real.pi_pos))]
  rw [norm_mul, hd, Complex.norm_real] at he
  rw [← he]
  have hn :=
    MeasureTheory.norm_integral_le_integral_norm (μ := MeasureTheory.volume)
      (fun t : ℝ ↦
        (1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t : ℂ) / 2)) *
          reciprocalGapCentralWeight h x t)
  have hm :=
    mul_le_mul_of_nonneg_left hn
      (div_nonneg zero_le_one (mul_pos (by norm_num only : (0 : ℝ) < 2) Real.pi_pos).le)
  simpa only [div_eq_mul_inv, one_mul, mul_comm, mul_assoc] using hm

end PseudoPrime.LLS.PaperStatements
