/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Meromorphic.LogDeriv
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.RCLike
import PseudoPrime.AnalyticNumberTheory.General.CanonicalDecomposition
import PseudoPrime.AnalyticNumberTheory.RiemannXi.OrderOneBound
import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroFiniteness
import PseudoPrime.AnalyticNumberTheory.RiemannXi.HadamardLimit
import PseudoPrime.AnalyticNumberTheory.Gamma.TrigammaSpecialValues
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroContribution
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.TrivialZeroMultiplicity

/-!
# Xi endpoint derivatives and RH zero mass

The kernel-independent Hadamard limit and the endpoint logarithmic derivatives
give `Σρ mρ/|ρ|² = 2 * riemannZeroMass` under RH. Differentiating finite genus sums
also bounds the second logarithmic derivative at zero. The xi/zeta factorization
and the trigamma value at one transfer this bound to zeta residue estimates.
-/

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- `logDeriv riemannXi 0 = log(4π)/2 - 1 - γ/2`.
Differentiate the local xi/zeta factorization at zero using `Γ(1)`, `digamma(1)`,
and `ζ'(0)`, then divide by `ξ(0)=1/2`. Together with the functional equation,
this evaluates both endpoints of the centered logarithmic derivative. -/
theorem logDeriv_riemannXi_zero_eq :
    logDeriv RiemannXi.riemannXi 0 =
      Complex.log (4 * Real.pi) / 2 - 1 - (Real.eulerMascheroniConstant : ℂ) / 2 := by
  have hone_ne : ∀ m : ℕ, (1 : ℂ) ≠ -m := Gamma.one_ne_neg_nat
  have hGamma1ne : Complex.Gamma 1 ≠ 0 := Complex.Gamma_ne_zero hone_ne
  have hΓ1 : HasDerivAt Complex.Gamma (Complex.Gamma 1 * Complex.digamma 1) 1 := by
    have heqg : Complex.Gamma 1 * Complex.digamma 1 = deriv Complex.Gamma 1 := by
      rw [Complex.digamma_def, logDeriv_apply]
      field_simp [hGamma1ne]
    rw [heqg]
    exact (Complex.differentiableAt_Gamma 1 hone_ne).hasDerivAt
  have haffine : HasDerivAt (fun z : ℂ => z / 2 + 1) (1 / 2 : ℂ) 0 := by
    have h1 : HasDerivAt (fun z : ℂ => z / 2) (1 / 2 : ℂ) 0 := by
      simpa only [one_div, id_eq] using (hasDerivAt_id (0 : ℂ)).div_const 2
    simpa only [one_div, hasDerivAt_add_const_iff] using h1.add_const 1
  have hGammaComp :
    HasDerivAt (fun z : ℂ => Complex.Gamma (z / 2 + 1))
      (Complex.Gamma 1 * Complex.digamma 1 * (1 / 2)) 0 := by
    have hraw :=
      HasDerivAt.comp_of_eq (0 : ℂ) hΓ1 haffine (show (1 : ℂ) = (0 : ℂ) / 2 + 1 by norm_num only)
    convert hraw using 1
    rfl
  have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hExp : HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2 : ℂ) 0 := by
    have h1 : HasDerivAt (fun z : ℂ => -z) (-1 : ℂ) 0 := (hasDerivAt_id (0 : ℂ)).neg
    simpa only using h1.div_const 2
  have hPow := hExp.const_cpow (c := (Real.pi : ℂ)) (Or.inl hpiC)
  have hPowMul := hPow.const_mul (2 : ℂ)
  have hD := hPowMul.mul hGammaComp
  have hUfac1 : HasDerivAt (fun z : ℂ => (1 / 2 : ℂ) * (z - 1)) (1 / 2 : ℂ) 0 := by
    have h1 : HasDerivAt (fun z : ℂ => z - 1) (1 : ℂ) 0 := (hasDerivAt_id (0 : ℂ)).sub_const 1
    simpa only [one_div, mul_one] using h1.const_mul (1 / 2 : ℂ)
  have hU := hUfac1.mul hD
  have hζne : riemannZeta 0 ≠ 0 := by
    rw [riemannZeta_zero]; norm_num only
  have hζderiv :=
    (analyticOn_riemannZeta 0
        (by norm_num only [Set.mem_compl_iff, Set.mem_singleton_iff])).differentiableAt.hasDerivAt
  have hUD := hU.mul hζderiv
  have hs1 : (0 : ℂ) ≠ 1 := by norm_num only
  have hsavoid : ∀ n : ℕ, (0 : ℂ) ≠ -2 * (n + 1) := by
    intro n hcontra
    have hcontra' : (0 : ℝ) = -2 * ((n : ℝ) + 1) := by exact_mod_cast hcontra
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have heqf :
    RiemannXi.riemannXi =ᶠ[nhds (0 : ℂ)] fun z : ℂ =>
      ((1 / 2 : ℂ) * (z - 1) * (2 * (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2 + 1))) *
        riemannZeta z :=
    RiemannXi.riemannXi_eventuallyEq_mul_riemannZeta hs1 hsavoid
  have hUDeq :
    ((fun z : ℂ => (1 / 2 : ℂ) * (z - 1)) *
        ((fun y : ℂ => (2 : ℂ) * (Real.pi : ℂ) ^ (-y / 2)) * fun z : ℂ =>
          Complex.Gamma (z / 2 + 1)) *
        riemannZeta) =
      fun z : ℂ =>
      ((1 / 2 : ℂ) * (z - 1) * (2 * (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2 + 1))) *
        riemannZeta z := by
    funext z; rfl
  rw [hUDeq] at hUD
  have hXideriv := hUD.congr_of_eventuallyEq heqf
  have hderivXi0 := hXideriv.deriv
  have hζeval : deriv riemannZeta 0 = Complex.log (2 * Real.pi) * riemannZeta 0 := by
    have h := RiemannXi.logDeriv_riemannZeta_zero
    rw [logDeriv_apply] at h
    exact (div_eq_iff hζne).mp h
  rw [hζeval] at hderivXi0
  norm_num only at hderivXi0
  simp only [Complex.cpow_zero, Complex.Gamma_one] at hderivXi0
  simp only [logDeriv, Pi.div_apply]
  rw [hderivXi0, RiemannXi.riemannXi_zero, riemannZeta_zero, Complex.digamma_one]
  have harg_pos : ∀ x : ℝ, 0 ≤ x → Complex.arg (x : ℂ) = 0 := fun x hx =>
    Complex.arg_ofReal_of_nonneg hx
  have harg2 : Complex.arg (2 : ℂ) = 0 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by simp only [Complex.ofReal_ofNat]]
    exact harg_pos 2 (by norm_num only)
  have hargpi : Complex.arg (Real.pi : ℂ) = 0 := harg_pos Real.pi Real.pi_pos.le
  have hargtwopi : Complex.arg (2 * (Real.pi : ℂ)) = 0 := by
    rw [show (2 : ℂ) * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) from by
        push_cast; ring]
    exact harg_pos (2 * Real.pi) (by positivity)
  have hpi4 : Complex.log (4 * Real.pi) = Complex.log 2 * 2 + Complex.log (Real.pi : ℂ) := by
    have h1 : (4 : ℂ) * (Real.pi : ℂ) = 2 * (2 * (Real.pi : ℂ)) := by ring
    rw [h1,
      Complex.log_mul (by norm_num only) (mul_ne_zero (by norm_num only) hpiC)
        (by
          rw [harg2, hargtwopi]; constructor <;> nlinarith [Real.pi_pos]),
      Complex.log_mul (by norm_num only) hpiC
        (by
          rw [harg2, hargpi]; constructor <;> nlinarith [Real.pi_pos])]
    ring_nf
  rw [show Complex.log (2 * Real.pi) = Complex.log 2 + Complex.log (Real.pi : ℂ) from by
      rw [Complex.log_mul (by norm_num only) hpiC
          (by
            rw [harg2, hargpi]; constructor <;> nlinarith [Real.pi_pos])]]
  rw [hpi4]
  have hpi0 : (Real.pi : ℂ) ^ (0 : ℂ) = 1 := Complex.cpow_zero _
  simp only [hpi0, Pi.mul_apply, Complex.Gamma_one, neg_zero, zero_div, one_mul, mul_one, zero_sub,
    zero_add]
  ring_nf

/-- Under RH, `Σρ mρ/|ρ|² = 2 * riemannZeroMass`.
Combine the centered Hadamard limit with the functional equation and the endpoint
value to get `2 + γ - log(4π)`. Nonnegativity of the sum removes the absolute
value in the definition of `riemannZeroMass`. -/
theorem tsum_riemannXiZeroMultiplicity_invNormSq_eq_two_mul_riemannZeroMass_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    (∑' ρ : ℂ,
        if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0) =
      2 * RiemannXi.riemannZeroMass := by
  have hH := riemannXi_centeredLogDeriv_one_eq_tsum_invNormSq_of_riemannHypothesis hRH
  have hcomb : logDeriv riemannXi 1 - logDeriv riemannXi 0 = -2 * logDeriv riemannXi 0 := by
    rw [logDeriv_riemannXi_one_eq_neg_zero]; ring
  rw [hcomb, logDeriv_riemannXi_zero_eq] at hH
  have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hlog4pi : Complex.log (4 * (Real.pi : ℂ)) = ((Real.log (4 * Real.pi) : ℝ) : ℂ) := by
    rw [show (4 : ℂ) * (Real.pi : ℂ) = ((4 * Real.pi : ℝ) : ℂ) from by
        push_cast; ring]
    exact (Complex.ofReal_log (by positivity)).symm
  rw [hlog4pi] at hH
  have hHreal :
    (∑' ρ : ℂ,
        if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0) =
      2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) := by
    have hcast :
      ((∑' ρ : ℂ,
              if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0 :
            ℝ) :
          ℂ) =
        ((2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) : ℝ) : ℂ) := by
      rw [← hH]; push_cast; ring
    exact_mod_cast hcast
  have hnonneg :
    (0 : ℝ) ≤
      ∑' ρ : ℂ,
        if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0 := by
    apply tsum_nonneg
    intro ρ
    split
    · exact div_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
    · exact le_refl 0
  rw [hHreal] at hnonneg ⊢
  unfold riemannZeroMass
  rw [abs_of_nonpos (by linarith)]
  ring

/-!
### Bounding the second logarithmic derivative at zero under RH

Differentiate finite genus sums at zero and bound their norms by the zero mass.
The finite-radius slope error vanishes along the good-radius sequence.
-/

/-- Under RH, the derivative at zero of the truncated genus sum has norm at
most `2 * riemannZeroMass`: each summand differentiates to `-mρ/ρ²`, and the
triangle inequality bounds the finite sum by the global inverse-square mass. -/
theorem exists_hasDerivAt_riemannXiTruncatedGenusSum_zero_norm_le (hRH : RiemannHypothesis) {R : ℝ}
    (_hR : 0 < R) :
    ∃ D : ℂ, HasDerivAt (riemannXiTruncatedGenusSum R) D 0 ∧ ‖D‖ ≤ 2 * riemannZeroMass := by
  have hanalyticClosed : AnalyticOnNhd ℂ riemannXi (Metric.closedBall (0 : ℂ) R) := fun z _ =>
    differentiable_riemannXi.analyticAt z
  set Dv := MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) with hDv_def
  have hfin : (Function.support Dv).Finite :=
    hanalyticClosed.meromorphicOn.divisor_ball_support_finite
  have h0ne : riemannXi (0 : ℂ) ≠ 0 := by
    rw [riemannXi_zero]; norm_num only
  have hkey : ∀ u ∈ hfin.toFinset, u ∈ Metric.ball (0 : ℂ) R ∧ u ≠ 0 := by
    intro u hu
    rw [Set.Finite.mem_toFinset] at hu
    exact ⟨Dv.supportWithinDomain hu, ne_of_mem_divisorBallSupport_of_riemannXi_ne_zero hu h0ne⟩
  have hsub :
    ∀ s : ℂ,
      Function.support (fun ρ : ℂ => ((Dv ρ : ℤ) : ℂ) * (1 / (s - ρ) + 1 / ρ)) ⊆ hfin.toFinset := by
    intro s u hu
    rw [Function.mem_support] at hu
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    intro hDu0
    apply hu
    rw [hDu0]
    simp only [Int.cast_zero, zero_mul]
  have heq :
    riemannXiTruncatedGenusSum R = fun s : ℂ =>
      ∑ ρ ∈ hfin.toFinset, ((Dv ρ : ℤ) : ℂ) * (1 / (s - ρ) + 1 / ρ) := by
    funext s
    rw [riemannXiTruncatedGenusSum, finsum_eq_sum_of_support_subset _ (hsub s)]
  set D : ℂ := ∑ ρ ∈ hfin.toFinset, ((Dv ρ : ℤ) : ℂ) * (-(1 / ρ ^ 2)) with hD_def
  refine ⟨D, ?_, ?_⟩
  · rw [heq]
    apply HasDerivAt.fun_sum
    intro ρ hρ
    obtain ⟨_, hρne0⟩ := hkey ρ hρ
    have hne' : (0 : ℂ) - ρ ≠ 0 := by
      rw [zero_sub, neg_ne_zero]; exact hρne0
    have hc : HasDerivAt (fun s : ℂ => s - ρ) 1 0 := (hasDerivAt_id (0 : ℂ)).sub_const ρ
    have hinvderiv := hc.inv hne'
    have hval : -(1 : ℂ) / ((0 : ℂ) - ρ) ^ 2 = -(1 / ρ ^ 2) := by
      rw [zero_sub, neg_sq]; ring
    rw [hval] at hinvderiv
    have h2 : HasDerivAt (fun s : ℂ => (1 : ℂ) / (s - ρ)) (-(1 / ρ ^ 2)) 0 := by
      have heq2 : (fun s : ℂ => (1 : ℂ) / (s - ρ)) = (fun s : ℂ => s - ρ)⁻¹ := by
        funext s; rw [Pi.inv_apply, one_div]
      rw [heq2]; exact hinvderiv
    have h3 : HasDerivAt (fun _ : ℂ => (1 : ℂ) / ρ) 0 0 := hasDerivAt_const 0 (1 / ρ)
    have h4 : HasDerivAt (fun s : ℂ => (1 : ℂ) / (s - ρ) + 1 / ρ) (-(1 / ρ ^ 2)) 0 := by
      have hadd := h2.add h3
      have hfun :
        (fun s : ℂ => (1 : ℂ) / (s - ρ)) + (fun _ : ℂ => (1 : ℂ) / ρ) = fun s : ℂ =>
          (1 : ℂ) / (s - ρ) + 1 / ρ := by
        funext s; rfl
      rw [hfun, add_zero] at hadd
      exact hadd
    exact h4.const_mul ((Dv ρ : ℤ) : ℂ)
  · have hzm :=
      tsum_riemannXiZeroMultiplicity_invNormSq_eq_two_mul_riemannZeroMass_of_riemannHypothesis hRH
    have hsummable := summable_riemannXiZeroMultiplicityInvNormSq_of_riemannHypothesis hRH
    have hterm :
      ∀ ρ ∈ hfin.toFinset,
        ‖((Dv ρ : ℤ) : ℂ) * (-(1 / ρ ^ 2))‖ =
          if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0 := by
      intro ρ hρ
      obtain ⟨hρball, hρne0⟩ := hkey ρ hρ
      have hDeq : Dv ρ = (riemannXiZeroMultiplicity ρ : ℤ) :=
        divisor_riemannXi_ball_eq_zeroMultiplicity_of_mem_ball hρball
      have hρzero : riemannXi ρ = 0 := by
        by_contra hcon
        have hmz : riemannXiZeroMultiplicity ρ = 0 := by
          unfold riemannXiZeroMultiplicity analyticOrderNatAt
          rw [analyticOrderAt_eq_zero.mpr (Or.inr hcon)]
          rfl
        have hρ' : Dv ρ ≠ 0 := by
          rw [Set.Finite.mem_toFinset, Function.mem_support] at hρ
          exact hρ
        rw [hDeq, hmz] at hρ'
        exact hρ' (by norm_num only)
      have hDnonneg : (0 : ℝ) ≤ (riemannXiZeroMultiplicity ρ : ℝ) := Nat.cast_nonneg _
      have hnormsq : ‖ρ ^ 2‖ = Complex.normSq ρ := by rw [norm_pow, ← Complex.normSq_eq_norm_sq]
      rw [ite_eq_left hρzero, norm_mul, Complex.norm_intCast, hDeq,
        abs_of_nonneg (by exact_mod_cast hDnonneg), norm_neg, norm_div, norm_one, hnormsq,
        mul_one_div]
      norm_cast
    calc
      ‖D‖ ≤ ∑ ρ ∈ hfin.toFinset, ‖((Dv ρ : ℤ) : ℂ) * (-(1 / ρ ^ 2))‖ := by
        rw [hD_def]; exact norm_sum_le _ _
      _ =
          ∑ ρ ∈ hfin.toFinset,
            if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0 :=
        Finset.sum_congr rfl hterm
      _ ≤
          ∑' ρ : ℂ,
            if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0 :=
        hsummable.sum_le_tsum hfin.toFinset
          (fun ρ _ => by
            split <;> [exact div_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _);
              exact le_refl 0])
      _ = 2 * RiemannXi.riemannZeroMass := hzm

/-- At a zero-free radius `R > 2`, the norm of the second logarithmic derivative
at zero is bounded by twice the RH zero mass plus the finite-radius slope error. -/
theorem norm_deriv_logDeriv_riemannXi_zero_le (hRH : RiemannHypothesis) {R : ℝ} (hR : 2 < R)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → RiemannXi.riemannXi ρ ≠ 0) :
    ‖deriv (logDeriv RiemannXi.riemannXi) 0‖ ≤
      RiemannXi.riemannXiH9eSlopeError R + 2 * RiemannXi.riemannZeroMass := by
  obtain ⟨D, hD, hDnorm⟩ :=
    exists_hasDerivAt_riemannXiTruncatedGenusSum_zero_norm_le hRH
      (lt_trans (by norm_num only : (0 : ℝ) < 2) hR)
  have hsub := RiemannXi.norm_deriv_logDeriv_riemannXi_zero_sub_le hR hzf hD
  calc
    ‖deriv (logDeriv RiemannXi.riemannXi) 0‖ ≤ ‖deriv (logDeriv RiemannXi.riemannXi) 0 - D‖ + ‖D‖ :=
      by
      have := norm_add_le (deriv (logDeriv RiemannXi.riemannXi) 0 - D) D
      simpa only [sub_add_cancel] using this
    _ ≤ RiemannXi.riemannXiH9eSlopeError R + 2 * RiemannXi.riemannZeroMass := add_le_add hsub hDnorm

/-- Under RH, `‖deriv (logDeriv riemannXi) 0‖ ≤ 2 * riemannZeroMass`.
Pass the finite-radius inequality to the good-radius limit, where the slope
error vanishes. No termwise differentiation of an infinite series is needed. -/
theorem norm_deriv_logDeriv_riemannXi_zero_le_two_mul_riemannZeroMass (hRH : RiemannHypothesis) :
    ‖deriv (logDeriv RiemannXi.riemannXi) 0‖ ≤ 2 * RiemannXi.riemannZeroMass := by
  have htendError := RiemannXi.tendsto_riemannXiGoodRadius_H9eSlopeError_atTop
  have htendSum :
    Filter.Tendsto
      (fun n : ℕ =>
        RiemannXi.riemannXiH9eSlopeError (RiemannXi.riemannXiGoodRadius n) +
          2 * RiemannXi.riemannZeroMass)
      Filter.atTop (nhds (0 + 2 * riemannZeroMass)) :=
    htendError.add tendsto_const_nhds
  simp only [zero_add] at htendSum
  have hev :
    ∀ᶠ n : ℕ in Filter.atTop,
      ‖deriv (logDeriv RiemannXi.riemannXi) 0‖ ≤
        RiemannXi.riemannXiH9eSlopeError (RiemannXi.riemannXiGoodRadius n) +
          2 * RiemannXi.riemannZeroMass := by
    filter_upwards with n
    exact
      norm_deriv_logDeriv_riemannXi_zero_le hRH (RiemannXi.riemannXiGoodRadius_gt_two n)
        (RiemannXi.riemannXi_ne_zero_on_goodRadius n)
  exact ge_of_tendsto htendSum hev

/-- The bridge identity:
`deriv (logDeriv PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXi) 0` and
`PseudoPrime.AnalyticNumberTheory.RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero`
differ by the explicit constant `-1 + π²/24`, coming
from differentiating `U`'s closed-form log-derivative (`1/(s-1) - log(π)/2 + digamma(s/2+1)/2`)
at `s = 0` (using
`PseudoPrime.AnalyticNumberTheory.Gamma.deriv_digamma_one_eq : deriv Complex.digamma 1 = π²/6`). -/
theorem deriv_logDeriv_riemannXi_zero_eq :
    deriv (logDeriv riemannXi) 0 =
      (-1 + (Real.pi : ℂ) ^ 2 / 24) + qMinusOneRiemannZetaSecondLogDerivAtZero := by
  have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs1 : (0 : ℂ) ≠ 1 := by norm_num only
  have hsavoid : ∀ n : ℕ, (0 : ℂ) ≠ -2 * (n + 1) := by
    intro n hcontra
    have hcontra' : (0 : ℝ) = -2 * ((n : ℝ) + 1) := by exact_mod_cast hcontra
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have heqf := riemannXi_eventuallyEq_mul_riemannZeta hs1 hsavoid
  have hloc_all := heqf.eventuallyEq_nhds
  have hζne : riemannZeta 0 ≠ 0 := by
    rw [riemannZeta_zero]; norm_num only
  have hζeventually : ∀ᶠ z : ℂ in nhds (0 : ℂ), riemannZeta z ≠ 0 :=
    (analyticAt_riemannZeta_zero.continuousAt).eventually_ne hζne
  have hzone : ∀ᶠ z : ℂ in nhds (0 : ℂ), z ≠ 1 :=
    (continuousAt_id).eventually_ne (by norm_num only [id_eq])
  have hΓpoles : ∀ᶠ z : ℂ in nhds (0 : ℂ), ∀ m : ℕ, z / 2 + 1 ≠ -m := by
    have hcont : ContinuousAt (fun z : ℂ => z / 2 + 1) 0 := by fun_prop
    have hval : (fun z : ℂ => z / 2 + 1) (0 : ℂ) = (1 : ℂ) := by norm_num only
    have hmem :=
      hcont.eventually_mem
        (show Metric.ball (1 : ℂ) (1 / 2) ∈ nhds ((fun z : ℂ => z / 2 + 1) (0 : ℂ)) from by
          rw [hval]; exact Metric.ball_mem_nhds (1 : ℂ) (by norm_num only))
    filter_upwards [hmem] with z hz
    have hball :=
      Gamma.ball_avoids_nonpos_int (c := 1) (r := 1 / 2) (by norm_num only) (by norm_num only)
    have hcast : ((1 : ℝ) : ℂ) = (1 : ℂ) := by simp only [Complex.ofReal_one]
    rw [hcast] at hball
    exact hball (z / 2 + 1) hz
  have hclosedform :
    logDeriv riemannXi =ᶠ[nhds (0 : ℂ)] fun z : ℂ =>
      (1 / (z - 1) - (Complex.log (Real.pi : ℂ)) / 2 + (1 / 2) * Complex.digamma (z / 2 + 1)) +
        logDeriv riemannZeta z := by
    filter_upwards [heqf, hloc_all, hζeventually, hzone, hΓpoles] with z hzval hloc hζz hz1 hΓz
    have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hpowne : (Real.pi : ℂ) ^ (-z / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hpiC)
    have hΓne : Complex.Gamma (z / 2 + 1) ≠ 0 := Complex.Gamma_ne_zero hΓz
    have hζdiff : DifferentiableAt ℂ riemannZeta z :=
      (analyticOn_riemannZeta z hz1).differentiableAt
    have hζderiv : HasDerivAt riemannZeta (deriv riemannZeta z) z := hζdiff.hasDerivAt
    have hExp : HasDerivAt (fun w : ℂ => -w / 2) (-1 / 2 : ℂ) z := by
      have h1 : HasDerivAt (fun w : ℂ => -w) (-1 : ℂ) z := (hasDerivAt_id z).neg
      simpa only [one_div, id_eq] using h1.div_const 2
    have hPow :
      HasDerivAt (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2))
        ((Real.pi : ℂ) ^ (-z / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2)) z :=
      hExp.const_cpow (Or.inl hpiC)
    have hPowMul := hPow.const_mul (2 : ℂ)
    have hGammaComp := RiemannXi.hasDerivAt_Gamma_affine_half hΓz
    have hD := hPowMul.mul hGammaComp
    have hUfac1 : HasDerivAt (fun w : ℂ => (1 / 2 : ℂ) * (w - 1)) (1 / 2 : ℂ) z := by
      have h1 : HasDerivAt (fun w : ℂ => w - 1) (1 : ℂ) z := (hasDerivAt_id z).sub_const 1
      simpa only [one_div, mul_one] using h1.const_mul (1 / 2 : ℂ)
    have hU := hUfac1.mul hD
    have hU' :
      HasDerivAt
        (fun w : ℂ =>
          (1 / 2 : ℂ) * (w - 1) * (2 * (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2 + 1)))
        ((1 / 2 : ℂ) * (2 * (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2 + 1)) +
          (1 / 2 : ℂ) * (z - 1) *
            ((2 * ((Real.pi : ℂ) ^ (-z / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2))) *
                Complex.Gamma (z / 2 + 1) +
              2 * (Real.pi : ℂ) ^ (-z / 2) *
                (Complex.Gamma (z / 2 + 1) * Complex.digamma (z / 2 + 1) * (1 / 2))))
        z := by
      convert hU using 1
    have hUD := hU'.mul hζderiv
    have hUDeq :
      ((fun w : ℂ =>
            (1 / 2 : ℂ) * (w - 1) * (2 * (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2 + 1))) *
          riemannZeta) =
        fun w : ℂ =>
        (1 / 2 : ℂ) * (w - 1) * (2 * (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2 + 1)) *
          riemannZeta w := by
      funext w; rfl
    rw [hUDeq] at hUD
    have hxideriv :
      HasDerivAt RiemannXi.riemannXi
        (((1 / 2 : ℂ) * (2 * (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2 + 1)) +
              (1 / 2 : ℂ) * (z - 1) *
                ((2 * ((Real.pi : ℂ) ^ (-z / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2))) *
                    Complex.Gamma (z / 2 + 1) +
                  2 * (Real.pi : ℂ) ^ (-z / 2) *
                    (Complex.Gamma (z / 2 + 1) * Complex.digamma (z / 2 + 1) * (1 / 2)))) *
            riemannZeta z +
          (1 / 2 : ℂ) * (z - 1) * (2 * (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2 + 1)) *
            deriv riemannZeta z)
        z :=
      hUD.congr_of_eventuallyEq hloc
    have hζval : riemannZeta z ≠ 0 := hζz
    have hFval :
      (1 / 2 : ℂ) * (z - 1) * (2 * (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2 + 1)) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (by norm_num only) hz1') ?_
      exact mul_ne_zero (mul_ne_zero two_ne_zero hpowne) hΓne
    have hxival : RiemannXi.riemannXi z ≠ 0 := by
      rw [hzval]; exact mul_ne_zero hFval hζval
    unfold logDeriv
    change
      deriv RiemannXi.riemannXi z / RiemannXi.riemannXi z =
        1 / (z - 1) - Complex.log (Real.pi : ℂ) / 2 + (1 / 2 : ℂ) * Complex.digamma (z / 2 + 1) +
          deriv riemannZeta z / riemannZeta z
    rw [hxideriv.deriv]
    field_simp [hxival, hz1', hζval, hpowne, hΓne]
    rw [hzval]
    have hGamma : Complex.Gamma (1 + z * (1 / 2 : ℂ)) ≠ 0 := by
      convert hΓne using 1; ring_nf
    field_simp [hxival, hFval, hζval, hpowne, hGamma]
    ring_nf
  have hderiv_eq := hclosedform.deriv_eq
  rw [hderiv_eq]
  have hDeriv1 : HasDerivAt ((fun z : ℂ => z - 1)⁻¹) (-1 : ℂ) (0 : ℂ) := by
    have h1 : HasDerivAt (fun z : ℂ => z - 1) (1 : ℂ) (0 : ℂ) := (hasDerivAt_id (0 : ℂ)).sub_const 1
    have h2 := h1.inv (by norm_num only : (0 : ℂ) - 1 ≠ 0)
    convert h2 using 1
    norm_num only
  have hDeriv2 : HasDerivAt (fun _ : ℂ => -(Complex.log (Real.pi : ℂ)) / 2) (0 : ℂ) (0 : ℂ) :=
    hasDerivAt_const 0 _
  have hDigamma1 : HasDerivAt Complex.digamma ((Real.pi : ℂ) ^ 2 / 6) (1 : ℂ) := by
    have h := Gamma.differentiableAt_digamma_one.hasDerivAt
    rwa [show deriv Complex.digamma 1 = (Real.pi : ℂ) ^ 2 / 6 from Gamma.deriv_digamma_one_eq] at h
  have hDigammaComp :
    HasDerivAt (fun z : ℂ => Complex.digamma (z / 2 + 1)) ((Real.pi : ℂ) ^ 2 / 6 * (1 / 2))
      (0 : ℂ) := by
    have haffine : HasDerivAt (fun z : ℂ => z / 2 + 1) (1 / 2 : ℂ) (0 : ℂ) := by
      have h1 : HasDerivAt (fun z : ℂ => z / 2) (1 / 2 : ℂ) (0 : ℂ) := by
        simpa only [one_div, id_eq] using (hasDerivAt_id (0 : ℂ)).div_const 2
      simpa only [one_div, hasDerivAt_add_const_iff] using h1.add_const 1
    have hraw := HasDerivAt.comp_of_eq (0 : ℂ) hDigamma1 haffine (by norm_num only)
    convert hraw using 1
    rfl
  have hDeriv3 :
    HasDerivAt (fun z : ℂ => (1 / 2 : ℂ) * Complex.digamma (z / 2 + 1))
      ((1 / 2 : ℂ) * ((Real.pi : ℂ) ^ 2 / 6 * (1 / 2))) (0 : ℂ) :=
    hDigammaComp.const_mul _
  have hSum := (hDeriv1.add hDeriv2).add hDeriv3
  have hFinalEq :
    (((fun z : ℂ => z - 1)⁻¹) + (fun _ : ℂ => -(Complex.log (Real.pi : ℂ)) / 2) +
        (fun z : ℂ => (1 / 2 : ℂ) * Complex.digamma (z / 2 + 1))) =
      fun z : ℂ =>
      1 / (z - 1) - Complex.log (Real.pi : ℂ) / 2 + (1 / 2 : ℂ) * Complex.digamma (z / 2 + 1) := by
    funext z
    simp only [Pi.add_apply, Pi.inv_apply, one_div]
    ring
  rw [hFinalEq] at hSum
  have hζdiff0 : DifferentiableAt ℂ (logDeriv riemannZeta) 0 :=
    RiemannXi.differentiableAt_logDeriv_riemannZeta_zero
  have hζderiv0 := hζdiff0.hasDerivAt
  have hcombined := hSum.add hζderiv0
  have hval := hcombined.deriv
  have hgoal_eq :
    deriv
        (fun z : ℂ =>
          (1 / (z - 1) - Complex.log (Real.pi : ℂ) / 2 +
              (1 / 2 : ℂ) * Complex.digamma (z / 2 + 1)) +
            logDeriv riemannZeta z)
        0 =
      -1 - 0 + (1 / 2 : ℂ) * ((Real.pi : ℂ) ^ 2 / 6 * (1 / 2)) +
        deriv (logDeriv riemannZeta) 0 := by
    change
      deriv
          ((fun z : ℂ =>
              1 / (z - 1) - Complex.log (Real.pi : ℂ) / 2 +
                (1 / 2 : ℂ) * Complex.digamma (z / 2 + 1)) +
            logDeriv riemannZeta)
          0 =
        _
    convert hval using 1; ring
  rw [hgoal_eq]
  unfold RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero
  ring

/-! The real part of the zeta second-log-derivative constant is bounded by the
norm estimate for the corresponding `PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXi`
derivative and the bridge above. -/

theorem re_qMinusOneRiemannZetaSecondLogDerivAtZero_le (hRH : RiemannHypothesis) :
    RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re ≤
      1 - Real.pi ^ 2 / 24 + 2 * RiemannXi.riemannZeroMass := by
  have hD := norm_deriv_logDeriv_riemannXi_zero_le_two_mul_riemannZeroMass hRH
  have hre : (deriv (logDeriv RiemannXi.riemannXi) 0).re ≤ 2 * RiemannXi.riemannZeroMass :=
    (Complex.re_le_norm _).trans hD
  have hbridge := deriv_logDeriv_riemannXi_zero_eq
  have hbridge_re := congrArg Complex.re hbridge
  norm_num only [Complex.add_re, Complex.sub_re, Complex.div_re] at hbridge_re
  have hpi2re : ((Real.pi : ℂ) ^ 2).re = Real.pi ^ 2 := by
    simp only [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [hpi2re] at hbridge_re
  norm_num only [Complex.neg_re, Complex.one_re, Complex.natCast_re, Complex.natCast_im,
    Complex.im_ofNat, Complex.normSq_ofNat, Complex.normSq_ofReal, Complex.ofReal_im, mul_zero,
    add_zero] at hbridge_re
  have h24 : Complex.re (24 : ℂ) = 24 := by
    change (24 : ℝ) = 24
    rfl
  rw [h24] at hbridge_re
  linarith

/-- The explicit `π²/24` term and the trivial-zero tail combine into the constant
`1 + 2 * PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannZeroMass`
used by the logarithmic residue ledger. -/
theorem re_qMinusOne_add_logTrivialZeroSeries_le (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    qMinusOneRiemannZetaSecondLogDerivAtZero.re + RiemannZeta.riemannZetaLogTrivialZeroSeries x ≤
      1 + 2 * riemannZeroMass := by
  have hq := re_qMinusOneRiemannZetaSecondLogDerivAtZero_le hRH
  have ht := RiemannZeta.riemannZetaLogTrivialZeroSeries_le_pi_sq_div_twenty_four hx
  linarith

end PseudoPrime.AnalyticNumberTheory.RiemannXi
