/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCounting
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.GoodHeight
import Mathlib.Analysis.Meromorphic.FactorizedRational

/-!
# Logarithmic derivatives at good heights

Extract the finitely many zeros in a disk, leaving an analytic nonvanishing
factor. Continuity upgrades the codiscrete factorization to equality throughout
the ball. A holomorphic logarithmic primitive, good-radius boundary separation,
and Borel–Carathéodory estimates bound this factor's logarithmic derivative.
At good heights the zero terms are also controlled, yielding the final
`O(log(T+2)²)` bound on `-1/2 ≤ Re s ≤ 2`.
-/

noncomputable section


namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- `ζ` factors on `ball z R` as a finite product over its zeros there times an analytic
function `g` that is zero-free on all of `ball z R`. -/
theorem exists_riemannZeta_zeroFree_factorization {z : ℂ} {R : ℝ} (hR : 0 < R)
    (hz1 : ∀ w ∈ Metric.closedBall z R, w ≠ 1) :
    ∃ (S : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
      AnalyticOnNhd ℂ g (Metric.ball z R) ∧
        (∀ w ∈ Metric.ball z R, g w ≠ 0) ∧
        (∀ u ∈ S, 0 < m u) ∧
        (∀ u ∈ S, u ∈ Metric.ball z R) ∧
        (∀ u ∈ S, riemannZeta u = 0) ∧
        (∀ u ∈ S, (m u : ℤ) = MeromorphicOn.divisor riemannZeta (Metric.ball z R) u) ∧
        Set.EqOn riemannZeta (fun w => (∏ u ∈ S, (w - u) ^ m u) * g w) (Metric.ball z R) := by
  set U := Metric.ball z R with hU_def
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hzU : z ∈ U := Metric.mem_ball_self hR
  have hUclosed : U ⊆ Metric.closedBall z R := Metric.ball_subset_closedBall
  have hAnClosed : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall z R) := fun w hw =>
    analyticOn_riemannZeta w (hz1 w hw)
  have hAn : AnalyticOnNhd ℂ riemannZeta U := fun w hw => hAnClosed w (hUclosed hw)
  have h1f : MeromorphicOn riemannZeta U := hAn.meromorphicOn
  have h2f : ∀ u : U, meromorphicOrderAt riemannZeta (u : ℂ) ≠ ⊤ := by
    intro u htop
    have hmero := (hAn u.1 u.2).meromorphicOrderAt_eq
    rw [hmero] at htop
    apply
      analyticOrderAt_riemannZeta_ne_top
        (hz1 u.1 (hUclosed u.2))
    rw [← ENat.map_top (Nat.cast : ℕ → ℤ)] at htop
    exact ENat.map_natCast_injective.eq_iff.mp htop
  have h3f : (MeromorphicOn.divisor riemannZeta U).support.Finite :=
    MeromorphicOn.divisor_ball_support_finite hAnClosed.meromorphicOn
  obtain ⟨g, hgAn, hgne, heq⟩ := MeromorphicOn.extract_zeros_poles h1f h2f h3f
  have hdivnn : ∀ u : ℂ, (0 : ℤ) ≤ MeromorphicOn.divisor riemannZeta U u := fun u =>
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn u
  set S : Finset ℂ := h3f.toFinset with hS_def
  set m : ℂ → ℕ := fun u => (MeromorphicOn.divisor riemannZeta U u).toNat with hm_def
  set P : ℂ → ℂ := fun x => ∏ u ∈ S, (x - u) ^ m u with hP_def
  set φ : ℂ → ℂ := fun x => ∏ᶠ u, (x - u) ^ MeromorphicOn.divisor riemannZeta U u with hφ_def
  have hφP : φ = P := by
    funext x
    have hsub :
      Function.mulSupport (fun u => (x - u) ^ MeromorphicOn.divisor riemannZeta U u) ⊆ ↑S := by
      intro u hu
      simp only [Function.mem_mulSupport] at hu
      rw [hS_def, Finset.mem_coe, Set.Finite.mem_toFinset]
      intro hcon
      exact
        hu
          (by
            rw [hcon]; simp only [zpow_ofNat, pow_zero])
    change (∏ᶠ u, (x - u) ^ MeromorphicOn.divisor riemannZeta U u) = ∏ u ∈ S, (x - u) ^ m u
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
    apply Finset.prod_congr rfl
    intro u _
    rw [show MeromorphicOn.divisor riemannZeta U u =
      ((MeromorphicOn.divisor riemannZeta U u).toNat : ℤ) from
        (Int.toNat_of_nonneg (hdivnn u)).symm,
      zpow_natCast]
  have hPAn : AnalyticOnNhd ℂ P Set.univ := by
    intro x _
    have heq : P = ∏ u ∈ S, fun y => (y - u) ^ m u := by
      rw [hP_def]; funext y; rw [Finset.prod_apply]
    rw [heq]
    apply Finset.analyticAt_prod
    intro u _
    exact (analyticAt_id.sub analyticAt_const).pow _
  have hmpos : ∀ u ∈ S, 0 < m u := by
    intro u hu
    rw [hS_def, Set.Finite.mem_toFinset, Function.mem_support] at hu
    rw [hm_def]
    simp only
    apply Nat.pos_of_ne_zero
    intro h0
    apply hu
    have hcast := Int.toNat_of_nonneg (hdivnn u)
    rw [h0] at hcast
    omega
  have hSU : ∀ u ∈ S, u ∈ U := by
    intro u hu
    rw [hS_def, Set.Finite.mem_toFinset] at hu
    exact (MeromorphicOn.divisor riemannZeta U).supportWithinDomain hu
  have hmeq : ∀ u ∈ S, (m u : ℤ) = MeromorphicOn.divisor riemannZeta U u := fun u _ => by
    rw [hm_def]; exact Int.toNat_of_nonneg (hdivnn u)
  have hSzero : ∀ u ∈ S, riemannZeta u = 0 := by
    intro u hu
    have huU := hSU u hu
    rw [hS_def, Set.Finite.mem_toFinset, Function.mem_support] at hu
    by_contra hne
    apply hu
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hAn huU]
    rw [(hAn u huU).analyticOrderAt_eq_zero.mpr hne]
    simp only [ENat.map_zero, CharP.cast_eq_zero, WithTop.coe_zero, WithTop.untop₀_zero]
  refine ⟨S, m, g, hgAn, fun w hw => hgne ⟨w, hw⟩, hmpos, hSU, hSzero, hmeq, ?_⟩
  have hfeq : (∏ᶠ u, (· - u) ^ MeromorphicOn.divisor riemannZeta U u) = φ := by
    rw [hφ_def]; exact Function.FactorizedRational.finprod_eq_fun h3f
  intro z' hz'U
  have hcontZ : ContinuousAt riemannZeta z' := (hAn z' hz'U).continuousAt
  have hcontH : ContinuousAt (fun w => P w * g w) z' :=
    ((hPAn z' (Set.mem_univ z')).continuousAt).mul (hgAn z' hz'U).continuousAt
  have hle : nhdsWithin z' (U \ {z'}) ≤ Filter.codiscreteWithin U :=
    le_iSup₂ (f := fun x (_ : x ∈ U) => nhdsWithin x (U \ {x})) z' hz'U
  have hUdiff : nhdsWithin z' (U \ {z'}) = nhdsWithin z' {z'}ᶜ := by
    rw [Set.sdiff_eq, Set.inter_comm,
      nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds (hUopen.mem_nhds hz'U))]
  have hstep1 : riemannZeta =ᶠ[nhdsWithin z' {z'}ᶜ] (fun w => φ w * g w) := by
    rw [← hUdiff]
    filter_upwards [heq.filter_mono hle] with w hw
    rw [hfeq] at hw
    simpa only [Pi.smul_apply', smul_eq_mul] using hw
  have hstep2 : riemannZeta =ᶠ[nhds z'] (fun w => φ w * g w) :=
    (hcontZ.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE (by rwa [hφP])).mp hstep1
  have hstep3 := hstep2.eq_of_nhds
  rwa [hφP] at hstep3

/-- The logarithmic derivative of `ζ` at a non-zero point `z` decomposes as a finite sum over
nearby zeros' contributions `m_ρ/(z-ρ)` plus the logarithmic derivative of a zero-free analytic
remainder `g`. -/
theorem exists_logDeriv_riemannZeta_eq_sum_add_logDeriv {z : ℂ} {R : ℝ} (hR : 0 < R)
    (hz1 : ∀ w ∈ Metric.closedBall z R, w ≠ 1) (hzgood : riemannZeta z ≠ 0) :
    ∃ (S : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
      AnalyticOnNhd ℂ g (Metric.ball z R) ∧
        (∀ w ∈ Metric.ball z R, g w ≠ 0) ∧
        (∀ u ∈ S, 0 < m u) ∧
        (∀ u ∈ S, u ∈ Metric.ball z R) ∧
        (∀ u ∈ S, riemannZeta u = 0) ∧
        (∀ u ∈ S, (m u : ℤ) = MeromorphicOn.divisor riemannZeta (Metric.ball z R) u) ∧
        Set.EqOn riemannZeta (fun w => (∏ u ∈ S, (w - u) ^ m u) * g w) (Metric.ball z R) ∧
        logDeriv riemannZeta z = (∑ u ∈ S, (m u : ℂ) / (z - u)) + logDeriv g z := by
  obtain ⟨S, m, g, hgAn, hgne, hmpos, hSU, hSzero, hmeq, heq⟩ :=
    exists_riemannZeta_zeroFree_factorization hR hz1
  have hzU : z ∈ Metric.ball z R := Metric.mem_ball_self hR
  have hzval : riemannZeta z = (∏ u ∈ S, (z - u) ^ m u) * g z := heq hzU
  have hzS : ∀ u ∈ S, u ≠ z := by
    intro u huS heqz
    apply hzgood
    rw [hzval]
    apply mul_eq_zero_of_left
    apply Finset.prod_eq_zero huS
    have hsubzero : z - u = 0 := sub_eq_zero.mpr heqz.symm
    rw [hsubzero]
    exact zero_pow (M₀ := ℂ) (hmpos u huS).ne'
  refine ⟨S, m, g, hgAn, hgne, hmpos, hSU, hSzero, hmeq, heq, ?_⟩
  have heqNhds : riemannZeta =ᶠ[nhds z] (fun w => (∏ u ∈ S, (w - u) ^ m u) * g w) :=
    Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hzU) heq
  have hlogeq :
    logDeriv riemannZeta =ᶠ[nhds z] logDeriv (fun w => (∏ u ∈ S, (w - u) ^ m u) * g w) :=
    logDeriv_congr_nhds heqNhds
  have hlogeqz := hlogeq.eq_of_nhds
  rw [hlogeqz]
  have hPz_ne : (∏ u ∈ S, (z - u) ^ m u) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro u hu
    exact pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm (hzS u hu)))
  have hgz_ne : g z ≠ 0 := hgne z hzU
  have hPdiff : DifferentiableAt ℂ (fun w => ∏ u ∈ S, (w - u) ^ m u) z := by
    have heqfun : (fun w : ℂ => ∏ u ∈ S, (w - u) ^ m u) = ∏ u ∈ S, fun w => (w - u) ^ m u := by
      funext w; rw [Finset.prod_apply]
    rw [heqfun]
    apply DifferentiableAt.finsetProd
    intro u _
    exact (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w - u) z).pow _
  have hgdiff : DifferentiableAt ℂ g z := (hgAn z hzU).differentiableAt
  rw [show (fun w : ℂ => (∏ u ∈ S, (w - u) ^ m u) * g w) = (fun w : ℂ => ∏ u ∈ S, (w - u) ^ m u) * g
      from by
      funext w
      simp only [Pi.mul_apply]]
  rw [logDeriv_mul z hPz_ne hgz_ne hPdiff hgdiff]
  congr 1
  have hprodfun :
    (fun w : ℂ => ∏ u ∈ S, (w - u) ^ m u) = ∏ u ∈ S, (fun w : ℂ => (w - u) ^ m u) := by
    funext w
    rw [Finset.prod_apply]
  rw [hprodfun]
  rw [logDeriv_prod (f := fun u (w : ℂ) => (w - u) ^ m u) (x := z) (s := S)
      (fun u hu => pow_ne_zero (m u) (sub_ne_zero.mpr (Ne.symm (hzS u hu))))
      (fun u _ => (differentiableAt_id.sub_const u).pow (m u))]
  apply Finset.sum_congr rfl
  intro u _
  rw [logDeriv_fun_pow (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w - u) z)]
  have hlogw : logDeriv (fun w : ℂ => w - u) z = 1 / (z - u) := by
    rw [logDeriv_apply]
    have hderiv1 : deriv (fun w : ℂ => w - u) z = 1 := ((hasDerivAt_id z).sub_const u).deriv
    rw [hderiv1]
  rw [hlogw]
  ring

/-- The same log-derivative decomposition as
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.exists_logDeriv_riemannZeta_eq_sum_add_logDeriv`,
but evaluated at an arbitrary point `z0` of the factorization ball (not necessarily the
factorization center `z` itself), taking the factorization data directly as input. This is what
lets a single Jensen-scale factorization (centered far from the evaluation point, where `ζ` is
known to be bounded away from `0`) be evaluated at the actual point of interest. -/
theorem logDeriv_riemannZeta_eq_sum_add_logDeriv_at {z : ℂ} {R : ℝ} {S : Finset ℂ} {m : ℂ → ℕ}
    {g : ℂ → ℂ} (hgAn : AnalyticOnNhd ℂ g (Metric.ball z R)) (hgne : ∀ w ∈ Metric.ball z R, g w ≠ 0)
    (hmpos : ∀ u ∈ S, 0 < m u)
    (heq : Set.EqOn riemannZeta (fun w => (∏ u ∈ S, (w - u) ^ m u) * g w) (Metric.ball z R))
    {z0 : ℂ} (hz0U : z0 ∈ Metric.ball z R) (hz0good : riemannZeta z0 ≠ 0) :
    logDeriv riemannZeta z0 = (∑ u ∈ S, (m u : ℂ) / (z0 - u)) + logDeriv g z0 := by
  have hz0val : riemannZeta z0 = (∏ u ∈ S, (z0 - u) ^ m u) * g z0 := heq hz0U
  have hz0S : ∀ u ∈ S, u ≠ z0 := by
    intro u huS heqz
    apply hz0good
    rw [hz0val]
    apply mul_eq_zero_of_left
    apply Finset.prod_eq_zero huS
    have hsubzero : z0 - u = 0 := sub_eq_zero.mpr heqz.symm
    rw [hsubzero]
    exact zero_pow (M₀ := ℂ) (hmpos u huS).ne'
  have heqNhds : riemannZeta =ᶠ[nhds z0] (fun w => (∏ u ∈ S, (w - u) ^ m u) * g w) :=
    Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz0U) heq
  have hlogeq :
    logDeriv riemannZeta =ᶠ[nhds z0] logDeriv (fun w => (∏ u ∈ S, (w - u) ^ m u) * g w) :=
    logDeriv_congr_nhds heqNhds
  have hlogeqz := hlogeq.eq_of_nhds
  rw [hlogeqz]
  have hPz_ne : (∏ u ∈ S, (z0 - u) ^ m u) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro u hu
    exact pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm (hz0S u hu)))
  have hgz_ne : g z0 ≠ 0 := hgne z0 hz0U
  have hPdiff : DifferentiableAt ℂ (fun w => ∏ u ∈ S, (w - u) ^ m u) z0 := by
    have heqfun : (fun w : ℂ => ∏ u ∈ S, (w - u) ^ m u) = ∏ u ∈ S, fun w => (w - u) ^ m u := by
      funext w; rw [Finset.prod_apply]
    rw [heqfun]
    apply DifferentiableAt.finsetProd
    intro u _
    exact (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w - u) z0).pow _
  have hgdiff : DifferentiableAt ℂ g z0 := (hgAn z0 hz0U).differentiableAt
  rw [show (fun w : ℂ => (∏ u ∈ S, (w - u) ^ m u) * g w) = (fun w : ℂ => ∏ u ∈ S, (w - u) ^ m u) * g
      from by
      funext w
      simp only [Pi.mul_apply]]
  rw [logDeriv_mul z0 hPz_ne hgz_ne hPdiff hgdiff]
  congr 1
  have hprodfun :
    (fun w : ℂ => ∏ u ∈ S, (w - u) ^ m u) = ∏ u ∈ S, (fun w : ℂ => (w - u) ^ m u) := by
    funext w
    rw [Finset.prod_apply]
  rw [hprodfun]
  rw [logDeriv_prod (f := fun u (w : ℂ) => (w - u) ^ m u) (x := z0) (s := S)
      (fun u hu => pow_ne_zero (m u) (sub_ne_zero.mpr (Ne.symm (hz0S u hu))))
      (fun u _ => (differentiableAt_id.sub_const u).pow (m u))]
  apply Finset.sum_congr rfl
  intro u _
  rw [logDeriv_fun_pow (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w - u) z0)]
  have hlogw : logDeriv (fun w : ℂ => w - u) z0 = 1 / (z0 - u) := by
    rw [logDeriv_apply]
    have hderiv1 : deriv (fun w : ℂ => w - u) z0 = 1 := ((hasDerivAt_id z0).sub_const u).deriv
    rw [hderiv1]
  rw [hlogw]
  ring

/-! ### Bounding the finite-sum term via the good-height margin -/

/-- `MeromorphicOn.divisor`'s value at a point is a purely local quantity (the analytic order
of `ζ` there), so it doesn't depend on which analytic domain it's computed within. -/
theorem divisor_riemannZeta_eq_of_analyticOnNhd {U₁ U₂ : Set ℂ}
    (h1 : AnalyticOnNhd ℂ riemannZeta U₁) (h2 : AnalyticOnNhd ℂ riemannZeta U₂) {u : ℂ}
    (hu1 : u ∈ U₁) (hu2 : u ∈ U₂) : MeromorphicOn.divisor riemannZeta U₁ u =
      MeromorphicOn.divisor riemannZeta U₂ u := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply h1 hu1,
    MeromorphicOn.AnalyticOnNhd.divisor_apply h2 hu2]

/-- At a good height `T` (as produced by
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.exists_good_height`), for any `σ` in the (shrunk)
target range `[-1/2, 2]`, `ζ` factors locally around `z := σ + iT` and the resulting finite-sum
part of `logDeriv ζ`'s decomposition is bounded by
`4(PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensenLogConst·log(H+2))²`: each of the
`≤ PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensenLogConst·log(H+2)` nearby zeros
contributes a term of norm `≤ 1/margin`, where
`margin = 1/(4·PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensenLogConst·log(H+2))`. -/
theorem exists_logDeriv_riemannZeta_eq_sum_add_logDeriv_of_good_height {H : ℝ} (hH : 8 ≤ H) {T : ℝ}
    (hT : T ∈ Set.Icc H (H + 1))
    (hgood :
      ∀ ρ : ℂ,
        riemannZeta ρ = 0 →
          |ρ.im - H| ≤ 2 →
          1 / (4 * jensenLogConst * Real.log (H + 2)) ≤
            |T - ρ.im|)
    {σ : ℝ} (_hσ1 : -(1 : ℝ) / 2 ≤ σ) (_hσ2 : σ ≤ 2) :
    ∃ (S : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
      AnalyticOnNhd ℂ g (Metric.ball (σ + T * Complex.I) (2 / 5)) ∧
        (∀ w ∈ Metric.ball (σ + T * Complex.I) (2 / 5), g w ≠ 0) ∧
        logDeriv riemannZeta (σ + T * Complex.I) =
          (∑ u ∈ S, (m u : ℂ) / ((σ + T * Complex.I) - u)) + logDeriv g (σ + T * Complex.I) ∧
        ‖∑ u ∈ S, (m u : ℂ) / ((σ + T * Complex.I) - u)‖ ≤
          4 *
            (jensenLogConst * Real.log (H + 2)) ^
              2 := by
  set z : ℂ := σ + T * Complex.I with hz_def
  have hzim : z.im = T := by
    simp only [hz_def, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  have hzre : z.re = σ := by
    simp only [hz_def, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hTpos : (0 : ℝ) < T := by linarith [hT.1]
  have hz1 : ∀ w ∈ Metric.closedBall z (2 / 5 : ℝ), w ≠ 1 := by
    intro w hw hw1
    rw [Metric.mem_closedBall, Complex.dist_eq, hw1] at hw
    have him : |(1 : ℂ).im - z.im| ≤ ‖(1 : ℂ) - z‖ := by
      have h := Complex.abs_im_le_norm ((1 : ℂ) - z)
      simpa only [Complex.one_im, zero_sub, abs_neg, ge_iff_le, Complex.sub_im] using h
    rw [hzim, Complex.one_im, zero_sub, abs_neg, abs_of_nonneg hTpos.le] at him
    linarith only [hH, hT.1, him, hw]
  have hzgood : riemannZeta z ≠ 0 := by
    intro hzero
    have h1 : |z.im - H| ≤ 2 := by
      rw [hzim]
      rw [abs_le]
      constructor <;> linarith [hT.1, hT.2]
    have h2 := hgood z hzero h1
    rw [hzim, sub_self, abs_zero] at h2
    have hLCpos := jensenLogConst_pos
    have hlogpos : (0 : ℝ) < Real.log (H + 2) := Real.log_pos (by linarith)
    have : (0 : ℝ) < 1 / (4 * jensenLogConst * Real.log (H + 2)) := by positivity
    linarith
  obtain ⟨S, m, g, hgAn, hgne, hmpos, hSU, hSzero, hmeqSmall, _heqOn, hlog⟩ :=
    exists_logDeriv_riemannZeta_eq_sum_add_logDeriv
      (R := 2 / 5) (by norm_num only) hz1 hzgood
  refine ⟨S, m, g, hgAn, hgne, hlog, ?_⟩
  -- Every zero in `S` has ordinate within `2` of `H`: reused for both the margin bound and the
  -- containment in the zeta-side estimate disk.
  have hu_im_H : ∀ u ∈ S, |u.im - H| ≤ 2 := by
    intro u hu
    have huU := hSU u hu
    rw [Metric.mem_ball, Complex.dist_eq] at huU
    have h := Complex.abs_im_le_norm (u - z)
    rw [Complex.sub_im, hzim] at h
    have h2 : |u.im - T| < 2 / 5 := lt_of_le_of_lt h huU
    rw [abs_lt] at h2
    rw [abs_le]
    constructor <;> linarith [h2.1, h2.2, hT.1, hT.2]
  -- Bound each term's denominator away from 0 via the good-height margin.
  have hmargin :
    ∀ u ∈ S,
      1 / (4 * jensenLogConst * Real.log (H + 2)) ≤
        ‖z - u‖ := by
    intro u hu
    have hmarg := hgood u (hSzero u hu) (hu_im_H u hu)
    have hle : |T - u.im| ≤ ‖z - u‖ := by
      have h := Complex.abs_im_le_norm (z - u)
      rw [Complex.sub_im, hzim] at h
      exact h
    linarith [hmarg, hle]
  -- Bound the total multiplicity via the zeta-side estimate zero count.
  have hAnSmall : AnalyticOnNhd ℂ riemannZeta (Metric.ball z (2 / 5 : ℝ)) := fun w hw =>
    analyticOn_riemannZeta w (hz1 w (Metric.ball_subset_closedBall hw))
  have hAnBig :
    AnalyticOnNhd ℂ riemannZeta
      (Metric.closedBall (jensenCenter H) (37 / 10)) :=
    (jensen_analyticOnNhd (by linarith : (4 : ℝ) ≤ H)).mono
      (Metric.closedBall_subset_closedBall (by norm_num only))
  have hSbig :
    ∀ u ∈ S,
      u ∈
        Metric.closedBall (jensenCenter H) (37 / 10) :=
    fun u hu =>
    riemannZeta_zero_mem_jensenBall hH (hSzero u hu)
      (hu_im_H u hu)
  have hfin :=
    (MeromorphicOn.divisor riemannZeta
          (Metric.closedBall (jensenCenter H)
            (37 / 10))).finiteSupport
      (isCompact_closedBall _ _)
  have hmeqBig :
    ∀ u ∈ S,
      (m u : ℤ) =
        MeromorphicOn.divisor riemannZeta
          (Metric.closedBall (jensenCenter H)
            (37 / 10))
          u :=
    fun u hu =>
    (hmeqSmall u hu).trans
      (divisor_riemannZeta_eq_of_analyticOnNhd hAnSmall
        hAnBig (hSU u hu) (hSbig u hu))
  have hSsub : S ⊆ hfin.toFinset := by
    intro u hu
    rw [Set.Finite.mem_toFinset, Function.mem_support]
    rw [← hmeqBig u hu]
    exact_mod_cast (hmpos u hu).ne'
  have hsum_le :
    (∑ u ∈ S, (m u : ℝ)) ≤
      jensenLogConst * Real.log (H + 2) := by
    have hcongr :
      ∑ u ∈ S, (m u : ℝ) =
        ∑ u ∈ S,
          (MeromorphicOn.divisor riemannZeta
              (Metric.closedBall (jensenCenter H)
                (37 / 10))
              u :
            ℝ) :=
      Finset.sum_congr rfl (fun u hu => by exact_mod_cast hmeqBig u hu)
    rw [hcongr]
    have hcard1 :
      ∑ u ∈ S,
          (MeromorphicOn.divisor riemannZeta
              (Metric.closedBall (jensenCenter H)
                (37 / 10))
              u :
            ℝ) ≤
        ∑ u ∈ hfin.toFinset,
          (MeromorphicOn.divisor riemannZeta
              (Metric.closedBall (jensenCenter H)
                (37 / 10))
              u :
            ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hSsub
      intro u _ _
      exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAnBig u
    have hcard2 :
      ∑ u ∈ hfin.toFinset,
          (MeromorphicOn.divisor riemannZeta
              (Metric.closedBall (jensenCenter H)
                (37 / 10))
              u :
            ℝ) =
        ((∑ᶠ u,
              MeromorphicOn.divisor riemannZeta
                (Metric.closedBall (jensenCenter H)
                  (37 / 10))
                u :
            ℤ) :
          ℝ) := by
      rw [finsum_eq_finsetSum_of_support_subset _ (s := hfin.toFinset)
          (by rw [Set.Finite.coe_toFinset])]
      push_cast
      rfl
    rw [hcard2] at hcard1
    exact
      hcard1.trans
        (finsum_divisor_riemannZeta_le_explicit hH)
  have hlogpos : (0 : ℝ) < Real.log (H + 2) := Real.log_pos (by linarith)
  have hLCpos := jensenLogConst_pos
  have hmarginpos :
    (0 : ℝ) <
      4 * jensenLogConst * Real.log (H + 2) := by
    positivity
  calc
    ‖∑ u ∈ S, (m u : ℂ) / (z - u)‖ ≤ ∑ u ∈ S, ‖(m u : ℂ) / (z - u)‖ := norm_sum_le _ _
    _ = ∑ u ∈ S, (m u : ℝ) / ‖z - u‖ := by
      apply Finset.sum_congr rfl
      intro u _
      rw [norm_div, Complex.norm_natCast]
    _ ≤
        ∑ u ∈ S,
          (m u : ℝ) *
            (4 * jensenLogConst * Real.log (H + 2)) :=
      by
      apply Finset.sum_le_sum
      intro u hu
      have hrecip :
        1 / ‖z - u‖ ≤
          4 * jensenLogConst * Real.log (H + 2) := by
        have h1 := one_div_le_one_div_of_le (by positivity) (hmargin u hu)
        rwa [one_div_one_div] at h1
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hrecip (Nat.cast_nonneg _)
    _ =
        (∑ u ∈ S, (m u : ℝ)) *
          (4 * jensenLogConst * Real.log (H + 2)) :=
      by rw [Finset.sum_mul]
    _ ≤
        (jensenLogConst * Real.log (H + 2)) *
          (4 * jensenLogConst * Real.log (H + 2)) :=
      by apply mul_le_mul_of_nonneg_right hsum_le (by positivity)
    _ = 4 * (jensenLogConst * Real.log (H + 2)) ^ 2 :=
      by ring

/-!
### A logarithmic primitive on a zero-free disk

For an analytic nonvanishing function on a disk, construct a primitive of its
logarithmic derivative with real part equal to the logarithm of its norm.
This avoids choosing the principal complex logarithm.
-/

theorem exists_hasDerivAt_logDeriv_re_eq_log_norm {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hfAn : AnalyticOnNhd ℂ f (Metric.ball c r)) (hfne : ∀ w ∈ Metric.ball c r, f w ≠ 0) :
    ∃ h : ℂ → ℂ,
      (∀ w ∈ Metric.ball c r, HasDerivAt h (logDeriv f w) w) ∧
        ∀ w ∈ Metric.ball c r, (h w).re = Real.log ‖f w‖ := by
  have hfDiffOn : DifferentiableOn ℂ f (Metric.ball c r) := fun w hw =>
    (hfAn w hw).differentiableWithinAt
  have hlogDerivEq : logDeriv f = fun w => deriv f w / f w := by
    funext w; rw [logDeriv_apply]
  have hlogDerivDiffOn : DifferentiableOn ℂ (logDeriv f) (Metric.ball c r) := by
    rw [hlogDerivEq]
    exact (hfDiffOn.deriv Metric.isOpen_ball).div hfDiffOn hfne
  obtain ⟨h, hhc, hh'⟩ := (hlogDerivDiffOn.isExactOn_ball).with_val_at c (Complex.log (f c))
  set G : ℂ → ℂ := fun w => Complex.exp (h w) * (f w)⁻¹ with hG_def
  have hGhasDerivAt : ∀ w ∈ Metric.ball c r, HasDerivAt G 0 w := by
    intro w hw
    have hhw := hh' w hw
    have hfnew := hfne w hw
    have hderivf : deriv f w = logDeriv f w * f w := by
      have hlog : logDeriv f w = deriv f w / f w := by rw [hlogDerivEq]
      rw [hlog, div_mul_cancel₀]
      exact hfnew
    have hfHasDeriv : HasDerivAt f (logDeriv f w * f w) w := by
      rw [← hderivf]
      exact ((hfDiffOn w hw).differentiableAt (Metric.isOpen_ball.mem_nhds hw)).hasDerivAt
    have hexpw : HasDerivAt (fun w => Complex.exp (h w)) (Complex.exp (h w) * logDeriv f w) w :=
      hhw.cexp
    have hinvw : HasDerivAt (fun w => (f w)⁻¹) (-(logDeriv f w * f w) / (f w) ^ 2) w :=
      hfHasDeriv.inv hfnew
    have hGw :
      HasDerivAt G
        (Complex.exp (h w) * logDeriv f w * (f w)⁻¹ +
          Complex.exp (h w) * (-(logDeriv f w * f w) / (f w) ^ 2))
        w :=
      hexpw.mul hinvw
    have hzero :
      Complex.exp (h w) * logDeriv f w * (f w)⁻¹ +
          Complex.exp (h w) * (-(logDeriv f w * f w) / (f w) ^ 2) =
        0 := by
      field_simp
      ring
    rw [hzero] at hGw
    exact hGw
  have hGDiffOn : DifferentiableOn ℂ G (Metric.ball c r) := fun w hw =>
    (hGhasDerivAt w hw).differentiableAt.differentiableWithinAt
  have hderiv0 : (Metric.ball c r).EqOn (deriv G) 0 := fun w hw => (hGhasDerivAt w hw).deriv
  have hcmem : c ∈ Metric.ball c r := Metric.mem_ball_self hr
  have hfnec := hfne c hcmem
  have hGc : G c = 1 := by
    change Complex.exp (h c) * (f c)⁻¹ = 1
    rw [hhc, Complex.exp_log hfnec, mul_inv_cancel₀ hfnec]
  have hconst := fun w (hw : w ∈ Metric.ball c r) =>
    Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c r).isPreconnected hGDiffOn hderiv0
      hcmem hw
  refine ⟨h, hh', fun w hw => ?_⟩
  have hGw1 : G w = 1 := (hconst w hw).symm.trans hGc
  have hfnew := hfne w hw
  have hexpeq : Complex.exp (h w) = f w := by
    have heq1 : Complex.exp (h w) * (f w)⁻¹ = 1 := hGw1
    field_simp at heq1
    exact heq1
  have hnormeq : Real.exp (h w).re = ‖f w‖ := by rw [← Complex.norm_exp, hexpeq]
  have hpos : (0 : ℝ) < ‖f w‖ := norm_pos_iff.mpr hfnew
  rw [← hnormeq, Real.log_exp]

/-! ### The "good radius" selection

Mirrors `PseudoPrime.AnalyticNumberTheory.RiemannZeta.exists_good_height`'s "good height" selection,
but in the radius direction: for a good
height `T`, some radius `R` near `z := σ + iT` keeps every zero extracted into the local
factorization at that radius safely away from the boundary sphere `sphere(z,R)`. This is needed
because a zero could otherwise sit arbitrarily close to a naively-chosen fixed boundary radius,
making the boundary bound on `log‖g‖` degenerate. -/

/-- `ζ`'s analytic order is never `⊤` on a closed ball whose center is a known non-zero point
(and which avoids the pole at `1`): the identity theorem argument of
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.riemannZeta_analyticOrderAt_ne_top`,
generalized from the Jensen disk to an arbitrary ball. -/
theorem riemannZeta_analyticOrderAt_ne_top_of_center {c : ℂ} {R : ℝ}
    (hc1 : ∀ w ∈ Metric.closedBall c R, w ≠ 1) (hcgood : riemannZeta c ≠ 0) {u : ℂ}
    (hu : u ∈ Metric.closedBall c R) : analyticOrderAt riemannZeta u ≠ ⊤ := by
  intro htop
  have hAn : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall c R) := fun w hw =>
    analyticOn_riemannZeta w (hc1 w hw)
  have hUconv : IsPreconnected (Metric.closedBall c R) := (convex_closedBall _ _).isPreconnected
  have hRnn : (0 : ℝ) ≤ R := le_trans dist_nonneg (Metric.mem_closedBall.mp hu)
  have hcenter : c ∈ Metric.closedBall c R := Metric.mem_closedBall_self hRnn
  have heq0 : Set.EqOn riemannZeta 0 (Metric.closedBall c R) :=
    hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUconv hu (analyticOrderAt_eq_top.mp htop)
  exact hcgood (heq0 hcenter)

/-- The two-sided form of `PseudoPrime.AnalyticNumberTheory.RiemannZeta.exists_good_radius`:
`R` keeps every zero within distance `2/5` of
`z` at margin `≥ c` from `R` on BOTH sides (not just from inside). This lets a downstream
factorization radius be pushed slightly past `R` (into the resulting zero-free gap) while still
capturing exactly the same zero set, which is what makes the extracted `g` continuous up to a
closed ball boundary (see the discussion above
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.exists_good_radius`). -/
theorem exists_good_radius_twoSided {H : ℝ} (hH : 8 ≤ H) {T : ℝ} (hT : T ∈ Set.Icc H (H + 1))
    (hgood :
      ∀ ρ : ℂ,
        riemannZeta ρ = 0 →
          |ρ.im - H| ≤ 2 →
          1 / (4 * jensenLogConst * Real.log (H + 2)) ≤
            |T - ρ.im|)
    (σ : ℝ) :
    ∃ R ∈ Set.Icc (1 / 5 : ℝ) (3 / 10),
      ∀ ρ : ℂ,
        riemannZeta ρ = 0 →
          ‖(σ + T * Complex.I) - ρ‖ < 2 / 5 →
          1 /
              (40 * jensenLogConst *
                Real.log (H + 2)) ≤
            |R - ‖(σ + T * Complex.I) - ρ‖| := by
  set z : ℂ := σ + T * Complex.I with hz_def
  have hzim : z.im = T := by
    simp only [hz_def, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  have hTpos : (0 : ℝ) < T := by linarith [hT.1]
  have hz1 : ∀ w ∈ Metric.closedBall z (2 / 5 : ℝ), w ≠ 1 := by
    intro w hw hw1
    rw [Metric.mem_closedBall, Complex.dist_eq, hw1] at hw
    have him : |(1 : ℂ).im - z.im| ≤ ‖(1 : ℂ) - z‖ := by
      have h := Complex.abs_im_le_norm ((1 : ℂ) - z)
      simpa only [Complex.one_im, zero_sub, abs_neg, ge_iff_le, Complex.sub_im] using h
    rw [hzim, Complex.one_im, zero_sub, abs_neg, abs_of_nonneg hTpos.le] at him
    linarith only [hH, hT.1, him, hw]
  have hzgood : riemannZeta z ≠ 0 := by
    intro hzero
    have h1 : |z.im - H| ≤ 2 := by
      rw [hzim]; rw [abs_le]; constructor <;> linarith [hT.1, hT.2]
    have h2 := hgood z hzero h1
    rw [hzim, sub_self, abs_zero] at h2
    have hLCpos := jensenLogConst_pos
    have hlogpos : (0 : ℝ) < Real.log (H + 2) := Real.log_pos (by linarith)
    have :
      (0 : ℝ) <
        1 /
          (4 * jensenLogConst * Real.log (H + 2)) := by
      positivity
    linarith
  have hAnClosed : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall z (2 / 5 : ℝ)) := fun w hw =>
    analyticOn_riemannZeta w (hz1 w hw)
  have hAnBall : AnalyticOnNhd ℂ riemannZeta (Metric.ball z (2 / 5 : ℝ)) := fun w hw =>
    hAnClosed w (Metric.ball_subset_closedBall hw)
  have hfin : (MeromorphicOn.divisor riemannZeta (Metric.ball z (2 / 5 : ℝ))).support.Finite :=
    MeromorphicOn.divisor_ball_support_finite hAnClosed.meromorphicOn
  set Sfin : Finset ℂ := hfin.toFinset with hSfin_def
  set D : Finset ℝ := Sfin.image (fun ρ => ‖z - ρ‖) with hD_def
  -- Bound `D`'s cardinality via the zeta-side estimate zero count (same subset-of-big-Jensen-disk
  -- argument used in
  -- `PseudoPrime.AnalyticNumberTheory.RiemannZeta.`
  -- `exists_logDeriv_riemannZeta_eq_sum_add_logDeriv_of_good_height`).
  have hu_im_H : ∀ u ∈ Sfin, |u.im - H| ≤ 2 := by
    intro u hu
    rw [hSfin_def, Set.Finite.mem_toFinset] at hu
    have huU : u ∈ Metric.ball z (2 / 5 : ℝ) :=
      (MeromorphicOn.divisor riemannZeta (Metric.ball z (2 / 5 : ℝ))).supportWithinDomain hu
    rw [Metric.mem_ball, Complex.dist_eq] at huU
    have h := Complex.abs_im_le_norm (u - z)
    rw [Complex.sub_im, hzim] at h
    have h2 : |u.im - T| < 2 / 5 := lt_of_le_of_lt h huU
    rw [abs_lt] at h2
    rw [abs_le]
    constructor <;> linarith [h2.1, h2.2, hT.1, hT.2]
  have hSzero : ∀ u ∈ Sfin, riemannZeta u = 0 := by
    intro u hu
    have huU : u ∈ Metric.ball z (2 / 5 : ℝ) := by
      rw [hSfin_def, Set.Finite.mem_toFinset] at hu
      exact (MeromorphicOn.divisor riemannZeta (Metric.ball z (2 / 5 : ℝ))).supportWithinDomain hu
    rw [hSfin_def, Set.Finite.mem_toFinset, Function.mem_support] at hu
    by_contra hne
    apply hu
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hAnBall huU]
    rw [(hAnBall u huU).analyticOrderAt_eq_zero.mpr hne]
    simp only [ENat.map_zero, CharP.cast_eq_zero, WithTop.coe_zero, WithTop.untop₀_zero]
  have hAnBig :
    AnalyticOnNhd ℂ riemannZeta
      (Metric.closedBall (jensenCenter H) (37 / 10)) :=
    (jensen_analyticOnNhd
          (by linarith : (4 : ℝ) ≤ H)).mono
      (Metric.closedBall_subset_closedBall (by norm_num only))
  have hSbig :
    ∀ u ∈ Sfin,
      u ∈
        Metric.closedBall (jensenCenter H) (37 / 10) :=
    fun u hu =>
    riemannZeta_zero_mem_jensenBall hH (hSzero u hu)
      (hu_im_H u hu)
  have hfinBig :=
    (MeromorphicOn.divisor riemannZeta
          (Metric.closedBall (jensenCenter H) (37 / 10))).finiteSupport
      (isCompact_closedBall _ _)
  have hSsub : Sfin ⊆ hfinBig.toFinset := by
    intro u hu
    rw [Set.Finite.mem_toFinset, Function.mem_support]
    have huU : u ∈ Metric.ball z (2 / 5 : ℝ) := by
      rw [hSfin_def, Set.Finite.mem_toFinset] at hu
      exact (MeromorphicOn.divisor riemannZeta (Metric.ball z (2 / 5 : ℝ))).supportWithinDomain hu
    rw [←
      divisor_riemannZeta_eq_of_analyticOnNhd hAnBall
        hAnBig huU (hSbig u hu)]
    rw [hSfin_def, Set.Finite.mem_toFinset] at hu
    exact hu
  have hcard :
    (D.card : ℝ) ≤
      jensenLogConst * Real.log (H + 2) := by
    have h1 : D.card ≤ Sfin.card := Finset.card_image_le
    have h2 : Sfin.card ≤ hfinBig.toFinset.card := Finset.card_le_card hSsub
    have h3 :
      (hfinBig.toFinset.card : ℝ) ≤
        ((∑ᶠ u,
              MeromorphicOn.divisor riemannZeta
                (Metric.closedBall (jensenCenter H) (37 / 10))
                u :
            ℤ) :
          ℝ) := by
      have heach :
        ∀ u ∈ hfinBig.toFinset,
          (1 : ℤ) ≤
            MeromorphicOn.divisor riemannZeta
              (Metric.closedBall (jensenCenter H) (37 / 10))
              u := by
        intro u hu
        rw [Set.Finite.mem_toFinset, Function.mem_support] at hu
        have hnn :
          (0 : ℤ) ≤
            MeromorphicOn.divisor riemannZeta
              (Metric.closedBall (jensenCenter H) (37 / 10))
              u :=
          MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAnBig u
        omega
      calc
        (hfinBig.toFinset.card : ℝ) = ∑ _u ∈ hfinBig.toFinset, (1 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤
            ∑ u ∈ hfinBig.toFinset,
              (MeromorphicOn.divisor riemannZeta
                  (Metric.closedBall (jensenCenter H) (37 / 10))
                  u :
                ℝ) :=
          by
          apply Finset.sum_le_sum
          intro u hu
          exact_mod_cast heach u hu
        _ =
            ((∑ᶠ u,
                  MeromorphicOn.divisor riemannZeta
                    (Metric.closedBall (jensenCenter H) (37 / 10))
                    u :
                ℤ) :
              ℝ) :=
          by
          rw [finsum_eq_finsetSum_of_support_subset _ (s := hfinBig.toFinset)
              (by rw [Set.Finite.coe_toFinset])]
          push_cast
          rfl
    have h4 :=
      finsum_divisor_riemannZeta_le_explicit hH
    calc
      (D.card : ℝ) ≤ (Sfin.card : ℝ) := by exact_mod_cast h1
      _ ≤ (hfinBig.toFinset.card : ℝ) := by exact_mod_cast h2
      _ ≤ _ := h3
      _ ≤ jensenLogConst * Real.log (H + 2) := h4
  set c : ℝ :=
    1 / (40 * jensenLogConst * Real.log (H + 2)) with
    hc_def
  have hLCpos := jensenLogConst_pos
  have hlogpos : (0 : ℝ) < Real.log (H + 2) := Real.log_pos (by linarith)
  have hc_pos : 0 < c := by
    rw [hc_def]; positivity
  have hlen : 2 * c * (D.card : ℝ) < (1 / 10 : ℝ) := by
    calc
      2 * c * (D.card : ℝ) ≤
          2 * c *
            (jensenLogConst * Real.log (H + 2)) :=
        mul_le_mul_of_nonneg_left hcard (by positivity)
      _ = 1 / 20 := by
        rw [hc_def]; field_simp; norm_num only
      _ < 1 / 10 := by norm_num only
  obtain ⟨R, hR, hRgood⟩ :=
    exists_avoiding_point_length (a := 1 / 5) hc_pos
      (by norm_num only : (0 : ℝ) < 1 / 10) hlen
  have hR' : R ∈ Set.Icc (1 / 5 : ℝ) (3 / 10) := by
    rw [show (1 / 5 : ℝ) + 1 / 10 = 3 / 10 from by norm_num only] at hR; exact hR
  refine ⟨R, hR', ?_⟩
  intro ρ hζ hlt
  have hρmem : ρ ∈ Metric.ball z (2 / 5 : ℝ) := by
    rw [Metric.mem_ball, Complex.dist_eq, norm_sub_rev]
    exact hlt
  have hmapinj :
    ENat.map (Nat.cast : ℕ → ℤ) (analyticOrderAt riemannZeta ρ) = (⊤ : WithTop ℤ) ↔
      analyticOrderAt riemannZeta ρ = ⊤ := by
    rw [← ENat.map_top (Nat.cast : ℕ → ℤ)]
    exact ENat.map_natCast_injective.eq_iff
  have hd : ρ ∈ Sfin := by
    rw [hSfin_def, Set.Finite.mem_toFinset, Function.mem_support,
      MeromorphicOn.AnalyticOnNhd.divisor_apply hAnBall hρmem, ne_eq, WithTop.untop₀_eq_zero,
      not_or]
    refine ⟨?_, ?_⟩
    · rw [ENat.map_natCast_eq_zero]
      exact (hAnBall ρ hρmem).analyticOrderAt_ne_zero.mpr hζ
    · rw [hmapinj]
      exact
        riemannZeta_analyticOrderAt_ne_top_of_center
          hz1 hzgood (Metric.ball_subset_closedBall hρmem)
  have hmem : ‖z - ρ‖ ∈ D := Finset.mem_image_of_mem _ hd
  exact hRgood _ hmem

/-- The "good radius" `R`: keeps every zero within distance `2/5` of `z := σ + iT` at margin
`≥ c := 1/(40·PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensenLogConst·log(H+2))` from `R`,
on the *inside* (this is the form needed to
bound `‖P‖` from below on the boundary sphere `sphere z R`). The two-sided version
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.exists_good_radius_twoSided` additionally certifies
a genuine zero-free gap `(R - c, R + c)`,
so a factorization radius can safely be pushed slightly past `R` while capturing the same zero
set — this is what gives the extracted `g` continuity up to the closed ball `closedBall z R`
(via restriction from the larger open ball, rather than by extending `g` after the fact). -/
theorem exists_good_radius {H : ℝ} (hH : 8 ≤ H) {T : ℝ} (hT : T ∈ Set.Icc H (H + 1))
    (hgood :
      ∀ ρ : ℂ,
        riemannZeta ρ = 0 →
          |ρ.im - H| ≤ 2 →
          1 / (4 * jensenLogConst * Real.log (H + 2)) ≤
            |T - ρ.im|)
    (σ : ℝ) :
    ∃ R ∈ Set.Icc (1 / 5 : ℝ) (3 / 10),
      ∀ ρ : ℂ,
        riemannZeta ρ = 0 →
          ‖(σ + T * Complex.I) - ρ‖ < R →
          1 /
              (40 * jensenLogConst *
                Real.log (H + 2)) ≤
            R - ‖(σ + T * Complex.I) - ρ‖ := by
  obtain ⟨R, hR, hRgood⟩ :=
    exists_good_radius_twoSided hH hT hgood σ
  refine ⟨R, hR, fun ρ hζ hlt => ?_⟩
  have hthis := hRgood ρ hζ (by linarith only [hR.2, hlt] : ‖(σ + T * Complex.I) - ρ‖ < 2 / 5)
  rw [abs_sub_comm] at hthis
  rwa [abs_of_neg (by linarith [hlt] : ‖(σ + T * Complex.I) - ρ‖ - R < 0), neg_sub] at hthis

/-! ### Local factorization at the good radius, with room to spare for continuity

Combining `PseudoPrime.AnalyticNumberTheory.RiemannZeta.exists_good_radius_twoSided` with
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.exists_riemannZeta_zeroFree_factorization`: factor
`ζ` at a radius `R2` just past the good radius `R` (still inside the resulting zero-free gap),
so that `g` is analytic and zero-free on `ball z R2`. Since the eventual max-modulus domain
`ball z (R + δ/2)` has closure `closedBall z (R + δ/2) ⊆ ball z R2` (as `R + δ/2 < R2`), `g` (and
anything built from it) is automatically continuous up to that closure by plain restriction —
no separate boundary-extension argument is needed. -/

theorem exists_riemannZeta_zeroFree_factorization_good_radius {H : ℝ} (hH : 8 ≤ H) {T : ℝ}
    (hT : T ∈ Set.Icc H (H + 1))
    (hgood :
      ∀ ρ : ℂ,
        riemannZeta ρ = 0 →
          |ρ.im - H| ≤ 2 →
          1 / (4 * jensenLogConst * Real.log (H + 2)) ≤
            |T - ρ.im|)
    (σ : ℝ) :
    ∃ (R δ R2 : ℝ) (S : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
      0 < δ ∧
        R ∈ Set.Icc (1 / 5 : ℝ) (3 / 10) ∧
        R + δ / 2 < R2 ∧
        R2 < 2 / 5 ∧
        AnalyticOnNhd ℂ g (Metric.ball (σ + T * Complex.I) R2) ∧
        (∀ w ∈ Metric.ball (σ + T * Complex.I) R2, g w ≠ 0) ∧
        (∀ u ∈ S, 0 < m u) ∧
        (∀ u ∈ S, riemannZeta u = 0) ∧
        (∀ u ∈ S, ‖(σ + T * Complex.I) - u‖ ≤ R - δ) ∧
        (∑ u ∈ S, (m u : ℝ)) ≤
          jensenLogConst * Real.log (H + 2) ∧
        Set.EqOn riemannZeta (fun w => (∏ u ∈ S, (w - u) ^ m u) * g w)
          (Metric.ball (σ + T * Complex.I) R2) ∧
        ‖∑ u ∈ S, (m u : ℂ) / ((σ + T * Complex.I) - u)‖ ≤
          4 * (jensenLogConst * Real.log (H + 2)) ^ 2 ∧
        logDeriv riemannZeta (σ + T * Complex.I) =
          (∑ u ∈ S, (m u : ℂ) / ((σ + T * Complex.I) - u)) + logDeriv g (σ + T * Complex.I) := by
  set z : ℂ := σ + T * Complex.I with hz_def
  have hzim : z.im = T := by
    simp only [hz_def, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  have hTpos : (0 : ℝ) < T := by linarith [hT.1]
  have hLCpos := jensenLogConst_pos
  have hlogpos : (0 : ℝ) < Real.log (H + 2) := Real.log_pos (by linarith)
  set c : ℝ :=
    1 / (40 * jensenLogConst * Real.log (H + 2)) with
    hc_def
  have hc_pos : 0 < c := by
    rw [hc_def]; positivity
  set δ : ℝ := min c (1 / 20) with hδ_def
  have hδ_pos : 0 < δ := lt_min hc_pos (by norm_num only)
  have hδ_c : δ ≤ c := min_le_left _ _
  have hδ_small : δ ≤ 1 / 20 := min_le_right _ _
  obtain ⟨R, hR, hRgood⟩ :=
    exists_good_radius_twoSided hH hT hgood σ
  have hRgood' : ∀ ρ : ℂ, riemannZeta ρ = 0 → ‖z - ρ‖ < 2 / 5 → δ ≤ |R - ‖z - ρ‖| := fun ρ hζ hlt =>
    le_trans hδ_c (hRgood ρ hζ hlt)
  set R2 : ℝ := R + 3 * δ / 4 with hR2_def
  have hR1R2 : R + δ / 2 < R2 := by
    rw [hR2_def]; linarith
  have hR2small : R2 < 2 / 5 := by
    rw [hR2_def]; nlinarith [hR.2, hδ_small]
  have hR2pos : (0 : ℝ) < R2 := by
    rw [hR2_def]; linarith [hR.1]
  have hz1 : ∀ w ∈ Metric.closedBall z (2 / 5 : ℝ), w ≠ 1 := by
    intro w hw hw1
    rw [Metric.mem_closedBall, Complex.dist_eq, hw1] at hw
    have him : |(1 : ℂ).im - z.im| ≤ ‖(1 : ℂ) - z‖ := by
      have h := Complex.abs_im_le_norm ((1 : ℂ) - z)
      simpa only [Complex.one_im, zero_sub, abs_neg, ge_iff_le, Complex.sub_im] using h
    rw [hzim, Complex.one_im, zero_sub, abs_neg, abs_of_nonneg hTpos.le] at him
    linarith only [hH, hT.1, him, hw]
  have hzgood : riemannZeta z ≠ 0 := by
    intro hzero
    have h1 : |z.im - H| ≤ 2 := by
      rw [hzim]; rw [abs_le]; constructor <;> linarith [hT.1, hT.2]
    have h2 := hgood z hzero h1
    rw [hzim, sub_self, abs_zero] at h2
    have :
      (0 : ℝ) <
        1 /
          (4 * jensenLogConst * Real.log (H + 2)) := by
      positivity
    linarith
  have hz1R2 : ∀ w ∈ Metric.closedBall z R2, w ≠ 1 := fun w hw =>
    hz1 w (Metric.closedBall_subset_closedBall hR2small.le hw)
  obtain ⟨S, m, g, hgAn, hgne, hmpos, hSU, hSzero, hmeqSmall, heqOn, hlog⟩ :=
    exists_logDeriv_riemannZeta_eq_sum_add_logDeriv
      (R := R2) hR2pos hz1R2 hzgood
  have hu_dist : ∀ u ∈ S, ‖z - u‖ ≤ R - δ := by
    intro u hu
    have huU := hSU u hu
    rw [Metric.mem_ball, Complex.dist_eq] at huU
    have hlt_R2 : ‖z - u‖ < R2 := by
      rw [norm_sub_rev]; exact huU
    have hlt25 : ‖z - u‖ < 2 / 5 := lt_trans hlt_R2 hR2small
    have hthis := hRgood' u (hSzero u hu) hlt25
    by_contra hcon
    push Not at hcon
    have hup : ‖z - u‖ < R + δ := by
      rw [hR2_def] at hlt_R2; linarith
    have habs : |R - ‖z - u‖| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
    linarith [hthis]
  have hAnSmall : AnalyticOnNhd ℂ riemannZeta (Metric.ball z R2) := fun w hw =>
    analyticOn_riemannZeta w (hz1R2 w (Metric.ball_subset_closedBall hw))
  have hu_im_H : ∀ u ∈ S, |u.im - H| ≤ 2 := by
    intro u hu
    have huU := hSU u hu
    rw [Metric.mem_ball, Complex.dist_eq] at huU
    have h := Complex.abs_im_le_norm (u - z)
    rw [Complex.sub_im, hzim] at h
    have h2 : |u.im - T| < R2 := lt_of_le_of_lt h huU
    have h2' : |u.im - T| < 2 / 5 := lt_trans h2 hR2small
    rw [abs_lt] at h2'
    rw [abs_le]
    constructor <;> linarith [h2'.1, h2'.2, hT.1, hT.2]
  have hAnBig :
    AnalyticOnNhd ℂ riemannZeta
      (Metric.closedBall (jensenCenter H) (37 / 10)) :=
    (jensen_analyticOnNhd
          (by linarith : (4 : ℝ) ≤ H)).mono
      (Metric.closedBall_subset_closedBall (by norm_num only))
  have hSbig :
    ∀ u ∈ S,
      u ∈
        Metric.closedBall (jensenCenter H) (37 / 10) :=
    fun u hu =>
    riemannZeta_zero_mem_jensenBall hH (hSzero u hu)
      (hu_im_H u hu)
  have hfin :=
    (MeromorphicOn.divisor riemannZeta
          (Metric.closedBall (jensenCenter H)
            (37 / 10))).finiteSupport
      (isCompact_closedBall _ _)
  have hmeqBig :
    ∀ u ∈ S,
      (m u : ℤ) =
        MeromorphicOn.divisor riemannZeta
          (Metric.closedBall (jensenCenter H)
            (37 / 10))
          u :=
    fun u hu =>
    (hmeqSmall u hu).trans
      (divisor_riemannZeta_eq_of_analyticOnNhd hAnSmall
        hAnBig (hSU u hu) (hSbig u hu))
  have hSsub : S ⊆ hfin.toFinset := by
    intro u hu
    rw [Set.Finite.mem_toFinset, Function.mem_support]
    rw [← hmeqBig u hu]
    exact_mod_cast (hmpos u hu).ne'
  have hsum_le :
    (∑ u ∈ S, (m u : ℝ)) ≤
      jensenLogConst * Real.log (H + 2) := by
    have hcongr :
      ∑ u ∈ S, (m u : ℝ) =
        ∑ u ∈ S,
          (MeromorphicOn.divisor riemannZeta
              (Metric.closedBall (jensenCenter H)
                (37 / 10))
              u :
            ℝ) :=
      Finset.sum_congr rfl (fun u hu => by exact_mod_cast hmeqBig u hu)
    rw [hcongr]
    have hcard1 :
      ∑ u ∈ S,
          (MeromorphicOn.divisor riemannZeta
      (Metric.closedBall (jensenCenter H)
        (37 / 10))
              u :
            ℝ) ≤
        ∑ u ∈ hfin.toFinset,
          (MeromorphicOn.divisor riemannZeta
              (Metric.closedBall (jensenCenter H)
                (37 / 10))
              u :
            ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hSsub
      intro u _ _
      exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAnBig u
    have hcard2 :
      ∑ u ∈ hfin.toFinset,
          (MeromorphicOn.divisor riemannZeta
              (Metric.closedBall (jensenCenter H)
                (37 / 10))
              u :
            ℝ) =
        ((∑ᶠ u,
              MeromorphicOn.divisor riemannZeta
                (Metric.closedBall (jensenCenter H)
                  (37 / 10))
                u :
            ℤ) :
          ℝ) := by
      rw [finsum_eq_finsetSum_of_support_subset _ (s := hfin.toFinset)
          (by rw [Set.Finite.coe_toFinset])]
      push_cast
      rfl
    rw [hcard2] at hcard1
    exact
      hcard1.trans
        (finsum_divisor_riemannZeta_le_explicit hH)
  have hmargin :
    ∀ u ∈ S,
      1 / (4 * jensenLogConst * Real.log (H + 2)) ≤
        ‖z - u‖ := by
    intro u hu
    have hmarg := hgood u (hSzero u hu) (hu_im_H u hu)
    have hle : |T - u.im| ≤ ‖z - u‖ := by
      have h := Complex.abs_im_le_norm (z - u)
      rw [Complex.sub_im, hzim] at h
      exact h
    linarith [hmarg, hle]
  have hnormsum_le :
    ‖∑ u ∈ S, (m u : ℂ) / (z - u)‖ ≤
      4 * (jensenLogConst * Real.log (H + 2)) ^ 2 := by
    have hmarginpos :
      (0 : ℝ) <
        4 * jensenLogConst * Real.log (H + 2) := by
      positivity
    calc
      ‖∑ u ∈ S, (m u : ℂ) / (z - u)‖ ≤ ∑ u ∈ S, ‖(m u : ℂ) / (z - u)‖ := norm_sum_le _ _
      _ = ∑ u ∈ S, (m u : ℝ) / ‖z - u‖ := by
        apply Finset.sum_congr rfl
        intro u _
        rw [norm_div, Complex.norm_natCast]
      _ ≤
          ∑ u ∈ S,
            (m u : ℝ) *
              (4 * jensenLogConst *
                Real.log (H + 2)) :=
        by
        apply Finset.sum_le_sum
        intro u hu
        have hrecip :
          1 / ‖z - u‖ ≤
            4 * jensenLogConst * Real.log (H + 2) := by
          have h1 := one_div_le_one_div_of_le (by positivity) (hmargin u hu)
          rwa [one_div_one_div] at h1
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left hrecip (Nat.cast_nonneg _)
      _ =
          (∑ u ∈ S, (m u : ℝ)) *
            (4 * jensenLogConst * Real.log (H + 2)) :=
        by rw [Finset.sum_mul]
      _ ≤
          (jensenLogConst * Real.log (H + 2)) *
            (4 * jensenLogConst * Real.log (H + 2)) :=
        by apply mul_le_mul_of_nonneg_right hsum_le (by positivity)
      _ =
          4 *
            (jensenLogConst * Real.log (H + 2)) ^ 2 :=
        by ring
  exact
    ⟨R, δ, R2, S, m, g, hδ_pos, hR, hR1R2, hR2small, hgAn, hgne, hmpos, hSzero, hu_dist, hsum_le,
      heqOn, hnormsum_le, hlog⟩

/-!
### Zeta growth on a small disk around a good-height point

Use the sawtooth bound with norm, real-part, and pole-distance estimates on
a disk of radius less than `2/5` around `σ+iT`.
-/

theorem norm_riemannZeta_le_on_good_radius_ball {H : ℝ} (hH : 8 ≤ H) {T : ℝ}
    (hT : T ∈ Set.Icc H (H + 1)) {σ : ℝ} (hσ1 : -(1 : ℝ) / 2 ≤ σ) (_hσ2 : σ ≤ 2) {R1 : ℝ}
    (hR1 : 0 < R1) (hR1small : R1 < 2 / 5) :
    ∀ w ∈ Metric.closedBall (σ + T * Complex.I) R1,
      ‖riemannZeta w‖ ≤
        (‖σ + T * Complex.I‖ + R1) / (T - R1) + 1 / 2 +
          (‖σ + T * Complex.I‖ + R1) * (‖σ + T * Complex.I‖ + R1 + 1) *
            sawtoothRemainderBound (-9 / 10) := by
  set z : ℂ := σ + T * Complex.I with hz_def
  have hzim : z.im = T := by
    simp only [hz_def, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  have hzre : z.re = σ := by
    simp only [hz_def, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hTpos : (0 : ℝ) < T := by linarith [hT.1]
  intro w hw
  simp only [Metric.mem_closedBall, dist_eq_norm] at hw
  have hwre : σ - R1 ≤ w.re := by
    have h1 : |w.re - z.re| ≤ ‖w - z‖ := by
      have h := Complex.abs_re_le_norm (w - z)
      simpa only [ge_iff_le, Complex.sub_re] using h
    rw [hzre] at h1
    have := (abs_le.mp h1).1
    linarith
  have hwim : T - R1 ≤ w.im := by
    have h1 : |w.im - z.im| ≤ ‖w - z‖ := by
      have h := Complex.abs_im_le_norm (w - z)
      simpa only [ge_iff_le, Complex.sub_im] using h
    rw [hzim] at h1
    have := (abs_le.mp h1).1
    linarith
  have hzmem : w ∈ ({s : ℂ | -1 < s.re} \ {(1 : ℂ)}) := by
    refine ⟨?_, ?_⟩
    · change (-1 : ℝ) < w.re
      linarith [hwre, hσ1, hR1small]
    · simp only [Set.mem_singleton_iff]
      intro hw1
      rw [hw1, Complex.one_im] at hwim
      linarith [hT.1, hR1small]
  have hb :=
    norm_riemannZeta_le_of_reGt_neg_one_diff_one hzmem
  have hnw : ‖w‖ ≤ ‖z‖ + R1 := by
    have h1 : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
      have h := norm_add_le z (w - z)
      simpa only [ge_iff_le, add_sub_cancel] using h
    linarith [h1, hw]
  have hnw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
  have hwre9 : (-9 : ℝ) / 10 ≤ w.re := by linarith [hwre, hσ1, hR1small]
  have hwsub1 : T - R1 ≤ ‖w - 1‖ := by
    have h1 : |(w - 1).im| ≤ ‖w - 1‖ := Complex.abs_im_le_norm (w - 1)
    rw [Complex.sub_im, Complex.one_im, sub_zero] at h1
    have h2 := le_abs_self w.im
    linarith [h1, h2, hwim]
  have hwsub1_pos : (0 : ℝ) < T - R1 := by linarith [hT.1, hR1small]
  have hwsub1_pos' : (0 : ℝ) < ‖w - 1‖ := lt_of_lt_of_le hwsub1_pos hwsub1
  have hterm1 : ‖w‖ / ‖w - 1‖ ≤ (‖z‖ + R1) / (T - R1) := by
    rw [div_le_div_iff₀ hwsub1_pos' hwsub1_pos]
    have h1 : ‖w‖ * (T - R1) ≤ (‖z‖ + R1) * (T - R1) := mul_le_mul_of_nonneg_right hnw hwsub1_pos.le
    have h2 : (‖z‖ + R1) * (T - R1) ≤ (‖z‖ + R1) * ‖w - 1‖ :=
      mul_le_mul_of_nonneg_left hwsub1 (by positivity)
    linarith
  have hterm3 :
    ‖w‖ * (‖w‖ + 1) * sawtoothRemainderBound w.re ≤
      (‖z‖ + R1) * (‖z‖ + R1 + 1) *
        sawtoothRemainderBound (-9 / 10) := by
    have hanti :
      sawtoothRemainderBound w.re ≤
        sawtoothRemainderBound (-9 / 10) :=
      sawtoothRemainderBound_antitone
        (by norm_num only) hwre9
    have hbndnn0 :
      (0 : ℝ) ≤ sawtoothRemainderBound w.re :=
      sawtoothRemainderBound_nonneg w.re
    have h1 : ‖w‖ * (‖w‖ + 1) ≤ (‖z‖ + R1) * (‖z‖ + R1 + 1) :=
      mul_le_mul hnw (by linarith) (by linarith) (by linarith)
    exact mul_le_mul h1 hanti hbndnn0 (by positivity)
  linarith [hb, hterm1, hterm3]

/-! ### Extending a boundary bound on `Re h` to the whole region via the exponential trick

A general, `ζ`-independent fact: if `h` is holomorphic on a bounded region and `Re h ≤ M` on its
frontier, then `Re h ≤ M` throughout (apply the ordinary maximum modulus principle to
`exp(h - M)`, whose norm is `exp(Re h - M)`). -/

theorem re_le_of_forall_mem_frontier_re_le {h : ℂ → ℂ} {U : Set ℂ} (hU : Bornology.IsBounded U)
    (hd : DiffContOnCl ℂ h U) {M : ℝ} (hM : ∀ w ∈ frontier U, (h w).re ≤ M) {z : ℂ}
    (hz : z ∈ closure U) : (h z).re ≤ M := by
  set F : ℂ → ℂ := fun w => Complex.exp (h w - (M : ℂ)) with hF_def
  have hFdiffContOnCl : DiffContOnCl ℂ F U := by
    constructor
    · intro w hw
      exact ((hd.differentiableOn w hw).sub_const (M : ℂ)).cexp
    · exact Complex.continuous_exp.comp_continuousOn (hd.continuousOn.sub continuousOn_const)
  have hFbound : ∀ w ∈ frontier U, ‖F w‖ ≤ 1 := by
    intro w hw
    rw [hF_def]
    change ‖Complex.exp (h w - (M : ℂ))‖ ≤ 1
    rw [Complex.norm_exp]
    have hre : (h w - (M : ℂ)).re = (h w).re - M := by simp only [Complex.sub_re, Complex.ofReal_re]
    rw [hre]
    exact Real.exp_le_one_iff.mpr (by linarith [hM w hw])
  have hFz : ‖F z‖ ≤ 1 :=
    Complex.norm_le_of_forall_mem_frontier_norm_le hU hFdiffContOnCl hFbound hz
  rw [hF_def] at hFz
  change (h z).re ≤ M
  have hre : (h z - (M : ℂ)).re = (h z).re - M := by simp only [Complex.sub_re, Complex.ofReal_re]
  rw [Complex.norm_exp, hre] at hFz
  have := Real.exp_le_one_iff.mp hFz
  linarith

/-! ### The boundary bound on `Re h`, extended to the whole disk

Combining the `ζ`-growth bound
(`PseudoPrime.AnalyticNumberTheory.RiemannZeta.norm_riemannZeta_le_on_good_radius_ball`)
with the good-radius margin (`‖w - u‖ ≥ 3δ/2` on `sphere z R1` for each extracted zero `u`,
since `u` sits at distance
`≤ R - δ` from `z` while `R1 = R + δ/2`) gives `Re h ≤ M` on `sphere z R1 = frontier (ball z R1)`
for an explicit `M`;
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.re_le_of_forall_mem_frontier_re_le`
then extends this to all of
`closedBall z R1`. Continuity of `h` up to that closed ball is automatic, since
`closedBall z R1 ⊆ ball z R2` (as `R1 < R2`) and `h` already has a genuine derivative throughout
`ball z R2`. -/

theorem exists_bound_re_logDeriv_g_good_radius {H : ℝ} (hH : 8 ≤ H) {T : ℝ}
    (hT : T ∈ Set.Icc H (H + 1))
    (hgood :
      ∀ ρ : ℂ,
        riemannZeta ρ = 0 →
          |ρ.im - H| ≤ 2 →
          1 / (4 * jensenLogConst * Real.log (H + 2)) ≤
            |T - ρ.im|)
    {σ : ℝ} (hσ1 : -(1 : ℝ) / 2 ≤ σ) (hσ2 : σ ≤ 2) :
    ∃ (R1 R2 : ℝ) (S : Finset ℂ) (m : ℂ → ℕ) (g h : ℂ → ℂ) (M : ℝ),
      0 < R1 ∧
        R1 < R2 ∧
        R2 < 2 / 5 ∧
        (∀ w ∈ Metric.ball (σ + T * Complex.I) R2, HasDerivAt h (logDeriv g w) w) ∧
        logDeriv riemannZeta (σ + T * Complex.I) =
          (∑ u ∈ S, (m u : ℂ) / ((σ + T * Complex.I) - u)) + logDeriv g (σ + T * Complex.I) ∧
        ‖∑ u ∈ S, (m u : ℂ) / ((σ + T * Complex.I) - u)‖ ≤
          4 * (jensenLogConst * Real.log (H + 2)) ^ 2 ∧
        (∀ w ∈ Metric.closedBall (σ + T * Complex.I) R1, (h w).re ≤ M) := by
  obtain
    ⟨R, δ, R2, S, m, g, hδ_pos, hR, hR1R2, hR2small, hgAn, hgne, hmpos, hSzero, hu_dist, hsum_le,
      heqOn, hnormsum_le, hlog⟩ :=
    exists_riemannZeta_zeroFree_factorization_good_radius
      hH hT hgood σ
  set z : ℂ := σ + T * Complex.I with hz_def
  set R1 : ℝ := R + δ / 2 with hR1_def
  have hR1pos : (0 : ℝ) < R1 := by
    rw [hR1_def]; linarith [hR.1]
  have hR1lt25 : R1 < 2 / 5 := lt_trans hR1R2 hR2small
  have hR2pos : (0 : ℝ) < R2 := lt_trans hR1pos hR1R2
  obtain ⟨h, hh', hh_re⟩ :=
    exists_hasDerivAt_logDeriv_re_eq_log_norm (f := g)
      (c := z) (r := R2) hR2pos hgAn hgne
  have hR1subR2 : Metric.closedBall z R1 ⊆ Metric.ball z R2 := by
    intro w hw
    rw [Metric.mem_closedBall] at hw
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt hw hR1R2
  have hdiff : DifferentiableOn ℂ h (Metric.ball z R1) := fun w hw =>
    (hh' w (hR1subR2 (Metric.ball_subset_closedBall hw))).differentiableAt.differentiableWithinAt
  have hcont : ContinuousOn h (Metric.closedBall z R1) := fun w hw =>
    (hh' w (hR1subR2 hw)).continuousAt.continuousWithinAt
  have hR1ne : R1 ≠ 0 := hR1pos.ne'
  have hclosure : closure (Metric.ball z R1) = Metric.closedBall z R1 := closure_ball z hR1ne
  have hdcc : DiffContOnCl ℂ h (Metric.ball z R1) :=
    ⟨hdiff, by
      rw [hclosure]; exact hcont⟩
  have hζbound :=
    norm_riemannZeta_le_on_good_radius_ball hH hT hσ1
      hσ2 hR1pos hR1lt25
  set Mζ : ℝ :=
    (‖z‖ + R1) / (T - R1) + 1 / 2 +
      (‖z‖ + R1) * (‖z‖ + R1 + 1) *
        sawtoothRemainderBound (-9 / 10) with
    hMζ_def
  set Nmax : ℝ :=
    jensenLogConst * Real.log (H + 2) with hNmax_def
  set M : ℝ := Real.log Mζ - Nmax * Real.log (3 * δ / 2) with hM_def
  have hδlt : δ < 2 / 5 := by
    rw [hR1_def] at hR1R2; linarith [hR.1, hR2small]
  have h3δ2 : 3 * δ / 2 < 1 := by linarith [hδlt]
  have h3δ2pos : (0 : ℝ) < 3 * δ / 2 := by linarith [hδ_pos]
  have hlogneg : Real.log (3 * δ / 2) ≤ 0 := Real.log_nonpos h3δ2pos.le h3δ2.le
  have hNmaxnn : (0 : ℝ) ≤ Nmax := by
    have hLCpos := jensenLogConst_pos
    have hlogpos : (0 : ℝ) < Real.log (H + 2) := Real.log_pos (by linarith)
    rw [hNmax_def]; positivity
  refine ⟨R1, R2, S, m, g, h, M, hR1pos, hR1R2, hR2small, hh', hlog, hnormsum_le, ?_⟩
  have hMbound : ∀ w ∈ frontier (Metric.ball z R1), (h w).re ≤ M := by
    intro w hwf
    rw [frontier_ball z hR1ne, Metric.mem_sphere] at hwf
    have hwR1 : w ∈ Metric.closedBall z R1 := by
      rw [Metric.mem_closedBall]; exact hwf.le
    have hwR2 : w ∈ Metric.ball z R2 := hR1subR2 hwR1
    have hPlb : ∀ u ∈ S, 3 * δ / 2 ≤ ‖w - u‖ := by
      intro u hu
      have h1 : ‖z - u‖ ≤ R - δ := hu_dist u hu
      have h3 : ‖w - z‖ = R1 := by
        rw [← dist_eq_norm]; exact hwf
      have htri : ‖w - z‖ ≤ ‖w - u‖ + ‖u - z‖ := by
        have h := norm_add_le (w - u) (u - z)
        simpa only [ge_iff_le, sub_add_sub_cancel] using h
      rw [norm_sub_rev u z, h3] at htri
      linarith [htri, h1, hR1_def]
    have hPfactor_pos : ∀ u ∈ S, (0 : ℝ) < ‖w - u‖ := fun u hu => lt_of_lt_of_le h3δ2pos (hPlb u hu)
    have hPne : (∏ u ∈ S, (w - u) ^ m u) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro u hu
      exact pow_ne_zero _ (norm_pos_iff.mp (hPfactor_pos u hu))
    have hζval : riemannZeta w = (∏ u ∈ S, (w - u) ^ m u) * g w := heqOn hwR2
    have hgval : g w = riemannZeta w / (∏ u ∈ S, (w - u) ^ m u) := by
      rw [hζval, mul_div_cancel_left₀ (g w) hPne]
    have hgw_ne : g w ≠ 0 := hgne w hwR2
    have hnormg : ‖g w‖ = ‖riemannZeta w‖ / ‖∏ u ∈ S, (w - u) ^ m u‖ := by rw [hgval, norm_div]
    have hnormP : ‖∏ u ∈ S, (w - u) ^ m u‖ = ∏ u ∈ S, ‖w - u‖ ^ m u := by
      rw [norm_prod]
      exact Finset.prod_congr rfl (fun u _ => norm_pow (w - u) (m u))
    have hlogP : Real.log (∏ u ∈ S, ‖w - u‖ ^ m u) = ∑ u ∈ S, (m u : ℝ) * Real.log ‖w - u‖ := by
      rw [Real.log_prod (fun u hu => (pow_pos (hPfactor_pos u hu) (m u)).ne')]
      exact Finset.sum_congr rfl (fun u _ => Real.log_pow ‖w - u‖ (m u))
    have hlogP_lb :
      (∑ u ∈ S, (m u : ℝ)) * Real.log (3 * δ / 2) ≤ ∑ u ∈ S, (m u : ℝ) * Real.log ‖w - u‖ := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro u hu
      have hlogle : Real.log (3 * δ / 2) ≤ Real.log ‖w - u‖ := Real.log_le_log h3δ2pos (hPlb u hu)
      exact mul_le_mul_of_nonneg_left hlogle (Nat.cast_nonneg (m u))
    have hNmax_le : Nmax * Real.log (3 * δ / 2) ≤ (∑ u ∈ S, (m u : ℝ)) * Real.log (3 * δ / 2) :=
      mul_le_mul_of_nonpos_right hsum_le hlogneg
    have hlogPw_ge : Nmax * Real.log (3 * δ / 2) ≤ Real.log ‖∏ u ∈ S, (w - u) ^ m u‖ := by
      rw [hnormP, hlogP]
      linarith [hNmax_le, hlogP_lb]
    have hζw_pos : (0 : ℝ) < ‖riemannZeta w‖ := by
      rw [hζval]
      exact norm_pos_iff.mpr (mul_ne_zero hPne hgw_ne)
    have hPw_pos : (0 : ℝ) < ‖∏ u ∈ S, (w - u) ^ m u‖ := norm_pos_iff.mpr hPne
    have hζw : ‖riemannZeta w‖ ≤ Mζ := hζbound w hwR1
    have hloggw :
      Real.log ‖g w‖ = Real.log ‖riemannZeta w‖ - Real.log ‖∏ u ∈ S, (w - u) ^ m u‖ := by
      rw [hnormg, Real.log_div hζw_pos.ne' hPw_pos.ne']
    rw [hh_re w hwR2, hloggw]
    have hlogζ_le : Real.log ‖riemannZeta w‖ ≤ Real.log Mζ := Real.log_le_log hζw_pos hζw
    rw [hM_def]
    linarith [hlogζ_le, hlogPw_ge]
  intro w hw
  refine
    re_le_of_forall_mem_frontier_re_le
      (Metric.isBounded_ball) hdcc hMbound ?_
  rw [hclosure]; exact hw

/-!
### Off-center derivative estimates

For `h'=F` on `ball c R`, a bound `Re h ≤ M` and a strict center bound
control `F` at every interior point. Shift to the origin, apply
Borel–Carathéodory, then use Cauchy's estimate on a circle about the evaluation point.
-/

theorem norm_hasDerivAt_le_of_re_le {h F : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hh' : ∀ w ∈ Metric.ball c R, HasDerivAt h (F w) w) {M : ℝ} (hMc : (h c).re < M)
    (hRe_le : ∀ w ∈ Metric.ball c R, (h w).re ≤ M) {z : ℂ} (hz : z ∈ Metric.ball c R) :
    ‖F z‖ ≤ 4 * (M - (h c).re) * (R + ‖z - c‖) / (R - ‖z - c‖) ^ 2 := by
  set M' : ℝ := M - (h c).re with hM'_def
  have hM'pos : 0 < M' := by
    rw [hM'_def]; linarith
  set hs : ℂ → ℂ := fun w => h (c + w) - h c with hhs_def
  have hs_diffOn : DifferentiableOn ℂ hs (Metric.ball (0 : ℂ) R) := by
    intro w hw
    have hcw_mem : c + w ∈ Metric.ball c R := by
      simpa only [Metric.mem_ball, dist_self_add_left, dist_zero_right] using hw
    exact
      (((hh' (c + w) hcw_mem).differentiableAt).comp w (differentiableAt_id.const_add c)).sub_const
          (h c) |>.differentiableWithinAt
  have hs0 : hs 0 = 0 := by simp only [hhs_def, add_zero, sub_self]
  have hs_bound : ∀ w ∈ Metric.ball (0 : ℂ) R, (hs w).re ≤ M' := by
    intro w hw
    have hcw_mem : c + w ∈ Metric.ball c R := by
      simpa only [Metric.mem_ball, dist_self_add_left, dist_zero_right] using hw
    have := hRe_le (c + w) hcw_mem
    simp only [hhs_def, Complex.sub_re, hM'_def]
    linarith
  have hBC : ∀ w ∈ Metric.ball (0 : ℂ) R, ‖hs w‖ ≤ 2 * M' * ‖w‖ / (R - ‖w‖) := fun w hw =>
    Complex.borelCaratheodory_zero hM'pos hs_diffOn (fun v hv => hs_bound v hv) hR hw hs0
  set d : ℝ := ‖z - c‖ with hd_def
  have hdR : d < R := by
    rw [hd_def]; simpa only [Metric.mem_ball, Complex.dist_eq] using hz
  have hdnn : 0 ≤ d := norm_nonneg _
  set r : ℝ := (R - d) / 2 with hr_def
  have hrpos : 0 < r := by
    rw [hr_def]; linarith
  set wz : ℂ := z - c with hwz_def
  have hwz_norm : ‖wz‖ = d := hd_def.symm
  have hclose_mem : ∀ w : ℂ, dist w wz ≤ r → w ∈ Metric.ball (0 : ℂ) R := by
    intro w hw
    have hle : ‖w‖ ≤ (R + d) / 2 := by
      calc
        ‖w‖ ≤ ‖wz‖ + dist w wz := by
          have h := norm_add_le wz (w - wz)
          simpa only [dist_eq_norm, ge_iff_le, add_sub_cancel] using h
        _ ≤ d + r := by
          rw [hwz_norm]; linarith
        _ = (R + d) / 2 := by
          rw [hr_def]; ring
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hf_diffOn : DifferentiableOn ℂ hs (Metric.ball wz r) :=
    hs_diffOn.mono (fun w hw => hclose_mem w (le_of_lt (Metric.mem_ball.mp hw)))
  have hf_diffContOnCl : DiffContOnCl ℂ hs (Metric.ball wz r) := by
    constructor
    · exact hf_diffOn
    · have hDiffCl : DifferentiableOn ℂ hs (closure (Metric.ball wz r)) :=
        hs_diffOn.mono
          (fun w hw =>
            hclose_mem w (Metric.mem_closedBall.mp (Metric.closure_ball_subset_closedBall hw)))
      exact hDiffCl.continuousOn
  set C : ℝ := 2 * M' * ((R + d) / 2) / (R - (R + d) / 2) with hC_def
  have hsphere_bound : ∀ w ∈ Metric.sphere wz r, ‖hs w‖ ≤ C := by
    intro w hw
    have hw_dist : dist w wz = r := Metric.mem_sphere.mp hw
    have hw_norm_le : ‖w‖ ≤ (R + d) / 2 := by
      calc
        ‖w‖ ≤ ‖wz‖ + dist w wz := by
          have h := norm_add_le wz (w - wz)
          simpa only [dist_eq_norm, ge_iff_le, add_sub_cancel] using h
        _ = d + r := by rw [hwz_norm, hw_dist]
        _ = (R + d) / 2 := by
          rw [hr_def]; ring
    have hw_mem : w ∈ Metric.ball (0 : ℂ) R := hclose_mem w hw_dist.le
    have h1 : (0 : ℝ) < R - (R + d) / 2 := by linarith [hdR]
    have h2 : (0 : ℝ) < R - ‖w‖ := by
      have h3 := Metric.mem_ball.mp hw_mem
      rw [dist_zero_right] at h3
      linarith
    have hmono : 2 * M' * ‖w‖ / (R - ‖w‖) ≤ C := by
      rw [hC_def, div_le_div_iff₀ h2 h1]
      have h3 : ‖w‖ * (R - (R + d) / 2) ≤ ((R + d) / 2) * (R - (R + d) / 2) :=
        mul_le_mul_of_nonneg_right hw_norm_le h1.le
      have h4 : ((R + d) / 2) * (R - (R + d) / 2) ≤ ((R + d) / 2) * (R - ‖w‖) :=
        mul_le_mul_of_nonneg_left (by linarith only [hw_norm_le]) (by linarith only [hdnn, hR])
      have hchain : ‖w‖ * (R - (R + d) / 2) ≤ (R + d) / 2 * (R - ‖w‖) := h3.trans h4
      have h2M'nn : (0 : ℝ) ≤ 2 * M' := by linarith only [hM'pos]
      calc
        2 * M' * ‖w‖ * (R - (R + d) / 2) = 2 * M' * (‖w‖ * (R - (R + d) / 2)) := by ring
        _ ≤ 2 * M' * ((R + d) / 2 * (R - ‖w‖)) := mul_le_mul_of_nonneg_left hchain h2M'nn
        _ = 2 * M' * ((R + d) / 2) * (R - ‖w‖) := by ring
    exact (hBC w hw_mem).trans hmono
  have hcauchy :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (f := hs) (c := wz) (R := r) (C := C)
      1 hrpos hf_diffContOnCl hsphere_bound
  simp only [iteratedDeriv_one] at hcauchy
  have hderivf : deriv hs wz = F z := by
    have heq : c + wz = z := by
      rw [hwz_def]; ring
    have hderivh : HasDerivAt h (F z) (c + wz) := by
      rw [heq]; exact hh' z hz
    have hcomp : HasDerivAt (fun w => h (c + w)) (F z) wz := hderivh.comp_const_add c wz
    exact (hcomp.sub_const (h c)).deriv
  rw [hderivf] at hcauchy
  have hfactor : (Nat.factorial 1 : ℝ) * C / r ^ 1 = 4 * M' * (R + d) / (R - d) ^ 2 := by
    have hRd_pos : (0 : ℝ) < R - d := by linarith [hdR]
    have hRd_ne : R - d ≠ 0 := hRd_pos.ne'
    have hr_ne : r ≠ 0 := hrpos.ne'
    rw [hC_def, hr_def, Nat.factorial_one, Nat.cast_one, one_mul]
    have h1 : R - (R + d) / 2 = (R - d) / 2 := by ring
    rw [h1]
    rw [div_div, pow_one]
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [hfactor] at hcauchy
  rw [hM'_def] at hcauchy
  exact hcauchy

/-! ### A Jensen-scale good radius, centered at `jensenCenter T`

Mirrors `PseudoPrime.AnalyticNumberTheory.RiemannZeta.exists_good_radius_twoSided`,
but centered at `PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensenCenter T` instead of
the evaluation point, with the good radius near `37/10` instead of near `1/5`. Since
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensenCenter T` (real part `3`) is far enough
from the target range `σ ∈ [-1/2, 2]` (distance up to `7/2`) that no small
disk around the evaluation point can reach a point where `‖ζ‖` is known to be bounded away from
`0`, the Borel–Carathéodory reference point must be
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensenCenter T` itself — reusing
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensen_center_norm_ge`.
Since `37/10` already exceeds the needed `7/2` reach with room to
spare, and `PseudoPrime.AnalyticNumberTheory.RiemannZeta.finsum_divisor_riemannZeta_le_explicit`
is already generic in its height parameter
(not tied to a separately-chosen `H`), this reuses the zeta-side estimate zero-count bound directly
at `T`, with no need to extend it to a bigger radius or to embed via a separate
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensenCenter H` disk. -/

theorem exists_jensen_good_radius_twoSided {T : ℝ} (hT : 8 ≤ T) :
    ∃ R ∈ Set.Icc (71 / 20 : ℝ) (73 / 20),
      ∀ ρ : ℂ,
        riemannZeta ρ = 0 →
          ‖jensenCenter T - ρ‖ < 37 / 10 →
          1 /
              (40 * jensenLogConst *
                Real.log (T + 2)) ≤
            |R - ‖jensenCenter T - ρ‖| := by
  set z : ℂ := jensenCenter T with hz_def
  have hT4 : (4 : ℝ) ≤ T := by linarith
  have hz1 : ∀ w ∈ Metric.closedBall z (37 / 10 : ℝ), w ≠ 1 := fun w hw =>
    (jensenBall_subset hT4
        (Metric.closedBall_subset_closedBall (by norm_num only) hw)).2
  have hzgood : riemannZeta z ≠ 0 :=
    jensen_center_ne_zero T
  have hAnClosed : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall z (37 / 10 : ℝ)) := fun w hw =>
    analyticOn_riemannZeta w (hz1 w hw)
  have hAnBall : AnalyticOnNhd ℂ riemannZeta (Metric.ball z (37 / 10 : ℝ)) := fun w hw =>
    hAnClosed w (Metric.ball_subset_closedBall hw)
  have hfin : (MeromorphicOn.divisor riemannZeta (Metric.ball z (37 / 10 : ℝ))).support.Finite :=
    MeromorphicOn.divisor_ball_support_finite hAnClosed.meromorphicOn
  set Sfin : Finset ℂ := hfin.toFinset with hSfin_def
  set D : Finset ℝ := Sfin.image (fun ρ => ‖z - ρ‖) with hD_def
  have hcard :
    (D.card : ℝ) ≤
      jensenLogConst * Real.log (T + 2) := by
    have hfinBig :=
      (MeromorphicOn.divisor riemannZeta (Metric.closedBall z (37 / 10 : ℝ))).finiteSupport
        (isCompact_closedBall _ _)
    have h1 : D.card ≤ Sfin.card := Finset.card_image_le
    have h2 : Sfin.card ≤ hfinBig.toFinset.card :=
      Finset.card_le_card
        (by
          intro u hu
          rw [Set.Finite.mem_toFinset, Function.mem_support]
          have huU : u ∈ Metric.ball z (37 / 10 : ℝ) := by
            rw [hSfin_def, Set.Finite.mem_toFinset] at hu
            exact (MeromorphicOn.divisor riemannZeta (Metric.ball z (37 / 10 : ℝ))
            ).supportWithinDomain hu
          rw [←
            divisor_riemannZeta_eq_of_analyticOnNhd
              hAnBall hAnClosed huU (Metric.ball_subset_closedBall huU)]
          rw [hSfin_def, Set.Finite.mem_toFinset] at hu
          exact hu)
    have h3 :
      (hfinBig.toFinset.card : ℝ) ≤
        ((∑ᶠ u, MeromorphicOn.divisor riemannZeta (Metric.closedBall z (37 / 10 : ℝ)) u : ℤ) : ℝ
        ) := by
      have heach :
        ∀ u ∈ hfinBig.toFinset,
          (1 : ℤ) ≤ MeromorphicOn.divisor riemannZeta (Metric.closedBall z (37 / 10 : ℝ)) u := by
        intro u hu
        rw [Set.Finite.mem_toFinset, Function.mem_support] at hu
        have hnn : (0 : ℤ) ≤ MeromorphicOn.divisor riemannZeta (Metric.closedBall z (37 / 10 : ℝ)
        ) u :=
          MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAnClosed u
        omega
      calc
        (hfinBig.toFinset.card : ℝ) = ∑ _u ∈ hfinBig.toFinset, (1 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤
            ∑ u ∈ hfinBig.toFinset,
              (MeromorphicOn.divisor riemannZeta (Metric.closedBall z (37 / 10 : ℝ)) u : ℝ) :=
          by
          apply Finset.sum_le_sum
          intro u hu
          exact_mod_cast heach u hu
        _ = ((∑ᶠ u, MeromorphicOn.divisor riemannZeta (Metric.closedBall z (37 / 10 : ℝ)) u : ℤ) : ℝ
        ) := by
          rw [finsum_eq_finsetSum_of_support_subset _ (s := hfinBig.toFinset)
              (by rw [Set.Finite.coe_toFinset])]
          push_cast
          rfl
    have h4 :=
      finsum_divisor_riemannZeta_le_explicit hT
    calc
      (D.card : ℝ) ≤ (Sfin.card : ℝ) := by exact_mod_cast h1
      _ ≤ (hfinBig.toFinset.card : ℝ) := by exact_mod_cast h2
      _ ≤ _ := h3
      _ ≤ jensenLogConst * Real.log (T + 2) := h4
  set c : ℝ :=
    1 / (40 * jensenLogConst * Real.log (T + 2)) with
    hc_def
  have hLCpos := jensenLogConst_pos
  have hlogpos : (0 : ℝ) < Real.log (T + 2) := Real.log_pos (by linarith)
  have hc_pos : 0 < c := by
    rw [hc_def]; positivity
  have hlen : 2 * c * (D.card : ℝ) < (1 / 10 : ℝ) := by
    calc
      2 * c * (D.card : ℝ) ≤
          2 * c *
            (jensenLogConst * Real.log (T + 2)) :=
        mul_le_mul_of_nonneg_left hcard (by positivity)
      _ = 1 / 20 := by
        rw [hc_def]; field_simp; norm_num only
      _ < 1 / 10 := by norm_num only
  obtain ⟨R, hR, hRgood⟩ :=
    exists_avoiding_point_length (a := 71 / 20) hc_pos
      (by norm_num only : (0 : ℝ) < 1 / 10) hlen
  have hR' : R ∈ Set.Icc (71 / 20 : ℝ) (73 / 20) := by
    rw [show (71 / 20 : ℝ) + 1 / 10 = 73 / 20 from by norm_num only] at hR; exact hR
  refine ⟨R, hR', ?_⟩
  intro ρ hζ hlt
  have hρmem : ρ ∈ Metric.ball z (37 / 10 : ℝ) := by
    rw [Metric.mem_ball, Complex.dist_eq, norm_sub_rev]
    exact hlt
  have hmapinj :
    ENat.map (Nat.cast : ℕ → ℤ) (analyticOrderAt riemannZeta ρ) = (⊤ : WithTop ℤ) ↔
      analyticOrderAt riemannZeta ρ = ⊤ := by
    rw [← ENat.map_top (Nat.cast : ℕ → ℤ)]
    exact ENat.map_natCast_injective.eq_iff
  have hd : ρ ∈ Sfin := by
    rw [hSfin_def, Set.Finite.mem_toFinset, Function.mem_support,
      MeromorphicOn.AnalyticOnNhd.divisor_apply hAnBall hρmem, ne_eq, WithTop.untop₀_eq_zero,
      not_or]
    refine ⟨?_, ?_⟩
    · rw [ENat.map_natCast_eq_zero]
      exact (hAnBall ρ hρmem).analyticOrderAt_ne_zero.mpr hζ
    · rw [hmapinj]
      exact
        riemannZeta_analyticOrderAt_ne_top_of_center
          hz1 hzgood (Metric.ball_subset_closedBall hρmem)
  have hmem : ‖z - ρ‖ ∈ D := Finset.mem_image_of_mem _ hd
  exact hRgood _ hmem

/-! ### Jensen-scale local factorization, with room to spare for continuity

Mirrors `PseudoPrime.AnalyticNumberTheory.RiemannZeta.`
`exists_riemannZeta_zeroFree_factorization_good_radius`,
but centered at `PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensenCenter T`
with radius near `37/10` instead of centered at the evaluation point with radius near `1/5`. -/

theorem exists_riemannZeta_zeroFree_factorization_jensen_good_radius {T : ℝ} (hT : 8 ≤ T) :
    ∃ (R δ R2 : ℝ) (S : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
      0 < δ ∧
        1 /
            (40 * jensenLogConst * Real.log (T + 2) +
              50) ≤
          δ ∧
        R ∈ Set.Icc (71 / 20 : ℝ) (73 / 20) ∧
        R + δ / 2 < R2 ∧
        R2 < 37 / 10 ∧
        AnalyticOnNhd ℂ g
          (Metric.ball (jensenCenter T) R2) ∧
        (∀ w ∈ Metric.ball (jensenCenter T) R2,
          g w ≠ 0) ∧
        (∀ u ∈ S, 0 < m u) ∧
        (∀ u ∈ S, riemannZeta u = 0) ∧
        (∀ u ∈ S, ‖jensenCenter T - u‖ ≤ R - δ) ∧
        (∑ u ∈ S, (m u : ℝ)) ≤
          jensenLogConst * Real.log (T + 2) ∧
        Set.EqOn riemannZeta (fun w => (∏ u ∈ S, (w - u) ^ m u) * g w)
          (Metric.ball (jensenCenter T) R2) := by
  set z : ℂ := jensenCenter T with hz_def
  have hT4 : (4 : ℝ) ≤ T := by linarith
  have hzgood : riemannZeta z ≠ 0 :=
    jensen_center_ne_zero T
  set c : ℝ :=
    1 / (40 * jensenLogConst * Real.log (T + 2)) with
    hc_def
  have hLCpos := jensenLogConst_pos
  have hlogpos : (0 : ℝ) < Real.log (T + 2) := Real.log_pos (by linarith)
  have hc_pos : 0 < c := by
    rw [hc_def]; positivity
  set δ : ℝ := min c (1 / 50) with hδ_def
  have hδ_pos : 0 < δ := lt_min hc_pos (by norm_num only)
  have hδ_c : δ ≤ c := min_le_left _ _
  have hδ_small : δ ≤ 1 / 50 := min_le_right _ _
  have hδ_ge :
    1 / (40 * jensenLogConst * Real.log (T + 2) + 50) ≤
      δ := by
    set K : ℝ :=
      40 * jensenLogConst * Real.log (T + 2) with
      hK_def
    have hKpos : 0 < K := by
      rw [hK_def]; positivity
    have hc_eq : c = 1 / K := by rw [hc_def, hK_def]
    have h1 : 1 / (K + 50) ≤ c := by
      rw [hc_eq]; exact one_div_le_one_div_of_le hKpos (by linarith)
    have h2 : 1 / (K + 50) ≤ 1 / 50 := one_div_le_one_div_of_le (by norm_num only) (by linarith)
    rw [hδ_def]
    exact le_min h1 h2
  obtain ⟨R, hR, hRgood⟩ :=
    exists_jensen_good_radius_twoSided hT
  have hRgood' : ∀ ρ : ℂ, riemannZeta ρ = 0 → ‖z - ρ‖ < 37 / 10 → δ ≤ |R - ‖z - ρ‖| :=
    fun ρ hζ hlt => le_trans hδ_c (hRgood ρ hζ hlt)
  set R2 : ℝ := R + 3 * δ / 4 with hR2_def
  have hR1R2 : R + δ / 2 < R2 := by
    rw [hR2_def]; linarith
  have hR2small : R2 < 37 / 10 := by
    rw [hR2_def]; linarith only [hR.2, hδ_small]
  have hR2pos : (0 : ℝ) < R2 := by
    rw [hR2_def]; linarith [hR.1]
  have hz1 : ∀ w ∈ Metric.closedBall z (37 / 10 : ℝ), w ≠ 1 := fun w hw =>
    (jensenBall_subset hT4
        (Metric.closedBall_subset_closedBall (by norm_num only) hw)).2
  have hz1R2 : ∀ w ∈ Metric.closedBall z R2, w ≠ 1 := fun w hw =>
    hz1 w (Metric.closedBall_subset_closedBall hR2small.le hw)
  obtain ⟨S, m, g, hgAn, hgne, hmpos, hSU, hSzero, hmeqSmall, heqOn, hlog⟩ :=
    exists_logDeriv_riemannZeta_eq_sum_add_logDeriv
      (R := R2) hR2pos hz1R2 hzgood
  have hu_dist : ∀ u ∈ S, ‖z - u‖ ≤ R - δ := by
    intro u hu
    have huU := hSU u hu
    rw [Metric.mem_ball, Complex.dist_eq] at huU
    have hlt_R2 : ‖z - u‖ < R2 := by
      rw [norm_sub_rev]; exact huU
    have hlt37 : ‖z - u‖ < 37 / 10 := lt_trans hlt_R2 hR2small
    have hthis := hRgood' u (hSzero u hu) hlt37
    by_contra hcon
    push Not at hcon
    have hup : ‖z - u‖ < R + δ := by
      rw [hR2_def] at hlt_R2; linarith
    have habs : |R - ‖z - u‖| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
    linarith [hthis]
  have hAnSmall : AnalyticOnNhd ℂ riemannZeta (Metric.ball z R2) := fun w hw =>
    analyticOn_riemannZeta w (hz1R2 w (Metric.ball_subset_closedBall hw))
  have hAnBig : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall z (37 / 10 : ℝ)) := fun w hw =>
    analyticOn_riemannZeta w (hz1 w hw)
  have hSbig : ∀ u ∈ S, u ∈ Metric.closedBall z (37 / 10 : ℝ) := fun u hu =>
    Metric.ball_subset_closedBall (Metric.ball_subset_ball hR2small.le (hSU u hu))
  have hfin :=
    (MeromorphicOn.divisor riemannZeta (Metric.closedBall z (37 / 10 : ℝ))).finiteSupport
      (isCompact_closedBall _ _)
  have hmeqBig : ∀ u ∈ S, (m u : ℤ) =
    MeromorphicOn.divisor riemannZeta (Metric.closedBall z (37 / 10 : ℝ)) u :=
    fun u hu =>
    (hmeqSmall u hu).trans
      (divisor_riemannZeta_eq_of_analyticOnNhd hAnSmall
        hAnBig (hSU u hu) (hSbig u hu))
  have hSsub : S ⊆ hfin.toFinset := by
    intro u hu
    rw [Set.Finite.mem_toFinset, Function.mem_support]
    rw [← hmeqBig u hu]
    exact_mod_cast (hmpos u hu).ne'
  have hsum_le :
    (∑ u ∈ S, (m u : ℝ)) ≤
      jensenLogConst * Real.log (T + 2) := by
    have hcongr :
      ∑ u ∈ S, (m u : ℝ) =
        ∑ u ∈ S, (MeromorphicOn.divisor riemannZeta (Metric.closedBall z (37 / 10 : ℝ)) u : ℝ) :=
      Finset.sum_congr rfl (fun u hu => by exact_mod_cast hmeqBig u hu)
    rw [hcongr]
    have hcard1 :
      ∑ u ∈ S, (MeromorphicOn.divisor riemannZeta (Metric.closedBall z (37 / 10 : ℝ)) u : ℝ) ≤
        ∑ u ∈ hfin.toFinset,
        (MeromorphicOn.divisor riemannZeta (Metric.closedBall z (37 / 10 : ℝ)) u : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hSsub
      intro u _ _
      exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAnBig u
    have hcard2 :
      ∑ u ∈ hfin.toFinset,
      (MeromorphicOn.divisor riemannZeta (Metric.closedBall z (37 / 10 : ℝ)) u : ℝ) =
        ((∑ᶠ u, MeromorphicOn.divisor riemannZeta (Metric.closedBall z (37 / 10 : ℝ)) u : ℤ) : ℝ
        ) := by
      rw [finsum_eq_finsetSum_of_support_subset _ (s := hfin.toFinset)
          (by rw [Set.Finite.coe_toFinset])]
      push_cast
      rfl
    rw [hcard2] at hcard1
    exact
      hcard1.trans
        (finsum_divisor_riemannZeta_le_explicit hT)
  exact
    ⟨R, δ, R2, S, m, g, hδ_pos, hδ_ge, hR, hR1R2, hR2small, hgAn, hgne, hmpos, hSzero, hu_dist,
      hsum_le, heqOn⟩

/-! ### The boundary bound at the Jensen scale, with a strict bound at the center

Mirrors `PseudoPrime.AnalyticNumberTheory.RiemannZeta.exists_bound_re_logDeriv_g_good_radius`,
but centered at `PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensenCenter T`. The `ζ`-growth
bound throughout the disk comes from
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensen_f_bound_ball` (a single constant `jensenM T`,
not depending on the radius, unlike
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.norm_riemannZeta_le_on_good_radius_ball`'s
`z`-dependent `Mζ`).  The genuinely new ingredient is the *strict* inequality at the center
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensenCenter T` itself, needed to invoke
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.norm_hasDerivAt_le_of_re_le`:
every zero `u` of `ζ` satisfies `u.re ≤ 1`
(`PseudoPrime.AnalyticNumberTheory.RiemannZeta.riemannZeta_zero_re_le_one`, unconditional) while
`(PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensenCenter T).re = 3`, giving
`‖PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensenCenter T - u‖ ≥ 2 > 1` for every zero — hence
`‖P(PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensenCenter T)‖ ≥ 1` regardless of
which zeros are extracted, giving
`Re h(PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensenCenter T) ≤ log(jensenM T) < M` directly
(`M` being strictly larger due to the extra positive term from the boundary's zero-count penalty).
-/

theorem exists_bound_re_logDeriv_g_jensen_good_radius {T : ℝ} (hT : 8 ≤ T) :
    ∃ (R1 R2 : ℝ) (S : Finset ℂ) (m : ℂ → ℕ) (g h : ℂ → ℂ) (M : ℝ),
      (71 : ℝ) / 20 ≤ R1 ∧
        R1 < R2 ∧
        R2 < 37 / 10 ∧
        AnalyticOnNhd ℂ g
          (Metric.ball (jensenCenter T) R2) ∧
        (∀ w ∈ Metric.ball (jensenCenter T) R2,
          g w ≠ 0) ∧
        (∀ u ∈ S, 0 < m u) ∧
        (∀ w ∈ Metric.ball (jensenCenter T) R2,
          HasDerivAt h (logDeriv g w) w) ∧
        (∀ u ∈ S, riemannZeta u = 0) ∧
        (∑ u ∈ S, (m u : ℝ)) ≤
          jensenLogConst * Real.log (T + 2) ∧
        Set.EqOn riemannZeta (fun w => (∏ u ∈ S, (w - u) ^ m u) * g w)
          (Metric.ball (jensenCenter T) R2) ∧
        (h (jensenCenter T)).re < M ∧
        Real.log (1 / 2) -
            jensenLogConst * Real.log (T + 2) *
              Real.log 4 ≤
          (h (jensenCenter T)).re ∧
        M ≤
          Real.log (jensenM T) +
            jensenLogConst * Real.log (T + 2) *
              (Real.log (2 / 3) +
                  Real.log (40 * jensenLogConst + 50) +
                  Real.log (T + 2) -
                1) ∧
        (∀ w ∈ Metric.closedBall (jensenCenter T) R1,
          (h w).re ≤ M) := by
  obtain
    ⟨R, δ, R2, S, m, g, hδ_pos, hδ_ge, hR, hR1R2, hR2small, hgAn, hgne, hmpos, hSzero, hu_dist,
      hsum_le, heqOn⟩ :=
    exists_riemannZeta_zeroFree_factorization_jensen_good_radius
      hT
  set z : ℂ := jensenCenter T with hz_def
  have hT4 : (4 : ℝ) ≤ T := by linarith
  set R1 : ℝ := R + δ / 2 with hR1_def
  have hR1big : (71 : ℝ) / 20 ≤ R1 := by
    rw [hR1_def]; linarith [hR.1, hδ_pos]
  have hR1pos : (0 : ℝ) < R1 := by linarith
  have hR1lt37 : R1 < 37 / 10 := lt_trans hR1R2 hR2small
  have hR2pos : (0 : ℝ) < R2 := lt_trans hR1pos hR1R2
  obtain ⟨h, hh', hh_re⟩ :=
    exists_hasDerivAt_logDeriv_re_eq_log_norm (f := g)
      (c := z) (r := R2) hR2pos hgAn hgne
  have hR1subR2 : Metric.closedBall z R1 ⊆ Metric.ball z R2 := by
    intro w hw
    rw [Metric.mem_closedBall] at hw
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt hw hR1R2
  have hdiff : DifferentiableOn ℂ h (Metric.ball z R1) := fun w hw =>
    (hh' w (hR1subR2 (Metric.ball_subset_closedBall hw))).differentiableAt.differentiableWithinAt
  have hcont : ContinuousOn h (Metric.closedBall z R1) := fun w hw =>
    (hh' w (hR1subR2 hw)).continuousAt.continuousWithinAt
  have hR1ne : R1 ≠ 0 := hR1pos.ne'
  have hclosure : closure (Metric.ball z R1) = Metric.closedBall z R1 := closure_ball z hR1ne
  have hdcc : DiffContOnCl ℂ h (Metric.ball z R1) :=
    ⟨hdiff, by
      rw [hclosure]; exact hcont⟩
  have hζbound : ∀ w ∈ Metric.closedBall z R1, ‖riemannZeta w‖ ≤ jensenM T := by
    intro w hw
    exact
      jensen_f_bound_ball hT4 w
        (Metric.closedBall_subset_closedBall (by linarith) hw)
  set Nmax : ℝ :=
    jensenLogConst * Real.log (T + 2) with hNmax_def
  set M : ℝ := Real.log (jensenM T) - Nmax * Real.log (3 * δ / 2) with hM_def
  have hδlt : δ < 37 / 10 := by
    rw [hR1_def] at hR1R2; linarith [hR.1, hR2small]
  have h3δ2 : 3 * δ / 2 < 1 := by
    have hδlt2 : δ < 2 / 3 := by
      rw [hR1_def] at hR1R2
      linarith only [hR.1, hR1R2, hR2small]
    linarith
  have h3δ2pos : (0 : ℝ) < 3 * δ / 2 := by linarith [hδ_pos]
  have hlogneg : Real.log (3 * δ / 2) < 0 := Real.log_neg h3δ2pos h3δ2
  have hLCpos := jensenLogConst_pos
  have hlogTpos : (0 : ℝ) < Real.log (T + 2) := Real.log_pos (by linarith)
  have hNmaxnn : (0 : ℝ) ≤ Nmax := by
    rw [hNmax_def]; positivity
  have hNmaxpos : (0 : ℝ) < Nmax := by
    rw [hNmax_def]; positivity
  have hzmem : z ∈ Metric.ball z R2 := Metric.mem_ball_self hR2pos
  have hPfactor_ge : ∀ u ∈ S, (2 : ℝ) ≤ ‖z - u‖ := by
    intro u hu
    have hure : u.re ≤ 1 :=
      riemannZeta_zero_re_le_one (hSzero u hu)
    have hzre3 : z.re = 3 := by
      rw [hz_def]; exact jensenCenter_re T
    have h1 : |z.re - u.re| ≤ ‖z - u‖ := by
      have h := Complex.abs_re_le_norm (z - u)
      simpa only [ge_iff_le, Complex.sub_re] using h
    have h2 : z.re - u.re ≤ |z.re - u.re| := le_abs_self _
    rw [hzre3] at h1 h2
    linarith [h1, h2, hure]
  have hPfactor_pos : ∀ u ∈ S, (0 : ℝ) < ‖z - u‖ := fun u hu =>
    lt_of_lt_of_le (by norm_num only) (hPfactor_ge u hu)
  have hPne : (∏ u ∈ S, (z - u) ^ m u) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro u hu
    exact pow_ne_zero _ (norm_pos_iff.mp (hPfactor_pos u hu))
  have hζval : riemannZeta z = (∏ u ∈ S, (z - u) ^ m u) * g z := heqOn hzmem
  have hgval : g z = riemannZeta z / (∏ u ∈ S, (z - u) ^ m u) := by
    rw [hζval, mul_div_cancel_left₀ (g z) hPne]
  have hgz_ne : g z ≠ 0 := hgne z hzmem
  have hnormg : ‖g z‖ = ‖riemannZeta z‖ / ‖∏ u ∈ S, (z - u) ^ m u‖ := by rw [hgval, norm_div]
  have hnormP : ‖∏ u ∈ S, (z - u) ^ m u‖ = ∏ u ∈ S, ‖z - u‖ ^ m u := by
    rw [norm_prod]
    exact Finset.prod_congr rfl (fun u _ => norm_pow (z - u) (m u))
  have hPge1 : (1 : ℝ) ≤ ∏ u ∈ S, ‖z - u‖ ^ m u := by
    have h1 : ∏ _u ∈ S, (1 : ℝ) ≤ ∏ u ∈ S, ‖z - u‖ ^ m u := by
      apply Finset.prod_le_prod₀
      · intro u _; norm_num only
      · intro u hu; exact one_le_pow₀ (by linarith [hPfactor_ge u hu])
    simpa only [ge_iff_le, Finset.prod_const_one] using h1
  have hζz_pos : (0 : ℝ) < ‖riemannZeta z‖ :=
    norm_pos_iff.mpr (jensen_center_ne_zero T)
  have hPz_pos : (0 : ℝ) < ‖∏ u ∈ S, (z - u) ^ m u‖ := norm_pos_iff.mpr hPne
  have hloggz : Real.log ‖g z‖ = Real.log ‖riemannZeta z‖ - Real.log ‖∏ u ∈ S, (z - u) ^ m u‖ := by
    rw [hnormg, Real.log_div hζz_pos.ne' hPz_pos.ne']
  have hgz_val : (h z).re = Real.log ‖riemannZeta z‖ - Real.log (∏ u ∈ S, ‖z - u‖ ^ m u) := by
    rw [hh_re z hzmem, hloggz, hnormP]
  have hlogζz_le : Real.log ‖riemannZeta z‖ ≤ Real.log (jensenM T) :=
    Real.log_le_log hζz_pos
      (jensen_f_bound_ball hT4 z
        (Metric.mem_closedBall_self (by norm_num only)))
  have hlogPnn : (0 : ℝ) ≤ Real.log (∏ u ∈ S, ‖z - u‖ ^ m u) := Real.log_nonneg hPge1
  have hextra : (0 : ℝ) < Nmax * (-Real.log (3 * δ / 2)) := by
    apply mul_pos hNmaxpos
    linarith [hlogneg]
  have hMle :
    M ≤
      Real.log (jensenM T) +
        jensenLogConst * Real.log (T + 2) *
          (Real.log (2 / 3) +
              Real.log (40 * jensenLogConst + 50) +
              Real.log (T + 2) -
            1) := by
    have hδ_inv_le :
      1 / δ ≤
        40 * jensenLogConst * Real.log (T + 2) +
          50 := by
      have h1 :
        1 / δ ≤
          1 /
            (1 /
              (40 * jensenLogConst * Real.log (T + 2) +
                50)) :=
        one_div_le_one_div_of_le (by positivity) hδ_ge
      rwa [one_div_one_div] at h1
    have hlog_T2_ge1 : (1 : ℝ) ≤ Real.log (T + 2) := by
      rw [Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < T + 2)]
      have := Real.exp_one_lt_three
      linarith
    have hK50pos :
      (0 : ℝ) <
        40 * jensenLogConst * Real.log (T + 2) +
          50 := by
      positivity
    have hK50'pos :
      (0 : ℝ) < 40 * jensenLogConst + 50 := by
      positivity
    have hsum_le2 :
      40 * jensenLogConst * Real.log (T + 2) + 50 ≤
        (40 * jensenLogConst + 50) *
          Real.log (T + 2) := by
      have hexpand :
        (40 * jensenLogConst + 50) * Real.log (T + 2) =
          40 * jensenLogConst * Real.log (T + 2) +
            50 * Real.log (T + 2) := by
        ring
      rw [hexpand]; linarith only [hlog_T2_ge1]
    have hstep1 : -Real.log (3 * δ / 2) = Real.log (2 / 3) + Real.log (1 / δ) := by
      have heq : (3 * δ / 2 : ℝ) = (2 / 3 * (1 / δ))⁻¹ := by field_simp
      rw [heq, Real.log_inv, neg_neg, Real.log_mul (by norm_num only) (by positivity)]
    have hstep2 :
      Real.log (1 / δ) ≤
        Real.log
          (40 * jensenLogConst * Real.log (T + 2) +
            50) :=
      Real.log_le_log (by positivity) hδ_inv_le
    have hstep3 :
      Real.log
          (40 * jensenLogConst * Real.log (T + 2) +
            50) ≤
        Real.log
          ((40 * jensenLogConst + 50) *
            Real.log (T + 2)) :=
      Real.log_le_log hK50pos hsum_le2
    have hstep4 :
      Real.log
          ((40 * jensenLogConst + 50) *
            Real.log (T + 2)) =
        Real.log (40 * jensenLogConst + 50) +
          Real.log (Real.log (T + 2)) :=
      Real.log_mul hK50'pos.ne' hlogTpos.ne'
    have hstep5 : Real.log (Real.log (T + 2)) ≤ Real.log (T + 2) - 1 :=
      Real.log_le_sub_one_of_pos hlogTpos
    have hfinal :
      -Real.log (3 * δ / 2) ≤
        Real.log (2 / 3) +
            Real.log (40 * jensenLogConst + 50) +
            Real.log (T + 2) -
          1 := by
      rw [hstep1]; linarith [hstep2, hstep3, hstep4, hstep5]
    have hmul :
      Nmax * (-Real.log (3 * δ / 2)) ≤
        Nmax *
          (Real.log (2 / 3) +
              Real.log (40 * jensenLogConst + 50) +
              Real.log (T + 2) -
            1) :=
      mul_le_mul_of_nonneg_left hfinal hNmaxnn
    rw [hM_def, hNmax_def]
    linarith only [hmul, hNmax_def]
  refine
    ⟨R1, R2, S, m, g, h, M, hR1big, hR1R2, hR2small, hgAn, hgne, hmpos, hh', hSzero, hsum_le, heqOn,
      ?_, ?_, ?_, ?_⟩
  · -- strict inequality at the center
    rw [hgz_val, hM_def]
    linarith [hlogζz_le, hlogPnn, hextra]
  · -- lower bound `log(1/2) - Nmax·log4 ≤ (h z).re`
    rw [hgz_val]
    have hζz_ge : Real.log (1 / 2 : ℝ) ≤ Real.log ‖riemannZeta z‖ :=
      Real.log_le_log (by norm_num only)
        (jensen_center_norm_ge T)
    have hzu_lt4 : ∀ u ∈ S, ‖z - u‖ < 4 := fun u hu => by linarith [hu_dist u hu, hR.2]
    have hlog4pos : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num only)
    have hlogP_le : Real.log (∏ u ∈ S, ‖z - u‖ ^ m u) ≤ Nmax * Real.log 4 := by
      rw [Real.log_prod (fun u hu => (pow_pos (hPfactor_pos u hu) (m u)).ne')]
      calc
        ∑ u ∈ S, Real.log (‖z - u‖ ^ m u) = ∑ u ∈ S, (m u : ℝ) * Real.log ‖z - u‖ := by
          apply Finset.sum_congr rfl; intro u _; rw [Real.log_pow]
        _ ≤ ∑ u ∈ S, (m u : ℝ) * Real.log 4 := by
          apply Finset.sum_le_sum
          intro u hu
          exact
            mul_le_mul_of_nonneg_left (Real.log_le_log (hPfactor_pos u hu) (hzu_lt4 u hu).le)
              (Nat.cast_nonneg _)
        _ = (∑ u ∈ S, (m u : ℝ)) * Real.log 4 := by rw [Finset.sum_mul]
        _ ≤ Nmax * Real.log 4 := mul_le_mul_of_nonneg_right hsum_le hlog4pos
    linarith [hζz_ge, hlogP_le]
  · -- explicit upper bound on `M`
    exact hMle
  · -- boundary bound extended to the whole disk
    have hMbound : ∀ w ∈ frontier (Metric.ball z R1), (h w).re ≤ M := by
      intro w hwf
      rw [frontier_ball z hR1ne, Metric.mem_sphere] at hwf
      have hwR1 : w ∈ Metric.closedBall z R1 := by
        rw [Metric.mem_closedBall]; exact hwf.le
      have hwR2 : w ∈ Metric.ball z R2 := hR1subR2 hwR1
      have hPlb : ∀ u ∈ S, 3 * δ / 2 ≤ ‖w - u‖ := by
        intro u hu
        have h1 : ‖z - u‖ ≤ R - δ := hu_dist u hu
        have h3 : ‖w - z‖ = R1 := by
          rw [← dist_eq_norm]; exact hwf
        have htri : ‖w - z‖ ≤ ‖w - u‖ + ‖u - z‖ := by
          have h := norm_add_le (w - u) (u - z)
          simpa only [ge_iff_le, sub_add_sub_cancel] using h
        rw [norm_sub_rev u z, h3] at htri
        linarith [htri, h1, hR1_def]
      have hPfactor_pos : ∀ u ∈ S, (0 : ℝ) < ‖w - u‖ := fun u hu =>
        lt_of_lt_of_le h3δ2pos (hPlb u hu)
      have hPne : (∏ u ∈ S, (w - u) ^ m u) ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro u hu
        exact pow_ne_zero _ (norm_pos_iff.mp (hPfactor_pos u hu))
      have hζval : riemannZeta w = (∏ u ∈ S, (w - u) ^ m u) * g w := heqOn hwR2
      have hgval : g w = riemannZeta w / (∏ u ∈ S, (w - u) ^ m u) := by
        rw [hζval, mul_div_cancel_left₀ (g w) hPne]
      have hgw_ne : g w ≠ 0 := hgne w hwR2
      have hnormg : ‖g w‖ = ‖riemannZeta w‖ / ‖∏ u ∈ S, (w - u) ^ m u‖ := by rw [hgval, norm_div]
      have hnormP : ‖∏ u ∈ S, (w - u) ^ m u‖ = ∏ u ∈ S, ‖w - u‖ ^ m u := by
        rw [norm_prod]
        exact Finset.prod_congr rfl (fun u _ => norm_pow (w - u) (m u))
      have hlogP : Real.log (∏ u ∈ S, ‖w - u‖ ^ m u) = ∑ u ∈ S, (m u : ℝ) * Real.log ‖w - u‖ := by
        rw [Real.log_prod (fun u hu => (pow_pos (hPfactor_pos u hu) (m u)).ne')]
        exact Finset.sum_congr rfl (fun u _ => Real.log_pow ‖w - u‖ (m u))
      have hlogP_lb :
        (∑ u ∈ S, (m u : ℝ)) * Real.log (3 * δ / 2) ≤ ∑ u ∈ S, (m u : ℝ) * Real.log ‖w - u‖ := by
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro u hu
        have hlogle : Real.log (3 * δ / 2) ≤ Real.log ‖w - u‖ := Real.log_le_log h3δ2pos (hPlb u hu)
        exact mul_le_mul_of_nonneg_left hlogle (Nat.cast_nonneg (m u))
      have hNmax_le : Nmax * Real.log (3 * δ / 2) ≤ (∑ u ∈ S, (m u : ℝ)) * Real.log (3 * δ / 2) :=
        mul_le_mul_of_nonpos_right hsum_le hlogneg.le
      have hlogPw_ge : Nmax * Real.log (3 * δ / 2) ≤ Real.log ‖∏ u ∈ S, (w - u) ^ m u‖ := by
        rw [hnormP, hlogP]
        linarith [hNmax_le, hlogP_lb]
      have hζw_pos : (0 : ℝ) < ‖riemannZeta w‖ := by
        rw [hζval]
        exact norm_pos_iff.mpr (mul_ne_zero hPne hgw_ne)
      have hPw_pos : (0 : ℝ) < ‖∏ u ∈ S, (w - u) ^ m u‖ := norm_pos_iff.mpr hPne
      have hζw : ‖riemannZeta w‖ ≤ jensenM T := hζbound w hwR1
      have hloggw :
        Real.log ‖g w‖ = Real.log ‖riemannZeta w‖ - Real.log ‖∏ u ∈ S, (w - u) ^ m u‖ := by
        rw [hnormg, Real.log_div hζw_pos.ne' hPw_pos.ne']
      rw [hh_re w hwR2, hloggw]
      have hlogζ_le : Real.log ‖riemannZeta w‖ ≤ Real.log (jensenM T) := Real.log_le_log hζw_pos hζw
      rw [hM_def]
      linarith [hlogζ_le, hlogPw_ge]
    intro w hw
    refine
      re_le_of_forall_mem_frontier_re_le
        (Metric.isBounded_ball) hdcc hMbound ?_
    rw [hclosure]; exact hw

/-!
### Reduction of the semi-explicit bound

A separate numerical inequality combines the zero-sum and derivative terms
into a fixed constant times `log(T+2)²`.
-/

/-- A fixed constant for the good-height bound on `‖ζ'/ζ‖`, depending on
`jensenLogConst` and `sawtoothRemainderBound (-9/10)`, but not on height or real part. -/
noncomputable def qMinusOneZetaLogDerivConst : ℝ :=
  (4 * jensenLogConst ^ 2 +
      jensenLogConst) +
    4 * 2880 *
      (|Real.log
              (9 / 2 +
                4 * sawtoothRemainderBound (-9 / 10)) +
            Real.log 2| +
        |2 +
            jensenLogConst *
              (Real.log (2 / 3) + Real.log 4 +
                  Real.log (40 * jensenLogConst + 50) -
                1)| +
        jensenLogConst)

theorem qMinusOneZetaLogDerivConst_nonneg :
    0 ≤ qMinusOneZetaLogDerivConst := by
  unfold qMinusOneZetaLogDerivConst
  have := jensenLogConst_pos
  positivity

theorem le_qMinusOneZetaLogDerivConst_mul_log_sq_of_semi_explicit {H T R1 M gjc d X : ℝ}
    (hH : 8 ≤ H) (hT1 : H ≤ T) (_hT2 : T ≤ H + 1) (hR1big : 71 / 20 ≤ R1) (hR1lt37 : R1 < 37 / 10)
    (hd_le : d ≤ 7 / 2) (hMc : gjc < M)
    (hMle :
      M ≤
        Real.log (jensenM T) +
          jensenLogConst * Real.log (T + 2) *
            (Real.log (2 / 3) +
                Real.log (40 * jensenLogConst + 50) +
                Real.log (T + 2) -
              1))
    (hgjc_ge :
      Real.log (1 / 2) -
          jensenLogConst * Real.log (T + 2) *
            Real.log 4 ≤
        gjc)
    (hX :
      X ≤
        jensenLogConst * Real.log (T + 2) *
            max (4 * jensenLogConst * Real.log (H + 2))
              1 +
          4 * (M - gjc) * (R1 + d) / (R1 - d) ^ 2) :
    X ≤
      qMinusOneZetaLogDerivConst *
        Real.log (T + 2) ^ 2 := by
  have hT8 : (8 : ℝ) ≤ T := by linarith
  have hLCpos := jensenLogConst_pos
  have hlogTpos : (0 : ℝ) < Real.log (T + 2) := Real.log_pos (by linarith)
  have hL_ge1 : (1 : ℝ) ≤ Real.log (T + 2) := by
    rw [Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < T + 2)]
    have := Real.exp_one_lt_three
    linarith
  have hL_le_L2 : Real.log (T + 2) ≤ Real.log (T + 2) ^ 2 := le_self_pow₀ hL_ge1 (by norm_num only)
  have hL2_ge1 : (1 : ℝ) ≤ Real.log (T + 2) ^ 2 := le_trans hL_ge1 hL_le_L2
  -- Step A: bound the sum term by `(4·PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensenLogConst²`
  --   `+ PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensenLogConst)·(log(T+2))²`.
  have hlogH_le_logT : Real.log (H + 2) ≤ Real.log (T + 2) := by
    apply Real.log_le_log (by linarith) (by linarith)
  have htermA :
    jensenLogConst * Real.log (T + 2) *
        max (4 * jensenLogConst * Real.log (H + 2)) 1 ≤
      (4 * jensenLogConst ^ 2 +
          jensenLogConst) *
        Real.log (T + 2) ^ 2 := by
    have hmax_le :
      max (4 * jensenLogConst * Real.log (H + 2)) 1 ≤
        4 * jensenLogConst * Real.log (T + 2) + 1 := by
      apply max_le
      · have :=
          mul_le_mul_of_nonneg_left hlogH_le_logT
            (by positivity :
              (0 : ℝ) ≤ 4 * jensenLogConst)
        linarith [this]
      · have hnn :
          (0 : ℝ) ≤
            4 * jensenLogConst * Real.log (T + 2) :=
          mul_nonneg (by positivity) hlogTpos.le
        linarith only [hnn]
    have h5 : Real.log (T + 2) ≤ Real.log (T + 2) ^ 2 := le_self_pow₀ hL_ge1 (by norm_num only)
    calc
      jensenLogConst * Real.log (T + 2) *
            max (4 * jensenLogConst * Real.log (H + 2))
              1 ≤
          jensenLogConst * Real.log (T + 2) *
            (4 * jensenLogConst * Real.log (T + 2) +
              1) :=
        mul_le_mul_of_nonneg_left hmax_le (by positivity)
      _ =
          4 * jensenLogConst ^ 2 *
              Real.log (T + 2) ^ 2 +
            jensenLogConst * Real.log (T + 2) :=
        by ring
      _ ≤
          4 * jensenLogConst ^ 2 *
              Real.log (T + 2) ^ 2 +
            jensenLogConst * Real.log (T + 2) ^ 2 :=
        by
        have hkey := mul_le_mul_of_nonneg_left h5 hLCpos.le
        linarith [hkey]
      _ =
          (4 * jensenLogConst ^ 2 +
              jensenLogConst) *
            Real.log (T + 2) ^ 2 :=
        by ring
  -- Step B: bound `(R1 + d) / (R1 - d)²` by a fixed constant `2880`.
  have hR1d_pos : (0 : ℝ) < R1 - d := by linarith [hR1big, hd_le]
  have hRd_le : (R1 + d) / (R1 - d) ^ 2 ≤ 2880 := by
    have hnum_le : R1 + d ≤ 72 / 10 := by linarith [hR1lt37, hd_le]
    have hden_ge : (1 : ℝ) / 20 ≤ R1 - d := by linarith [hR1big, hd_le]
    rw [div_le_iff₀ (by positivity)]
    have hsq : (1 / 20 : ℝ) ^ 2 ≤ (R1 - d) ^ 2 := pow_le_pow_left₀ (by norm_num only) hden_ge 2
    linarith only [hnum_le, hsq]
  -- Step C: bound `M - gjc` by an explicit `A₀ + A₁·log(T+2)`
  --   `+ PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensenLogConst·(log(T+2))²`.
  set B : ℝ := sawtoothRemainderBound (-9 / 10) with
    hB_def
  have hBnn : (0 : ℝ) ≤ B :=
    sawtoothRemainderBound_nonneg _
  have hjensenMpos : (0 : ℝ) < jensenM T := by
    unfold jensenM
    rw [← hB_def]
    have hT390 : (0 : ℝ) < T - 39 / 10 := by linarith
    have hdiv_pos : (0 : ℝ) < (T + 69 / 10) / (T - 39 / 10) := div_pos (by linarith) hT390
    have hthird_nn : (0 : ℝ) ≤ (T + 69 / 10) * (T + 69 / 10 + 1) * B :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) hBnn
    linarith [hdiv_pos, hthird_nn]
  have hlogjensenM_le : Real.log (jensenM T) ≤ Real.log (9 / 2 + 4 * B) + 2 * Real.log (T + 2) := by
    have h1 : Real.log (jensenM T) ≤ Real.log ((9 / 2 + 4 * B) * T ^ 2) :=
      Real.log_le_log hjensenMpos (jensenM_le hT8)
    have h2 : Real.log ((9 / 2 + 4 * B) * T ^ 2) = Real.log (9 / 2 + 4 * B) + Real.log (T ^ 2) :=
      Real.log_mul (by positivity) (by positivity)
    have h3 : Real.log (T ^ 2) = 2 * Real.log T := Real.log_pow T 2
    have h4 : Real.log T ≤ Real.log (T + 2) := Real.log_le_log (by linarith) (by linarith)
    linarith [h1, h2, h3, h4]
  have hlog2eq : -Real.log (1 / 2 : ℝ) = Real.log 2 := by
    rw [show (1 / 2 : ℝ) = 2⁻¹ from by norm_num only, Real.log_inv, neg_neg]
  set A0 : ℝ := Real.log (9 / 2 + 4 * B) + Real.log 2 with hA0_def
  set A1 : ℝ :=
    2 +
      jensenLogConst *
        (Real.log (2 / 3) + Real.log 4 +
            Real.log (40 * jensenLogConst + 50) -
          1) with
    hA1_def
  have hMgjc_le :
    M - gjc ≤
      A0 + A1 * Real.log (T + 2) +
        jensenLogConst * Real.log (T + 2) ^ 2 := by
    have hkey :
      A0 + A1 * Real.log (T + 2) +
            jensenLogConst * Real.log (T + 2) ^ 2 -
          ((Real.log (9 / 2 + 4 * B) + 2 * Real.log (T + 2)) + Real.log 2 +
            jensenLogConst * Real.log (T + 2) *
              (Real.log (2 / 3) +
                  Real.log (40 * jensenLogConst + 50) +
                  Real.log (T + 2) -
                1) +
            jensenLogConst * Real.log (T + 2) *
              Real.log 4) =
        0 := by
      rw [hA0_def, hA1_def]; ring
    linarith [hMle, hgjc_ge, hlogjensenM_le, hkey, hlog2eq]
  have hMgjc_nonneg : (0 : ℝ) ≤ M - gjc := by linarith [hMc]
  have htermB_inner :
    M - gjc ≤
      (|A0| + |A1| + jensenLogConst) *
        Real.log (T + 2) ^ 2 := by
    have hA0le : A0 ≤ |A0| * Real.log (T + 2) ^ 2 := by
      calc
        A0 ≤ |A0| := le_abs_self _
        _ ≤ |A0| * Real.log (T + 2) ^ 2 := by
          have := mul_le_mul_of_nonneg_left hL2_ge1 (abs_nonneg A0)
          linarith [this]
    have hA1le : A1 * Real.log (T + 2) ≤ |A1| * Real.log (T + 2) ^ 2 := by
      calc
        A1 * Real.log (T + 2) ≤ |A1| * Real.log (T + 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hlogTpos.le
        _ ≤ |A1| * Real.log (T + 2) ^ 2 := by
          have := mul_le_mul_of_nonneg_left hL_le_L2 (abs_nonneg A1)
          linarith [this]
    linarith [hMgjc_le, hA0le, hA1le]
  have htermB :
    4 * (M - gjc) * (R1 + d) / (R1 - d) ^ 2 ≤
      4 * 2880 * (|A0| + |A1| + jensenLogConst) *
        Real.log (T + 2) ^ 2 := by
    have hstep1 :
      4 * (M - gjc) * (R1 + d) / (R1 - d) ^ 2 = 4 * (M - gjc) * ((R1 + d) / (R1 - d) ^ 2) := by ring
    rw [hstep1]
    calc
      4 * (M - gjc) * ((R1 + d) / (R1 - d) ^ 2) ≤ 4 * (M - gjc) * 2880 :=
        mul_le_mul_of_nonneg_left hRd_le (by positivity)
      _ ≤
          4 *
            ((|A0| + |A1| + jensenLogConst) *
              Real.log (T + 2) ^ 2) *
            2880 :=
        by
        apply mul_le_mul_of_nonneg_right _ (by norm_num only)
        exact mul_le_mul_of_nonneg_left htermB_inner (by norm_num only)
      _ =
          4 * 2880 * (|A0| + |A1| + jensenLogConst) *
            Real.log (T + 2) ^ 2 :=
        by ring
  have hCeq :
    qMinusOneZetaLogDerivConst =
      (4 * jensenLogConst ^ 2 +
          jensenLogConst) +
        4 * 2880 * (|A0| + |A1| + jensenLogConst) := by
    unfold qMinusOneZetaLogDerivConst
    rw [hA0_def, hA1_def, hB_def]
  rw [hCeq]
  calc
    X ≤
        jensenLogConst * Real.log (T + 2) *
            max (4 * jensenLogConst * Real.log (H + 2))
              1 +
          4 * (M - gjc) * (R1 + d) / (R1 - d) ^ 2 :=
      hX
    _ ≤
        (4 * jensenLogConst ^ 2 +
              jensenLogConst) *
            Real.log (T + 2) ^ 2 +
          4 * 2880 * (|A0| + |A1| + jensenLogConst) *
            Real.log (T + 2) ^ 2 :=
      add_le_add htermA htermB
    _ =
        ((4 * jensenLogConst ^ 2 +
              jensenLogConst) +
            4 * 2880 *
              (|A0| + |A1| + jensenLogConst)) *
          Real.log (T + 2) ^ 2 :=
      by ring

/-- At a good height `T`, `ζ` never vanishes on the whole horizontal line `Im s = T`, for any real
part `σ`: a zero at `σ + iT` would have ordinate exactly `T`, hence `|T - ρ.im| = 0`, contradicting
the good-height margin (since `|ρ.im - H| ≤ |T - H| ≤ 1 ≤ 2`, so `hgood` applies). This removes the
`ζ(σ + iT) ≠ 0` hypothesis from
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.forall_norm_logDeriv_riemannZeta_le`
when combined below. -/
theorem riemannZeta_ne_zero_of_good_height {H : ℝ} (hH : 8 ≤ H) {T : ℝ} (hT : T ∈ Set.Icc H (H + 1))
    (hgood :
      ∀ ρ : ℂ,
        riemannZeta ρ = 0 →
          |ρ.im - H| ≤ 2 →
          1 / (4 * jensenLogConst * Real.log (H + 2)) ≤
            |T - ρ.im|)
    (σ : ℝ) : riemannZeta (σ + T * Complex.I) ≠ 0 := by
  intro hzero
  have him : (σ + T * Complex.I).im = T := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  have h1 : |(σ + T * Complex.I).im - H| ≤ 2 := by
    rw [him, abs_le]; constructor <;> linarith [hT.1, hT.2]
  have h2 := hgood (σ + T * Complex.I) hzero h1
  rw [him, sub_self, abs_zero] at h2
  have hLCpos := jensenLogConst_pos
  have hlogpos : (0 : ℝ) < Real.log (H + 2) := Real.log_pos (by linarith)
  have :
    (0 : ℝ) <
      1 / (4 * jensenLogConst * Real.log (H + 2)) := by
    positivity
  linarith

/-!
### A squared-logarithmic bound at a good height

For `H ≥ 8`, `T ∈ [H,H+1]` satisfying the stated zero-avoidance margin,
and `-1/2 ≤ σ ≤ 2` with `ζ(σ+iT) ≠ 0`, combine the Jensen-scale derivative
estimate and the finite zero sum. Nearby zeros use the good-height margin;
other zeros have ordinate distance greater than one.
-/

theorem forall_norm_logDeriv_riemannZeta_le {H : ℝ} (hH : 8 ≤ H) {T : ℝ}
    (hT : T ∈ Set.Icc H (H + 1))
    (hgood :
      ∀ ρ : ℂ,
        riemannZeta ρ = 0 →
          |ρ.im - H| ≤ 2 →
          1 / (4 * jensenLogConst * Real.log (H + 2)) ≤
            |T - ρ.im|) :
    ∀ σ : ℝ,
      -(1 : ℝ) / 2 ≤ σ →
        σ ≤ 2 →
        riemannZeta (σ + T * Complex.I) ≠ 0 →
        ‖logDeriv riemannZeta (σ + T * Complex.I)‖ ≤
          qMinusOneZetaLogDerivConst *
            Real.log (T + 2) ^ 2 := by
  have hT8 : (8 : ℝ) ≤ T := le_trans hH hT.1
  obtain
    ⟨R1, R2, S, m, g, h, M, hR1big, hR1R2, hR2small, hgAn, hgne, hmpos, hh', hSzero, hsum_le, heqOn,
      hMc, hgjc_ge, hMle, hMbound⟩ :=
    exists_bound_re_logDeriv_g_jensen_good_radius hT8
  intro σ hσ1 hσ2 hzgood
  set z : ℂ := σ + T * Complex.I with hz_def
  set c : ℂ := jensenCenter T with hc_def
  have hcim : c.im = T := by
    rw [hc_def]; exact jensenCenter_im T
  have hcre : c.re = 3 := by
    rw [hc_def]; exact jensenCenter_re T
  have hzim : z.im = T := by
    simp only [hz_def, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  have hzre : z.re = σ := by
    simp only [hz_def, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  set d : ℝ := ‖z - c‖ with hd_def
  have himzero : (z - c).im = 0 := by
    rw [Complex.sub_im, hzim, hcim]; ring
  have hzc_eq : z - c = ((σ - 3 : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.sub_re, hzre, hcre];
      simp only [Complex.ofReal_sub, Complex.ofReal_ofNat, Complex.sub_re, Complex.ofReal_re,
        Complex.re_ofNat]
    · rw [himzero];
      simp only [Complex.ofReal_sub, Complex.ofReal_ofNat, Complex.sub_im, Complex.ofReal_im,
        Complex.im_ofNat, sub_self]
  have hd_eq : d = |σ - 3| := by rw [hd_def, hzc_eq, Complex.norm_real, Real.norm_eq_abs]
  have hd_le : d ≤ 7 / 2 := by
    rw [hd_eq, abs_le]; constructor <;> linarith
  have hR1pos : (0 : ℝ) < R1 := by linarith [hR1big]
  have hzR1 : z ∈ Metric.ball c R1 := by
    rw [Metric.mem_ball, dist_eq_norm, ← hd_def]; linarith [hR1big, hd_le]
  have hzR2 : z ∈ Metric.ball c R2 := by
    rw [Metric.mem_ball, dist_eq_norm, ← hd_def]; linarith [hR1big, hd_le, hR1R2]
  have hh'R1 : ∀ w ∈ Metric.ball c R1, HasDerivAt h (logDeriv g w) w := fun w hw =>
    hh' w (Metric.ball_subset_ball hR1R2.le hw)
  have hMboundOpen : ∀ w ∈ Metric.ball c R1, (h w).re ≤ M := fun w hw =>
    hMbound w (Metric.ball_subset_closedBall hw)
  have hderiv_bound :=
    norm_hasDerivAt_le_of_re_le hR1pos hh'R1 hMc
      hMboundOpen hzR1
  have hdecomp :=
    logDeriv_riemannZeta_eq_sum_add_logDeriv_at hgAn
      hgne hmpos heqOn hzR2 hzgood
  set margin0 : ℝ :=
    1 / (4 * jensenLogConst * Real.log (H + 2)) with
    hmargin0_def
  have hLCpos := jensenLogConst_pos
  have hlogHpos : (0 : ℝ) < Real.log (H + 2) := Real.log_pos (by linarith)
  have hmargin0pos : 0 < margin0 := by
    rw [hmargin0_def]; positivity
  set margin1 : ℝ := min margin0 1 with hmargin1_def
  have hmargin1pos : 0 < margin1 := lt_min hmargin0pos (by norm_num only)
  have hmargin1_le_margin0 : margin1 ≤ margin0 := min_le_left _ _
  have hmargin1_le_1 : margin1 ≤ 1 := min_le_right _ _
  have hzu_margin : ∀ u ∈ S, margin1 ≤ ‖z - u‖ := by
    intro u hu
    have h2 : |T - u.im| ≤ ‖z - u‖ := by
      have h := Complex.abs_im_le_norm (z - u)
      rw [Complex.sub_im, hzim] at h
      exact h
    by_cases hcase : |u.im - H| ≤ 2
    · have h1 := hgood u (hSzero u hu) hcase
      linarith [hmargin1_le_margin0, h1, h2]
    · push Not at hcase
      have hTH : |T - H| ≤ 1 := abs_le.mpr ⟨by linarith [hT.1, hT.2], by linarith [hT.1, hT.2]⟩
      have htri : |u.im - H| ≤ |u.im - T| + |T - H| := by
        have h := abs_add_le (u.im - T) (T - H)
        simpa only [ge_iff_le, sub_add_sub_cancel] using h
      have hsymm : |u.im - T| = |T - u.im| := abs_sub_comm _ _
      linarith [htri, hTH, hcase, hsymm, h2, hmargin1_le_1]
  have hsum_bound :
    ‖∑ u ∈ S, (m u : ℂ) / (z - u)‖ ≤
      (jensenLogConst * Real.log (T + 2)) /
        margin1 := by
    calc
      ‖∑ u ∈ S, (m u : ℂ) / (z - u)‖ ≤ ∑ u ∈ S, ‖(m u : ℂ) / (z - u)‖ := norm_sum_le _ _
      _ = ∑ u ∈ S, (m u : ℝ) / ‖z - u‖ := by
        apply Finset.sum_congr rfl
        intro u _
        rw [norm_div, Complex.norm_natCast]
      _ ≤ ∑ u ∈ S, (m u : ℝ) / margin1 := by
        apply Finset.sum_le_sum
        intro u hu
        gcongr
        exact hzu_margin u hu
      _ = (∑ u ∈ S, (m u : ℝ)) / margin1 := by rw [Finset.sum_div]
      _ ≤
          (jensenLogConst * Real.log (T + 2)) /
            margin1 :=
        (div_le_div_iff_of_pos_right hmargin1pos).mpr hsum_le
  have hmargin1_inv_le :
    1 / margin1 ≤
      max (4 * jensenLogConst * Real.log (H + 2))
        1 := by
    rcases le_total margin0 1 with hcase | hcase
    · have heq : margin1 = margin0 := min_eq_left hcase
      rw [heq, hmargin0_def, one_div_one_div]
      exact le_max_left _ _
    · have heq : margin1 = 1 := min_eq_right hcase
      rw [heq]
      simp only [ne_eq, one_ne_zero, not_false_eq_true, div_self, le_max_iff, Std.le_refl, or_true]
  have hlogTpos : (0 : ℝ) < Real.log (T + 2) := Real.log_pos (by linarith)
  have hsemi :
    ‖logDeriv riemannZeta z‖ ≤
      jensenLogConst * Real.log (T + 2) *
          max (4 * jensenLogConst * Real.log (H + 2))
            1 +
        4 * (M - (h c).re) * (R1 + d) / (R1 - d) ^ 2 := by
    rw [hdecomp]
    calc
      ‖(∑ u ∈ S, (m u : ℂ) / (z - u)) + logDeriv g z‖ ≤
          ‖∑ u ∈ S, (m u : ℂ) / (z - u)‖ + ‖logDeriv g z‖ :=
        norm_add_le _ _
      _ ≤
          (jensenLogConst * Real.log (T + 2)) /
              margin1 +
            4 * (M - (h c).re) * (R1 + d) / (R1 - d) ^ 2 :=
        add_le_add hsum_bound hderiv_bound
      _ =
          jensenLogConst * Real.log (T + 2) *
              (1 / margin1) +
            4 * (M - (h c).re) * (R1 + d) / (R1 - d) ^ 2 :=
        by
        rw [div_eq_mul_one_div
            (jensenLogConst * Real.log (T + 2))]
      _ ≤
          jensenLogConst * Real.log (T + 2) *
              max
                (4 * jensenLogConst * Real.log (H + 2))
                1 +
            4 * (M - (h c).re) * (R1 + d) / (R1 - d) ^ 2 :=
        by gcongr
  have hR1lt37 : R1 < 37 / 10 := lt_trans hR1R2 hR2small
  exact
    le_qMinusOneZetaLogDerivConst_mul_log_sq_of_semi_explicit
      hH hT.1 hT.2 hR1big hR1lt37 hd_le hMc hMle hgjc_ge hsemi

/-- The explicit `O((log T)²/T²)` bound decays to `0` as `T → ∞`: `log(T+2)²/T²` is squeezed
between `0` and `4 * (log(T+2)/(T+2))²`, and the latter tends to `0` since `log t / t → 0`
(`isLittleO_log_id_atTop`). -/
theorem tendsto_log_add_two_sq_div_sq_atTop :
    Filter.Tendsto (fun T : ℝ => Real.log (T + 2) ^ 2 / T ^ 2) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun t : ℝ => Real.log t / t) Filter.atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h2 : Filter.Tendsto (fun T : ℝ => T + 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop 2 Filter.tendsto_id
  have h3 : Filter.Tendsto (fun T : ℝ => Real.log (T + 2) / (T + 2)) Filter.atTop (nhds 0) :=
    h1.comp h2
  have h4 :
    Filter.Tendsto (fun T : ℝ => (Real.log (T + 2) / (T + 2)) ^ 2) Filter.atTop (nhds 0) := by
    simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using h3.pow 2
  have h5 :
    Filter.Tendsto (fun T : ℝ => 4 * (Real.log (T + 2) / (T + 2)) ^ 2) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using h4.const_mul (4 : ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h5
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with T hT
    positivity
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with T hT
    have hTpos : (0 : ℝ) < T := by linarith
    have hkey : (T + 2) ^ 2 ≤ 4 * T ^ 2 := by nlinarith only [hT]
    have heq :
      (4 : ℝ) * (Real.log (T + 2) / (T + 2)) ^ 2 = (4 * Real.log (T + 2) ^ 2) / (T + 2) ^ 2 := by
      rw [div_pow]; ring
    rw [heq, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hkey (sq_nonneg (Real.log (T + 2)))]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
