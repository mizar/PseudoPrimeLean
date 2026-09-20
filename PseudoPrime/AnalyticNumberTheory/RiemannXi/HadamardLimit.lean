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
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import PseudoPrime.AnalyticNumberTheory.General.CanonicalDecomposition
import PseudoPrime.AnalyticNumberTheory.RiemannXi.OrderOneBound
import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroFiniteness
import PseudoPrime.AnalyticNumberTheory.Gamma.TrigammaSpecialValues

/-!
# Finite-radius xi factorization and its Hadamard limit

Zero-free spheres and canonical decomposition give finite-radius centered
logarithmic-derivative identities. Growth estimates and summability make the
error vanish along a good-radius sequence. Under RH the genus-one terms at one
become inverse squared norms. Endpoint and zeta-at-zero facts support the
zero-mass identity proved in `PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMass`.
-/

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- The nonnegative constant `|log(4π)/2 - 1 - γ/2|`, where `γ` is Euler's
constant. Under RH it is half the multiplicity-weighted inverse-square zero mass;
that identity is proved in `PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMass`. -/
noncomputable def riemannZeroMass : ℝ :=
  |Real.log (4 * Real.pi) / 2 - 1 - Real.eulerMascheroniConstant / 2|

/-- For every natural `n`, some radius in `(n,n+1)` has a zero-free xi sphere.
The finitely many zero norms in the closed ball of radius `n+1` cannot cover
this open interval. Such radii permit canonical-product boundary estimates. -/
theorem exists_riemannXi_zeroFree_radius (n : ℕ) :
    ∃ R : ℝ, (n : ℝ) < R ∧ R < n + 1 ∧ ∀ z : ℂ, ‖z‖ = R → riemannXi z ≠ 0 := by
  set S := riemannXiZerosInClosedBall ((n : ℝ) + 1) with hS_def
  set norms : Finset ℝ := S.image (fun ρ => ‖ρ‖) with hnorms_def
  have hIooInf : (Set.Ioo (n : ℝ) (n + 1)).Infinite := Set.Ioo_infinite (by linarith)
  have hdiff : (Set.Ioo (n : ℝ) (n + 1) \ (norms : Set ℝ)).Nonempty :=
    (hIooInf.sdiff norms.finite_toSet).nonempty
  obtain ⟨R, hRmem, hRnotin⟩ := hdiff
  obtain ⟨hRlt, hRlt1⟩ := hRmem
  refine ⟨R, hRlt, hRlt1, fun z hz hzero => hRnotin ?_⟩
  have hzball : z ∈ Metric.closedBall (0 : ℂ) ((n : ℝ) + 1) := by
    simp only [Metric.mem_closedBall, dist_zero_right, hz]
    linarith
  have hzmem : z ∈ S := mem_riemannXiZerosInClosedBall_iff.mpr ⟨hzero, hzball⟩
  rw [hnorms_def]
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
  exact ⟨z, hzmem, hz⟩

/-- Xi has finite meromorphic order at every point. Entireness and connectedness
propagate finite order from `ξ(0)=1/2`. This verifies the finite-order hypothesis
for canonical decomposition on closed balls. -/
theorem meromorphicOrderAt_riemannXi_ne_top (s : ℂ) : meromorphicOrderAt riemannXi s ≠ ⊤ := by
  have hanalytic : AnalyticAt ℂ riemannXi 0 := differentiable_riemannXi.analyticAt 0
  have horder : meromorphicOrderAt riemannXi 0 = 0 :=
    hanalytic.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
      (by
        rw [riemannXi_zero]; norm_num only)
  have hmero : Meromorphic riemannXi := fun u ↦
    differentiable_riemannXi.analyticAt u |>.meromorphicAt
  apply (hmero.exists_meromorphicOrderAt_ne_top_iff_forall.mp ?_) s
  exact
    ⟨0, by
      rw [horder];
      simp only [ne_eq, LinearOrderedAddCommGroupWithTop.zero_ne_top, not_false_eq_true]⟩

/-- Xi admits an extended canonical decomposition on each closed ball centered
at zero. Entireness and finite meromorphic order supply the decomposition;
its zero-free factor is used in growth and logarithmic-derivative estimates. -/
theorem exists_ecanonicalDecomp_riemannXi (R : ℝ) :
    ∃ g, Complex.ECanonicalDecomp riemannXi g R := by
  have hanalytic : AnalyticOnNhd ℂ riemannXi (Metric.closedBall (0 : ℂ) R) := fun z _ =>
    differentiable_riemannXi.analyticAt z
  exact
    MeromorphicOn.exists_ecanonicalDecomp hanalytic.meromorphicOn fun u =>
      meromorphicOrderAt_riemannXi_ne_top u

/-- Nonvanishing of xi at a point forces meromorphic order zero there. -/
theorem meromorphicOrderAt_riemannXi_eq_zero_of_ne_zero {i : ℂ} (hi : riemannXi i ≠ 0) :
    meromorphicOrderAt riemannXi i = 0 := by
  rw [(differentiable_riemannXi.analyticAt i).meromorphicOrderAt_eq,
    analyticOrderAt_eq_zero.mpr (Or.inr hi)]
  rfl

/-- On a zero-free sphere of positive radius, the canonical-decomposition
factor `g` has the same norm as xi. -/
theorem norm_ecanonicalDecomp_riemannXi_eq_of_zeroFree_sphere {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (D : Complex.ECanonicalDecomp riemannXi g R) (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → riemannXi ρ ≠ 0) {w : ℂ}
    (hw : ‖w‖ = R) : ‖g w‖ = ‖riemannXi w‖ := by
  have hanalyticSphere : AnalyticOnNhd ℂ riemannXi (Metric.sphere (0 : ℂ) R) := fun z _ =>
    differentiable_riemannXi.analyticAt z
  have hwmem : w ∈ Metric.closedBall (0 : ℂ) R := by rw [Metric.mem_closedBall, dist_zero_right, hw]
  have horder := meromorphicOrderAt_riemannXi_eq_zero_of_ne_zero (hzf w hw)
  have hlogeq := D.log_norm_eq hwmem horder hR
  have hspherezero :
    ∀ i : ℂ,
      ((MeromorphicOn.divisor riemannXi (Metric.sphere (0 : ℂ) R) i : ℤ) : ℝ) * Real.log ‖w - i‖ =
        0 := by
    intro i
    by_cases hi : i ∈ Metric.sphere (0 : ℂ) R
    · have hine : ‖i‖ = R := by rwa [Metric.mem_sphere, dist_zero_right] at hi
      have hdiv0 : MeromorphicOn.divisor riemannXi (Metric.sphere (0 : ℂ) R) i = 0 := by
        rw [MeromorphicOn.divisor_apply hanalyticSphere.meromorphicOn hi,
          meromorphicOrderAt_riemannXi_eq_zero_of_ne_zero (hzf i hine)]
        rfl
      simp only [hdiv0, Int.cast_zero, zero_mul]
    · have hdiv0 : MeromorphicOn.divisor riemannXi (Metric.sphere (0 : ℂ) R) i = 0 :=
        (MeromorphicOn.divisor riemannXi (Metric.sphere (0 : ℂ) R)).apply_eq_zero_of_notMem hi
      simp only [hdiv0, Int.cast_zero, zero_mul]
  have hballzero :
    ∀ i : ℂ,
      ((MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) i : ℤ) : ℝ) *
          Real.log ‖Complex.canonicalFactor R i w‖ =
        0 := by
    intro i
    by_cases hi0 : MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) i = 0
    · simp only [hi0, Int.cast_zero, zero_mul]
    · have hiball : i ∈ Metric.ball (0 : ℂ) R :=
        (MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R)).supportWithinDomain hi0
      have hwsphere : w ∈ Metric.sphere (0 : ℂ) R := by
        rw [Metric.mem_sphere, dist_zero_right]; exact hw
      rw [Complex.norm_canonicalFactor_eval_circle_eq_one hiball hwsphere, Real.log_one, mul_zero]
  rw [finsum_eq_zero_of_forall_eq_zero hballzero, finsum_eq_zero_of_forall_eq_zero hspherezero,
    sub_zero, zero_add] at hlogeq
  have hFw_ne := hzf w hw
  have hgw_ne := D.ne_zero w hwmem
  have hmtc_eq : meromorphicTrailingCoeffAt riemannXi w = riemannXi w :=
    (differentiable_riemannXi.analyticAt w).meromorphicTrailingCoeffAt_of_ne_zero hFw_ne
  rw [hmtc_eq] at hlogeq
  exact
    Real.log_injOn_pos (Set.mem_Ioi.mpr (norm_pos_iff.mpr hgw_ne))
      (Set.mem_Ioi.mpr (norm_pos_iff.mpr hFw_ne)) hlogeq

/-- For a positive radius, the canonical-decomposition factor has norm at zero
at least `‖ξ(0)‖`. In the logarithmic norm formula, each interior-zero
contribution `log(R/‖ρ‖)` is nonnegative. -/
theorem norm_ecanonicalDecomp_riemannXi_zero_ge {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (D : Complex.ECanonicalDecomp riemannXi g R) (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → riemannXi ρ ≠ 0) :
    ‖riemannXi 0‖ ≤ ‖g 0‖ := by
  have hanalyticBall : AnalyticOnNhd ℂ riemannXi (Metric.ball (0 : ℂ) R) := fun z _ =>
    differentiable_riemannXi.analyticAt z
  have hF0ne : riemannXi 0 ≠ 0 := by
    rw [riemannXi_zero]; norm_num only
  have h0mem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := by
    simp only [Metric.mem_closedBall, dist_self, hR.le]
  have horder0 := meromorphicOrderAt_riemannXi_eq_zero_of_ne_zero hF0ne
  have hlogeq := D.log_norm_eq h0mem horder0 hR
  have hspherezero :
    ∀ i : ℂ,
      ((MeromorphicOn.divisor riemannXi (Metric.sphere (0 : ℂ) R) i : ℤ) : ℝ) *
          Real.log ‖(0 : ℂ) - i‖ =
        0 := by
    intro i
    by_cases hi : i ∈ Metric.sphere (0 : ℂ) R
    · have hine : ‖i‖ = R := by rwa [Metric.mem_sphere, dist_zero_right] at hi
      have hanalyticSphere : AnalyticOnNhd ℂ riemannXi (Metric.sphere (0 : ℂ) R) := fun z _ =>
        differentiable_riemannXi.analyticAt z
      have hdiv0 : MeromorphicOn.divisor riemannXi (Metric.sphere (0 : ℂ) R) i = 0 := by
        rw [MeromorphicOn.divisor_apply hanalyticSphere.meromorphicOn hi,
          meromorphicOrderAt_riemannXi_eq_zero_of_ne_zero (hzf i hine)]
        rfl
      simp only [hdiv0, Int.cast_zero, zero_sub, norm_neg, zero_mul]
    · have hdiv0 : MeromorphicOn.divisor riemannXi (Metric.sphere (0 : ℂ) R) i = 0 :=
        (MeromorphicOn.divisor riemannXi (Metric.sphere (0 : ℂ) R)).apply_eq_zero_of_notMem hi
      simp only [hdiv0, Int.cast_zero, zero_sub, norm_neg, zero_mul]
  have hballnonneg :
    ∀ i : ℂ,
      (0 : ℝ) ≤
        ((MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) i : ℤ) : ℝ) *
          Real.log ‖Complex.canonicalFactor R i 0‖ := by
    intro i
    by_cases hi0 : MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) i = 0
    · simp only [hi0, Int.cast_zero, zero_mul, Std.le_refl]
    · have hiball : i ∈ Metric.ball (0 : ℂ) R :=
        (MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R)).supportWithinDomain hi0
      have hine0 : i ≠ 0 := by
        rintro rfl
        apply hi0
        rw [MeromorphicOn.divisor_apply hanalyticBall.meromorphicOn hiball, horder0]
        rfl
      have hnormlt : ‖i‖ < R := by rwa [Metric.mem_ball, dist_zero_right] at hiball
      have hnormeq : ‖Complex.canonicalFactor R i 0‖ = R / ‖i‖ := by
        rw [Complex.canonicalFactor_apply]
        simp only [mul_zero, sub_zero, zero_sub, norm_div, norm_mul, norm_neg, norm_pow]
        rw [Complex.norm_real, Real.norm_of_nonneg hR.le, sq, mul_div_mul_left R ‖i‖ hR.ne']
      have hge1 : (1 : ℝ) ≤ ‖Complex.canonicalFactor R i 0‖ := by
        rw [hnormeq, le_div_iff₀ (norm_pos_iff.mpr hine0)]
        linarith
      have hlognn : (0 : ℝ) ≤ Real.log ‖Complex.canonicalFactor R i 0‖ := Real.log_nonneg hge1
      have hdivnn :
        (0 : ℝ) ≤ ((MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) i : ℤ) : ℝ) :=
        mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalyticBall i
      exact mul_nonneg hdivnn hlognn
  rw [finsum_eq_zero_of_forall_eq_zero hspherezero, sub_zero] at hlogeq
  have hballnn :
    (0 : ℝ) ≤
      ∑ᶠ i,
        ((MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) i : ℤ) : ℝ) *
          Real.log ‖Complex.canonicalFactor R i 0‖ :=
    finsum_nonneg hballnonneg
  have hmtc_eq : meromorphicTrailingCoeffAt riemannXi 0 = riemannXi 0 :=
    (differentiable_riemannXi.analyticAt 0).meromorphicTrailingCoeffAt_of_ne_zero hF0ne
  rw [hmtc_eq] at hlogeq
  have hg0_pos : (0 : ℝ) < ‖g 0‖ := norm_pos_iff.mpr (D.ne_zero 0 h0mem)
  have hF0_pos : (0 : ℝ) < ‖riemannXi 0‖ := norm_pos_iff.mpr hF0ne
  have hlog_le : Real.log ‖riemannXi 0‖ ≤ Real.log ‖g 0‖ := by
    rw [hlogeq]; linarith
  exact (Real.log_le_log_iff hF0_pos hg0_pos).mp hlog_le

/-- For a positive radius with zero-free boundary, the maximum modulus principle
extends the xi boundary envelope to the canonical-decomposition factor on the closed ball. -/
theorem norm_ecanonicalDecomp_riemannXi_le_orderOneBound {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (D : Complex.ECanonicalDecomp riemannXi g R) (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → riemannXi ρ ≠ 0) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) R) : ‖g z‖ ≤ xiOrderOneBound (R + 1) := by
  have hcl : closure (Metric.ball (0 : ℂ) R) = Metric.closedBall (0 : ℂ) R := closure_ball 0 hR.ne'
  have hd : DiffContOnCl ℂ g (Metric.ball (0 : ℂ) R) := by
    apply DifferentiableOn.diffContOnCl
    rw [hcl]
    exact D.analyticOnNhd.differentiableOn
  have hfrontier : frontier (Metric.ball (0 : ℂ) R) = Metric.sphere (0 : ℂ) R :=
    frontier_ball 0 hR.ne'
  have hC : ∀ w ∈ frontier (Metric.ball (0 : ℂ) R), ‖g w‖ ≤ xiOrderOneBound (R + 1) := by
    intro w hw
    rw [hfrontier, Metric.mem_sphere, dist_zero_right] at hw
    rw [norm_ecanonicalDecomp_riemannXi_eq_of_zeroFree_sphere hR D hzf hw]
    exact
      norm_riemannXi_le_xiOrderOneBound_on_closedBall hR.le
        (by rw [Metric.mem_closedBall, dist_zero_right, hw])
  have hzcl : z ∈ closure (Metric.ball (0 : ℂ) R) := hcl ▸ hz
  exact Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hd hC hzcl

/-- For a positive zero-free radius, the logarithmic norm oscillation of the
canonical-decomposition factor is bounded using its boundary envelope and its
center lower bound. -/
theorem ecanonicalDecomp_riemannXi_log_norm_oscillation_le {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (D : Complex.ECanonicalDecomp riemannXi g R) (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → riemannXi ρ ≠ 0) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    Real.log ‖g z‖ - Real.log ‖g 0‖ ≤
      Real.log (xiOrderOneBound (R + 1)) - Real.log ‖riemannXi 0‖ := by
  have hzle := norm_ecanonicalDecomp_riemannXi_le_orderOneBound hR D hzf hz
  have hF0ge := norm_ecanonicalDecomp_riemannXi_zero_ge hR D hzf
  have hgz_pos : (0 : ℝ) < ‖g z‖ := norm_pos_iff.mpr (D.ne_zero z hz)
  have hg0_pos : (0 : ℝ) < ‖g 0‖ :=
    norm_pos_iff.mpr (D.ne_zero 0 (by simp only [Metric.mem_closedBall, dist_self, hR.le]))
  have hF0_pos : (0 : ℝ) < ‖riemannXi 0‖ :=
    norm_pos_iff.mpr
      (by
        rw [riemannXi_zero]; norm_num only)
  have hbound_pos : (0 : ℝ) < xiOrderOneBound (R + 1) := hgz_pos.trans_le hzle
  have h1 : Real.log ‖g z‖ ≤ Real.log (xiOrderOneBound (R + 1)) :=
    (Real.log_le_log_iff hgz_pos hbound_pos).mpr hzle
  have h2 : Real.log ‖riemannXi 0‖ ≤ Real.log ‖g 0‖ :=
    (Real.log_le_log_iff hF0_pos hg0_pos).mpr hF0ge
  calc
    Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ Real.log (xiOrderOneBound (R + 1)) - Real.log ‖g 0‖ :=
      sub_le_sub_right h1 _
    _ ≤ Real.log (xiOrderOneBound (R + 1)) - Real.log ‖riemannXi 0‖ := sub_le_sub_left h2 _

/-!
### Good radii

Choose `R_n` in `(n+2,n+3)` with a zero-free boundary. Then `R_n > 2`,
so the evaluation point one lies within the half-radius used in the estimates.
-/

/-- A zero-free radius past `n + 2`, chosen once and for all so later statements can refer to
`R_n` without re-choosing at each use site. -/
noncomputable def riemannXiGoodRadius (n : ℕ) : ℝ :=
  Classical.choose (exists_riemannXi_zeroFree_radius (n + 2))

/-- Packages `Classical.choose_spec` once, so the three named accessors below all destructure the
*same* proof term. -/
theorem riemannXiGoodRadius_spec (n : ℕ) :
    ((n : ℝ) + 2 < riemannXiGoodRadius n) ∧
      (riemannXiGoodRadius n < (n : ℝ) + 2 + 1) ∧
      (∀ ρ : ℂ, ‖ρ‖ = riemannXiGoodRadius n → riemannXi ρ ≠ 0) := by
  unfold riemannXiGoodRadius
  exact_mod_cast Classical.choose_spec (exists_riemannXi_zeroFree_radius (n + 2))

theorem riemannXiGoodRadius_gt (n : ℕ) : (n : ℝ) + 2 < riemannXiGoodRadius n :=
  (riemannXiGoodRadius_spec n).1

theorem riemannXiGoodRadius_gt_two (n : ℕ) : (2 : ℝ) < riemannXiGoodRadius n := by
  have h := riemannXiGoodRadius_gt n
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith only [h, hn]

theorem riemannXi_ne_zero_on_goodRadius (n : ℕ) :
    ∀ ρ : ℂ, ‖ρ‖ = riemannXiGoodRadius n → riemannXi ρ ≠ 0 :=
  (riemannXiGoodRadius_spec n).2.2

/-- The good-radius sequence tends to infinity, sandwiched between `n + 2` and `n + 3`. -/
theorem tendsto_riemannXiGoodRadius_atTop :
    Filter.Tendsto riemannXiGoodRadius Filter.atTop Filter.atTop := by
  have hlow : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop 2 tendsto_natCast_atTop_atTop
  exact Filter.tendsto_atTop_mono (fun n => (riemannXiGoodRadius_gt n).le) hlow

/-!
### A coarse logarithmic growth bound

The logarithm of `xiOrderOneBound (R+1)` is `O(R log R)`, hence its ratio
to `R²` tends to zero.
-/

/-- A crude cubic envelope for `PseudoPrime.AnalyticNumberTheory.RiemannXi.xiOrderOneBound`'s
polynomial factor, absorbing the
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.sawtoothRemainderBound (1/2)`
constant symbolically (its numeric value is never needed). -/
theorem xiOrderOnePolynomial_le {x : ℝ} (hx : 1 ≤ x) :
    x + (x + 1) / 2 + x * (x + 1) ^ 2 * RiemannZeta.sawtoothRemainderBound (1 / 2) ≤
      (2 + 4 * RiemannZeta.sawtoothRemainderBound (1 / 2)) * (x + 1) ^ 3 := by
  have hC : 0 ≤ RiemannZeta.sawtoothRemainderBound (1 / 2 : ℝ) :=
    RiemannZeta.sawtoothRemainderBound_nonneg _
  have hxpos : (0 : ℝ) < x + 1 := by linarith only [hx]
  have hge1 : (1 : ℝ) ≤ x + 1 := by linarith only [hx]
  have hcube : x + 1 ≤ (x + 1) ^ 3 := by
    have hsq : (1 : ℝ) ≤ (x + 1) ^ 2 := by nlinarith only [hge1]
    calc
      x + 1 = (x + 1) * 1 := by ring
      _ ≤ (x + 1) * (x + 1) ^ 2 := mul_le_mul_of_nonneg_left hsq hxpos.le
      _ = (x + 1) ^ 3 := by ring
  have h1 : x ≤ (x + 1) ^ 3 := by linarith only [hcube]
  have h2 : (x + 1) / 2 ≤ (x + 1) ^ 3 := by linarith only [hcube, hxpos]
  have hxle : x ≤ x + 1 := by linarith only [hxpos]
  have h3 : x * (x + 1) ^ 2 ≤ (x + 1) ^ 3 := by
    calc
      x * (x + 1) ^ 2 ≤ (x + 1) * (x + 1) ^ 2 := mul_le_mul_of_nonneg_right hxle (sq_nonneg (x + 1))
      _ = (x + 1) ^ 3 := by ring
  have h4 :
    x * (x + 1) ^ 2 * RiemannZeta.sawtoothRemainderBound (1 / 2) ≤
      (x + 1) ^ 3 * RiemannZeta.sawtoothRemainderBound (1 / 2) :=
    mul_le_mul_of_nonneg_right h3 hC
  nlinarith only [h1, h2, h4, hxpos, hC, pow_pos hxpos 3]

/-- The Gamma exponent `(x/2+1) log(x/2+1)` is bounded by
`(x+3) log(x+3)` for `x ≥ 1`, using monotonicity of `t log t` on `[1,∞)`. -/
theorem half_add_one_mul_log_le {x : ℝ} (hx : 1 ≤ x) :
    (x / 2 + 1) * Real.log (x / 2 + 1) ≤ (x + 3) * Real.log (x + 3) :=
  Gamma.mul_log_mono_of_one_le (by linarith only [hx]) (by linarith only [hx])

/-- A single fixed additive constant absorbing every implicit constant in
`PseudoPrime.AnalyticNumberTheory.RiemannXi.xiOrderOneBound`'s
three factors: the polynomial envelope's
`2 + 4·PseudoPrime.AnalyticNumberTheory.RiemannZeta.sawtoothRemainderBound(1/2)` coefficient, plus a
`+1` slack absorbing the `1 +` head term (via `1 + B ≤ 2B ≤ exp(1)·B` once `B ≥ 1`). Its numeric
value is never needed, only its nonnegativity. -/
noncomputable def xiOrderOneGrowthConstant : ℝ :=
  3 + 4 * RiemannZeta.sawtoothRemainderBound (1 / 2)

/-- For `x ≥ 1`, the envelope at `x+1` is bounded by
`exp(xiOrderOneGrowthConstant + 2*(x+4)*log(x+4))`.
Bound the Gamma exponent by `(x+4) log(x+4)` and absorb the polynomial
factor and the additive head term into the remaining exponential bound. -/
theorem xiOrderOneBound_le_exp_orderOne {x : ℝ} (hx : 1 ≤ x) :
    xiOrderOneBound (x + 1) ≤
      Real.exp (xiOrderOneGrowthConstant + 2 * (x + 4) * Real.log (x + 4)) := by
  have hC : 0 ≤ RiemannZeta.sawtoothRemainderBound (1 / 2 : ℝ) :=
    RiemannZeta.sawtoothRemainderBound_nonneg _
  have hx1 : (1 : ℝ) ≤ x + 1 := by linarith
  have hpoly := xiOrderOnePolynomial_le hx1
  have hgle := half_add_one_mul_log_le hx1
  have hx13 : x + 1 + 3 = x + 4 := by ring
  rw [hx13] at hgle
  set L : ℝ := (x + 4) * Real.log (x + 4) with hL_def
  have hx4pos : (0 : ℝ) < x + 4 := by linarith
  have hlog4pos : 0 < Real.log (x + 4) := Real.log_pos (by linarith)
  have hLpos : 0 < L := by
    rw [hL_def]; positivity
  -- the polynomial factor, evaluated at `x + 1`, is at most `K · (x + 4) ^ 3`
  have hx24 : (x + 2 : ℝ) ^ 3 ≤ (x + 4) ^ 3 := by apply pow_le_pow_left₀ (by linarith) (by linarith)
  set K : ℝ := 2 + 4 * RiemannZeta.sawtoothRemainderBound (1 / 2) with hK_def
  have hKnn : (0 : ℝ) ≤ K := by
    rw [hK_def]; linarith
  have hpoly4 :
    (x + 1) + (x + 1 + 1) / 2 +
        (x + 1) * (x + 1 + 1) ^ 2 * RiemannZeta.sawtoothRemainderBound (1 / 2) ≤
      K * (x + 4) ^ 3 := by
    calc
      (x + 1) + (x + 1 + 1) / 2 +
            (x + 1) * (x + 1 + 1) ^ 2 * RiemannZeta.sawtoothRemainderBound (1 / 2) ≤
          K * (x + 2) ^ 3 :=
        by
        rw [hK_def]; convert hpoly using 2; ring
      _ ≤ K * (x + 4) ^ 3 := mul_le_mul_of_nonneg_left hx24 hKnn
  -- `(x + 4) ^ 3 ≤ exp L`
  have hcubeeq : (x + 4 : ℝ) ^ 3 = Real.exp (3 * Real.log (x + 4)) := by
    have hlp := Real.log_pow (x + 4) 3
    rw [show ((3 : ℕ) : ℝ) = (3 : ℝ) from by norm_num only] at hlp
    rw [← hlp, Real.exp_log (by positivity)]
  have hcube_le : (x + 4 : ℝ) ^ 3 ≤ Real.exp L := by
    rw [hcubeeq, hL_def]
    apply Real.exp_le_exp.mpr
    nlinarith only [hx, hlog4pos]
  -- `π^{-1/4} ≤ 1`
  have hpifac : (Real.pi : ℝ) ^ (-(1 : ℝ) / 4) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by norm_num only)
  -- the Gamma-exponential factor is `≤ exp L`
  have hexpg_le : Real.exp (((x + 1 : ℝ) / 2 + 1) * Real.log ((x + 1) / 2 + 1)) ≤ Real.exp L :=
    Real.exp_le_exp.mpr hgle
  -- assemble the head term `A ≤ exp(K + 2L)`
  set A : ℝ :=
    (Real.pi : ℝ) ^ (-(1 : ℝ) / 4) * Real.exp (((x + 1 : ℝ) / 2 + 1) * Real.log ((x + 1) / 2 + 1)) *
      ((x + 1) + (x + 1 + 1) / 2 +
        (x + 1) * (x + 1 + 1) ^ 2 * RiemannZeta.sawtoothRemainderBound (1 / 2)) with
    hA_def
  have hpolynn :
    (0 : ℝ) ≤
      (x + 1) + (x + 1 + 1) / 2 +
        (x + 1) * (x + 1 + 1) ^ 2 * RiemannZeta.sawtoothRemainderBound (1 / 2) := by
    positivity
  have hA_le : A ≤ K * Real.exp (2 * L) := by
    rw [hA_def]
    calc
      (Real.pi : ℝ) ^ (-(1 : ℝ) / 4) *
            Real.exp (((x + 1 : ℝ) / 2 + 1) * Real.log ((x + 1) / 2 + 1)) *
            ((x + 1) + (x + 1 + 1) / 2 +
              (x + 1) * (x + 1 + 1) ^ 2 * RiemannZeta.sawtoothRemainderBound (1 / 2)) ≤
          1 * Real.exp L *
            ((x + 1) + (x + 1 + 1) / 2 +
              (x + 1) * (x + 1 + 1) ^ 2 * RiemannZeta.sawtoothRemainderBound (1 / 2)) :=
        by gcongr
      _ =
          Real.exp L *
            ((x + 1) + (x + 1 + 1) / 2 +
              (x + 1) * (x + 1 + 1) ^ 2 * RiemannZeta.sawtoothRemainderBound (1 / 2)) :=
        by ring
      _ ≤ Real.exp L * (K * (x + 4) ^ 3) := mul_le_mul_of_nonneg_left hpoly4 (Real.exp_pos _).le
      _ ≤ Real.exp L * (K * Real.exp L) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcube_le hKnn) (Real.exp_pos _).le
      _ = K * Real.exp (2 * L) := by
        rw [two_mul, Real.exp_add]; ring
  have hKexp : K ≤ Real.exp K := by linarith [Real.add_one_le_exp K]
  have hB_ge1 : (1 : ℝ) ≤ Real.exp (K + 2 * L) := by
    apply Real.one_le_exp
    linarith
  have hAB : A ≤ Real.exp (K + 2 * L) := by
    calc
      A ≤ K * Real.exp (2 * L) := hA_le
      _ ≤ Real.exp K * Real.exp (2 * L) := mul_le_mul_of_nonneg_right hKexp (Real.exp_pos _).le
      _ = Real.exp (K + 2 * L) := (Real.exp_add K (2 * L)).symm
  have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hfinal : (1 : ℝ) + A ≤ Real.exp (1 + (K + 2 * L)) := by
    have h1 : (1 : ℝ) + A ≤ 2 * Real.exp (K + 2 * L) := by linarith [hAB, hB_ge1]
    have h2 : 2 * Real.exp (K + 2 * L) ≤ Real.exp 1 * Real.exp (K + 2 * L) :=
      mul_le_mul_of_nonneg_right hexp1 (Real.exp_pos _).le
    calc
      (1 : ℝ) + A ≤ 2 * Real.exp (K + 2 * L) := h1
      _ ≤ Real.exp 1 * Real.exp (K + 2 * L) := h2
      _ = Real.exp (1 + (K + 2 * L)) := (Real.exp_add 1 (K + 2 * L)).symm
  have hunfold : xiOrderOneBound (x + 1) = 1 + A := by rw [hA_def, xiOrderOneBound]
  rw [hunfold]
  convert hfinal using 2
  rw [hK_def]
  unfold xiOrderOneGrowthConstant
  ring

/-- The logarithm of the xi envelope has an explicit `O(x log x)` bound for `x ≥ 1`. -/
theorem log_xiOrderOneBound_le_orderOne {x : ℝ} (hx : 1 ≤ x) :
    Real.log (xiOrderOneBound (x + 1)) ≤
      xiOrderOneGrowthConstant + 2 * (x + 4) * Real.log (x + 4) := by
  have hle := xiOrderOneBound_le_exp_orderOne hx
  have hpos : (0 : ℝ) < xiOrderOneBound (x + 1) := by
    have h1 : (0 : ℝ) ≤ x + 1 := by linarith only [hx]
    exact lt_of_lt_of_le zero_lt_one (one_le_xiOrderOneBound h1)
  calc
    Real.log (xiOrderOneBound (x + 1)) ≤
        Real.log (Real.exp (xiOrderOneGrowthConstant + 2 * (x + 4) * Real.log (x + 4))) :=
      Real.log_le_log hpos hle
    _ = xiOrderOneGrowthConstant + 2 * (x + 4) * Real.log (x + 4) := Real.log_exp _

/-!
### Derivative variation from a real-part bound

Apply `PseudoPrime.AnalyticNumberTheory.General.norm_hasDerivAt_sub_le_of_re_le`
to a holomorphic primitive of the zero-free factor's logarithmic derivative.
-/

/-!
### Logarithmic-derivative variation, at general points and at one
-/

/-- For `R > 2` with zero-free boundary, the logarithmic derivative of the
canonical-decomposition factor varies by an explicit multiple of `‖s‖` between
zero and `‖s‖ ≤ R/2`. The coefficient is controlled by logarithmic xi growth. -/
theorem norm_logDeriv_ecanonicalDecomp_riemannXi_sub_zero_le {R : ℝ} (hR : 2 < R) {g : ℂ → ℂ}
    (D : Complex.ECanonicalDecomp riemannXi g R) (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → riemannXi ρ ≠ 0) {s : ℂ}
    (hs : ‖s‖ ≤ R / 2) :
    ‖logDeriv g s - logDeriv g 0‖ ≤
      192 * ‖s‖ *
          (xiOrderOneGrowthConstant + 2 * (R + 4) * Real.log (R + 4) - Real.log ‖riemannXi 0‖ + 1) /
        R ^ 2 := by
  have hR0 : 0 < R := by linarith
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hanalyticBall : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) R) := fun z hz =>
    D.analyticOnNhd z (Metric.ball_subset_closedBall hz)
  have hgne : ∀ w ∈ Metric.ball (0 : ℂ) R, g w ≠ 0 := fun w hw =>
    D.ne_zero w (Metric.ball_subset_closedBall hw)
  obtain ⟨hh, hh', hh_re⟩ :=
    RiemannZeta.exists_hasDerivAt_logDeriv_re_eq_log_norm hR0 hanalyticBall hgne
  have hF0_pos : (0 : ℝ) < ‖riemannXi 0‖ :=
    norm_pos_iff.mpr
      (by
        rw [riemannXi_zero]; norm_num only)
  have h0R : ‖(0 : ℂ)‖ ≤ R := by
    rw [norm_zero]; linarith
  have hboundge : ‖riemannXi 0‖ ≤ xiOrderOneBound (R + 1) :=
    norm_riemannXi_le_xiOrderOneBound_on_closedBall hR0.le
      (by simp only [Metric.mem_closedBall, dist_self, hR0.le])
  have hlog_bound_le :
    Real.log (xiOrderOneBound (R + 1)) ≤
      xiOrderOneGrowthConstant + 2 * (R + 4) * Real.log (R + 4) :=
    log_xiOrderOneBound_le_orderOne hR1
  have hlogF0_le_bound : Real.log ‖riemannXi 0‖ ≤ Real.log (xiOrderOneBound (R + 1)) :=
    Real.log_le_log hF0_pos hboundge
  have hosc :
    ∀ w ∈ Metric.ball (0 : ℂ) R,
      (hh w).re ≤
        (hh 0).re +
          (xiOrderOneGrowthConstant + 2 * (R + 4) * Real.log (R + 4) - Real.log ‖riemannXi 0‖) := by
    intro w hw
    have hwcl : w ∈ Metric.closedBall (0 : ℂ) R := Metric.ball_subset_closedBall hw
    have h0ball : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := Metric.mem_ball_self hR0
    have hoscR := ecanonicalDecomp_riemannXi_log_norm_oscillation_le hR0 D hzf hwcl
    have hew := hh_re w hw
    have he0 := hh_re 0 h0ball
    linarith [hoscR, hlog_bound_le, hew, he0]
  set M : ℝ :=
    (hh 0).re +
      (xiOrderOneGrowthConstant + 2 * (R + 4) * Real.log (R + 4) - Real.log ‖riemannXi 0‖) +
      1 with
    hM_def
  have hM0 : (hh 0).re < M := by
    rw [hM_def]; linarith [hlog_bound_le, hlogF0_le_bound]
  have hRe_le : ∀ w ∈ Metric.ball (0 : ℂ) R, (hh w).re ≤ M := by
    intro w hw
    have := hosc w hw
    rw [hM_def]; linarith
  have h7 := General.norm_hasDerivAt_sub_le_of_re_le hR0 hh' hM0 hRe_le hs
  have hMcalc :
    M - (hh 0).re =
      xiOrderOneGrowthConstant + 2 * (R + 4) * Real.log (R + 4) - Real.log ‖riemannXi 0‖ + 1 := by
    rw [hM_def]; ring
  rw [hMcalc] at h7
  set A : ℝ :=
    xiOrderOneGrowthConstant + 2 * (R + 4) * Real.log (R + 4) - Real.log ‖riemannXi 0‖ + 1 with
    hA_def
  have hApos : 0 < A := by
    rw [← hMcalc]; linarith
  have hRs_pos : (0 : ℝ) < R - ‖s‖ := by linarith
  have hratio : (R + ‖s‖) / (R - ‖s‖) ^ 3 ≤ 12 / R ^ 2 := by
    rw [div_le_div_iff₀ (pow_pos hRs_pos 3) (by positivity)]
    have h3 : (R / 2) ^ 3 ≤ (R - ‖s‖) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
    nlinarith only [h3, sq_nonneg R, norm_nonneg s, hs, hR0]
  have hcrude : 16 * A * (R + ‖s‖) / (R - ‖s‖) ^ 3 * ‖s‖ ≤ 192 * A * ‖s‖ / R ^ 2 := by
    have hAnn : (0 : ℝ) ≤ 16 * A := by linarith
    have hsnn : (0 : ℝ) ≤ ‖s‖ := norm_nonneg s
    have h1 : 16 * A * ((R + ‖s‖) / (R - ‖s‖) ^ 3) ≤ 16 * A * (12 / R ^ 2) :=
      mul_le_mul_of_nonneg_left hratio hAnn
    calc
      16 * A * (R + ‖s‖) / (R - ‖s‖) ^ 3 * ‖s‖ = (16 * A * ((R + ‖s‖) / (R - ‖s‖) ^ 3)) * ‖s‖ := by
        ring
      _ ≤ (16 * A * (12 / R ^ 2)) * ‖s‖ := mul_le_mul_of_nonneg_right h1 hsnn
      _ = 192 * A * ‖s‖ / R ^ 2 := by ring
  calc
    ‖logDeriv g s - logDeriv g 0‖ ≤ 16 * A * (R + ‖s‖) / (R - ‖s‖) ^ 3 * ‖s‖ := h7
    _ ≤ 192 * A * ‖s‖ / R ^ 2 := hcrude
    _ = 192 * ‖s‖ * A / R ^ 2 := by ring

/-- Specialize the canonical-factor logarithmic-derivative variation bound to `s=1`. -/
theorem norm_logDeriv_ecanonicalDecomp_riemannXi_one_sub_zero_le {R : ℝ} (hR : 2 < R) {g : ℂ → ℂ}
    (D : Complex.ECanonicalDecomp riemannXi g R) (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → riemannXi ρ ≠ 0) :
    ‖logDeriv g 1 - logDeriv g 0‖ ≤
      192 *
          (xiOrderOneGrowthConstant + 2 * (R + 4) * Real.log (R + 4) - Real.log ‖riemannXi 0‖ + 1) /
        R ^ 2 := by
  have hs1 : ‖(1 : ℂ)‖ ≤ R / 2 := by
    rw [norm_one]; linarith
  have h := norm_logDeriv_ecanonicalDecomp_riemannXi_sub_zero_le hR D hzf hs1
  rwa [norm_one, mul_one] at h

/-!
### Centered logarithmic derivatives at finite radius

The generic canonical-factor identities separate genus-one terms from the
finite-radius correction. Xi's nonzero values at zero and one allow evaluation
at these endpoints without additional arithmetic assumptions.
-/

/-- On a zero-free xi sphere, every sphere-divisor exponent is zero, so the
sphere factor is identically one. -/
theorem sphereFactor_riemannXi_eq_one_of_zeroFree {R : ℝ}
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → riemannXi ρ ≠ 0) :
    (∏ᶠ v : ℂ,
        (fun z : ℂ => z - v) ^ (MeromorphicOn.divisor riemannXi (Metric.sphere (0 : ℂ) R) v)) =
      (1 : ℂ → ℂ) := by
  apply finprod_eq_one_of_forall_eq_one
  intro v
  by_cases hv : v ∈ Metric.sphere (0 : ℂ) R
  · have hvne : ‖v‖ = R := by rwa [Metric.mem_sphere, dist_zero_right] at hv
    have hanalyticSphere : AnalyticOnNhd ℂ riemannXi (Metric.sphere (0 : ℂ) R) := fun z _ =>
      differentiable_riemannXi.analyticAt z
    have hdiv0 : MeromorphicOn.divisor riemannXi (Metric.sphere (0 : ℂ) R) v = 0 := by
      rw [MeromorphicOn.divisor_apply hanalyticSphere.meromorphicOn hv,
        meromorphicOrderAt_riemannXi_eq_zero_of_ne_zero (hzf v hvne)]
      rfl
    rw [hdiv0]; funext z
    simp only [Pi.pow_apply, zpow_ofNat, pow_zero, Pi.one_apply]
  · have hdiv0 : MeromorphicOn.divisor riemannXi (Metric.sphere (0 : ℂ) R) v = 0 :=
      (MeromorphicOn.divisor riemannXi (Metric.sphere (0 : ℂ) R)).apply_eq_zero_of_notMem hv
    rw [hdiv0]; funext z
    simp only [Pi.pow_apply, zpow_ofNat, pow_zero, Pi.one_apply]

/-- For a zero-free boundary sphere, the right-hand side of the extended canonical
decomposition is meromorphic at each point of its closed ball. -/
theorem meromorphicAt_riemannXi_ecanonicalDecompRHS {R : ℝ} {g : ℂ → ℂ}
    (D : Complex.ECanonicalDecomp riemannXi g R) (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → riemannXi ρ ≠ 0) {x : ℂ}
    (hx : x ∈ Metric.closedBall (0 : ℂ) R) :
    MeromorphicAt
      (((∏ᶠ u : ℂ,
            (Complex.canonicalFactor R u) ^
              (-MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) u)) *
          (∏ᶠ v : ℂ,
            (fun z : ℂ => z - v) ^ (MeromorphicOn.divisor riemannXi (Metric.sphere (0 : ℂ) R) v))) •
        g)
      x := by
  have hprod :
    MeromorphicAt
      (∏ᶠ u : ℂ,
        (Complex.canonicalFactor R u) ^
          (-MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) u))
      x :=
    MeromorphicAt.finprod (fun u => (Complex.meromorphic_canonicalFactor R u x).zpow _)
  have hsphere1 := sphereFactor_riemannXi_eq_one_of_zeroFree hzf (R := R)
  have hgAt : MeromorphicAt g x := (D.analyticOnNhd x hx).meromorphicAt
  rw [hsphere1, mul_one]
  exact hprod.smul hgAt

/-- Where xi is nonzero, the finite canonical-factor product is analytic. -/
theorem analyticAt_canonicalFactorProduct_of_riemannXi_ne_zero {R : ℝ} {x : ℂ}
    (hxclosed : x ∈ Metric.closedBall (0 : ℂ) R) (hxne : riemannXi x ≠ 0) :
    AnalyticAt ℂ
      (∏ᶠ u : ℂ,
        (Complex.canonicalFactor R u) ^
          (-MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) u))
      x := by
  apply analyticAt_finprod
  intro u
  by_cases hdu : MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) u = 0
  · rw [hdu, neg_zero, zpow_zero]
    exact analyticAt_const
  · have huball : u ∈ Metric.ball (0 : ℂ) R :=
      (MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R)).supportWithinDomain hdu
    have huxne : u ≠ x := by
      rintro rfl
      apply hdu
      have hanalyticBall : AnalyticOnNhd ℂ riemannXi (Metric.ball (0 : ℂ) R) := fun z _ =>
        differentiable_riemannXi.analyticAt z
      rw [MeromorphicOn.divisor_apply hanalyticBall.meromorphicOn huball,
        meromorphicOrderAt_riemannXi_eq_zero_of_ne_zero hxne]
      rfl
    have hcfAt : AnalyticAt ℂ (Complex.canonicalFactor R u) x :=
      Complex.analyticOnNhd_canonicalFactor R u x huxne.symm
    have hcfne : Complex.canonicalFactor R u x ≠ 0 :=
      Complex.canonicalFactor_ne_zero huball hxclosed huxne.symm
    exact hcfAt.zpow hcfne

/-- At a nonzero xi value in the closed ball, the canonical decomposition gives
the pointwise logarithmic-derivative identity. -/
theorem ecanonicalDecomp_riemannXi_logDeriv_eq_at {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (D : Complex.ECanonicalDecomp riemannXi g R) (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → riemannXi ρ ≠ 0) {x : ℂ}
    (hxclosed : x ∈ Metric.closedBall (0 : ℂ) R) (hxne : riemannXi x ≠ 0) :
    logDeriv riemannXi x =
      logDeriv
          (∏ᶠ u : ℂ,
            (Complex.canonicalFactor R u) ^
              (-MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) u))
          x +
        logDeriv g x := by
  set P : ℂ → ℂ :=
    ∏ᶠ u : ℂ,
      (Complex.canonicalFactor R u) ^
        (-MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) u) with
    hP_def
  have hFAt : MeromorphicAt riemannXi x := (differentiable_riemannXi.analyticAt x).meromorphicAt
  have hRHSAt := meromorphicAt_riemannXi_ecanonicalDecompRHS D hzf hxclosed
  have hFeqRHS :=
    hFAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect hRHSAt hxclosed
      (General.preperfect_closedBall hR) D.eventuallyEq
  have hsphere1 := sphereFactor_riemannXi_eq_one_of_zeroFree hzf (R := R)
  have hFeqPg : riemannXi =ᶠ[nhdsWithin x {x}ᶜ] (P * g) := by
    have hrw :
      (((P *
              (∏ᶠ v : ℂ,
                (fun z : ℂ => z - v) ^
                  (MeromorphicOn.divisor riemannXi (Metric.sphere (0 : ℂ) R) v))) •
            g) :
          ℂ → ℂ) =
        P * g := by
      rw [hsphere1, mul_one]; funext z
      simp only [Pi.smul_apply', smul_eq_mul, Pi.mul_apply]
    rwa [hrw] at hFeqRHS
  have hPAt : AnalyticAt ℂ P x :=
    analyticAt_canonicalFactorProduct_of_riemannXi_ne_zero hxclosed hxne
  have hgxne : g x ≠ 0 := D.ne_zero x hxclosed
  have hPxne : P x ≠ 0 := by
    have hFxeqPg : riemannXi x = (P * g) x :=
      General.eq_of_eventuallyEq_nhdsNE_of_continuousAt
        (differentiable_riemannXi.analyticAt x).continuousAt
        (hPAt.continuousAt.mul (D.analyticOnNhd x hxclosed).continuousAt) hFeqPg
    intro hP0
    rw [show (P * g) x = P x * g x from rfl, hP0, zero_mul] at hFxeqPg
    exact hxne hFxeqPg
  have hlogDerivEq : logDeriv riemannXi =ᶠ[nhdsWithin x {x}ᶜ] logDeriv (P * g) :=
    logDeriv_congr_nhdsNE hFeqPg
  have hFContAt : ContinuousAt (logDeriv riemannXi) x := by
    have h1 : ContinuousAt (deriv riemannXi) x :=
      (differentiable_riemannXi.deriv.analyticAt x).continuousAt
    exact h1.div (differentiable_riemannXi.analyticAt x).continuousAt hxne
  have hPgContAt : ContinuousAt (logDeriv (P * g)) x := by
    have hderivPg : ContinuousAt (deriv (P * g)) x := by
      have : AnalyticAt ℂ (deriv (P * g)) x := (hPAt.mul (D.analyticOnNhd x hxclosed)).deriv
      exact this.continuousAt
    have hPgcont : ContinuousAt (P * g) x :=
      hPAt.continuousAt.mul (D.analyticOnNhd x hxclosed).continuousAt
    have hPgne : (P * g) x ≠ 0 := mul_ne_zero hPxne hgxne
    exact hderivPg.div hPgcont hPgne
  have hval := General.eq_of_eventuallyEq_nhdsNE_of_continuousAt hFContAt hPgContAt hlogDerivEq
  rw [hval]
  exact
    logDeriv_mul x hPxne hgxne hPAt.differentiableAt (D.analyticOnNhd x hxclosed).differentiableAt

/-- A point in the support of xi's ball divisor differs from any point where xi is nonzero. -/
theorem ne_of_mem_divisorBallSupport_of_riemannXi_ne_zero {R : ℝ} {u x : ℂ}
    (hu : MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) u ≠ 0) (hxne : riemannXi x ≠ 0) :
    u ≠ x := by
  rintro rfl
  apply hu
  have huball : u ∈ Metric.ball (0 : ℂ) R :=
    (MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R)).supportWithinDomain hu
  have hanalyticBall : AnalyticOnNhd ℂ riemannXi (Metric.ball (0 : ℂ) R) := fun z _ =>
    differentiable_riemannXi.analyticAt z
  rw [MeromorphicOn.divisor_apply hanalyticBall.meromorphicOn huball,
    meromorphicOrderAt_riemannXi_eq_zero_of_ne_zero hxne]
  rfl

/-- At a point where xi is nonzero, the logarithmic derivative of the finite
canonical-factor product equals the weighted sum of the individual logarithmic derivatives. -/
theorem logDeriv_riemannXi_canonicalFactorProduct_eq_finsum_at {R : ℝ} {x : ℂ}
    (hxclosed : x ∈ Metric.closedBall (0 : ℂ) R) (hxne : riemannXi x ≠ 0) :
    logDeriv
        (∏ᶠ u : ℂ,
          (Complex.canonicalFactor R u) ^
            (-MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) u))
        x =
      ∑ᶠ u : ℂ,
        ((-MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) u : ℤ) : ℂ) *
          logDeriv (Complex.canonicalFactor R u) x := by
  have hanalyticClosed : AnalyticOnNhd ℂ riemannXi (Metric.closedBall (0 : ℂ) R) := fun z _ =>
    differentiable_riemannXi.analyticAt z
  have hfin := hanalyticClosed.meromorphicOn.divisor_ball_support_finite
  have hdfin :
    (Function.support
        (fun u : ℂ => -MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) u)).Finite := by
    simpa only [Function.support, ne_eq, neg_eq_zero] using hfin
  have hkey : ∀ i ∈ hdfin.toFinset, i ≠ x ∧ i ∈ Metric.ball (0 : ℂ) R := by
    intro i hi
    rw [Set.Finite.mem_toFinset, Function.mem_support, ne_eq, neg_eq_zero] at hi
    have hine : i ≠ x := ne_of_mem_divisorBallSupport_of_riemannXi_ne_zero hi hxne
    exact ⟨hine, (MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R)).supportWithinDomain hi⟩
  have h0 :
    (∏ᶠ u : ℂ,
        (Complex.canonicalFactor R u) ^
          (-MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) u)) =
      ∏ i ∈ hdfin.toFinset,
        (Complex.canonicalFactor R i) ^
          (-MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) i) := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro i hi
    simp only [Function.mem_mulSupport] at hi
    simp only [Set.Finite.coe_toFinset, Function.mem_support, ne_eq, neg_eq_zero]
    intro hi0
    exact
      hi
        (by
          rw [hi0]; simp only [neg_zero, zpow_ofNat, pow_zero])
  have hAnalyticAll : ∀ i ∈ hdfin.toFinset, AnalyticAt ℂ (Complex.canonicalFactor R i) x :=
    fun i hi => Complex.analyticOnNhd_canonicalFactor R i x (hkey i hi).1.symm
  have hcfxne :
    ∀ i ∈ hdfin.toFinset,
      Complex.canonicalFactor R i x ^ (-MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) i) ≠
        0 :=
    fun i hi =>
    zpow_ne_zero _ (Complex.canonicalFactor_ne_zero (hkey i hi).2 hxclosed (hkey i hi).1.symm)
  have hdAt :
    ∀ i ∈ hdfin.toFinset,
      DifferentiableAt ℂ
        (fun z =>
          (Complex.canonicalFactor R i z) ^
            (-MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) i))
        x :=
    fun i hi =>
    (hAnalyticAll i hi).differentiableAt.zpow
      (Or.inl (Complex.canonicalFactor_ne_zero (hkey i hi).2 hxclosed (hkey i hi).1.symm))
  have hprodfun :
    (fun a =>
        ∏ i ∈ hdfin.toFinset,
          (Complex.canonicalFactor R i a) ^
            (-MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) i)) =
      ∏ i ∈ hdfin.toFinset,
        (fun a =>
          (Complex.canonicalFactor R i a) ^
            (-MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) i)) := by
    funext a
    rw [Finset.prod_apply]
  have hstep :
    logDeriv
        (fun a =>
          ∏ i ∈ hdfin.toFinset,
            (Complex.canonicalFactor R i a) ^
              (-MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) i))
        x =
      ∑ i ∈ hdfin.toFinset,
        logDeriv
          (fun z =>
            (Complex.canonicalFactor R i z) ^
              (-MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) i))
          x := by
    rw [hprodfun]
    exact logDeriv_prod hcfxne hdAt
  rw [h0, Finset.prod_fn]
  rw [show
      (fun a =>
          ∏ i ∈ hdfin.toFinset,
            (Complex.canonicalFactor R i ^
                (-MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) i))
              a) =
        (fun a =>
          ∏ i ∈ hdfin.toFinset,
            (Complex.canonicalFactor R i a) ^
              (-MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) i))
      from rfl,
    hstep]
  have hsub :
    Function.support
        (fun i : ℂ =>
          ((-MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) i : ℤ) : ℂ) *
            logDeriv (Complex.canonicalFactor R i) x) ⊆
      hdfin.toFinset := by
    intro i hi
    rw [Function.mem_support] at hi
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    intro h0'
    apply hi
    rw [h0']; simp only [Int.cast_zero, zero_mul]
  rw [show
      (∑ i ∈ hdfin.toFinset,
          logDeriv
            (fun z =>
              (Complex.canonicalFactor R i z) ^
                (-MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) i))
            x) =
        ∑ i ∈ hdfin.toFinset,
          ((-MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) i : ℤ) : ℂ) *
            logDeriv (Complex.canonicalFactor R i) x
      from
      Finset.sum_congr rfl
        (fun i hi => by rw [logDeriv_fun_zpow (hAnalyticAll i hi).differentiableAt, mul_comm])]
  exact (finsum_eq_sum_of_support_subset _ hsub).symm

/-- The centered logarithmic derivative at finite radius splits into the
zero-free factor's variation, genus-one terms, and the canonical correction. -/
theorem ecanonicalDecomp_riemannXi_centered_logDeriv_eq {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (D : Complex.ECanonicalDecomp riemannXi g R) (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → riemannXi ρ ≠ 0) {s : ℂ}
    (hsclosed : s ∈ Metric.closedBall (0 : ℂ) R) (hsne : riemannXi s ≠ 0) :
    logDeriv riemannXi s - logDeriv riemannXi 0 =
      ((∑ᶠ u : ℂ,
            ((-MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) u : ℤ) : ℂ) *
              logDeriv (Complex.canonicalFactor R u) s) -
          (∑ᶠ u : ℂ,
            ((-MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) u : ℤ) : ℂ) *
              logDeriv (Complex.canonicalFactor R u) 0)) +
        (logDeriv g s - logDeriv g 0) := by
  have h0closed : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := by
    simp only [Metric.mem_closedBall, dist_self, hR.le]
  have h0ne : riemannXi 0 ≠ 0 := by
    rw [riemannXi_zero]
    norm_num only
  have heqs := ecanonicalDecomp_riemannXi_logDeriv_eq_at hR D hzf hsclosed hsne
  have heq0 := ecanonicalDecomp_riemannXi_logDeriv_eq_at hR D hzf h0closed h0ne
  rw [logDeriv_riemannXi_canonicalFactorProduct_eq_finsum_at hsclosed hsne] at heqs
  rw [logDeriv_riemannXi_canonicalFactorProduct_eq_finsum_at h0closed h0ne] at heq0
  linear_combination heqs - heq0

/-- Inside the open ball, xi's meromorphic divisor equals its analytic zero
multiplicity. This rewrites divisor sums using the zero-multiplicity API. -/
theorem divisor_riemannXi_ball_eq_zeroMultiplicity_of_mem_ball {R : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ Metric.ball (0 : ℂ) R) :
    MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) ρ =
      (riemannXiZeroMultiplicity ρ : ℤ) := by
  have hanalyticBall : AnalyticOnNhd ℂ riemannXi (Metric.ball (0 : ℂ) R) := fun z _ =>
    differentiable_riemannXi.analyticAt z
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hanalyticBall hρ]
  unfold riemannXiZeroMultiplicity
  rw [← Nat.cast_analyticOrderNatAt (riemannXi_analyticOrderAt_ne_top ρ)]
  simp only [ENat.map_natCast, WithTop.coe_natCast, WithTop.untop₀_natCast]

/-!
### Finite-radius errors without an auxiliary factor in the statement

Combine the zero-free factor's derivative variation with the centered identity
and the summed canonical correction. The resulting inequalities use only xi,
the radius, and truncated multiplicity sums.
-/

/-- The multiplicity-weighted number of xi zeros in `ball 0 R`, used to bound
finite-radius corrections. -/
noncomputable def riemannXiTruncatedMultiplicitySum (R : ℝ) : ℝ :=
  ∑ᶠ ρ : ℂ, if ‖ρ‖ < R then (riemannXiZeroMultiplicity ρ : ℝ) else 0

/-- The ball-divisor sum (real-cast) equals the truncated multiplicity mass. -/
theorem finsum_divisor_riemannXi_ball_eq_truncatedMultiplicitySum {R : ℝ} :
    (∑ᶠ ρ : ℂ, ((MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) ρ : ℤ) : ℝ)) =
      riemannXiTruncatedMultiplicitySum R := by
  unfold riemannXiTruncatedMultiplicitySum
  apply finsum_congr
  intro ρ
  by_cases hρ : ρ ∈ Metric.ball (0 : ℂ) R
  · rw [divisor_riemannXi_ball_eq_zeroMultiplicity_of_mem_ball hρ]
    have hρnorm : ‖ρ‖ < R := by rwa [Metric.mem_ball, dist_zero_right] at hρ
    rw [ite_eq_left hρnorm]
    push_cast
    ring
  · rw [(MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R)).apply_eq_zero_of_notMem hρ]
    have hρnorm : ¬‖ρ‖ < R := by rwa [Metric.mem_ball, dist_zero_right] at hρ
    rw [ite_eq_right hρnorm]
    simp only [Int.cast_zero]

/-- The genus-one sum at `s = 1`, truncated to the zeros of `ξ` inside `ball 0 R` (with
multiplicity). -/
noncomputable def riemannXiTruncatedGenusSumOne (R : ℝ) : ℂ :=
  ∑ᶠ ρ : ℂ,
    ((MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) ρ : ℤ) : ℂ) * (1 / (1 - ρ) + 1 / ρ)

/-- The genus-one sum `Σρ mρ*(1/(s-ρ)+1/ρ)` over xi zeros in `ball 0 R`.
Its finite support permits differentiation at zero. -/
noncomputable def riemannXiTruncatedGenusSum (R : ℝ) (s : ℂ) : ℂ :=
  ∑ᶠ ρ : ℂ,
    ((MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) ρ : ℤ) : ℂ) * (1 / (s - ρ) + 1 / ρ)

/-- The genus-one sum at `s = 0` vanishes pointwise (each summand is `m_ρ*(1/(-ρ)+1/ρ) = 0`,
using the `1/0 = 0` convention for `ρ = 0`, which never occurs since
`PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXi 0 ≠ 0`). -/
theorem riemannXiTruncatedGenusSum_zero (R : ℝ) : riemannXiTruncatedGenusSum R 0 = 0 := by
  unfold riemannXiTruncatedGenusSum
  have heq :
    ∀ ρ : ℂ,
      ((MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) ρ : ℤ) : ℂ) *
          (1 / ((0 : ℂ) - ρ) + 1 / ρ) =
        0 := by
    intro ρ
    by_cases hρ : ρ = 0
    · simp only [hρ, sub_self, div_zero, add_zero, mul_zero]
    · rw [show (1 : ℂ) / (0 - ρ) + 1 / ρ = 0 from by
          field_simp; ring,
        mul_zero]
  simp only [heq, finsum_zero]

/-- The finite canonical-correction sum at general `s` (`‖s‖ ≤ R/2`), summed via the triangle
inequality from the pointwise bound
(`PseudoPrime.AnalyticNumberTheory.General.norm_canonicalCorrection_le`). Generalizes
`PseudoPrime.AnalyticNumberTheory.RiemannXi.norm_riemannXiCanonicalCorrectionSum_one_le`
from `s = 1`. -/
theorem norm_riemannXiCanonicalCorrectionSum_le {R : ℝ} (hR : 2 < R) {s : ℂ} (hs : ‖s‖ ≤ R / 2) :
    ‖∑ᶠ ρ : ℂ,
          ((MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) ρ : ℤ) : ℂ) *
            ((starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * s) -
              (starRingEnd ℂ) ρ / (R : ℂ) ^ 2)‖ ≤
      2 * ‖s‖ / R ^ 2 * riemannXiTruncatedMultiplicitySum R := by
  have hR0 : (0 : ℝ) < R := by linarith
  have hanalyticBall : AnalyticOnNhd ℂ riemannXi (Metric.ball (0 : ℂ) R) := fun z _ =>
    differentiable_riemannXi.analyticAt z
  have hanalyticClosed : AnalyticOnNhd ℂ riemannXi (Metric.closedBall (0 : ℂ) R) := fun z _ =>
    differentiable_riemannXi.analyticAt z
  set Dv := MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) with hDv_def
  have hfin : (Function.support Dv).Finite :=
    hanalyticClosed.meromorphicOn.divisor_ball_support_finite
  have heq1 :
    (∑ᶠ ρ : ℂ,
        ((Dv ρ : ℤ) : ℂ) *
          ((starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * s) -
            (starRingEnd ℂ) ρ / (R : ℂ) ^ 2)) =
      ∑ ρ ∈ hfin.toFinset,
        ((Dv ρ : ℤ) : ℂ) *
          ((starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * s) -
            (starRingEnd ℂ) ρ / (R : ℂ) ^ 2) := by
    apply finsum_eq_sum_of_support_subset
    intro ρ hρ
    rw [Function.mem_support] at hρ
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    intro hDρ0; apply hρ; rw [hDρ0]; simp only [Int.cast_zero, zero_mul]
  rw [heq1]
  have hterm_le :
    ∀ ρ ∈ hfin.toFinset,
      ‖((Dv ρ : ℤ) : ℂ) *
            ((starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * s) -
              (starRingEnd ℂ) ρ / (R : ℂ) ^ 2)‖ ≤
        (Dv ρ : ℝ) * (2 * ‖s‖ / R ^ 2) := by
    intro ρ hρmem
    have hρball : ρ ∈ Metric.ball (0 : ℂ) R :=
      Dv.supportWithinDomain (by rwa [Set.Finite.mem_toFinset] at hρmem)
    have hρnorm : ‖ρ‖ < R := by rwa [Metric.mem_ball, dist_zero_right] at hρball
    have hcorr := General.norm_canonicalCorrection_le hρnorm hs
    have hDvnn : (0 : ℤ) ≤ Dv ρ := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalyticBall ρ
    rw [norm_mul,
      show ‖((Dv ρ : ℤ) : ℂ)‖ = (Dv ρ : ℝ) from by
        rw [Complex.norm_intCast]; exact_mod_cast abs_of_nonneg hDvnn]
    exact mul_le_mul_of_nonneg_left hcorr (by exact_mod_cast hDvnn)
  calc
    ‖∑ ρ ∈ hfin.toFinset,
            ((Dv ρ : ℤ) : ℂ) *
              ((starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * s) -
                (starRingEnd ℂ) ρ / (R : ℂ) ^ 2)‖ ≤
        ∑ ρ ∈ hfin.toFinset,
          ‖((Dv ρ : ℤ) : ℂ) *
              ((starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * s) -
                (starRingEnd ℂ) ρ / (R : ℂ) ^ 2)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ ρ ∈ hfin.toFinset, (Dv ρ : ℝ) * (2 * ‖s‖ / R ^ 2) := Finset.sum_le_sum hterm_le
    _ = (∑ ρ ∈ hfin.toFinset, (Dv ρ : ℝ)) * (2 * ‖s‖ / R ^ 2) := by rw [Finset.sum_mul]
    _ = riemannXiTruncatedMultiplicitySum R * (2 * ‖s‖ / R ^ 2) := by
      have hsum_eq :
        (∑ ρ ∈ hfin.toFinset, ((Dv ρ : ℤ) : ℝ)) = riemannXiTruncatedMultiplicitySum R := by
        rw [(finsum_eq_sum_of_support_subset (fun ρ => ((Dv ρ : ℤ) : ℝ))
              (by
                intro ρ hρ
                rw [Function.mem_support] at hρ
                rw [Set.Finite.coe_toFinset, Function.mem_support]
                intro hDρ0
                apply hρ
                rw [hDρ0]
                simp only [Int.cast_zero])).symm]
        exact finsum_divisor_riemannXi_ball_eq_truncatedMultiplicitySum
      rw [hsum_eq]
    _ = 2 * ‖s‖ / R ^ 2 * riemannXiTruncatedMultiplicitySum R := by ring

/-- At `s=1`, the canonical-correction sum is bounded by the pointwise correction
estimate and the truncated multiplicity mass, using nonnegativity of the divisor. -/
theorem norm_riemannXiCanonicalCorrectionSum_one_le {R : ℝ} (hR : 2 < R) :
    ‖∑ᶠ ρ : ℂ,
          ((MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) ρ : ℤ) : ℂ) *
            ((starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * 1) -
              (starRingEnd ℂ) ρ / (R : ℂ) ^ 2)‖ ≤
      2 / R ^ 2 * riemannXiTruncatedMultiplicitySum R := by
  have hR0 : (0 : ℝ) < R := by linarith
  have hs1 : ‖(1 : ℂ)‖ ≤ R / 2 := by
    rw [norm_one]; linarith
  have hanalyticBall : AnalyticOnNhd ℂ riemannXi (Metric.ball (0 : ℂ) R) := fun z _ =>
    differentiable_riemannXi.analyticAt z
  have hanalyticClosed : AnalyticOnNhd ℂ riemannXi (Metric.closedBall (0 : ℂ) R) := fun z _ =>
    differentiable_riemannXi.analyticAt z
  set Dv := MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) with hDv_def
  have hfin : (Function.support Dv).Finite :=
    hanalyticClosed.meromorphicOn.divisor_ball_support_finite
  have heq1 :
    (∑ᶠ ρ : ℂ,
        ((Dv ρ : ℤ) : ℂ) *
          ((starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * 1) -
            (starRingEnd ℂ) ρ / (R : ℂ) ^ 2)) =
      ∑ ρ ∈ hfin.toFinset,
        ((Dv ρ : ℤ) : ℂ) *
          ((starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * 1) -
            (starRingEnd ℂ) ρ / (R : ℂ) ^ 2) := by
    apply finsum_eq_sum_of_support_subset
    intro ρ hρ
    rw [Function.mem_support] at hρ
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    intro hDρ0; apply hρ; rw [hDρ0]; simp only [Int.cast_zero, zero_mul]
  rw [heq1]
  have hterm_le :
    ∀ ρ ∈ hfin.toFinset,
      ‖((Dv ρ : ℤ) : ℂ) *
            ((starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * 1) -
              (starRingEnd ℂ) ρ / (R : ℂ) ^ 2)‖ ≤
        (Dv ρ : ℝ) * (2 / R ^ 2) := by
    intro ρ hρmem
    have hρball : ρ ∈ Metric.ball (0 : ℂ) R :=
      Dv.supportWithinDomain (by rwa [Set.Finite.mem_toFinset] at hρmem)
    have hρnorm : ‖ρ‖ < R := by rwa [Metric.mem_ball, dist_zero_right] at hρball
    have hcorr := General.norm_canonicalCorrection_le hρnorm hs1
    have hDvnn : (0 : ℤ) ≤ Dv ρ := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalyticBall ρ
    rw [norm_mul,
      show ‖((Dv ρ : ℤ) : ℂ)‖ = (Dv ρ : ℝ) from by
        rw [Complex.norm_intCast]; exact_mod_cast abs_of_nonneg hDvnn]
    calc
      (Dv ρ : ℝ) *
            ‖(starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * 1) -
                (starRingEnd ℂ) ρ / (R : ℂ) ^ 2‖ ≤
          (Dv ρ : ℝ) * (2 * ‖(1 : ℂ)‖ / R ^ 2) :=
        mul_le_mul_of_nonneg_left hcorr (by exact_mod_cast hDvnn)
      _ = (Dv ρ : ℝ) * (2 / R ^ 2) := by
        rw [norm_one]; ring
  calc
    ‖∑ ρ ∈ hfin.toFinset,
            ((Dv ρ : ℤ) : ℂ) *
              ((starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * 1) -
                (starRingEnd ℂ) ρ / (R : ℂ) ^ 2)‖ ≤
        ∑ ρ ∈ hfin.toFinset,
          ‖((Dv ρ : ℤ) : ℂ) *
              ((starRingEnd ℂ) ρ / ((R : ℂ) ^ 2 - (starRingEnd ℂ) ρ * 1) -
                (starRingEnd ℂ) ρ / (R : ℂ) ^ 2)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ ρ ∈ hfin.toFinset, (Dv ρ : ℝ) * (2 / R ^ 2) := Finset.sum_le_sum hterm_le
    _ = (∑ ρ ∈ hfin.toFinset, (Dv ρ : ℝ)) * (2 / R ^ 2) := by rw [Finset.sum_mul]
    _ = riemannXiTruncatedMultiplicitySum R * (2 / R ^ 2) := by
      have hsum_eq :
        (∑ ρ ∈ hfin.toFinset, ((Dv ρ : ℤ) : ℝ)) = riemannXiTruncatedMultiplicitySum R := by
        rw [(finsum_eq_sum_of_support_subset (fun ρ => ((Dv ρ : ℤ) : ℝ))
              (by
                intro ρ hρ
                rw [Function.mem_support] at hρ
                rw [Set.Finite.coe_toFinset, Function.mem_support]
                intro hDρ0
                apply hρ
                rw [hDρ0]
                simp only [Int.cast_zero])).symm]
        exact finsum_divisor_riemannXi_ball_eq_truncatedMultiplicitySum
      rw [hsum_eq]
    _ = 2 / R ^ 2 * riemannXiTruncatedMultiplicitySum R := by ring

/-- For a zero-free radius `R > 2` and a nonzero xi value at `‖s‖ ≤ R/2`,
the centered logarithmic derivative differs from the truncated genus sum by
at most the zero-free-factor variation plus the canonical-correction bound. -/
theorem norm_riemannXi_centeredLogDeriv_sub_truncatedGenus_le {R : ℝ} (hR : 2 < R)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → riemannXi ρ ≠ 0) {s : ℂ} (hs : ‖s‖ ≤ R / 2) (hsne : riemannXi s ≠ 0) :
    ‖(logDeriv riemannXi s - logDeriv riemannXi 0) - riemannXiTruncatedGenusSum R s‖ ≤
      192 * ‖s‖ *
            (xiOrderOneGrowthConstant + 2 * (R + 4) * Real.log (R + 4) - Real.log ‖riemannXi 0‖ +
              1) /
          R ^ 2 +
        2 * ‖s‖ / R ^ 2 * riemannXiTruncatedMultiplicitySum R := by
  have hR0 : (0 : ℝ) < R := by linarith
  obtain ⟨g, D⟩ := exists_ecanonicalDecomp_riemannXi R
  have hsclosed : s ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_zero_right]; linarith
  have heq := ecanonicalDecomp_riemannXi_centered_logDeriv_eq hR0 D hzf hsclosed hsne
  have hanalyticClosed : AnalyticOnNhd ℂ riemannXi (Metric.closedBall (0 : ℂ) R) := fun z _ =>
    differentiable_riemannXi.analyticAt z
  set Dv := MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) with hDv_def
  have hfin : (Function.support Dv).Finite :=
    hanalyticClosed.meromorphicOn.divisor_ball_support_finite
  have h0ne : riemannXi (0 : ℂ) ≠ 0 := by
    rw [riemannXi_zero]; norm_num only
  have hkey : ∀ u ∈ hfin.toFinset, u ∈ Metric.ball (0 : ℂ) R ∧ u ≠ 0 ∧ s ≠ u := by
    intro u hu
    rw [Set.Finite.mem_toFinset] at hu
    refine ⟨Dv.supportWithinDomain hu, ?_, ?_⟩
    · exact ne_of_mem_divisorBallSupport_of_riemannXi_ne_zero hu h0ne
    · exact (ne_of_mem_divisorBallSupport_of_riemannXi_ne_zero hu hsne).symm
  have hsub1 :
    Function.support (fun u : ℂ => ((-Dv u : ℤ) : ℂ) * logDeriv (Complex.canonicalFactor R u) s) ⊆
      hfin.toFinset := by
    intro u hu
    rw [Function.mem_support] at hu
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    intro hDu0; apply hu; rw [hDu0]; simp only [Int.cast_zero, neg_zero, zero_mul]
  have hsub2 :
    Function.support
        (fun u : ℂ => ((-Dv u : ℤ) : ℂ) * logDeriv (Complex.canonicalFactor R u) (0 : ℂ)) ⊆
      hfin.toFinset := by
    intro u hu
    rw [Function.mem_support] at hu
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    intro hDu0; apply hu; rw [hDu0]; simp only [Int.cast_zero, neg_zero, zero_mul]
  have hcombine :
    (∑ᶠ u : ℂ, ((-Dv u : ℤ) : ℂ) * logDeriv (Complex.canonicalFactor R u) s) -
        (∑ᶠ u : ℂ, ((-Dv u : ℤ) : ℂ) * logDeriv (Complex.canonicalFactor R u) 0) =
      riemannXiTruncatedGenusSum R s +
        ∑ᶠ u : ℂ,
          ((Dv u : ℤ) : ℂ) *
            ((starRingEnd ℂ) u / ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * s) -
              (starRingEnd ℂ) u / (R : ℂ) ^ 2) := by
    rw [finsum_eq_sum_of_support_subset _ hsub1, finsum_eq_sum_of_support_subset _ hsub2, ←
      Finset.sum_sub_distrib]
    have hterm :
      ∀ u ∈ hfin.toFinset,
        ((-Dv u : ℤ) : ℂ) * logDeriv (Complex.canonicalFactor R u) s -
            ((-Dv u : ℤ) : ℂ) * logDeriv (Complex.canonicalFactor R u) 0 =
          ((Dv u : ℤ) : ℂ) * (1 / (s - u) + 1 / u) +
            ((Dv u : ℤ) : ℂ) *
              ((starRingEnd ℂ) u / ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * s) -
                (starRingEnd ℂ) u / (R : ℂ) ^ 2) := by
      intro u hu
      obtain ⟨huball, hune0, hsneu⟩ := hkey u hu
      rw [← mul_sub, General.centered_logDeriv_canonicalFactor huball hsclosed hsneu hune0]
      push_cast
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    congr 1
    · exact
        (finsum_eq_sum_of_support_subset _
            (by
              intro u hu
              rw [Function.mem_support] at hu
              rw [Set.Finite.coe_toFinset, Function.mem_support]
              intro hDu0
              apply hu
              rw [hDu0]
              simp only [Int.cast_zero, one_div, zero_mul])).symm
    · exact
        (finsum_eq_sum_of_support_subset _
            (by
              intro u hu
              rw [Function.mem_support] at hu
              rw [Set.Finite.coe_toFinset, Function.mem_support]
              intro hDu0
              apply hu
              rw [hDu0]
              simp only [Int.cast_zero, zero_mul])).symm
  rw [hcombine] at heq
  have hfinal :
    (logDeriv riemannXi s - logDeriv riemannXi 0) - riemannXiTruncatedGenusSum R s =
      (∑ᶠ u : ℂ,
          ((Dv u : ℤ) : ℂ) *
            ((starRingEnd ℂ) u / ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * s) -
              (starRingEnd ℂ) u / (R : ℂ) ^ 2)) +
        (logDeriv g s - logDeriv g 0) := by
    rw [heq]; ring
  rw [hfinal]
  refine (norm_add_le _ _).trans ?_
  rw [add_comm]
  exact
    add_le_add (norm_logDeriv_ecanonicalDecomp_riemannXi_sub_zero_le hR D hzf hs)
      (norm_riemannXiCanonicalCorrectionSum_le hR hs)

/-- At `s=1` and a zero-free radius `R > 2`, the centered logarithmic derivative
differs from the truncated genus sum by the sum of the two finite-radius error bounds. -/
theorem norm_riemannXi_centeredLogDeriv_one_sub_truncatedGenus_le {R : ℝ} (hR : 2 < R)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → riemannXi ρ ≠ 0) :
    ‖(logDeriv riemannXi 1 - logDeriv riemannXi 0) - riemannXiTruncatedGenusSumOne R‖ ≤
      192 *
            (xiOrderOneGrowthConstant + 2 * (R + 4) * Real.log (R + 4) - Real.log ‖riemannXi 0‖ +
              1) /
          R ^ 2 +
        2 / R ^ 2 * riemannXiTruncatedMultiplicitySum R := by
  have hR0 : (0 : ℝ) < R := by linarith
  obtain ⟨g, D⟩ := exists_ecanonicalDecomp_riemannXi R
  have hsclosed : (1 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_one]; linarith
  have hsne : riemannXi (1 : ℂ) ≠ 0 := by
    rw [riemannXi_one]; norm_num only
  have heq := ecanonicalDecomp_riemannXi_centered_logDeriv_eq hR0 D hzf hsclosed hsne
  have hanalyticClosed : AnalyticOnNhd ℂ riemannXi (Metric.closedBall (0 : ℂ) R) := fun z _ =>
    differentiable_riemannXi.analyticAt z
  set Dv := MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R) with hDv_def
  have hfin : (Function.support Dv).Finite :=
    hanalyticClosed.meromorphicOn.divisor_ball_support_finite
  have h0ne : riemannXi (0 : ℂ) ≠ 0 := by
    rw [riemannXi_zero]; norm_num only
  have hkey : ∀ u ∈ hfin.toFinset, u ∈ Metric.ball (0 : ℂ) R ∧ u ≠ 0 ∧ (1 : ℂ) ≠ u := by
    intro u hu
    rw [Set.Finite.mem_toFinset] at hu
    refine ⟨Dv.supportWithinDomain hu, ?_, ?_⟩
    · exact ne_of_mem_divisorBallSupport_of_riemannXi_ne_zero hu h0ne
    · exact (ne_of_mem_divisorBallSupport_of_riemannXi_ne_zero hu hsne).symm
  have hsub1 :
    Function.support (fun u : ℂ => ((-Dv u : ℤ) : ℂ) * logDeriv (Complex.canonicalFactor R u) 1) ⊆
      hfin.toFinset := by
    intro u hu
    rw [Function.mem_support] at hu
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    intro hDu0; apply hu; rw [hDu0]; simp only [Int.cast_zero, neg_zero, zero_mul]
  have hsub2 :
    Function.support
        (fun u : ℂ => ((-Dv u : ℤ) : ℂ) * logDeriv (Complex.canonicalFactor R u) (0 : ℂ)) ⊆
      hfin.toFinset := by
    intro u hu
    rw [Function.mem_support] at hu
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    intro hDu0; apply hu; rw [hDu0]; simp only [Int.cast_zero, neg_zero, zero_mul]
  have hcombine :
    (∑ᶠ u : ℂ, ((-Dv u : ℤ) : ℂ) * logDeriv (Complex.canonicalFactor R u) 1) -
        (∑ᶠ u : ℂ, ((-Dv u : ℤ) : ℂ) * logDeriv (Complex.canonicalFactor R u) 0) =
      riemannXiTruncatedGenusSumOne R +
        ∑ᶠ u : ℂ,
          ((Dv u : ℤ) : ℂ) *
            ((starRingEnd ℂ) u / ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * 1) -
              (starRingEnd ℂ) u / (R : ℂ) ^ 2) := by
    rw [finsum_eq_sum_of_support_subset _ hsub1, finsum_eq_sum_of_support_subset _ hsub2, ←
      Finset.sum_sub_distrib]
    have hterm :
      ∀ u ∈ hfin.toFinset,
        ((-Dv u : ℤ) : ℂ) * logDeriv (Complex.canonicalFactor R u) 1 -
            ((-Dv u : ℤ) : ℂ) * logDeriv (Complex.canonicalFactor R u) 0 =
          ((Dv u : ℤ) : ℂ) * (1 / (1 - u) + 1 / u) +
            ((Dv u : ℤ) : ℂ) *
              ((starRingEnd ℂ) u / ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * 1) -
                (starRingEnd ℂ) u / (R : ℂ) ^ 2) := by
      intro u hu
      obtain ⟨huball, hune0, hsneu⟩ := hkey u hu
      rw [← mul_sub, General.centered_logDeriv_canonicalFactor huball hsclosed hsneu hune0]
      push_cast
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    congr 1
    · exact
        (finsum_eq_sum_of_support_subset _
            (by
              intro u hu
              rw [Function.mem_support] at hu
              rw [Set.Finite.coe_toFinset, Function.mem_support]
              intro hDu0; apply hu; rw [hDu0]; simp only [Int.cast_zero, one_div, zero_mul])).symm
    · exact
        (finsum_eq_sum_of_support_subset _
            (by
              intro u hu
              rw [Function.mem_support] at hu
              rw [Set.Finite.coe_toFinset, Function.mem_support]
              intro hDu0; apply hu; rw [hDu0]; simp only [Int.cast_zero, mul_one, zero_mul])).symm
  rw [hcombine] at heq
  have hfinal :
    (logDeriv riemannXi 1 - logDeriv riemannXi 0) - riemannXiTruncatedGenusSumOne R =
      (∑ᶠ u : ℂ,
          ((Dv u : ℤ) : ℂ) *
            ((starRingEnd ℂ) u / ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * 1) -
              (starRingEnd ℂ) u / (R : ℂ) ^ 2)) +
        (logDeriv g 1 - logDeriv g 0) := by
    rw [heq]; ring
  rw [hfinal]
  refine (norm_add_le _ _).trans ?_
  rw [add_comm]
  exact
    add_le_add (norm_logDeriv_ecanonicalDecomp_riemannXi_one_sub_zero_le hR D hzf)
      (norm_riemannXiCanonicalCorrectionSum_one_le hR)

/-!
### The truncated multiplicity mass divided by the squared radius tends to zero
-/

/-- The truncated multiplicity finsum equals the corresponding tsum over the indicator function
(both reduce to the same finite sum over the zero-free-boundary ledger). -/
theorem riemannXiTruncatedMultiplicitySum_eq_tsum_indicator {R : ℝ} :
    riemannXiTruncatedMultiplicitySum R =
      ∑' ρ : ℂ, if ‖ρ‖ < R then (riemannXiZeroMultiplicity ρ : ℝ) else 0 := by
  unfold riemannXiTruncatedMultiplicitySum
  have hsub :
    Function.support (fun ρ : ℂ => if ‖ρ‖ < R then (riemannXiZeroMultiplicity ρ : ℝ) else 0) ⊆
      (riemannXiZerosInClosedBall R : Set ℂ) := by
    intro ρ hρ
    rw [Function.mem_support] at hρ
    by_cases hρnorm : ‖ρ‖ < R
    · rw [ite_eq_left hρnorm] at hρ
      have hne : riemannXiZeroMultiplicity ρ ≠ 0 := by exact_mod_cast hρ
      have hzero : riemannXi ρ = 0 := by
        by_contra hcon
        apply hne
        unfold riemannXiZeroMultiplicity analyticOrderNatAt
        rw [analyticOrderAt_eq_zero.mpr (Or.inr hcon)]
        rfl
      rw [Finset.mem_coe, mem_riemannXiZerosInClosedBall_iff]
      exact
        ⟨hzero, by
          rw [Metric.mem_closedBall, dist_zero_right]; linarith⟩
    · exact absurd (ite_eq_right hρnorm) hρ
  rw [finsum_eq_sum_of_support_subset _ hsub,
    tsum_eq_sum (s := riemannXiZerosInClosedBall R)
      (fun ρ hρ => Function.notMem_support.mp (fun hmem => hρ (hsub hmem)))]

/-- The truncated multiplicity mass divided by `R_n²` tends to zero along good
radii. Dominated convergence uses the summable radial multiplicity weight. -/
theorem tendsto_riemannXiGoodRadius_truncatedMultiplicity_div_sq :
    Filter.Tendsto
      (fun n : ℕ =>
        riemannXiTruncatedMultiplicitySum (riemannXiGoodRadius n) / (riemannXiGoodRadius n) ^ 2)
      Filter.atTop (nhds 0) := by
  have hmain :
    Filter.Tendsto
      (fun n : ℕ =>
        ∑' ρ : ℂ,
          (if ‖ρ‖ < riemannXiGoodRadius n then (riemannXiZeroMultiplicity ρ : ℝ) else 0) /
            (riemannXiGoodRadius n) ^ 2)
      Filter.atTop (nhds (∑' _ρ : ℂ, (0 : ℝ))) := by
    apply
      tendsto_tsum_of_dominated_convergence (bound := fun ρ =>
        2 * riemannXiZeroMultiplicityNormWeight ρ) (h_sum :=
        summable_riemannXiZeroMultiplicityNormWeight.mul_left 2)
    · intro ρ
      have hev : ∀ᶠ n : ℕ in Filter.atTop, ‖ρ‖ < riemannXiGoodRadius n :=
        tendsto_riemannXiGoodRadius_atTop.eventually_gt_atTop ‖ρ‖
      have hrsq :
        Filter.Tendsto (fun n : ℕ => (riemannXiGoodRadius n) ^ 2) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_mono (fun n => by nlinarith [riemannXiGoodRadius_gt_two n])
          tendsto_riemannXiGoodRadius_atTop
      have htend0 :
        Filter.Tendsto
          (fun n : ℕ => (riemannXiZeroMultiplicity ρ : ℝ) / (riemannXiGoodRadius n) ^ 2)
          Filter.atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop hrsq
      have heq :
        (fun n : ℕ =>
            (if ‖ρ‖ < riemannXiGoodRadius n then (riemannXiZeroMultiplicity ρ : ℝ) else 0) /
              (riemannXiGoodRadius n) ^ 2) =ᶠ[Filter.atTop]
          (fun n : ℕ => (riemannXiZeroMultiplicity ρ : ℝ) / (riemannXiGoodRadius n) ^ 2) := by
        filter_upwards [hev] with n hn
        rw [ite_eq_left hn]
      exact Filter.Tendsto.congr' heq.symm htend0
    · filter_upwards with n ρ
      by_cases hρnorm : ‖ρ‖ < riemannXiGoodRadius n
      · rw [ite_eq_left hρnorm]
        have hRgt2 := riemannXiGoodRadius_gt_two n
        have hRpos : (0 : ℝ) < riemannXiGoodRadius n := by linarith
        have hmnn : (0 : ℝ) ≤ (riemannXiZeroMultiplicity ρ : ℝ) := Nat.cast_nonneg _
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        unfold riemannXiZeroMultiplicityNormWeight
        by_cases hρzero : riemannXi ρ = 0
        · rw [ite_eq_left hρzero]
          have hρsq : ‖ρ‖ ^ 2 < (riemannXiGoodRadius n) ^ 2 :=
            pow_lt_pow_left₀ hρnorm (norm_nonneg ρ) two_ne_zero
          have hbound : 1 + ‖ρ‖ ^ 2 ≤ 2 * (riemannXiGoodRadius n) ^ 2 := by nlinarith [hρsq, hRgt2]
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_left hbound hmnn]
        · have hmzero : riemannXiZeroMultiplicity ρ = 0 := by
            unfold riemannXiZeroMultiplicity analyticOrderNatAt
            rw [analyticOrderAt_eq_zero.mpr (Or.inr hρzero)]
            rfl
          rw [hmzero]
          simp only [CharP.cast_eq_zero, zero_div, ite_self, mul_zero, Std.le_refl]
      · rw [ite_eq_right hρnorm]
        have : (0 : ℝ) ≤ riemannXiZeroMultiplicityNormWeight ρ := by
          unfold riemannXiZeroMultiplicityNormWeight
          split <;> positivity
        simp only [zero_div, norm_zero, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, this]
  simp only [tsum_zero] at hmain
  refine hmain.congr (fun n => ?_)
  rw [tsum_div_const, ← riemannXiTruncatedMultiplicitySum_eq_tsum_indicator]

/-!
### Decay of the finite-radius growth term

The elementary ratio `(R+4)*log(R+4)/R²` tends to zero.
-/

theorem tendsto_add_mul_log_div_sq_atTop_shift4 :
    Filter.Tendsto (fun R : ℝ => (R + 4) * Real.log (R + 4) / R ^ 2) Filter.atTop (nhds 0) := by
  have hlogdiv : Filter.Tendsto (fun t : ℝ => Real.log t / t) Filter.atTop (nhds 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (one_ne_zero)
    simpa only [pow_one, one_mul, add_zero] using h
  have ht : Filter.Tendsto (fun R : ℝ => R + 4) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop 4 Filter.tendsto_id
  have hcomp : Filter.Tendsto (fun R : ℝ => Real.log (R + 4) / (R + 4)) Filter.atTop (nhds 0) :=
    hlogdiv.comp ht
  have hratio1 : Filter.Tendsto (fun R : ℝ => (R + 4) / R) Filter.atTop (nhds 1) := by
    have hdiv4 : Filter.Tendsto (fun R : ℝ => (4 : ℝ) / R) Filter.atTop (nhds 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul (4 : ℝ)
    have hadd : Filter.Tendsto (fun R : ℝ => 1 + 4 / R) Filter.atTop (nhds 1) := by
      simpa only [add_zero] using tendsto_const_nhds.add hdiv4
    have heq2 : (fun R : ℝ => 1 + 4 / R) =ᶠ[Filter.atTop] (fun R : ℝ => (R + 4) / R) := by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
      have hRne : R ≠ 0 := hR.ne'
      field_simp
    exact hadd.congr' heq2
  have hratiosq : Filter.Tendsto (fun R : ℝ => ((R + 4) / R) ^ 2) Filter.atTop (nhds 1) := by
    have := hratio1.pow 2
    simpa only [one_pow] using this
  have hmul :
    Filter.Tendsto (fun R : ℝ => (Real.log (R + 4) / (R + 4)) * ((R + 4) / R) ^ 2) Filter.atTop
      (nhds 0) := by
    have := hcomp.mul hratiosq
    simpa only [mul_one] using this
  have heq1 :
    (fun R : ℝ => (R + 4) * Real.log (R + 4) / R ^ 2) =ᶠ[Filter.atTop]
      (fun R : ℝ => (Real.log (R + 4) / (R + 4)) * ((R + 4) / R) ^ 2) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
    have hRne : R ≠ 0 := hR.ne'
    have hR4ne : R + 4 ≠ 0 := by positivity
    field_simp
  exact hmul.congr' heq1.symm

/-- For fixed real constants `K1`, `K2`, and `c0`, the ratio
`K1*(K2*(R+4)*log(R+4)+c0)/R²` tends to zero as `R` tends to infinity. -/
theorem tendsto_const_mul_add_mul_log_add_const_div_sq_atTop_shift4 (K1 K2 c0 : ℝ) :
    Filter.Tendsto (fun R : ℝ => K1 * (K2 * (R + 4) * Real.log (R + 4) + c0) / R ^ 2) Filter.atTop
      (nhds 0) := by
  have hlog2 :
    Filter.Tendsto (fun R : ℝ => (R + 4) * Real.log (R + 4) / R ^ 2) Filter.atTop (nhds 0) :=
    tendsto_add_mul_log_div_sq_atTop_shift4
  have hinv2 : Filter.Tendsto (fun R : ℝ => (R ^ 2)⁻¹) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun R : ℝ => R ^ 2) Filter.atTop Filter.atTop :=
      Filter.tendsto_pow_atTop (two_ne_zero)
    exact tendsto_inv_atTop_zero.comp h1
  have hK1K2 :
    Filter.Tendsto (fun R : ℝ => (K1 * K2) * ((R + 4) * Real.log (R + 4) / R ^ 2)) Filter.atTop
      (nhds 0) := by
    have := hlog2.const_mul (K1 * K2)
    simpa only [mul_zero] using this
  have hconst : Filter.Tendsto (fun R : ℝ => (K1 * c0) * (R ^ 2)⁻¹) Filter.atTop (nhds 0) := by
    have := hinv2.const_mul (K1 * c0)
    simpa only [mul_zero] using this
  have hsum :
    Filter.Tendsto
      (fun R : ℝ => (K1 * K2) * ((R + 4) * Real.log (R + 4) / R ^ 2) + (K1 * c0) * (R ^ 2)⁻¹)
      Filter.atTop (nhds 0) := by
    have := hK1K2.add hconst
    simpa only [add_zero] using this
  refine hsum.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
  have hRne : R ≠ 0 := hR.ne'
  field_simp

/-- Along good radii, the difference between the centered logarithmic derivative
at one and the truncated genus sum tends to zero. Both the growth error and
the normalized truncated multiplicity mass vanish. -/
theorem tendsto_riemannXiGoodRadius_centeredLogDeriv_sub_truncatedGenus :
    Filter.Tendsto
      (fun n : ℕ =>
        (logDeriv riemannXi 1 - logDeriv riemannXi 0) -
          riemannXiTruncatedGenusSumOne (riemannXiGoodRadius n))
      Filter.atTop (nhds 0) := by
  have hH7 :
    Filter.Tendsto
      (fun n : ℕ =>
        192 *
            (xiOrderOneGrowthConstant +
                  2 * (riemannXiGoodRadius n + 4) * Real.log (riemannXiGoodRadius n + 4) -
                Real.log ‖riemannXi 0‖ +
              1) /
          (riemannXiGoodRadius n) ^ 2)
      Filter.atTop (nhds 0) := by
    have hcomp :=
      (tendsto_const_mul_add_mul_log_add_const_div_sq_atTop_shift4 192 2
            (xiOrderOneGrowthConstant - Real.log ‖riemannXi 0‖ + 1)).comp
        tendsto_riemannXiGoodRadius_atTop
    refine hcomp.congr (fun n => ?_)
    simp only [Function.comp_apply]
    ring_nf
  have hH8 := tendsto_riemannXiGoodRadius_truncatedMultiplicity_div_sq
  have hH8' :
    Filter.Tendsto
      (fun n : ℕ =>
        2 / (riemannXiGoodRadius n) ^ 2 * riemannXiTruncatedMultiplicitySum (riemannXiGoodRadius n))
      Filter.atTop (nhds 0) := by
    have hmul := hH8.const_mul (2 : ℝ)
    simp only [mul_zero] at hmul
    refine hmul.congr (fun n => ?_)
    ring
  have hsum :
    Filter.Tendsto
      (fun n : ℕ =>
        192 *
              (xiOrderOneGrowthConstant +
                    2 * (riemannXiGoodRadius n + 4) * Real.log (riemannXiGoodRadius n + 4) -
                  Real.log ‖riemannXi 0‖ +
                1) /
            (riemannXiGoodRadius n) ^ 2 +
          2 / (riemannXiGoodRadius n) ^ 2 *
            riemannXiTruncatedMultiplicitySum (riemannXiGoodRadius n))
      Filter.atTop (nhds 0) := by
    have := hH7.add hH8'
    simpa only [add_zero] using this
  have hbound :
    ∀ n : ℕ,
      ‖(logDeriv riemannXi 1 - logDeriv riemannXi 0) -
            riemannXiTruncatedGenusSumOne (riemannXiGoodRadius n)‖ ≤
        192 *
              (xiOrderOneGrowthConstant +
                    2 * (riemannXiGoodRadius n + 4) * Real.log (riemannXiGoodRadius n + 4) -
                  Real.log ‖riemannXi 0‖ +
                1) /
            (riemannXiGoodRadius n) ^ 2 +
          2 / (riemannXiGoodRadius n) ^ 2 *
            riemannXiTruncatedMultiplicitySum (riemannXiGoodRadius n) := by
    intro n
    exact
      norm_riemannXi_centeredLogDeriv_one_sub_truncatedGenus_le (riemannXiGoodRadius_gt_two n)
        (riemannXi_ne_zero_on_goodRadius n)
  exact squeeze_zero_norm hbound hsum

/-! ### RH, injected at the finite-sum level

Rather than build a generic (`s`-arbitrary, RH-free) global Hadamard identity and specialize to
RH afterwards, RH is injected directly into the *finite* truncated genus sum: every summand
`1/(1-ρ)+1/ρ` (for `ρ` an actual zero of `ξ`) collapses to `1/|ρ|²` since RH forces `1-ρ = ρ̄`.
This lets the rest of the argument use only the existing real-valued
`PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXiZeroMultiplicityNormWeight`
summability machinery, with no new complex-analytic content. -/

/-- **RH pointwise identity**: at a zero of `ξ`, the genus-one term collapses to the
inverse-norm-square term. `ρ ≠ 0` follows immediately from `ξ(0) = 1/2 ≠ 0`. -/
theorem riemannXi_genusOneTerm_eq_inv_normSq_of_riemannHypothesis (hRH : RiemannHypothesis) {ρ : ℂ}
    (hρ : riemannXi ρ = 0) : 1 / (1 - ρ) + 1 / ρ = ((Complex.normSq ρ)⁻¹ : ℝ) := by
  have hρ0 : ρ ≠ 0 := by
    intro h; rw [h, riemannXi_zero] at hρ; norm_num only at hρ
  have hre : ρ.re = 1 / 2 := riemannXi_zero_re_eq_half_of_riemannHypothesis hRH hρ
  have hone : (1 : ℂ) - ρ = starRingEnd ℂ ρ := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, hre, one_div, Complex.conj_re]
      norm_num only
    · simp only [Complex.sub_im, Complex.one_im, zero_sub, Complex.conj_im]
  have hρne : (starRingEnd ℂ) ρ ≠ 0 := by simpa only [ne_eq, map_eq_zero] using hρ0
  have hmul : (starRingEnd ℂ) ρ * ρ = (Complex.normSq ρ : ℂ) := by
    rw [mul_comm]; exact Complex.mul_conj ρ
  have hadd : ρ + (starRingEnd ℂ) ρ = 1 := by
    rw [Complex.add_conj, hre]
    push_cast
    norm_num only
  have hstep :
    (1 : ℂ) / (starRingEnd ℂ ρ) + 1 / ρ = (ρ + starRingEnd ℂ ρ) / (starRingEnd ℂ ρ * ρ) := by
    field_simp
  rw [hone, hstep, hadd, hmul]
  push_cast
  simp only [one_div]

/-- The truncated inverse-norm-square mass inside `ball 0 R`, the RH-side counterpart of
`PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXiTruncatedGenusSumOne`
(real-valued, no complex genus-one algebra). -/
noncomputable def riemannXiTruncatedInvNormSqSum (R : ℝ) : ℝ :=
  ∑ᶠ ρ : ℂ, if ‖ρ‖ < R then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0

/-- Under RH, the truncated genus sum equals the (complex-cast) truncated inverse-norm-square
sum: this severs the connection to Hadamard/`ECanonicalDecomp` machinery entirely. -/
theorem riemannXiTruncatedGenusSumOne_eq_invNormSq_of_riemannHypothesis (hRH : RiemannHypothesis)
    (R : ℝ) : riemannXiTruncatedGenusSumOne R = (riemannXiTruncatedInvNormSqSum R : ℂ) := by
  unfold riemannXiTruncatedGenusSumOne riemannXiTruncatedInvNormSqSum
  have hfin :
    (Function.support
        (fun ρ : ℂ =>
          if ‖ρ‖ < R then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0)).Finite := by
    apply Set.Finite.subset (riemannXiZerosInClosedBall R).finite_toSet
    intro ρ hρ
    rw [Function.mem_support] at hρ
    by_cases hρnorm : ‖ρ‖ < R
    · rw [ite_eq_left hρnorm] at hρ
      have hmne : riemannXiZeroMultiplicity ρ ≠ 0 := fun h =>
        hρ
          (by
            rw [h]; simp only [CharP.cast_eq_zero, zero_div])
      have hzero : riemannXi ρ = 0 := by
        by_contra hcon
        apply hmne
        unfold riemannXiZeroMultiplicity analyticOrderNatAt
        rw [analyticOrderAt_eq_zero.mpr (Or.inr hcon)]
        rfl
      rw [Finset.mem_coe, mem_riemannXiZerosInClosedBall_iff]
      exact
        ⟨hzero, by
          rw [Metric.mem_closedBall, dist_zero_right]; linarith⟩
    · exact absurd (ite_eq_right hρnorm) hρ
  rw [show
      ((∑ᶠ ρ : ℂ, if ‖ρ‖ < R then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0 : ℝ) :
          ℂ) =
        ∑ᶠ ρ : ℂ,
          ((if ‖ρ‖ < R then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0 : ℝ) : ℂ)
      from Complex.ofRealHom.toAddMonoidHom.map_finsum hfin]
  apply finsum_congr
  intro ρ
  by_cases hρball : ρ ∈ Metric.ball (0 : ℂ) R
  · have hρnorm : ‖ρ‖ < R := by rwa [Metric.mem_ball, dist_zero_right] at hρball
    rw [divisor_riemannXi_ball_eq_zeroMultiplicity_of_mem_ball hρball, ite_eq_left hρnorm]
    by_cases hmult : riemannXiZeroMultiplicity ρ = 0
    · simp only [hmult, CharP.cast_eq_zero, Int.cast_zero, one_div, zero_mul, zero_div,
        Complex.ofReal_zero]
    · have hρzero : riemannXi ρ = 0 := by
        by_contra hcon
        apply hmult
        unfold riemannXiZeroMultiplicity analyticOrderNatAt
        rw [analyticOrderAt_eq_zero.mpr (Or.inr hcon)]
        rfl
      rw [riemannXi_genusOneTerm_eq_inv_normSq_of_riemannHypothesis hRH hρzero]
      push_cast
      ring
  · have hρnorm : ¬‖ρ‖ < R := by rwa [Metric.mem_ball, dist_zero_right] at hρball
    rw [(MeromorphicOn.divisor riemannXi (Metric.ball (0 : ℂ) R)).apply_eq_zero_of_notMem hρball,
      ite_eq_right hρnorm]
    simp only [Int.cast_zero, one_div, zero_mul, Complex.ofReal_zero]

/-- **Inverse-norm-square summability under RH**: `m_ρ/|ρ|²` (over zeros of `ξ`) is summable,
via comparison with the existing
`PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXiZeroMultiplicityNormWeight` (`RH` zeros satisfy
`|ρ|² ≥ 1/4`, so `1 + |ρ|² ≤ 5|ρ|²`). -/
theorem summable_riemannXiZeroMultiplicityInvNormSq_of_riemannHypothesis (hRH : RiemannHypothesis) :
    Summable
      (fun ρ : ℂ =>
        if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0) := by
  refine
    Summable.of_nonneg_of_le
      (fun ρ => by
        split <;> [exact div_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _); exact le_refl 0])
      ?_ (summable_riemannXiZeroMultiplicityNormWeight.mul_left 5)
  · intro ρ
    unfold riemannXiZeroMultiplicityNormWeight
    by_cases hρ : riemannXi ρ = 0
    · rw [ite_eq_left hρ, ite_eq_left hρ]
      have hnsq : Complex.normSq ρ = ‖ρ‖ ^ 2 := Complex.normSq_eq_norm_sq ρ
      have hquarter : (1 : ℝ) / 4 ≤ ‖ρ‖ ^ 2 :=
        (norm_sq_riemannXi_zero_eq_quarter_add_im_sq_of_riemannHypothesis hRH hρ) ▸
          (by nlinarith [sq_nonneg ρ.im])
      have hmnn : (0 : ℝ) ≤ (riemannXiZeroMultiplicity ρ : ℝ) := Nat.cast_nonneg _
      have h1 : (1 : ℝ) + ‖ρ‖ ^ 2 ≤ 5 * ‖ρ‖ ^ 2 := by nlinarith [hquarter]
      rw [hnsq,
        show
          (5 : ℝ) * ((riemannXiZeroMultiplicity ρ : ℝ) / (1 + ‖ρ‖ ^ 2)) =
            (5 * (riemannXiZeroMultiplicity ρ : ℝ)) / (1 + ‖ρ‖ ^ 2)
          from by ring,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left h1 hmnn]
    · rw [ite_eq_right hρ, ite_eq_right hρ]; norm_num only

/-- The truncated inverse-norm-square sum tends to the global `tsum` as `R → ∞`, via Tannery's
theorem with the RH summability above as majorant. -/
theorem tendsto_riemannXiTruncatedInvNormSqSum_atTop (hRH : RiemannHypothesis) :
    Filter.Tendsto riemannXiTruncatedInvNormSqSum Filter.atTop
      (nhds
        (∑' ρ : ℂ,
          if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ
          else 0)) := by
  have hsummable := summable_riemannXiZeroMultiplicityInvNormSq_of_riemannHypothesis hRH
  have hmain :
    Filter.Tendsto
      (fun R : ℝ =>
        ∑' ρ : ℂ,
          if ‖ρ‖ < R then
            (if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0)
          else 0)
      Filter.atTop
      (nhds
        (∑' ρ : ℂ,
          if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ
          else 0)) := by
    apply
      tendsto_tsum_of_dominated_convergence (bound := fun ρ =>
        if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0)
        (h_sum := hsummable)
    · intro ρ
      have hev : ∀ᶠ R : ℝ in Filter.atTop, ‖ρ‖ < R := Filter.eventually_gt_atTop ‖ρ‖
      have heq :
        (fun R : ℝ =>
            if ‖ρ‖ < R then
              (if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0)
            else 0) =ᶠ[Filter.atTop]
          (fun _ : ℝ =>
            if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ
            else 0) := by
        filter_upwards [hev] with R hn
        rw [ite_eq_left hn]
      exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds
    · filter_upwards with R ρ
      by_cases hρnorm : ‖ρ‖ < R
      · rw [ite_eq_left hρnorm]
        by_cases hρzero : riemannXi ρ = 0
        · rw [ite_eq_left hρzero]
          have hquarter : (1 : ℝ) / 4 ≤ Complex.normSq ρ := by
            rw [Complex.normSq_eq_norm_sq,
              norm_sq_riemannXi_zero_eq_quarter_add_im_sq_of_riemannHypothesis hRH hρzero]
            nlinarith [sq_nonneg ρ.im]
          have hmnn : (0 : ℝ) ≤ (riemannXiZeroMultiplicity ρ : ℝ) := Nat.cast_nonneg _
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        · rw [ite_eq_right hρzero, norm_zero]
      · rw [ite_eq_right hρnorm, norm_zero]
        split
        · exact div_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
        · exact le_refl 0
  refine hmain.congr (fun R => ?_)
  unfold riemannXiTruncatedInvNormSqSum
  have hpteq :
    ∀ ρ : ℂ,
      (if ‖ρ‖ < R then
          (if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0)
        else 0) =
        (if ‖ρ‖ < R then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0) := by
    intro ρ
    by_cases hn : ‖ρ‖ < R
    · rw [ite_eq_left hn, ite_eq_left hn]
      by_cases hz : riemannXi ρ = 0
      · rw [ite_eq_left hz]
      · rw [ite_eq_right hz]
        have hmz : riemannXiZeroMultiplicity ρ = 0 := by
          unfold riemannXiZeroMultiplicity analyticOrderNatAt
          rw [analyticOrderAt_eq_zero.mpr (Or.inr hz)]
          rfl
        rw [hmz]
        simp only [Nat.cast_zero, zero_div]
    · rw [ite_eq_right hn, ite_eq_right hn]
  simp_rw [hpteq]
  rw [(finsum_eq_sum_of_support_subset
      (fun ρ : ℂ => if ‖ρ‖ < R then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0)
      (show
        Function.support
            (fun ρ : ℂ =>
              if ‖ρ‖ < R then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0) ⊆
          (riemannXiZerosInClosedBall R : Set ℂ)
        from by
        intro ρ hρ
        rw [Function.mem_support] at hρ
        by_cases hρnorm : ‖ρ‖ < R
        · rw [ite_eq_left hρnorm] at hρ
          have hmne : riemannXiZeroMultiplicity ρ ≠ 0 := by
            intro h; apply hρ; rw [h]; simp only [Nat.cast_zero, zero_div]
          have hzero : riemannXi ρ = 0 := by
            by_contra hcon
            apply hmne
            unfold riemannXiZeroMultiplicity analyticOrderNatAt
            rw [analyticOrderAt_eq_zero.mpr (Or.inr hcon)]
            rfl
          rw [Finset.mem_coe, mem_riemannXiZerosInClosedBall_iff]
          exact
            ⟨hzero, by
              rw [Metric.mem_closedBall, dist_zero_right]; linarith⟩
        · exact absurd (ite_eq_right hρnorm) hρ))]
  apply tsum_eq_sum
  intro ρ hρ
  by_cases hρnorm : ‖ρ‖ < R
  · rw [ite_eq_left hρnorm]
    by_cases hz : riemannXi ρ = 0
    · exfalso
      apply hρ
      rw [mem_riemannXiZerosInClosedBall_iff]
      exact
        ⟨hz, by
          rw [Metric.mem_closedBall, dist_zero_right]; linarith⟩
    · have hmz : riemannXiZeroMultiplicity ρ = 0 := by
        unfold riemannXiZeroMultiplicity analyticOrderNatAt
        rw [analyticOrderAt_eq_zero.mpr (Or.inr hz)]
        rfl
      rw [hmz]
      simp only [Nat.cast_zero, zero_div]
  · rw [ite_eq_right hρnorm]

/-- Good-radius specialization of
`PseudoPrime.AnalyticNumberTheory.RiemannXi.tendsto_riemannXiTruncatedInvNormSqSum_atTop`. -/
theorem tendsto_riemannXiGoodRadius_truncatedInvNormSqSum (hRH : RiemannHypothesis) :
    Filter.Tendsto (fun n : ℕ => riemannXiTruncatedInvNormSqSum (riemannXiGoodRadius n))
      Filter.atTop
      (nhds
        (∑' ρ : ℂ,
          if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0)) :=
  (tendsto_riemannXiTruncatedInvNormSqSum_atTop hRH).comp tendsto_riemannXiGoodRadius_atTop

/-- Under RH, the centered logarithmic derivative of xi at one equals the
global multiplicity-weighted inverse-square zero mass. Rewrite the finite genus
sum using RH and identify the limits by uniqueness. -/
theorem riemannXi_centeredLogDeriv_one_eq_tsum_invNormSq_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    logDeriv riemannXi 1 - logDeriv riemannXi 0 =
      ((∑' ρ : ℂ,
            if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0 :
          ℝ) :
        ℂ) := by
  have h1 := tendsto_riemannXiGoodRadius_centeredLogDeriv_sub_truncatedGenus
  have h2 :
    Filter.Tendsto (fun n : ℕ => riemannXiTruncatedGenusSumOne (riemannXiGoodRadius n)) Filter.atTop
      (nhds
        ((∑' ρ : ℂ,
              if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ else 0 :
            ℝ) :
          ℂ)) := by
    have h3 :=
      (Complex.continuous_ofReal.tendsto _).comp
        (tendsto_riemannXiGoodRadius_truncatedInvNormSqSum hRH)
    refine h3.congr (fun n => ?_)
    exact
      (riemannXiTruncatedGenusSumOne_eq_invNormSq_of_riemannHypothesis hRH
          (riemannXiGoodRadius n)).symm
  have h4 :
    Filter.Tendsto
      (fun n : ℕ =>
        (logDeriv riemannXi 1 - logDeriv riemannXi 0) -
            riemannXiTruncatedGenusSumOne (riemannXiGoodRadius n) +
          riemannXiTruncatedGenusSumOne (riemannXiGoodRadius n))
      Filter.atTop
      (nhds
        (0 +
          ((∑' ρ : ℂ,
                if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ
                else 0 :
              ℝ) :
            ℂ))) :=
    h1.add h2
  simp only [sub_add_cancel, zero_add] at h4
  exact tendsto_nhds_unique tendsto_const_nhds h4

/-- The functional equation gives `logDeriv riemannXi 1 = -logDeriv riemannXi 0`.
Differentiate `ξ(1-s)=ξ(s)` at zero and use `ξ(0)=ξ(1)=1/2`.
Consequently the centered value at one is `2*logDeriv ξ 1 = -2*logDeriv ξ 0`. -/
theorem logDeriv_riemannXi_one_eq_neg_zero : logDeriv riemannXi 1 = -logDeriv riemannXi 0 := by
  have hg : HasDerivAt (fun s : ℂ => (1 : ℂ) - s) (-1) 0 := (hasDerivAt_id (0 : ℂ)).const_sub 1
  have hf : HasDerivAt riemannXi (deriv riemannXi (1 - (0 : ℂ))) (1 - (0 : ℂ)) :=
    (differentiable_riemannXi (1 - 0)).hasDerivAt
  have hcomp :
    HasDerivAt (fun s : ℂ => riemannXi (1 - s)) (deriv riemannXi (1 - (0 : ℂ)) * (-1)) 0 :=
    hf.comp 0 hg
  have heq : (fun s : ℂ => riemannXi (1 - s)) = riemannXi := funext riemannXi_one_sub
  rw [heq] at hcomp
  have hderiv0 : deriv riemannXi 0 = deriv riemannXi 1 * (-1) := by
    have hsub : (1 : ℂ) - 0 = 1 := by ring
    rw [hsub] at hcomp
    exact hcomp.deriv
  simp only [logDeriv, Pi.div_apply]
  rw [riemannXi_zero, riemannXi_one, hderiv0]
  ring

/-- `logDeriv PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXi` is analytic
(hence differentiable) at `0`, since `PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXi`
is entire and `PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXi 0 ≠ 0`. -/
theorem analyticAt_logDeriv_riemannXi_zero : AnalyticAt ℂ (logDeriv riemannXi) 0 := by
  rw [logDeriv]
  have h0ne : riemannXi 0 ≠ 0 := by
    rw [riemannXi_zero]; norm_num only
  exact
    (differentiable_riemannXi.analyticAt 0).deriv.div (differentiable_riemannXi.analyticAt 0) h0ne

theorem differentiableAt_logDeriv_riemannXi_zero : DifferentiableAt ℂ (logDeriv riemannXi) 0 :=
  analyticAt_logDeriv_riemannXi_zero.differentiableAt

/-- The finite-radius slope-error coefficient for
`Q_R(s) = logDeriv ξ s - logDeriv ξ 0 - riemannXiTruncatedGenusSum R s`.
At an admissible zero-free radius it bounds `‖Q_R(s)‖` by this coefficient times `‖s‖`. -/
noncomputable def riemannXiH9eSlopeError (R : ℝ) : ℝ :=
  192 * (xiOrderOneGrowthConstant + 2 * (R + 4) * Real.log (R + 4) - Real.log ‖riemannXi 0‖ + 1) /
      R ^ 2 +
    2 / R ^ 2 * riemannXiTruncatedMultiplicitySum R

/-- The slope-error coefficient tends to zero along good radii, by decay of
the logarithmic growth ratio and the normalized truncated multiplicity mass. -/
theorem tendsto_riemannXiGoodRadius_H9eSlopeError_atTop :
    Filter.Tendsto (fun n : ℕ => riemannXiH9eSlopeError (riemannXiGoodRadius n)) Filter.atTop
      (nhds 0) := by
  have hH7 :
    Filter.Tendsto
      (fun n : ℕ =>
        192 *
            (xiOrderOneGrowthConstant +
                  2 * (riemannXiGoodRadius n + 4) * Real.log (riemannXiGoodRadius n + 4) -
                Real.log ‖riemannXi 0‖ +
              1) /
          (riemannXiGoodRadius n) ^ 2)
      Filter.atTop (nhds 0) := by
    have hcomp :=
      (tendsto_const_mul_add_mul_log_add_const_div_sq_atTop_shift4 192 2
            (xiOrderOneGrowthConstant - Real.log ‖riemannXi 0‖ + 1)).comp
        tendsto_riemannXiGoodRadius_atTop
    refine hcomp.congr (fun n => ?_)
    simp only [Function.comp_apply]
    ring_nf
  have hH8 := tendsto_riemannXiGoodRadius_truncatedMultiplicity_div_sq
  have hH8' :
    Filter.Tendsto
      (fun n : ℕ =>
        2 / (riemannXiGoodRadius n) ^ 2 * riemannXiTruncatedMultiplicitySum (riemannXiGoodRadius n))
      Filter.atTop (nhds 0) := by
    have hmul := hH8.const_mul (2 : ℝ)
    simp only [mul_zero] at hmul
    refine hmul.congr (fun n => ?_)
    ring
  have hsum := hH7.add hH8'
  simp only [add_zero] at hsum
  refine hsum.congr (fun n => ?_)
  unfold riemannXiH9eSlopeError
  ring

/-- If a function has derivative `D` at zero, vanishes there, and locally satisfies
`‖f s‖ ≤ C*‖s‖`, then `‖D‖ ≤ C`. This is a general derivative estimate. -/
theorem norm_deriv_le_of_eventually_norm_le_mul_norm {f : ℂ → ℂ} {D : ℂ} {C : ℝ}
    (hf : HasDerivAt f D 0) (hf0 : f 0 = 0)
    (hbound : ∀ᶠ s : ℂ in nhdsWithin 0 ({0}ᶜ : Set ℂ), ‖f s‖ ≤ C * ‖s‖) : ‖D‖ ≤ C := by
  have htend := hf.tendsto_slope
  have htendNorm := (continuous_norm.tendsto D).comp htend
  have hev : ∀ᶠ s : ℂ in nhdsWithin 0 ({0}ᶜ : Set ℂ), ‖slope f 0 s‖ ≤ C := by
    filter_upwards [hbound, self_mem_nhdsWithin] with s hs hsne
    have hsne' : s ≠ 0 := hsne
    rw [slope_def_module, norm_smul]
    have hnorm_inv : ‖(s - 0)⁻¹‖ = ‖s‖⁻¹ := by rw [sub_zero, norm_inv]
    rw [hnorm_inv, hf0, sub_zero]
    have hsnorm_pos : (0 : ℝ) < ‖s‖ := norm_pos_iff.mpr hsne'
    calc
      ‖s‖⁻¹ * ‖f s‖ ≤ ‖s‖⁻¹ * (C * ‖s‖) :=
        mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hsnorm_pos.le)
      _ = C := by field_simp
  exact le_of_tendsto htendNorm hev

/-- The centered logarithmic derivative minus the truncated genus sum vanishes
at zero and satisfies the finite-radius slope bound nearby. Applying the local
derivative estimate bounds the difference of their derivatives at zero. -/
theorem norm_deriv_logDeriv_riemannXi_zero_sub_le {R : ℝ} (hR : 2 < R)
    (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → riemannXi ρ ≠ 0) {D : ℂ}
    (hD : HasDerivAt (riemannXiTruncatedGenusSum R) D 0) :
    ‖deriv (logDeriv riemannXi) 0 - D‖ ≤ riemannXiH9eSlopeError R := by
  have h0ne : riemannXi (0 : ℂ) ≠ 0 := by
    rw [riemannXi_zero]; norm_num only
  have hLogHasDeriv : HasDerivAt (logDeriv riemannXi) (deriv (logDeriv riemannXi) 0) 0 :=
    differentiableAt_logDeriv_riemannXi_zero.hasDerivAt
  have hQ :
    HasDerivAt
      (fun s : ℂ => (logDeriv riemannXi s - logDeriv riemannXi 0) - riemannXiTruncatedGenusSum R s)
      (deriv (logDeriv riemannXi) 0 - D) 0 :=
    (hLogHasDeriv.sub_const _).sub hD
  have hQ0 :
    (logDeriv riemannXi 0 - logDeriv riemannXi 0) - riemannXiTruncatedGenusSum R 0 = 0 := by
    rw [sub_self, riemannXiTruncatedGenusSum_zero, zero_sub, neg_zero]
  have hRpos : (0 : ℝ) < R := by linarith
  have hev : ∀ᶠ s : ℂ in nhds (0 : ℂ), ‖s‖ ≤ R / 2 ∧ riemannXi s ≠ 0 := by
    have h1 : ∀ᶠ s : ℂ in nhds (0 : ℂ), ‖s‖ ≤ R / 2 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (show (0 : ℝ) < R / 2 by linarith)] with s hs
      rw [Metric.mem_ball, dist_zero_right] at hs
      exact hs.le
    have h2 : ∀ᶠ s : ℂ in nhds (0 : ℂ), riemannXi s ≠ 0 :=
      (differentiable_riemannXi.continuous.continuousAt).eventually_ne h0ne
    filter_upwards [h1, h2] with s hs1 hs2 using ⟨hs1, hs2⟩
  have hbound :
    ∀ᶠ s : ℂ in nhdsWithin 0 ({0}ᶜ : Set ℂ),
      ‖(logDeriv riemannXi s - logDeriv riemannXi 0) - riemannXiTruncatedGenusSum R s‖ ≤
        riemannXiH9eSlopeError R * ‖s‖ := by
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with s hs
    have h9e := norm_riemannXi_centeredLogDeriv_sub_truncatedGenus_le hR hzf hs.1 hs.2
    have hfactor :
      192 * ‖s‖ *
              (xiOrderOneGrowthConstant + 2 * (R + 4) * Real.log (R + 4) - Real.log ‖riemannXi 0‖ +
                1) /
            R ^ 2 +
          2 * ‖s‖ / R ^ 2 * riemannXiTruncatedMultiplicitySum R =
        riemannXiH9eSlopeError R * ‖s‖ := by
      unfold riemannXiH9eSlopeError; ring
    rwa [hfactor] at h9e
  exact norm_deriv_le_of_eventually_norm_le_mul_norm hQ hQ0 hbound

/-- `Γ` differentiates to `Γ * digamma` at every point avoiding the nonpositive integers. -/
theorem hasDerivAt_Gamma_mul_digamma {w : ℂ} (hw : ∀ m : ℕ, w ≠ -m) :
    HasDerivAt Complex.Gamma (Complex.Gamma w * Complex.digamma w) w := by
  have hGne : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hw
  have heqg : Complex.Gamma w * Complex.digamma w = deriv Complex.Gamma w := by
    rw [Complex.digamma_def, logDeriv_apply]
    field_simp [hGne]
  rw [heqg]
  exact (Complex.differentiableAt_Gamma w hw).hasDerivAt

/-- `Γ(z/2+1)` differentiates to `Γ(z0/2+1) * digamma(z0/2+1) / 2` at every `z0` whose image
`z0/2+1` avoids the nonpositive integers. -/
theorem hasDerivAt_Gamma_affine_half {z0 : ℂ} (hz0 : ∀ m : ℕ, z0 / 2 + 1 ≠ -m) :
    HasDerivAt (fun z : ℂ => Complex.Gamma (z / 2 + 1))
      (Complex.Gamma (z0 / 2 + 1) * Complex.digamma (z0 / 2 + 1) * (1 / 2)) z0 := by
  have haffine : HasDerivAt (fun z : ℂ => z / 2 + 1) (1 / 2 : ℂ) z0 := by
    have h1 : HasDerivAt (fun z : ℂ => z / 2) (1 / 2 : ℂ) z0 := by
      simpa only [one_div, id_eq] using (hasDerivAt_id z0).div_const 2
    simpa only [one_div, hasDerivAt_add_const_iff] using h1.add_const 1
  have hraw := HasDerivAt.comp_of_eq z0 (hasDerivAt_Gamma_mul_digamma hz0) haffine rfl
  convert hraw using 1
  rfl

/-- `ζ` is analytic at `0` (away from its only pole at `1`). -/
theorem analyticAt_riemannZeta_zero : AnalyticAt ℂ riemannZeta 0 :=
  analyticOn_riemannZeta 0
    (by simp only [Set.mem_compl_iff, Set.mem_singleton_iff, zero_ne_one, not_false_eq_true])

/-- `logDeriv ζ` is analytic (hence differentiable) at `0`, since `ζ` is analytic and nonzero
there. -/
theorem analyticAt_logDeriv_riemannZeta_zero : AnalyticAt ℂ (logDeriv riemannZeta) 0 := by
  rw [logDeriv]
  have hne : riemannZeta 0 ≠ 0 := by
    rw [riemannZeta_zero]; norm_num only
  exact analyticAt_riemannZeta_zero.deriv.div analyticAt_riemannZeta_zero hne

theorem differentiableAt_logDeriv_riemannZeta_zero : DifferentiableAt ℂ (logDeriv riemannZeta) 0 :=
  analyticAt_logDeriv_riemannZeta_zero.differentiableAt

/-- The known value of `logDeriv riemannZeta` at `0`, computed directly from mathlib's
`deriv_riemannZeta_zero : deriv riemannZeta 0 = -log(2π)/2` and `riemannZeta_zero : ζ 0 = -1/2`. -/
theorem logDeriv_riemannZeta_zero : logDeriv riemannZeta 0 = Complex.log (2 * Real.pi) := by
  rw [logDeriv_apply, deriv_riemannZeta_zero, riemannZeta_zero]
  ring

/-- The constant `deriv (logDeriv riemannZeta) 0`, retained symbolically in
residue formulas; its real part is bounded using the xi/zeta derivative comparison. -/
noncomputable def qMinusOneRiemannZetaSecondLogDerivAtZero : ℂ :=
  deriv (logDeriv riemannZeta) 0

end PseudoPrime.AnalyticNumberTheory.RiemannXi
