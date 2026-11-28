/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentIntegral656
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalLimit644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalLimit644
import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedSummationByParts
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExponentialLogWeightedSummation
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.IntegratedLogSplit
import PseudoPrime.LLS.RiemannWeightedErrorBounds
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentIntegral656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterKernel656
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterBoundary656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseRows644

/-! # Convergence of the principal zero contribution in section 132 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The centered Abel action for the section 132 weight, evaluated at a
physical cutoff `X ≥ 1`. The terms at `X` and at one retain the endpoint
values of the input `F` after integration by parts. -/
noncomputable def quarterAbelAction656 (X : ℝ) (F : ℝ → ℝ) : ℝ :=
  let P := fun t ↦ t * deriv (quarterWeight656 X) t
  4 * (∫ t in (1 : ℝ)..X, F t * deriv P t) -
      (∫ t in (1 : ℝ)..X * Real.exp (21 / 8), F t * deriv P t) -
      4 * P X * F X +
    3 * P 1 * F 1

private theorem abel_deriv_continuous_656 {X b : ℝ} (hX : 0 < X) :
    ContinuousOn (deriv (fun t ↦ t * deriv (quarterWeight656 X) t)) (Set.Icc 1 b) := by
  have hp : ContDiffOn ℝ 1 (fun t ↦ t * deriv (quarterWeight656 X) t) (Set.Ioi 0) :=
    contDiffOn_id.mul ((weight_smooth_656 hX).deriv_of_isOpen (m := 1) isOpen_Ioi (by decide))
  exact
    (hp.continuousOn_deriv_of_isOpen isOpen_Ioi (by decide)).mono
      (fun _ ht ↦ zero_lt_one.trans_le ht.1)

/-- At a physical cutoff `X ≥ 1`, the centered section 132 Abel actions of
the rectangular zero ledgers converge to the action of the full logarithmic
zero sum. The weighted integrals and the two endpoint values converge
separately. -/
theorem quarter_zero_abel_limit_656 {X : ℝ} (hX : 1 ≤ X) :
    Filter.Tendsto (fun k ↦ quarterAbelAction656 X (quarterZeroLedger644 k)) Filter.atTop
      (nhds
        (quarterAbelAction656 X
          (fun t ↦
            (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re))) := by
  have hx := zero_lt_one.trans_le hX
  have hb : X ≤ X * Real.exp (21 / 8) :=
    le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only))
  have hi :=
    AnalyticNumberTheory.RiemannZeta.weighted_zero_integral_limit le_rfl hX
      (abel_deriv_continuous_656 hx)
  have ho :=
    AnalyticNumberTheory.RiemannZeta.weighted_zero_integral_limit le_rfl (hX.trans hb)
      (abel_deriv_continuous_656 hx)
  have hcut :=
    (Complex.continuous_re.tendsto _).comp
      (AnalyticNumberTheory.RiemannZeta.log_zero_tsum_limit_closed hX)
  have hone :=
    (Complex.continuous_re.tendsto _).comp
      (AnalyticNumberTheory.RiemannZeta.log_zero_tsum_limit_closed (le_refl (1 : ℝ)))
  exact (((hi.const_mul 4).sub ho).sub (hcut.const_mul _)).add (hone.const_mul _)

/-- An eventual lower bound for the physical Abel actions of the rectangular
zero ledgers yields the same lower bound for the full principal zero term.
This is the limit step after including the physical cutoff correction. -/
theorem quarter_zero_abel_lower_656 {X B : ℝ} (hX : 1 ≤ X)
    (hB : ∀ᶠ k : ℕ in Filter.atTop, B ≤ quarterAbelAction656 X (quarterZeroLedger644 k)) :
    B ≤
      quarterAbelAction656 X
        (fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) := by
  exact ge_of_tendsto (quarter_zero_abel_limit_656 hX) hB

/-- At the upper support endpoint the fifth-order zero kills both boundary terms. -/
theorem quarter_support_jet_656 {X : ℝ} (hx : 0 < X) :
    let B := X * Real.exp (21 / 8)
    quarterWeight656 X B = 0 ∧ deriv (quarterWeight656 X) B = 0 := by
  intro B
  let v := fun t : ℝ ↦ (11 / 10) * (21 / 8 - Real.log (t / X))
  have hb : 0 < B := mul_pos hx (Real.exp_pos _)
  have hv : v B = 0 := by
    dsimp only [v, B]
    rw [mul_div_cancel_left₀ _ hx.ne', Real.log_exp]
    norm_num only
  have hd : DifferentiableAt ℝ v B := by
    dsimp only [v]
    fun_prop (disch := positivity)
  let g := fun t : ℝ ↦ 1 / Real.sqrt t * (Real.exp (-v t) / 120)
  have hg : DifferentiableAt ℝ g B := by
    dsimp only [g]
    fun_prop (disch := positivity)
  have he : quarterWeight656 X = fun t ↦ v t ^ 5 * g t := by
    funext t
    dsimp only [quarterWeight656, v, g]
    ring
  rw [he]
  have h := ((hd.hasDerivAt.pow 5).mul hg.hasDerivAt).deriv
  constructor
  · change v B ^ 5 * g B = 0
    rw [hv]
    ring
  · change deriv (v ^ 5 * g) B = 0
    rw [h, Pi.pow_apply, hv]
    ring

/-- The Abel action depends only on the input on its physical support. -/
private theorem quarter_abel_congr_656 {X : ℝ} (hX : 1 ≤ X) {F G : ℝ → ℝ}
    (h : Set.EqOn F G (Set.Icc 1 (X * Real.exp (21 / 8)))) :
    quarterAbelAction656 X F = quarterAbelAction656 X G := by
  have hXB :=
    le_mul_of_one_le_right (zero_le_one.trans hX)
      (Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 21 / 8))
  have hB := hX.trans hXB
  dsimp only [quarterAbelAction656]
  rw [h ⟨hX, hXB⟩, h ⟨le_rfl, hB⟩]
  have inner :=
    intervalIntegral.integral_congr (μ := MeasureTheory.volume) (f := fun t ↦
      F t * deriv (fun u ↦ u * deriv (quarterWeight656 X) u) t) (g := fun t ↦
      G t * deriv (fun u ↦ u * deriv (quarterWeight656 X) u) t) (a := 1) (b := X)
      (fun t ht ↦ by
        rw [Set.uIcc_of_le hX] at ht
        exact
          congrArg (fun y ↦ y * deriv (fun u ↦ u * deriv (quarterWeight656 X) u) t)
            (h ⟨ht.1, ht.2.trans hXB⟩))
  have outer :=
    intervalIntegral.integral_congr (μ := MeasureTheory.volume) (f := fun t ↦
      F t * deriv (fun u ↦ u * deriv (quarterWeight656 X) u) t) (g := fun t ↦
      G t * deriv (fun u ↦ u * deriv (quarterWeight656 X) u) t) (a := 1) (b :=
      X * Real.exp (21 / 8))
      (fun t ht ↦ by
        rw [Set.uIcc_of_le hB] at ht
        exact congrArg (fun y ↦ y * deriv (fun u ↦ u * deriv (quarterWeight656 X) u) t) (h ht))
  rw [inner, outer]

/-- On the physical support, a finite sum of continuous inputs can be
evaluated by summing their individual Abel actions. -/
private theorem quarter_abel_finset_sum_656 {ι : Type*} {X : ℝ} (hX : 1 ≤ X) (S : Finset ι)
    (F : ι → ℝ → ℝ) (hF : ∀ i ∈ S, ContinuousOn (F i) (Set.Icc 1 (X * Real.exp (21 / 8)))) :
    quarterAbelAction656 X (fun t ↦ ∑ i ∈ S, F i t) = ∑ i ∈ S, quarterAbelAction656 X (F i) := by
  let B := X * Real.exp (21 / 8)
  let P := fun t ↦ t * deriv (quarterWeight656 X) t
  have hx := zero_lt_one.trans_le hX
  have hXB : X ≤ B := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only))
  have hQ : ContinuousOn (deriv P) (Set.Icc 1 B) := abel_deriv_continuous_656 hx
  have hI {b : ℝ} (hb : 1 ≤ b) (hbB : b ≤ B) :
    (∫ t in (1 : ℝ)..b, ∑ i ∈ S, F i t * deriv P t) =
      ∑ i ∈ S, ∫ t in (1 : ℝ)..b, F i t * deriv P t := by
    apply intervalIntegral.integral_finsetSum
    intro i hi
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hb).2
    exact (((hF i hi).mul hQ).mono (Set.Icc_subset_Icc_right hbB)).integrableOn_Icc
  change
    4 * (∫ t in (1 : ℝ)..X, (∑ i ∈ S, F i t) * deriv P t) -
          (∫ t in (1 : ℝ)..B, (∑ i ∈ S, F i t) * deriv P t) -
          4 * P X * (∑ i ∈ S, F i X) +
        3 * P 1 * (∑ i ∈ S, F i 1) =
      ∑ i ∈ S,
        (4 * (∫ t in (1 : ℝ)..X, F i t * deriv P t) - (∫ t in (1 : ℝ)..B, F i t * deriv P t) -
            4 * P X * F i X +
          3 * P 1 * F i 1)
  simp only [Finset.sum_mul, hI hX hXB, hI (hX.trans hXB) le_rfl, Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- Summing the individual physical Abel contributions over successively
larger zero rectangles converges to the full nontrivial-zero contribution. -/
private theorem quarter_sum_action_limit_656 {X : ℝ} (hX : 1 ≤ X) :
    Filter.Tendsto
      (fun m : ℕ ↦
        ∑
          ρ ∈
            (AnalyticNumberTheory.RiemannZeta.riemannZetaZerosInAnyRectangle
                  (AnalyticNumberTheory.RiemannZeta.unifiedRectangleLower m)
                  (AnalyticNumberTheory.RiemannZeta.unifiedTauRectangleUpper 2 m)).filter
              (fun ρ ↦ ¬ρ.re < 0),
          quarterAbelAction656 X
            (fun t ↦ (AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re))
      Filter.atTop
      (nhds
        (quarterAbelAction656 X
          (fun t ↦
            (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re))) := by
  apply (quarter_zero_abel_limit_656 hX).congr'
  filter_upwards with m
  let S :=
    (AnalyticNumberTheory.RiemannZeta.riemannZetaZerosInAnyRectangle
          (AnalyticNumberTheory.RiemannZeta.unifiedRectangleLower m)
          (AnalyticNumberTheory.RiemannZeta.unifiedTauRectangleUpper 2 m)).filter
      (fun ρ ↦ ¬ρ.re < 0)
  let F := fun (ρ : ℂ) (t : ℝ) ↦ (AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re
  change
    quarterAbelAction656 X
        (fun t ↦
          (∑ ρ ∈ S, AnalyticNumberTheory.RiemannZeta.riemannZetaLogZeroContribution t ρ).re) =
      ∑ ρ ∈ S, quarterAbelAction656 X (F ρ)
  rw [←
    quarter_abel_finset_sum_656 hX S F
      (fun ρ _ ↦
        Complex.continuous_re.comp_continuousOn
          (AnalyticNumberTheory.RiemannZeta.zero_term_continuous zero_lt_one ρ))]
  apply quarter_abel_congr_656 hX
  intro t _
  dsimp only [F]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hm := Finset.mem_filter.mp hρ
  have hz := (AnalyticNumberTheory.RiemannZeta.mem_riemannZetaZerosInAnyRectangle_iff.mp hm.1).2
  simp only [AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm, hz, true_and, not_lt.mp hm.2,
    ↓reduceIte]

/-- Two integrations by parts move the Abel action onto the derivative of
the logarithmic derivative of its input, retaining both cutoff values. -/
private theorem quarter_abel_parts_656 {X : ℝ} (hX : 1 ≤ X) {F D H : ℝ → ℝ}
    (hF : ∀ t > 0, HasDerivAt F (D t) t) (hG : ∀ t > 0, HasDerivAt (fun u ↦ u * D u) (H t) t)
    (hD : ContinuousOn D (Set.Ioi 0)) (hH : ContinuousOn H (Set.Ioi 0)) :
    let B := X * Real.exp (21 / 8)
    let W := quarterWeight656 X
    quarterAbelAction656 X F =
      4 * (∫ t in (1 : ℝ)..X, H t * W t) - (∫ t in (1 : ℝ)..B, H t * W t) - 4 * (X * D X) * W X +
        3 * D 1 * W 1 := by
  intro B W
  let P := fun t ↦ t * deriv W t
  let G := fun t ↦ t * D t
  have hx := zero_lt_one.trans_le hX
  have hb : 1 ≤ B := hX.trans (le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only)))
  have hW := weight_smooth_656 hx
  have hP : ContDiffOn ℝ 1 P (Set.Ioi 0) :=
    contDiffOn_id.mul (hW.deriv_of_isOpen (m := 1) isOpen_Ioi (by decide))
  have hw (t : ℝ) (ht : 0 < t) : HasDerivAt W (deriv W t) t :=
    (((hW.differentiableOn (by decide)) t ht).differentiableAt (isOpen_Ioi.mem_nhds ht)).hasDerivAt
  have hp (t : ℝ) (ht : 0 < t) : HasDerivAt P (deriv P t) t :=
    (((hP.differentiableOn (by decide)) t ht).differentiableAt (isOpen_Ioi.mem_nhds ht)).hasDerivAt
  have hi {b : ℝ} (h : 1 ≤ b) :
    (∫ t in (1 : ℝ)..b, F t * deriv P t) =
      F b * P b - F 1 * P 1 - (G b * W b - G 1 * W 1) + ∫ t in (1 : ℝ)..b, H t * W t := by
    have hsub : Set.uIcc (1 : ℝ) b ⊆ Set.Ioi 0 := by
      rw [Set.uIcc_of_le h]
      exact fun _ ht ↦ zero_lt_one.trans_le ht.1
    have h₁ :=
      intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun t ht ↦ hF t (hsub ht))
        (fun t ht ↦ hp t (hsub ht)) (hD.mono hsub).intervalIntegrable
        ((hP.continuousOn_deriv_of_isOpen isOpen_Ioi (by decide)).mono hsub).intervalIntegrable
    have h₂ :=
      intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun t ht ↦ hG t (hsub ht))
        (fun t ht ↦ hw t (hsub ht)) (hH.mono hsub).intervalIntegrable
        ((hW.continuousOn_deriv_of_isOpen isOpen_Ioi (by decide)).mono hsub).intervalIntegrable
    have he : (∫ t in (1 : ℝ)..b, D t * P t) = ∫ t in (1 : ℝ)..b, G t * deriv W t := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only [P, G]
      ring
    rw [h₁, he, h₂]
    ring
  obtain ⟨hwB, hpB⟩ := quarter_support_jet_656 hx
  change W B = 0 at hwB
  have hPB : P B = 0 := by
    dsimp only [P, W, B]
    rw [hpB, mul_zero]
  change
    4 * (∫ t in (1 : ℝ)..X, F t * deriv P t) - (∫ t in (1 : ℝ)..B, F t * deriv P t) -
          4 * P X * F X +
        3 * P 1 * F 1 =
      _
  rw [hi hX, hi hb, hPB, hwB]
  dsimp only [G]
  ring

/-- Multiplying the first derivative of a complex power by its real
argument restores the original exponent. This is the derivative input to
the two integrations by parts for a zero contribution. -/
private theorem cpow_log_deriv {t : ℝ} (ht : 0 < t) (c ρ : ℂ) :
    t * (c * ρ * (t : ℂ) ^ (ρ - 1)).re = (c * ρ * (t : ℂ) ^ ρ).re := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hre (z : ℂ) : ((t : ℂ) * z).re = t * z.re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [← hre]
  apply congrArg Complex.re
  calc
    (t : ℂ) * (c * ρ * (t : ℂ) ^ (ρ - 1)) = c * ρ * ((t : ℂ) ^ (ρ - 1) * (t : ℂ) ^ (1 : ℂ)) := by
      rw [Complex.cpow_one]
      ring
    _ = c * ρ * (t : ℂ) ^ ρ := by rw [← Complex.cpow_add _ _ ht', sub_add_cancel]

/-- The physical Abel action of a complex power times a constant is a
weighted Mellin integral with explicit endpoint terms. Zero contributions
use the constant minus the multiplicity divided by the square of the zero. -/
private theorem quarter_abel_cpow_656 {X : ℝ} (hX : 1 ≤ X) {ρ : ℂ} (hρ : ρ ≠ 0) (c : ℂ) :
    let B := X * Real.exp (21 / 8)
    let W := quarterWeight656 X
    let H := fun t : ℝ ↦ (c * ρ * ρ * (t : ℂ) ^ (ρ - 1)).re
    quarterAbelAction656 X (fun t ↦ (c * (t : ℂ) ^ ρ).re) =
      4 * (∫ t in (1 : ℝ)..X, H t * W t) - (∫ t in (1 : ℝ)..B, H t * W t) -
          4 * (c * ρ * (X : ℂ) ^ ρ).re * W X +
        3 * (c * ρ).re * W 1 := by
  intro B W H
  let D := fun t : ℝ ↦ (c * ρ * (t : ℂ) ^ (ρ - 1)).re
  have hpow (a : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ ↦ (a * (u : ℂ) ^ ρ).re) (a * ρ * (t : ℂ) ^ (ρ - 1)).re t := by
    have hd := (hasDerivAt_ofReal_cpow_const ht.ne' hρ).const_mul a
    simpa only [zero_apply, zero_add, Complex.reCLM_apply, mul_assoc] using
      (hasDerivAt_const t Complex.reCLM).clm_apply hd
  have hg (t : ℝ) (ht : 0 < t) : HasDerivAt (fun u ↦ u * D u) (H t) t := by
    apply (hpow (c * ρ) ht).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds ht] with u hu
    exact cpow_log_deriv hu c ρ
  have hc (a : ℂ) : ContinuousOn (fun t : ℝ ↦ (a * (t : ℂ) ^ (ρ - 1)).re) (Set.Ioi 0) := by
    intro t ht
    have hp := Complex.continuousAt_ofReal_cpow_const t (ρ - 1) (Or.inr (ne_of_gt ht))
    exact (Complex.continuous_re.continuousAt.comp (continuousAt_const.mul hp)).continuousWithinAt
  have h := quarter_abel_parts_656 hX (fun _ ht ↦ hpow c ht) hg (hc (c * ρ)) (hc (c * ρ * ρ))
  dsimp only at h
  change _ = _ - 4 * (c * ρ * (X : ℂ) ^ ρ).re * W X + 3 * (c * ρ).re * W 1
  rw [h, cpow_log_deriv (zero_lt_one.trans_le hX), Complex.ofReal_one, Complex.one_cpow, mul_one]

/-- The contribution of a nontrivial zero to the physical Abel action is
its signed power integral with two explicit boundary values. The zero's
multiplicity multiplies every term. -/
private theorem quarter_abel_zero_term_656 {X : ℝ} (hX : 1 ≤ X) {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (hre : 0 ≤ ρ.re) (hρ : ρ ≠ 0) :
    let B := X * Real.exp (21 / 8)
    let W := quarterWeight656 X
    let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
    let H := fun t : ℝ ↦ (-m * (t : ℂ) ^ (ρ - 1)).re
    quarterAbelAction656 X
        (fun t ↦ (AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) =
      4 * (∫ t in (1 : ℝ)..X, H t * W t) - (∫ t in (1 : ℝ)..B, H t * W t) -
          4 * (-m / ρ * (X : ℂ) ^ ρ).re * W X +
        3 * (-m / ρ).re * W 1 := by
  intro B W m H
  let c := -m / ρ ^ 2
  have h₁ : c * ρ = -m / ρ := by
    dsimp only [c]
    rw [pow_two, ← div_div, div_mul_cancel₀ _ hρ]
  have h₂ : c * ρ * ρ = -m := by rw [h₁, div_mul_cancel₀ _ hρ]
  have he :
    (fun t ↦ (AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) =
      (fun t : ℝ ↦ (c * (t : ℂ) ^ ρ).re) := by
    funext t
    simp only [AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm, hz, hre, and_self,
      ↓reduceIte, AnalyticNumberTheory.RiemannZeta.riemannZetaLogZeroContribution, c]
    rw [div_mul_eq_mul_div]
  rw [he]
  have h := quarter_abel_cpow_656 hX hρ c
  dsimp only at h
  simp only [h₂] at h
  simp only [h₁] at h
  exact h

/-- The sum of the explicit Mellin and endpoint contributions converges to
the nontrivial-zero part of the section 132 principal Abel action. -/
theorem quarter_zero_integral_limit_656 {X : ℝ} (hX : 1 ≤ X) :
    Filter.Tendsto
      (fun m : ℕ ↦
        ∑
          ρ ∈
            (AnalyticNumberTheory.RiemannZeta.riemannZetaZerosInAnyRectangle
                  (AnalyticNumberTheory.RiemannZeta.unifiedRectangleLower m)
                  (AnalyticNumberTheory.RiemannZeta.unifiedTauRectangleUpper 2 m)).filter
              (fun ρ ↦ ¬ρ.re < 0),
          quarterZeroIntegral656 X ρ)
      Filter.atTop
      (nhds
        (quarterAbelAction656 X
          (fun t ↦
            (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re))) := by
  apply (quarter_sum_action_limit_656 hX).congr'
  filter_upwards with m
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hm := Finset.mem_filter.mp hρ
  have hz := (AnalyticNumberTheory.RiemannZeta.mem_riemannZetaZerosInAnyRectangle_iff.mp hm.1).2
  have hn : ρ ≠ 0 := by
    intro he
    rw [he, riemannZeta_zero] at hz
    norm_num only at hz
  exact quarter_abel_zero_term_656 hX hz (not_lt.mp hm.2) hn

/-- Under RH the finite physical zero lower bound survives passage to
the full logarithmic zero sum in the section 132 Abel action. -/
theorem quarter_zero_abel_bound_656 (hRH : RiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc 322 328) :
    (-0.002594 : ℝ) ≤
      quarterAbelAction656 (r ^ 2)
        (fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) := by
  have h1 : 1 ≤ r := (by norm_num only : (1 : ℝ) ≤ 322).trans hr.1
  apply ge_of_tendsto (quarter_zero_integral_limit_656 (one_le_pow₀ h1 (n := 2)))
  filter_upwards [Filter.tendsto_atTop.mp
      AnalyticNumberTheory.RiemannZeta.tendsto_unifiedContourHeightSeq_atTop 100] with
    k hk
  rw [unified_ledger_eq k ((by norm_num only : (0 : ℝ) ≤ 100).trans hk)]
  exact quarter_zero_integral_lower_656 hRH hr hk

/-- Integrating the second logarithmic derivative against one logarithmic atom
recovers the weight at v, with both endpoint terms at b. -/
private theorem quarter_log_atom_656 {X v b : ℝ} (hX : 0 < X) (hv : 0 < v) (hb : v ≤ b) :
    let W := quarterWeight656 X
    let P := fun t ↦ t * deriv W t
    W v = (∫ t in v..b, Real.log (t / v) * deriv P t) - Real.log (b / v) * P b + W b := by
  intro W P
  have hw := weight_smooth_656 hX
  have hp : ContDiffOn ℝ 1 P (Set.Ioi 0) :=
    contDiffOn_id.mul (hw.deriv_of_isOpen (m := 1) isOpen_Ioi (by decide))
  have ht (t : ℝ) (h : t ∈ Set.Icc v b) : t ∈ Set.Ioi (0 : ℝ) := hv.trans_le h.1
  have hi : ContinuousOn (fun t ↦ Real.log (t / v) * deriv P t) (Set.Icc v b) := by
    apply ContinuousOn.mul
    · exact
        (continuous_id.div_const v).continuousOn.log (fun t h ↦ (div_pos (hv.trans_le h.1) hv).ne')
    · exact (hp.continuousOn_deriv_of_isOpen isOpen_Ioi (by decide)).mono (fun t h ↦ ht t h)
  rw [← Set.uIcc_of_le hb] at hi
  have h :=
    Analysis.log_variation_integral hv hv hb
      (fun t h ↦
        ((hw.differentiableOn (by decide) t (ht t h)).differentiableAt
            (isOpen_Ioi.mem_nhds (ht t h))).hasDerivAt)
      (fun t h ↦
        ((hp.differentiableOn (by decide) t (ht t h)).differentiableAt
            (isOpen_Ioi.mem_nhds (ht t h))).hasDerivAt)
      hi.intervalIntegrable
  rw [Real.log_div_self, zero_mul, zero_sub] at h
  dsimp only [P] at h ⊢
  linarith only [h]

/-- The principal prefix equals its second-order integral sum plus the psi endpoint
minus the logarithmically weighted Mangoldt endpoint. Each integral starts at its own atom. -/
private theorem quarter_second_abel_656 {X b : ℝ} (hX : 0 < X) (hb : 0 ≤ b)
    (hs : Real.log (b / X) ≤ 21 / 8) :
    let W := quarterWeight656 X
    let P := fun t ↦ t * deriv W t
    (∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) X n).re) =
      (∑ n ∈ Finset.Ioc 0 ⌊b⌋₊,
            ArithmeticFunction.vonMangoldt n * ∫ t in (n : ℝ)..b, Real.log (t / n) * deriv P t) -
          P b * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum b +
        W b * Chebyshev.psi b := by
  intro W P
  rw [AnalyticNumberTheory.Arithmetic.psi_eq_positive_sum,
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 := (Finset.mem_Ioc.mp hn).1
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hnb := (Nat.le_floor_iff hb).mp (Finset.mem_Ioc.mp hn).2
  rw [quarter_summand_656 hX hn0
      ((Real.log_le_log (div_pos hnr hX) (div_le_div_of_nonneg_right hnb hX.le)).trans hs)]
  have h := quarter_log_atom_656 hX hnr hnb
  change W n = _ at h
  change W n * _ = _
  rw [h]
  unfold AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm
  dsimp only [W, P]
  ring

/-- The second Abel formula for the supported principal prefix has a single integral
of the logarithmically weighted Mangoldt sum, with explicit boundary terms at b. -/
private theorem quarter_log_integral_656 {X b : ℝ} (hX : 0 < X) (hb : 1 ≤ b)
    (hs : Real.log (b / X) ≤ 21 / 8) :
    let W := quarterWeight656 X
    let P := fun t ↦ t * deriv W t
    (∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) X n).re) =
      (∫ t in (1 : ℝ)..b, AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * deriv P t) -
          P b * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum b +
        W b * Chebyshev.psi b := by
  intro W P
  have hw := weight_smooth_656 hX
  have hp : ContDiffOn ℝ 1 P (Set.Ioi 0) :=
    contDiffOn_id.mul (hw.deriv_of_isOpen (m := 1) isOpen_Ioi (by decide))
  have hq :=
    (hp.continuousOn_deriv_of_isOpen isOpen_Ioi (by decide)).mono
      (show Set.Icc 1 b ⊆ Set.Ioi 0 from fun t ht ↦ zero_lt_one.trans_le ht.1)
  exact
    (quarter_second_abel_656 hX (zero_le_one.trans hb) hs).trans (by rw [log_sum_integral hb hq])

/-- Evaluate the linear and logarithmic main terms in the double Abel integral.
The free coefficient c can be specialized to log(2 pi) for the centered remainder. -/
private theorem quarter_centering_integral_656 {X b : ℝ} (hx : 0 < X) (hb : 1 ≤ b) (c : ℝ) :
    let W := quarterWeight656 X
    let P := fun t ↦ t * deriv W t
    (∫ t in (1 : ℝ)..b, (t - c * Real.log t) * deriv P t) =
      (b - c * Real.log b) * P b - (b - c) * W b - P 1 + (1 - c) * W 1 +
        ∫ t in (1 : ℝ)..b, W t := by
  intro W P
  have hw := weight_smooth_656 hx
  have hp : ContDiffOn ℝ 1 P (Set.Ioi 0) :=
    contDiffOn_id.mul (hw.deriv_of_isOpen (m := 1) isOpen_Ioi (by decide))
  have ht {u : ℝ} (h : u ∈ Set.uIcc 1 b) : u ∈ Set.Ioi (0 : ℝ) :=
    zero_lt_one.trans_le ((Set.uIcc_of_le hb ▸ h : u ∈ Set.Icc 1 b).1)
  have hdW (u : ℝ) (h : u ∈ Set.uIcc 1 b) :=
    ((hw.differentiableOn (by decide) u (ht h)).differentiableAt
        (isOpen_Ioi.mem_nhds (ht h))).hasDerivAt
  have hdP (u : ℝ) (h : u ∈ Set.uIcc 1 b) :=
    ((hp.differentiableOn (by decide) u (ht h)).differentiableAt
        (isOpen_Ioi.mem_nhds (ht h))).hasDerivAt
  have hq :=
    (hp.continuousOn_deriv_of_isOpen isOpen_Ioi (by decide)).mono
      (show Set.uIcc 1 b ⊆ Set.Ioi 0 from fun _ h ↦ ht h)
  have hi : IntervalIntegrable (fun t ↦ t * deriv P t) MeasureTheory.volume 1 b :=
    (continuous_id.continuousOn.mul hq).intervalIntegrable
  have hlog : IntervalIntegrable (fun t ↦ Real.log t * deriv P t) MeasureTheory.volume 1 b :=
    ((Real.continuousOn_log.mono (show Set.uIcc 1 b ⊆ {0}ᶜ from fun _ h ↦ ne_of_gt (ht h))).mul
        hq).intervalIntegrable
  have hlin :=
    Analysis.linear_variation_integral hdW hdP hi
      (hw.continuousOn.mono (fun _ h ↦ ht h)).intervalIntegrable
  have hlg :=
    Analysis.log_variation_integral zero_lt_one zero_lt_one hb
      (fun u h ↦ hdW u (Set.uIcc_of_le hb ▸ h)) (fun u h ↦ hdP u (Set.uIcc_of_le hb ▸ h))
      (by simpa only [div_one] using hlog)
  simp only [div_one, Real.log_one, zero_mul, one_mul] at hlg hlin
  simp only [sub_mul, mul_assoc, intervalIntegral.integral_sub hi (hlog.const_mul c),
    intervalIntegral.integral_const_mul]
  dsimp only [P, W] at *
  rw [hlin, hlg]
  ring

/-- After subtracting t - c log t from the log-weighted Mangoldt sum, the supported
prefix has a single remainder integral and two explicit endpoint contributions. -/
private theorem quarter_centered_prefix_656 {X b : ℝ} (hx : 0 < X) (hb : 1 ≤ b)
    (hs : Real.log (b / X) ≤ 21 / 8) (c : ℝ) :
    let W := quarterWeight656 X
    let P := fun t ↦ t * deriv W t
    let E := fun t ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - (t - c * Real.log t)
    (∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) X n).re) =
      (∫ t in (1 : ℝ)..b, W t) + (∫ t in (1 : ℝ)..b, E t * deriv P t) - P b * E b +
            W b * (Chebyshev.psi b - b + c) -
          P 1 +
        (1 - c) * W 1 := by
  intro W P E
  have hp : ContDiffOn ℝ 1 P (Set.Ioi 0) :=
    contDiffOn_id.mul ((weight_smooth_656 hx).deriv_of_isOpen (m := 1) isOpen_Ioi (by decide))
  have ht {u : ℝ} (h : u ∈ Set.uIcc 1 b) : 0 < u :=
    zero_lt_one.trans_le ((Set.uIcc_of_le hb ▸ h : u ∈ Set.Icc 1 b).1)
  have hq :=
    (hp.continuousOn_deriv_of_isOpen isOpen_Ioi (by decide)).mono
      (show Set.uIcc 1 b ⊆ Set.Ioi 0 from fun _ h ↦ ht h)
  have hm :=
    AnalyticNumberTheory.Arithmetic.continuousOn_logWeightedMangoldtSum_scaled (x := 1) zero_lt_one
      b
  simp only [one_mul] at hm
  have hi :=
    (hm.mono
          (show Set.uIcc 1 b ⊆ Set.Icc 0 b by
            rw [Set.uIcc_of_le hb]
            exact Set.Icc_subset_Icc_left zero_le_one)).mul
      hq
  have hl := Real.continuousOn_log.mono (show Set.uIcc 1 b ⊆ {0}ᶜ from fun _ h ↦ (ht h).ne')
  have hj :=
    (continuous_id.continuousOn.sub ((continuous_const (y := c)).continuousOn.mul hl)).mul hq
  have hh := quarter_log_integral_656 hx hb hs
  have hc := quarter_centering_integral_656 hx hb c
  dsimp only [E, W, P] at *
  simp_rw [sub_mul (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum _) _ _]
  rw [intervalIntegral.integral_sub (f := fun t ↦
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * deriv P t) (g := fun t ↦
      (t - c * Real.log t) * deriv P t) hi.intervalIntegrable hj.intervalIntegrable]
  linarith only [hh, hc]

/-- Terms beyond X exp(21/8) vanish, so the full real principal series is a finite sum. -/
theorem quarter_principal_finite_656 {X : ℝ} (hX : 0 < X) :
    (∑' n : ℕ, (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) X n).re) =
      ∑ n ∈ Finset.Ioc 0 ⌊X * Real.exp (21 / 8)⌋₊,
        (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) X n).re := by
  apply tsum_eq_sum
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp only [LLS.PaperStatements.MellinKernel.summand, ite_true, Complex.zero_re]
  have hcut : ⌊X * Real.exp (21 / 8)⌋₊ < n := by
    by_contra h
    exact hn (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0, le_of_not_gt h⟩)
  have hi : Real.exp (21 / 8) < (n : ℝ) / X :=
    (lt_div_iff₀ hX).mpr ((mul_comm _ X).trans_lt (Nat.lt_of_floor_lt hcut))
  have hp := (Real.exp_pos _).trans hi
  have hlog := Real.log_lt_log (Real.exp_pos _) hi
  rw [Real.log_exp] at hlog
  rw [LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn0, quarterKernel656,
    LLS.PaperStatements.rationalPole_transform _ _ _ _ hp, Analysis.rationalPoleProfile,
    ite_eq_right (fun h ↦ (not_lt_of_ge h.2) (by linarith only [hlog]))]
  simp only [Complex.ofReal_zero, mul_zero, Complex.zero_re]

/-- Center the difference of four principal prefixes and the full principal series.
The support jet vanishes at B, leaving a weighted difference of two remainder integrals,
one remainder value at X, and explicit boundary terms. -/
theorem quarter_centered_difference_656 {X : ℝ} (hX : 1 ≤ X) :
    let B := X * Real.exp (21 / 8)
    let S := fun n : ℕ ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) X n).re
    let W := quarterWeight656 X
    let P := fun t ↦ t * deriv W t
    let c := Real.log (2 * Real.pi)
    let E := fun t ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - (t - c * Real.log t)
    4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) =
      4 * (∫ t in (1 : ℝ)..X, W t) - (∫ t in (1 : ℝ)..B, W t) +
            (4 * (∫ t in (1 : ℝ)..X, E t * deriv P t) - (∫ t in (1 : ℝ)..B, E t * deriv P t) -
              4 * P X * E X) +
            4 * W X * (Chebyshev.psi X - X + c) -
          3 * P 1 +
        3 * (1 - c) * W 1 := by
  intro B S W P c E
  have hx := zero_lt_one.trans_le hX
  have hb :=
    hX.trans (le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 21 / 8)))
  have hlog : Real.log (B / X) = 21 / 8 := by
    dsimp only [B]
    rw [mul_div_cancel_left₀ _ hx.ne', Real.log_exp]
  have hf := quarter_centered_prefix_656 hx hb hlog.le c
  have hu :=
    quarter_centered_prefix_656 hx hX
      (by
        rw [div_self hx.ne', Real.log_one]; norm_num only)
      c
  obtain ⟨hw, hd⟩ := quarter_support_jet_656 hx
  dsimp only at hf hu
  rw [hd, hw, mul_zero, zero_mul, sub_zero, zero_mul, add_zero] at hf
  dsimp only [S, W, P, E, B]
  rw [quarter_principal_finite_656 hx, hf, hu]
  ring

/-- An additive constant in the centered explicit formula cancels exactly. -/
private theorem quarter_abel_const_656 {X : ℝ} (hX : 1 ≤ X) (c : ℝ) :
    quarterAbelAction656 X (fun _ ↦ c) = 0 := by
  let B := X * Real.exp (21 / 8)
  let P := fun t ↦ t * deriv (quarterWeight656 X) t
  have hx := zero_lt_one.trans_le hX
  have hb : 1 ≤ B := hX.trans (le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only)))
  have hP : ContDiffOn ℝ 1 P (Set.Ioi 0) :=
    contDiffOn_id.mul ((weight_smooth_656 hx).deriv_of_isOpen (m := 1) isOpen_Ioi (by decide))
  have hI {b : ℝ} (h : 1 ≤ b) : (∫ t in (1 : ℝ)..b, deriv P t) = P b - P 1 := by
    have hsub : Set.Icc (1 : ℝ) b ⊆ Set.Ioi 0 := fun _ ht ↦ zero_lt_one.trans_le ht.1
    apply intervalIntegral.integral_deriv_eq_sub
    · intro t ht
      have ht' := hsub ((Set.uIcc_of_le h) ▸ ht)
      exact ((hP.differentiableOn (by decide)) t ht').differentiableAt (isOpen_Ioi.mem_nhds ht')
    · apply (intervalIntegrable_iff_integrableOn_Icc_of_le h).2
      exact ((hP.continuousOn_deriv_of_isOpen isOpen_Ioi (by decide)).mono hsub).integrableOn_Icc
  have hB : P B = 0 := by
    dsimp only [P, B]
    rw [(quarter_support_jet_656 hx).2, mul_zero]
  change
    4 * (∫ t in (1 : ℝ)..X, c * deriv P t) - (∫ t in (1 : ℝ)..B, c * deriv P t) - 4 * P X * c +
        3 * P 1 * c =
      0
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hI hX, hI hb, hB]
  ring

/-- At and above one, the centered Mangoldt error is the real nontrivial-zero series
minus the trivial-zero series and the constant pole residue. This gives the
input for the section 122 Abel action on the interior of its support. -/
private theorem quarter_abel_zero_expansion_656 {X : ℝ} (hX : 1 ≤ X) :
    quarterAbelAction656 X
        (fun t ↦
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
            (t - Real.log (2 * Real.pi) * Real.log t)) =
      quarterAbelAction656 X
        (fun t ↦
          (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re -
            AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries t -
            AnalyticNumberTheory.RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re) := by
  exact quarter_abel_congr_656 hX (fun _ ht ↦ quarter_centered_zero_eq_644 ht.1)

/-- Continuous inputs on the physical support satisfy the integrability
conditions for subtracting their Abel actions. -/
private theorem quarter_abel_sub_656 {X : ℝ} (hX : 1 ≤ X) {F G : ℝ → ℝ}
    (hF : ContinuousOn F (Set.Icc 1 (X * Real.exp (21 / 8))))
    (hG : ContinuousOn G (Set.Icc 1 (X * Real.exp (21 / 8)))) :
    quarterAbelAction656 X (fun t ↦ F t - G t) =
      quarterAbelAction656 X F - quarterAbelAction656 X G := by
  let B := X * Real.exp (21 / 8)
  let P := fun t ↦ t * deriv (quarterWeight656 X) t
  have hx := zero_lt_one.trans_le hX
  have hXB : X ≤ B := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only))
  have hQ : ContinuousOn (deriv P) (Set.Icc 1 B) := abel_deriv_continuous_656 hx
  have hI {H : ℝ → ℝ} (hH : ContinuousOn H (Set.Icc 1 B)) {b : ℝ} (hb : 1 ≤ b) (hbB : b ≤ B) :
    IntervalIntegrable (fun t ↦ H t * deriv P t) MeasureTheory.volume 1 b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hb).2
    exact ((hH.mul hQ).mono (Set.Icc_subset_Icc_right hbB)).integrableOn_Icc
  have hf₁ := hI hF hX hXB
  have hg₁ := hI hG hX hXB
  have hf₂ := hI hF (hX.trans hXB) le_rfl
  have hg₂ := hI hG (hX.trans hXB) le_rfl
  dsimp (config := { failIfUnchanged := false }) only [P, B] at hf₁ hg₁ hf₂ hg₂
  dsimp only [quarterAbelAction656]
  simp only [sub_mul, intervalIntegral.integral_sub hf₁ hg₁, intervalIntegral.integral_sub hf₂ hg₂]
  ring

/-- On the entire physical support, split the centered Mangoldt Abel action
into nontrivial and trivial zero contributions. The constant pole residue
cancels exactly. -/
theorem quarter_abel_zero_split_656 {X : ℝ} (hX : 1 ≤ X) :
    quarterAbelAction656 X
        (fun t ↦
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
            (t - Real.log (2 * Real.pi) * Real.log t)) =
      quarterAbelAction656 X
          (fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) -
        quarterAbelAction656 X
          AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries := by
  let Z := fun t : ℝ ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re
  let T := AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries
  let c := AnalyticNumberTheory.RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re
  have hz : ContinuousOn Z (Set.Icc 1 (X * Real.exp (21 / 8))) :=
    Complex.continuous_re.comp_continuousOn
      (AnalyticNumberTheory.RiemannZeta.zero_sum_continuous (b := X * Real.exp (21 / 8))
        (le_refl (1 : ℝ)))
  have ht : ContinuousOn T (Set.Icc 1 (X * Real.exp (21 / 8))) :=
    AnalyticNumberTheory.RiemannZeta.trivial_cont_closed (le_refl (1 : ℝ))
  rw [quarter_abel_zero_expansion_656 hX]
  change quarterAbelAction656 X (fun t ↦ (Z - T) t - c) = _
  rw [quarter_abel_sub_656 hX (hz.sub ht) (continuousOn_const (c := c)), quarter_abel_const_656 hX,
    sub_zero]
  exact quarter_abel_sub_656 hX hz ht

/-- For `X ≥ 1`, four principal prefixes minus the full principal sum
equal the integrated weight terms, the psi boundary, and the difference
of the nontrivial and trivial zero actions. The lower endpoint contributes
three times the weight at one. -/
theorem quarter_principal_explicit_656 {X : ℝ} (hX : 1 ≤ X) :
    let B := X * Real.exp (21 / 8)
    let S := fun n : ℕ ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) X n).re
    let W := quarterWeight656 X
    4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) =
      4 * (∫ t in (1 : ℝ)..X, W t) - (∫ t in (1 : ℝ)..B, W t) +
          4 * W X * (Chebyshev.psi X - X + Real.log (2 * Real.pi)) +
          3 * W 1 +
          quarterAbelAction656 X
            (fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) -
        quarterAbelAction656 X AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries -
        3 * Real.log (2 * Real.pi) * W 1 := by
  intro B S W
  have h := quarter_centered_difference_656 hX
  dsimp only at h
  dsimp only [quarterAbelAction656] at ⊢
  have hz := quarter_abel_zero_split_656 hX
  dsimp only [quarterAbelAction656] at hz
  rw [LLS.logWeightedMangoldtSum_eq_zero_of_le_one (le_refl (1 : ℝ)), Real.log_one, mul_zero,
    sub_zero, zero_sub] at hz
  change 4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) = _
  rw [h]
  dsimp only [B, W]
  linarith only [hz]

/-- In either broad section 132 interval, the fourfold principal prefix
less the full principal sum is bounded below by the integrated weights,
the certified boundary terms, and the remaining trivial-zero action. -/
theorem quarter_principal_lower_656 (hRH : RiemannHypothesis) {a b r : ℝ} (ha : 0 < a) (har : a ≤ r)
    (hrb : r ≤ b) (hr : r ∈ Set.Icc 322 328) :
    let X := r ^ 2
    let W := quarterWeight656 X
    let S := fun n : ℕ ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) X n).re
    4 * (∫ t in (1 : ℝ)..X, W t) - (∫ t in (1 : ℝ)..X * Real.exp (21 / 8), W t) -
            4 * (9319732 / 100000000) * 70.4 / a +
          4 * (9319731 / 100000000) * (1837 / 1000) / b +
          3 * W 1 -
        0.002594 -
        quarterAbelAction656 X AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries -
        3 * Real.log (2 * Real.pi) * W 1 ≤
      4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) := by
  intro X W S
  have hX : 1 ≤ X := one_le_pow₀ ((by norm_num only : (1 : ℝ) ≤ 322).trans hr.1)
  have h := quarter_principal_explicit_656 hX
  dsimp only at h
  have hb := quarter_cutoff_boundary_656 ha har hrb hr
  have hz := quarter_zero_abel_bound_656 hRH hr
  dsimp only [X, W, S] at h ⊢
  linarith only [h, hb, hz]

end PseudoPrime.PrimeTestBounds.MillerRabin
