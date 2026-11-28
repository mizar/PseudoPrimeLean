/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAbel644
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseTail644
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LogZeroIntegration
import PseudoPrime.Analysis.MellinLogMoments
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAbel570
import PseudoPrime.Analysis.LogWeightedVariation
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExponentialLogWeightedSummation
import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedSummationByParts
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.IntegratedLogSplit
import PseudoPrime.LLS.RiemannWeightedErrorBounds

/-! # Convergence of the principal zero contribution in section 122 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The centered Abel action for the section 122 weight, evaluated at a
physical cutoff `X ≥ 1`. The terms at `X` and at one retain the endpoint
values of the input `F` after integration by parts. -/
noncomputable def quarterAbelAction644 (X : ℝ) (F : ℝ → ℝ) : ℝ :=
  let P := fun t ↦ t * deriv (quarterWeight644 X) t
  4 * (∫ t in (1 : ℝ)..X, F t * deriv P t) -
      (∫ t in (1 : ℝ)..X * Real.exp (2687 / 1000), F t * deriv P t) -
      4 * P X * F X +
    3 * P 1 * F 1

private theorem weight_smooth {X : ℝ} (hX : 0 < X) :
    ContDiffOn ℝ 2 (quarterWeight644 X) (Set.Ioi 0) := by
  intro t ht
  have ht' : 0 < t := ht
  have hs : ContDiffAt ℝ 2 Real.sqrt t := Real.contDiffAt_sqrt ht'.ne'
  apply ContDiffAt.contDiffWithinAt
  unfold quarterWeight644
  dsimp only
  fun_prop (disch := positivity)

private theorem abel_deriv_continuous {X b : ℝ} (hX : 0 < X) :
    ContinuousOn (deriv (fun t ↦ t * deriv (quarterWeight644 X) t)) (Set.Icc 1 b) := by
  have hp : ContDiffOn ℝ 1 (fun t ↦ t * deriv (quarterWeight644 X) t) (Set.Ioi 0) :=
    contDiffOn_id.mul ((weight_smooth hX).deriv_of_isOpen isOpen_Ioi (by decide))
  exact
    (hp.continuousOn_deriv_of_isOpen isOpen_Ioi (by decide)).mono
      (fun _ ht ↦ zero_lt_one.trans_le ht.1)

/-- The logarithmic zero ledger at rectangular truncation index `k`,
restricted to nontrivial zeros and evaluated at the physical argument `t`.
It supplies the finite input to the section 122 Abel action. -/
noncomputable def quarterZeroLedger644 (k : ℕ) (t : ℝ) : ℝ :=
  (∑
      ρ ∈
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZerosInAnyRectangle
              (AnalyticNumberTheory.RiemannZeta.unifiedRectangleLower k)
              (AnalyticNumberTheory.RiemannZeta.unifiedTauRectangleUpper 2 k)).filter
          (fun ρ ↦ ¬ρ.re < 0),
      AnalyticNumberTheory.RiemannZeta.riemannZetaLogZeroContribution t ρ).re

/-- At a physical cutoff `X ≥ 1`, the centered section 122 Abel actions of
the rectangular zero ledgers converge to the action of the full logarithmic
zero sum. The weighted integrals and the two endpoint values converge
separately. -/
theorem quarter_zero_abel_limit_644 {X : ℝ} (hX : 1 ≤ X) :
    Filter.Tendsto (fun k ↦ quarterAbelAction644 X (quarterZeroLedger644 k)) Filter.atTop
      (nhds
        (quarterAbelAction644 X
          (fun t ↦
            (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re))) := by
  have hx := zero_lt_one.trans_le hX
  have hb : X ≤ X * Real.exp (2687 / 1000) :=
    le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only))
  have hi :=
    AnalyticNumberTheory.RiemannZeta.weighted_zero_integral_limit le_rfl hX
      (abel_deriv_continuous hx)
  have ho :=
    AnalyticNumberTheory.RiemannZeta.weighted_zero_integral_limit le_rfl (hX.trans hb)
      (abel_deriv_continuous hx)
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
theorem quarter_zero_abel_lower_644 {X B : ℝ} (hX : 1 ≤ X)
    (hB : ∀ᶠ k : ℕ in Filter.atTop, B ≤ quarterAbelAction644 X (quarterZeroLedger644 k)) :
    B ≤
      quarterAbelAction644 X
        (fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) := by
  exact ge_of_tendsto (quarter_zero_abel_limit_644 hX) hB

/-- At the upper support endpoint the fifth-order zero kills both boundary terms. -/
theorem quarter_support_jet_644 {X : ℝ} (hx : 0 < X) :
    let B := X * Real.exp (2687 / 1000)
    quarterWeight644 X B = 0 ∧ deriv (quarterWeight644 X) B = 0 := by
  intro B
  let v := fun t : ℝ ↦ (107 / 100) * (2687 / 1000 - Real.log (t / X))
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
  have he : quarterWeight644 X = fun t ↦ v t ^ 5 * g t := by
    funext t
    dsimp only [quarterWeight644, v, g]
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
private theorem quarter_abel_congr_644 {X : ℝ} (hX : 1 ≤ X) {F G : ℝ → ℝ}
    (h : Set.EqOn F G (Set.Icc 1 (X * Real.exp (2687 / 1000)))) :
    quarterAbelAction644 X F = quarterAbelAction644 X G := by
  have hXB :=
    le_mul_of_one_le_right (zero_le_one.trans hX)
      (Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 2687 / 1000))
  have hB := hX.trans hXB
  dsimp only [quarterAbelAction644]
  rw [h ⟨hX, hXB⟩, h ⟨le_rfl, hB⟩]
  have inner :=
    intervalIntegral.integral_congr (μ := MeasureTheory.volume) (f := fun t ↦
      F t * deriv (fun u ↦ u * deriv (quarterWeight644 X) u) t) (g := fun t ↦
      G t * deriv (fun u ↦ u * deriv (quarterWeight644 X) u) t) (a := 1) (b := X)
      (fun t ht ↦ by
        rw [Set.uIcc_of_le hX] at ht
        exact
          congrArg (fun y ↦ y * deriv (fun u ↦ u * deriv (quarterWeight644 X) u) t)
            (h ⟨ht.1, ht.2.trans hXB⟩))
  have outer :=
    intervalIntegral.integral_congr (μ := MeasureTheory.volume) (f := fun t ↦
      F t * deriv (fun u ↦ u * deriv (quarterWeight644 X) u) t) (g := fun t ↦
      G t * deriv (fun u ↦ u * deriv (quarterWeight644 X) u) t) (a := 1) (b :=
      X * Real.exp (2687 / 1000))
      (fun t ht ↦ by
        rw [Set.uIcc_of_le hB] at ht
        exact congrArg (fun y ↦ y * deriv (fun u ↦ u * deriv (quarterWeight644 X) u) t) (h ht))
  rw [inner, outer]

/-- On the physical support, a finite sum of continuous inputs can be
evaluated by summing their individual Abel actions. -/
private theorem quarter_abel_finset_sum_644 {ι : Type*} {X : ℝ} (hX : 1 ≤ X) (S : Finset ι)
    (F : ι → ℝ → ℝ) (hF : ∀ i ∈ S, ContinuousOn (F i) (Set.Icc 1 (X * Real.exp (2687 / 1000)))) :
    quarterAbelAction644 X (fun t ↦ ∑ i ∈ S, F i t) = ∑ i ∈ S, quarterAbelAction644 X (F i) := by
  let B := X * Real.exp (2687 / 1000)
  let P := fun t ↦ t * deriv (quarterWeight644 X) t
  have hx := zero_lt_one.trans_le hX
  have hXB : X ≤ B := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only))
  have hQ : ContinuousOn (deriv P) (Set.Icc 1 B) := abel_deriv_continuous hx
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
private theorem quarter_sum_action_limit_644 {X : ℝ} (hX : 1 ≤ X) :
    Filter.Tendsto
      (fun m : ℕ ↦
        ∑
          ρ ∈
            (AnalyticNumberTheory.RiemannZeta.riemannZetaZerosInAnyRectangle
                  (AnalyticNumberTheory.RiemannZeta.unifiedRectangleLower m)
                  (AnalyticNumberTheory.RiemannZeta.unifiedTauRectangleUpper 2 m)).filter
              (fun ρ ↦ ¬ρ.re < 0),
          quarterAbelAction644 X
            (fun t ↦ (AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re))
      Filter.atTop
      (nhds
        (quarterAbelAction644 X
          (fun t ↦
            (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re))) := by
  apply (quarter_zero_abel_limit_644 hX).congr'
  filter_upwards with m
  let S :=
    (AnalyticNumberTheory.RiemannZeta.riemannZetaZerosInAnyRectangle
          (AnalyticNumberTheory.RiemannZeta.unifiedRectangleLower m)
          (AnalyticNumberTheory.RiemannZeta.unifiedTauRectangleUpper 2 m)).filter
      (fun ρ ↦ ¬ρ.re < 0)
  let F := fun (ρ : ℂ) (t : ℝ) ↦ (AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re
  change
    quarterAbelAction644 X
        (fun t ↦
          (∑ ρ ∈ S, AnalyticNumberTheory.RiemannZeta.riemannZetaLogZeroContribution t ρ).re) =
      ∑ ρ ∈ S, quarterAbelAction644 X (F ρ)
  rw [←
    quarter_abel_finset_sum_644 hX S F
      (fun ρ _ ↦
        Complex.continuous_re.comp_continuousOn
          (AnalyticNumberTheory.RiemannZeta.zero_term_continuous zero_lt_one ρ))]
  apply quarter_abel_congr_644 hX
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
private theorem quarter_abel_parts_644 {X : ℝ} (hX : 1 ≤ X) {F D H : ℝ → ℝ}
    (hF : ∀ t > 0, HasDerivAt F (D t) t) (hG : ∀ t > 0, HasDerivAt (fun u ↦ u * D u) (H t) t)
    (hD : ContinuousOn D (Set.Ioi 0)) (hH : ContinuousOn H (Set.Ioi 0)) :
    let B := X * Real.exp (2687 / 1000)
    let W := quarterWeight644 X
    quarterAbelAction644 X F =
      4 * (∫ t in (1 : ℝ)..X, H t * W t) - (∫ t in (1 : ℝ)..B, H t * W t) - 4 * (X * D X) * W X +
        3 * D 1 * W 1 := by
  intro B W
  let P := fun t ↦ t * deriv W t
  let G := fun t ↦ t * D t
  have hx := zero_lt_one.trans_le hX
  have hb : 1 ≤ B := hX.trans (le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only)))
  have hW := weight_smooth hx
  have hP : ContDiffOn ℝ 1 P (Set.Ioi 0) :=
    contDiffOn_id.mul (hW.deriv_of_isOpen isOpen_Ioi (by decide))
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
  obtain ⟨hwB, hpB⟩ := quarter_support_jet_644 hx
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
private theorem quarter_abel_cpow_644 {X : ℝ} (hX : 1 ≤ X) {ρ : ℂ} (hρ : ρ ≠ 0) (c : ℂ) :
    let B := X * Real.exp (2687 / 1000)
    let W := quarterWeight644 X
    let H := fun t : ℝ ↦ (c * ρ * ρ * (t : ℂ) ^ (ρ - 1)).re
    quarterAbelAction644 X (fun t ↦ (c * (t : ℂ) ^ ρ).re) =
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
  have h := quarter_abel_parts_644 hX (fun _ ht ↦ hpow c ht) hg (hc (c * ρ)) (hc (c * ρ * ρ))
  dsimp only at h
  change _ = _ - 4 * (c * ρ * (X : ℂ) ^ ρ).re * W X + 3 * (c * ρ).re * W 1
  rw [h, cpow_log_deriv (zero_lt_one.trans_le hX), Complex.ofReal_one, Complex.one_cpow, mul_one]

/-- The contribution of a nontrivial zero to the physical Abel action is
its signed power integral with two explicit boundary values. The zero's
multiplicity multiplies every term. -/
private theorem quarter_abel_zero_term_644 {X : ℝ} (hX : 1 ≤ X) {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (hre : 0 ≤ ρ.re) (hρ : ρ ≠ 0) :
    let B := X * Real.exp (2687 / 1000)
    let W := quarterWeight644 X
    let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
    let H := fun t : ℝ ↦ (-m * (t : ℂ) ^ (ρ - 1)).re
    quarterAbelAction644 X
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
  have h := quarter_abel_cpow_644 hX hρ c
  dsimp only at h
  simp only [h₂] at h
  simp only [h₁] at h
  exact h

/-- The physical Mellin integral and boundary contributions from one
nontrivial zero at cutoff X, including its multiplicity. -/
noncomputable def quarterZeroIntegral644 (X : ℝ) (ρ : ℂ) : ℝ :=
  let W := quarterWeight644 X
  let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
  let H := fun t : ℝ ↦ (-m * (t : ℂ) ^ (ρ - 1)).re
  4 * (∫ t in (1 : ℝ)..X, H t * W t) - (∫ t in (1 : ℝ)..X * Real.exp (2687 / 1000), H t * W t) -
      4 * (-m / ρ * (X : ℂ) ^ ρ).re * W X +
    3 * (-m / ρ).re * W 1

/-- The sum of the explicit Mellin and endpoint contributions converges to
the nontrivial-zero part of the section 122 principal Abel action. -/
theorem quarter_zero_integral_limit_644 {X : ℝ} (hX : 1 ≤ X) :
    Filter.Tendsto
      (fun m : ℕ ↦
        ∑
          ρ ∈
            (AnalyticNumberTheory.RiemannZeta.riemannZetaZerosInAnyRectangle
                  (AnalyticNumberTheory.RiemannZeta.unifiedRectangleLower m)
                  (AnalyticNumberTheory.RiemannZeta.unifiedTauRectangleUpper 2 m)).filter
              (fun ρ ↦ ¬ρ.re < 0),
          quarterZeroIntegral644 X ρ)
      Filter.atTop
      (nhds
        (quarterAbelAction644 X
          (fun t ↦
            (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re))) := by
  apply (quarter_sum_action_limit_644 hX).congr'
  filter_upwards with m
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hm := Finset.mem_filter.mp hρ
  have hz := (AnalyticNumberTheory.RiemannZeta.mem_riemannZetaZerosInAnyRectangle_iff.mp hm.1).2
  have hn : ρ ≠ 0 := by
    intro he
    rw [he, riemannZeta_zero] at hz
    norm_num only at hz
  exact quarter_abel_zero_term_644 hX hz (not_lt.mp hm.2) hn

/-- At positive arguments the physical weight at cutoff X is the unit
weight evaluated at the rescaled argument, divided by the square root of X. -/
private theorem quarter_weight_rescale {X u : ℝ} (hX : 0 < X) (hu : 0 < u) :
    quarterWeight644 X (u * X) = (Real.sqrt X)⁻¹ * quarterWeight644 1 u := by
  simp only [quarterWeight644, mul_div_cancel_right₀ _ hX.ne', div_one, Real.sqrt_mul hu.le,
    one_div, mul_inv_rev]
  ring

/-- Rescale each signed power integral in the physical zero contribution
to a unit-cutoff integral. Its lower limit is exactly the physical endpoint
one divided by the cutoff. -/
theorem quarter_power_integral_scale_644 {X b : ℝ} (hX : 0 < X) (hb : 1 ≤ b) (c ρ : ℂ) :
    (∫ t in (1 : ℝ)..b, (c * (t : ℂ) ^ (ρ - 1)).re * quarterWeight644 X t) =
      Real.sqrt X *
        ∫ u in (1 / X : ℝ)..b / X,
          (c * (X : ℂ) ^ (ρ - 1) * (u : ℂ) ^ (ρ - 1)).re * quarterWeight644 1 u := by
  let f := fun t : ℝ ↦ (c * (t : ℂ) ^ (ρ - 1)).re * quarterWeight644 X t
  have h := intervalIntegral.integral_comp_mul_right f (a := 1 / X) (b := b / X) hX.ne'
  rw [div_mul_cancel₀ _ hX.ne', div_mul_cancel₀ _ hX.ne', smul_eq_mul] at h
  have he :
    (∫ u in (1 / X : ℝ)..b / X, f (u * X)) =
      ∫ u in (1 / X : ℝ)..b / X,
        (Real.sqrt X)⁻¹ *
          ((c * (X : ℂ) ^ (ρ - 1) * (u : ℂ) ^ (ρ - 1)).re * quarterWeight644 1 u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (div_le_div_of_nonneg_right hb hX.le)] at hu
    have hu0 := (one_div_pos.mpr hX).trans_le hu.1
    dsimp only [f]
    rw [quarter_weight_rescale hX hu0, Complex.ofReal_mul, Complex.ofReal_mul_cpow hu0.le X,
      show c * ((u : ℂ) ^ (ρ - 1) * (X : ℂ) ^ (ρ - 1)) = c * (X : ℂ) ^ (ρ - 1) * (u : ℂ) ^ (ρ - 1)
        by ring]
    ring
  rw [he, intervalIntegral.integral_const_mul] at h
  have hh := congrArg (fun y : ℝ ↦ X * y) h
  rw [mul_inv_cancel_left₀ hX.ne'] at hh
  have hs : X * (Real.sqrt X)⁻¹ = Real.sqrt X := by
    rw [← div_eq_mul_inv]
    apply (div_eq_iff (Real.sqrt_pos.mpr hX).ne').mpr
    rw [← sq, Real.sq_sqrt hX.le]
  rw [← mul_assoc, hs] at hh
  exact hh.symm

/-- In the zero coefficient both integrals use the same unit-cutoff
integrand, with upper limits one and the exponential support endpoint. -/
private theorem quarter_zero_integral_scale_644 {X : ℝ} (hX : 1 ≤ X) (ρ : ℂ) :
    let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
    let F := fun u : ℝ ↦ (-m * (X : ℂ) ^ (ρ - 1) * (u : ℂ) ^ (ρ - 1)).re * quarterWeight644 1 u
    quarterZeroIntegral644 X ρ =
      4 * (Real.sqrt X * ∫ u in (1 / X : ℝ)..1, F u) -
          (Real.sqrt X * ∫ u in (1 / X : ℝ)..Real.exp (2687 / 1000), F u) -
          4 * (-m / ρ * (X : ℂ) ^ ρ).re * quarterWeight644 X X +
        3 * (-m / ρ).re * quarterWeight644 X 1 := by
  dsimp only [quarterZeroIntegral644]
  have hx := zero_lt_one.trans_le hX
  have hb :=
    hX.trans
      (le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 2687 / 1000)))
  rw [quarter_power_integral_scale_644 hx hX, quarter_power_integral_scale_644 hx hb,
    div_self hx.ne', mul_div_cancel_left₀ _ hx.ne']

private theorem unit_weight_power {u : ℝ} (hu : 0 < u) :
    quarterWeight644 1 u =
      (107 / 100 : ℝ) ^ 5 * Real.exp (-(2687 / 1000 * (107 / 100))) / 120 *
        (u ^ (57 / 100 : ℝ) * (2687 / 1000 - Real.log u) ^ 5) := by
  unfold quarterWeight644
  dsimp only
  rw [div_one, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hu, Real.rpow_def_of_pos hu]
  have he :
    Real.exp (-(107 / 100 * (2687 / 1000 - Real.log u))) =
      Real.exp (-(2687 / 1000 * (107 / 100))) *
        (Real.exp (Real.log u * (57 / 100)) * Real.exp (Real.log u * (1 / 2))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  field_simp [Real.exp_ne_zero]

/-- A complex power times the unit weight is integrable down to zero
whenever the effective Mellin exponent has positive real part. -/
private theorem quarter_power_integrable_zero_644 {ρ : ℂ} (hρ : 0 < ρ.re + 57 / 100) (c : ℂ) :
    IntervalIntegrable (fun u : ℝ ↦ (c * (u : ℂ) ^ (ρ - 1)).re * quarterWeight644 1 u)
      MeasureTheory.volume 0 1 := by
  let C := (107 / 100 : ℝ) ^ 5 * Real.exp (-(2687 / 1000 * (107 / 100))) / 120
  have hC : 0 ≤ C := by
    dsimp only [C]; positivity
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
  have hi := ((Analysis.shifted_log_moment 5 (2687 / 1000) hρ).1.const_mul (‖c‖ * C))
  apply hi.mono'
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
    intro u hu
    have hp := Complex.continuousAt_ofReal_cpow_const u (ρ - 1) (Or.inr hu.1.ne')
    have hW : ContinuousOn (quarterWeight644 1) (Set.Ioi 0) :=
      (weight_smooth (X := 1) zero_lt_one).continuousOn
    have hw := (hW u hu.1).continuousAt (isOpen_Ioi.mem_nhds hu.1)
    exact
      ((Complex.continuous_re.continuousAt.comp (continuousAt_const.mul hp)).mul
          hw).continuousWithinAt
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    have hl : 0 ≤ 2687 / 1000 - Real.log u := by linarith only [Real.log_nonpos hu.1.le hu.2]
    have hw : 0 ≤ quarterWeight644 1 u := by
      rw [unit_weight_power hu.1]
      exact mul_nonneg hC (mul_nonneg (Real.rpow_nonneg hu.1.le _) (pow_nonneg hl _))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
    calc
      _ ≤ ‖c * (u : ℂ) ^ (ρ - 1)‖ * quarterWeight644 1 u :=
        mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) hw
      _ = _ := by
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu.1, Complex.sub_re, Complex.one_re,
          unit_weight_power hu.1]
        rw [show ρ.re + 57 / 100 - 1 = (ρ.re - 1) + 57 / 100 by ring, Real.rpow_add hu.1]
        ring

/-- Extending both scaled zero integrals to zero subtracts exactly three
times the omitted lower integral, since both use the same integrand. -/
private theorem quarter_extend_integrals_644 {X : ℝ} (hX : 1 ≤ X) {ρ : ℂ} (hρ : 0 < ρ.re + 57 / 100)
    (c : ℂ) :
    let F := fun u : ℝ ↦ (c * (u : ℂ) ^ (ρ - 1)).re * quarterWeight644 1 u
    4 * (∫ u in (1 / X : ℝ)..1, F u) - (∫ u in (1 / X : ℝ)..Real.exp (2687 / 1000), F u) =
      4 * (∫ u in (0 : ℝ)..1, F u) - (∫ u in (0 : ℝ)..Real.exp (2687 / 1000), F u) -
        3 * (∫ u in (0 : ℝ)..1 / X, F u) := by
  intro F
  have hx := zero_lt_one.trans_le hX
  have ha : 0 < 1 / X := one_div_pos.mpr hx
  have ha1 : 1 / X ≤ 1 := by
    rw [one_div]; exact inv_le_one_of_one_le₀ hX
  have h0 : IntervalIntegrable F MeasureTheory.volume 0 (1 / X) :=
    (quarter_power_integrable_zero_644 hρ c).mono_set
      (by
        rw [Set.uIcc_of_le ha.le, Set.uIcc_of_le zero_le_one]
        exact Set.Icc_subset_Icc_right ha1)
  have hi {b : ℝ} (hb : 1 ≤ b) : IntervalIntegrable F MeasureTheory.volume (1 / X) b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (ha1.trans hb)]
    intro u hu
    have hu0 := ha.trans_le hu.1
    have hp := Complex.continuousAt_ofReal_cpow_const u (ρ - 1) (Or.inr hu0.ne')
    have hw : ContinuousOn (quarterWeight644 1) (Set.Ioi 0) :=
      (weight_smooth (X := 1) zero_lt_one).continuousOn
    exact
      ((Complex.continuous_re.continuousAt.comp (continuousAt_const.mul hp)).mul
          ((hw u hu0).continuousAt (isOpen_Ioi.mem_nhds hu0))).continuousWithinAt
  rw [← intervalIntegral.integral_add_adjacent_intervals h0 (hi le_rfl), ←
    intervalIntegral.integral_add_adjacent_intervals h0 (hi (Real.one_le_exp (by norm_num only)))]
  ring

/-- The zero contribution is the difference of two moments starting at
zero, the common omitted integral, and its explicit boundary terms. -/
private theorem quarter_zero_integral_extended_644 {X : ℝ} (hX : 1 ≤ X) {ρ : ℂ}
    (hρ : 0 < ρ.re + 57 / 100) :
    let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
    let F := fun u : ℝ ↦ (-m * (X : ℂ) ^ (ρ - 1) * (u : ℂ) ^ (ρ - 1)).re * quarterWeight644 1 u
    quarterZeroIntegral644 X ρ =
      Real.sqrt X *
            (4 * (∫ u in (0 : ℝ)..1, F u) - (∫ u in (0 : ℝ)..Real.exp (2687 / 1000), F u) -
              3 * (∫ u in (0 : ℝ)..1 / X, F u)) -
          4 * (-m / ρ * (X : ℂ) ^ ρ).re * quarterWeight644 X X +
        3 * (-m / ρ).re * quarterWeight644 X 1 := by
  intro m F
  have hs := quarter_zero_integral_scale_644 hX ρ
  have he := quarter_extend_integrals_644 hX hρ (-m * (X : ℂ) ^ (ρ - 1))
  dsimp only at hs he
  rw [hs]
  have hm := congrArg (fun y : ℝ ↦ Real.sqrt X * y) he
  change Real.sqrt X * _ = Real.sqrt X * _ at hm
  dsimp only [F, m] at *
  linarith only [hm]

/-- The zero moment up to a positive cutoff is a six-term rational function of the
effective Mellin exponent, multiplied by the fixed kernel normalization. -/
private theorem quarter_mellin_moment_644 {ρ : ℂ} (hρ : 0 < ρ.re + 57 / 100) (c : ℂ) {y : ℝ}
    (hy : 0 < y) :
    let s := ρ + (57 / 100 : ℂ)
    (∫ u in (0 : ℝ)..y, (c * (u : ℂ) ^ (ρ - 1)).re * quarterWeight644 1 u) =
      ((107 / 100 : ℝ) ^ 5 * Real.exp (-(2687 / 1000 * (107 / 100))) / 120) *
        (c *
            ((y : ℂ) ^ s *
              (∑ j ∈ Finset.range 6,
                (((5 : ℕ).choose j : ℂ) * ((2687 / 1000 - Real.log y : ℝ) : ℂ) ^ (5 - j)) *
                  ((j.factorial : ℂ) / s ^ (j + 1))))).re := by
  intro s
  have hs : 0 < s.re := by
    dsimp only [s]
    norm_num only [Complex.add_re, Complex.div_ofNat_re]
    exact hρ
  let f := fun u : ℝ ↦ (u : ℂ) ^ (s - 1) * ((2687 / 1000 - Real.log u : ℝ) : ℂ) ^ 5
  have hm := Analysis.complex_log_moment_cutoff 5 (2687 / 1000) hs hy
  rw [intervalIntegral.integral_of_le hy.le] at hm
  have hi : MeasureTheory.IntegrableOn f (Set.Ioc 0 y) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hy.le).1
      (Analysis.complex_log_moment_integrable 5 (2687 / 1000) hs hy)
  let C := (107 / 100 : ℝ) ^ 5 * Real.exp (-(2687 / 1000 * (107 / 100))) / 120
  rw [intervalIntegral.integral_of_le hy.le]
  have hw :
    (∫ u in Set.Ioc (0 : ℝ) y, (c * (u : ℂ) ^ (ρ - 1)).re * quarterWeight644 1 u) =
      ∫ u in Set.Ioc (0 : ℝ) y, C * (c * f u).re := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    have hpow : (u : ℂ) ^ (s - 1) = (u : ℂ) ^ (ρ - 1) * ((u ^ (57 / 100 : ℝ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hu.1.le, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu.1.ne')]
      congr 1
      dsimp only [s]
      push_cast
      ring
    dsimp only [f]
    rw [unit_weight_power hu.1, hpow, ← Complex.ofReal_pow]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
    dsimp only [C]
    ring
  rw [hw, MeasureTheory.integral_const_mul]
  have hr := integral_re (hi.const_mul c)
  simp only [RCLike.re_eq_complex_re] at hr
  rw [hr, MeasureTheory.integral_const_mul]
  change C * (c * ∫ u in Set.Ioc (0 : ℝ) y, f u).re = _
  rw [show (∫ u in Set.Ioc (0 : ℝ) y, f u) = _ from hm]

/-- The six logarithmic moments at a positive endpoint y form the
polynomial in inverse powers of the effective exponent s. -/
noncomputable def quarterMoment644 (s : ℂ) (y : ℝ) : ℂ :=
  (y : ℂ) ^ s *
    ∑ j ∈ Finset.range 6,
      (((5 : ℕ).choose j : ℂ) * ((2687 / 1000 - Real.log y : ℝ) : ℂ) ^ (5 - j)) *
        ((j.factorial : ℂ) / s ^ (j + 1))

/-- Evaluate the physical zero coefficient by finite moments at the unit
cutoff, support endpoint and omitted lower endpoint. -/
theorem quarter_zero_integral_formula_644 {X : ℝ} (hX : 1 ≤ X) {ρ : ℂ} (hρ : 0 < ρ.re + 57 / 100) :
    let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
    let c := -m * (X : ℂ) ^ (ρ - 1)
    let s := ρ + (57 / 100 : ℂ)
    let C := (107 / 100 : ℝ) ^ 5 * Real.exp (-(2687 / 1000 * (107 / 100))) / 120
    quarterZeroIntegral644 X ρ =
      Real.sqrt X * C *
            (c *
                (4 * quarterMoment644 s 1 - quarterMoment644 s (Real.exp (2687 / 1000)) -
                  3 * quarterMoment644 s (1 / X))).re -
          4 * (-m / ρ * (X : ℂ) ^ ρ).re * quarterWeight644 X X +
        3 * (-m / ρ).re * quarterWeight644 X 1 := by
  intro m c s C
  have h := quarter_zero_integral_extended_644 hX hρ
  have hM {y : ℝ} (hy : 0 < y) :
    (∫ u in (0 : ℝ)..y, (c * (u : ℂ) ^ (ρ - 1)).re * quarterWeight644 1 u) =
      C * (c * quarterMoment644 s y).re :=
    quarter_mellin_moment_644 hρ c hy
  change quarterZeroIntegral644 X ρ = _ at h
  rw [h, hM zero_lt_one, hM (Real.exp_pos _), hM (one_div_pos.mpr (zero_lt_one.trans_le hX))]
  have hscale (a : ℝ) (z : ℂ) : (c * ((a : ℂ) * z)).re = a * (c * z).re := by
    rw [← mul_assoc, mul_comm c, mul_assoc]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hlinear (A B D : ℂ) :
    (c * (4 * A - B - 3 * D)).re = 4 * (c * A).re - (c * B).re - 3 * (c * D).re := by
    simp only [mul_sub, Complex.sub_re]
    exact congrArg₂ (· - ·) (congrArg (· - (c * B).re) (hscale 4 A)) (hscale 3 D)
  rw [hlinear]
  ring

/-- At the exponential endpoint the logarithmic shift vanishes and only
the highest inverse power contributes to the full-support Mellin moment. -/
theorem quarter_moment_support_644 (s : ℂ) :
    quarterMoment644 s (Real.exp (2687 / 1000)) =
      (Real.exp (2687 / 1000) : ℂ) ^ s * (120 / s ^ 6) := by
  unfold quarterMoment644
  norm_num only [Real.log_exp, sub_self, Complex.ofReal_zero, Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.reduceSub, Nat.reduceAdd, zero_pow, pow_zero, Nat.factorial,
    Nat.choose_self, Nat.cast_one, Nat.cast_ofNat, zero_mul, mul_zero, one_mul, zero_add,
    Nat.reduceMul]

/-- Normalize the cutoff power so its modulus is one on the critical line. -/
private theorem cutoff_phase_mul {X : ℝ} (hX : 0 < X) (ρ : ℂ) :
    (Real.sqrt X : ℂ) * (X : ℂ) ^ (ρ - 1) = (X : ℂ) ^ ρ / (Real.sqrt X : ℂ) := by
  apply (eq_div_iff (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne')).mpr
  calc
    _ = ((Real.sqrt X : ℂ) * (Real.sqrt X : ℂ)) * (X : ℂ) ^ (ρ - 1) := by ring
    _ = (X : ℂ) ^ (1 : ℂ) * (X : ℂ) ^ (ρ - 1) := by
      rw [Complex.cpow_one, ← Complex.ofReal_mul, ← sq, Real.sq_sqrt hX.le]
    _ = (X : ℂ) ^ ρ := by
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hX.ne')]
      congr 1
      ring

/-- The radius-independent coefficient multiplying the critical-line
cutoff phase. The two full moments and the upper boundary enter together. -/
noncomputable def quarterMellinPhase644 (ρ : ℂ) : ℂ :=
  let s := ρ + (57 / 100 : ℂ)
  let C := ((107 / 100 : ℝ) ^ 5 * Real.exp (-(2687 / 1000 * (107 / 100))) / 120 : ℝ)
  4 * (quarterWeight644 1 1 : ℂ) / ρ -
    (C : ℂ) * (4 * quarterMoment644 s 1 - quarterMoment644 s (Real.exp (2687 / 1000)))

/-- Split a zero coefficient into its normalized phase times a fixed kernel
and two corrections from the physical lower cutoff. -/
theorem quarter_zero_phase_split_644 {X : ℝ} (hX : 1 ≤ X) {ρ : ℂ} (hρ : 0 < ρ.re + 57 / 100) :
    let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
    let p := (X : ℂ) ^ ρ / (Real.sqrt X : ℂ)
    let C := ((107 / 100 : ℝ) ^ 5 * Real.exp (-(2687 / 1000 * (107 / 100))) / 120 : ℝ)
    quarterZeroIntegral644 X ρ =
      (m * p * quarterMellinPhase644 ρ).re +
        3 * C * (m * p * quarterMoment644 (ρ + 57 / 100) (1 / X)).re +
        3 * (-m / ρ).re * quarterWeight644 X 1 := by
  intro m p C
  have hx := zero_lt_one.trans_le hX
  have hp := cutoff_phase_mul hx ρ
  have hw := quarter_weight_rescale hx (u := 1) zero_lt_one
  rw [one_mul] at hw
  have h := quarter_zero_integral_formula_644 hX hρ
  dsimp only at h
  rw [h, hw]
  let A :=
    4 * quarterMoment644 (ρ + 57 / 100) 1 - quarterMoment644 (ρ + 57 / 100) (Real.exp (2687 / 1000))
  let D := quarterMoment644 (ρ + 57 / 100) (1 / X)
  let w := quarterWeight644 1 1
  change
    Real.sqrt X * C * (-m * (X : ℂ) ^ (ρ - 1) * (A - 3 * D)).re -
          4 * (-m / ρ * (X : ℂ) ^ ρ).re * ((Real.sqrt X)⁻¹ * w) +
        3 * (-m / ρ).re * quarterWeight644 X 1 =
      (m * p * (4 * (w : ℂ) / ρ - (C : ℂ) * A)).re + 3 * C * (m * p * D).re +
        3 * (-m / ρ).re * quarterWeight644 X 1
  have hre (a : ℝ) (z : ℂ) : ((a : ℂ) * z).re = a * z.re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have h₁ :
    ((Real.sqrt X : ℂ) * (-m * (X : ℂ) ^ (ρ - 1) * (A - 3 * D))) = -m * p * (A - 3 * D) := by
    dsimp only [p]
    rw [← hp]
    ring
  have h₂ : (((Real.sqrt X)⁻¹ : ℝ) : ℂ) * (-m / ρ * (X : ℂ) ^ ρ) = -m / ρ * p := by
    dsimp only [p]
    rw [Complex.ofReal_inv]
    ring
  have hr₁ := congrArg Complex.re h₁
  have hr₂ := congrArg Complex.re h₂
  rw [hre] at hr₁ hr₂
  have he :
    (m * p * (4 * (w : ℂ) / ρ - (C : ℂ) * A)).re =
      -4 * w * (-m / ρ * p).re - C * (m * p * A).re := by
    rw [mul_sub, Complex.sub_re]
    congr 1
    · rw [← hre (-4 * w)]
      congr 1
      push_cast
      ring
    · rw [← hre C]
      congr 1
      ring
  have hf : (-m * p * (A - 3 * D)).re = -(m * p * A).re + 3 * (m * p * D).re := by
    rw [← hre (3 : ℝ), ← Complex.neg_re, ← Complex.add_re]
    congr 1
    push_cast
    ring
  rw [he]
  rw [hf] at hr₁
  calc
    _ =
        C * ((Real.sqrt X) * (-m * (X : ℂ) ^ (ρ - 1) * (A - 3 * D)).re) -
            4 * w * ((Real.sqrt X)⁻¹ * (-m / ρ * (X : ℂ) ^ ρ).re) +
          3 * (-m / ρ).re * quarterWeight644 X 1 :=
      by ring
    _ = _ := by
      rw [hr₁, hr₂]; ring

private theorem rational_phase_identity {w s : ℂ} (hw : w ≠ 0) (hs : s ≠ 0)
    (he : s = w + 57 / 100) :
    (2687 / 1000 : ℂ) ^ 5 / w - quarterMoment644 s 1 =
      ∑ j ∈ Finset.range 6, (quarterPhaseCoeff644 j : ℂ) / (w * s ^ (j + 1)) := by
  unfold quarterMoment644 quarterPhaseCoeff644
  norm_num only [Complex.ofReal_one, Complex.one_cpow, one_mul, Real.log_one, sub_zero,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff,
    ite_true, ite_false, Nat.choose, Nat.factorial, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_zero, zero_add, add_zero, zero_mul, mul_zero, pow_zero, pow_one, mul_one,
    Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_ofNat, Complex.ofReal_zero, Complex.ofReal_one]
  field_simp [hw, hs]
  rw [he]
  ring

private theorem support_phase_identity (t : ℝ) :
    (Real.exp (2687 / 1000) : ℂ) ^ ((107 / 100 : ℂ) + Complex.I * t) =
      (Real.exp ((107 / 100) * (2687 / 1000)) : ℂ) *
        Complex.exp (Complex.I * ((2687 / 1000 : ℝ) * t : ℝ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)), ←
    Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

/-- On the critical line, the exact Mellin phase coefficient equals the
kernel used by the certified four-interval lower bounds. The rational
parts share the derivative coefficients and the support term gives the
shift by `2687/1000`. -/
theorem quarter_mellin_phase_eq_644 (t : ℝ) :
    quarterMellinPhase644 ((1 / 2 : ℂ) + Complex.I * t) = quarterPhaseKernel644 t := by
  let w : ℂ := 1 / 2 + Complex.I * t
  let s : ℂ := 107 / 100 + Complex.I * t
  let C : ℝ := (107 / 100) ^ 5 * Real.exp (-(107 / 100) * (2687 / 1000)) / 120
  have hws : s = w + 57 / 100 := by
    dsimp only [s, w]; ring
  have hw : w ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    norm_num only [w, Complex.add_re, Complex.div_ofNat_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re,
      Complex.one_re, ← Complex.ofReal_ofNat, Complex.ofReal_re] at h'
  have hs : s ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    norm_num only [s, Complex.add_re, Complex.div_ofNat_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re,
      Complex.one_re, ← Complex.ofReal_ofNat, Complex.ofReal_re] at h'
    rw [← Complex.ofReal_ofNat (n := 107), Complex.ofReal_re] at h'
    norm_num only at h'
  have hu : quarterWeight644 1 1 = C * (2687 / 1000) ^ 5 := by
    rw [unit_weight_power zero_lt_one, Real.one_rpow, Real.log_one, sub_zero, one_mul]
    dsimp only [C]
    rw [mul_comm (2687 / 1000 : ℝ) (107 / 100), neg_mul]
  have hS :
    (C : ℂ) * quarterMoment644 s (Real.exp (2687 / 1000)) =
      (107 / 100 : ℂ) ^ 5 * Complex.exp (Complex.I * ((2687 / 1000 : ℝ) * t : ℝ)) / s ^ 6 := by
    rw [quarter_moment_support_644, show s = _ from rfl, support_phase_identity]
    dsimp only [C]
    push_cast
    simp only [neg_mul]
    let z : ℂ := (107 / 100) * (2687 / 1000)
    have hz : Complex.exp (-z) * Complex.exp z = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    change
      (107 / 100 : ℂ) ^ 5 * Complex.exp (-z) / 120 *
          (Complex.exp z * Complex.exp _ * (120 / s ^ 6)) =
        _
    calc
      _ =
          (Complex.exp (-z) * Complex.exp z) *
            ((107 / 100 : ℂ) ^ 5 * Complex.exp (Complex.I * ((2687 / 1000 : ℝ) * t : ℝ)) / s ^ 6) :=
        by
        push_cast; ring
      _ = _ := by
        rw [hz, one_mul]; push_cast; rfl
  unfold quarterMellinPhase644 quarterPhaseKernel644
  dsimp only
  rw [mul_comm (2687 / 1000 : ℝ) (107 / 100), ← neg_mul]
  change
    4 * (quarterWeight644 1 1 : ℂ) / w -
        (C : ℂ) *
          (4 * quarterMoment644 (w + 57 / 100) 1 -
            quarterMoment644 (w + 57 / 100) (Real.exp (2687 / 1000))) =
      ((4 * C : ℝ) : ℂ) * (∑ j ∈ Finset.range 6, (quarterPhaseCoeff644 j : ℂ) / (w * s ^ (j + 1))) +
        (107 / 100 : ℂ) ^ 5 * Complex.exp (Complex.I * ((2687 / 1000 : ℝ) * t : ℝ)) / s ^ 6
  rw [← hws, hu, mul_sub, sub_sub_eq_add_sub, hS]
  rw [← rational_phase_identity hw hs hws]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

/-- Integrating the second logarithmic derivative against one logarithmic atom
recovers the weight at v, with both endpoint terms at b. -/
private theorem quarter_log_atom_644 {X v b : ℝ} (hX : 0 < X) (hv : 0 < v) (hb : v ≤ b) :
    let W := quarterWeight644 X
    let P := fun t ↦ t * deriv W t
    W v = (∫ t in v..b, Real.log (t / v) * deriv P t) - Real.log (b / v) * P b + W b := by
  intro W P
  have hw := weight_smooth hX
  have hp : ContDiffOn ℝ 1 P (Set.Ioi 0) :=
    contDiffOn_id.mul (hw.deriv_of_isOpen isOpen_Ioi (by decide))
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
private theorem quarter_second_abel_644 {X b : ℝ} (hX : 0 < X) (hb : 0 ≤ b)
    (hs : Real.log (b / X) ≤ 2687 / 1000) :
    let W := quarterWeight644 X
    let P := fun t ↦ t * deriv W t
    (∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, (quarterKernel644.summand (1 : DirichletCharacter ℂ 1) X n).re) =
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
  rw [quarter_summand_644 hX hn0
      ((Real.log_le_log (div_pos hnr hX) (div_le_div_of_nonneg_right hnb hX.le)).trans hs)]
  have h := quarter_log_atom_644 hX hnr hnb
  change W n = _ at h
  change W n * _ = _
  rw [h]
  unfold AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm
  dsimp only [W, P]
  ring

/-- The second Abel formula for the supported principal prefix has a single integral
of the logarithmically weighted Mangoldt sum, with explicit boundary terms at b. -/
private theorem quarter_log_integral_644 {X b : ℝ} (hX : 0 < X) (hb : 1 ≤ b)
    (hs : Real.log (b / X) ≤ 2687 / 1000) :
    let W := quarterWeight644 X
    let P := fun t ↦ t * deriv W t
    (∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, (quarterKernel644.summand (1 : DirichletCharacter ℂ 1) X n).re) =
      (∫ t in (1 : ℝ)..b, AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * deriv P t) -
          P b * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum b +
        W b * Chebyshev.psi b := by
  intro W P
  have hw := weight_smooth hX
  have hp : ContDiffOn ℝ 1 P (Set.Ioi 0) :=
    contDiffOn_id.mul (hw.deriv_of_isOpen isOpen_Ioi (by decide))
  have hq :=
    (hp.continuousOn_deriv_of_isOpen isOpen_Ioi (by decide)).mono
      (show Set.Icc 1 b ⊆ Set.Ioi 0 from fun t ht ↦ zero_lt_one.trans_le ht.1)
  exact
    (quarter_second_abel_644 hX (zero_le_one.trans hb) hs).trans (by rw [log_sum_integral hb hq])

/-- Evaluate the linear and logarithmic main terms in the double Abel integral.
The free coefficient c can be specialized to log(2 pi) for the centered remainder. -/
private theorem quarter_centering_integral_644 {X b : ℝ} (hx : 0 < X) (hb : 1 ≤ b) (c : ℝ) :
    let W := quarterWeight644 X
    let P := fun t ↦ t * deriv W t
    (∫ t in (1 : ℝ)..b, (t - c * Real.log t) * deriv P t) =
      (b - c * Real.log b) * P b - (b - c) * W b - P 1 + (1 - c) * W 1 +
        ∫ t in (1 : ℝ)..b, W t := by
  intro W P
  have hw := weight_smooth hx
  have hp : ContDiffOn ℝ 1 P (Set.Ioi 0) :=
    contDiffOn_id.mul (hw.deriv_of_isOpen isOpen_Ioi (by decide))
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
private theorem quarter_centered_prefix_644 {X b : ℝ} (hx : 0 < X) (hb : 1 ≤ b)
    (hs : Real.log (b / X) ≤ 2687 / 1000) (c : ℝ) :
    let W := quarterWeight644 X
    let P := fun t ↦ t * deriv W t
    let E := fun t ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - (t - c * Real.log t)
    (∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, (quarterKernel644.summand (1 : DirichletCharacter ℂ 1) X n).re) =
      (∫ t in (1 : ℝ)..b, W t) + (∫ t in (1 : ℝ)..b, E t * deriv P t) - P b * E b +
            W b * (Chebyshev.psi b - b + c) -
          P 1 +
        (1 - c) * W 1 := by
  intro W P E
  have hp : ContDiffOn ℝ 1 P (Set.Ioi 0) :=
    contDiffOn_id.mul ((weight_smooth hx).deriv_of_isOpen isOpen_Ioi (by decide))
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
  have hh := quarter_log_integral_644 hx hb hs
  have hc := quarter_centering_integral_644 hx hb c
  dsimp only [E, W, P] at *
  simp_rw [sub_mul (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum _) _ _]
  rw [intervalIntegral.integral_sub (f := fun t ↦
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * deriv P t) (g := fun t ↦
      (t - c * Real.log t) * deriv P t) hi.intervalIntegrable hj.intervalIntegrable]
  linarith only [hh, hc]

/-- Center the difference of four principal prefixes and the full principal series.
The support jet vanishes at B, leaving a weighted difference of two remainder integrals,
one remainder value at X, and explicit boundary terms. -/
theorem quarter_centered_difference_644 {X : ℝ} (hX : 1 ≤ X) :
    let B := X * Real.exp (2687 / 1000)
    let S := fun n : ℕ ↦ (quarterKernel644.summand (1 : DirichletCharacter ℂ 1) X n).re
    let W := quarterWeight644 X
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
    hX.trans
      (le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 2687 / 1000)))
  have hlog : Real.log (B / X) = 2687 / 1000 := by
    dsimp only [B]
    rw [mul_div_cancel_left₀ _ hx.ne', Real.log_exp]
  have hf := quarter_centered_prefix_644 hx hb hlog.le c
  have hu :=
    quarter_centered_prefix_644 hx hX
      (by
        rw [div_self hx.ne', Real.log_one]; norm_num only)
      c
  obtain ⟨hw, hd⟩ := quarter_support_jet_644 hx
  dsimp only at hf hu
  rw [hd, hw, mul_zero, zero_mul, sub_zero, zero_mul, add_zero] at hf
  dsimp only [S, W, P, E, B]
  rw [quarter_principal_finite_644 hx, hf, hu]
  ring

/-- An additive constant in the centered explicit formula cancels exactly. -/
private theorem quarter_abel_const_644 {X : ℝ} (hX : 1 ≤ X) (c : ℝ) :
    quarterAbelAction644 X (fun _ ↦ c) = 0 := by
  let B := X * Real.exp (2687 / 1000)
  let P := fun t ↦ t * deriv (quarterWeight644 X) t
  have hx := zero_lt_one.trans_le hX
  have hb : 1 ≤ B := hX.trans (le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only)))
  have hP : ContDiffOn ℝ 1 P (Set.Ioi 0) :=
    contDiffOn_id.mul ((weight_smooth hx).deriv_of_isOpen isOpen_Ioi (by decide))
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
    rw [(quarter_support_jet_644 hx).2, mul_zero]
  change
    4 * (∫ t in (1 : ℝ)..X, c * deriv P t) - (∫ t in (1 : ℝ)..B, c * deriv P t) - 4 * P X * c +
        3 * P 1 * c =
      0
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hI hX, hI hb, hB]
  ring

/-- At and above one, the centered Mangoldt error is the real nontrivial-zero series
minus the trivial-zero series and the constant pole residue. This gives the
input for the section 122 Abel action on the interior of its support. -/
private theorem quarter_centered_zero_eq_644 {t : ℝ} (ht : 1 ≤ t) :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
        (t - Real.log (2 * Real.pi) * Real.log t) =
      (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re -
        AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries t -
        AnalyticNumberTheory.RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re := by
  rcases ht.eq_or_lt with he | hlt
  · subst t
    rw [AnalyticNumberTheory.RiemannZeta.log_weighted_exact_one]
    ring
  · rw [AnalyticNumberTheory.RiemannZeta.log_weighted_exact hlt]
    ring

/-- The section 122 Abel action can use the exact zero expansion on its
entire physical support, including the lower endpoint. -/
private theorem quarter_abel_zero_expansion_644 {X : ℝ} (hX : 1 ≤ X) :
    quarterAbelAction644 X
        (fun t ↦
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
            (t - Real.log (2 * Real.pi) * Real.log t)) =
      quarterAbelAction644 X
        (fun t ↦
          (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re -
            AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries t -
            AnalyticNumberTheory.RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re) := by
  exact quarter_abel_congr_644 hX (fun _ ht ↦ quarter_centered_zero_eq_644 ht.1)

/-- Continuous inputs on the physical support satisfy the integrability
conditions for subtracting their Abel actions. -/
private theorem quarter_abel_sub_644 {X : ℝ} (hX : 1 ≤ X) {F G : ℝ → ℝ}
    (hF : ContinuousOn F (Set.Icc 1 (X * Real.exp (2687 / 1000))))
    (hG : ContinuousOn G (Set.Icc 1 (X * Real.exp (2687 / 1000)))) :
    quarterAbelAction644 X (fun t ↦ F t - G t) =
      quarterAbelAction644 X F - quarterAbelAction644 X G := by
  let B := X * Real.exp (2687 / 1000)
  let P := fun t ↦ t * deriv (quarterWeight644 X) t
  have hx := zero_lt_one.trans_le hX
  have hXB : X ≤ B := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only))
  have hQ : ContinuousOn (deriv P) (Set.Icc 1 B) := abel_deriv_continuous hx
  have hI {H : ℝ → ℝ} (hH : ContinuousOn H (Set.Icc 1 B)) {b : ℝ} (hb : 1 ≤ b) (hbB : b ≤ B) :
    IntervalIntegrable (fun t ↦ H t * deriv P t) MeasureTheory.volume 1 b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hb).2
    exact ((hH.mul hQ).mono (Set.Icc_subset_Icc_right hbB)).integrableOn_Icc
  have hf₁ := hI hF hX hXB
  have hg₁ := hI hG hX hXB
  have hf₂ := hI hF (hX.trans hXB) le_rfl
  have hg₂ := hI hG (hX.trans hXB) le_rfl
  dsimp (config := { failIfUnchanged := false }) only [P, B] at hf₁ hg₁ hf₂ hg₂
  dsimp only [quarterAbelAction644]
  simp only [sub_mul, intervalIntegral.integral_sub hf₁ hg₁, intervalIntegral.integral_sub hf₂ hg₂]
  ring

/-- On the entire physical support, split the centered Mangoldt Abel action
into nontrivial and trivial zero contributions. The constant pole residue
cancels exactly. -/
theorem quarter_abel_zero_split_644 {X : ℝ} (hX : 1 ≤ X) :
    quarterAbelAction644 X
        (fun t ↦
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
            (t - Real.log (2 * Real.pi) * Real.log t)) =
      quarterAbelAction644 X
          (fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) -
        quarterAbelAction644 X
          AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries := by
  let Z := fun t : ℝ ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re
  let T := AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries
  let c := AnalyticNumberTheory.RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re
  have hz : ContinuousOn Z (Set.Icc 1 (X * Real.exp (2687 / 1000))) :=
    Complex.continuous_re.comp_continuousOn
      (AnalyticNumberTheory.RiemannZeta.zero_sum_continuous (b := X * Real.exp (2687 / 1000))
        (le_refl (1 : ℝ)))
  have ht : ContinuousOn T (Set.Icc 1 (X * Real.exp (2687 / 1000))) :=
    AnalyticNumberTheory.RiemannZeta.trivial_cont_closed (le_refl (1 : ℝ))
  rw [quarter_abel_zero_expansion_644 hX]
  change quarterAbelAction644 X (fun t ↦ (Z - T) t - c) = _
  rw [quarter_abel_sub_644 hX (hz.sub ht) (continuousOn_const (c := c)), quarter_abel_const_644 hX,
    sub_zero]
  exact quarter_abel_sub_644 hX hz ht

/-- For `X ≥ 1`, four principal prefixes minus the full principal sum
equal the integrated weight terms, the psi boundary, and the difference
of the nontrivial and trivial zero actions. The lower endpoint contributes
three times the weight at one. -/
theorem quarter_principal_explicit_644 {X : ℝ} (hX : 1 ≤ X) :
    let B := X * Real.exp (2687 / 1000)
    let S := fun n : ℕ ↦ (quarterKernel644.summand (1 : DirichletCharacter ℂ 1) X n).re
    let W := quarterWeight644 X
    4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) =
      4 * (∫ t in (1 : ℝ)..X, W t) - (∫ t in (1 : ℝ)..B, W t) +
          4 * W X * (Chebyshev.psi X - X + Real.log (2 * Real.pi)) +
          3 * W 1 +
          quarterAbelAction644 X
            (fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) -
        quarterAbelAction644 X AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries -
        3 * Real.log (2 * Real.pi) * W 1 := by
  intro B S W
  have h := quarter_centered_difference_644 hX
  dsimp only at h
  dsimp only [quarterAbelAction644] at ⊢
  have hz := quarter_abel_zero_split_644 hX
  dsimp only [quarterAbelAction644] at hz
  rw [LLS.logWeightedMangoldtSum_eq_zero_of_le_one (le_refl (1 : ℝ)), Real.log_one, mul_zero,
    sub_zero, zero_sub] at hz
  change 4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) = _
  rw [h]
  dsimp only [B, W]
  linarith only [hz]

end PseudoPrime.PrimeTestBounds.MillerRabin
