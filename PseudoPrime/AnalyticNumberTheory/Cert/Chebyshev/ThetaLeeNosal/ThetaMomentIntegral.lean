/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaMomentCells
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaMomentCells
import PseudoPrime.Analysis.PreciseLogTaylorBounds
public import PseudoPrime.Analysis.SincMomentTail
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SincTailAbel
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SincCountError
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SincTailAnchorRH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.IntegratedSincTail
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SincSmoothingWidth

/-! # Integrating the certified moment samples -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- The plain or logarithmically weighted integrand used in the Simpson sum. -/
noncomputable def momentIntegrand (b : Bool) : ℝ → ℝ :=
  Analysis.sincMomentNumerator *
    Analysis.momentWeightTerm 0 ((if b then 1 else 0 : ℚ) : ℝ) ((if b then 0 else 1 : ℚ) : ℝ)

/-- The shared sample array bounds both integrands at every node in the finite grid. -/
theorem momentIntegrand_node_le (b : Bool) (i : Fin 97) :
    momentIntegrand b (momentNode i) ≤ (momentSample b i : ℝ) := by
  cases b <;>
    simp only [momentIntegrand, Analysis.momentWeightTerm, Pi.mul_apply, Bool.false_eq_true,
      ite_false, ite_true, Rat.cast_zero, Rat.cast_one, pow_zero, Nat.factorial_one, Nat.cast_one,
      one_mul, zero_mul, mul_zero, zero_add, add_zero, Analysis.momentLogShift, sub_zero,
      ← mul_div_assoc, mul_one]
  · exact plainSample_le i
  · exact logSample_le i

/-- Summing all 48 real cell integrals is bounded by the certified rational budget. -/
theorem momentIntegral_sum_le (b : Bool) :
    (∑ i : Fin 48,
        ∫ x in (momentNode (momentCellIndex i 0) : ℝ)..(momentNode (momentCellIndex i 2) : ℝ),
          momentIntegrand b x) ≤
      (momentFiniteUpper b : ℝ) := by
  rw [momentFiniteUpper, Rat.cast_sum]
  apply Finset.sum_le_sum
  intro i _
  apply (momentCell_integral_le i (if b then 1 else 0) (if b then 0 else 1)).trans
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_sub]
  apply add_le_add_left
  apply
    mul_le_mul_of_nonneg_left _
      (div_nonneg (sub_nonneg.mpr (Rat.cast_le.mpr (momentNode_cell i).1.le)) (by norm_num only))
  apply add_le_add _ (momentIntegrand_node_le b _)
  exact
    add_le_add (momentIntegrand_node_le b _)
      (mul_le_mul_of_nonneg_left (momentIntegrand_node_le b _) (by norm_num only))

private noncomputable def boundary (k : ℕ) : ℝ :=
  (momentNode ⟨2 * k % 97, Nat.mod_lt _ (by decide)⟩ : ℝ)

private theorem boundary_pos (k : ℕ) : 0 < boundary k :=
  Rat.cast_pos.mpr ((show (0 : ℚ) < 2 / 5 by decide +kernel).trans_le (momentNode_range _).1)

/-- Positivity of both endpoints keeps the logarithm and reciprocal square continuous
on the closed interval, so the two moment integrands are interval integrable. -/
private theorem integrable_cell (b : Bool) (k : ℕ) :
    IntervalIntegrable (momentIntegrand b) MeasureTheory.volume (boundary k)
      (boundary (k + 1)) := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hp := (lt_min (boundary_pos k) (boundary_pos (k + 1))).trans_le hx.1
  unfold momentIntegrand Analysis.sincMomentNumerator Analysis.sineMajorant
    Analysis.momentWeightTerm
  fun_prop (disch :=
    first
    | exact hp.ne'
    | exact pow_ne_zero _ hp.ne')

/-- On the full interval from 2/5 to 16, the integral is at most the rational
Simpson budget. Adjacent intervals telescope across all 48 cells. -/
theorem momentIntegral_finite_le (b : Bool) :
    (∫ x in (2 / 5 : ℝ)..16, momentIntegrand b x) ≤ (momentFiniteUpper b : ℝ) := by
  have he :=
    intervalIntegral.sum_integral_adjacent_intervals (n := 48) (fun k _ ↦ integrable_cell b k)
  let g := fun k : ℕ ↦ ∫ x in boundary k..boundary (k + 1), momentIntegrand b x
  change ∑ k ∈ Finset.range 48, g k = _ at he
  rw [← Fin.sum_univ_eq_sum_range g] at he
  have hidx :
    ∀ i : Fin 48,
      2 * i.val % 97 = (momentCellIndex i 0).val ∧
        2 * (i.val + 1) % 97 = (momentCellIndex i 2).val := by
    decide +kernel
  have hleft : boundary 0 = 2 / 5 := by
    change (momentNode 0 : ℝ) = _
    rw [momentNode_ends.1, Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofNat]
  have hright : boundary 48 = 16 := by
    change (momentNode 96 : ℝ) = _
    exact_mod_cast momentNode_ends.2
  rw [← hleft, ← hright, ← he]
  apply le_trans (Finset.sum_le_sum (fun i _ ↦ ?_)) (momentIntegral_sum_le b)
  exact le_of_eq (by simp only [g, boundary, (hidx i).1, (hidx i).2])

/-- Adding the analytic tail allowance and the lower cutoff correction gives
the plain moment budget used by the zero-sum estimate. -/
theorem plainMoment_budget :
    Real.log (2 / 5) + (∫ x in (2 / 5 : ℝ)..16, momentIntegrand false x) +
        (2 / 3 + Analysis.sineMajorantShift) / 16 +
        (5 / 12) / 16 ^ 2 ≤
      748 / 1000 := by
  have hf : momentFiniteUpper false ≤ 16202 / 10000 := by decide +kernel
  have h := (momentIntegral_finite_le false).trans ((Rat.cast_le (K := ℝ)).mpr hf)
  have hl :=
    (Analysis.preciseLogCheck_sound (N := 2 / 5) (j := 0) (n := 24) (lo := -1) (hi := -9162 / 10000)
        (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] at hl h
  linarith only [hl, h, Analysis.sineMajorantShift_bounds.2]

/-- The logarithmic cutoff correction, finite integral, and analytic allowance
at sixteen fit the logarithmic moment budget. -/
theorem logMoment_budget :
    (Real.log (2 / 5)) ^ 2 / 2 + (∫ x in (2 / 5 : ℝ)..16, momentIntegrand true x) +
        (2 / 3 + Analysis.sineMajorantShift) * (Real.log 16 + 1) / 16 +
        (5 / 12) * Real.log 16 / 16 ^ 2 ≤
      73 / 100 := by
  have h :=
    (momentIntegral_finite_le true).trans ((Rat.cast_le (K := ℝ)).mpr momentFiniteUpper_bounds.2)
  have ha :=
    Analysis.preciseLogCheck_sound (N := 2 / 5) (j := 0) (n := 24) (lo := -917 / 1000) (hi := 0)
      (by decide +kernel)
  have hb :=
    (Analysis.preciseLogCheck_sound (N := 16) (j := 4) (n := 4) (lo := 0) (hi := 278 / 100)
        (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_zero] at h ha hb
  have hs :=
    mul_le_mul
      (show 2 / 3 + Analysis.sineMajorantShift ≤ (2 / 3 + 3 / 1000 : ℝ) by
        linarith only [Analysis.sineMajorantShift_bounds.2])
      (add_le_add_left hb 1) (by linarith only [Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 16)])
      (by norm_num only)
  nlinarith only [hs, h, hb,
    mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ Real.log (2 / 5) + 917 / 1000 by linarith only [ha.1])
      (show Real.log (2 / 5) - 917 / 1000 ≤ 0 by linarith only [ha.2])]

/-- The cutoff correction and the actual finite and infinite plain integrals
together satisfy the target moment bound. -/
theorem plainMoment_le :
    Real.log (2 / 5) + (∫ x in (2 / 5 : ℝ)..16, momentIntegrand false x) +
        (∫ x in Set.Ioi (16 : ℝ), Analysis.sincMomentNumerator x * (1 / x ^ 2)) ≤
      748 / 1000 := by
  linarith only [plainMoment_budget, Analysis.plainMoment_tail_le]

/-- The corrected logarithmic moment, including the actual improper tail,
satisfies the second target bound. -/
theorem logMoment_le :
    (Real.log (2 / 5)) ^ 2 / 2 + (∫ x in (2 / 5 : ℝ)..16, momentIntegrand true x) +
        (∫ x in Set.Ioi (16 : ℝ), Analysis.sincMomentNumerator x * (Real.log x / x ^ 2)) ≤
      73 / 100 := by
  linarith only [logMoment_budget, Analysis.logMoment_tail_le]

private theorem momentIntegrand_eq (b : Bool) (x : ℝ) :
    momentIntegrand b x =
      Analysis.sincMomentNumerator x * ((if b then Real.log x else 1) / x ^ 2) := by
  cases b <;>
    simp only [momentIntegrand, Analysis.momentWeightTerm, Pi.mul_apply, Bool.false_eq_true,
      ite_false, ite_true, Rat.cast_zero, Rat.cast_one, pow_zero, Nat.factorial_one, Nat.cast_one,
      one_mul, zero_mul, mul_zero, zero_add, add_zero, Analysis.momentLogShift, sub_zero]

private theorem momentIntegrable_parts (b : Bool) :
    IntervalIntegrable (momentIntegrand b) MeasureTheory.volume (2 / 5) 16 ∧
      MeasureTheory.IntegrableOn (momentIntegrand b) (Set.Ioi 16) := by
  constructor
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by norm_num only : (2 / 5 : ℝ) ≤ 16)] at hx
    have hp := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2 / 5) hx.1
    unfold momentIntegrand Analysis.sincMomentNumerator Analysis.sineMajorant
      Analysis.momentWeightTerm
    fun_prop (disch :=
      first
      | exact hp.ne'
      | exact pow_ne_zero _ hp.ne')
  · have hw :
      MeasureTheory.IntegrableOn (fun x : ℝ ↦ (if b then Real.log x else 1) / x ^ 2)
        (Set.Ioi 16) := by
      cases b
      · exact Analysis.plainWeight_integrable
      · exact Analysis.logWeight_integrable
    rw [show momentIntegrand b = _ from funext (momentIntegrand_eq b)]
    apply
      hw.bdd_mul (c := (Analysis.sincMomentAmplitude 0 : ℝ))
        (Analysis.contDiff_sincMomentNumerator 1).continuous.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    exact
      (Analysis.abs_iteratedDeriv_sincNumerator 0 x :
        |iteratedDeriv 0 _ x| ≤ (Analysis.sincMomentAmplitude 0 : ℝ))

private theorem momentIntegral_split (b : Bool) :
    (∫ x in Set.Ioi (2 / 5 : ℝ), momentIntegrand b x) =
      (∫ x in (2 / 5 : ℝ)..16, momentIntegrand b x) +
        ∫ x in Set.Ioi (16 : ℝ), momentIntegrand b x :=
  (intervalIntegral.integral_interval_add_Ioi' (momentIntegrable_parts b).1
      (momentIntegrable_parts b).2).symm

/-- Both corrected moments over the entire half-line satisfy the scalar certificate. -/
theorem momentIntegral_Ioi_bounds :
    Real.log (2 / 5) + (∫ x in Set.Ioi (2 / 5 : ℝ), momentIntegrand false x) ≤ 748 / 1000 ∧
      (Real.log (2 / 5)) ^ 2 / 2 + (∫ x in Set.Ioi (2 / 5 : ℝ), momentIntegrand true x) ≤
        73 / 100 := by
  rw [momentIntegral_split false, momentIntegral_split true, ← add_assoc, ← add_assoc]
  constructor
  · simpa only [momentIntegrand_eq, Bool.false_eq_true, ite_false] using plainMoment_le
  · simpa only [momentIntegrand_eq, ite_true] using logMoment_le

/-- At the scaled cutoff the smooth count density converges to a linear combination
of the two certified moments, with the scale retained in the logarithmic coefficient. -/
theorem densityMoment_tendsto {β a : ℝ} (hb : 0 < β) (ha : 0 < a) (hc : β * a = 2 / 5) :
    let I := fun b ↦ ∫ z in Set.Ioi (2 / 5 : ℝ), momentIntegrand b z
    Filter.Tendsto
      (fun t ↦
        ∫ x in a..t, (Real.log x - Real.log (2 * Real.pi)) / Real.pi * Analysis.sincTailWeight β x)
      Filter.atTop (nhds ((I true - Real.log (2 * Real.pi * β) * I false) / Real.pi)) := by
  intro I
  have hm (b : Bool) : MeasureTheory.IntegrableOn (momentIntegrand b) (Set.Ioi (2 / 5)) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num only : (2 / 5 : ℝ) ≤ 16)]
    exact (momentIntegrable_parts b).1.1.union (momentIntegrable_parts b).2
  have ht (b : Bool) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi (2 / 5) (hm b)
      (Filter.tendsto_id.const_mul_atTop hb)
  apply (((ht true).sub ((ht false).const_mul _)).div_const Real.pi).congr'
  filter_upwards [Filter.eventually_ge_atTop a] with t hat
  rw [RiemannZeta.sincTail_density_moments hb ha hat, hc]
  simp only [momentIntegrand_eq, Bool.false_eq_true, ite_false, ite_true, id_eq]

/-- For a nonnegative coefficient the corrected density limit inherits both upper bounds. -/
theorem densityMoment_le {c : ℝ} (hc : 0 ≤ c) :
    let I := fun b ↦ ∫ z in Set.Ioi (2 / 5 : ℝ), momentIntegrand b z
    (I true + c * I false) / Real.pi ≤
      (73 / 100 - (Real.log (2 / 5)) ^ 2 / 2 + c * (748 / 1000 - Real.log (2 / 5))) / Real.pi := by
  intro I
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  apply add_le_add (by linarith only [momentIntegral_Ioi_bounds.2] : I true ≤ _)
  exact mul_le_mul_of_nonneg_left (by linarith only [momentIntegral_Ioi_bounds.1]) hc

/-- At the actual middle-band scale, the corrected logarithmic and plain
moments contribute at most 0.73 plus 0.748 times the phase-grid parameter. -/
theorem middleMoment_le {L : ℝ} (hl : 35 / 2 ≤ L) (hr : L ≤ 53 / 2) :
    let q := 2 * L / 7 - 2 / 3
    let β := -Real.log (1 - q / Real.exp (L / 2)) / 2
    let I := fun b ↦ ∫ z in Set.Ioi (2 / 5 : ℝ), momentIntegrand b z
    (Real.log (2 / 5)) ^ 2 / 2 + I true +
        (-Real.log (2 * Real.pi * β)) * (Real.log (2 / 5) + I false) ≤
      73 / 100 + (748 / 1000) * (L / 2 - Real.log (Real.pi * q)) := by
  intro q β I
  have hc := RiemannZeta.sinc_log_coefficient hl hr
  have h := mul_le_mul_of_nonneg_left momentIntegral_Ioi_bounds.1 hc.1
  have h' := mul_le_mul_of_nonneg_right hc.2 (by norm_num only : (0 : ℝ) ≤ 748 / 1000)
  exact add_le_add momentIntegral_Ioi_bounds.2 ((h.trans h').trans_eq (mul_comm _ _))

/-- At the scaled cutoff the clamped zero sum equals its smooth endpoint,
the two fixed moments and the reciprocal correction, up to the quadratic count error. -/
theorem clampedTail_moments (hRH : RiemannHypothesis) {β T : ℝ} (hb : 0 < β) (hT : 100 ≤ T)
    (hc : β * T = 2 / 5) :
    let W := fun t : ℝ ↦ Analysis.sincWeight (β * t) / t
    let w := fun ρ : ℂ ↦
      if riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ T < |ρ.im| then
        (RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) * W |ρ.im|
      else 0
    let I := fun b ↦ ∫ z in Set.Ioi (2 / 5 : ℝ), momentIntegrand b z
    let M := (1 / Real.pi) * T * (Real.log T - Real.log (2 * Real.pi) - 1) + 7 / 4
    ∃ E : ℝ,
      |E| ≤ β ^ 2 * (57 * (16 + 7 / 5 * Real.log T) + 234 / 5) ∧
        RiemannZeta.zeroCount T * W T + ∑' ρ, w ρ =
          M * Analysis.sincTailWeight β T +
              (I true - Real.log (2 * Real.pi * β) * I false) / Real.pi -
            (E -
              ∫ t in Set.Ioi T, (2 * t⁻¹ ^ 3) * (∫ y in T..t, RiemannZeta.zeroCountError y)) := by
  intro W w I M
  have hp : 0 < T := lt_of_lt_of_le (by norm_num only) hT
  obtain ⟨E, hE, he⟩ := RiemannZeta.sincCountError_weight_limit hRH hb hT hc
  have hm := (RiemannZeta.sincTail_main_endpoint hb).const_sub (M * Analysis.sincTailWeight β T)
  rw [sub_zero] at hm
  refine ⟨E, hE, tendsto_nhds_unique (RiemannZeta.sincTail_integral_tendsto hRH hb hp hc.ge) ?_⟩
  apply ((hm.add (densityMoment_tendsto hb hp hc)).sub he).congr'
  filter_upwards [Filter.eventually_ge_atTop T] with R hR
  exact (RiemannZeta.sincTail_main_split hb hp hR).symm

/-- Adding the reciprocal head at the scaled cutoff cancels both the exact
count endpoint and the reciprocal discrepancy integral in the strict tail. -/
theorem reciprocalHead_tail_le (hRH : RiemannHypothesis) {β T : ℝ} (hb : 0 < β) (hT : 100 ≤ T)
    (hc : β * T = 2 / 5) :
    let w := fun ρ : ℂ ↦
      if riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ T < |ρ.im| then
        (RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          (Analysis.sincWeight (β * |ρ.im|) / |ρ.im|)
      else 0
    let I := fun b ↦ ∫ z in Set.Ioi (2 / 5 : ℝ), momentIntegrand b z
    RiemannZeta.zeroReciprocalSum T + ∑' ρ, w ρ ≤
      RiemannZeta.zeroReciprocalConstant +
        (Real.log T - Real.log (2 * Real.pi)) ^ 2 / (2 * Real.pi) +
        (I true - Real.log (2 * Real.pi * β) * I false) / Real.pi +
        β ^ 2 * (57 * (16 + 7 / 5 * Real.log T) + 234 / 5) := by
  intro w I
  obtain ⟨E, hE, he⟩ := clampedTail_moments hRH hb hT hc
  have hw : Analysis.sincWeight (β * T) = 1 := by
    simp only [Analysis.sincWeight, hc, le_refl, ite_true]
  rw [← Analysis.sincWeight_div_eq_tail hc.ge, hw] at he
  have ha := RiemannZeta.zeroReciprocalConstant_anchor hRH hT
  simp only [w, I, RiemannZeta.zeroCountError, div_eq_mul_inv, hw, one_mul] at ha he ⊢
  linarith only [he, ha, (abs_le.mp hE).1]

/-- Removing the height-100 head and adding the damping correction gives the
anchored numerical saving for the reciprocal head and the strict smooth tail. -/
theorem anchoredTail_moment_le (hRH : RiemannHypothesis) {β T : ℝ} (hb : 0 < β) (hT : 100 ≤ T)
    (hc : β * T = 2 / 5) :
    let w := fun ρ : ℂ ↦
      if riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ T < |ρ.im| then
        (RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          (Analysis.sincWeight (β * |ρ.im|) / |ρ.im|)
      else 0
    let I := fun b ↦ ∫ z in Set.Ioi (2 / 5 : ℝ), momentIntegrand b z
    RiemannZeta.zeroReciprocalSum T - RiemannZeta.zeroReciprocalSum 100 + ∑' ρ, w ρ +
        3 / 2 * RiemannZeta.ordinateTail 100 ≤
      (Real.log T - Real.log (2 * Real.pi)) ^ 2 / (2 * Real.pi) +
            (I true - Real.log (2 * Real.pi * β) * I false) / Real.pi -
          748 / 625 +
        β ^ 2 * (57 * (16 + 7 / 5 * Real.log T) + 234 / 5) := by
  intro w I
  linarith only [reciprocalHead_tail_le hRH hb hT hc, RiemannZeta.sincTail_anchor_le hRH]

/-- At the middle-band cutoff the reciprocal main term and the certified density
moments together fit the quadratic envelope used by the phase cells. -/
theorem middleDensity_le {L : ℝ} (hl : 35 / 2 ≤ L) (hr : L ≤ 53 / 2) :
    let q := 2 * L / 7 - 2 / 3
    let β := -Real.log (1 - q / Real.exp (L / 2)) / 2
    let T := (2 / 5) / β
    let A := L / 2 - Real.log (Real.pi * q)
    let I := fun b ↦ ∫ z in Set.Ioi (2 / 5 : ℝ), momentIntegrand b z
    (Real.log T - Real.log (2 * Real.pi)) ^ 2 / (2 * Real.pi) +
        (I true - Real.log (2 * Real.pi * β) * I false) / Real.pi ≤
      (A ^ 2 + 3 / 2 * A + 3 / 2) / (2 * Real.pi) := by
  intro q β T A I
  have hb : 0 < β :=
    lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1 / 300000) (RiemannZeta.sinc_beta_bounds hl hr).1
  let c := -Real.log (2 * Real.pi * β)
  have hc : 0 ≤ c ∧ c ≤ A := RiemannZeta.sinc_log_coefficient hl hr
  have hs := pow_le_pow_left₀ hc.1 hc.2 2
  have ht : Real.log T - Real.log (2 * Real.pi) = Real.log (2 / 5) + c := by
    dsimp only [T, c]
    rw [Real.log_div (by norm_num only) hb.ne',
      Real.log_mul (mul_pos (by norm_num only) Real.pi_pos).ne' hb.ne']
    ring
  have hm :
    (Real.log (2 / 5)) ^ 2 / 2 + I true + c * (Real.log (2 / 5) + I false) ≤
      73 / 100 + (748 / 1000) * A :=
    middleMoment_le hl hr
  rw [ht, sub_eq_add_neg, ← neg_mul, show -Real.log (2 * Real.pi * β) = c from rfl]
  field_simp [Real.pi_pos]
  nlinarith only [hm, hs, hc.1.trans hc.2]

/-- Throughout the middle band the anchored, damped tail fits the phase-grid
quadratic plus the uniform count-error allowance at the actual smoothing scale. -/
theorem middleTail_le (hRH : RiemannHypothesis) {L : ℝ} (hl : 35 / 2 ≤ L) (hr : L ≤ 53 / 2) :
    let q := 2 * L / 7 - 2 / 3
    let β := -Real.log (1 - q / Real.exp (L / 2)) / 2
    let T := (2 / 5) / β
    let A := L / 2 - Real.log (Real.pi * q)
    let w := fun ρ : ℂ ↦
      if riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ T < |ρ.im| then
        (RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          (Analysis.sincWeight (β * |ρ.im|) / |ρ.im|)
      else 0
    RiemannZeta.zeroReciprocalSum T - RiemannZeta.zeroReciprocalSum 100 + ∑' ρ, w ρ +
        3 / 2 * RiemannZeta.ordinateTail 100 ≤
      (A ^ 2 + 3 / 2 * A + 3 / 2) / (2 * Real.pi) - 748 / 625 + 19164 / 10 * β ^ 2 := by
  intro q β T A w
  have hb : 1 / 300000 ≤ β ∧ β ≤ 1 / 1998 := RiemannZeta.sinc_beta_bounds hl hr
  have hp : 0 < β := lt_of_lt_of_le (by norm_num only) hb.1
  have ht : 100 ≤ T ∧ Real.log T ≤ 12 := RiemannZeta.sinc_cut_height_bounds hb.1 hb.2
  have hc : β * T = 2 / 5 := by
    dsimp only [T]; field_simp [hp.ne']
  have he := mul_le_mul_of_nonneg_left ht.2 (sq_nonneg β)
  have hd := middleDensity_le hl hr
  have ha := anchoredTail_moment_le hRH hp ht.1 hc
  apply ha.trans
  apply add_le_add (sub_le_sub_right hd _) _
  nlinarith only [he]

/-- Every finite integrated zero sum strictly above 100 satisfies the middle-band
quadratic bound with the common endpoint factor, uniformly in the truncation. -/
theorem middleIntegratedTail_le (hRH : RiemannHypothesis) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hr : ∀ ρ ∈ S, 0 ≤ ρ.re) (hy : ∀ ρ ∈ S, 100 < |ρ.im|)
    {x L : ℝ} (hx : 0 < x) (hl : 35 / 2 ≤ L) (hu : L ≤ 53 / 2) :
    let q := 2 * L / 7 - 2 / 3
    let η := -Real.log (1 - q / Real.exp (L / 2))
    let β := η / 2
    let A := L / 2 - Real.log (Real.pi * q)
    ‖∑ ρ ∈ S,
          (RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
              ((x : ℂ) ^ (ρ + 1) - ((x * Real.exp (-η) : ℝ) : ℂ) ^ (ρ + 1)) /
            (ρ * (ρ + 1))‖ ≤
      x ^ (3 / 2 : ℝ) * (1 - Real.exp (-η)) *
        ((A ^ 2 + 3 / 2 * A + 3 / 2) / (2 * Real.pi) - 748 / 625 + 19164 / 10 * β ^ 2) := by
  intro q η β A
  have hb : 1 / 300000 ≤ β ∧ β ≤ 1 / 1998 := RiemannZeta.sinc_beta_bounds hl hu
  have hp : 0 < β := lt_of_lt_of_le (by norm_num only) hb.1
  have he : 0 < η := by
    change 0 < η / 2 at hp; linarith only [hp]
  let T := (2 / 5) / β
  have ht : 100 ≤ T := (RiemannZeta.sinc_cut_height_bounds hb.1 hb.2).1
  have hc : β * T = 2 / 5 := by
    dsimp only [T]; field_simp [hp.ne']
  apply (RiemannZeta.integrated_sinc_above_hundred hRH S hz hr hy hx he).trans
  apply
    mul_le_mul_of_nonneg_left _
      (mul_nonneg (Real.rpow_nonneg hx.le _)
        (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr he.le))))
  exact
    (add_le_add_left (RiemannZeta.finite_sinc_split_le hRH S hz hr hy hp ht hc) _).trans
      (middleTail_le hRH hl hu)

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
