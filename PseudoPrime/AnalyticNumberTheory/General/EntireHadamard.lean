/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.EntireCanonicalFactors
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Centered Hadamard identity from subquadratic growth

Pass finite-radius canonical decompositions to their genus-one limit using
absolute convergence and the decay of subquadratic growth errors.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For entire F nonzero at zero and at s, assume a global exponential power bound
and a zero-free sphere of radius R ≥ 1. At `norm s ≤ R / 2`, bound the difference
between the centered logarithmic derivative and the finite genus sum.
Combine variation of the analytic factor with the canonical correction estimate;
the resulting error tends to zero when the growth exponent is below two. -/
theorem norm_centeredLogDeriv_sub_truncatedGenus_le {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (h0 : F 0 ≠ 0) {C r R : ℝ} (hC : 0 < C) (hg : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (‖z‖ + 1) ^ r))
    (hR : 1 ≤ R) (hzf : ∀ ρ : ℂ, ‖ρ‖ = R → F ρ ≠ 0) {s : ℂ} (hs : ‖s‖ ≤ R / 2) (hsne : F s ≠ 0) :
    ‖(logDeriv F s - logDeriv F 0) - truncatedGenusSum F R s‖ ≤
      192 * ‖s‖ * (C * (R + 1) ^ r - Real.log ‖F 0‖ + 1) / R ^ 2 +
        (2 * ‖s‖ / R ^ 2) * ((C * (2 * R + 1) ^ r - Real.log ‖F 0‖) / Real.log 2) := by
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) hR
  obtain ⟨g, D⟩ := exists_ecanonicalDecomp_of_entire hF h0 R
  have h0closed : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := by
    simp only [Metric.mem_closedBall, dist_self, hR0.le]
  have hsclosed : s ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hs.trans (half_le_self hR0.le)
  have heq := ecanonicalDecomp_centered_logDeriv_eq h0 hF hR0 D hzf hsclosed hsne
  have hdiff := hF
  have hanalyticClosed : AnalyticOnNhd ℂ (F) (Metric.closedBall (0 : ℂ) R) := fun z _ ↦
    hdiff.analyticAt z
  set Dv := MeromorphicOn.divisor (F) (Metric.ball (0 : ℂ) R) with hDv_def
  have hfin : (Function.support Dv).Finite :=
    hanalyticClosed.meromorphicOn.divisor_ball_support_finite
  have h0ne : F 0 ≠ 0 := h0
  have hkey : ∀ u ∈ hfin.toFinset, u ∈ Metric.ball (0 : ℂ) R ∧ u ≠ 0 ∧ s ≠ u := by
    intro u hu
    rw [Set.Finite.mem_toFinset] at hu
    refine ⟨Dv.supportWithinDomain hu, ?_, ?_⟩
    · exact ne_of_mem_divisorBallSupport_of_entire_value_ne_zero hF hu h0ne
    · exact (ne_of_mem_divisorBallSupport_of_entire_value_ne_zero hF hu hsne).symm
  have hsub1 :
    Function.support (fun u : ℂ ↦ ((-Dv u : ℤ) : ℂ) * logDeriv (Complex.canonicalFactor R u) s) ⊆
      hfin.toFinset := by
    intro u hu
    rw [Function.mem_support] at hu
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    intro hDu0
    apply hu
    rw [hDu0]
    simp only [Int.cast_zero, neg_zero, zero_mul]
  have hsub2 :
    Function.support
        (fun u : ℂ ↦ ((-Dv u : ℤ) : ℂ) * logDeriv (Complex.canonicalFactor R u) (0 : ℂ)) ⊆
      hfin.toFinset := by
    intro u hu
    rw [Function.mem_support] at hu
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    intro hDu0
    apply hu
    rw [hDu0]
    simp only [Int.cast_zero, neg_zero, zero_mul]
  have hcombine :
    (∑ᶠ u : ℂ, ((-Dv u : ℤ) : ℂ) * logDeriv (Complex.canonicalFactor R u) s) -
        (∑ᶠ u : ℂ, ((-Dv u : ℤ) : ℂ) * logDeriv (Complex.canonicalFactor R u) 0) =
      truncatedGenusSum F R s +
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
      rw [← mul_sub, centered_logDeriv_canonicalFactor huball hsclosed hsneu hune0]
      simp only [Int.cast_neg]
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
              simp only [Int.cast_zero, zero_mul])).symm
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
    (logDeriv (F) s - logDeriv (F) 0) - truncatedGenusSum F R s =
      (∑ᶠ u : ℂ,
          ((Dv u : ℤ) : ℂ) *
            ((starRingEnd ℂ) u / ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * s) -
              (starRingEnd ℂ) u / (R : ℂ) ^ 2)) +
        (logDeriv g s - logDeriv g 0) := by
    rw [heq]
    ring
  rw [hfinal]
  refine (norm_add_le _ _).trans ?_
  rw [add_comm]
  exact
    add_le_add
      (norm_centered_logDeriv_canonical_factor_le hF h0 hR D hzf
        (fun z hz ↦ by simpa only [hz] using hg z) hs)
      (norm_canonicalCorrectionSum_le hF h0 hC hR0 hg hs)

/-- For an entire function nonzero at zero, its zeros on every compact set are
finite. The identity theorem gives a codiscrete nonzero set; compactness gives finiteness. -/
theorem finite_entire_zerosOn_compact {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    {K : Set ℂ} (hK : IsCompact K) : (K ∩ F ⁻¹' {0}).Finite := by
  have ha : AnalyticOnNhd ℂ F Set.univ := fun z _ ↦ hF.analyticAt z
  have he : ∀ᶠ z in Filter.codiscreteWithin Set.univ, F z ≠ 0 := by
    rcases ha.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with hz | hn
    · exact False.elim (h0 (hz (Set.mem_univ 0)))
    · exact hn
  have hm : {z : ℂ | F z ≠ 0} ∈ Filter.codiscreteWithin K :=
    Filter.codiscreteWithin_mono (Set.subset_univ K) he
  have hf := hK.finite_sdiff_of_mem_codiscreteWithin hm
  apply hf.subset
  intro z hz
  exact ⟨hz.1, fun hn ↦ hn hz.2⟩

/-- For an entire function nonzero at zero, choose a zero-free sphere radius
between n and n+1. Compact zero finiteness excludes only finitely many radii. -/
theorem exists_zeroFree_sphere_radius_of_entire {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    (n : ℕ) : ∃ R : ℝ, (n : ℝ) < R ∧ R < (n : ℝ) + 1 ∧ ∀ z : ℂ, ‖z‖ = R → F z ≠ 0 := by
  have hf :=
    finite_entire_zerosOn_compact hF h0 (isCompact_closedBall (x := (0 : ℂ)) (r := (n : ℝ) + 1))
  have hn := hf.image (fun z : ℂ ↦ ‖z‖)
  have hi : (Set.Ioo (n : ℝ) ((n : ℝ) + 1)).Infinite :=
    Set.Ioo_infinite (lt_add_of_pos_right _ zero_lt_one)
  obtain ⟨R, hR, hnot⟩ := hi.exists_notMem_finite hn
  refine ⟨R, hR.1, hR.2, fun z hz hzero ↦ hnot ?_⟩
  refine ⟨z, ⟨?_, hzero⟩, hz⟩
  rw [Metric.mem_closedBall, dist_zero_right, hz]
  exact hR.2.le

/-- For an entire function, its ball divisor is natural analytic multiplicity
inside the ball and zero outside. Unfold the analytic divisor formula and its domain. -/
theorem divisor_ball_eq_if_entire {F : ℂ → ℂ} (hF : Differentiable ℂ F) (R : ℝ) (z : ℂ) :
    MeromorphicOn.divisor F (Metric.ball 0 R) z =
      if ‖z‖ < R then (analyticOrderNatAt F z : ℤ) else 0 := by
  by_cases hz : ‖z‖ < R
  · have ha : AnalyticOnNhd ℂ F (Metric.ball 0 R) := fun w _ ↦ hF.analyticAt w
    rw [ite_eq_left hz,
      MeromorphicOn.AnalyticOnNhd.divisor_apply ha (by rwa [Metric.mem_ball, dist_zero_right])]
    unfold analyticOrderNatAt
    induction analyticOrderAt F z using ENat.recTopCoe <;> rfl
  · rw [ite_eq_right hz]
    exact
      (MeromorphicOn.divisor F (Metric.ball 0 R)).apply_eq_zero_of_notMem
        (by rwa [Metric.mem_ball, dist_zero_right])

/-- For a nonnegative exponent below two and a nonnegative affine argument,
the power divided by the radius squared tends to zero. Compare with the decaying
power of the radius. This makes subquadratic Hadamard errors vanish. -/
theorem tendsto_affine_rpow_div_sq {r a b : ℝ} (hr0 : 0 ≤ r) (hr2 : r < 2) (ha : 0 ≤ a)
    (hb : 0 ≤ b) : Filter.Tendsto (fun R : ℝ ↦ (a * R + b) ^ r / R ^ 2) Filter.atTop (nhds 0) := by
  have ht : Filter.Tendsto (fun R : ℝ ↦ (a + b) ^ r * R ^ (r - 2)) Filter.atTop (nhds 0) := by
    have he : r - 2 = -(2 - r) := by ring
    rw [he]
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop (sub_pos.mpr hr2)).const_mul ((a + b) ^ r)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with R hR
    exact
      div_nonneg (Real.rpow_nonneg (add_nonneg (mul_nonneg ha (zero_le_one.trans hR)) hb) _)
        (sq_nonneg R)
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with R hR
    have hp : 0 < R := zero_lt_one.trans_le hR
    have he : a * R + b ≤ (a + b) * R := by
      have ht := mul_le_mul_of_nonneg_left hR hb
      nlinarith only [ht]
    have hbound := Real.rpow_le_rpow (add_nonneg (mul_nonneg ha hp.le) hb) he hr0
    calc
      _ ≤ ((a + b) * R) ^ r / R ^ 2 := div_le_div_of_nonneg_right hbound (sq_nonneg R)
      _ = _ := by
        rw [Real.mul_rpow (add_nonneg ha hb) hp.le, Real.rpow_sub hp, Real.rpow_two]
        ring

/-- For a nonnegative growth exponent below two, the finite-radius genus error
tends to zero as radius tends to infinity. Each growth term is an affine power
divided by the radius squared, and the remaining constants decay similarly. -/
theorem tendsto_centeredGenusError {F : ℂ → ℂ} (C : ℝ) {r : ℝ} (hr0 : 0 ≤ r) (hr2 : r < 2) (s : ℂ) :
    Filter.Tendsto
      (fun R : ℝ ↦
        192 * ‖s‖ * (C * (R + 1) ^ r - Real.log ‖F 0‖ + 1) / R ^ 2 +
          (2 * ‖s‖ / R ^ 2) * ((C * (2 * R + 1) ^ r - Real.log ‖F 0‖) / Real.log 2))
      Filter.atTop (nhds 0) := by
  have h1 := tendsto_affine_rpow_div_sq hr0 hr2 zero_le_one zero_le_one
  simp only [one_mul] at h1
  have h2 := tendsto_affine_rpow_div_sq hr0 hr2 zero_le_two zero_le_one
  have hi : Filter.Tendsto (fun R : ℝ ↦ (1 : ℝ) / R ^ 2) Filter.atTop (nhds 0) := by
    have h := tendsto_rpow_neg_atTop (show (0 : ℝ) < 2 by norm_num only)
    apply h.congr'
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
    rw [Real.rpow_neg hR.le, Real.rpow_two, one_div]
  have h := ((h1.const_mul C).add (hi.const_mul (1 - Real.log ‖F 0‖))).const_mul (192 * ‖s‖)
  have h' := ((h2.const_mul C).sub (hi.const_mul (Real.log ‖F 0‖))).const_mul (2 * ‖s‖ / Real.log 2)
  have ht := h.add h'
  simp only [mul_zero, add_zero, sub_zero] at ht
  convert ht using 1
  funext R
  ring

/-- For entire F and an absolutely convergent genus series, finite-radius genus
sums converge to that series along every radius sequence tending to infinity.
Use indicator truncation and dominated convergence on the summable term norms. -/
theorem tendsto_truncatedGenusSum {F : ℂ → ℂ} (hF : Differentiable ℂ F) {s : ℂ}
    (hsum : Summable (fun ρ : ℂ ↦ (analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) + 1 / ρ))) {R : ℕ → ℝ}
    (hR : Filter.Tendsto R Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n ↦ truncatedGenusSum F (R n) s) Filter.atTop
      (nhds (∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) + 1 / ρ))) := by
  let T : ℂ → ℂ := fun ρ ↦ (analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)
  let U : ℕ → ℂ → ℂ := fun n ρ ↦ if ‖ρ‖ < R n then T ρ else 0
  have he : ∀ n, truncatedGenusSum F (R n) s = ∑' ρ : ℂ, U n ρ := by
    intro n
    have ha : AnalyticOnNhd ℂ F (Metric.closedBall 0 (R n)) := fun z _ ↦ hF.analyticAt z
    have hf :
      (Function.support
          (fun ρ : ℂ ↦
            (MeromorphicOn.divisor F (Metric.ball 0 (R n)) ρ : ℂ) *
              (1 / (s - ρ) + 1 / ρ))).Finite := by
      apply Set.Finite.subset ha.meromorphicOn.divisor_ball_support_finite
      intro ρ hρ
      exact fun hzero ↦
        hρ
          (by
            change (_ : ℂ) * _ = 0; rw [hzero]; simp only [Int.cast_zero, zero_mul])
    unfold truncatedGenusSum
    rw [← tsum_eq_finsum (L := SummationFilter.unconditional ℂ) hf]
    apply tsum_congr
    intro ρ
    rw [divisor_ball_eq_if_entire hF]
    by_cases hρ : ‖ρ‖ < R n
    · simp only [U, ite_eq_left hρ, T, Int.cast_natCast]
    · simp only [U, ite_eq_right hρ, Int.cast_zero, zero_mul]
  have hab : ∀ ρ : ℂ, Filter.Tendsto (fun n ↦ U n ρ) Filter.atTop (nhds (T ρ)) := by
    intro ρ
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [hR.eventually_gt_atTop ‖ρ‖] with n hn
    simp only [U, ite_eq_left hn]
  have hb : ∀ᶠ n in Filter.atTop, ∀ ρ : ℂ, ‖U n ρ‖ ≤ ‖T ρ‖ := by
    apply Filter.Eventually.of_forall
    intro n ρ
    dsimp only [U]
    split_ifs
    · exact le_refl _
    · simpa only [norm_zero] using norm_nonneg (T ρ)
  have ht := tendsto_tsum_of_dominated_convergence hsum.norm hab hb
  simpa only [← he] using ht

/-- For entire F nonzero at zero and s, subquadratic exponential growth and
absolute genus convergence imply the centered Hadamard logarithmic derivative identity.
Choose zero-free radii, pass the finite sums to the full series, and let both
canonical decomposition errors vanish. -/
theorem centered_logDeriv_eq_genusSum {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) {C r : ℝ}
    (hC : 0 < C) (hr0 : 0 ≤ r) (hr2 : r < 2) (hg : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (‖z‖ + 1) ^ r))
    {s : ℂ} (hs : F s ≠ 0)
    (hsum : Summable (fun ρ : ℂ ↦ (analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) + 1 / ρ))) :
    logDeriv F s - logDeriv F 0 =
      ∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) + 1 / ρ) := by
  choose R hlo hhi hfree using fun n : ℕ ↦ exists_zeroFree_sphere_radius_of_entire hF h0 (n + 2)
  have hR : Filter.Tendsto R Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono (fun n ↦ (hlo n).le)
    exact (tendsto_natCast_atTop_atTop (R := ℝ)).comp (Filter.tendsto_add_atTop_nat 2)
  have ht := tendsto_truncatedGenusSum hF hsum hR
  have he := (tendsto_centeredGenusError (F := F) C hr0 hr2 s).comp hR
  have hn :
    Filter.Tendsto (fun n ↦ ‖(logDeriv F s - logDeriv F 0) - truncatedGenusSum F (R n) s‖)
      Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
    · exact Filter.Eventually.of_forall (fun n ↦ norm_nonneg _)
    · filter_upwards [hR.eventually_ge_atTop (max 1 (2 * ‖s‖))] with n hn
      exact
        norm_centeredLogDeriv_sub_truncatedGenus_le hF h0 hC hg ((le_max_left _ _).trans hn)
          (hfree n)
          (by
            have h := (le_max_right 1 (2 * ‖s‖)).trans hn; linarith only [h])
          hs
  have hc := (tendsto_const_nhds (x := logDeriv F s - logDeriv F 0)).sub ht
  have hnorm := hc.norm
  have hz :
    ‖(logDeriv F s - logDeriv F 0) -
          ∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)‖ =
      0 :=
    tendsto_nhds_unique hnorm hn
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end PseudoPrime.AnalyticNumberTheory.General
