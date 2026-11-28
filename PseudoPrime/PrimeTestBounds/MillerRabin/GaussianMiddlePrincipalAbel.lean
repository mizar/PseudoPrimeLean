/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogWeightedVariation
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleEulerDeriv
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleIntTransforms
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExponentialLogWeightedSummation
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedSummationByParts
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.IntegratedLogSplit

/-! # Second Abel summation for the middle principal Euler sum -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Apply logarithmic variation to one positive Mangoldt atom. -/
private theorem middle_log_atom {W : ℝ → ℝ} {v b : ℝ} (hv : 0 < v) (hb : v ≤ b)
    (hW : ∀ t ∈ Set.Icc v b, DifferentiableAt ℝ W t)
    (hP : ∀ t ∈ Set.Icc v b, DifferentiableAt ℝ (fun x ↦ x * deriv W x) t)
    (hi :
      IntervalIntegrable (fun t ↦ Real.log (t / v) * deriv (fun x ↦ x * deriv W x) t)
        MeasureTheory.volume v b) :
    let P := fun t ↦ t * deriv W t
    W v = (∫ t in v..b, Real.log (t / v) * deriv P t) - Real.log (b / v) * P b + W b := by
  intro P
  have h :=
    Analysis.log_variation_integral hv hv hb (fun t ht ↦ (hW t ht).hasDerivAt)
      (fun t ht ↦ (hP t ht).hasDerivAt) hi
  rw [Real.log_div_self, zero_mul, zero_sub] at h
  dsimp only [P] at h ⊢
  linarith only [h]

/-- Apply two partial summations atomwise, retaining both boundary terms. -/
private theorem middle_mangoldt_second_abel (W : ℝ → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hW : ∀ t > 0, DifferentiableAt ℝ W t)
    (hP : ∀ t > 0, DifferentiableAt ℝ (fun x ↦ x * deriv W x) t)
    (hi :
      ∀ v,
        0 < v →
          v ≤ b →
          IntervalIntegrable (fun t ↦ Real.log (t / v) * deriv (fun x ↦ x * deriv W x) t)
            MeasureTheory.volume v b) :
    let P := fun t ↦ t * deriv W t
    (∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * W n) =
      (∑ n ∈ Finset.Ioc 0 ⌊b⌋₊,
            ArithmeticFunction.vonMangoldt n * ∫ t in (n : ℝ)..b, Real.log (t / n) * deriv P t) -
          P b * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum b +
        W b * Chebyshev.psi b := by
  intro P
  rw [AnalyticNumberTheory.Arithmetic.psi_eq_positive_sum,
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hp : (0 : ℝ) < n := Nat.cast_pos.mpr (Finset.mem_Ioc.mp hn).1
  have hnb := (Nat.le_floor_iff hb).mp (Finset.mem_Ioc.mp hn).2
  have h :=
    middle_log_atom hp hnb (fun t ht ↦ hW t (hp.trans_le ht.1)) (fun t ht ↦ hP t (hp.trans_le ht.1))
      (hi n hp hnb)
  change W n = _ at h
  rw [h]
  unfold AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm
  dsimp only [P]
  ring

/-- Combine the atom integrals by the clipped logarithm on the common interval. -/
private theorem middle_log_sum_integral {b : ℝ} (hb : 1 ≤ b) {Q : ℝ → ℝ}
    (hq : ContinuousOn Q (Set.Icc 1 b)) :
    (∑ n ∈ Finset.Ioc 0 ⌊b⌋₊,
        ArithmeticFunction.vonMangoldt n * ∫ t in (n : ℝ)..b, Real.log (t / n) * Q t) =
      ∫ t in (1 : ℝ)..b, AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * Q t := by
  let f (n : ℕ) (t : ℝ) := Analysis.positiveLogRatio n t * Q t
  have hi {n : ℕ} (hn : n ∈ Finset.Ioc 0 ⌊b⌋₊) :
    IntervalIntegrable (f n) MeasureTheory.volume 1 b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hb]
    exact
      (Analysis.positiveLogRatio_continuous
            (Nat.cast_pos.mpr (Finset.mem_Ioc.mp hn).1)).continuousOn.mul
        hq
  have he {n : ℕ} (hn : n ∈ Finset.Ioc 0 ⌊b⌋₊) :
    (∫ t in (n : ℝ)..b, Real.log (t / n) * Q t) = ∫ t in (1 : ℝ)..b, f n t := by
    have hl : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
    have hu := (Nat.le_floor_iff (zero_le_one.trans hb)).mp (Finset.mem_Ioc.mp hn).2
    have h1 : IntervalIntegrable (f n) MeasureTheory.volume 1 n :=
      (hi hn).mono_set
        (by
          rw [Set.uIcc_of_le hb, Set.uIcc_of_le hl]
          exact Set.Icc_subset_Icc_right hu)
    have h2 : IntervalIntegrable (f n) MeasureTheory.volume n b :=
      (hi hn).mono_set
        (by
          rw [Set.uIcc_of_le hb, Set.uIcc_of_le hu]
          exact Set.Icc_subset_Icc_left hl)
    have hz : (∫ t in (1 : ℝ)..n, f n t) = 0 := by
      rw [← intervalIntegral.integral_zero (a := 1) (b := (n : ℝ))]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hl] at ht
      simp only [f, Analysis.positiveLogRatio_zero ht.2, zero_mul]
    rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2, hz, zero_add]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hu] at ht
    simp only [f, Analysis.positiveLogRatio_eq_log ht.1]
  calc
    _ = ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, ∫ t in (1 : ℝ)..b, ArithmeticFunction.vonMangoldt n * f n t := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [he hn, intervalIntegral.integral_const_mul]
    _ = _ := by
      rw [← intervalIntegral.integral_finsetSum (fun n hn ↦ (hi hn).const_mul _)]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hb] at ht
      have h :=
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum_eq_clipped_scaled (x := 1)
          zero_lt_one (zero_le_one.trans ht.1) ht.2
      simp only [one_mul, div_one] at h
      simp only [h, Finset.sum_mul, f, mul_assoc]

/-- A smooth positive-axis weight has a second Abel formula with one logarithmically
weighted Mangoldt integral and two terms at the upper endpoint. -/
public theorem middle_mangoldt_log_integral (W : ℝ → ℝ) {b : ℝ} (hb : 1 ≤ b)
    (hW : ∀ t > 0, DifferentiableAt ℝ W t)
    (hP : ∀ t > 0, DifferentiableAt ℝ (fun x ↦ x * deriv W x) t)
    (hQ : ContinuousOn (deriv (fun x ↦ x * deriv W x)) (Set.Ioi 0)) :
    let P := fun t ↦ t * deriv W t
    (∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * W n) =
      (∫ t in (1 : ℝ)..b, AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * deriv P t) -
          P b * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum b +
        W b * Chebyshev.psi b := by
  have h :=
    middle_mangoldt_second_abel W (zero_le_one.trans hb) hW hP
      (fun v hv hvb ↦ by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le hvb]
        have hlog : ContinuousOn (fun t : ℝ ↦ Real.log (t / v)) (Set.Icc v b) :=
          (continuous_id.div_const v).continuousOn.log
            (fun _ ht ↦ (div_pos (hv.trans_le ht.1) hv).ne')
        exact hlog.mul (hQ.mono fun _ ht ↦ hv.trans_le ht.1))
  exact
    h.trans
      (by
        exact
          congrArg
            (fun x ↦
              x - (b * deriv W b) * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum b +
                W b * Chebyshev.psi b)
            (middle_log_sum_integral hb
              (hQ.mono (show Set.Icc 1 b ⊆ Set.Ioi 0 from fun _ ht ↦ zero_lt_one.trans_le ht.1))))

/-- The power-log polynomial weight before truncation at its upper support endpoint. -/
@[expose]
public noncomputable def middlePrincipalWeight (B : Polynomial ℝ) (c z d t : ℝ) : ℝ :=
  c * (t ^ d * B.eval (z - Real.log t))

/-- The smooth extension of the principal weight has the prescribed derivative for `t > 0`. -/
public theorem middle_principal_weight_deriv (B : Polynomial ℝ) (c z d : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (middlePrincipalWeight B c z d)
      (c * (t ^ (d - 1) * (Polynomial.C d * B - B.derivative).eval (z - Real.log t))) t := by
  exact (middle_log_poly_deriv B z d ht).const_mul c

/-- Multiplying the derivative by `t` keeps the same power-log form. -/
public theorem middle_principal_t_mul_deriv (B : Polynomial ℝ) (c z d : ℝ) {t : ℝ} (ht : 0 < t) :
    t * deriv (middlePrincipalWeight B c z d) t =
      middlePrincipalWeight (Polynomial.C d * B - B.derivative) c z d t := by
  rw [(middle_principal_weight_deriv B c z d ht).deriv, middlePrincipalWeight,
    Real.rpow_sub_one ht.ne']
  field_simp (disch := exact ht.ne')

/-- Both upper boundary terms vanish if the source and its derivative vanish at zero. -/
public theorem middle_principal_upper_jet (B : Polynomial ℝ) (c z d : ℝ) (hB : B.eval 0 = 0)
    (hB' : B.derivative.eval 0 = 0) :
    middlePrincipalWeight B c z d (Real.exp z) = 0 ∧
      deriv (middlePrincipalWeight B c z d) (Real.exp z) = 0 := by
  rw [(middle_principal_weight_deriv B c z d (Real.exp_pos z)).deriv]
  simp only [middlePrincipalWeight, Real.log_exp, sub_self, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C, hB, hB', mul_zero, and_self]

/-- Differentiate the weighted first derivative on the positive half-line. -/
public theorem middle_principal_moment_deriv (B : Polynomial ℝ) (c z d : ℝ) {t : ℝ} (ht : 0 < t) :
    let Q := Polynomial.C d * B - B.derivative
    HasDerivAt (fun x ↦ x * deriv (middlePrincipalWeight B c z d) x)
      (c * (t ^ (d - 1) * (Polynomial.C d * Q - Q.derivative).eval (z - Real.log t))) t := by
  intro Q
  have h := middle_principal_weight_deriv Q c z d ht
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with x hx
  exact middle_principal_t_mul_deriv B c z d hx

/-- The weighted derivative has a continuous derivative on the positive half-line. -/
public theorem middle_principal_moment_cont (B : Polynomial ℝ) (c z d : ℝ) :
    ContinuousOn (deriv (fun x ↦ x * deriv (middlePrincipalWeight B c z d) x)) (Set.Ioi 0) := by
  intro t ht
  let Q := Polynomial.C d * B - B.derivative
  let R := Polynomial.C d * Q - Q.derivative
  have hpow := Real.continuousAt_rpow_const t (d - 1) (Or.inl (ne_of_gt ht))
  have hlog : ContinuousAt (fun x : ℝ ↦ z - Real.log x) t :=
    continuousAt_const.sub (Real.continuousAt_log (ne_of_gt ht))
  have he : ContinuousAt (fun x : ℝ ↦ c * (x ^ (d - 1) * R.eval (z - Real.log x))) t :=
    continuousAt_const.mul (hpow.mul (R.continuous.continuousAt.comp hlog))
  exact
    he.continuousWithinAt.congr (fun x hx ↦ (middle_principal_moment_deriv B c z d hx).deriv)
      (middle_principal_moment_deriv B c z d ht).deriv

/-- Apply second Abel summation at the cutoff and the support endpoint, leaving
only the two boundary terms at the cutoff. -/
public theorem middle_principal_difference (B : Polynomial ℝ) (c z d X : ℝ) (hX : 1 ≤ X)
    (hXZ : X ≤ Real.exp z) (hB : B.eval 0 = 0) (hB' : B.derivative.eval 0 = 0) :
    let W := middlePrincipalWeight B c z d
    let P := fun t ↦ t * deriv W t
    let L := AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum
    (4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n * W n) -
        (∑ n ∈ Finset.Ioc 0 ⌊Real.exp z⌋₊, ArithmeticFunction.vonMangoldt n * W n)) =
      4 * (∫ t in (1 : ℝ)..X, L t * deriv P t) - (∫ t in (1 : ℝ)..Real.exp z, L t * deriv P t) -
          4 * (P X * L X) +
        4 * (W X * Chebyshev.psi X) := by
  intro W P L
  have hW t ht := (middle_principal_weight_deriv B c z d (t := t) ht).differentiableAt
  have hP t ht := (middle_principal_moment_deriv B c z d (t := t) ht).differentiableAt
  have hQ := middle_principal_moment_cont B c z d
  have h1 := middle_mangoldt_log_integral W hX hW hP hQ
  have h2 := middle_mangoldt_log_integral W (hX.trans hXZ) hW hP hQ
  obtain ⟨hw, hp⟩ := middle_principal_upper_jet B c z d hB hB'
  change W (Real.exp z) = 0 at hw
  change deriv W (Real.exp z) = 0 at hp
  dsimp only at h1 h2
  rw [h1, h2, hw, hp, mul_zero, zero_mul, zero_mul, sub_zero, add_zero]
  dsimp only [P, L]
  ring

/-- Integrate the linear and logarithmic terms of the centered formula. -/
private theorem middle_centering_integral (W : ℝ → ℝ) {b : ℝ} (hb : 1 ≤ b) (c : ℝ)
    (hW : ∀ t > 0, DifferentiableAt ℝ W t)
    (hP : ∀ t > 0, DifferentiableAt ℝ (fun x ↦ x * deriv W x) t)
    (hQ : ContinuousOn (deriv (fun x ↦ x * deriv W x)) (Set.Ioi 0)) :
    let P := fun t ↦ t * deriv W t
    (∫ t in (1 : ℝ)..b, (t - c * Real.log t) * deriv P t) =
      (b - c * Real.log b) * P b - (b - c) * W b - P 1 + (1 - c) * W 1 +
        ∫ t in (1 : ℝ)..b, W t := by
  intro P
  have ht {u : ℝ} (h : u ∈ Set.uIcc 1 b) : u ∈ Set.Ioi (0 : ℝ) :=
    zero_lt_one.trans_le ((Set.uIcc_of_le hb ▸ h : u ∈ Set.Icc 1 b).1)
  have hdW (u : ℝ) (h : u ∈ Set.uIcc 1 b) := (hW u (ht h)).hasDerivAt
  have hdP (u : ℝ) (h : u ∈ Set.uIcc 1 b) := (hP u (ht h)).hasDerivAt
  have hq : ContinuousOn (deriv P) (Set.uIcc 1 b) := hQ.mono fun _ h ↦ ht h
  have hi : IntervalIntegrable (fun t ↦ t * deriv P t) MeasureTheory.volume 1 b :=
    (continuous_id.continuousOn.mul hq).intervalIntegrable
  have hlog : IntervalIntegrable (fun t ↦ Real.log t * deriv P t) MeasureTheory.volume 1 b :=
    ((Real.continuousOn_log.mono (show Set.uIcc 1 b ⊆ {0}ᶜ from fun _ h ↦ ne_of_gt (ht h))).mul
        hq).intervalIntegrable
  have hWi : IntervalIntegrable W MeasureTheory.volume 1 b :=
    (show ContinuousOn W (Set.uIcc 1 b) from fun t ht' ↦
        (hW t (ht ht')).continuousAt.continuousWithinAt).intervalIntegrable
  have hlin := Analysis.linear_variation_integral hdW hdP hi hWi
  have hlg :=
    Analysis.log_variation_integral zero_lt_one zero_lt_one hb
      (fun u h ↦ hdW u (Set.uIcc_of_le hb ▸ h)) (fun u h ↦ hdP u (Set.uIcc_of_le hb ▸ h))
      (by simpa only [div_one] using hlog)
  simp only [div_one, Real.log_one, zero_mul, one_mul] at hlg hlin
  simp only [sub_mul, mul_assoc, intervalIntegral.integral_sub hi (hlog.const_mul c),
    intervalIntegral.integral_const_mul]
  dsimp only [P] at hlin hlg ⊢
  rw [hlin, hlg]
  ring

/-- Center one Mangoldt prefix by subtracting `t - c * log t`. -/
private theorem middle_centered_prefix (W : ℝ → ℝ) {b : ℝ} (hb : 1 ≤ b) (c : ℝ)
    (hW : ∀ t > 0, DifferentiableAt ℝ W t)
    (hP : ∀ t > 0, DifferentiableAt ℝ (fun x ↦ x * deriv W x) t)
    (hQ : ContinuousOn (deriv (fun x ↦ x * deriv W x)) (Set.Ioi 0)) :
    let P := fun t ↦ t * deriv W t
    let E := fun t ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - (t - c * Real.log t)
    (∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * W n) =
      (∫ t in (1 : ℝ)..b, W t) + (∫ t in (1 : ℝ)..b, E t * deriv P t) - P b * E b +
            W b * (Chebyshev.psi b - b + c) -
          P 1 +
        (1 - c) * W 1 := by
  intro P E
  have ht {u : ℝ} (h : u ∈ Set.uIcc 1 b) : 0 < u :=
    zero_lt_one.trans_le ((Set.uIcc_of_le hb ▸ h : u ∈ Set.Icc 1 b).1)
  have hq : ContinuousOn (deriv P) (Set.uIcc 1 b) := hQ.mono fun _ h ↦ ht h
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
  have hh := middle_mangoldt_log_integral W hb hW hP hQ
  have hc := middle_centering_integral W hb c hW hP hQ
  dsimp only [E, P] at hh hc ⊢
  simp_rw [sub_mul (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum _) _ _]
  rw [intervalIntegral.integral_sub (f := fun t ↦
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * deriv (fun x ↦ x * deriv W x) t)
      (g := fun t ↦ (t - c * Real.log t) * deriv (fun x ↦ x * deriv W x) t) hi.intervalIntegrable
      hj.intervalIntegrable]
  linarith only [hh, hc]

/-- Split the unsigned Euler difference into its main integrals, centered remainder,
and explicit boundary contributions. -/
public theorem middle_centered_difference (B : Polynomial ℝ) (k z d X c : ℝ) (hX : 1 ≤ X)
    (hXZ : X ≤ Real.exp z) (hB : B.eval 0 = 0) (hB' : B.derivative.eval 0 = 0) :
    let W := middlePrincipalWeight B k z d
    let P := fun t ↦ t * deriv W t
    let E := fun t ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - (t - c * Real.log t)
    (4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n * W n) -
        (∑ n ∈ Finset.Ioc 0 ⌊Real.exp z⌋₊, ArithmeticFunction.vonMangoldt n * W n)) =
      (4 * (∫ t in (1 : ℝ)..X, W t) - (∫ t in (1 : ℝ)..Real.exp z, W t)) +
            (4 * (∫ t in (1 : ℝ)..X, E t * deriv P t) -
              (∫ t in (1 : ℝ)..Real.exp z, E t * deriv P t) -
              4 * (P X * E X)) +
            4 * (W X * (Chebyshev.psi X - X + c)) -
          3 * P 1 +
        3 * (1 - c) * W 1 := by
  intro W P E
  have hW t ht := (middle_principal_weight_deriv B k z d (t := t) ht).differentiableAt
  have hP t ht := (middle_principal_moment_deriv B k z d (t := t) ht).differentiableAt
  have hQ := middle_principal_moment_cont B k z d
  have h1 := middle_centered_prefix W hX c hW hP hQ
  have h2 := middle_centered_prefix W (hX.trans hXZ) c hW hP hQ
  obtain ⟨hw, hp⟩ := middle_principal_upper_jet B k z d hB hB'
  change W (Real.exp z) = 0 at hw
  change deriv W (Real.exp z) = 0 at hp
  dsimp only at h1 h2
  rw [h1, h2, hw, hp, mul_zero, zero_mul, zero_mul, sub_zero, add_zero]
  dsimp only [P, E]
  ring

/-- A polynomial Laplace equation provides the antiderivative of the principal weight. -/
public theorem middle_principal_integral (B M : Polynomial ℝ) (k z d : ℝ) {l r : ℝ} (hl : 0 < l)
    (hlr : l ≤ r) (hM : Polynomial.C (d + 1) * M - M.derivative = B) :
    (∫ t in l..r, middlePrincipalWeight B k z d t) =
      middlePrincipalWeight M k z (d + 1) r - middlePrincipalWeight M k z (d + 1) l := by
  have hd : d + 1 - 1 = d := add_sub_cancel_right d 1
  have h (t : ℝ) (ht : t ∈ Set.uIcc l r) :
    HasDerivAt (middlePrincipalWeight M k z (d + 1)) (middlePrincipalWeight B k z d t) t := by
    have hp := hl.trans_le (Set.uIcc_of_le hlr ▸ ht).1
    simpa only [hM, hd, middlePrincipalWeight] using middle_principal_weight_deriv M k z (d + 1) hp
  have hi : ContinuousOn (middlePrincipalWeight B k z d) (Set.uIcc l r) := by
    intro t ht
    have hp := hl.trans_le (Set.uIcc_of_le hlr ▸ ht).1
    exact (middle_principal_weight_deriv B k z d hp).continuousAt.continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt h hi.intervalIntegrable

/-- Evaluate the main integral using the rational Laplace polynomial. -/
public theorem middle_principal_rat_integral (B : Polynomial ℚ) (k z : ℝ) {s : ℚ} (hs : s ≠ 0)
    {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) :
    let d := (s : ℝ) - 1
    let M := (middleMomentPoly B s 0).map (Rat.castHom ℝ)
    (∫ t in l..r, middlePrincipalWeight (B.map (Rat.castHom ℝ)) k z d t) =
      middlePrincipalWeight M k z (s : ℝ) r - middlePrincipalWeight M k z (s : ℝ) l := by
  intro d M
  have hc : d + 1 = (s : ℝ) := sub_add_cancel _ _
  have hm := congrArg (Polynomial.map (Rat.castHom ℝ)) (middle_moment_ode B hs)
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, ← Polynomial.derivative_map,
    Rat.coe_castHom] at hm
  change Polynomial.C (s : ℝ) * M - M.derivative = B.map (Rat.castHom ℝ) at hm
  have hM : Polynomial.C (d + 1) * M - M.derivative = B.map (Rat.castHom ℝ) := by rw [hc, hm]
  rw [middle_principal_integral (B.map (Rat.castHom ℝ)) M k z d hl hlr hM, hc]

/-- Reduce the principal main difference to the three Laplace endpoint values. -/
public theorem middle_principal_main_difference (B : Polynomial ℚ) (k z : ℝ) {s : ℚ} (hs : s ≠ 0)
    {X : ℝ} (hX : 1 ≤ X) (hXZ : X ≤ Real.exp z) :
    let W := middlePrincipalWeight (B.map (Rat.castHom ℝ)) k z ((s : ℝ) - 1)
    let F := middlePrincipalWeight ((middleMomentPoly B s 0).map (Rat.castHom ℝ)) k z (s : ℝ)
    4 * (∫ t in (1 : ℝ)..X, W t) - (∫ t in (1 : ℝ)..Real.exp z, W t) =
      4 * F X - F (Real.exp z) - 3 * F 1 := by
  intro W F
  rw [middle_principal_rat_integral B k z hs zero_lt_one hX,
    middle_principal_rat_integral B k z hs zero_lt_one (hX.trans hXZ)]
  dsimp only [F]
  ring

/-- Evaluate the Laplace antiderivative at an exponential cutoff in physical coordinates. -/
public theorem middle_laplace_physical_at (M : Polynomial ℝ) (κ a z x : ℝ) :
    middlePrincipalWeight M (κ * Real.exp (-a * z)) z (a + 1 / 2) (Real.exp x) =
      (κ * Real.exp (-a * (z - x))) * Real.exp (x / 2) * M.eval (z - x) := by
  have h :
    Real.exp (-a * z) * Real.exp (x * (a + 1 / 2)) =
      Real.exp (-a * (z - x)) * Real.exp (x / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simpa only [middlePrincipalWeight, Real.log_exp, Real.rpow_def_of_pos (Real.exp_pos x),
    ← mul_assoc] using congrArg (fun v : ℝ ↦ κ * v * M.eval (z - x)) h

/-- Identify the physical compensation-style weight with the smooth principal extension. -/
public theorem middle_principal_physical (B : Polynomial ℝ) (κ a b s : ℝ) {t : ℝ} (ht : 0 < t) :
    κ * middleCompWeight B.eval (Real.exp s) b a t =
      middlePrincipalWeight B (κ * Real.exp (-a * (s + b))) (s + b) (a - 1 / 2) t := by
  have he :
    Real.exp (Real.log t * (-(1 / 2))) * Real.exp (-a * (b - (Real.log t - s))) =
      Real.exp (-a * (s + b)) * Real.exp (Real.log t * (a - 1 / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp only [middleCompWeight, middlePrincipalWeight, Real.rpow_def_of_pos ht,
    Real.log_div ht.ne' (Real.exp_pos _).ne', Real.log_exp]
  rw [show s + b - Real.log t = b - (Real.log t - s) by ring]
  simpa only [← mul_assoc] using congrArg (fun e : ℝ ↦ κ * e * B.eval (b - (Real.log t - s))) he

/-- The main integral difference is a linear term in `exp (x / 2)` minus the
contribution of the lower endpoint at one. -/
public theorem middle_principal_main_slope (B : Polynomial ℚ) (κ b x : ℝ) {σ : ℚ} (hσ : σ ≠ 0)
    (hx : 0 ≤ x) (hb : 0 ≤ b) :
    let M := (middleMomentPoly B σ 0).map (Rat.castHom ℝ)
    let a := (σ : ℝ) - 1 / 2
    let z := x + b
    let k := κ * Real.exp (-a * z)
    let W := middlePrincipalWeight (B.map (Rat.castHom ℝ)) k z ((σ : ℝ) - 1)
    (4 * (∫ t in (1 : ℝ)..Real.exp x, W t) - (∫ t in (1 : ℝ)..Real.exp z, W t)) =
      Real.exp (x / 2) *
          (4 * κ * Real.exp (-a * b) * M.eval b - Real.exp (b / 2) * (κ * M.eval 0)) -
        3 * (k * M.eval z) := by
  intro M a z k W
  have h1 :=
    middle_principal_main_difference B k z hσ (Real.one_le_exp hx)
      (Real.exp_le_exp.mpr (le_add_of_nonneg_right hb))
  have hs : (σ : ℝ) = a + 1 / 2 := (sub_add_cancel _ _).symm
  have hf (y : ℝ) :
    middlePrincipalWeight M k z (σ : ℝ) (Real.exp y) =
      (κ * Real.exp (-a * (z - y))) * Real.exp (y / 2) * M.eval (z - y) := by
    rw [hs]
    exact middle_laplace_physical_at M κ a z y
  have hcut : z - x = b := by
    dsimp only [z]; ring
  have hz : Real.exp (z / 2) = Real.exp (x / 2) * Real.exp (b / 2) := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [z]
    ring
  change (4 * (∫ t in (1 : ℝ)..Real.exp x, W t) - (∫ t in (1 : ℝ)..Real.exp z, W t)) = _ at h1
  rw [h1, hf x, hf z, hcut, sub_self, mul_zero, Real.exp_zero, mul_one, hz]
  simp only [middlePrincipalWeight, Real.log_one, sub_zero, Real.one_rpow, one_mul]
  ring

/-- Adding one to the centered summatory function adds the derivative integral. -/
private theorem middle_anchor_integral (P : ℝ → ℝ) {T : ℝ} (hT : 1 ≤ T) (c : ℝ)
    (hP : ∀ t > 0, DifferentiableAt ℝ P t) (hQ : ContinuousOn (deriv P) (Set.Ioi 0)) :
    let E := fun t ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - (t - c * Real.log t)
    (∫ t in (1 : ℝ)..T, (E t + 1) * deriv P t) =
      (∫ t in (1 : ℝ)..T, E t * deriv P t) + (P T - P 1) := by
  intro E
  have ht {u : ℝ} (h : u ∈ Set.uIcc 1 T) : 0 < u :=
    zero_lt_one.trans_le ((Set.uIcc_of_le hT ▸ h : u ∈ Set.Icc 1 T).1)
  have hc : ContinuousOn (deriv P) (Set.uIcc 1 T) := hQ.mono fun _ h ↦ ht h
  have hm :=
    AnalyticNumberTheory.Arithmetic.continuousOn_logWeightedMangoldtSum_scaled (x := 1) zero_lt_one
      T
  simp only [one_mul] at hm
  have hdom : Set.uIcc (1 : ℝ) T ⊆ Set.Icc 0 T := by
    rw [Set.uIcc_of_le hT]
    exact Set.Icc_subset_Icc_left zero_le_one
  have hl := Real.continuousOn_log.mono (show Set.uIcc 1 T ⊆ {0}ᶜ from fun _ h ↦ (ht h).ne')
  have he : ContinuousOn E (Set.uIcc 1 T) :=
    (hm.mono hdom).sub (continuous_id.continuousOn.sub (continuous_const.continuousOn.mul hl))
  have hd :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t h ↦ (hP t (ht h)).hasDerivAt)
      hc.intervalIntegrable
  simp only [add_mul, one_mul]
  rw [intervalIntegral.integral_add (f := fun t ↦ E t * deriv P t) (he.mul hc).intervalIntegrable
      hc.intervalIntegrable,
    hd]

/-- Anchor the centered summatory function at one, absorbing its lower derivative term. -/
public theorem middle_centered_anchored (B : Polynomial ℝ) (k z d X c : ℝ) (hX : 1 ≤ X)
    (hXZ : X ≤ Real.exp z) (hB : B.eval 0 = 0) (hB' : B.derivative.eval 0 = 0) :
    let W := middlePrincipalWeight B k z d
    let P := fun t ↦ t * deriv W t
    let E := fun t ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - (t - c * Real.log t)
    let H := fun t ↦ E t + 1
    (4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n * W n) -
        (∑ n ∈ Finset.Ioc 0 ⌊Real.exp z⌋₊, ArithmeticFunction.vonMangoldt n * W n)) =
      (4 * (∫ t in (1 : ℝ)..X, W t) - (∫ t in (1 : ℝ)..Real.exp z, W t)) +
        (4 * (∫ t in (1 : ℝ)..X, H t * deriv P t) - (∫ t in (1 : ℝ)..Real.exp z, H t * deriv P t) -
          4 * (P X * H X)) +
        4 * (W X * (Chebyshev.psi X - X + c)) +
        3 * (1 - c) * W 1 := by
  intro W P E H
  have hP t ht := (middle_principal_moment_deriv B k z d (t := t) ht).differentiableAt
  have hQ := middle_principal_moment_cont B k z d
  have h := middle_centered_difference B k z d X c hX hXZ hB hB'
  have hi := middle_anchor_integral P hX c hP hQ
  have hz := middle_anchor_integral P (hX.trans hXZ) c hP hQ
  have hp : P (Real.exp z) = 0 := by
    dsimp only [P, W]
    rw [(middle_principal_upper_jet B k z d hB hB').2, mul_zero]
  change (∫ t in (1 : ℝ)..X, H t * deriv P t) = _ at hi
  change (∫ t in (1 : ℝ)..Real.exp z, H t * deriv P t) = _ at hz
  rw [hi, hz, hp]
  dsimp only [H, E, P, W] at h ⊢
  rw [h]
  ring

/-- The anchored log-weighted error is the difference of the zero series at `t`
and at one, with the corresponding trivial-zero difference subtracted. -/
public theorem middle_anchored_explicit {t : ℝ} (ht : 1 ≤ t) :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
          (t - Real.log (2 * Real.pi) * Real.log t) +
        1 =
      ((∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re -
          (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm 1 ρ).re) -
        (AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries t -
          AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries 1) := by
  have h0 : AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 1 = 0 := by
    rw [AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum, Nat.floor_one]
    apply Finset.sum_eq_zero
    intro n hn
    have hn' : n = 1 := le_antisymm (Finset.mem_Ioc.mp hn).2 (Finset.mem_Ioc.mp hn).1
    simp only [hn', AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm, Nat.cast_one, div_one,
      Real.log_one, mul_zero]
  rcases eq_or_lt_of_le ht with rfl | ht'
  · simp only [h0, Real.log_one, mul_zero, sub_zero, zero_sub, neg_add_cancel, sub_self]
  have h1 := AnalyticNumberTheory.RiemannZeta.log_weighted_exact_one
  rw [h0, Real.log_one, mul_zero, sub_zero] at h1
  linarith only [AnalyticNumberTheory.RiemannZeta.log_weighted_exact ht', h1]

/-- The first logarithmic derivative of a physical profile rescales to the
unit-cutoff profile. Its ordinary derivative gains an inverse cutoff factor. -/
public theorem middle_principal_weight_scale (B : Polynomial ℝ) (k d b : ℝ) {X : ℝ} (hX : 0 < X) :
    let W := middlePrincipalWeight B k (Real.log X + b) d
    let V := fun u : ℝ ↦ u ^ d * B.eval (b - Real.log u)
    let P := fun t ↦ t * deriv W t
    let F := fun u ↦ u * deriv V u
    let c := k * X ^ d
    (∀ u > 0, P (X * u) = c * F u) ∧ ∀ u > 0, deriv P (X * u) = (c / X) * deriv F u := by
  intro W V P F c
  have hv : middlePrincipalWeight B 1 b d = V := by
    funext u
    simp only [middlePrincipalWeight, V, one_mul]
  have he (u : ℝ) (hu : 0 < u) : P (X * u) = c * F u := by
    have hw := middle_principal_t_mul_deriv B k (Real.log X + b) d (mul_pos hX hu)
    have hf := middle_principal_t_mul_deriv B 1 b d hu
    rw [hv] at hf
    change P (X * u) = _ at hw
    change F u = _ at hf
    rw [hw, hf]
    simp only [middlePrincipalWeight, c, one_mul, Real.log_mul hX.ne' hu.ne',
      Real.mul_rpow hX.le hu.le]
    rw [show Real.log X + b - (Real.log X + Real.log u) = b - Real.log u by ring]
    ring
  refine ⟨he, ?_⟩
  intro u hu
  have hp : DifferentiableAt ℝ P (X * u) :=
    (middle_principal_moment_deriv B k (Real.log X + b) d (mul_pos hX hu)).differentiableAt
  have hf := (middle_principal_moment_deriv B 1 b d hu).differentiableAt
  rw [hv] at hf
  change DifferentiableAt ℝ F u at hf
  have hh := hp.hasDerivAt.comp u ((hasDerivAt_id u).const_mul X)
  simp only [mul_one] at hh
  have hc := hf.hasDerivAt.const_mul c
  have heq : (fun v ↦ c * F v) =ᶠ[nhds u] (fun v ↦ P (X * v)) := by
    filter_upwards [Ioi_mem_nhds hu] with v hv'
    exact (he v hv').symm
  have hd := hh.unique (hc.congr_of_eventuallyEq heq.symm)
  rw [div_mul_eq_mul_div]
  exact (eq_div_iff hX.ne').mpr hd

end PseudoPrime.PrimeTestBounds.MillerRabin
