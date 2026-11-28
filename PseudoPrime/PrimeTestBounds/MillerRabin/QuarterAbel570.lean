/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterKernel570
import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedDifferences
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExponentialLogWeightedSummation
import PseudoPrime.Analysis.LogWeightedVariation
import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedSummationByParts
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # Abel summation for the section 31 principal weight -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Smooth extension of the section 31 summand weight on its positive support.
At scale X the shifted coordinate is (14/5 - log(t/X)) times 51/50. -/
noncomputable def quarterWeight570 (X t : ℝ) : ℝ :=
  let v := (2 * (7 / 5) - Real.log (t / X)) / (2 * (25 / 51))
  (1 / Real.sqrt t) * (v ^ 5 * Real.exp (-v) / 120)

/-- At each nonzero index in the support, the principal summand is the
von Mangoldt function times the smooth section 31 weight. -/
theorem quarter_summand_570 {X : ℝ} (hX : 0 < X) {n : ℕ} (hn : 0 < n)
    (hs : Real.log ((n : ℝ) / X) ≤ 14 / 5) :
    (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X n).re =
      quarterWeight570 X n * ArithmeticFunction.vonMangoldt n := by
  simp only [LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn.ne',
    MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), mul_one, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [quarterKernel570,
    LLS.PaperStatements.rationalPole_transform _ _ _ _ (div_pos (Nat.cast_pos.mpr hn) hX),
    Complex.ofReal_re]
  rw [Analysis.rationalPoleProfile,
    ite_eq_left ⟨div_pos (Nat.cast_pos.mpr hn) hX, by linarith only [hs]⟩]
  norm_num only [quarterWeight570, Nat.reduceMul, Nat.reduceSub, Nat.factorial, Nat.cast_ofNat]
  ring

/-- On any positive subinterval of the support, the principal sum has an exact
Abel formula with both endpoint atoms and the psi-weighted derivative integral. -/
theorem quarter_principal_abel_570 {X a b : ℝ} (hX : 0 < X) (ha : 0 < a) (hab : a ≤ b)
    (hb : Real.log (b / X) ≤ 14 / 5) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X n).re) =
      quarterWeight570 X b * Chebyshev.psi b - quarterWeight570 X a * Chebyshev.psi a -
        ∫ t in a..b, deriv (quarterWeight570 X) t * Chebyshev.psi t := by
  have hc {t : ℝ} (ht : 0 < t) : ContDiffAt ℝ 1 (quarterWeight570 X) t := by
    have hs : ContDiffAt ℝ 1 Real.sqrt t := Real.contDiffAt_sqrt ht.ne'
    unfold quarterWeight570
    dsimp only
    fun_prop (disch := positivity)
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) := hc (ha.trans_le ht.1)
  have hder : ContinuousOn (deriv (quarterWeight570 X)) (Set.Icc a b) := by
    have hu : ContDiffOn ℝ 1 (quarterWeight570 X) (Set.Ioi 0) := fun t ht ↦ (hc ht).contDiffWithinAt
    exact
      (hu.continuousOn_deriv_of_isOpen isOpen_Ioi (by decide)).mono (fun t ht ↦ ha.trans_le ht.1)
  have hh :=
    sum_mul_eq_sub_sub_integral_mul ArithmeticFunction.vonMangoldt ha.le hab
      (fun t ht ↦ (hd t ht).differentiableAt (by decide)) hder.integrableOn_Icc
  rw [← intervalIntegral.integral_of_le hab] at hh
  simp only [← Chebyshev.psi_eq_sum_Icc] at hh
  rw [← hh]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 := Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1
  have hnb := (Nat.le_floor_iff (ha.le.trans hab)).mp (Finset.mem_Ioc.mp hn).2
  exact
    quarter_summand_570 hX hn0
      ((Real.log_le_log (div_pos (Nat.cast_pos.mpr hn0) hX)
            (div_le_div_of_nonneg_right hnb hX.le)).trans
        hb)

/-- Terms beyond X exp(14/5) vanish, so the full real principal series is a finite sum. -/
theorem quarter_principal_finite_570 {X : ℝ} (hX : 0 < X) :
    (∑' n : ℕ, (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X n).re) =
      ∑ n ∈ Finset.Ioc 0 ⌊X * Real.exp (14 / 5)⌋₊,
        (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X n).re := by
  apply tsum_eq_sum
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp only [LLS.PaperStatements.MellinKernel.summand, ite_true, Complex.zero_re]
  have hcut : ⌊X * Real.exp (14 / 5)⌋₊ < n := by
    by_contra h
    exact hn (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0, le_of_not_gt h⟩)
  have hi : Real.exp (14 / 5) < (n : ℝ) / X :=
    (lt_div_iff₀ hX).mpr ((mul_comm _ X).trans_lt (Nat.lt_of_floor_lt hcut))
  have hp := (Real.exp_pos _).trans hi
  have hlog := Real.log_lt_log (Real.exp_pos _) hi
  rw [Real.log_exp] at hlog
  rw [LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn0, quarterKernel570,
    LLS.PaperStatements.rationalPole_transform _ _ _ _ hp, Analysis.rationalPoleProfile,
    ite_eq_right (fun h ↦ (not_lt_of_ge h.2) (by linarith only [hlog]))]
  simp only [Complex.ofReal_zero, mul_zero, Complex.zero_re]

/-- For scales at least one, the difference between four cutoff sums and the full series
is exactly a psi boundary and two first-derivative integrals on the kernel support. -/
theorem quarter_combined_abel_570 {X : ℝ} (hX : 1 ≤ X) :
    let B := X * Real.exp (14 / 5)
    let S := fun n : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X n).re
    4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) =
      4 * quarterWeight570 X X * Chebyshev.psi X -
          4 * (∫ t in (1 / 2 : ℝ)..X, deriv (quarterWeight570 X) t * Chebyshev.psi t) +
        ∫ t in (1 / 2 : ℝ)..B, deriv (quarterWeight570 X) t * Chebyshev.psi t := by
  intro B S
  have hx := zero_lt_one.trans_le hX
  have hxB : X ≤ B := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only))
  have hlog : Real.log (B / X) = 14 / 5 := by
    rw [show B / X = Real.exp (14 / 5) by
        dsimp only [B]; field_simp [hx.ne'],
      Real.log_exp]
  have hu :=
    quarter_principal_abel_570 hx (by norm_num only : (0 : ℝ) < 1 / 2)
      ((by norm_num only : (1 / 2 : ℝ) ≤ 1).trans hX)
      (by
        rw [div_self hx.ne', Real.log_one]; norm_num only)
  have hf :=
    quarter_principal_abel_570 hx (by norm_num only : (0 : ℝ) < 1 / 2)
      ((by norm_num only : (1 / 2 : ℝ) ≤ 1).trans (hX.trans hxB)) hlog.le
  have hfloor : ⌊(1 / 2 : ℝ)⌋₊ = 0 := Nat.floor_eq_zero.mpr (by norm_num only)
  have hz : Chebyshev.psi (1 / 2 : ℝ) = 0 := by
    rw [Chebyshev.psi_eq_sum_Icc]
    simp only [hfloor, Finset.Icc_self, Finset.sum_singleton, ArithmeticFunction.map_zero]
  have hw : quarterWeight570 X B = 0 := by
    norm_num only [quarterWeight570, hlog, zero_pow, zero_mul, mul_zero, zero_div]
  dsimp only [S]
  rw [quarter_principal_finite_570 hx]
  norm_num only [hfloor, hw, hz, zero_mul, mul_zero, sub_zero, zero_sub] at hu hf
  linarith only [hu, hf]

private theorem quarter_weight_smooth {X : ℝ} (hX : 0 < X) :
    let W := quarterWeight570 X
    ContDiffOn ℝ 2 W (Set.Ioi 0) ∧ ContDiffOn ℝ 1 (fun t ↦ t * deriv W t) (Set.Ioi 0) := by
  intro W
  have hw : ContDiffOn ℝ 2 W (Set.Ioi 0) := by
    intro t ht
    have ht' : 0 < t := ht
    have hs : ContDiffAt ℝ 2 Real.sqrt t := Real.contDiffAt_sqrt ht'.ne'
    apply ContDiffAt.contDiffWithinAt
    unfold W quarterWeight570
    dsimp only
    fun_prop (disch := positivity)
  exact ⟨hw, contDiffOn_id.mul (hw.deriv_of_isOpen isOpen_Ioi (by decide))⟩

/-- Integrating the second logarithmic derivative against one logarithmic atom
recovers the weight at v, with both endpoint terms at b. -/
theorem quarter_log_atom_570 {X v b : ℝ} (hX : 0 < X) (hv : 0 < v) (hb : v ≤ b) :
    let W := quarterWeight570 X
    let P := fun t ↦ t * deriv W t
    W v = (∫ t in v..b, Real.log (t / v) * deriv P t) - Real.log (b / v) * P b + W b := by
  intro W P
  obtain ⟨hw, hp⟩ := quarter_weight_smooth hX
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
theorem quarter_second_abel_570 {X b : ℝ} (hX : 0 < X) (hb : 0 ≤ b)
    (hs : Real.log (b / X) ≤ 14 / 5) :
    let W := quarterWeight570 X
    let P := fun t ↦ t * deriv W t
    (∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X n).re) =
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
  rw [quarter_summand_570 hX hn0
      ((Real.log_le_log (div_pos hnr hX) (div_le_div_of_nonneg_right hnb hX.le)).trans hs)]
  have h := quarter_log_atom_570 hX hnr hnb
  change W n = _ at h
  change W n * _ = _
  rw [h]
  unfold AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm
  dsimp only [W, P]
  ring

private theorem log_sum_integral {b : ℝ} (hb : 1 ≤ b) {Q : ℝ → ℝ}
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

/-- The second Abel formula for the supported principal prefix has a single integral
of the logarithmically weighted Mangoldt sum, with explicit boundary terms at b. -/
theorem quarter_log_integral_570 {X b : ℝ} (hX : 0 < X) (hb : 1 ≤ b)
    (hs : Real.log (b / X) ≤ 14 / 5) :
    let W := quarterWeight570 X
    let P := fun t ↦ t * deriv W t
    (∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X n).re) =
      (∫ t in (1 : ℝ)..b, AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * deriv P t) -
          P b * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum b +
        W b * Chebyshev.psi b := by
  intro W P
  obtain ⟨hw, hp⟩ := quarter_weight_smooth hX
  have hq :=
    (hp.continuousOn_deriv_of_isOpen isOpen_Ioi (by decide)).mono
      (show Set.Icc 1 b ⊆ Set.Ioi 0 from fun t ht ↦ zero_lt_one.trans_le ht.1)
  exact
    (quarter_second_abel_570 hX (zero_le_one.trans hb) hs).trans (by rw [log_sum_integral hb hq])

/-- At the upper support endpoint the fifth-order zero kills both boundary terms. -/
theorem quarter_support_jet_570 {X : ℝ} (hx : 0 < X) :
    let B := X * Real.exp (14 / 5)
    quarterWeight570 X B = 0 ∧ deriv (quarterWeight570 X) B = 0 := by
  intro B
  let v := fun t : ℝ ↦ (2 * (7 / 5) - Real.log (t / X)) / (2 * (25 / 51))
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
  have he : quarterWeight570 X = fun t ↦ v t ^ 5 * g t := by
    funext t
    dsimp only [quarterWeight570, v, g]
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

/-- The difference of four cutoff sums and the full series equals two log-weighted
Mangoldt integrals with only the endpoint terms at X surviving. -/
theorem quarter_combined_log_570 {X : ℝ} (hX : 1 ≤ X) :
    let B := X * Real.exp (14 / 5)
    let S := fun n : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X n).re
    let W := quarterWeight570 X
    let P := fun t ↦ t * deriv W t
    let M := AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum
    4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) =
      4 * (∫ t in (1 : ℝ)..X, M t * deriv P t) - (∫ t in (1 : ℝ)..B, M t * deriv P t) -
          4 * P X * M X +
        4 * W X * Chebyshev.psi X := by
  intro B S W P M
  have hx := zero_lt_one.trans_le hX
  have hb :=
    hX.trans (le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 14 / 5)))
  have hlog : Real.log (B / X) = 14 / 5 := by
    dsimp only [B]
    rw [mul_div_cancel_left₀ _ hx.ne', Real.log_exp]
  have hf := quarter_log_integral_570 hx hb hlog.le
  obtain ⟨hw, hd⟩ := quarter_support_jet_570 hx
  dsimp only at hf
  rw [hd, hw, mul_zero, zero_mul, sub_zero, zero_mul, add_zero] at hf
  have hu :=
    quarter_log_integral_570 hx hX
      (by
        rw [div_self hx.ne', Real.log_one]; norm_num only)
  dsimp only [S, W, P, M, B]
  rw [quarter_principal_finite_570 hx, hf, hu]
  ring

/-- Evaluate the linear and logarithmic main terms in the double Abel integral.
The free coefficient c can be specialized to log(2 pi) for the centered remainder. -/
theorem quarter_centering_integral_570 {X b : ℝ} (hx : 0 < X) (hb : 1 ≤ b) (c : ℝ) :
    let W := quarterWeight570 X
    let P := fun t ↦ t * deriv W t
    (∫ t in (1 : ℝ)..b, (t - c * Real.log t) * deriv P t) =
      (b - c * Real.log b) * P b - (b - c) * W b - P 1 + (1 - c) * W 1 +
        ∫ t in (1 : ℝ)..b, W t := by
  intro W P
  obtain ⟨hw, hp⟩ := quarter_weight_smooth hx
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
theorem quarter_centered_prefix_570 {X b : ℝ} (hx : 0 < X) (hb : 1 ≤ b)
    (hs : Real.log (b / X) ≤ 14 / 5) (c : ℝ) :
    let W := quarterWeight570 X
    let P := fun t ↦ t * deriv W t
    let E := fun t ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - (t - c * Real.log t)
    (∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X n).re) =
      (∫ t in (1 : ℝ)..b, W t) + (∫ t in (1 : ℝ)..b, E t * deriv P t) - P b * E b +
            W b * (Chebyshev.psi b - b + c) -
          P 1 +
        (1 - c) * W 1 := by
  intro W P E
  obtain ⟨_, hp⟩ := quarter_weight_smooth hx
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
  have hh := quarter_log_integral_570 hx hb hs
  have hc := quarter_centering_integral_570 hx hb c
  dsimp only [E, W, P] at *
  simp_rw [sub_mul (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum _) _ _]
  rw [intervalIntegral.integral_sub (f := fun t ↦
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * deriv P t) (g := fun t ↦
      (t - c * Real.log t) * deriv P t) hi.intervalIntegrable hj.intervalIntegrable]
  linarith only [hh, hc]

/-- Center the difference of four principal prefixes and the full principal series.
The support jet vanishes at B, leaving a weighted difference of two remainder integrals,
one remainder value at X, and explicit boundary terms. -/
theorem quarter_centered_difference_570 {X : ℝ} (hX : 1 ≤ X) :
    let B := X * Real.exp (14 / 5)
    let S := fun n : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X n).re
    let W := quarterWeight570 X
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
    hX.trans (le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 14 / 5)))
  have hlog : Real.log (B / X) = 14 / 5 := by
    dsimp only [B]
    rw [mul_div_cancel_left₀ _ hx.ne', Real.log_exp]
  have hf := quarter_centered_prefix_570 hx hb hlog.le c
  have hu :=
    quarter_centered_prefix_570 hx hX
      (by
        rw [div_self hx.ne', Real.log_one]; norm_num only)
      c
  obtain ⟨hw, hd⟩ := quarter_support_jet_570 hx
  dsimp only at hf hu
  rw [hd, hw, mul_zero, zero_mul, sub_zero, zero_mul, add_zero] at hf
  dsimp only [S, W, P, E, B]
  rw [quarter_principal_finite_570 hx, hf, hu]
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
