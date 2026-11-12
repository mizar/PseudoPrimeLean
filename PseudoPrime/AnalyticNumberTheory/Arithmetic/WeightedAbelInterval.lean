/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedAbel
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import PseudoPrime.AnalyticNumberTheory.Arithmetic.NaturalTailLimit

/-! # Centered Abel summation on arbitrary nonnegative intervals -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Abel summation on a nonnegative interval, retaining both psi boundary values. -/
private theorem mangoldt_abel_interval {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {f : ℝ → ℝ}
    (hd : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hi : MeasureTheory.IntegrableOn (deriv f) (Set.Icc a b)) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * f n) =
      f b * Chebyshev.psi b - f a * Chebyshev.psi a -
        ∫ t : ℝ in a..b, deriv f t * Chebyshev.psi t := by
  have h := sum_mul_eq_sub_sub_integral_mul (c := ArithmeticFunction.vonMangoldt) ha hab hd hi
  simpa only [← Chebyshev.psi_eq_sum_Icc, intervalIntegral.integral_of_le hab, mul_comm] using h

/-- The centered psi integral is the difference of its psi and linear parts. -/
private theorem centered_psi_integral {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {f : ℝ → ℝ}
    (hi : MeasureTheory.IntegrableOn (deriv f) (Set.Icc a b)) :
    (∫ t : ℝ in a..b, (Chebyshev.psi t - t) * deriv f t) =
      (∫ t : ℝ in a..b, deriv f t * Chebyshev.psi t) - ∫ t : ℝ in a..b, t * deriv f t := by
  have ht := hi.mul_continuousOn continuousOn_id isCompact_Icc
  have ht' : IntervalIntegrable (fun t : ℝ ↦ t * deriv f t) MeasureTheory.volume a b := by
    simpa only [id_eq, mul_comm] using (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr ht
  have hψ := integrableOn_mul_sum_Icc (fun n ↦ ArithmeticFunction.vonMangoldt n) (m := 0) ha hi
  simp only [← Chebyshev.psi_eq_sum_Icc] at hψ
  have hp :
    IntervalIntegrable (fun t : ℝ ↦ Chebyshev.psi t * deriv f t) MeasureTheory.volume a b := by
    simpa only [mul_comm] using (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hψ
  simp only [sub_mul]
  simpa only [mul_comm] using intervalIntegral.integral_sub hp ht'

/-- Integration by parts for a differentiable weight and the identity function. -/
private theorem integral_weight_parts {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hd : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hi : MeasureTheory.IntegrableOn (deriv f) (Set.Icc a b)) :
    (∫ t : ℝ in a..b, f t) + (∫ t : ℝ in a..b, t * deriv f t) = b * f b - a * f a := by
  have hc : ContinuousOn f (Set.Icc a b) := fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt
  have hf : IntervalIntegrable f MeasureTheory.volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hc.integrableOn_Icc
  have hdf : IntervalIntegrable (deriv f) MeasureTheory.volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hi
  have ht := hi.mul_continuousOn continuousOn_id isCompact_Icc
  have ht' : IntervalIntegrable (fun t : ℝ ↦ t * deriv f t) MeasureTheory.volume a b := by
    simpa only [id_eq, mul_comm] using (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr ht
  have hFTC :=
    intervalIntegral.integral_deriv_mul_eq_sub (u := fun t : ℝ ↦ t) (u' := fun _ ↦ (1 : ℝ)) (v := f)
      (v' := deriv f) (fun t _ ↦ hasDerivAt_id t)
      (fun t ht ↦ (hd t (by simpa only [Set.uIcc_of_le hab] using ht)).hasDerivAt)
      intervalIntegrable_const hdf
  simpa only [one_mul, intervalIntegral.integral_add hf ht'] using hFTC

/-- For `0 ≤ a ≤ b` and a differentiable real weight with integrable derivative,
centered Abel summation expresses the Mangoldt sum on `(a,b]` minus its main integral
using both exact Chebyshev error boundary terms and the centered derivative integral.
The explicit lower boundary is retained for subsequent infinite-tail estimates. -/
theorem mangoldt_centered_abel_interval {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {f : ℝ → ℝ}
    (hd : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hi : MeasureTheory.IntegrableOn (deriv f) (Set.Icc a b)) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * f n) - (∫ t : ℝ in a..b, f t) =
      (Chebyshev.psi b - b) * f b - (Chebyshev.psi a - a) * f a -
        ∫ t : ℝ in a..b, (Chebyshev.psi t - t) * deriv f t := by
  have hFTC := integral_weight_parts hab hd hi
  have hAbel := mangoldt_abel_interval ha hab hd hi
  have he := centered_psi_integral (f := f) ha hab hi
  nlinarith only [hFTC, hAbel, he]

/-- Let `a ≥ 0`. If the main integral and centered error integral have limits `M` and `E`,
and the upper Chebyshev boundary term tends to zero, then the finite Mangoldt tails
converge to `M - (psi a - a) * f a - E`. The lower boundary term is retained exactly. -/
theorem mangoldt_centered_abel_tendsto {a M E : ℝ} (ha : 0 ≤ a) {f : ℝ → ℝ}
    (hd : ∀ b : ℝ, a ≤ b → ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hi : ∀ b : ℝ, a ≤ b → MeasureTheory.IntegrableOn (deriv f) (Set.Icc a b))
    (hmain : Filter.Tendsto (fun b : ℝ ↦ ∫ t : ℝ in a..b, f t) Filter.atTop (nhds M))
    (herr :
      Filter.Tendsto (fun b : ℝ ↦ ∫ t : ℝ in a..b, (Chebyshev.psi t - t) * deriv f t) Filter.atTop
        (nhds E))
    (hboundary : Filter.Tendsto (fun b : ℝ ↦ (Chebyshev.psi b - b) * f b) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun b : ℝ ↦ ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * f n)
      Filter.atTop (nhds (M - (Chebyshev.psi a - a) * f a - E)) := by
  have hconst :
    Filter.Tendsto (fun _ : ℝ ↦ (Chebyshev.psi a - a) * f a) Filter.atTop
      (nhds ((Chebyshev.psi a - a) * f a)) :=
    tendsto_const_nhds
  have hlim := ((hmain.add hboundary).sub hconst).sub herr
  have heq :
    ∀ᶠ b : ℝ in Filter.atTop,
      (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * f n) =
        (∫ t : ℝ in a..b, f t) + (Chebyshev.psi b - b) * f b - (Chebyshev.psi a - a) * f a -
          ∫ t : ℝ in a..b, (Chebyshev.psi t - t) * deriv f t := by
    filter_upwards [Filter.eventually_ge_atTop a] with b hb
    have h := mangoldt_centered_abel_interval ha hb (hd b hb) (hi b hb)
    linarith only [h]
  have hres := hlim.congr' (heq.mono (fun _ h ↦ h.symm))
  simpa only [add_zero] using hres

/-- Under the convergence and summability assumptions, the infinite Mangoldt tail equals
the main integral limit minus the exact centered boundary term and centered error integral.
This is the infinite centered Abel identity at an arbitrary nonnegative cutoff. -/
theorem mangoldt_centered_abel_tsum {a M E : ℝ} (ha : 0 ≤ a) {f : ℝ → ℝ}
    (hd : ∀ b : ℝ, a ≤ b → ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hi : ∀ b : ℝ, a ≤ b → MeasureTheory.IntegrableOn (deriv f) (Set.Icc a b))
    (hmain : Filter.Tendsto (fun b : ℝ ↦ ∫ t : ℝ in a..b, f t) Filter.atTop (nhds M))
    (herr :
      Filter.Tendsto (fun b : ℝ ↦ ∫ t : ℝ in a..b, (Chebyshev.psi t - t) * deriv f t) Filter.atTop
        (nhds E))
    (hboundary : Filter.Tendsto (fun b : ℝ ↦ (Chebyshev.psi b - b) * f b) Filter.atTop (nhds 0))
    (hs : Summable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * f n)) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * f n) -
        (∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt n * f n) =
      M - (Chebyshev.psi a - a) * f a - E := by
  have hreal := mangoldt_centered_abel_tendsto ha hd hi hmain herr hboundary
  have hnat :=
    hreal.comp
      (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop)
  have hnat' :
    Filter.Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Ioc ⌊a⌋₊ N, ArithmeticFunction.vonMangoldt n * f n)
      Filter.atTop (nhds (M - (Chebyshev.psi a - a) * f a - E)) := by
    apply Filter.Tendsto.congr (fun N ↦ ?_) hnat
    simp only [Function.comp_apply, Nat.floor_natCast]
  exact
    tendsto_nhds_unique
      (tendsto_tail_prefix _ (by simp only [ArithmeticFunction.map_zero, zero_mul]) hs a) hnat'

/-- An absolute upper bound `K` for the centered error integral gives a tail upper bound
with the exact lower Chebyshev boundary term. All other assumptions match the infinite
centered Abel identity; this avoids discarding information already certified at the cutoff. -/
theorem mangoldt_centered_abel_tsum_le {a M E K : ℝ} (ha : 0 ≤ a) {f : ℝ → ℝ}
    (hd : ∀ b : ℝ, a ≤ b → ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hi : ∀ b : ℝ, a ≤ b → MeasureTheory.IntegrableOn (deriv f) (Set.Icc a b))
    (hmain : Filter.Tendsto (fun b : ℝ ↦ ∫ t : ℝ in a..b, f t) Filter.atTop (nhds M))
    (herr :
      Filter.Tendsto (fun b : ℝ ↦ ∫ t : ℝ in a..b, (Chebyshev.psi t - t) * deriv f t) Filter.atTop
        (nhds E))
    (hboundary : Filter.Tendsto (fun b : ℝ ↦ (Chebyshev.psi b - b) * f b) Filter.atTop (nhds 0))
    (hs : Summable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * f n)) (hE : |E| ≤ K) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * f n) -
        (∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt n * f n) ≤
      M - (Chebyshev.psi a - a) * f a + K := by
  have h := mangoldt_centered_abel_tsum ha hd hi hmain herr hboundary hs
  linarith only [h, (abs_le.mp hE).1]

/-- If `K` bounds the absolute centered error integral, then the full Mangoldt sum differs
from the finite prefix plus main-integral limit and exact boundary correction by at most `K`.
This applies to signed weights without assuming that the weight or its derivative has a sign. -/
theorem mangoldt_centered_abel_tsum_abs {a M E K : ℝ} (ha : 0 ≤ a) {f : ℝ → ℝ}
    (hd : ∀ b : ℝ, a ≤ b → ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hi : ∀ b : ℝ, a ≤ b → MeasureTheory.IntegrableOn (deriv f) (Set.Icc a b))
    (hmain : Filter.Tendsto (fun b : ℝ ↦ ∫ t : ℝ in a..b, f t) Filter.atTop (nhds M))
    (herr :
      Filter.Tendsto (fun b : ℝ ↦ ∫ t : ℝ in a..b, (Chebyshev.psi t - t) * deriv f t) Filter.atTop
        (nhds E))
    (hboundary : Filter.Tendsto (fun b : ℝ ↦ (Chebyshev.psi b - b) * f b) Filter.atTop (nhds 0))
    (hs : Summable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * f n)) (hE : |E| ≤ K) :
    |(∑' n : ℕ, ArithmeticFunction.vonMangoldt n * f n) -
          ((∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt n * f n) + M -
            (Chebyshev.psi a - a) * f a)| ≤
      K := by
  have h := mangoldt_centered_abel_tsum ha hd hi hmain herr hboundary hs
  have he :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * f n) -
        ((∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt n * f n) + M -
          (Chebyshev.psi a - a) * f a) =
      -E := by
    linarith only [h]
  rw [he, abs_neg]
  exact hE

/-- If the weight and centered error kernel are integrable on `(a,∞)`, the full Mangoldt
sum is the finite prefix plus the improper main integral, minus the exact boundary correction
and the improper centered error integral. This form applies to signed differentiable weights. -/
theorem mangoldt_centered_abel_integral {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℝ}
    (hd : ∀ b : ℝ, a ≤ b → ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hi : ∀ b : ℝ, a ≤ b → MeasureTheory.IntegrableOn (deriv f) (Set.Icc a b))
    (hmain : MeasureTheory.IntegrableOn f (Set.Ioi a))
    (herr : MeasureTheory.IntegrableOn (fun t : ℝ ↦ (Chebyshev.psi t - t) * deriv f t) (Set.Ioi a))
    (hboundary : Filter.Tendsto (fun b : ℝ ↦ (Chebyshev.psi b - b) * f b) Filter.atTop (nhds 0))
    (hs : Summable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * f n)) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * f n) -
        (∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt n * f n) =
      (∫ t in Set.Ioi a, f t) - (Chebyshev.psi a - a) * f a -
        ∫ t in Set.Ioi a, (Chebyshev.psi t - t) * deriv f t := by
  apply mangoldt_centered_abel_tsum ha hd hi
  · exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi a hmain Filter.tendsto_id
  · exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi a herr Filter.tendsto_id
  · exact hboundary
  · exact hs

/-- A pointwise Chebyshev error envelope bounds the norm of the centered improper integral.
The majorant `B * |f'|` is integrable; no sign condition on the weight is needed. -/
private theorem centered_integral_abs_le {a : ℝ} {f B : ℝ → ℝ}
    (hB : MeasureTheory.IntegrableOn (fun t : ℝ ↦ B t * |deriv f t|) (Set.Ioi a))
    (hpoint : ∀ t ∈ Set.Ioi a, |Chebyshev.psi t - t| ≤ B t) :
    |∫ t in Set.Ioi a, (Chebyshev.psi t - t) * deriv f t| ≤
      ∫ t in Set.Ioi a, B t * |deriv f t| := by
  have h :=
    MeasureTheory.norm_integral_le_of_norm_le hB
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hpoint t ht) (abs_nonneg _))
  simpa only [Real.norm_eq_abs] using h

/-- An integrable pointwise envelope for the centered error kernel supplies its
integrability. Measurability follows from monotonicity of psi and measurability of derivatives. -/
private theorem centered_integrable_of_majorant {a : ℝ} {f B : ℝ → ℝ}
    (hB : MeasureTheory.IntegrableOn (fun t : ℝ ↦ B t * |deriv f t|) (Set.Ioi a))
    (hpoint : ∀ t ∈ Set.Ioi a, |Chebyshev.psi t - t| ≤ B t) :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ (Chebyshev.psi t - t) * deriv f t) (Set.Ioi a) := by
  apply hB.mono' ?_ ?_
  · exact
      ((Chebyshev.psi_mono.measurable.sub measurable_id).mul
          (measurable_deriv f)).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hpoint t ht) (abs_nonneg _)

/-- An integrable pointwise psi-error envelope bounds the deviation of the full Mangoldt
sum from its finite prefix, main integral, and exact lower boundary correction. This is
valid for signed weights and retains the derivative of the combined weight. -/
theorem mangoldt_centered_abel_error {a : ℝ} (ha : 0 ≤ a) {f B : ℝ → ℝ}
    (hd : ∀ b : ℝ, a ≤ b → ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hi : ∀ b : ℝ, a ≤ b → MeasureTheory.IntegrableOn (deriv f) (Set.Icc a b))
    (hmain : MeasureTheory.IntegrableOn f (Set.Ioi a))
    (hboundary : Filter.Tendsto (fun b : ℝ ↦ (Chebyshev.psi b - b) * f b) Filter.atTop (nhds 0))
    (hs : Summable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * f n))
    (hB : MeasureTheory.IntegrableOn (fun t : ℝ ↦ B t * |deriv f t|) (Set.Ioi a))
    (hpoint : ∀ t ∈ Set.Ioi a, |Chebyshev.psi t - t| ≤ B t) :
    |(∑' n : ℕ, ArithmeticFunction.vonMangoldt n * f n) -
          ((∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt n * f n) +
              (∫ t in Set.Ioi a, f t) -
            (Chebyshev.psi a - a) * f a)| ≤
      ∫ t in Set.Ioi a, B t * |deriv f t| := by
  have herr := centered_integrable_of_majorant hB hpoint
  apply mangoldt_centered_abel_tsum_abs ha hd hi
  · exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi a hmain Filter.tendsto_id
  · exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi a herr Filter.tendsto_id
  · exact hboundary
  · exact hs
  · exact centered_integral_abs_le hB hpoint

end PseudoPrime.AnalyticNumberTheory.Arithmetic
