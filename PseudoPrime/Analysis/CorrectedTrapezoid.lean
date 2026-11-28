/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-! # Corrected trapezoid estimates for unit-step series -/

public section

namespace PseudoPrime.Analysis

/-- The polynomial kernel for the corrected trapezoid rule and its first
four derivatives on a unit interval. The kernel and its first derivative
vanish at both endpoints. -/
private noncomputable def trapKernel : ℕ → ℝ → ℝ
  | 0, x => (x ^ 4 - 2 * x ^ 3 + x ^ 2) / 24
  | 1, x => (4 * x ^ 3 - 6 * x ^ 2 + 2 * x) / 24
  | 2, x => (12 * x ^ 2 - 12 * x + 2) / 24
  | 3, x => x - 1 / 2
  | _ + 4, _ => 1

/-- Integration by parts uses the explicit derivative of each of the
first four kernel polynomials. -/
private theorem trap_kernel_deriv (k : Fin 4) (x : ℝ) :
    HasDerivAt (trapKernel k.val) (trapKernel (k.val + 1) x) x := by
  fin_cases k
  · convert
      ((((hasDerivAt_id x).pow 4).sub (((hasDerivAt_id x).pow 3).const_mul 2)).add
            ((hasDerivAt_id x).pow 2)).div_const
        24 using
      1
    · funext t
      simp only [trapKernel, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
    · norm_num only [trapKernel, id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one, pow_one]
      ring
  · convert
      (((((hasDerivAt_id x).pow 3).const_mul 4).sub (((hasDerivAt_id x).pow 2).const_mul 6)).add
            ((hasDerivAt_id x).const_mul 2)).div_const
        24 using
      1
    · funext t
      simp only [trapKernel, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
    · norm_num only [trapKernel, id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one, pow_one]
      ring
  · convert
      (((((hasDerivAt_id x).pow 2).const_mul 12).sub ((hasDerivAt_id x).const_mul 12)).add_const
            2).div_const
        24 using
      1
    · funext t
      simp only [trapKernel, Pi.sub_apply, Pi.pow_apply, id_eq]
    · norm_num only [trapKernel, id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one, pow_one]
      ring
  · exact (hasDerivAt_id x).sub_const (1 / 2)

/-- Four integrations by parts on a unit interval yield the corrected
trapezoid formula with its signed fourth-derivative remainder. The functions
in the derivative chain are continuous on the closed unit interval. -/
private theorem corrected_trapezoid_unit (f : ℕ → ℝ → ℝ)
    (hf : ∀ k : Fin 4, ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (f k.val) (f (k.val + 1) x) x)
    (hc : ∀ k ≤ 4, ContinuousOn (f k) (Set.Icc (0 : ℝ) 1)) :
    (∫ x in (0 : ℝ)..1, f 0 x) - (f 0 0 + f 0 1) / 2 + (f 1 1 - f 1 0) / 12 =
      ∫ x in (0 : ℝ)..1, trapKernel 0 x * f 4 x := by
  have hk (k : Fin 4) : Continuous (trapKernel k.val) :=
    continuous_iff_continuousAt.mpr (fun x ↦ (trap_kernel_deriv k x).continuousAt)
  have hstep (k : Fin 4) :
    (∫ x in (0 : ℝ)..1, trapKernel k.val x * f (4 - k.val) x) =
      trapKernel k.val 1 * f (3 - k.val) 1 - trapKernel k.val 0 * f (3 - k.val) 0 -
        ∫ x in (0 : ℝ)..1, trapKernel (k.val + 1) x * f (3 - k.val) x := by
    have he : min (0 : ℝ) 1 = 0 := min_eq_left zero_le_one
    have hE : max (0 : ℝ) 1 = 1 := max_eq_right zero_le_one
    have hj : 3 - k.val < 4 := (Nat.sub_le 3 _).trans_lt (by decide)
    have hidx : 3 - k.val + 1 = 4 - k.val := by
      exact (Nat.sub_add_comm (Nat.le_of_lt_succ k.isLt)).symm
    have hfun (x : ℝ) (hx : x ∈ Set.Ioo (min (0 : ℝ) 1) (max 0 1)) :=
      hf ⟨3 - k.val, hj⟩ x (by simpa only [he, hE] using hx)
    simp only [hidx] at hfun
    have hk' : Continuous (trapKernel (k.val + 1)) := by
      fin_cases k <;> unfold trapKernel <;> fun_prop
    have hc₁ := hc (3 - k.val) ((Nat.sub_le 3 _).trans (by decide))
    have hc₂ := hc (4 - k.val) (Nat.sub_le 4 _)
    apply
      intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt (hk k).continuousOn
        (by simpa only [Set.uIcc_of_le zero_le_one] using hc₁) (fun x _ ↦ trap_kernel_deriv k x)
        hfun (hk'.intervalIntegrable _ _)
    exact
      (by simpa only [Set.uIcc_of_le zero_le_one] using hc₂ :
          ContinuousOn (f (4 - k.val)) (Set.uIcc 0 1)).intervalIntegrable
  have h₀ := hstep 0
  have h₁ := hstep 1
  have h₂ := hstep ⟨2, by decide⟩
  have h₃ := hstep ⟨3, by decide⟩
  norm_num only [Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.reduceFinMk, Nat.reduceSub,
    Nat.reduceAdd, trapKernel, zero_pow, one_pow, OfNat.ofNat_ne_zero, zero_mul, mul_zero, sub_zero,
    zero_add, zero_div, one_mul] at h₀ h₁ h₂ h₃
  unfold trapKernel
  linarith only [h₀, h₁, h₂, h₃]

/-- The nonnegative unit kernel has integral 1/720, as follows by
integrating its quartic polynomial. -/
private theorem trap_kernel_integral : (∫ x in (0 : ℝ)..1, trapKernel 0 x) = 1 / 720 := by
  let P (x : ℝ) := (x ^ 5 / 5 - x ^ 4 / 2 + x ^ 3 / 3) / 24
  have hd (x : ℝ) : HasDerivAt P (trapKernel 0 x) x := by
    convert
      (((((hasDerivAt_id x).pow 5).div_const 5).sub (((hasDerivAt_id x).pow 4).div_const 2)).add
            (((hasDerivAt_id x).pow 3).div_const 3)).div_const
        24 using
      1
    · funext t
      simp only [P, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]
    · norm_num only [trapKernel, id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one]
      ring
  have hi : Continuous (trapKernel 0) :=
    continuous_iff_continuousAt.mpr (fun x ↦ (trap_kernel_deriv 0 x).continuousAt)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hd x) (hi.intervalIntegrable _ _)]
  norm_num only [P]

/-- A uniform fourth-derivative bound M on a unit interval bounds the
corrected trapezoid error by M/720. Translation covers arbitrary endpoints. -/
theorem corrected_trapezoid_error (f : ℕ → ℝ → ℝ) (a M : ℝ)
    (hf : ∀ k : Fin 4, ∀ x ∈ Set.Ioo a (a + 1), HasDerivAt (f k.val) (f (k.val + 1) x) x)
    (hc : ∀ k ≤ 4, ContinuousOn (f k) (Set.Icc a (a + 1)))
    (hM : ∀ x ∈ Set.Icc a (a + 1), |f 4 x| ≤ M) :
    |(∫ x in a..a + 1, f 0 x) - (f 0 a + f 0 (a + 1)) / 2 + (f 1 (a + 1) - f 1 a) / 12| ≤
      M / 720 := by
  let g : ℕ → ℝ → ℝ := fun k t ↦ f k (t + a)
  have hg (k : Fin 4) (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (g k.val) (g (k.val + 1) x) x := by
    have ht : x + a ∈ Set.Ioo a (a + 1) := ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
    simpa only [g, Function.comp_def, id_eq, mul_one] using
      (hf k _ ht).comp x ((hasDerivAt_id x).add_const a)
  have hm : Set.MapsTo (fun t : ℝ ↦ t + a) (Set.Icc 0 1) (Set.Icc a (a + 1)) := by
    intro t ht
    exact ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
  have cg (k : ℕ) (hk : k ≤ 4) : ContinuousOn (g k) (Set.Icc 0 1) :=
    (hc k hk).comp (continuous_id.add continuous_const).continuousOn hm
  have he := corrected_trapezoid_unit g hg cg
  dsimp only [g] at he
  rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm 1 a] at he
  rw [he]
  have hk (x : ℝ) : 0 ≤ trapKernel 0 x := by
    rw [show trapKernel 0 x = (x * (1 - x)) ^ 2 / 24 by
        unfold trapKernel; ring]
    exact div_nonneg (sq_nonneg _) (by norm_num only)
  have hI : Continuous (trapKernel 0) :=
    continuous_iff_continuousAt.mpr (fun x ↦ (trap_kernel_deriv 0 x).continuousAt)
  have hi : IntervalIntegrable (fun x ↦ trapKernel 0 x * g 4 x) MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
    exact (hI.continuousOn.mul (cg 4 le_rfl)).integrableOn_compact isCompact_Icc
  have bound (C : ℝ) : IntervalIntegrable (fun x ↦ C * trapKernel 0 x) MeasureTheory.volume 0 1 :=
    (hI.const_mul C).intervalIntegrable _ _
  have upper :=
    intervalIntegral.integral_mono_on zero_le_one hi (bound M)
      (fun x hx ↦ by
        rw [mul_comm (trapKernel 0 x)];
        exact mul_le_mul_of_nonneg_right (le_abs_self _ |>.trans (hM _ (hm hx))) (hk x))
  have lower :=
    intervalIntegral.integral_mono_on zero_le_one (bound (-M)) hi
      (fun x hx ↦ by
        rw [mul_comm (trapKernel 0 x)];
        exact mul_le_mul_of_nonneg_right ((neg_le_neg (hM _ (hm hx))).trans (neg_abs_le _)) (hk x))
  rw [intervalIntegral.integral_const_mul, trap_kernel_integral] at upper lower
  exact abs_le.mpr ⟨by linarith only [lower], by linarith only [upper]⟩

/-- Summing the corrected unit rule telescopes both the endpoint
correction and the first derivative. The error is the sum of the supplied
fourth-derivative bounds, divided by 720. -/
theorem corrected_trapezoid_sum (f : ℕ → ℝ → ℝ) (a : ℝ) (N : ℕ) (M : ℕ → ℝ)
    (hf : ∀ k : Fin 4, ∀ x ∈ Set.Ioo a (a + N), HasDerivAt (f k.val) (f (k.val + 1) x) x)
    (hc : ∀ k ≤ 4, ContinuousOn (f k) (Set.Icc a (a + N)))
    (hM : ∀ n < N, ∀ x ∈ Set.Icc (a + n) (a + n + 1), |f 4 x| ≤ M n) :
    |(∫ x in a..a + N, f 0 x) - (∑ n ∈ Finset.range N, f 0 (a + n)) - (f 0 (a + N) - f 0 a) / 2 +
          (f 1 (a + N) - f 1 a) / 12| ≤
      (∑ n ∈ Finset.range N, M n) / 720 := by
  induction N with
  | zero =>
    simp only [Nat.cast_zero, add_zero, intervalIntegral.integral_same, Finset.sum_range_zero,
      sub_self, zero_div, add_zero, abs_zero, le_refl]
  | succ N ih =>
    rw [Nat.cast_succ, ← add_assoc] at hf hc ⊢
    have hN : a ≤ a + (N : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg N)
    have hs : a + (N : ℝ) ≤ a + N + 1 := le_add_of_nonneg_right zero_le_one
    have h₀ :=
      ih (fun k x hx ↦ hf k x ⟨hx.1, hx.2.trans_le hs⟩)
        (fun k hk ↦ (hc k hk).mono (Set.Icc_subset_Icc le_rfl hs))
        (fun n hn ↦ hM n (hn.trans (Nat.lt_succ_self N)))
    have h₁ :=
      corrected_trapezoid_error f (a + N) (M N) (fun k x hx ↦ hf k x ⟨hN.trans_lt hx.1, hx.2⟩)
        (fun k hk ↦ (hc k hk).mono (Set.Icc_subset_Icc hN le_rfl)) (hM N (Nat.lt_succ_self N))
    have hi (l u : ℝ) (ha : a ≤ l) (hlu : l ≤ u) (hu : u ≤ a + N + 1) :
      IntervalIntegrable (f 0) MeasureTheory.volume l u := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hlu]
      exact
        ((hc 0 (Nat.zero_le _)).mono (Set.Icc_subset_Icc ha hu)).integrableOn_compact isCompact_Icc
    rw [←
      intervalIntegral.integral_add_adjacent_intervals (hi a (a + N) le_rfl hN hs)
        (hi (a + N) (a + N + 1) hN hs le_rfl),
      Finset.sum_range_succ, Finset.sum_range_succ]
    have h := (abs_le.mp h₀)
    have h' := (abs_le.mp h₁)
    exact abs_le.mpr ⟨by linarith only [h.1, h'.1], by linarith only [h.2, h'.2]⟩

/-- On a half-line, summable fourth-derivative bounds control the
corrected trapezoid approximation to the full unit-step series. The function
and its first derivative vanish at infinity, leaving only lower boundary terms. -/
theorem corrected_trapezoid_tsum (f : ℕ → ℝ → ℝ) (a : ℝ) (M : ℕ → ℝ)
    (hf : ∀ k : Fin 4, ∀ x ∈ Set.Ioi a, HasDerivAt (f k.val) (f (k.val + 1) x) x)
    (hc : ∀ k ≤ 4, ContinuousOn (f k) (Set.Ici a))
    (hM : ∀ n : ℕ, ∀ x ∈ Set.Icc (a + n) (a + n + 1), |f 4 x| ≤ M n)
    (hi : MeasureTheory.IntegrableOn (f 0) (Set.Ioi a)) (hs : Summable (fun n : ℕ ↦ f 0 (a + n)))
    (hm : Summable M) (ht₀ : Filter.Tendsto (f 0) Filter.atTop (nhds 0))
    (ht₁ : Filter.Tendsto (f 1) Filter.atTop (nhds 0)) :
    |(∑' n : ℕ, f 0 (a + n)) - ((∫ x in Set.Ioi a, f 0 x) + f 0 a / 2 - f 1 a / 12)| ≤
      (∑' n : ℕ, M n) / 720 := by
  have ht : Filter.Tendsto (fun n : ℕ ↦ a + (n : ℝ)) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [(Filter.tendsto_atTop.mp
          (tendsto_natCast_atTop_atTop :
            Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop))
        (b - a)] with
      n hn
    linarith only [hn]
  have hI := MeasureTheory.intervalIntegral_tendsto_integral_Ioi a hi ht
  have hS := hs.hasSum.tendsto_sum_nat
  have hB₀ := ((ht₀.comp ht).sub_const (f 0 a)).div_const 2
  have hB₁ := ((ht₁.comp ht).sub_const (f 1 a)).div_const 12
  have hlim := (((hI.sub hS).sub hB₀).add hB₁).abs
  have hle :=
    le_of_tendsto_of_tendsto hlim (hm.hasSum.tendsto_sum_nat.div_const 720)
      (Filter.Eventually.of_forall
        (fun N ↦
          corrected_trapezoid_sum f a N M (fun k x hx ↦ hf k x hx.1)
            (fun k hk ↦ (hc k hk).mono (fun _ hx ↦ hx.1)) (fun n _ ↦ hM n)))
  rw [← abs_neg]
  convert hle using 2
  ring

end PseudoPrime.Analysis
