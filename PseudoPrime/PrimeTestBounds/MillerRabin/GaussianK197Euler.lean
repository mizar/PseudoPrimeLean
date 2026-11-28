/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Profile
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterProfileWeight663
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Profile
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterProfile663
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCombinedEuler137
import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.NaturalTailLimit

/-! # Nonnegativity of the combined K197 Euler weight -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A rational lower polynomial for the centered K197 profile. -/
private def lowerPoly (v : ℝ) : ℝ :=
  4.028662 - 7.025620 * v + 2.061370 * v ^ 2

/-- Apply the lower coefficient endpoints with nonnegative displacement. -/
private theorem profile_lower {v : ℝ} (hv : 23 / 2 ≤ v) :
    lowerPoly (v - 23 / 2) ≤ gaussianProfile197 v := by
  rw [profile_expand_197]
  have h := profile_coeff_bounds_197
  have h₁ := mul_le_mul_of_nonneg_right h.2.1.1 (sub_nonneg.mpr hv)
  have h₂ := mul_le_mul_of_nonneg_right h.2.2.1 (sq_nonneg (v - 23 / 2))
  unfold lowerPoly
  linarith only [h.1.1, h₁, h₂]

/-- The rational lower polynomial increases on the displacement range above two. -/
private theorem lower_poly_mono {v w : ℝ} (hw : 2 ≤ w) (hv : w ≤ v) :
    lowerPoly w ≤ lowerPoly v := by
  have h :=
    mul_nonneg (sub_nonneg.mpr hv)
      (show 0 ≤ 2.061370 * (v + w) - 7.025620 by linarith only [hw, hv])
  unfold lowerPoly
  nlinarith only [h]

/-- All K197 radii give at least 0.111 in the centered logarithmic coordinate. -/
private theorem radius_log_lower {r : ℝ} (hr : 332.15 ≤ r) : 23 / 2 + 0.111 ≤ 2 * Real.log r := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 6643 / 20) (j := 9) (n := 27) (lo := 5.80555)
        (hi := 6) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at h
  have hr' : (6643 / 20 : ℝ) ≤ r := by linarith only [hr]
  linarith only [h, Real.log_le_log (by norm_num only : (0 : ℝ) < 6643 / 20) hr']

/-- On a closed subinterval, bound the forward weight at the left exponential
and the right polynomial endpoint. -/
private theorem forward_box {r u l b E : ℝ} (hr : 328 ≤ r) (hu : u ∈ Set.Icc l b) (hb : b ≤ 21 / 8)
    (hE₀ : 0 ≤ E) (hE : E ≤ Real.exp ((11 / 5) * l)) :
    250 * E * (21 / 8 - b) ^ 5 ≤ quarterForward663 r u := by
  have he : E ≤ Real.exp ((11 / 5) * u) := hE.trans (Real.exp_le_exp.mpr (by linarith only [hu.1]))
  have hp := pow_le_pow_left₀ (sub_nonneg.mpr hb) (sub_le_sub_left hu.2 (21 / 8)) 5
  have hm :=
    mul_le_mul (forward_scale_lower hr) he hE₀
      ((by norm_num only : (0 : ℝ) ≤ 30000).trans (forward_scale_lower hr))
  have h :=
    mul_le_mul hm hp (pow_nonneg (sub_nonneg.mpr hb) _)
      (mul_nonneg ((by norm_num only : (0 : ℝ) ≤ 30000).trans (forward_scale_lower hr))
        (Real.exp_pos _).le)
  unfold quarterForward663
  linarith only [h]

private theorem exp_lower_80 : (80 : ℝ) ≤ Real.exp ((11 / 5) * 2) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 80) (j := 7) (n := 27) (lo := 4) (hi := 4.4)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at h
  exact (Real.log_le_iff_le_exp (by norm_num only)).mp (by linarith only [h])

private theorem exp_lower_200 : (200 : ℝ) ≤ Real.exp ((11 / 5) * 2.45) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 200) (j := 8) (n := 27) (lo := 5) (hi := 5.35)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at h
  exact (Real.log_le_iff_le_exp (by norm_num only)).mp (by linarith only [h])

private theorem exp_lower_250 : (250 : ℝ) ≤ Real.exp ((11 / 5) * 2.53) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 250) (j := 8) (n := 27) (lo := 5) (hi := 5.55)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at h
  exact (Real.log_le_iff_le_exp (by norm_num only)).mp (by linarith only [h])

/-- For the middle subintervals, combine the two endpoint estimates with
the forward and signed profile weights evaluated at the same radius. -/
private theorem combined_box {r u l b E : ℝ} (hr : 332.15 ≤ r) (hu : u ∈ Set.Icc l b) (hl : 2 ≤ l)
    (hb : b ≤ 21 / 8) (hE₀ : 0 ≤ E) (hE : E ≤ Real.exp ((11 / 5) * l))
    (hcheck : 0 ≤ lowerPoly (0.111 + l) + 250 * E * (21 / 8 - b) ^ 5) :
    0 ≤ gaussianProfile197 (2 * Real.log r + u) + quarterForward663 r u := by
  have hlog := radius_log_lower hr
  have hp :=
    lower_poly_mono (v := 2 * Real.log r + u - 23 / 2) (show 2 ≤ 0.111 + l by linarith only [hl])
      (by linarith only [hlog, hu.1])
  have hg := profile_lower (show 23 / 2 ≤ 2 * Real.log r + u by linarith only [hlog, hl, hu.1])
  have hf := forward_box ((by norm_num only : (328 : ℝ) ≤ 332.15).trans hr) hu hb hE₀ hE
  linarith only [hp, hg, hf, hcheck]

/-- At nonnegative relative logarithm through 2.45, the forward weight covers
the global negative part of the lower quadratic. -/
private theorem combined_low {r u : ℝ} (hr : 332.15 ≤ r) (hu : u ∈ Set.Icc 0 2.45) :
    0 ≤ gaussianProfile197 (2 * Real.log r + u) + quarterForward663 r u := by
  have hlog := radius_log_lower hr
  have hg := profile_lower (show 23 / 2 ≤ 2 * Real.log r + u by linarith only [hlog, hu.1])
  have hp : -2 ≤ lowerPoly (2 * Real.log r + u - 23 / 2) := by
    unfold lowerPoly
    nlinarith only [sq_nonneg (2 * Real.log r + u - 23 / 2 - 7.025620 / (2 * 2.061370))]
  have hr' : (328 : ℝ) ≤ r := (by norm_num only : (328 : ℝ) ≤ 332.15).trans hr
  by_cases h : u ≤ 2
  · have hf :=
      forward_box (E := 1) hr' ⟨hu.1, h⟩ (by norm_num only) (by norm_num only)
        (by norm_num only [mul_zero, Real.exp_zero])
    linarith only [hg, hp, hf]
  · have hf :=
      forward_box hr' ⟨le_of_not_ge h, hu.2⟩ (by norm_num only) (by norm_num only) exp_lower_80
    linarith only [hg, hp, hf]

/-- At relative logarithm at least 2.57, the centered quadratic itself is nonnegative. -/
private theorem profile_high {r u : ℝ} (hr : 332.15 ≤ r) (hu : 2.57 ≤ u) :
    0 ≤ gaussianProfile197 (2 * Real.log r + u) := by
  have hl := radius_log_lower hr
  have hp :=
    lower_poly_mono (w := 2.681) (v := 2 * Real.log r + u - 23 / 2) (by norm_num only)
      (by linarith only [hl, hu])
  exact
    ((by norm_num only [lowerPoly] : 0 ≤ lowerPoly 2.681).trans hp).trans
      (profile_lower (by linarith only [hl, hu]))

/-- For every radius used by K197 and every point past the witness cutoff,
the normalized forward and reflected weights have nonnegative sum. -/
theorem gaussian_profile_nonneg_197 {r u : ℝ} (hr : 332.15 ≤ r) (hu : 0 ≤ u) :
    0 ≤
      gaussianProfile197 (2 * Real.log r + u) +
        if u ≤ 21 / 8 then quarterForward663 r u else 0 := by
  by_cases hb : u ≤ 21 / 8
  · rw [ite_eq_left hb]
    by_cases h₁ : u ≤ 2.45
    · exact combined_low hr ⟨hu, h₁⟩
    by_cases h₂ : u ≤ 2.5
    · exact
        combined_box hr ⟨le_of_not_ge h₁, h₂⟩ (by norm_num only) (by norm_num only)
          (by norm_num only) exp_lower_200 (by norm_num only [lowerPoly])
    by_cases h₃ : u ≤ 2.53
    · exact
        combined_box (l := 2.5) hr ⟨le_of_not_ge h₂, h₃⟩ (by norm_num only) (by norm_num only)
          (by norm_num only) (exp_lower_200.trans (Real.exp_le_exp.mpr (by norm_num only)))
          (by norm_num only [lowerPoly])
    by_cases h₄ : u ≤ 2.55
    · exact
        combined_box hr ⟨le_of_not_ge h₃, h₄⟩ (by norm_num only) (by norm_num only)
          (by norm_num only) exp_lower_250 (by norm_num only [lowerPoly])
    by_cases h₅ : u ≤ 2.56
    · exact
        combined_box (l := 2.55) hr ⟨le_of_not_ge h₄, h₅⟩ (by norm_num only) (by norm_num only)
          (by norm_num only) (exp_lower_250.trans (Real.exp_le_exp.mpr (by norm_num only)))
          (by norm_num only [lowerPoly])
    by_cases h₆ : u ≤ 2.57
    · exact
        combined_box (l := 2.56) hr ⟨le_of_not_ge h₅, h₆⟩ (by norm_num only) (by norm_num only)
          (by norm_num only) (exp_lower_250.trans (Real.exp_le_exp.mpr (by norm_num only)))
          (by norm_num only [lowerPoly])
    have hf : 0 ≤ quarterForward663 r u := by
      have h := sub_nonneg.mpr hb
      unfold quarterForward663
      positivity
    exact add_nonneg (profile_high hr (le_of_not_ge h₆)) hf
  · rw [ite_eq_right hb, add_zero]
    exact profile_high hr ((by norm_num only : (2.57 : ℝ) ≤ 21 / 8).trans (le_of_not_ge hb))

/-- The combined Euler expression on the unknown support loses at most
four copies of the K197 reflected profile. -/
theorem gaussian_profile_euler_197 {r u a : ℝ} (hr : 332.15 ≤ r) (hu : 0 ≤ u)
    (ha : a ∈ Set.Icc 0 4) :
    let g := gaussianProfile197 (2 * Real.log r + u)
    let f := if u ≤ 21 / 8 then quarterForward663 r u else 0
    (-4) * g ≤ (4 - a) * f - a * g := by
  intro g f
  have h := common_euler_lower ha.1 ha.2 f g
  have hfg : 0 ≤ f + g := by
    rw [add_comm]
    exact gaussian_profile_nonneg_197 hr hu
  rw [max_eq_left (neg_nonpos.mpr hfg), mul_zero, sub_zero] at h
  exact h

/-- At a physical argument above the tested cutoff, the common Euler
deficit is bounded with the forward kernel and reflected weight in their
original units. The forward weight is zero beyond its support. -/
theorem gaussian_physical_euler_197 {r t a : ℝ} (hr : 332.15 ≤ r) (ht : r ^ 2 ≤ t)
    (ha : a ∈ Set.Icc 0 4) :
    let f := if Real.log (t / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) t else 0
    let g := gaussianDensity197 t
    (-4) * g ≤ (4 - a) * f - a * g := by
  intro f g
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 332.15).trans_le hr
  have hX : 0 < r ^ 2 := sq_pos_of_pos hr₀
  have ht₀ := hX.trans_le ht
  let u := Real.log (t / r ^ 2)
  have hu : 0 ≤ u := Real.log_nonneg ((le_div_iff₀ hX).mpr (by simpa only [one_mul] using ht))
  have hl : 2 * Real.log r + u = Real.log t := by
    dsimp only [u]
    rw [Real.log_div ht₀.ne' hX.ne', Real.log_pow, Nat.cast_ofNat]
    ring
  have hf : t ^ (-(8 / 5) : ℝ) * (if u ≤ 21 / 8 then quarterForward663 r u else 0) = f := by
    dsimp only [f, u]
    rw [mul_ite, mul_zero, quarter_forward_weight_663 hr₀ ht₀]
  have h :=
    mul_le_mul_of_nonneg_left (gaussian_profile_euler_197 hr hu ha)
      (Real.rpow_nonneg ht₀.le (-(8 / 5) : ℝ))
  rw [hl] at h
  dsimp only [g, gaussianDensity197]
  linear_combination h + (4 - a) * hf

/-- The forward part has finite support, and a bounded common trace
preserves absolute convergence of the reflected series. -/
private theorem common_tail_summable {r : ℝ} (hr : 332.15 ≤ r) (a : ℕ → ℝ)
    (ha : ∀ n, a n ∈ Set.Icc 0 4) :
    Summable
      (fun n : ℕ ↦
        ArithmeticFunction.vonMangoldt n *
          ((4 - a n) *
              (if Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n else 0) -
            a n * gaussianDensity197 n)) := by
  have hx := sq_pos_of_pos ((by norm_num only : (0 : ℝ) < 332.15).trans_le hr)
  let f := fun n : ℕ ↦
    ArithmeticFunction.vonMangoldt n *
      ((4 - a n) * (if Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n else 0))
  have hf : Summable f := by
    apply summable_of_ne_finset_zero (s := Finset.Iic ⌊Real.exp (21 / 8) * r ^ 2⌋₊)
    intro n hn
    have hn' := Nat.lt_of_floor_lt (lt_of_not_ge (fun hh ↦ hn (Finset.mem_Iic.mpr hh)))
    have hp : 0 < (n : ℝ) := (mul_pos (Real.exp_pos _) hx).trans hn'
    have hs : ¬Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 := by
      intro h
      exact (not_le_of_gt hn') ((div_le_iff₀ hx).mp ((Real.log_le_iff_le_exp (div_pos hp hx)).mp h))
    simp only [f, ite_eq_right hs, mul_zero]
  have hg :
    Summable (fun n : ℕ ↦ a n * (ArithmeticFunction.vonMangoldt n * gaussianDensity197 n)) := by
    apply Summable.of_norm_bounded (gaussian_profile_summable_197.norm.mul_left 4)
    intro n
    rw [norm_mul, Real.norm_of_nonneg (ha n).1]
    exact mul_le_mul_of_nonneg_right (ha n).2 (norm_nonneg _)
  exact
    (hf.sub hg).congr
      (fun n ↦ by
        dsimp only [f, Pi.sub_apply]; ring)

/-- At a retained atom, the reflected density costs at most twice the
common inverse power. -/
private theorem retained_atom_lower {r : ℝ} (hr : 332.15 ≤ r) {n : ℕ} (hn : r ^ 2 ≤ (n : ℝ)) :
    -(2 : ℝ) * (n : ℝ) ^ (-(8 / 5) : ℝ) ≤ gaussianDensity197 n := by
  have hlog := radius_log_lower hr
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 332.15).trans_le hr
  have h := Real.log_le_log (sq_pos_of_pos hr₀) hn
  rw [Real.log_pow, Nat.cast_ofNat] at h
  have hP := profile_lower (show 23 / 2 ≤ Real.log n by linarith only [hlog, h])
  have hl : -2 ≤ lowerPoly (Real.log n - 23 / 2) := by
    unfold lowerPoly
    nlinarith only [sq_nonneg (Real.log n - 23 / 2 - 7.025620 / (2 * 2.061370))]
  unfold gaussianDensity197
  rw [mul_comm (-(2 : ℝ))]
  exact mul_le_mul_of_nonneg_left (hl.trans hP) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- Retain the known passing atoms in the common Euler comparison with their full signed density.
The finite retained set and the
remaining infinite tail use the same trace deficit. -/
theorem gaussian_euler_retained_signed_197 {r T : ℝ} (hr : 332.15 ≤ r) (a : ℕ → ℝ)
    (ha : ∀ n, a n ∈ Set.Icc 0 4) (K : Finset ℕ) (hK : ∀ n ∈ K, r ^ 2 < (n : ℝ))
    (hpass : ∀ n ∈ K, a n = 0)
    (hmain :
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * gaussianDensity197 n) -
          ∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, ArithmeticFunction.vonMangoldt n * gaussianDensity197 n ≤
        T) :
    let f := fun n : ℕ ↦
      if Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n else 0
    let w := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n * ((4 - a n) * f n - a n * gaussianDensity197 n)
    (-4 * T) + (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * (f n + gaussianDensity197 n))) ≤
      (∑' n : ℕ, w n) - ∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, w n := by
  intro f w
  let g := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * gaussianDensity197 n
  let c := fun n : ℕ ↦ 4 * (ArithmeticFunction.vonMangoldt n * (f n + gaussianDensity197 n))
  have hg :=
    AnalyticNumberTheory.Arithmetic.tendsto_tail_prefix g
      (by simp only [g, ArithmeticFunction.map_zero, zero_mul]) gaussian_profile_summable_197
      (r ^ 2)
  have hw :=
    AnalyticNumberTheory.Arithmetic.tendsto_tail_prefix w
      (by simp only [w, ArithmeticFunction.map_zero, zero_mul]) (common_tail_summable hr a ha)
      (r ^ 2)
  have hs :=
    le_of_tendsto_of_tendsto ((hg.const_mul (-4)).add_const (∑ n ∈ K, c n)) hw
      (by
        filter_upwards [Filter.eventually_ge_atTop (K.sup id)] with N hN
        have hKS : K ⊆ Finset.Ioc ⌊r ^ 2⌋₊ N := fun n hn ↦
          Finset.mem_Ioc.mpr
            ⟨Nat.floor_lt (by positivity) |>.mpr (hK n hn), (Finset.le_sup (f := id) hn).trans hN⟩
        rw [Finset.mul_sum, ←
          Finset.sum_filter_add_sum_filter_not (s := Finset.Ioc ⌊r ^ 2⌋₊ N) (p := fun n ↦ n ∈ K)]
        rw [show (Finset.Ioc ⌊r ^ 2⌋₊ N).filter (fun n ↦ n ∈ K) = K
            by
            ext n
            simp only [Finset.mem_filter]
            exact ⟨And.right, fun hn ↦ ⟨hKS hn, hn⟩⟩]
        rw [add_assoc, add_comm _ (∑ n ∈ K, c n), ← add_assoc, ← Finset.sum_add_distrib]
        rw [←
          Finset.sum_filter_add_sum_filter_not (s := Finset.Ioc ⌊r ^ 2⌋₊ N) (p := fun n ↦ n ∈ K)
            (f := w)]
        rw [show (Finset.Ioc ⌊r ^ 2⌋₊ N).filter (fun n ↦ n ∈ K) = K
            by
            ext n
            simp only [Finset.mem_filter]
            exact ⟨And.right, fun hn ↦ ⟨hKS hn, hn⟩⟩]
        apply add_le_add
        · apply Finset.sum_le_sum
          intro n hn
          dsimp only [w, g, c]
          rw [hpass n hn]
          exact le_of_eq (by ring)
        · apply Finset.sum_le_sum
          intro n hn
          have hn' := (Finset.mem_filter.mp hn).1
          have ht := (Nat.lt_of_floor_lt (Finset.mem_Ioc.mp hn').1).le
          have h :=
            mul_le_mul_of_nonneg_left (gaussian_physical_euler_197 hr ht (ha n))
              (ArithmeticFunction.vonMangoldt_nonneg (n := n))
          dsimp only [w, f, g]
          linear_combination h)
  dsimp only [c, g] at hs
  linarith only [hs, hmain]

/-- Combine the signed Abel estimate with the full Euler tail and any
retained finite set of passing atoms above the K197 witness cutoff. -/
theorem gaussian_euler_abel_signed_197 (hRH : RiemannHypothesis) {r : ℝ} (hr : 332.15 ≤ r)
    (a : ℕ → ℝ) (ha : ∀ n, a n ∈ Set.Icc 0 4) (K : Finset ℕ) (hK : ∀ n ∈ K, r ^ 2 < (n : ℝ))
    (hpass : ∀ n ∈ K, a n = 0) :
    let x := r ^ 2
    let f := fun n : ℕ ↦ if Real.log ((n : ℝ) / x) ≤ 21 / 8 then quarterWeight656 x n else 0
    let w := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n * ((4 - a n) * f n - a n * gaussianDensity197 n)
    let T :=
      (∫ t in Set.Ioi x, gaussianDensity197 t) - (Chebyshev.psi x - x) * gaussianDensity197 x +
        gaussianAbelError197 x
    (-4 * T) + (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * (f n + gaussianDensity197 n))) ≤
      (∑' n : ℕ, w n) - ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w n := by
  have hx : (1423 : ℝ) ≤ r ^ 2 :=
    (by norm_num only : (1423 : ℝ) ≤ 332.15 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hr 2)
  have hl : 23 / 2 ≤ Real.log (r ^ 2) := by
    rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [radius_log_lower hr]
  exact
    gaussian_euler_retained_signed_197 hr a ha K hK hpass
      (gaussian_profile_tail_upper_197 hRH hx hl)

/-- Retain the known passing atoms in the common Euler comparison while
charging their reflected negative parts. The finite retained set and the
remaining infinite tail use the same trace deficit. -/
theorem gaussian_euler_retained_197 {r T : ℝ} (hr : 332.15 ≤ r) (a : ℕ → ℝ)
    (ha : ∀ n, a n ∈ Set.Icc 0 4) (K : Finset ℕ) (hK : ∀ n ∈ K, r ^ 2 < (n : ℝ))
    (hpass : ∀ n ∈ K, a n = 0)
    (hmain :
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * gaussianDensity197 n) -
          ∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, ArithmeticFunction.vonMangoldt n * gaussianDensity197 n ≤
        T) :
    let f := fun n : ℕ ↦
      if Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n else 0
    let w := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n * ((4 - a n) * f n - a n * gaussianDensity197 n)
    (-4 * T) + (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * f n)) -
        (∑ n ∈ K, 8 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(8 / 5) : ℝ))) ≤
      (∑' n : ℕ, w n) - ∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, w n := by
  intro f w
  have hs := gaussian_euler_retained_signed_197 hr a ha K hK hpass hmain
  change
    (-4 * T) + (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * (f n + gaussianDensity197 n))) ≤
      _ at hs
  have hcredit :
    (∑ n ∈ K, -(8 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(8 / 5) : ℝ)))) ≤
      ∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * gaussianDensity197 n) := by
    apply Finset.sum_le_sum
    intro n hn
    linear_combination
      mul_le_mul_of_nonneg_left (retained_atom_lower hr (hK n hn).le)
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4)
          (ArithmeticFunction.vonMangoldt_nonneg (n := n)))
  simp only [Finset.sum_neg_distrib] at hcredit
  have hsplit (n : ℕ) :
    4 * (ArithmeticFunction.vonMangoldt n * (f n + gaussianDensity197 n)) =
      4 * (ArithmeticFunction.vonMangoldt n * f n) +
        4 * (ArithmeticFunction.vonMangoldt n * gaussianDensity197 n) := by
    ring
  simp only [hsplit, Finset.sum_add_distrib] at hs
  linarith only [hcredit, hs]

/-- Combine the signed Abel estimate with the full Euler tail and any
retained finite set of passing atoms above the K197 witness cutoff. -/
theorem gaussian_euler_abel_197 (hRH : RiemannHypothesis) {r : ℝ} (hr : 332.15 ≤ r) (a : ℕ → ℝ)
    (ha : ∀ n, a n ∈ Set.Icc 0 4) (K : Finset ℕ) (hK : ∀ n ∈ K, r ^ 2 < (n : ℝ))
    (hpass : ∀ n ∈ K, a n = 0) :
    let x := r ^ 2
    let f := fun n : ℕ ↦ if Real.log ((n : ℝ) / x) ≤ 21 / 8 then quarterWeight656 x n else 0
    let w := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n * ((4 - a n) * f n - a n * gaussianDensity197 n)
    let T :=
      (∫ t in Set.Ioi x, gaussianDensity197 t) - (Chebyshev.psi x - x) * gaussianDensity197 x +
        gaussianAbelError197 x
    (-4 * T) + (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * f n)) -
        (∑ n ∈ K, 8 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(8 / 5) : ℝ))) ≤
      (∑' n : ℕ, w n) - ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w n := by
  have hx : (1423 : ℝ) ≤ r ^ 2 :=
    (by norm_num only : (1423 : ℝ) ≤ 332.15 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hr 2)
  have hl : 23 / 2 ≤ Real.log (r ^ 2) := by
    rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [radius_log_lower hr]
  exact gaussian_euler_retained_197 hr a ha K hK hpass (gaussian_profile_tail_upper_197 hRH hx hl)

end PseudoPrime.PrimeTestBounds.MillerRabin
