/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.VerticalGrowth
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Local zeta zero counts by Jensen's inequality

The sawtooth growth bound and a nonzero center value allow a direct Jensen
estimate on disks centered at `3+iT`. A radius `37/10` contains all points
with `0 ≤ Re s ≤ 1` and `|Im s-T| ≤ 2`. For large positive heights, the
resulting multiplicity count is bounded by a constant times `log(T+2)`.
-/

noncomputable section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-! ### A numeric lower bound on `‖ζ‖` at a fixed line `Re s = 3` -/

/-- The classical telescoping sum `∑ 1/((n+1)(n+2)) = 1`. -/
theorem hasSum_inv_succ_mul_succ_succ : HasSum (fun n : ℕ => (1 : ℝ) / ((n + 1) * (n + 2))) 1 := by
  have hpartial :
    ∀ N : ℕ, ∑ n ∈ Finset.range N, (1 : ℝ) / ((n + 1) * (n + 2)) = 1 - 1 / (N + 1) := by
    intro N
    induction N with
    | zero =>
      simp only [Finset.range_zero, one_div, mul_inv_rev, Finset.sum_empty, CharP.cast_eq_zero,
        zero_add, ne_eq, one_ne_zero, not_false_eq_true, div_self, sub_self]
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : (k : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (k : ℝ) + 2 ≠ 0 := by positivity
      push_cast
      field_simp [one_div, mul_inv_rev]
      ring
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => by positivity)]
  simp_rw [hpartial]
  have htend : Filter.Tendsto (fun N : ℕ => (1 : ℝ) / (N + 1)) Filter.atTop (nhds 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
    simp only [Function.comp_def, Nat.cast_add, Nat.cast_one] at h
    exact h
  simpa only [one_div, sub_zero] using tendsto_const_nhds.sub htend

theorem tsum_inv_succ_mul_succ_succ : ∑' n : ℕ, (1 : ℝ) / ((n + 1) * (n + 2)) = 1 :=
  hasSum_inv_succ_mul_succ_succ.tsum_eq

/-- `‖ζ(s) - 1‖ ≤ 1/2` for `Re s ≥ 3`, by comparison with the telescoping sum above. -/
theorem norm_riemannZeta_sub_one_le {s : ℂ} (hs : 3 ≤ s.re) : ‖riemannZeta s - 1‖ ≤ 1 / 2 := by
  have hs1 : 1 < s.re := by linarith only [hs]
  have hsumm1 : Summable (fun n : ℕ => (1 : ℂ) / (n + 1 : ℂ) ^ s) := by
    have h := (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs1)
    simpa only [one_div, Nat.cast_add, Nat.cast_one] using h
  have heq : riemannZeta s - 1 = ∑' n : ℕ, (1 : ℂ) / ((n : ℂ) + 2) ^ s := by
    have hz := zeta_eq_tsum_one_div_nat_add_one_cpow hs1
    rw [hz, hsumm1.tsum_eq_zero_add]
    have h0 : (1 : ℂ) / (((0 : ℕ) : ℂ) + 1) ^ s = 1 := by norm_num only [Complex.one_cpow]
    rw [h0]
    have hcongr :
      (∑' n : ℕ, (1 : ℂ) / (((n + 1 : ℕ) : ℂ) + 1) ^ s) =
        ∑' n : ℕ, (1 : ℂ) / ((n : ℂ) + 2) ^ s := by
      apply tsum_congr
      intro n; push_cast; ring_nf
    rw [hcongr]; ring
  have hsummR : Summable (fun n : ℕ => ‖(1 : ℂ) / ((n : ℂ) + 2) ^ s‖) := by
    have h := (summable_nat_add_iff 1).mpr hsumm1
    have h2 : Summable (fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 2) ^ s) := by
      apply h.congr
      intro n; push_cast; ring_nf
    exact h2.norm
  have hsummHalf : Summable (fun n : ℕ => (1 : ℝ) / 2 * (1 / ((n + 1) * (n + 2)))) :=
    hasSum_inv_succ_mul_succ_succ.summable.mul_left
      (1 / 2)
  have hbound : ‖riemannZeta s - 1‖ ≤ ∑' n : ℕ, (1 : ℝ) / 2 * (1 / ((n + 1) * (n + 2))) := by
    rw [heq]
    refine (norm_tsum_le_tsum_norm hsummR).trans ?_
    apply hsummR.tsum_le_tsum _ hsummHalf
    intro n
    rw [norm_div, norm_one]
    have hcast : ((n : ℂ) + 2) = (((n : ℝ) + 2 : ℝ) : ℂ) := by
      push_cast; ring
    have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hn2]
    have hpow : ((n : ℝ) + 2) ^ (3 : ℝ) ≤ ((n : ℝ) + 2) ^ s.re :=
      (Real.rpow_le_rpow_left_iff (by linarith : (1 : ℝ) < (n : ℝ) + 2)).mpr (by linarith)
    have hpow2 : 2 * (((n : ℝ) + 1) * ((n : ℝ) + 2)) ≤ ((n : ℝ) + 2) ^ (3 : ℝ) := by
      rw [show (3 : ℝ) = (2 : ℝ) + 1 from by norm_num only, Real.rpow_add hn2, Real.rpow_two,
        Real.rpow_one]
      nlinarith
    have ha : (0 : ℝ) < 2 * (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by positivity
    have hthis := one_div_le_one_div_of_le ha (hpow2.trans hpow)
    have heqdiv :
      (1 : ℝ) / (2 * (((n : ℝ) + 1) * ((n : ℝ) + 2))) =
        1 / 2 * (1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) := by
      field_simp [one_div, mul_inv_rev]
    rwa [heqdiv] at hthis
  rw [tsum_mul_left,
    tsum_inv_succ_mul_succ_succ] at hbound
  linarith

/-- `‖ζ(s)‖ ≥ 1/2` for `Re s ≥ 3`. -/
theorem norm_riemannZeta_ge {s : ℂ} (hs : 3 ≤ s.re) : (1 : ℝ) / 2 ≤ ‖riemannZeta s‖ := by
  have h := norm_riemannZeta_sub_one_le hs
  have h2 : ‖(1 : ℂ)‖ - ‖riemannZeta s - 1‖ ≤ ‖riemannZeta s‖ := by
    have := norm_sub_norm_le (1 : ℂ) (1 - riemannZeta s)
    simp only [sub_sub_cancel] at this
    calc
      ‖(1 : ℂ)‖ - ‖riemannZeta s - 1‖ = ‖(1 : ℂ)‖ - ‖1 - riemannZeta s‖ := by rw [norm_sub_rev]
      _ ≤ ‖riemannZeta s‖ := by
        have := norm_sub_norm_le (1 : ℂ) (1 - riemannZeta s)
        simpa only [norm_one, tsub_le_iff_right, ge_iff_le, sub_sub_cancel] using this
  rw [norm_one] at h2
  linarith only [h2, h]

/-! ### Geometric setup for a direct Jensen application at height `T` -/

/-- The Jensen disk is centered at `3 + iT`: comfortably inside `Re s > 1` (so `ζ` is nonzero and
bounded away from `0` there), while a disk of radius `39/10` around it still avoids the pole at
`1` and stays within `Re s > -1` (for `T ≥ 4`), and a disk of radius `37/10` already contains
every point with `0 ≤ Re ≤ 1` and `|Im - T| ≤ 2` — in particular every nontrivial zero of `ζ`
with ordinate within `2` of `T` (recall all such zeros already satisfy `0 ≤ Re ≤ 1`
unconditionally). -/
noncomputable def jensenCenter (T : ℝ) : ℂ :=
  (3 : ℂ) + (T : ℂ) * Complex.I

theorem jensenCenter_re (T : ℝ) :
    (jensenCenter T).re = 3 := by
  simp only [jensenCenter, Complex.add_re, Complex.re_ofNat, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]

theorem jensenCenter_im (T : ℝ) :
    (jensenCenter T).im = T := by
  simp only [jensenCenter, Complex.add_im, Complex.im_ofNat, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, zero_add]

theorem norm_jensenCenter_le (T : ℝ) :
    ‖jensenCenter T‖ ≤ 3 + |T| := by
  calc
    ‖jensenCenter T‖ ≤
        ‖(3 : ℂ)‖ + ‖(T : ℂ) * Complex.I‖ :=
      norm_add_le _ _
    _ = 3 + |T| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      norm_num only [Complex.norm_ofNat]

theorem norm_jensenCenter_sub_one_ge (T : ℝ) :
    |T| ≤ ‖jensenCenter T - 1‖ := by
  have him : (jensenCenter T - 1).im = T := by
    simp only [jensenCenter, Complex.sub_im, Complex.add_im, Complex.im_ofNat, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero,
      zero_add, Complex.one_im, sub_zero]
  calc
    |T| = |(jensenCenter T - 1).im| := by rw [him]
    _ ≤ ‖jensenCenter T - 1‖ :=
      Complex.abs_im_le_norm _

/-- The closed ball of radius `39/10` around
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensenCenter T` (for `T ≥ 4`) lies inside the
domain `{Re s > -1} \ {1}` where the polynomial growth bound applies. -/
theorem jensenBall_subset {T : ℝ} (hT : 4 ≤ T) :
    Metric.closedBall (jensenCenter T) (39 / 10) ⊆
      {s : ℂ | -1 < s.re} \ {(1 : ℂ)} := by
  intro w hw
  simp only [Metric.mem_closedBall, dist_eq_norm] at hw
  refine ⟨?_, ?_⟩
  · have h1 :
      |w.re - (jensenCenter T).re| ≤
        ‖w - jensenCenter T‖ := by
      have h :=
        Complex.abs_re_le_norm (w - jensenCenter T)
      simpa only [ge_iff_le, Complex.sub_re] using h
    rw [jensenCenter_re] at h1
    have h2 := (abs_le.mp h1).1
    change (-1 : ℝ) < w.re
    linarith only [hw, h2]
  · simp only [Set.mem_singleton_iff]
    intro hw1
    have hge : |T| ≤ ‖jensenCenter T - 1‖ :=
      norm_jensenCenter_sub_one_ge T
    have hle : ‖jensenCenter T - 1‖ ≤ 39 / 10 := by
      rw [show
          jensenCenter T - 1 =
            -(w - jensenCenter T)
          from by
          rw [hw1]; ring,
        norm_neg]
      exact hw
    have : T ≤ 39 / 10 := (le_abs_self T).trans (hge.trans hle)
    linarith only [this, hT]

theorem jensen_analyticOnNhd {T : ℝ} (hT : 4 ≤ T) :
    AnalyticOnNhd ℂ riemannZeta
      (Metric.closedBall (jensenCenter T) (39 / 10)) :=
  analyticOnNhd_riemannZeta_reGt_neg_one_diff_one.mono
    (jensenBall_subset hT)

theorem jensen_center_ne_zero (T : ℝ) :
    riemannZeta (jensenCenter T) ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re
    (by
      rw [jensenCenter_re]; norm_num only)

theorem jensen_center_norm_ge (T : ℝ) :
    (1 : ℝ) / 2 ≤ ‖riemannZeta (jensenCenter T)‖ :=
  norm_riemannZeta_ge
    (by rw [jensenCenter_re])

/-- The explicit `T`-dependent bound on `‖ζ‖` throughout the outer sphere, obtained from the
`Im s`-uniform polynomial growth bound by plugging in the worst-case (over the sphere) values:
largest possible `‖z‖`, smallest possible `‖z - 1‖`, and smallest possible `Re z` (using
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.sawtoothRemainderBound`'s antitonicity for
the last one). -/
noncomputable def jensenM (T : ℝ) : ℝ :=
  (T + 69 / 10) / (T - 39 / 10) + 1 / 2 +
    (T + 69 / 10) * (T + 69 / 10 + 1) *
      sawtoothRemainderBound (-9 / 10)

theorem jensen_f_bound {T : ℝ} (hT : 4 ≤ T) :
    ∀ z ∈ Metric.sphere (jensenCenter T) (39 / 10),
      ‖riemannZeta z‖ ≤ jensenM T := by
  intro z hz
  simp only [Metric.mem_sphere, dist_eq_norm] at hz
  have hzmem : z ∈ ({s : ℂ | -1 < s.re} \ {(1 : ℂ)}) :=
    jensenBall_subset hT
      (by
        simp only [Metric.mem_closedBall, dist_eq_norm]; rw [hz])
  have hb :=
    norm_riemannZeta_le_of_reGt_neg_one_diff_one hzmem
  have hTabs : |T| = T := abs_of_nonneg (by linarith only [hT])
  have hnz : ‖z‖ ≤ T + 69 / 10 := by
    have h1 :
      ‖z‖ ≤
        ‖jensenCenter T‖ +
          ‖z - jensenCenter T‖ := by
      have h :=
        norm_add_le (jensenCenter T)
          (z - jensenCenter T)
      simpa only [ge_iff_le, add_sub_cancel] using h
    have h2 := norm_jensenCenter_le T
    rw [hz] at h1
    rw [hTabs] at h2
    linarith only [h1, h2]
  have hnz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg _
  have hzre : (-9 : ℝ) / 10 ≤ z.re := by
    have h1 :
      |z.re - (jensenCenter T).re| ≤
        ‖z - jensenCenter T‖ := by
      have h :=
        Complex.abs_re_le_norm (z - jensenCenter T)
      simpa only [ge_iff_le, Complex.sub_re] using h
    rw [jensenCenter_re, hz] at h1
    have := (abs_le.mp h1).1
    linarith only [this]
  have hzsub1 : T - 39 / 10 ≤ ‖z - 1‖ := by
    have h1 :
      ‖jensenCenter T - 1‖ ≤
        ‖jensenCenter T - z‖ + ‖z - 1‖ := by
      have h :=
        norm_add_le (jensenCenter T - z) (z - 1)
      simpa only [ge_iff_le, sub_add_sub_cancel] using h
    have h2 : ‖jensenCenter T - z‖ = 39 / 10 := by
      rw [show
          jensenCenter T - z =
            -(z - jensenCenter T)
          from by ring,
        norm_neg, hz]
    have h3 := norm_jensenCenter_sub_one_ge T
    rw [hTabs] at h3
    linarith only [h1, h2, h3]
  have hzsub1_pos : (0 : ℝ) < T - 39 / 10 := by linarith only [hT]
  have hzsub1_pos' : (0 : ℝ) < ‖z - 1‖ := lt_of_lt_of_le hzsub1_pos hzsub1
  have hterm1 : ‖z‖ / ‖z - 1‖ ≤ (T + 69 / 10) / (T - 39 / 10) := by
    rw [div_le_div_iff₀ hzsub1_pos' hzsub1_pos]
    have h1 : ‖z‖ * (T - 39 / 10) ≤ (T + 69 / 10) * (T - 39 / 10) :=
      mul_le_mul_of_nonneg_right hnz hzsub1_pos.le
    have h2 : (T + 69 / 10) * (T - 39 / 10) ≤ (T + 69 / 10) * ‖z - 1‖ :=
      mul_le_mul_of_nonneg_left hzsub1 (by linarith only [hT])
    linarith only [h1, h2]
  have hterm3 :
    ‖z‖ * (‖z‖ + 1) * sawtoothRemainderBound z.re ≤
      (T + 69 / 10) * (T + 69 / 10 + 1) *
        sawtoothRemainderBound (-9 / 10) := by
    have hanti :
      sawtoothRemainderBound z.re ≤
        sawtoothRemainderBound (-9 / 10) :=
      sawtoothRemainderBound_antitone
        (by norm_num only) hzre
    have hbndnn0 :
      (0 : ℝ) ≤ sawtoothRemainderBound z.re :=
      sawtoothRemainderBound_nonneg z.re
    have h1 : ‖z‖ * (‖z‖ + 1) ≤ (T + 69 / 10) * (T + 69 / 10 + 1) :=
      mul_le_mul hnz (by linarith only [hnz]) (by linarith only [hnz0]) (by linarith only [hT])
    exact mul_le_mul h1 hanti hbndnn0 (by positivity)
  unfold jensenM
  linarith only [hb, hterm1, hterm3]

/-- The same bound as `PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensen_f_bound`,
but throughout the whole closed disk rather than just on
the sphere: every step of the proof only ever used
`‖z - PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensenCenter T‖ ≤ 39/10`, never the
sphere's exact equality, so it generalizes immediately. Needed for a Borel–Carathéodory argument
centered at `PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensenCenter T`,
which requires the growth bound throughout an open ball, not just
on its boundary. -/
theorem jensen_f_bound_ball {T : ℝ} (hT : 4 ≤ T) :
    ∀ z ∈ Metric.closedBall (jensenCenter T) (39 / 10),
      ‖riemannZeta z‖ ≤ jensenM T := by
  intro z hz
  simp only [Metric.mem_closedBall, dist_eq_norm] at hz
  have hzmem : z ∈ ({s : ℂ | -1 < s.re} \ {(1 : ℂ)}) :=
    jensenBall_subset hT
      (by
        simp only [Metric.mem_closedBall, dist_eq_norm]; exact hz)
  have hb :=
    norm_riemannZeta_le_of_reGt_neg_one_diff_one hzmem
  have hTabs : |T| = T := abs_of_nonneg (by linarith)
  have hnz : ‖z‖ ≤ T + 69 / 10 := by
    have h1 :
      ‖z‖ ≤
        ‖jensenCenter T‖ +
          ‖z - jensenCenter T‖ := by
      have h :=
        norm_add_le (jensenCenter T)
          (z - jensenCenter T)
      simpa only [ge_iff_le, add_sub_cancel] using h
    have h2 := norm_jensenCenter_le T
    rw [hTabs] at h2
    linarith [h1, h2, hz]
  have hnz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg _
  have hzre : (-9 : ℝ) / 10 ≤ z.re := by
    have h1 :
      |z.re - (jensenCenter T).re| ≤
        ‖z - jensenCenter T‖ := by
      have h :=
        Complex.abs_re_le_norm (z - jensenCenter T)
      simpa only [ge_iff_le, Complex.sub_re] using h
    rw [jensenCenter_re] at h1
    have h2 := (abs_le.mp h1).1
    linarith [h2, hz]
  have hzsub1 : T - 39 / 10 ≤ ‖z - 1‖ := by
    have h1 :
      ‖jensenCenter T - 1‖ ≤
        ‖jensenCenter T - z‖ + ‖z - 1‖ := by
      have h :=
        norm_add_le (jensenCenter T - z) (z - 1)
      simpa only [ge_iff_le, sub_add_sub_cancel] using h
    have h2 : ‖jensenCenter T - z‖ ≤ 39 / 10 := by
      rw [show
          jensenCenter T - z =
            -(z - jensenCenter T)
          from by ring,
        norm_neg]
      exact hz
    have h3 := norm_jensenCenter_sub_one_ge T
    rw [hTabs] at h3
    linarith
  have hzsub1_pos : (0 : ℝ) < T - 39 / 10 := by linarith
  have hzsub1_pos' : (0 : ℝ) < ‖z - 1‖ := lt_of_lt_of_le hzsub1_pos hzsub1
  have hterm1 : ‖z‖ / ‖z - 1‖ ≤ (T + 69 / 10) / (T - 39 / 10) := by
    rw [div_le_div_iff₀ hzsub1_pos' hzsub1_pos]
    have h1 : ‖z‖ * (T - 39 / 10) ≤ (T + 69 / 10) * (T - 39 / 10) :=
      mul_le_mul_of_nonneg_right hnz hzsub1_pos.le
    have h2 : (T + 69 / 10) * (T - 39 / 10) ≤ (T + 69 / 10) * ‖z - 1‖ :=
      mul_le_mul_of_nonneg_left hzsub1 (by linarith)
    linarith
  have hterm3 :
    ‖z‖ * (‖z‖ + 1) * sawtoothRemainderBound z.re ≤
      (T + 69 / 10) * (T + 69 / 10 + 1) *
        sawtoothRemainderBound (-9 / 10) := by
    have hanti :
      sawtoothRemainderBound z.re ≤
        sawtoothRemainderBound (-9 / 10) :=
      sawtoothRemainderBound_antitone
        (by norm_num only) hzre
    have hbndnn0 :
      (0 : ℝ) ≤ sawtoothRemainderBound z.re :=
      sawtoothRemainderBound_nonneg z.re
    have h1 : ‖z‖ * (‖z‖ + 1) ≤ (T + 69 / 10) * (T + 69 / 10 + 1) :=
      mul_le_mul hnz (by linarith) (by linarith) (by linarith)
    exact mul_le_mul h1 hanti hbndnn0 (by positivity)
  unfold jensenM
  linarith [hb, hterm1, hterm3]

/-- **the zeta-side estimate, closed via a direct Jensen application**: the number of zeros of
`ζ` inside the
disk of radius `37/10` around `3 + iT` — in particular, every nontrivial zero with ordinate
within `2` of `T` — is bounded via Jensen's inequality, with the outer bound coming directly
from the `Im s`-uniform polynomial growth estimate (no Phragmén-Lindelöf/`vertical_strip` and
no auxiliary normalizing function needed). -/
theorem finsum_divisor_riemannZeta_le {T : ℝ} (hT : 4 ≤ T) :
    ((∑ᶠ u,
            MeromorphicOn.divisor riemannZeta
              (Metric.closedBall (jensenCenter T)
                (37 / 10))
              u :
          ℤ) :
        ℝ) ≤
      Real.log
          (jensenM T /
            ‖riemannZeta (jensenCenter T)‖) /
        Real.log ((39 / 10) / (37 / 10)) := by
  have hrpos : (0 : ℝ) < |(37 / 10 : ℝ)| := by norm_num only
  have hrR : |(37 / 10 : ℝ)| < |(39 / 10 : ℝ)| := by norm_num only
  have hM : (1 : ℝ) ≤ jensenM T := by
    unfold jensenM
    have h1 : (1 : ℝ) < (T + 69 / 10) / (T - 39 / 10) := by
      rw [lt_div_iff₀ (by linarith)]
      linarith
    have h2 :
      (0 : ℝ) ≤
        (T + 69 / 10) * (T + 69 / 10 + 1) *
          sawtoothRemainderBound (-9 / 10) := by
      have := sawtoothRemainderBound_nonneg (-9 / 10)
      positivity
    linarith
  have h1f :
    AnalyticOnNhd ℂ riemannZeta
      (Metric.closedBall (jensenCenter T)
        |(39 / 10 : ℝ)|) := by
    rw [abs_of_pos (by norm_num only : (0 : ℝ) < 39 / 10)]
    exact jensen_analyticOnNhd hT
  have fbound :
    ∀
      z ∈
        Metric.sphere (jensenCenter T) |(39 / 10 : ℝ)|,
      ‖riemannZeta z‖ ≤ jensenM T := by
    rw [abs_of_pos (by norm_num only : (0 : ℝ) < 39 / 10)]
    exact jensen_f_bound hT
  have hres :=
    AnalyticOnNhd.sum_divisor_le hrpos hrR hM h1f
      (jensen_center_ne_zero T) fbound
  rwa [abs_of_pos (by norm_num only : (0 : ℝ) < 37 / 10)] at hres

/-!
### An explicit logarithmic zero-count bound

For `T ≥ 8`, package the Jensen estimate as a fixed constant times `log(T+2)`
for quantitative good-height selection.
-/

theorem jensenM_le {T : ℝ} (hT : 8 ≤ T) :
    jensenM T ≤
      (9 / 2 + 4 * sawtoothRemainderBound (-9 / 10)) *
        T ^ 2 := by
  unfold jensenM
  have hB0 :
    (0 : ℝ) ≤ sawtoothRemainderBound (-9 / 10) :=
    sawtoothRemainderBound_nonneg _
  have h1 : (T + 69 / 10) / (T - 39 / 10) ≤ 4 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have h2 : (T + 69 / 10) * (T + 69 / 10 + 1) ≤ 4 * T ^ 2 := by
    have ha : T + 69 / 10 ≤ 2 * T := by linarith
    have hb : T + 69 / 10 + 1 ≤ 2 * T := by linarith
    calc
      (T + 69 / 10) * (T + 69 / 10 + 1) ≤ (2 * T) * (2 * T) :=
        mul_le_mul ha hb (by linarith) (by linarith)
      _ = 4 * T ^ 2 := by ring
  have h3 :
    (T + 69 / 10) * (T + 69 / 10 + 1) *
        sawtoothRemainderBound (-9 / 10) ≤
      4 * T ^ 2 * sawtoothRemainderBound (-9 / 10) :=
    mul_le_mul_of_nonneg_right h2 hB0
  have h4 : (1 : ℝ) ≤ T ^ 2 := by nlinarith
  nlinarith [h1, h3, h4]

/-- The explicit constant for the `C·log(T+2)` zero-count bound. -/
noncomputable def jensenLogConst : ℝ :=
  (Real.log
          (9 + 8 * sawtoothRemainderBound (-9 / 10)) /
        Real.log 10 +
      2) /
    Real.log (39 / 37)

theorem jensenLogConst_pos : 0 < jensenLogConst := by
  unfold jensenLogConst
  have h1 :
    (0 : ℝ) ≤
      Real.log
        (9 + 8 * sawtoothRemainderBound (-9 / 10)) :=
    Real.log_nonneg
      (by
        linarith [sawtoothRemainderBound_nonneg
            (-9 / 10)])
  have h2 : (0 : ℝ) < Real.log 10 := Real.log_pos (by norm_num only)
  have h3 : (0 : ℝ) < Real.log (39 / 37) := Real.log_pos (by norm_num only)
  positivity

theorem finsum_divisor_riemannZeta_le_explicit {T : ℝ} (hT : 8 ≤ T) :
    ((∑ᶠ u,
            MeromorphicOn.divisor riemannZeta
              (Metric.closedBall (jensenCenter T)
                (37 / 10))
              u :
          ℤ) :
        ℝ) ≤
      jensenLogConst * Real.log (T + 2) := by
  have hT4 : (4 : ℝ) ≤ T := by linarith
  have hres := finsum_divisor_riemannZeta_le hT4
  rw [show (39 / 10 : ℝ) / (37 / 10) = 39 / 37 from by norm_num only] at hres
  have hzge :
    (1 : ℝ) / 2 ≤ ‖riemannZeta (jensenCenter T)‖ :=
    jensen_center_norm_ge T
  have hzpos :
    (0 : ℝ) < ‖riemannZeta (jensenCenter T)‖ := by
    linarith
  have hMpos : (0 : ℝ) < jensenM T := by
    have h1 : (1 : ℝ) < (T + 69 / 10) / (T - 39 / 10) := by
      rw [lt_div_iff₀ (by linarith)]
      linarith only []
    have h2 :
      (0 : ℝ) ≤
        (T + 69 / 10) * (T + 69 / 10 + 1) *
          sawtoothRemainderBound (-9 / 10) := by
      have := sawtoothRemainderBound_nonneg (-9 / 10)
      positivity
    unfold jensenM
    linarith only [h2, h1]
  have hratio :
    jensenM T / ‖riemannZeta (jensenCenter T)‖ ≤
      2 * jensenM T := by
    rw [div_le_iff₀ hzpos]
    nlinarith [hzge, hMpos]
  have hB0 :
    (0 : ℝ) ≤ sawtoothRemainderBound (-9 / 10) :=
    sawtoothRemainderBound_nonneg _
  have hDpos :
    (0 : ℝ) <
      9 / 2 +
        4 * sawtoothRemainderBound (-9 / 10) := by
    linarith
  have hbound2 :
    2 * jensenM T ≤
      (9 + 8 * sawtoothRemainderBound (-9 / 10)) *
        T ^ 2 := by
    have := jensenM_le hT
    nlinarith [this]
  have hpos1 :
    (0 : ℝ) <
      jensenM T / ‖riemannZeta (jensenCenter T)‖ :=
    div_pos hMpos hzpos
  have hpos2 :
    (0 : ℝ) <
      (9 + 8 * sawtoothRemainderBound (-9 / 10)) *
        T ^ 2 := by
    have hTpos : (0 : ℝ) < T := by linarith
    positivity
  have hlog1 :
    Real.log
        (jensenM T / ‖riemannZeta (jensenCenter T)‖) ≤
      Real.log
        ((9 + 8 * sawtoothRemainderBound (-9 / 10)) *
          T ^ 2) :=
    Real.log_le_log hpos1 (hratio.trans hbound2)
  have hTpos : (0 : ℝ) < T := by linarith
  have hlog2 :
    Real.log
        ((9 + 8 * sawtoothRemainderBound (-9 / 10)) *
          T ^ 2) =
      Real.log
          (9 + 8 * sawtoothRemainderBound (-9 / 10)) +
        2 * Real.log T := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  have hlogT : Real.log T ≤ Real.log (T + 2) := Real.log_le_log hTpos (by linarith)
  have hlogT10 : Real.log 10 ≤ Real.log (T + 2) := Real.log_le_log (by norm_num only) (by linarith)
  have hlog10pos : (0 : ℝ) < Real.log 10 := Real.log_pos (by norm_num only)
  have hlogDnn :
    (0 : ℝ) ≤
      Real.log
        (9 + 8 * sawtoothRemainderBound (-9 / 10)) :=
    Real.log_nonneg (by linarith)
  have hlog3 :
    Real.log
        (9 + 8 * sawtoothRemainderBound (-9 / 10)) ≤
      (Real.log
            (9 +
              8 * sawtoothRemainderBound (-9 / 10)) /
          Real.log 10) *
        Real.log (T + 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog10pos]
    exact mul_le_mul_of_nonneg_left hlogT10 hlogDnn
  have hlog39_37 : (0 : ℝ) < Real.log (39 / 37) := Real.log_pos (by norm_num only)
  have hchain :
    Real.log
        (jensenM T / ‖riemannZeta (jensenCenter T)‖) ≤
      ((Real.log
              (9 +
                8 * sawtoothRemainderBound (-9 / 10)) /
            Real.log 10) +
          2) *
        Real.log (T + 2) := by
    calc
      Real.log
            (jensenM T /
              ‖riemannZeta (jensenCenter T)‖) ≤
          Real.log
              (9 +
                8 * sawtoothRemainderBound (-9 / 10)) +
            2 * Real.log T :=
        hlog1.trans (le_of_eq hlog2)
      _ ≤
          ((Real.log
                  (9 +
                    8 *
                      sawtoothRemainderBound
                        (-9 / 10)) /
                Real.log 10) *
              Real.log (T + 2)) +
            2 * Real.log (T + 2) :=
        add_le_add hlog3 (by linarith [hlogT])
      _ =
          ((Real.log
                  (9 +
                    8 *
                      sawtoothRemainderBound
                        (-9 / 10)) /
                Real.log 10) +
              2) *
            Real.log (T + 2) :=
        by ring
  have hfinal :
    Real.log
          (jensenM T /
            ‖riemannZeta (jensenCenter T)‖) /
        Real.log (39 / 37) ≤
      jensenLogConst * Real.log (T + 2) := by
    rw [div_le_iff₀ hlog39_37]
    have heq :
      jensenLogConst * Real.log (T + 2) *
          Real.log (39 / 37) =
        ((Real.log
                (9 +
                  8 *
                    sawtoothRemainderBound (-9 / 10)) /
              Real.log 10) +
            2) *
          Real.log (T + 2) := by
      unfold jensenLogConst
      field_simp
    rw [heq]
    exact hchain
  exact hres.trans hfinal

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
