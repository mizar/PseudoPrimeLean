/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.GoodHeight
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Jensen bounds at negative heights

Complex conjugation preserves zeta norms and sends `3+iT` to `3-iT`.
Transport the growth estimate to negative-height disks to obtain the
multiplicity bound and inclusion of nearby zeros. Disk analyticity uses
`|T| ≥ 4` to avoid the pole at one; the center is nonzero for every real `T`.
-/

noncomputable section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

theorem jensenCenter_conj (T : ℝ) :
    (starRingEnd ℂ) (jensenCenter T) = jensenCenter (-T) := by
  simp only [jensenCenter, map_add, map_mul, map_ofNat,
    Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem norm_riemannZeta_conj (z : ℂ) : ‖riemannZeta ((starRingEnd ℂ) z)‖ = ‖riemannZeta z‖ := by
  rw [riemannZeta_conj, Complex.norm_conj]

/-- The derivative of the Riemann zeta function commutes with complex conjugation. -/
theorem deriv_riemannZeta_conj (s : ℂ) :
    deriv riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (deriv riemannZeta s) := by
  have hzeta : (starRingEnd ℂ ∘ riemannZeta ∘ starRingEnd ℂ) = riemannZeta := by
    funext z
    simp only [Function.comp_apply]
    rw [riemannZeta_conj]
    simp only [RingHomCompTriple.comp_apply, RingHom.id_apply]
  have hderiv := congrFun (deriv_conj_conj (f := riemannZeta)) (starRingEnd ℂ s)
  rw [hzeta] at hderiv
  have hss : starRingEnd ℂ (starRingEnd ℂ s) = s := star_star s
  simpa only [Function.comp_apply, hss] using hderiv

/-- `ζ` is analytic on the disk of radius `39/10` around
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensenCenter T`, for any `T` with
`4 ≤ |T|` (both signs at once): the disk avoids the pole `s = 1` since
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.norm_jensenCenter_sub_one_ge` already bounds
`‖PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensenCenter T - 1‖` below by `|T|`. -/
theorem jensen_analyticOnNhd_of_abs {T : ℝ} (hT : 4 ≤ |T|) :
    AnalyticOnNhd ℂ riemannZeta
      (Metric.closedBall (RiemannZeta.jensenCenter T)
        (39 / 10)) := by
  apply analyticOn_riemannZeta.mono
  intro w hw
  simp only [Metric.mem_closedBall, dist_eq_norm] at hw
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
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
  linarith

/-- The mirror of `PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensen_f_bound` for `T ≤ -4`:
the outer-sphere bound transports across
conjugation, reusing `jensenM (-T)` (the *same* function `jensenM`, evaluated at `-T ≥ 4`) rather
than needing a new mirrored bound function. -/
theorem jensen_f_bound_neg {T : ℝ} (hT : T ≤ -4) :
    ∀ z ∈ Metric.sphere (jensenCenter T) (39 / 10),
      ‖riemannZeta z‖ ≤ jensenM (-T) := by
  intro z hz
  have hz' :
    (starRingEnd ℂ) z ∈
      Metric.sphere (jensenCenter (-T)) (39 / 10) := by
    rw [Metric.mem_sphere] at hz ⊢
    rw [← jensenCenter_conj T, Complex.dist_conj_conj]
    exact hz
  have hb :=
    jensen_f_bound (T := -T) (by linarith) _ hz'
  rwa [norm_riemannZeta_conj] at hb

/-- The mirror of `PseudoPrime.AnalyticNumberTheory.RiemannZeta.finsum_divisor_riemannZeta_le` for
`T ≤ -4`. -/
theorem finsum_divisor_riemannZeta_le_neg {T : ℝ} (hT : T ≤ -4) :
    ((∑ᶠ u,
            MeromorphicOn.divisor riemannZeta
              (Metric.closedBall (jensenCenter T)
                (37 / 10))
              u :
          ℤ) :
        ℝ) ≤
      Real.log
          (jensenM (-T) /
            ‖riemannZeta (jensenCenter T)‖) /
        Real.log ((39 / 10) / (37 / 10)) := by
  have hrpos : (0 : ℝ) < |(37 / 10 : ℝ)| := by norm_num only
  have hrR : |(37 / 10 : ℝ)| < |(39 / 10 : ℝ)| := by norm_num only
  have hT4 : (4 : ℝ) ≤ -T := by linarith
  have hM : (1 : ℝ) ≤ jensenM (-T) := by
    unfold jensenM
    have h1 : (1 : ℝ) < (-T + 69 / 10) / (-T - 39 / 10) := by
      rw [lt_div_iff₀ (by linarith)]
      linarith
    have h2 :
      (0 : ℝ) ≤
        (-T + 69 / 10) * (-T + 69 / 10 + 1) *
          sawtoothRemainderBound (-9 / 10) := by
      have := sawtoothRemainderBound_nonneg (-9 / 10)
      positivity
    linarith
  have h1f :
    AnalyticOnNhd ℂ riemannZeta
      (Metric.closedBall (jensenCenter T)
        |(39 / 10 : ℝ)|) := by
    rw [abs_of_pos (by norm_num only : (0 : ℝ) < 39 / 10)]
    exact
      jensen_analyticOnNhd_of_abs
        (by
          rw [abs_of_neg (by linarith : T < 0)]; linarith)
  have fbound :
    ∀
      z ∈
        Metric.sphere (jensenCenter T) |(39 / 10 : ℝ)|,
      ‖riemannZeta z‖ ≤ jensenM (-T) := by
    rw [abs_of_pos (by norm_num only : (0 : ℝ) < 39 / 10)]
    exact jensen_f_bound_neg hT
  have hres :=
    AnalyticOnNhd.sum_divisor_le hrpos hrR hM h1f
      (jensen_center_ne_zero T) fbound
  rwa [abs_of_pos (by norm_num only : (0 : ℝ) < 37 / 10)] at hres

/-- The mirror of
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.finsum_divisor_riemannZeta_le_explicit` for `T ≤ -8`:
a line-by-line copy of
the original proof with `T` replaced by `-T` throughout,
reusing `PseudoPrime.AnalyticNumberTheory.RiemannZeta.finsum_divisor_riemannZeta_le_neg`
as the starting point. -/
theorem finsum_divisor_riemannZeta_le_explicit_neg {T : ℝ} (hT : T ≤ -8) :
    ((∑ᶠ u,
            MeromorphicOn.divisor riemannZeta
              (Metric.closedBall (jensenCenter T)
                (37 / 10))
              u :
          ℤ) :
        ℝ) ≤
      jensenLogConst * Real.log (-T + 2) := by
  have hT4 : T ≤ (-4 : ℝ) := by linarith
  have hres := finsum_divisor_riemannZeta_le_neg hT4
  rw [show (39 / 10 : ℝ) / (37 / 10) = 39 / 37 from by norm_num only] at hres
  have hzge :
    (1 : ℝ) / 2 ≤ ‖riemannZeta (jensenCenter T)‖ :=
    jensen_center_norm_ge T
  have hzpos :
    (0 : ℝ) < ‖riemannZeta (jensenCenter T)‖ := by
    linarith
  have h8 : (8 : ℝ) ≤ -T := by linarith
  have hMpos : (0 : ℝ) < jensenM (-T) := by
    have h1 : (1 : ℝ) < (-T + 69 / 10) / (-T - 39 / 10) := by
      rw [lt_div_iff₀ (by linarith)]
      linarith
    have h2 :
      (0 : ℝ) ≤
        (-T + 69 / 10) * (-T + 69 / 10 + 1) *
          sawtoothRemainderBound (-9 / 10) := by
      have := sawtoothRemainderBound_nonneg (-9 / 10)
      positivity
    unfold jensenM
    linarith
  have hratio :
    jensenM (-T) / ‖riemannZeta (jensenCenter T)‖ ≤
      2 * jensenM (-T) := by
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
    2 * jensenM (-T) ≤
      (9 + 8 * sawtoothRemainderBound (-9 / 10)) *
        (-T) ^ 2 := by
    have := jensenM_le h8
    nlinarith [this]
  have hpos1 :
    (0 : ℝ) <
      jensenM (-T) / ‖riemannZeta (jensenCenter T)‖ :=
    div_pos hMpos hzpos
  have hpos2 :
    (0 : ℝ) <
      (9 + 8 * sawtoothRemainderBound (-9 / 10)) *
        (-T) ^ 2 := by
    have hTpos : (0 : ℝ) < -T := by linarith
    positivity
  have hlog1 :
    Real.log
        (jensenM (-T) /
          ‖riemannZeta (jensenCenter T)‖) ≤
      Real.log
        ((9 + 8 * sawtoothRemainderBound (-9 / 10)) *
          (-T) ^ 2) :=
    Real.log_le_log hpos1 (hratio.trans hbound2)
  have hTpos : (0 : ℝ) < -T := by linarith
  have hlog2 :
    Real.log
        ((9 + 8 * sawtoothRemainderBound (-9 / 10)) *
          (-T) ^ 2) =
      Real.log
          (9 + 8 * sawtoothRemainderBound (-9 / 10)) +
        2 * Real.log (-T) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  have hlogT : Real.log (-T) ≤ Real.log (-T + 2) := Real.log_le_log hTpos (by linarith)
  have hlogT10 : Real.log 10 ≤ Real.log (-T + 2) := Real.log_le_log (by norm_num only) (by linarith)
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
        Real.log (-T + 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog10pos]
    exact mul_le_mul_of_nonneg_left hlogT10 hlogDnn
  have hlog39_37 : (0 : ℝ) < Real.log (39 / 37) := Real.log_pos (by norm_num only)
  have hchain :
    Real.log
        (jensenM (-T) /
          ‖riemannZeta (jensenCenter T)‖) ≤
      ((Real.log
              (9 +
                8 * sawtoothRemainderBound (-9 / 10)) /
            Real.log 10) +
          2) *
        Real.log (-T + 2) := by
    calc
      Real.log
            (jensenM (-T) /
              ‖riemannZeta (jensenCenter T)‖) ≤
          Real.log
              (9 +
                8 * sawtoothRemainderBound (-9 / 10)) +
            2 * Real.log (-T) :=
        hlog1.trans (le_of_eq hlog2)
      _ ≤
          ((Real.log
                  (9 +
                    8 *
                      sawtoothRemainderBound
                        (-9 / 10)) /
                Real.log 10) *
              Real.log (-T + 2)) +
            2 * Real.log (-T + 2) :=
        add_le_add hlog3 (by linarith [hlogT])
      _ =
          ((Real.log
                  (9 +
                    8 *
                      sawtoothRemainderBound
                        (-9 / 10)) /
                Real.log 10) +
              2) *
            Real.log (-T + 2) :=
        by ring
  have hfinal :
    Real.log
          (jensenM (-T) /
            ‖riemannZeta (jensenCenter T)‖) /
        Real.log (39 / 37) ≤
      jensenLogConst * Real.log (-T + 2) := by
    rw [div_le_iff₀ hlog39_37]
    have heq :
      jensenLogConst * Real.log (-T + 2) *
          Real.log (39 / 37) =
        ((Real.log
                (9 +
                  8 *
                    sawtoothRemainderBound (-9 / 10)) /
              Real.log 10) +
            2) *
          Real.log (-T + 2) := by
      unfold jensenLogConst
      field_simp
    rw [heq]
    exact hchain
  exact hres.trans hfinal

/-- The mirror of `PseudoPrime.AnalyticNumberTheory.RiemannZeta.riemannZeta_zero_mem_jensenBall`
for `H ≤ -8`. -/
theorem riemannZeta_zero_mem_jensenBall_neg {H : ℝ} (hH : H ≤ -8) {ρ : ℂ} (hζ : riemannZeta ρ = 0)
    (him : |ρ.im - H| ≤ 2) :
    ρ ∈
      Metric.closedBall (jensenCenter H)
        (37 / 10) := by
  have himneg : ρ.im < 0 := by
    have h1 := (abs_le.mp him).2
    linarith
  have hre0 : 0 ≤ ρ.re :=
    riemannZeta_zero_re_nonneg_of_im_ne_zero hζ
      himneg.ne
  have hre1 : ρ.re ≤ 1 := riemannZeta_zero_re_le_one hζ
  simp only [Metric.mem_closedBall, dist_eq_norm]
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  have hre_eq :
    (ρ - jensenCenter H).re = ρ.re - 3 := by
    simp only [Complex.sub_re, jensenCenter_re]
  have him_eq :
    (ρ - jensenCenter H).im = ρ.im - H := by
    simp only [Complex.sub_im, jensenCenter_im]
  rw [hre_eq, him_eq]
  rw [show (37 / 10 : ℝ) = Real.sqrt ((37 / 10) ^ 2) from (Real.sqrt_sq (by norm_num only)).symm]
  apply Real.sqrt_le_sqrt
  have h1 : (ρ.re - 3) ^ 2 ≤ 9 := by nlinarith [hre0, hre1]
  have h2 : (ρ.im - H) ^ 2 ≤ 4 := by nlinarith [abs_le.mp him]
  nlinarith [h1, h2]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
