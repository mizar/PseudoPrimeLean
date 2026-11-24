/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaCellSound
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPhaseCellSlacks
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPhaseGrid
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPhaseNodes
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SincPhaseInterpolation
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SincSmoothingWidth
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiSign100RH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaFiniteGridApprox
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadPhase
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLowerMidpoint
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPhaseCoverage

/-! # Real scalar inequalities for every generated middle-band cell -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem tick_ranges :
    ∀ i : Fin 320,
      (35 / 2 : ℚ) ≤ phaseTick i.castSucc / 512 ∧
        (phaseTick i.castSucc / 512 : ℚ) ≤ phaseTick i.succ / 512 ∧
        (phaseTick i.succ / 512 : ℚ) ≤ 53 / 2 := by
  decide +kernel

/-- Each of the 320 cells satisfies the real scalar inequality at its two outer
endpoints with the generated signed phase caps. -/
theorem phaseCells_real_bound (i : Fin 320) :
    let a : ℚ := phaseTick i.castSucc / 512
    let b : ℚ := phaseTick i.succ / 512
    let q := 2 * (b : ℝ) / 7 - 2 / 3
    let A := (b : ℝ) / 2 - Real.log (Real.pi * q)
    q / 2 +
          (max 0 (max ((phaseCaps i).1 : ℝ) ((phaseCaps i).2 : ℝ)) +
            3611 * ((b : ℝ) - a + 1 / 2800) ^ 2 / 8) +
          (A ^ 2 + 3 / 2 * A + 3 / 2) / (2 * Real.pi) -
        579 / 5000 ≤
      (a : ℝ) * (a - Real.log a) / (8 * Real.pi) := by
  have h := tick_ranges i
  exact
    phaseCellSlack_sound h.1 h.2.1 h.2.2
      ((by norm_num only : (0 : ℚ) ≤ 9 / 1000).trans (phaseCells_slack i))

/-- On each shifted cell, the actual phase of any bracketed nonnegative ordinate tuple
satisfies the scalar certificate throughout the cell. -/
theorem phaseCell_signed_bound (i : Fin 320) (g : Fin 29 → ℝ) (hp : ∀ j, 0 ≤ g j)
    (hl : RiemannZeta.LowZero100LowerBounds g) (hu : RiemannZeta.LowZero100UpperBounds g) :
    let a : ℚ := phaseTick i.castSucc / 512
    let b : ℚ := phaseTick i.succ / 512
    let q := 2 * (b : ℝ) / 7 - 2 / 3
    let A := (b : ℝ) / 2 - Real.log (Real.pi * q)
    ∀ v ∈ Set.Icc ((a : ℝ) - 1 / 2800) (b : ℝ),
      q / 2 + max 0 (RiemannZeta.zeroHeadPhase g v) + (A ^ 2 + 3 / 2 * A + 3 / 2) / (2 * Real.pi) -
          579 / 5000 ≤
        (a : ℝ) * (a - Real.log a) / (8 * Real.pi) := by
  intro a b q A v hv
  obtain ⟨ha, hab, hb⟩ := tick_ranges i
  change (35 / 2 : ℚ) ≤ a at ha
  change a ≤ b at hab
  change b ≤ 53 / 2 at hb
  have node (x c : ℚ) (hx : 0 ≤ x) (hx' : x ≤ 27) (hc : RiemannZeta.sincPhaseUpper x ≤ c) :=
    (RiemannZeta.sincPhaseUpper_sound x hx hx' g hl hu).trans (Rat.cast_le.mpr hc)
  have left :=
    node (a - 1 / 2800) _ (by linarith only [ha]) (by linarith only [hab, hb])
      (phaseNodes_bounds i).1
  have right :=
    node b _ (by linarith only [ha, hab]) (by linarith only [hb]) (phaseNodes_bounds i).2
  simp only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at left
  have hs := RiemannZeta.signed_phase_shifted_cell g hp hu (Rat.cast_le.mpr hab) left right hv
  have hm := max_le (add_nonneg (le_max_left 0 _) (by positivity)) hs
  exact
    (sub_le_sub_right (add_le_add_left (add_le_add_right hm _) _) _).trans (phaseCells_real_bound i)

private theorem log_step {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (Real.log y - Real.log x) * x ≤ y - x := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at h
  have ht := mul_le_mul_of_nonneg_right h hx.le
  rwa [sub_mul (y / x) 1, div_mul_cancel₀ _ hx.ne', one_mul] at ht

private theorem phaseA_mono {x y : ℝ} (hx : 35 / 2 ≤ x) (hxy : x ≤ y) :
    x / 2 - Real.log (Real.pi * (2 * x / 7 - 2 / 3)) ≤
      y / 2 - Real.log (Real.pi * (2 * y / 7 - 2 / 3)) := by
  let q (u : ℝ) := 2 * u / 7 - 2 / 3
  have hp : 1 ≤ q x := by
    dsimp only [q]; linarith only [hx]
  have hq : q x ≤ q y := by
    dsimp only [q]; linarith only [hxy]
  have hpx : 0 < q x := zero_lt_one.trans_le hp
  have hpy := hpx.trans_le hq
  have hs := log_step hpx hpy
  have hd := sub_nonneg.mpr (Real.log_le_log hpx hq)
  have ht := mul_le_mul_of_nonneg_left hp hd
  change x / 2 - Real.log (Real.pi * q x) ≤ y / 2 - Real.log (Real.pi * q y)
  rw [Real.log_mul Real.pi_ne_zero hpx.ne', Real.log_mul Real.pi_ne_zero hpy.ne']
  dsimp only [q] at hs ht ⊢
  linarith only [hs, ht, hxy]

private theorem phaseTarget_mono {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    x * (x - Real.log x) ≤ y * (y - Real.log y) := by
  have hp := zero_lt_one.trans_le hx
  have hs := log_step hp (hp.trans_le hxy)
  have hd := sub_nonneg.mpr (Real.log_le_log hp hxy)
  have ht := mul_le_mul_of_nonneg_left hx hd
  exact
    mul_le_mul hxy (by linarith only [hs, ht]) (by linarith only [Real.log_le_sub_one_of_pos hp])
      (hp.le.trans hxy)

/-- Uniform signed phase inequality on the entire middle band, including the
backward shift of at most 1/2800 in the phase argument. -/
theorem phaseBand_signed_bound (g : Fin 29 → ℝ) (hp : ∀ j, 0 ≤ g j)
    (hl : RiemannZeta.LowZero100LowerBounds g) (hu : RiemannZeta.LowZero100UpperBounds g) {L : ℝ}
    (hL : 35 / 2 ≤ L) (hR : L ≤ 53 / 2) :
    ∀ v ∈ Set.Icc (L - 1 / 2800) L,
      let q := 2 * L / 7 - 2 / 3
      let A := L / 2 - Real.log (Real.pi * q)
      q / 2 + max 0 (RiemannZeta.zeroHeadPhase g v) + (A ^ 2 + 3 / 2 * A + 3 / 2) / (2 * Real.pi) -
          579 / 5000 ≤
        L * (L - Real.log L) / (8 * Real.pi) := by
  apply phaseGrid_cover _ hL hR
  intro i x hax hxb v hv
  let a : ℚ := phaseTick i.castSucc / 512
  let b : ℚ := phaseTick i.succ / 512
  have ha : (a : ℝ) ≤ x := by simpa only [a, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
  have hb : x ≤ (b : ℝ) := by simpa only [b, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
  have hlo : 35 / 2 ≤ (a : ℝ) := by
    simpa only [a, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (tick_ranges i).1
  have hhi : (b : ℝ) ≤ 53 / 2 := by
    simpa only [b, Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr (tick_ranges i).2.2
  have hs :=
    phaseCell_signed_bound i g hp hl hu v ⟨(sub_le_sub_right ha _).trans hv.1, hv.2.trans hb⟩
  have hm := phaseA_mono (hlo.trans ha) hb
  have hq : 0 < 2 * x / 7 - 2 / 3 := by linarith only [hlo, ha]
  have hlog :=
    Real.log_le_log (mul_pos Real.pi_pos hq)
      (show Real.pi * (2 * x / 7 - 2 / 3) ≤ 32 by
        nlinarith only [mul_le_mul_of_nonneg_right Real.pi_lt_four.le hq.le, hb, hhi])
  have h32 : Real.log 32 ≤ 5 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 2)]
  have hpos : 0 ≤ x / 2 - Real.log (Real.pi * (2 * x / 7 - 2 / 3)) := by
    linarith only [hlo, ha, hlog, h32]
  have hsquare := pow_le_pow_left₀ hpos hm 2
  have hpoly :=
    div_le_div_of_nonneg_right
      (add_le_add_left
        (add_le_add hsquare (mul_le_mul_of_nonneg_left hm (by norm_num only : (0 : ℝ) ≤ 3 / 2)))
        (3 / 2))
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) Real.pi_pos.le)
  have ht :=
    div_le_div_of_nonneg_right (phaseTarget_mono (by linarith only [hlo]) ha)
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 8) Real.pi_pos.le)
  dsimp only at *
  apply le_trans _ (hs.trans ht)
  apply sub_le_sub_right
  apply add_le_add _ hpoly
  apply add_le_add_left
  linarith only [hb]

/-- The actual signed height-100 midpoint sum, normalized by the square root
of the right endpoint, satisfies the generated phase inequality throughout the band. -/
theorem phaseBand_midpoint (hRH : RiemannHypothesis) {L : ℝ} (hl : 35 / 2 ≤ L) (hu : L ≤ 53 / 2) :
    let x := Real.exp L
    let q := 2 * L / 7 - 2 / 3
    let d := q / Real.exp (L / 2)
    let m := (x * (1 - d) + x) / 2
    let A := L / 2 - Real.log (Real.pi * q)
    q / 2 + RiemannZeta.lowerMidpointSum m / Real.sqrt x +
          (A ^ 2 + 3 / 2 * A + 3 / 2) / (2 * Real.pi) -
        579 / 5000 ≤
      L * (L - Real.log L) / (8 * Real.pi) := by
  intro x q d m A
  obtain ⟨g, hg, hp, hh, hz, hlo, hhi⟩ :=
    RiemannZeta.low_zero_100_of_signs RiemannZeta.low_zero_100_sign_changes
  have hd : 0 < d ∧ d ≤ 13 / 18300 := RiemannZeta.sinc_relative_width hl
  have hx : 0 < x := Real.exp_pos L
  have ha : 0 < 1 - d := by linarith only [hd.2]
  have hm : 0 < m := half_pos (add_pos (mul_pos hx ha) hx)
  have hmx : m ≤ x := by
    dsimp only [m]; nlinarith only [mul_nonneg hx.le hd.1.le]
  have hphase :=
    RiemannZeta.zero_head_phase_of_count hRH (by norm_num only : (0 : ℝ) ≤ 100) hm g hg.injective hp
      hh hz ((RiemannZeta.zero_count_100_le_58_of_RH hRH).trans (by norm_num only [Nat.cast_ofNat]))
  have hv := RiemannZeta.sinc_midpoint_mem_cell hl (Set.mem_Icc.mpr ⟨le_rfl, le_rfl⟩)
  have hc := phaseBand_signed_bound g (fun j ↦ (hp j).le) hlo hhi hl hu (Real.log m) hv
  let k := RiemannZeta.zeroHeadPhase g (Real.log m)
  have hk : RiemannZeta.lowerMidpointSum m / Real.sqrt x ≤ max 0 k := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hx)).mpr
    rw [RiemannZeta.lowerMidpointSum, hphase, mul_comm (max 0 k)]
    exact
      (mul_le_mul_of_nonneg_left (le_max_right 0 k) (Real.sqrt_nonneg m)).trans
        (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hmx) (le_max_left 0 k))
  exact (sub_le_sub_right (add_le_add_left (add_le_add_right hk _) _) _).trans hc

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
