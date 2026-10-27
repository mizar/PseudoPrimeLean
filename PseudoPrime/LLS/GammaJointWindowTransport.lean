/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaJointCommonComparison
public import PseudoPrime.LLS.GammaQuadraticPolynomialSeparation
public import PseudoPrime.LLS.GammaLowerWindowBounds
public import PseudoPrime.Analysis.GammaWindowRationalCaps

/-! # Reusable window transport retaining the joint arithmetic saving -/

@[expose] public section

namespace PseudoPrime.LLS

/-- On the scale interval [16384,27556], the joint principal saving is at least
1/3. Bound log x below using log 2 and sqrt x above by 166. This gives a
whole-interval credit that can be spent in the paired polynomial comparison. -/
theorem gamma_joint_gain_ge_one_third (L b : ℝ) {x : ℝ} (hlo : 16384 ≤ x) (hhi : x ≤ 27556) :
    gammaSignedPrincipalFactorFreeSeparation L b x + 9 / 50 + 1 / 3 ≤
      gammaJointFactorFreeSeparation L b x := by
  have hx : 0 < x := by linarith only [hlo]
  rw [gammaJointFactorFreeSeparation_eq_signed L b hx]
  have hl : (19 / 2 : ℝ) ≤ Real.log x := by
    have hm :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 2 ^ 14)
        (show (2 : ℝ) ^ 14 ≤ x by
          norm_num only at hlo ⊢; exact hlo)
    rw [Real.log_pow] at hm
    norm_num only [Nat.cast_ofNat] at hm
    linarith only [hm, Real.log_two_gt_d9]
  have hr : Real.sqrt x ≤ 166 :=
    (Real.sqrt_le_iff).mpr
      ⟨by norm_num only, by
        norm_num only at hhi ⊢; exact hhi⟩
  have hs := Real.sqrt_pos.mpr hx
  have hn := Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 99 / 40)
  have hd :
    (1 / 3 - 2029 / 16000 : ℝ) ≤
      ((42297 / 12500 : ℝ) * Real.log x + (23907 / 10000 : ℝ) * Real.log (99 / 40 : ℝ) +
          8757 / 3200) /
        Real.sqrt x := by
    apply (le_div_iff₀ hs).mpr
    linarith only [hr, hl, hn]
  linarith only [hd]

/-- For an admissible scale, a dual cap, a polynomial separation and a certified
joint gain g, the adjusted prefix credit gives scalar joint margin above 7/60.
Retain g before comparing caps; this transfers window gains without new local data. -/
theorem gamma_joint_margin_gt_of_credited_polynomial {L x b C D g : ℝ} (hx : 1 ≤ x)
    (hcredit :
      C + (3 / 4 + D + 7 / 60 - g) / 2 ≤
        ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)
    (hdual : gammaScaleSignedDualBudget L x ≤ D)
    (hpoly : GammaPairedPolynomialCondition (L + 7 / 5) x C)
    (hgain :
      gammaSignedPrincipalFactorFreeSeparation L b x + 9 / 50 + g ≤
        gammaJointFactorFreeSeparation L b x) :
    7 / 60 < gammaJointFactorFreeSeparation L b x := by
  obtain ⟨R, u, hr, hl, hc, hp⟩ := hpoly
  have hs := gamma_paired_scalar_lt_gap hx hr hl hc hp
  dsimp only [gammaSignedPrincipalFactorFreeSeparation, gammaFactorFreeJointBudget] at hgain
  linarith only [hs, hcredit, hdual, hgain]

/-- Rational allowance for one old prime row on a lowered window. Inputs are the
old cell, row factory, new left endpoint and its positive rational root bound.
Keep the base-sensitive scale correction and signed endpoint quotients. -/
def loweredPrimeAllowance (c : Analysis.GammaLocalCellData) (rows : ℕ → Analysis.GammaLocalPrimeRow)
    (lo root : ℚ) (p : ℕ) : ℚ :=
  let r := rows p
  let N := r.rampUpper - 5 / 4 + (((p : ℚ) + 1) / (p - 1)) * (c.lo - lo) / lo
  r.logUpper * max (r.eulerUpper + max (N / root) (N / c.rootHi)) 0

/-- For a checked cell and prime row with matching base, ordered rational window
and valid lower root, the real local excess is at most its rational allowance.
Use signed quotient bounds and the row logarithm interval; no new row is checked. -/
theorem loweredPrimeAllowance_cap (c : Analysis.GammaLocalCellData)
    (rows : ℕ → Analysis.GammaLocalPrimeRow) (hc : c.check = true) {lo root : ℚ} (hr : 0 < root)
    (hrlo : root ^ 2 ≤ lo) (hlhi : lo ≤ c.hi) {p : ℕ} (hp : p.Prime) (hprime : (rows p).prime = p)
    (hcheck : (rows p).envelopeCheck c = true) :
    Real.log p *
        Analysis.gammaRamifiedWindowExcessBound lo c.hi (rows p).eulerUpper
          (((rows p).rampUpper : ℝ) - 5 / 4 + (((p : ℝ) + 1) / (p - 1)) * ((c.lo : ℝ) - lo) / lo) ≤
      (loweredPrimeAllowance c rows lo root p : ℝ) := by
  have hroot : (0 : ℝ) < root := Rat.cast_pos.mpr hr
  have hsq : (root : ℝ) ^ 2 ≤ lo := by exact_mod_cast hrlo
  have hlo0 : (0 : ℝ) ≤ lo := (sq_nonneg (root : ℝ)).trans hsq
  have hrloR := (Real.le_sqrt hroot.le hlo0).mpr hsq
  have hw :=
    Analysis.gamma_window_excess_le_root_bounds (e := ((rows p).eulerUpper : ℝ)) (N :=
      (((rows p).rampUpper - 5 / 4 + (((p : ℚ) + 1) / (p - 1)) * (c.lo - lo) / lo : ℚ) : ℝ)) hroot
      (Rat.cast_le.mpr hlhi) hrloR (c.check_sound hc).2.2.2.2.2.1
  have hl := (Analysis.rationalLogIntervalCheck_sound (Bool.and_eq_true_iff.mp hcheck).1).2
  change Real.log (rows p).prime ≤ ((rows p).logUpper : ℝ) at hl
  rw [hprime] at hl
  have hn := Real.log_nonneg (Nat.one_le_cast.mpr hp.one_le)
  have hmul := mul_le_mul hl hw (le_max_right _ _) (hn.trans hl)
  norm_num only [loweredPrimeAllowance, Rat.cast_mul, Rat.cast_max, Rat.cast_add, Rat.cast_sub,
    Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_zero] at hmul ⊢
  exact hmul

/-- If a prime set covers the old anchored support and its rational allowance sum
is capped by E, the real window excess sum is at most E. Apply row caps and
extend over nonnegative allowances. This keeps certificates compact and reusable. -/
theorem loweredPrimeAllowance_sum_cap (c : Analysis.GammaLocalCellData)
    (rows : ℕ → Analysis.GammaLocalPrimeRow) (hc : c.check = true) {lo root E : ℚ} (hr : 0 < root)
    (hrlo : root ^ 2 ≤ lo) (hlhi : lo ≤ c.hi) (S : Finset ℕ)
    (hsub : Analysis.gammaAnchoredWindowPrimeSet c.hi ⊆ S) (hp : ∀ p ∈ S, p.Prime)
    (hcheck : ∀ p ∈ S, (rows p).prime = p ∧ (rows p).envelopeCheck c = true)
    (hE : (∑ p ∈ S, loweredPrimeAllowance c rows lo root p) ≤ E) :
    (∑ p ∈ Analysis.gammaAnchoredWindowPrimeSet c.hi,
        Real.log p *
          Analysis.gammaRamifiedWindowExcessBound lo c.hi (rows p).eulerUpper
            (((rows p).rampUpper : ℝ) - 5 / 4 +
              (((p : ℝ) + 1) / (p - 1)) * ((c.lo : ℝ) - lo) / lo)) ≤
      (E : ℝ) := by
  have hcap (p : ℕ) (hm : p ∈ S) :=
    loweredPrimeAllowance_cap c rows hc hr hrlo hlhi (hp p hm) (hcheck p hm).1 (hcheck p hm).2
  have heR : (∑ p ∈ S, (loweredPrimeAllowance c rows lo root p : ℝ)) ≤ (E : ℝ) := by
    exact_mod_cast hE
  have hnonneg (p : ℕ) (hm : p ∈ S) : (0 : ℝ) ≤ loweredPrimeAllowance c rows lo root p :=
    (mul_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr (hp p hm).one_le)) (le_max_right _ _)).trans
      (hcap p hm)
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hm _ ↦ hnonneg p hm)
  exact (Finset.sum_le_sum (fun p hm ↦ hcap p (hsub hm))).trans (hs.trans heR)

/-- For a lowered checked window and nonnegative input log L, a rational sum cap
gives the actual dual budget at most 5L/(4root)+E throughout the window.
Combine the aggregate transfer with the lower square-root bound. -/
theorem loweredPrimeAllowance_dual_cap (c : Analysis.GammaLocalCellData)
    (rows : ℕ → Analysis.GammaLocalPrimeRow) (hc : c.check = true) {lo root E : ℚ} (hr : 0 < root)
    (hrlo : root ^ 2 ≤ lo) (hlo : 1 ≤ lo) (hlc : lo ≤ c.lo) (hlhi : lo ≤ c.hi) (S : Finset ℕ)
    (hsub : Analysis.gammaAnchoredWindowPrimeSet c.hi ⊆ S) (hp : ∀ p ∈ S, p.Prime)
    (hcheck : ∀ p ∈ S, (rows p).prime = p ∧ (rows p).envelopeCheck c = true)
    (he :
      ∀ p ∈ Analysis.gammaAnchoredWindowPrimeSet c.hi,
        Analysis.gammaPrimeEulerCost p ≤ ((rows p).eulerUpper : ℝ))
    (hE : (∑ p ∈ S, loweredPrimeAllowance c rows lo root p) ≤ E) {L x : ℝ} (hL : 0 ≤ L)
    (hlox : (lo : ℝ) ≤ x) (hxhi : x ≤ (c.hi : ℝ)) :
    gammaScaleSignedDualBudget L x ≤ 5 / (4 * (root : ℝ)) * L + (E : ℝ) := by
  have hsum := loweredPrimeAllowance_sum_cap c rows hc hr hrlo hlhi S hsub hp hcheck hE
  have hloR : (1 : ℝ) ≤ lo := by exact_mod_cast hlo
  have hcR : (lo : ℝ) ≤ c.lo := Rat.cast_le.mpr hlc
  have h :=
    gamma_scale_signed_dual_budget_le_lowered_window_rows_base_ratio c rows hc hL hloR hcR hlox hxhi
      (fun p hm ↦ hcheck p (hsub hm)) he hsum
  have hrR : (0 : ℝ) < root := Rat.cast_pos.mpr hr
  have hsq : (root : ℝ) ^ 2 ≤ lo := by exact_mod_cast hrlo
  have hroot := (Real.le_sqrt hrR.le (zero_le_one.trans hloR)).mpr hsq
  have hd : Analysis.gammaRamifiedDualParameter lo ≤ 5 / (4 * (root : ℝ)) := by
    dsimp only [Analysis.gammaRamifiedDualParameter]
    exact
      div_le_div₀ (by norm_num only : (0 : ℝ) ≤ 5) le_rfl (mul_pos (by norm_num only) hrR)
        (mul_le_mul_of_nonneg_left hroot (by norm_num only))
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_right hd hL) le_rfl)

end PseudoPrime.LLS
