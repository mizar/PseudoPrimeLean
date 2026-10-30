/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LogDerivBound
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.TrigonometricComparison

/-!
# Local zero residues in the zeta trigonometric comparison

Jensen factorization supplies an explicit squared-log remainder bound at every large
height, without requiring the height to avoid zeros. A selected actual zero is retained
in the three-four-one comparison.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Every zeta zero has real part at most one. Right-half-plane nonvanishing
excludes a larger real part. This gives the sign of the local zero residues. -/
theorem re_zero_le_one {u : ℂ} (hu : riemannZeta u = 0) : u.re ≤ 1 := by
  by_contra h
  exact riemannZeta_ne_zero_of_one_lt_re (lt_of_not_ge h) hu

/-- To the right of one, each nonnegative integral multiple of a zeta-zero residue
has nonnegative real part. Use the real quotient formula and the location of zeros.
This permits discarding other zeros without a height-separation assumption. -/
theorem zero_residue_re_nonneg {s u : ℂ} (hs : 1 < s.re) (hu : riemannZeta u = 0) (m : ℕ) :
    0 ≤ ((m : ℂ) / (s - u)).re := by
  rw [Complex.div_re]
  simp only [Complex.natCast_re, Complex.natCast_im, Complex.sub_re, zero_mul, zero_div, add_zero]
  exact
    div_nonneg (mul_nonneg (Nat.cast_nonneg m) (sub_nonneg.mpr ((re_zero_le_one hu).trans hs.le)))
      (Complex.normSq_nonneg _)

/-- If a point and a zero have the same imaginary part, the real part of the
residue with natural multiplicity is the real reciprocal distance times that multiplicity.
Identify their difference with a real complex number; this isolates a selected zero. -/
theorem zero_residue_re_of_same_im {s u : ℂ} (him : s.im = u.im) (m : ℕ) :
    ((m : ℂ) / (s - u)).re = (m : ℝ) / (s.re - u.re) := by
  have he : s - u = ((s.re - u.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.ofReal_re]
    · simp only [Complex.sub_im, Complex.ofReal_im, him, sub_self]
  rw [he, ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re]

/-- Given an analytic nonvanishing local factor and its finite positive-multiplicity
zeta-zero factorization, a selected zero at the evaluation height contributes at least
its reciprocal real distance. Discard the other nonnegative residues and bound the
remainder by its norm. This is the selected-zero input to the trigonometric comparison. -/
theorem re_logDeriv_ge_zero_pole {z : ℂ} {R : ℝ} {S : Finset ℂ} {m : ℂ → ℕ} {g : ℂ → ℂ}
    (hgAn : AnalyticOnNhd ℂ g (Metric.ball z R)) (hgne : ∀ w ∈ Metric.ball z R, g w ≠ 0)
    (hmpos : ∀ u ∈ S, 0 < m u) (hzero : ∀ u ∈ S, riemannZeta u = 0)
    (heq : Set.EqOn riemannZeta (fun w ↦ (∏ u ∈ S, (w - u) ^ m u) * g w) (Metric.ball z R))
    {s ρ : ℂ} (hsU : s ∈ Metric.ball z R) (hs : 1 < s.re) (hρ : ρ ∈ S) (him : s.im = ρ.im) :
    1 / (s.re - ρ.re) - ‖logDeriv g s‖ ≤ (logDeriv riemannZeta s).re := by
  have hfac :=
    logDeriv_riemannZeta_eq_sum_add_logDeriv_at hgAn hgne hmpos heq hsU
      (riemannZeta_ne_zero_of_one_lt_re hs)
  have hsum := Finset.single_le_sum (fun u hu ↦ zero_residue_re_nonneg hs (hzero u hu) (m u)) hρ
  rw [zero_residue_re_of_same_im him] at hsum
  have hd : 0 < s.re - ρ.re := sub_pos.mpr ((re_zero_le_one (hzero ρ hρ)).trans_lt hs)
  have hm : (1 : ℝ) ≤ (m ρ : ℝ) := by exact_mod_cast hmpos ρ hρ
  have hdiv := div_le_div_of_nonneg_right hm hd.le
  have hg := Complex.re_le_norm (-logDeriv g s)
  rw [Complex.neg_re, norm_neg] at hg
  have he := congrArg Complex.re hfac
  rw [Complex.add_re,
    show (∑ u ∈ S, (m u : ℂ) / (s - u)).re = ∑ u ∈ S, ((m u : ℂ) / (s - u)).re from
      map_sum Complex.reAddGroupHom _ S] at he
  linarith only [hsum, hdiv, hg, he]

/-- Given a local zeta factorization into positive-multiplicity zeros and an analytic
nonvanishing factor, the real logarithmic derivative to the right of one is at least
the negative norm of the factor logarithmic derivative. Discard the nonnegative residues.
This controls the double-height term in the zero-free-region comparison. -/
theorem re_logDeriv_ge_neg_remainder {z : ℂ} {R : ℝ} {S : Finset ℂ} {m : ℂ → ℕ} {g : ℂ → ℂ}
    (hgAn : AnalyticOnNhd ℂ g (Metric.ball z R)) (hgne : ∀ w ∈ Metric.ball z R, g w ≠ 0)
    (hmpos : ∀ u ∈ S, 0 < m u) (hzero : ∀ u ∈ S, riemannZeta u = 0)
    (heq : Set.EqOn riemannZeta (fun w ↦ (∏ u ∈ S, (w - u) ^ m u) * g w) (Metric.ball z R)) {s : ℂ}
    (hsU : s ∈ Metric.ball z R) (hs : 1 < s.re) :
    -‖logDeriv g s‖ ≤ (logDeriv riemannZeta s).re := by
  have hfac :=
    logDeriv_riemannZeta_eq_sum_add_logDeriv_at hgAn hgne hmpos heq hsU
      (riemannZeta_ne_zero_of_one_lt_re hs)
  have hsum := Finset.sum_nonneg (fun u hu ↦ zero_residue_re_nonneg hs (hzero u hu) (m u))
  have hg := Complex.re_le_norm (-logDeriv g s)
  rw [Complex.neg_re, norm_neg] at hg
  have he := congrArg Complex.re hfac
  rw [Complex.add_re,
    show (∑ u ∈ S, (m u : ℂ) / (s - u)).re = ∑ u ∈ S, ((m u : ℂ) / (s - u)).re from
      map_sum Complex.reAddGroupHom _ S] at he
  linarith only [hsum, hg, he]

/-- At every height at least eight, there is a local zeta-zero factorization whose
nonvanishing factor has logarithmic derivative bounded by the existing explicit constant
times the squared height logarithm throughout the real segment from minus one half to two.
Apply the Jensen real-part estimate and its off-center derivative bound, retaining the
finite zero set and its positive multiplicities for subsequent selected-zero estimates. -/
theorem exists_local_logDeriv_bound {T : ℝ} (hT : 8 ≤ T) :
    ∃ (R : ℝ) (S : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
      71 / 20 < R ∧
        R < 37 / 10 ∧
        AnalyticOnNhd ℂ g (Metric.ball (jensenCenter T) R) ∧
        (∀ w ∈ Metric.ball (jensenCenter T) R, g w ≠ 0) ∧
        (∀ u ∈ S, 0 < m u) ∧
        (∀ u ∈ S, riemannZeta u = 0) ∧
        Set.EqOn riemannZeta (fun w ↦ (∏ u ∈ S, (w - u) ^ m u) * g w)
          (Metric.ball (jensenCenter T) R) ∧
        (∀ σ : ℝ,
          -(1 : ℝ) / 2 ≤ σ →
            σ ≤ 2 →
            ‖logDeriv g ((σ : ℂ) + T * Complex.I)‖ ≤
              qMinusOneZetaLogDerivConst * Real.log (T + 2) ^ 2) := by
  obtain
    ⟨R1, R2, S, m, g, h, M, hR1big, hR1R2, hR2small, hgAn, hgne, hmpos, hh', hSzero, _, heqOn, hMc,
      hgjc_ge, hMle, hMbound⟩ :=
    exists_bound_re_logDeriv_g_jensen_good_radius hT
  refine ⟨R2, S, m, g, hR1big.trans_lt hR1R2, hR2small, hgAn, hgne, hmpos, hSzero, heqOn, ?_⟩
  intro σ hσ1 hσ2
  set z : ℂ := σ + T * Complex.I with hz_def
  set c : ℂ := jensenCenter T with hc_def
  have hcim : c.im = T := by
    rw [hc_def]
    exact jensenCenter_im T
  have hcre : c.re = 3 := by
    rw [hc_def]
    exact jensenCenter_re T
  have hzim : z.im = T := by
    simp only [hz_def, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  have hzre : z.re = σ := by
    simp only [hz_def, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  set d : ℝ := ‖z - c‖ with hd_def
  have hzc_eq : z - c = ((σ - 3 : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.sub_re, hzre, hcre, Complex.ofReal_re]
    · simp only [Complex.sub_im, hzim, hcim, Complex.ofReal_im, sub_self]
  have hd_eq : d = |σ - 3| := by rw [hd_def, hzc_eq, Complex.norm_real, Real.norm_eq_abs]
  have hd_le : d ≤ 7 / 2 := by
    rw [hd_eq, abs_le]
    constructor <;> linarith only [hσ1, hσ2]
  have hR1pos : (0 : ℝ) < R1 := lt_of_lt_of_le (by norm_num only) hR1big
  have hzR1 : z ∈ Metric.ball c R1 := by
    rw [Metric.mem_ball, dist_eq_norm, ← hd_def]
    linarith only [hR1big, hd_le]
  have hh'R1 : ∀ w ∈ Metric.ball c R1, HasDerivAt h (logDeriv g w) w := fun w hw ↦
    hh' w (Metric.ball_subset_ball hR1R2.le hw)
  have hMboundOpen : ∀ w ∈ Metric.ball c R1, (h w).re ≤ M := fun w hw ↦
    hMbound w (Metric.ball_subset_closedBall hw)
  have hderiv_bound := norm_hasDerivAt_le_of_re_le hR1pos hh'R1 hMc hMboundOpen hzR1
  have hnn :
    0 ≤ jensenLogConst * Real.log (T + 2) * max (4 * jensenLogConst * Real.log (T + 2)) 1 :=
    mul_nonneg (mul_nonneg jensenLogConst_pos.le (Real.log_nonneg (by linarith only [hT])))
      ((le_max_right _ _).trans' zero_le_one)
  exact
    le_qMinusOneZetaLogDerivConst_mul_log_sq_of_semi_explicit hT le_rfl (by linarith only) hR1big
      (hR1R2.trans hR2small) hd_le hMc hMle hgjc_ge (hderiv_bound.trans (le_add_of_nonneg_left hnn))

/-- A zeta zero inside a nonvanishing-factor decomposition belongs to its finite zero set.
Otherwise every product factor and the analytic remainder would be nonzero.
This connects an arbitrary actual zero to the local selected-zero estimate. -/
theorem zero_mem_factorization {z : ℂ} {R : ℝ} {S : Finset ℂ} {m : ℂ → ℕ} {g : ℂ → ℂ}
    (hgne : ∀ w ∈ Metric.ball z R, g w ≠ 0)
    (heq : Set.EqOn riemannZeta (fun w ↦ (∏ u ∈ S, (w - u) ^ m u) * g w) (Metric.ball z R)) {ρ : ℂ}
    (hρU : ρ ∈ Metric.ball z R) (hρ : riemannZeta ρ = 0) : ρ ∈ S := by
  classical
  by_contra hnot
  have hp : (∏ u ∈ S, (ρ - u) ^ m u) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr
      (fun u hu ↦ pow_ne_zero _ (sub_ne_zero.mpr (fun he ↦ hnot (he ▸ hu))))
  exact (mul_ne_zero hp (hgne ρ hρU)) ((heq hρU).symm.trans hρ)

/-- A point at the Jensen height with real part between minus one half and two
lies in any Jensen-centered disk of radius greater than seventy-one twentieths.
Reduce its distance to a real absolute value; this locates evaluation points and zeros. -/
theorem mem_jensen_ball_of_re_im {T R : ℝ} (hR : 71 / 20 < R) {s : ℂ} (ha : -(1 : ℝ) / 2 ≤ s.re)
    (hb : s.re ≤ 2) (him : s.im = T) : s ∈ Metric.ball (jensenCenter T) R := by
  have he : s - jensenCenter T = ((s.re - 3 : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.sub_re, jensenCenter_re, Complex.ofReal_re]
    · simp only [Complex.sub_im, jensenCenter_im, him, sub_self, Complex.ofReal_im]
  rw [Metric.mem_ball, dist_eq_norm, he, Complex.norm_real, Real.norm_eq_abs]
  have h : |s.re - 3| ≤ 7 / 2 := abs_le.mpr ⟨by linarith only [ha], by linarith only [hb]⟩
  linarith only [h, hR]

/-- For any actual zeta zero of nonnegative real part at height at least eight,
and any evaluation real part between one and two, its reciprocal real distance is bounded
by the real-axis zeta logarithmic derivative and two explicit squared-log remainder costs.
Construct local factors at the zero height and twice that height, isolate the selected zero,
and apply the unconditional three-four-one inequality. No RH or zero-free-region input is used. -/
theorem zero_pole_le_logDeriv_budget {T σ : ℝ} (hT : 8 ≤ T) (hσ : 1 < σ) (hσ2 : σ ≤ 2) {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (hρ0 : 0 ≤ ρ.re) (him : ρ.im = T) :
    4 / (σ - ρ.re) ≤
      -3 * (logDeriv riemannZeta (σ : ℂ)).re +
        4 * qMinusOneZetaLogDerivConst * Real.log (T + 2) ^ 2 +
        qMinusOneZetaLogDerivConst * Real.log (2 * T + 2) ^ 2 := by
  obtain ⟨R, S, m, g, hR, _, hgAn, hgne, hm, hzero, heq, hbound⟩ := exists_local_logDeriv_bound hT
  have hρU :=
    mem_jensen_ball_of_re_im hR (by linarith only [hρ0])
      ((re_zero_le_one hρ).trans (by norm_num only)) him
  have hρS := zero_mem_factorization hgne heq hρU hρ
  have hsre : ((σ : ℂ) + T * Complex.I).re = σ := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hsim : ((σ : ℂ) + T * Complex.I).im = T := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_zero, mul_one, add_zero, zero_add]
  have hlow :=
    re_logDeriv_ge_zero_pole hgAn hgne hm hzero heq
      (mem_jensen_ball_of_re_im hR
        (by
          rw [hsre]; linarith only [hσ])
        (hsre.trans_le hσ2) hsim)
      (by
        rw [hsre]; exact hσ)
      hρS (hsim.trans him.symm)
  rw [hsre] at hlow
  have hg := hbound σ (by linarith only [hσ]) hσ2
  obtain ⟨R2, S2, m2, g2, hR2, _, hgAn2, hgne2, hm2, hzero2, heq2, hbound2⟩ :=
    exists_local_logDeriv_bound (show 8 ≤ 2 * T by linarith only [hT])
  have hs2re : ((σ : ℂ) + ((2 * T : ℝ) : ℂ) * Complex.I).re = σ := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hs2im : ((σ : ℂ) + ((2 * T : ℝ) : ℂ) * Complex.I).im = 2 * T := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_zero, mul_one, add_zero, zero_add]
  have hlow2 :=
    re_logDeriv_ge_neg_remainder hgAn2 hgne2 hm2 hzero2 heq2
      (mem_jensen_ball_of_re_im hR2
        (by
          rw [hs2re]; linarith only [hσ])
        (hs2re.trans_le hσ2) hs2im)
      (by
        rw [hs2re]; exact hσ)
  have hg2 := hbound2 σ (by linarith only [hσ]) hσ2
  have htrig := three_four_one_logDeriv_nonneg hσ T
  norm_num only [Complex.ofReal_mul, Complex.ofReal_ofNat] at hlow2 hg2 htrig
  rw [show (4 : ℝ) / (σ - ρ.re) = 4 * (1 / (σ - ρ.re)) by ring]
  linarith only [hlow, hg, hlow2, hg2, htrig]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
