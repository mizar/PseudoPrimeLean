/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaFiniteDerivative128
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaPowerLogApprox
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaFiniteEulerMaclaurin
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridInterpolation100
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridPowerArithmetic
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridLogArithmetic
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridSumArithmetic
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridLogCert
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node000
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node016
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node032
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node048
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node064
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node080
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node096
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node112
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node128

/-! # Soundness bounds for the height-100 finite grid -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A uniform `1/10000` approximation to the first 512 complex powers and
a bound of 6 for the endpoint coefficient transfer a rational-sum lower
bound `6/5` to the analytic finite approximation lower bound `9/8`. -/
private theorem finite_grid_re_lower (s d : ℂ) (q : ℕ → ℂ)
    (hterm : ∀ n ∈ Finset.Icc (1 : ℕ) 512, ‖(n : ℂ) ^ (-s) - q n‖ ≤ 1 / 10000) (hd : ‖d‖ ≤ 6)
    (hsum : (6 / 5 : ℝ) ≤ ((∑ n ∈ Finset.Icc (1 : ℕ) 511, q n) + d * q 512).re) :
    (9 / 8 : ℝ) ≤ ((∑ n ∈ Finset.Icc (1 : ℕ) 511, (n : ℂ) ^ (-s)) + d * (512 : ℂ) ^ (-s)).re := by
  have hsumle :
    (∑ n ∈ Finset.Icc (1 : ℕ) 511, (q n).re) ≤
      (∑ n ∈ Finset.Icc (1 : ℕ) 511, (((n : ℂ) ^ (-s)).re + 1 / 10000)) := by
    apply Finset.sum_le_sum
    intro n hn
    have hmem : n ∈ Finset.Icc (1 : ℕ) 512 := by
      exact
        Finset.mem_Icc.mpr
          ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans (by norm_num only)⟩
    have h := (Complex.abs_re_le_norm _).trans (hterm n hmem)
    simp only [Complex.sub_re] at h
    have h' := (abs_le.mp h).1
    linarith only [h']
  have hlast := hterm 512 (Finset.mem_Icc.mpr ⟨by norm_num only, le_rfl⟩)
  have hprod : ‖d * ((512 : ℂ) ^ (-s) - q 512)‖ ≤ 6 / 10000 := by
    rw [norm_mul]
    have h := mul_le_mul hd hlast (norm_nonneg _) (by norm_num only : (0 : ℝ) ≤ 6)
    norm_num only at h ⊢
    exact h
  have hre := (Complex.abs_re_le_norm _).trans hprod
  simp only [mul_sub, Complex.sub_re] at hre
  have hre' := (abs_le.mp hre).1
  simp only [Complex.add_re, Complex.re_sum] at hsum ⊢
  rw [Finset.sum_add_distrib] at hsumle
  norm_num only [Finset.sum_const, Nat.card_Icc, Nat.cast_ofNat, nsmul_eq_mul] at hsumle
  linarith only [hsumle, hre', hsum]

/-- At height 100, the endpoint coefficient of the 512th power has norm
at most 6, since the distance to the pole at one is at least 100. -/
private theorem norm_grid_coefficient (s : ℂ) (hi : s.im = 100) :
    ‖(512 : ℂ) / (s - 1) + 1 / 2‖ ≤ 6 := by
  have hd : (100 : ℝ) ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    simp only [Complex.sub_im, Complex.one_im, sub_zero, hi] at h
    norm_num only at h
    exact h
  have hp : ‖(512 : ℂ) / (s - 1)‖ ≤ (512 : ℝ) / 100 := by
    rw [norm_div, Complex.norm_ofNat]
    exact div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hd
  have hh : ‖(1 : ℂ) / 2‖ = (1 / 2 : ℝ) := by norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  have htri := norm_add_le ((512 : ℂ) / (s - 1)) (1 / 2)
  linarith only [hp, hh, htri]

/-- The two Euler–Maclaurin endpoint corrections combine into one
coefficient times the 512th power. The identity holds for all complex `s`. -/
private theorem grid_correction_eq (s : ℂ) :
    (512 : ℂ) ^ (1 - s) / (s - 1) + (512 : ℂ) ^ (-s) / 2 =
      ((512 : ℂ) / (s - 1) + 1 / 2) * (512 : ℂ) ^ (-s) := by
  rw [show (1 : ℂ) - s = 1 + (-s) by ring,
    Complex.cpow_add 1 (-s) (by norm_num only : (512 : ℂ) ≠ 0), Complex.cpow_one]
  ring

/-- Under RH, uniform approximations of the first 512 powers at each of
the 129 grid points and a lower bound for the corresponding corrected sums
imply `N(100) ≤ 58`. The finite values are arbitrary inputs; no table is
assumed. The preceding analytic bounds account for all approximation errors. -/
theorem count_100_le_58_of_power_approx (hRH : RiemannHypothesis) (q : ℕ → ℕ → ℂ)
    (hterm :
      ∀ k : ℕ,
        k ≤ 128 →
          ∀ n ∈ Finset.Icc (1 : ℕ) 512,
            let s : ℂ := (((1 / 2 + (k : ℝ) / 128 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)
            ‖(n : ℂ) ^ (-s) - q k n‖ ≤ 1 / 10000)
    (hsum :
      ∀ k : ℕ,
        k ≤ 128 →
          let s : ℂ := (((1 / 2 + (k : ℝ) / 128 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)
          (6 / 5 : ℝ) ≤
            ((∑ n ∈ Finset.Icc (1 : ℕ) 511, q k n) + ((512 : ℂ) / (s - 1) + 1 / 2) * q k 512).re) :
    zeroCount 100 ≤ 58 := by
  apply count_100_le_58_of_finite_grid hRH
  intro k hk
  let s : ℂ := (((1 / 2 + (k : ℝ) / 128 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)
  have hi : s.im = 100 := by
    simp only [s, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero]
  have h :=
    finite_grid_re_lower s ((512 : ℂ) / (s - 1) + 1 / 2) (q k) (hterm k hk)
      (norm_grid_coefficient s hi) (hsum k hk)
  rw [← grid_correction_eq s] at h
  simpa only [← add_assoc] using h

/-- Grid points lie in the nonnegative half-plane and have norm at most 102.
This controls the propagation of logarithm approximation errors. -/
private theorem grid_point_bounds (k : ℕ) (hk : k ≤ 128) :
    let s : ℂ := (((1 / 2 + (k : ℝ) / 128 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)
    0 ≤ s.re ∧ ‖s‖ ≤ 102 := by
  let s : ℂ := (((1 / 2 + (k : ℝ) / 128 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)
  have hsr : s.re = 1 / 2 + (k : ℝ) / 128 := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hsi : s.im = 100 := by
    simp only [s, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hk128 : (k : ℝ) ≤ 128 := by exact_mod_cast hk
  have hr0 : 0 ≤ s.re := by
    rw [hsr]; nlinarith only [hk0]
  have hr2 : s.re ≤ 2 := by
    rw [hsr]; nlinarith only [hk128]
  have hn := Complex.norm_le_abs_re_add_abs_im s
  rw [abs_of_nonneg hr0, hsi] at hn
  norm_num only [abs_of_nonneg] at hn
  exact ⟨hr0, by linarith only [hn, hr2]⟩

/-- A rational logarithm approximation within `10⁻⁷`, followed by the
rounded exponential evaluator, approximates the corresponding complex power
within `10⁻⁴` at every height-100 grid point. -/
private theorem norm_grid_term_approx (k : ℕ) (hk : k ≤ 128) (n : ℕ) (hn : 1 ≤ n) (q : ℚ)
    (hq0 : 0 ≤ q) (hq7 : q ≤ 7) (he : |Real.log n - (q : ℝ)| ≤ 1 / 10000000) :
    let s : ℂ := (((1 / 2 + (k : ℝ) / 128 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)
    ‖(n : ℂ) ^ (-s) - Analysis.rationalComplexCast (gridPowerApprox k q)‖ ≤ 1 / 10000 := by
  let s : ℂ := (((1 / 2 + (k : ℝ) / 128 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)
  have hs := grid_point_bounds k hk
  have hlog := norm_cpow_log_approx s hs.1 n hn q hq0 he
  have hexp := norm_grid_power_approx k hk q hq0 hq7
  have ht :=
    norm_sub_le_norm_sub_add_norm_sub ((n : ℂ) ^ (-s)) (Complex.exp ((-s) * (q : ℂ)))
      (Analysis.rationalComplexCast (gridPowerApprox k q))
  nlinarith only [ht, hlog, hexp, hs.2]

/-- Under RH, certified rational logarithm approximations and the lower
bounds for their rounded finite grid sums imply `N(100) ≤ 58`. The
computed powers are used only within this module's proof. -/
private theorem count_100_le_58_of_log_grid (hRH : RiemannHypothesis) (q : ℕ → ℚ)
    (hlog :
      ∀ n ∈ Finset.Icc (1 : ℕ) 512, 0 ≤ q n ∧ q n ≤ 7 ∧ |Real.log n - (q n : ℝ)| ≤ 1 / 10000000)
    (hsum :
      ∀ k : ℕ,
        k ≤ 128 →
          let s : ℂ := (((1 / 2 + (k : ℝ) / 128 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)
          (6 / 5 : ℝ) ≤
            ((∑ n ∈ Finset.Icc (1 : ℕ) 511,
                  Analysis.rationalComplexCast (gridPowerApprox k (q n))) +
                ((512 : ℂ) / (s - 1) + 1 / 2) *
                  Analysis.rationalComplexCast (gridPowerApprox k (q 512))).re) :
    zeroCount 100 ≤ 58 := by
  apply
    count_100_le_58_of_power_approx hRH
      (fun k n => Analysis.rationalComplexCast (gridPowerApprox k (q n)))
  · intro k hk n hn
    have h := hlog n hn
    exact norm_grid_term_approx k hk n (Finset.mem_Icc.mp hn).1 (q n) h.1 h.2.1 h.2.2
  · exact hsum

/-- Under RH, successful logarithm checks and lower bounds for the rounded
finite sums imply `N(100) ≤ 58`. Both computations stay private to this
certificate consumer; no precomputed table is part of the conclusion. -/
private theorem count_100_le_58_of_grid_checks (hRH : RiemannHypothesis)
    (hlog : ∀ n ∈ Finset.Icc (1 : ℕ) 512, gridLogCheck n = true)
    (hsum :
      ∀ k : ℕ,
        k ≤ 128 →
          let s : ℂ := (((1 / 2 + (k : ℝ) / 128 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)
          (6 / 5 : ℝ) ≤
            ((∑ n ∈ Finset.Icc (1 : ℕ) 511,
                  Analysis.rationalComplexCast (gridPowerApprox k (gridLogApprox n))) +
                ((512 : ℂ) / (s - 1) + 1 / 2) *
                  Analysis.rationalComplexCast (gridPowerApprox k (gridLogApprox 512))).re) :
    zeroCount 100 ≤ 58 := by
  apply count_100_le_58_of_log_grid hRH gridLogApprox
  · intro n hn
    exact grid_log_check_sound n (hlog n hn)
  · exact hsum

/-- Under RH, successful rational logarithm and corrected-sum checks imply
`N(100) ≤ 58`. Both finite computations are imported privately; only their
checked mathematical consequences are used in this proof. -/
private theorem count_100_le_58_of_bool_checks (hRH : RiemannHypothesis)
    (hlog : ∀ n ∈ Finset.Icc (1 : ℕ) 512, gridLogCheck n = true)
    (hsum : ∀ k : ℕ, k ≤ 128 → gridFiniteCheck k = true) : zeroCount 100 ≤ 58 := by
  apply count_100_le_58_of_grid_checks hRH hlog
  intro k hk
  exact grid_finite_check_sound k (hsum k hk)

/-- Under RH, the 129 rational finite-sum checks imply `N(100) ≤ 58`.
The 512 logarithm checks are supplied by the internal kernel certificate. -/
private theorem count_100_le_58_of_sum_checks (hRH : RiemannHypothesis)
    (hsum : ∀ k : ℕ, k ≤ 128 → gridFiniteCheck k = true) : zeroCount 100 ≤ 58 := by
  exact count_100_le_58_of_bool_checks hRH grid_log_check_all hsum

/-- A successful finite-sum check at a grid point proves that the real part
of zeta there is at least one. The logarithm certificate and all analytic
error bounds are supplied internally. -/
private theorem zeta_re_grid_of_check (k : ℕ) (hk : k ≤ 128) (hcheck : gridFiniteCheck k = true) :
    1 ≤ (riemannZeta (((1 / 2 + (k : ℝ) / 128 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).re := by
  let s : ℂ := (((1 / 2 + (k : ℝ) / 128 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)
  have hcoords : (1 / 2 : ℝ) ≤ s.re ∧ s.re ≤ 2 ∧ 99 ≤ s.im ∧ s.im ≤ 101 := by
    dsimp only [s]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_add, add_zero]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have hk128 : (k : ℝ) ≤ 128 := by exact_mod_cast hk
    constructor
    · nlinarith only [hk0]
    constructor
    · nlinarith only [hk128]
    constructor <;> norm_num only
  have hi : s.im = 100 := by
    simp only [s, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero]
  have hterm :
    ∀ n ∈ Finset.Icc (1 : ℕ) 512,
      ‖(n : ℂ) ^ (-s) - Analysis.rationalComplexCast (gridPowerApprox k (gridLogApprox n))‖ ≤
        1 / 10000 := by
    intro n hn
    have hlog := grid_log_check_sound n (grid_log_check_all n hn)
    exact
      norm_grid_term_approx k hk n (Finset.mem_Icc.mp hn).1 (gridLogApprox n) hlog.1 hlog.2.1
        hlog.2.2
  have h :=
    finite_grid_re_lower s ((512 : ℂ) / (s - 1) + 1 / 2)
      (fun n => Analysis.rationalComplexCast (gridPowerApprox k (gridLogApprox n))) hterm
      (norm_grid_coefficient s hi) (grid_finite_check_sound k hcheck)
  apply zeta_re_lower_of_finite_512 hcoords.1 hcoords.2.1 hcoords.2.2.1 hcoords.2.2.2
  rw [add_assoc, grid_correction_eq]
  exact h

/-- Under RH, the 9 rational checks with indices `16*j`, `j ≤ 8`,
imply `N(100) ≤ 58`. The internal second-order interpolation covers every
point between these nodes and avoids requiring the other 120 checks. -/
private theorem count_100_le_58_of_sparse_checks (hRH : RiemannHypothesis)
    (hchecks : ∀ j : ℕ, j ≤ 8 → gridFiniteCheck (16 * j) = true) : zeroCount 100 ≤ 58 := by
  apply count_100_le_58_of_grid8 hRH
  intro j hj
  have hk : 16 * j ≤ 128 := by
    have h := Nat.mul_le_mul_left 16 hj
    norm_num only at h
    exact h
  have h := zeta_re_grid_of_check (16 * j) hk (hchecks j hj)
  have he : (1 / 2 : ℝ) + ((16 * j : ℕ) : ℝ) / 128 = 1 / 2 + (j : ℝ) / 8 := by
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [he] at h
  exact h

/-- The nine individual sparse grid checks cover every index `16*j` with
`j ≤ 8`. This finite case split is independent of how each check is proved. -/
private theorem sparse_checks_of_nine (h0 : gridFiniteCheck 0 = true)
    (h1 : gridFiniteCheck 16 = true) (h2 : gridFiniteCheck 32 = true)
    (h3 : gridFiniteCheck 48 = true) (h4 : gridFiniteCheck 64 = true)
    (h5 : gridFiniteCheck 80 = true) (h6 : gridFiniteCheck 96 = true)
    (h7 : gridFiniteCheck 112 = true) (h8 : gridFiniteCheck 128 = true) :
    ∀ j : ℕ, j ≤ 8 → gridFiniteCheck (16 * j) = true := by
  have hh (i : Fin 9) : gridFiniteCheck (16 * i.val) = true := by
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
    · exact h8
  intro j hj
  exact hh ⟨j, Nat.lt_succ_of_le hj⟩

/-- Under RH, the nine individual sparse grid checks imply `N(100) ≤ 58`.
The endpoint and intermediate checks are supplied separately so that their
independent kernel builds can be combined without exposing a table. -/
private theorem count_100_le_58_of_nine (hRH : RiemannHypothesis) (h0 : gridFiniteCheck 0 = true)
    (h1 : gridFiniteCheck 16 = true) (h2 : gridFiniteCheck 32 = true)
    (h3 : gridFiniteCheck 48 = true) (h4 : gridFiniteCheck 64 = true)
    (h5 : gridFiniteCheck 80 = true) (h6 : gridFiniteCheck 96 = true)
    (h7 : gridFiniteCheck 112 = true) (h8 : gridFiniteCheck 128 = true) : zeroCount 100 ≤ 58 := by
  exact count_100_le_58_of_sparse_checks hRH (sparse_checks_of_nine h0 h1 h2 h3 h4 h5 h6 h7 h8)

/-- Under RH, at most 58 zeta zeros, counted with multiplicity and on both
sides of the real axis, lie through height 100. Nine internally certified
finite sums and a second-derivative bound prove positivity on the horizontal
segment used in the zero-count estimate. -/
theorem zero_count_100_le_58_of_RH (hRH : RiemannHypothesis) : zeroCount 100 ≤ 58 := by
  exact
    count_100_le_58_of_nine hRH ZetaGridChecks.node000 ZetaGridChecks.node016 ZetaGridChecks.node032
      ZetaGridChecks.node048 ZetaGridChecks.node064 ZetaGridChecks.node080 ZetaGridChecks.node096
      ZetaGridChecks.node112 ZetaGridChecks.node128

/-- At `1/2 + 100i`, the real part of zeta is at least one. The proof uses
the internally checked finite Euler–Maclaurin approximation and its error
bound; neither RH nor a zero table is assumed. -/
theorem one_le_zeta_re_half_100 :
    1 ≤ (riemannZeta (((1 / 2 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).re := by
  have h := zeta_re_grid_of_check 0 (by norm_num only) ZetaGridChecks.node000
  norm_num only [Nat.cast_zero, zero_div, add_zero] at h
  exact h

/-- At `3/2 + 100i`, the real part of zeta is at least one. The endpoint
value is certified by the same internally checked finite approximation. -/
theorem one_le_zeta_re_three_halves_100 :
    1 ≤ (riemannZeta (((3 / 2 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).re := by
  have h := zeta_re_grid_of_check 128 (by norm_num only) ZetaGridChecks.node128
  norm_num only [Nat.cast_ofNat] at h
  exact h

/-- Under RH, height 100 contains no zeta zero with nonnegative real part.
The critical-line value is nonzero by the internally certified finite sum,
and RH places every such zero on that line. -/
theorem good_height_100_of_RH (hRH : RiemannHypothesis) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ 100 := by
  have hcenter : riemannZeta (((1 / 2 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro hz
    have h := one_le_zeta_re_half_100
    rw [hz, Complex.zero_re] at h
    norm_num only at h
  exact good_height_100_of_center_ne hRH hcenter

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
