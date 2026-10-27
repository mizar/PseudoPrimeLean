/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
module

public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Meromorphic.LogDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.PSeries
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ConductorPrimeFactors
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorVerticalGrowth
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CenteredHadamard
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HadamardLimit
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ShiftedPoissonEulerBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveFunctionalEquation
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveZeroTransfer
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ZeroCounting
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.PowerSumInterpolation

/-! # Local analytic estimates for zero counting -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/--
Inputs: a complex zero `ρ` with real part in `[1-η, 1]`, a height `t`, and a nonnegative width
`η` such that `|t - ρ.im| ≤ η`.
Claim: the distance from `ρ` to `1 + η + it` is at most `3η`.
Proof: bound the real-part difference by `2η`, the imaginary-part difference by `η`, and apply
the triangle inequality for the complex norm.
Role: places every zero in a height window inside the radius-`3η` disk used by local power sums.
-/
theorem norm_one_add_eta_add_it_sub_le_three_eta {η t : ℝ} {ρ : ℂ} (hη : 0 ≤ η)
    (hρlower : 1 - η ≤ ρ.re) (hρupper : ρ.re ≤ 1) (ht : |t - ρ.im| ≤ η) :
    ‖((1 + η : ℝ) : ℂ) + (t : ℂ) * Complex.I - ρ‖ ≤ 3 * η := by
  have hdecomp :
    ((1 + η : ℝ) : ℂ) + (t : ℂ) * Complex.I - ρ =
      ((1 + η - ρ.re : ℝ) : ℂ) + ((t - ρ.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul, add_zero]
    · simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_add]
      ring
  have hrealLower : 0 ≤ 1 + η - ρ.re := by linarith only [hρupper, hη]
  have hrealUpper : 1 + η - ρ.re ≤ 2 * η := by linarith only [hρlower]
  calc
    ‖((1 + η : ℝ) : ℂ) + (t : ℂ) * Complex.I - ρ‖ =
        ‖((1 + η - ρ.re : ℝ) : ℂ) + ((t - ρ.im : ℝ) : ℂ) * Complex.I‖ :=
      congrArg norm hdecomp
    _ ≤ ‖((1 + η - ρ.re : ℝ) : ℂ)‖ + ‖((t - ρ.im : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |1 + η - ρ.re| + |t - ρ.im| := by
      simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I]
      ring
    _ ≤ 2 * η + η :=
      add_le_add
        (by
          rw [abs_of_nonneg hrealLower]; exact hrealUpper)
        ht
    _ = 3 * η := by ring

/--
Inputs: a finite weighted family of zeros, a positive width `η`, and a height `t`; every zero has
real part in `[1-η, 1]`, imaginary part within `η` of `t`, and differs from `1+η+it`.
Claim: one of the next `s.card` weighted reciprocal-distance power sums has a positive lower
bound determined by the norm of the total weight.
Proof: place all zeros in the radius-`3η` disk and apply the finite weighted reciprocal Turán
estimate.
Role: preserves zero multiplicities as weights when local height-window zeros are sent to power
sums.
-/
theorem exists_height_window_weighted_reciprocal_power_sum (s : Finset ℂ) (a : ℂ → ℂ) (M : ℕ)
    (hs : 0 < s.card) {η t : ℝ} (hη : 0 < η) (hrealLower : ∀ ρ ∈ s, 1 - η ≤ ρ.re)
    (hrealUpper : ∀ ρ ∈ s, ρ.re ≤ 1) (himag : ∀ ρ ∈ s, |t - ρ.im| ≤ η)
    (hne : ∀ ρ ∈ s, ((1 + η : ℝ) : ℂ) + (t : ℂ) * Complex.I ≠ ρ) (hmass : 0 < ‖∑ ρ ∈ s, a ρ‖) :
    ∃ l ∈ Finset.range s.card,
      0 < ‖∑ ρ ∈ s, a ρ‖ / (2 ^ (M + 2 * s.card) * (3 * η) ^ (M + 1 + l)) ∧
        ‖∑ ρ ∈ s, a ρ‖ / (2 ^ (M + 2 * s.card) * (3 * η) ^ (M + 1 + l)) ≤
          ‖∑ ρ ∈ s, a ρ * (((1 + η : ℝ) : ℂ) + (t : ℂ) * Complex.I - ρ)⁻¹ ^ (M + 1 + l)‖ := by
  have hzeros :
    ∀ ρ ∈ s,
      0 < ‖((1 + η : ℝ) : ℂ) + (t : ℂ) * Complex.I - ρ‖ ∧
        ‖((1 + η : ℝ) : ℂ) + (t : ℂ) * Complex.I - ρ‖ ≤ 3 * η := by
    intro ρ hρ
    constructor
    · exact norm_pos_iff.mpr (sub_ne_zero.mpr (hne ρ hρ))
    · exact
        norm_one_add_eta_add_it_sub_le_three_eta hη.le (hrealLower ρ hρ) (hrealUpper ρ hρ)
          (himag ρ hρ)
  obtain ⟨l, hl, hpower⟩ :=
    exists_finset_weighted_reciprocal_power_sum_norm_ge_of_disk s
      (((1 + η : ℝ) : ℂ) + (t : ℂ) * Complex.I) a M hs (3 * η) (by positivity) hzeros
  have hden : 0 < 2 ^ (M + 2 * s.card) * (3 * η) ^ (M + 1 + l) :=
    mul_pos (by positivity) (pow_pos (by positivity) _)
  have hratio : 0 < ‖∑ ρ ∈ s, a ρ‖ / (2 ^ (M + 2 * s.card) * (3 * η) ^ (M + 1 + l)) :=
    div_pos hmass hden
  refine ⟨l, hl, hratio, ?_⟩
  exact hpower

/--
Inputs: a globally analytic function, a nonzero value at the height-window center, and a
nonempty divisor support contained in the stated real and imaginary window.
Claim: the divisor multiplicities produce a positive weighted reciprocal power-sum lower bound.
Proof: restrict the divisor to its finite support, use nonnegative integer multiplicities to show
that their sum has norm at least one, and apply the finite height-window estimate.
Role: connects analytic zeros with multiplicity weights to the local zero-detection power sums.
-/
theorem exists_analytic_divisor_height_window_weighted_reciprocal_power_sum {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F Set.univ) {η t : ℝ} (hη : 0 < η)
    (hcenter : F (((1 + η : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hzeros :
      ∃ ρ,
        ρ ∈
            (MeromorphicOn.divisor F
                (Metric.ball (((1 + η : ℝ) : ℂ) + (t : ℂ) * Complex.I) (3 * η))).support ∧
          1 - η ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |t - ρ.im| ≤ η)
    (M : ℕ) :
    ∃ s : Finset ℂ,
      ∃ l ∈ Finset.range s.card,
        0 <
            ‖∑ ρ ∈ s,
                  ((MeromorphicOn.divisor F
                        (Metric.ball (((1 + η : ℝ) : ℂ) + (t : ℂ) * Complex.I) (3 * η)) ρ :
                      ℤ) :
                    ℂ)‖ /
              (2 ^ (M + 2 * s.card) * (3 * η) ^ (M + 1 + l)) ∧
          ‖∑ ρ ∈ s,
                  ((MeromorphicOn.divisor F
                        (Metric.ball (((1 + η : ℝ) : ℂ) + (t : ℂ) * Complex.I) (3 * η)) ρ :
                      ℤ) :
                    ℂ)‖ /
              (2 ^ (M + 2 * s.card) * (3 * η) ^ (M + 1 + l)) ≤
            ‖∑ ρ ∈ s,
                ((MeromorphicOn.divisor F
                        (Metric.ball (((1 + η : ℝ) : ℂ) + (t : ℂ) * Complex.I) (3 * η)) ρ :
                      ℤ) :
                    ℂ) *
                  (((1 + η : ℝ) : ℂ) + (t : ℂ) * Complex.I - ρ)⁻¹ ^ (M + 1 + l)‖ := by
  classical
  let c : ℂ := ((1 + η : ℝ) : ℂ) + (t : ℂ) * Complex.I
  let U : Set ℂ := Metric.ball c (3 * η)
  let d : ℂ → ℤ := MeromorphicOn.divisor F U
  have hclosed : AnalyticOnNhd ℂ F (Metric.closedBall c (3 * η)) := by
    intro z _
    exact hF z trivial
  have hfinite : d.support.Finite := by exact hclosed.meromorphicOn.divisor_ball_support_finite
  let s := hfinite.toFinset.filter fun ρ => 1 - η ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |t - ρ.im| ≤ η
  have hspos : 0 < s.card := by
    apply Finset.card_pos.mpr
    rcases hzeros with ⟨ρ, hρ, hrealLower, hrealUpper, himag⟩
    refine
      ⟨ρ,
        Finset.mem_filter.mpr
          ⟨(Set.Finite.mem_toFinset hfinite).mpr hρ, hrealLower, hrealUpper, himag⟩⟩
  have hnonneg : ∀ ρ ∈ s, 0 ≤ d ρ := by
    intro ρ _
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun z _ => hF z trivial) ρ
  obtain ⟨ρ₀, hρ₀⟩ := Finset.card_pos.mp hspos
  have hpositive : 0 < d ρ₀ := by
    have hnonzero : d ρ₀ ≠ 0 := (Set.Finite.mem_toFinset hfinite).mp (Finset.mem_filter.mp hρ₀).1
    change d ρ₀ ≠ 0 at hnonzero
    exact lt_of_le_of_ne (hnonneg ρ₀ hρ₀) (Ne.symm hnonzero)
  have hsum : 1 ≤ ∑ ρ ∈ s, d ρ := by
    have hsingle : d ρ₀ ≤ ∑ ρ ∈ s, d ρ := by
      apply Finset.single_le_sum
      · intro ρ hρ
        exact hnonneg ρ hρ
      · exact hρ₀
    omega
  have hsumcast : (∑ ρ ∈ s, (d ρ : ℂ)) = ((∑ ρ ∈ s, d ρ : ℤ) : ℂ) := by
    push_cast
    rfl
  have hsumPos : (0 : ℤ) < ∑ ρ ∈ s, d ρ := by omega
  have hmass : 0 < ‖∑ ρ ∈ s, (d ρ : ℂ)‖ := by
    rw [hsumcast, Complex.norm_intCast]
    have hreal : (0 : ℝ) < (∑ ρ ∈ s, d ρ : ℤ) := by exact_mod_cast hsumPos
    rw [abs_of_pos hreal]
    exact_mod_cast hsumPos
  have hcenterNe : ∀ ρ ∈ s, c ≠ ρ := by
    intro ρ hρ heq
    subst ρ
    have hdivzero : d c = 0 := by
      rw [show d c = MeromorphicOn.divisor F U c from rfl,
        MeromorphicOn.AnalyticOnNhd.divisor_apply (fun z _ => hF z trivial)
          (Metric.mem_ball.mpr
            (by
              simp only [dist_self]; exact mul_pos (by norm_num) hη)),
        analyticOrderAt_eq_zero.mpr (Or.inr (by simpa only [c] using hcenter))]
      rfl
    have hdivne : d c ≠ 0 := (Set.Finite.mem_toFinset hfinite).mp (Finset.mem_filter.mp hρ).1
    change d c ≠ 0 at hdivne
    exact hdivne hdivzero
  have hdistance : ∀ ρ ∈ s, 0 < ‖c - ρ‖ ∧ ‖c - ρ‖ ≤ 3 * η := by
    intro ρ hρ
    have hdivne : d ρ ≠ 0 := (Set.Finite.mem_toFinset hfinite).mp (Finset.mem_filter.mp hρ).1
    have hρU : ρ ∈ U := (MeromorphicOn.divisor F U).supportWithinDomain hdivne
    have hmem : dist ρ c < 3 * η := Metric.mem_ball.mp hρU
    rw [dist_eq_norm] at hmem
    have hsub : c - ρ ≠ 0 := by
      intro heq
      exact hcenterNe ρ hρ (sub_eq_zero.mp heq)
    constructor
    · exact norm_pos_iff.mpr hsub
    · exact le_of_lt (by simpa only [norm_sub_rev] using hmem)
  have hresult :=
    exists_finset_weighted_reciprocal_power_sum_norm_ge_of_disk s c (fun ρ => (d ρ : ℂ)) M hspos
      (3 * η) (mul_pos (by norm_num) hη) hdistance
  rcases hresult with ⟨l, hl, hbound⟩
  have hden : 0 < 2 ^ (M + 2 * s.card) * (3 * η) ^ (M + 1 + l) := by positivity
  have hpositiveRatio : 0 < ‖∑ ρ ∈ s, (d ρ : ℂ)‖ / (2 ^ (M + 2 * s.card) * (3 * η) ^ (M + 1 + l)) :=
    div_pos hmass hden
  refine ⟨s, l, hl, hpositiveRatio, ?_⟩
  simpa only [d, U, c] using hbound

/--
Inputs: a sufficiently small positive real number `x`.
Claim: The norm of `ζ(1+x) - 1/x` is bounded by a constant independent of `x`.
Proof: Use local boundedness near `s = 1` of `ζ(s) - 1/(s-1)` and place `s = 1+x` in that
neighborhood.
Role: estimates the pole term when bounding Dirichlet series with real part near `1`.
-/
theorem exists_zeta_pole_remainder_bound :
    ∃ C ε : ℝ,
      0 ≤ C ∧
        0 < ε ∧
        ε ≤ 1 ∧
        ∀ x : ℝ, 0 < x → x < ε → ‖riemannZeta (1 + (x : ℂ)) - 1 / ((1 + (x : ℂ)) - 1)‖ ≤ C := by
  have hO := isBigO_riemannZeta_sub_one_div (F := ℂ)
  obtain ⟨c, hc⟩ := hO.bound
  have hc' := hc.mono (fun s hs => by simpa only [norm_one, mul_one] using hs)
  obtain ⟨ε₀, hε₀pos, hbound⟩ := Metric.eventually_nhds_iff.mp hc'
  let C : ℝ := max c 0
  let ε : ℝ := min ε₀ 1
  refine ⟨C, ε, ?_, ?_, min_le_right _ _, ?_⟩
  · exact le_max_right c 0
  · exact lt_min hε₀pos zero_lt_one
  intro x hxpos hxlt
  have hdist : dist (1 + (x : ℂ)) (1 : ℂ) < ε₀ := by
    rw [dist_eq_norm]
    have hsub : (1 + (x : ℂ)) - 1 = (x : ℂ) := by ring
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos]
    exact lt_of_lt_of_le hxlt (min_le_left _ _)
  have hb := hbound hdist
  change ‖riemannZeta (1 + (x : ℂ)) - 1 / ((1 + (x : ℂ)) - 1)‖ ≤ c at hb
  dsimp only [C]
  exact le_trans hb (le_max_left c 0)

/--
Inputs: positive `x` within the radius of the local remainder bound.
Claim: There are a constant `C` and a radius such that `‖ζ(1+x)‖ ≤ (C+1)/x`.
Proof: Separate the pole `1/x` from the bounded remainder and use `x ≤ 1` and `C ≥ 0`.
Role: bounds Dirichlet `L`-series near real part `1`.
-/
theorem exists_riemannZeta_one_add_bound :
    ∃ C ε : ℝ,
      0 ≤ C ∧
        0 < ε ∧ ε ≤ 1 ∧ ∀ x : ℝ, 0 < x → x < ε → ‖riemannZeta (1 + (x : ℂ))‖ ≤ (C + 1) / x := by
  obtain ⟨C, ε, hC, hε, hεle, hbound⟩ := exists_zeta_pole_remainder_bound
  refine ⟨C, ε, hC, hε, hεle, ?_⟩
  intro x hx hxε
  have hrem := hbound x hx hxε
  have hden : ((1 + (x : ℂ)) - 1) = (x : ℂ) := by ring
  have hsplit :
    riemannZeta (1 + (x : ℂ)) = (riemannZeta (1 + (x : ℂ)) - (x : ℂ)⁻¹) + (x : ℂ)⁻¹ := by ring
  have hrem' : ‖riemannZeta (1 + (x : ℂ)) - (x : ℂ)⁻¹‖ ≤ C := by
    simpa only [hden, one_div] using hrem
  have hinv : ‖(x : ℂ)⁻¹‖ = 1 / x := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx, one_div]
  have hxle : x ≤ 1 := le_trans hxε.le hεle
  have hCx : C * x ≤ C := by
    calc
      C * x ≤ C * 1 := mul_le_mul_of_nonneg_left hxle hC
      _ = C := by ring
  have hxinverse : 1 / x * x = 1 := by field_simp [ne_of_gt hx]
  rw [hsplit]
  calc
    ‖(riemannZeta (1 + (x : ℂ)) - (x : ℂ)⁻¹) + (x : ℂ)⁻¹‖ ≤
        ‖riemannZeta (1 + (x : ℂ)) - (x : ℂ)⁻¹‖ + ‖(x : ℂ)⁻¹‖ :=
      norm_add_le _ _
    _ ≤ C + ‖(x : ℂ)⁻¹‖ := add_le_add hrem' (le_of_eq rfl)
    _ = C + 1 / x := by rw [hinv]
    _ ≤ (C + 1) / x := by
      apply (le_div_iff₀ hx).2
      nlinarith only [hCx, hxinverse]

/--
Inputs: a real part `σ > 1` and any real height `t`.
Claim: `‖ζ(σ+it)‖ ≤ ‖ζ(σ)‖`.
Proof: expand both values as absolutely convergent Dirichlet series, bound the norm of the
complex sum by the sum of term norms, and identify those norms with the positive real series.
Role: transfers the real-axis pole estimate to a height-uniform bound in the half-plane
`Re(s) > 1`.
-/
theorem norm_riemannZeta_vertical_le_real {σ t : ℝ} (hσ : 1 < σ) :
    ‖riemannZeta ((σ : ℂ) + t * Complex.I)‖ ≤ ‖riemannZeta (σ : ℂ)‖ := by
  let s : ℂ := (σ : ℂ) + t * Complex.I
  let f : ℕ → ℂ := fun n => 1 / ((n + 1 : ℕ) : ℂ) ^ s
  let g : ℕ → ℝ := fun n => 1 / (((n : ℝ) + 1) ^ σ)
  have hsre : s.re = σ := by
    dsimp only [s]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero]
  have hs : 1 < s.re := by
    rw [hsre]; exact hσ
  have hseries : Summable f := by
    dsimp only [f]
    have h := Complex.summable_one_div_nat_cpow.mpr hs
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 h
  have hterm : ∀ n, ‖f n‖ = g n := by
    intro n
    dsimp only [f, g]
    rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos (Nat.succ_pos n)]
    rw [hsre, Nat.cast_succ]
  have hnormsum : Summable (fun n => ‖f n‖) := summable_norm_iff.mpr hseries
  have hgsum : Summable g := by
    apply hnormsum.congr
    intro n
    exact hterm n
  have hzetas : riemannZeta s = ∑' n, f n := by
    simpa only [f, Nat.cast_add, Nat.cast_one] using zeta_eq_tsum_one_div_nat_add_one_cpow hs
  have hreal : riemannZeta (σ : ℂ) = Complex.ofReal (∑' n, g n) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (s := (σ : ℂ)) hσ]
    calc
      (∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ (σ : ℂ)) = ∑' n, (g n : ℂ) := by
        apply tsum_congr
        intro n
        dsimp only [g]
        have hbase : (n : ℂ) + 1 = (((n : ℝ) + 1) : ℂ) := by rfl
        have hpow : (((n : ℝ) + 1) : ℂ) ^ (σ : ℂ) = Complex.ofReal (((n : ℝ) + 1) ^ σ) := by
          rw [← Complex.ofReal_one, ← Complex.ofReal_add,
            Complex.ofReal_cpow (by positivity : 0 ≤ (n : ℝ) + 1)]
        rw [hbase, hpow, Complex.ofReal_div, Complex.ofReal_one]
      _ = Complex.ofReal (∑' n, g n) := (Complex.ofReal_tsum g).symm
  have hgNonneg : 0 ≤ ∑' n, g n :=
    tsum_nonneg
      (fun n => by
        dsimp only [g]
        positivity)
  have hrealnorm : ‖riemannZeta (σ : ℂ)‖ = ∑' n, g n := by
    rw [hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgNonneg]
  calc
    ‖riemannZeta s‖ = ‖∑' n, f n‖ := by rw [hzetas]
    _ ≤ ∑' n, ‖f n‖ := norm_tsum_le_tsum_norm hnormsum
    _ = ∑' n, g n := tsum_congr hterm
    _ = ‖riemannZeta (σ : ℂ)‖ := hrealnorm.symm

/--
Inputs: a positive modulus `N` and a complex argument with real part greater than one.
Claim: the norm of the principal-character L-function is at most `N` times the norm of ζ.
Proof: use the finite Euler-factor formula, bound each factor by two, and bound their product
by `2 ^ ω(N) ≤ N`.
Role: gives a conductor-dependent majorant for principal factors in the three-L-function
product used to bound nonprincipal L-values.
-/
theorem norm_LFunctionTrivChar_le_level_mul_zeta {N : ℕ} [NeZero N] {s : ℂ} (hs : 1 < s.re) :
    ‖DirichletCharacter.LFunctionTrivChar N s‖ ≤ (N : ℝ) * ‖riemannZeta s‖ := by
  have hsne : s ≠ 1 := by
    intro heq
    rw [heq, Complex.one_re] at hs
    norm_num only at hs
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hsne, norm_mul]
  have hfac : ‖∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ (N : ℝ) := by
    calc
      ‖∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ ∏ p ∈ N.primeFactors, ‖1 - (p : ℂ) ^ (-s)‖ :=
        Finset.norm_prod_le _ _
      _ ≤ ∏ p ∈ N.primeFactors, (2 : ℝ) :=
        Finset.prod_le_prod₀ (fun p hp => norm_nonneg _)
          (by
            intro p hp
            have hprime := Nat.mem_primeFactors.mp hp
            have hpcast : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.1.one_le
            have hpow : (p : ℝ) ^ (-s.re) ≤ 1 :=
              Real.rpow_le_one_of_one_le_of_nonpos hpcast (by linarith only [hs])
            have hnorm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
              rw [Complex.norm_natCast_cpow_of_pos hprime.1.pos]
              simp only [Complex.neg_re]
            calc
              ‖1 - (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
              _ = 1 + ‖(p : ℂ) ^ (-s)‖ := by simp only [norm_one]
              _ ≤ 1 + 1 :=
                add_le_add (le_of_eq rfl)
                  (by
                    rw [hnorm]; exact hpow)
              _ = 2 := by norm_num only)
      _ = (2 : ℝ) ^ N.primeFactors.card := by simp only [Finset.prod_const]
      _ ≤ (N : ℝ) := by
        exact_mod_cast
          PseudoPrime.AnalyticNumberTheory.DirichletLFunction.two_pow_card_primeFactors_le
            (Nat.pos_of_ne_zero (NeZero.ne N))
  exact mul_le_mul_of_nonneg_right hfac (norm_nonneg (riemannZeta s))

/--
Inputs: a positive modulus and a sufficiently small positive real `x`.
Claim: the principal-character L-value at `1+x` is at most `N (C+1)/x` for fixed `C`.
Proof: combine the Euler-factor bound with the local pole estimate for ζ.
Role: supplies the horizontal principal factor in the three-L-function product estimate.
-/
theorem exists_norm_LFunctionTrivChar_one_add_bound {N : ℕ} [NeZero N] :
    ∃ C ε : ℝ,
      0 ≤ C ∧
        0 < ε ∧
        ε ≤ 1 ∧
        ∀ x : ℝ,
          0 < x →
            x < ε →
            ‖DirichletCharacter.LFunctionTrivChar N (1 + (x : ℂ))‖ ≤ (N : ℝ) * ((C + 1) / x) := by
  obtain ⟨C, ε, hC, hε, hεle, hζ⟩ := exists_riemannZeta_one_add_bound
  refine ⟨C, ε, hC, hε, hεle, ?_⟩
  intro x hx hxε
  have hupper :=
    norm_LFunctionTrivChar_le_level_mul_zeta (N := N) (s := 1 + (x : ℂ))
      (by simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, lt_add_iff_pos_right, hx])
  exact le_trans hupper (mul_le_mul_of_nonneg_left (hζ x hx hxε) (Nat.cast_nonneg N))

/--
Inputs: a positive modulus, a sufficiently small positive `x`, and any height `t`.
Claim: the principal-character L-value at `1+x+it` is at most `N(C+1)/x` uniformly in `t`.
Proof: bound its finite Euler factors by `N`, compare ζ at height `t` with ζ on the real axis,
and apply the local pole estimate.
Role: controls both principal factors in the three-L-function product independently of height.
-/
theorem exists_norm_LFunctionTrivChar_one_add_vertical_bound {N : ℕ} [NeZero N] :
    ∃ C ε : ℝ,
      0 ≤ C ∧
        0 < ε ∧
        ε ≤ 1 ∧
        ∀ x t : ℝ,
          0 < x →
            x < ε →
            ‖DirichletCharacter.LFunctionTrivChar N (1 + (x : ℂ) + t * Complex.I)‖ ≤
              (N : ℝ) * ((C + 1) / x) := by
  obtain ⟨C, ε, hC, hε, hεle, hzeta_bound⟩ := exists_riemannZeta_one_add_bound
  refine ⟨C, ε, hC, hε, hεle, ?_⟩
  intro x t hx hxε
  have hzeta := norm_riemannZeta_vertical_le_real (σ := 1 + x) (t := t) (by linarith only [hx])
  have hprincipal :=
    norm_LFunctionTrivChar_le_level_mul_zeta (N := N) (s := 1 + (x : ℂ) + t * Complex.I)
      (by
        simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, Complex.ofReal_im, zero_mul, sub_self, mul_zero, add_zero,
          lt_add_iff_pos_right, hx])
  have hzeta' : ‖riemannZeta (1 + (x : ℂ) + t * Complex.I)‖ ≤ ‖riemannZeta ((1 + x : ℝ) : ℂ)‖ := by
    simpa only [Complex.ofReal_add, Complex.ofReal_one] using hzeta
  have hzeta_real : ‖riemannZeta ((1 + x : ℝ) : ℂ)‖ ≤ (C + 1) / x := by
    simpa only [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_ofNat] using
      hzeta_bound x hx hxε
  calc
    ‖DirichletCharacter.LFunctionTrivChar N (1 + (x : ℂ) + t * Complex.I)‖ ≤
        (N : ℝ) * ‖riemannZeta (1 + (x : ℂ) + t * Complex.I)‖ :=
      hprincipal
    _ ≤ (N : ℝ) * ‖riemannZeta ((1 + x : ℝ) : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hzeta' (Nat.cast_nonneg N)
    _ ≤ (N : ℝ) * ((C + 1) / x) := mul_le_mul_of_nonneg_left hzeta_real (Nat.cast_nonneg N)

/--
Inputs: a Dirichlet character and a complex argument whose real part exceeds one.
Claim: the L-value is bounded by the zeta value at the same real part, uniformly in height.
Proof: compare the absolutely convergent Dirichlet series termwise with the positive real series.
Role: bounds the final factor in the three-L-function product near the line `re s = 1`.
-/
theorem norm_LFunction_le_riemannZeta_real {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {σ t : ℝ}
    (hσ : 1 < σ) :
    ‖DirichletCharacter.LFunction χ ((σ : ℂ) + t * Complex.I)‖ ≤ ‖riemannZeta (σ : ℂ)‖ := by
  let s : ℂ := (σ : ℂ) + t * Complex.I
  let f : ℕ → ℂ := fun n => (χ n : ℂ)
  let g : ℕ → ℝ := fun n => if n = 0 then 0 else 1 / (n : ℝ) ^ σ
  have hsre : s.re = σ := by
    dsimp only [s]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero]
  have hs : 1 < s.re := by
    rw [hsre]; exact hσ
  have hσc : (σ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans (by norm_num only : (0 : ℝ) < 1) hσ))
  have hseries : LSeriesSummable f s := by
    dsimp only [f]
    exact DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  have hnormsum : Summable (fun n => ‖LSeries.term f s n‖) := summable_norm_iff.mpr hseries
  have hg : Summable g := by
    have h' : Summable (fun n : ℕ => 1 / (n : ℝ) ^ σ) := Real.summable_one_div_nat_rpow.mpr hσ
    exact
      h'.congr fun n => by
        by_cases hn : n = 0
        · subst n
          dsimp only [g]
          rw [ite_eq_left rfl]
          rw [Nat.cast_zero]
          rw [Real.zero_rpow (ne_of_gt (by linarith only [hσ])), div_zero]
        · change 1 / (n : ℝ) ^ σ = if n = 0 then 0 else 1 / (n : ℝ) ^ σ
          rw [ite_eq_right hn]
  have hterm : ∀ n, ‖LSeries.term f s n‖ ≤ g n := by
    intro n
    by_cases hn : n = 0
    · subst n
      rw [LSeries.term_def, ite_eq_left rfl]
      dsimp only [g]
      rw [ite_eq_left rfl]
      rw [norm_zero]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      rw [LSeries.term_of_ne_zero hn f s]
      dsimp only [g]
      rw [ite_eq_right hn]
      rw [norm_div, Complex.norm_natCast_cpow_of_pos hnpos, hsre]
      have hden : 0 ≤ (n : ℝ) ^ σ := le_of_lt (Real.rpow_pos_of_pos (by exact_mod_cast hnpos) σ)
      exact (div_le_div_of_nonneg_right (χ.norm_le_one (n : ZMod N)) hden)
  have hsum : (∑' n, ‖LSeries.term f s n‖) ≤ ∑' n, g n := hnormsum.tsum_le_tsum hterm hg
  have hL : ‖DirichletCharacter.LFunction χ s‖ ≤ ∑' n, ‖LSeries.term f s n‖ := by
    rw [show DirichletCharacter.LFunction χ s = LSeries f s by
        simpa only [f] using (DirichletCharacter.LFunction_eq_LSeries χ hs)]
    exact norm_tsum_le_tsum_norm hnormsum
  have hζ : riemannZeta (σ : ℂ) = ∑' n : ℕ, 1 / (n : ℂ) ^ (σ : ℂ) :=
    zeta_eq_tsum_one_div_nat_cpow (by simpa only [Complex.ofReal_re] using hσ)
  have hζreal : ‖riemannZeta (σ : ℂ)‖ = ∑' n, g n := by
    rw [hζ]
    have hcomplex : (∑' n : ℕ, 1 / (n : ℂ) ^ (σ : ℂ)) = Complex.ofReal (∑' n, g n) := by
      calc
        (∑' n : ℕ, 1 / (n : ℂ) ^ (σ : ℂ)) = ∑' n, (g n : ℂ) := by
          apply tsum_congr
          intro n
          by_cases hn : n = 0
          · subst n
            dsimp only [g]
            rw [ite_eq_left rfl, Nat.cast_zero, Complex.zero_cpow hσc, div_zero]
            rfl
          · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
            have hnposR : 0 < (n : ℝ) := by exact_mod_cast hnpos
            simp only [g, ite_eq_right hn]
            have hpow : (((n : ℝ) : ℂ) ^ (σ : ℂ)) = Complex.ofReal ((n : ℝ) ^ σ) := by
              rw [← Complex.ofReal_cpow (le_of_lt hnposR) σ]
            rw [show (n : ℂ) = ((n : ℝ) : ℂ) by rfl, hpow, Complex.ofReal_div, Complex.ofReal_one]
        _ = Complex.ofReal (∑' n, g n) := (Complex.ofReal_tsum g).symm
    rw [hcomplex, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg
        (tsum_nonneg fun n => by
          dsimp only [g]
          by_cases hn : n = 0
          · rw [ite_eq_left hn]
          · rw [ite_eq_right hn]
            exact
              le_of_lt
                (one_div_pos.mpr
                  (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) σ)))]
  calc
    ‖DirichletCharacter.LFunction χ ((σ : ℂ) + t * Complex.I)‖ =
        ‖DirichletCharacter.LFunction χ s‖ :=
      rfl
    _ ≤ ∑' n, ‖LSeries.term f s n‖ := hL
    _ ≤ ∑' n, g n := hsum
    _ = ‖riemannZeta (σ : ℂ)‖ := hζreal.symm

/--
Inputs: a Dirichlet character, a positive offset from one, and any height.
Claim: the L-value is bounded below by `x / (2 N C)`, uniformly in the height.
Proof: apply the three-L-function product inequality and bound both other factors by the local
zeta estimate and absolute convergence.
Role: supplies a height-uniform center-value lower bound for local zero counting.
-/
theorem exists_norm_LFunction_lower_bound_one_add {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ∃ C ε : ℝ,
      0 < C ∧
        0 < ε ∧
        ε ≤ 1 ∧
        ∀ x y : ℝ,
          0 < x →
            x < ε →
            x / (2 * (N : ℝ) * C) ≤
              ‖DirichletCharacter.LFunction χ (1 + (x : ℂ) + Complex.I * y)‖ := by
  obtain ⟨C₀, ε₀, hC₀, hε₀, hε₀le, hζ⟩ := exists_riemannZeta_one_add_bound
  let C : ℝ := C₀ + 1
  refine ⟨C, ε₀ / 2, ?_, ?_, ?_, ?_⟩
  · dsimp only [C]
    linarith only [hC₀]
  · linarith only [hε₀]
  · linarith only [hε₀le]
  · intro x y hx hxε
    have hxε₀ : x < ε₀ := by linarith only [hxε, hε₀]
    have hζx : ‖riemannZeta (1 + (x : ℂ))‖ ≤ C / x := by simpa only [C] using hζ x hx hxε₀
    let A : ℝ := ‖DirichletCharacter.LFunctionTrivChar N (1 + (x : ℂ))‖
    let B : ℝ := ‖DirichletCharacter.LFunction χ (1 + (x : ℂ) + Complex.I * y)‖
    let D : ℝ := ‖DirichletCharacter.LFunction (χ ^ 2) (1 + (x : ℂ) + 2 * Complex.I * y)‖
    have hprincipal :=
      norm_LFunctionTrivChar_le_level_mul_zeta (N := N) (s := 1 + (x : ℂ))
        (by simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, lt_add_iff_pos_right, hx])
    have hA : A ≤ (N : ℝ) * (C / x) := by
      dsimp only [A]
      calc
        ‖DirichletCharacter.LFunctionTrivChar N (1 + (x : ℂ))‖ ≤
            (N : ℝ) * ‖riemannZeta (1 + (x : ℂ))‖ :=
          hprincipal
        _ ≤ (N : ℝ) * (C / x) := mul_le_mul_of_nonneg_left hζx (Nat.cast_nonneg N)
    have hthird :=
      norm_LFunction_le_riemannZeta_real (χ := χ ^ 2) (σ := 1 + x) (t := 2 * y)
        (by linarith only [hx])
    have hD : D ≤ C / x := by
      dsimp only [D]
      have harg : ((1 + x : ℝ) : ℂ) + (2 * y) * Complex.I = 1 + (x : ℂ) + 2 * Complex.I * y := by
        push_cast
        ring_nf
      have hthird' :
        ‖DirichletCharacter.LFunction (χ ^ 2) (((1 + x : ℝ) : ℂ) + (2 * y) * Complex.I)‖ ≤
          ‖riemannZeta (1 + (x : ℂ))‖ := by
        simpa only [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul,
          Complex.ofReal_ofNat] using hthird
      rw [← harg]
      exact le_trans hthird' hζx
    have hB : 0 ≤ B := norm_nonneg _
    have hA0 : 0 ≤ A := norm_nonneg _
    have hD0 : 0 ≤ D := norm_nonneg _
    have hProd := DirichletCharacter.norm_LFunction_product_ge_one (χ := χ) (x := x) hx y
    have hproduct : 1 ≤ A ^ 3 * B ^ 4 * D := by
      norm_num only [Complex.norm_mul, norm_pow] at hProd
      simpa only [A, B, D] using hProd
    have hN : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have hK : 0 < C := by
      dsimp only [C]; linarith only [hC₀]
    have hthreshold : 0 < x / (2 * (N : ℝ) * C) :=
      div_pos hx (mul_pos (mul_pos (by norm_num only) hN) hK)
    by_contra hnot
    have hBlt : B < x / (2 * (N : ℝ) * C) := lt_of_not_ge hnot
    have hA3 : A ^ 3 ≤ ((N : ℝ) * (C / x)) ^ 3 := pow_le_pow_left₀ hA0 hA 3
    have hB4 : B ^ 4 < (x / (2 * (N : ℝ) * C)) ^ 4 := by
      exact pow_lt_pow_left₀ hBlt hB (by norm_num only)
    have hAB : A ^ 3 * B ^ 4 ≤ ((N : ℝ) * (C / x)) ^ 3 * (x / (2 * (N : ℝ) * C)) ^ 4 :=
      mul_le_mul hA3 (le_of_lt hB4) (pow_nonneg hB 4)
        (pow_nonneg (mul_nonneg (le_of_lt hN) (le_of_lt (div_pos hK hx))) 3)
    have hABmax : 0 ≤ ((N : ℝ) * (C / x)) ^ 3 * (x / (2 * (N : ℝ) * C)) ^ 4 :=
      mul_nonneg (pow_nonneg (mul_nonneg (le_of_lt hN) (le_of_lt (div_pos hK hx))) 3)
        (pow_nonneg (le_of_lt hthreshold) 4)
    have hupper :
      A ^ 3 * B ^ 4 * D ≤ ((N : ℝ) * (C / x)) ^ 3 * (x / (2 * (N : ℝ) * C)) ^ 4 * (C / x) :=
      mul_le_mul hAB hD hD0 hABmax
    have hbound :
      ((N : ℝ) * (C / x)) ^ 3 * (x / (2 * (N : ℝ) * C)) ^ 4 * (C / x) = 1 / (16 * (N : ℝ)) := by
      field_simp [ne_of_gt hN, ne_of_gt hK, ne_of_gt hx]; ring
    have hNone : 1 / (16 * (N : ℝ)) ≤ 1 / 16 := by
      apply (div_le_div_iff₀ (mul_pos (by norm_num only) hN) (by norm_num only)).2
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
      nlinarith only [hN1]
    have hsmall : A ^ 3 * B ^ 4 * D ≤ 1 / 16 := by
      rw [hbound] at hupper
      exact le_trans hupper hNone
    nlinarith only [hproduct, hsmall]

/--
Inputs: the reciprocal-square series over the natural numbers.
Claim: Its sum is at most `2`.
Proof: Separate the zeroth term and bound the rest using the integral estimate
`sum_Ioo_inv_sq_le`.
Role: gives a uniform bound for Dirichlet series at real part `2`.
-/
private theorem tsum_inv_sq_le_two : (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) ≤ 2 := by
  apply Real.tsum_le_of_sum_range_le (fun n => by positivity)
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [Finset.range_zero, Finset.sum_empty]
    norm_num only
  · have hset : Finset.range n = insert 0 (Finset.Ioo 0 n) := by
      ext i
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
      omega
    have h0 : 0 ∉ Finset.Ioo 0 n := by
      intro hi
      exact Nat.lt_irrefl 0 (Finset.mem_Ioo.mp hi).1
    rw [hset, Finset.sum_insert h0]
    norm_num only [Nat.cast_zero, zero_pow, div_zero, one_div]
    simpa only [one_div, Nat.cast_zero, zero_add, div_one] using (sum_Ioo_inv_sq_le (α := ℝ) 0 n)

/--
Inputs: a Dirichlet character `χ` and a complex number `s` with real part `2`.
Claim: `‖L(s, χ)‖ ≤ 2`, uniformly in the character and imaginary part.
Proof: Bound the absolutely convergent Dirichlet series termwise by the reciprocal-square series
and use its sum bound.
Role: makes the polynomial growth constant on the circle uniform for the local Jensen estimate.
-/
theorem norm_LFunction_le_two_at_two {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : s.re = 2) : ‖DirichletCharacter.LFunction χ s‖ ≤ 2 := by
  let f : ℕ → ℂ := fun n => (χ n : ℂ)
  have hRe : 1 < s.re := by
    rw [hs]; norm_num only
  have hseries : LSeriesSummable f s := by
    simpa only [f] using (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hRe)
  have hnorm : Summable (fun n : ℕ => ‖LSeries.term f s n‖) := summable_norm_iff.mpr hseries
  have hpow : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num only)
  have hterm : ∀ n, ‖LSeries.term f s n‖ ≤ (1 : ℝ) / (n : ℝ) ^ 2 := by
    intro n
    by_cases hn : n = 0
    · subst n
      rw [LSeries.term_def, ite_eq_left rfl, norm_zero]
      norm_num only
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      rw [LSeries.term_of_ne_zero hn f s]
      rw [norm_div, Complex.norm_natCast_cpow_of_pos hnpos, hs, Real.rpow_two]
      have hχ := χ.norm_le_one (n : ZMod N)
      have hden : 0 < (n : ℝ) ^ 2 := pow_pos (by exact_mod_cast hnpos) 2
      apply (div_le_div_iff_of_pos_right hden).2
      exact hχ
  have hsumBound : (∑' n : ℕ, ‖LSeries.term f s n‖) ≤ ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 :=
    hnorm.tsum_le_tsum hterm hpow
  have hnormL : ‖LSeries f s‖ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hnorm
  calc
    ‖DirichletCharacter.LFunction χ s‖ = ‖LSeries f s‖ := by
      congr 1
      simpa only [f] using (DirichletCharacter.LFunction_eq_LSeries χ hRe)
    _ ≤ _ := hnormL
    _ ≤ _ := hsumBound
    _ ≤ 2 := tsum_inv_sq_le_two

/--
Inputs: a Dirichlet character `χ` and any height `y`.
Claim: On the line with real part `2`, `‖L(2 + iy, χ)‖ ≥ 1/2` uniformly.
Proof: Use the lower bound from the three-factor product for Dirichlet `L` functions and bound
the other two factors at real part `2`.
Role: supplies a denominator independent of the center value in the local Jensen estimate.
-/
theorem norm_LFunction_lower_bound_at_two {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) :
    (1 / 2 : ℝ) ≤ ‖DirichletCharacter.LFunction χ (2 + Complex.I * y)‖ := by
  let z : ℂ := 2 + Complex.I * y
  let w : ℂ := 2 + 2 * Complex.I * y
  have hz : z.re = 2 := by
    simp only [z, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.re_ofNat, zero_mul, mul_zero, sub_zero, add_zero]
  have hw : w.re = 2 := by
    simp only [w, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, mul_zero, sub_zero, add_zero]
  have hA0 :=
    norm_LFunction_le_two_at_two (N := N) (1 : DirichletCharacter ℂ N) (s := (2 : ℂ))
      (Complex.re_ofNat 2)
  have hC0 := norm_LFunction_le_two_at_two (χ := χ ^ 2) (s := w) hw
  let A := ‖DirichletCharacter.LFunctionTrivChar N (2 : ℂ)‖
  let B := ‖DirichletCharacter.LFunction χ z‖
  let C := ‖DirichletCharacter.LFunction (χ ^ 2) w‖
  have hProd :=
    DirichletCharacter.norm_LFunction_product_ge_one (χ := χ) (x := 1) (by norm_num only) y
  have hprod : 1 ≤ A ^ 3 * B ^ 4 * C := by
    norm_num only [DirichletCharacter.LFunctionTrivChar, Complex.ofReal_one, Complex.norm_mul,
      Complex.norm_pow] at hProd
    simpa only [A, B, C] using hProd
  have hA : A ≤ 2 := by simpa only [A, DirichletCharacter.LFunctionTrivChar] using hA0
  have hC : C ≤ 2 := by simpa only [C, w] using hC0
  have hB : 0 ≤ B := norm_nonneg _
  have hupper : A ^ 3 * B ^ 4 * C ≤ 16 * B ^ 4 := by
    calc
      A ^ 3 * B ^ 4 * C ≤ 2 ^ 3 * B ^ 4 * 2 := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_right
          · exact pow_le_pow_left₀ (norm_nonneg _) hA 3
          · positivity
        · exact hC
        · positivity
        · positivity
      _ = 16 * B ^ 4 := by ring
  have hB2 : (1 / 2 : ℝ) ^ 2 ≤ B ^ 2 := by
    by_contra hn
    have hlt : B ^ 2 < (1 / 2 : ℝ) ^ 2 := lt_of_not_ge hn
    have hfour' := (sq_lt_sq₀ (sq_nonneg B) (sq_nonneg (1 / 2 : ℝ))).2 hlt
    have hfour : B ^ 4 < (1 / 2 : ℝ) ^ 4 := by nlinarith only [hfour']
    nlinarith only [hprod, hupper, hfour]
  have hresult : (1 / 2 : ℝ) ≤ B := (sq_le_sq₀ (by norm_num only) hB).1 hB2
  simpa only [B, z] using hresult

/--
Inputs: a meromorphic function on a circle, a real bound `M ≥ 1` for its norm there, and the
corresponding pointwise norm estimate.

Claim: the circle average of the logarithm of the norm is at most `log M`.

Proof: meromorphicity gives integrability of the logarithm of the norm. Bound the integrand on the
circle, handling zeros separately because `Real.log 0` is defined as zero in Lean.

Role: supplies the boundary maximum estimate used with Jensen's formula in local zero counts.
-/
theorem circleAverage_log_norm_le_log_of_bound {c : ℂ} {R M : ℝ} {f : ℂ → ℂ} (hM : 1 ≤ M)
    (hmero : MeromorphicOn f (Metric.sphere c |R|))
    (hbound : ∀ z ∈ Metric.sphere c |R|, ‖f z‖ ≤ M) :
    Real.circleAverage (fun z => Real.log ‖f z‖) c R ≤ Real.log M := by
  have hInt : CircleIntegrable (fun z => Real.log ‖f z‖) c R := hmero.circleIntegrable_log_norm
  have hpoint : ∀ z ∈ Metric.sphere c |R|, Real.log ‖f z‖ ≤ Real.log M := by
    intro z hz
    by_cases hf : f z = 0
    · rw [hf, norm_zero, Real.log_zero]
      exact Real.log_nonneg hM
    · exact Real.log_le_log (norm_pos_iff.mpr hf) (hbound z hz)
  exact Real.circleAverage_mono_on_of_le_circle hInt hpoint

/--
Inputs: a nontrivial Dirichlet character, nested disks centered at `c`, a nonzero value at the
center, and a norm bound on the larger boundary circle.

Claim: the total divisor multiplicity of the completed Dirichlet `L`-function in the smaller disk
is bounded by Jensen's logarithmic ratio.

Proof: the completed `L`-function is analytic on the larger disk; apply Mathlib's Jensen
inequality
for analytic functions.

Role: converts a future uniform boundary estimate for completed `L`-functions into the local zero
counts required by log-free density.
-/
theorem completedLFunction_local_zero_count_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {c : ℂ} {r R M : ℝ} (hr : 0 < |r|) (hrR : |r| < |R|) (hM : 1 ≤ M)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0)
    (hbound : ∀ z ∈ Metric.sphere c |R|, ‖DirichletCharacter.completedLFunction χ z‖ ≤ M) :
    (Int.cast
          (∑ᶠ u : ℂ,
            MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall c |r|) u) :
        ℝ) ≤
      Real.log (M / ‖DirichletCharacter.completedLFunction χ c‖) / Real.log (R / r) := by
  have hanalytic :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.closedBall c |R|) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  exact hanalytic.sum_divisor_le hr hrR hM hc hbound

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/--
Inputs: a primitive nontrivial character whose inverse is also nontrivial, a nonzero center
value, and inner and outer radii.
Claim: Bound the number of zeros, counted with analytic multiplicity, of the completed `L`
function in a small disk around `c` by an explicit growth envelope centered at the origin.
Proof: Enclose the outer circle in the closed disk centered at the origin with radius `|c|+|R|`,
then apply the uniform completed-function bound in Jensen's estimate.
Role: makes the abstract local zero-count bound explicit in terms of the conductor and disk
location and size.
-/
theorem completedLFunction_local_zero_count_le_ball_bound {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hprimitive : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) {c : ℂ} {r R : ℝ} (hr : 0 < |r|) (hrR : |r| < |R|)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0) :
    (Int.cast
          (∑ᶠ u : ℂ,
            MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall c |r|) u) :
        ℝ) ≤
      Real.log
          (max (1 : ℝ)
              (PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedLFunctionBallBound q
                (‖c‖ + |R|)) /
            ‖DirichletCharacter.completedLFunction χ c‖) /
        Real.log (R / r) := by
  let F : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  let B : ℝ :=
    PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedLFunctionBallBound q (‖c‖ + |R|)
  have hboundary : ∀ z ∈ Metric.sphere c |R|, ‖F z‖ ≤ max (1 : ℝ) B := by
    intro z hz
    have hzdist : dist z c = |R| := Metric.mem_sphere.mp hz
    have hznorm : ‖z‖ ≤ ‖c‖ + |R| := by
      rw [dist_eq_norm] at hzdist
      calc
        ‖z‖ = ‖(z - c) + c‖ := by
          congr 1; abel
        _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
        _ = ‖c‖ + |R| := by
          rw [← hzdist]; ring
    have hq1 : 1 < q := by omega
    have hball :=
      norm_completedLFunction_le_completedLFunctionBallBound hq1 hprimitive hχ hinv
        (add_nonneg (norm_nonneg c) (abs_nonneg R)) (z := z) (R := ‖c‖ + |R|) hznorm
    exact hball.trans (le_max_right (1 : ℝ) B)
  have hcount :=
    completedLFunction_local_zero_count_le χ hχ hr hrR (M := max (1 : ℝ) B) (le_max_left 1 B) hc
      (by
        intro z hz
        exact hboundary z hz)
  simpa only [F, B] using hcount

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/--
Inputs: a nontrivial character, a nonzero central value of the `L` function, and real part at
least `1/2` on the outer circle.
Claim: Bound the zeros of the `L` function in the inner disk, counted with analytic
multiplicity, by polynomial growth in the conductor, center, and radius.
Proof: Evaluate the bound `|L(s,χ)| ≤ 2q|s|` from Abel summation on the outer circle and apply
Jensen's zero-count inequality.
Role: gives a logarithmic local zero-count estimate in the right half of the critical strip
without an exponential-type envelope for the completed function.
-/
theorem LFunction_local_zero_count_le_polynomial_bound {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 1 < q) (hχ : χ ≠ 1) {c : ℂ} {r R : ℝ} (hr : 0 < |r|)
    (hrR : |r| < |R|) (hc : DirichletCharacter.LFunction χ c ≠ 0)
    (hcircle : ∀ z ∈ Metric.sphere c |R|, 1 / 2 ≤ z.re) :
    (Int.cast
          (∑ᶠ u : ℂ,
            MeromorphicOn.divisor (DirichletCharacter.LFunction χ) (Metric.closedBall c |r|) u) :
        ℝ) ≤
      Real.log (max (1 : ℝ) (2 * (q : ℝ) * (‖c‖ + |R|)) / ‖DirichletCharacter.LFunction χ c‖) /
        Real.log (R / r) := by
  let F : ℂ → ℂ := DirichletCharacter.LFunction χ
  let B : ℝ := 2 * (q : ℝ) * (‖c‖ + |R|)
  have hboundary : ∀ z ∈ Metric.sphere c |R|, ‖F z‖ ≤ max (1 : ℝ) B := by
    intro z hz
    have hzdist : dist z c = |R| := Metric.mem_sphere.mp hz
    have hznorm : ‖z‖ ≤ ‖c‖ + |R| := by
      rw [dist_eq_norm] at hzdist
      calc
        ‖z‖ = ‖(z - c) + c‖ := by
          congr 1; abel
        _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
        _ = ‖c‖ + |R| := by
          rw [← hzdist]; ring
    have hbound := norm_lFunction_le_two_mul hq hχ (hcircle z hz)
    have hbound' : ‖F z‖ ≤ B := by
      change ‖DirichletCharacter.LFunction χ z‖ ≤ B
      calc
        _ ≤ 2 * (q : ℝ) * ‖z‖ := hbound
        _ ≤ B := mul_le_mul_of_nonneg_left hznorm (by positivity)
    exact hbound'.trans (le_max_right (1 : ℝ) B)
  have hdiff : AnalyticOnNhd ℂ F (Metric.closedBall c |R|) := by
    intro z hz
    exact (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hcount :=
    hdiff.sum_divisor_le hr hrR (M := max (1 : ℝ) B) (le_max_left (1 : ℝ) B) hc
      (by
        intro z hz
        exact hboundary z hz)
  simpa only [F, B] using hcount

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/--
Inputs: a nontrivial character, a nonzero central value of the `L` function, and real part at
least `1/2` on the outer circle.
Claim: Bound the number of zeros of the completed `L` function in the inner disk by a
logarithmic estimate based on polynomial growth of the ordinary `L` function.
Proof: Use the outer-circle real-part condition to show that the inner disk lies in the positive
half-plane, and use equality of the analytic orders of the two functions.
Role: connects a local zero-count estimate in the right half-plane to the completed-function
zero-count interface.
-/
theorem completedLFunction_local_zero_count_le_LFunction_polynomial_bound {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 1 < q) (hχ : χ ≠ 1) {c : ℂ} {r R : ℝ} (hr : 0 < |r|)
    (hrR : |r| < |R|) (hc : DirichletCharacter.LFunction χ c ≠ 0)
    (hcircle : ∀ z ∈ Metric.sphere c |R|, 1 / 2 ≤ z.re) :
    (Int.cast
          (∑ᶠ u : ℂ,
            MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall c |r|) u) :
        ℝ) ≤
      Real.log (max (1 : ℝ) (2 * (q : ℝ) * (‖c‖ + |R|)) / ‖DirichletCharacter.LFunction χ c‖) /
        Real.log (R / r) := by
  let U := Metric.closedBall c |r|
  let Fc : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  let Fl : ℂ → ℂ := DirichletCharacter.LFunction χ
  have hFc : AnalyticOnNhd ℂ Fc U := by
    intro z hz
    exact (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have hFl : AnalyticOnNhd ℂ Fl U := by
    intro z hz
    exact (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hinner : ∀ u ∈ U, 0 < u.re := by
    intro u hu
    have hleft : 1 / 2 + |R| ≤ c.re := by
      have hv : c - ((|R| : ℝ) : ℂ) ∈ Metric.sphere c |R| := by
        rw [Metric.mem_sphere, dist_eq_norm]
        simp only [sub_sub_cancel_left, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_abs]
      have h := hcircle (c - ((|R| : ℝ) : ℂ)) hv
      rw [Complex.sub_re, Complex.ofReal_re] at h
      linarith only [h]
    have hunorm : ‖u - c‖ ≤ |r| := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hu
      exact hu
    have hReLower : c.re - ‖u - c‖ ≤ u.re := by
      have h := Complex.abs_re_le_norm (u - c)
      rw [Complex.sub_re, abs_le] at h
      linarith only [h.1]
    have hhalf : 1 / 2 ≤ c.re - ‖u - c‖ := by linarith only [hleft, hunorm, hrR.le]
    exact lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1 / 2) (le_trans hhalf hReLower)
  have hdiv (u : ℂ) : MeromorphicOn.divisor Fc U u = MeromorphicOn.divisor Fl U u := by
    by_cases hu : u ∈ U
    · rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hFc hu,
        MeromorphicOn.AnalyticOnNhd.divisor_apply hFl hu]
      exact
        congrArg (fun v : ℕ∞ => (ENat.map (Nat.cast : ℕ → ℤ) v).untop₀)
          (completedLFunction_analyticOrderAt_eq_LFunction_of_re_pos χ hχ (hinner u hu))
    · rw [(MeromorphicOn.divisor Fc U).apply_eq_zero_of_notMem hu,
        (MeromorphicOn.divisor Fl U).apply_eq_zero_of_notMem hu]
  have hsum :
    (∑ᶠ u : ℂ, MeromorphicOn.divisor Fc U u) = ∑ᶠ u : ℂ, MeromorphicOn.divisor Fl U u := by
    apply finsum_congr
    intro u
    exact hdiv u
  have hcount := LFunction_local_zero_count_le_polynomial_bound hq hχ hr hrR hc hcircle
  change (Int.cast (∑ᶠ u : ℂ, MeromorphicOn.divisor Fc U u) : ℝ) ≤ _
  rw [hsum]
  exact hcount

/--
Inputs: a nontrivial Dirichlet character, a lower bound on its modulus, and any height `y`.
Claim: Bound the sum of zero multiplicities of the completed `L` function in the unit disk
centered at `2+iy` by logarithms of the conductor and height.
Proof: Substitute the uniform central-value lower bound and the circle real-part bound into the
local Jensen estimate.
Role: provides a local zero-count bound independent of the central value.
-/
theorem completedLFunction_local_zero_count_at_two_line {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 1 < q) (hχ : χ ≠ 1) (y : ℝ) :
    (Int.cast
          (∑ᶠ u : ℂ,
            MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall (2 + Complex.I * y) 1) u) :
        ℝ) ≤
      Real.log (2 * max (1 : ℝ) (2 * (q : ℝ) * (‖(2 + Complex.I * y : ℂ)‖ + 3 / 2))) /
        Real.log (3 / 2) := by
  let c : ℂ := 2 + Complex.I * y
  have hcenter := norm_LFunction_lower_bound_at_two χ y
  have hcenter' : (1 / 2 : ℝ) ≤ ‖DirichletCharacter.LFunction χ c‖ := by
    simpa only [c] using hcenter
  have hc : DirichletCharacter.LFunction χ c ≠ 0 := by
    intro heq
    have hzero : ‖DirichletCharacter.LFunction χ c‖ = 0 := by rw [heq, norm_zero]
    have hpos : (0 : ℝ) < ‖DirichletCharacter.LFunction χ c‖ :=
      lt_of_lt_of_le (by norm_num only) hcenter'
    rw [hzero] at hpos
    exact (lt_irrefl 0 hpos)
  have hcre : c.re = 2 := by
    simp only [c, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.re_ofNat, zero_mul, mul_zero, sub_zero, add_zero]
  have hcircle : ∀ z ∈ Metric.sphere c |(3 / 2 : ℝ)|, 1 / 2 ≤ z.re := by
    intro z hz
    have hdist : dist z c = (3 / 2 : ℝ) := by
      have h := Metric.mem_sphere.mp hz
      simpa only [abs_of_pos (by norm_num : (0 : ℝ) < (3 / 2 : ℝ))] using h
    have hnorm : ‖z - c‖ = 3 / 2 := by
      rw [← dist_eq_norm]
      exact hdist
    have hreal : |z.re - c.re| ≤ 3 / 2 := by
      rw [← Complex.sub_re]
      calc
        |(z - c).re| ≤ ‖z - c‖ := Complex.abs_re_le_norm (z - c)
        _ = 3 / 2 := hnorm
    have hlow := (abs_le.mp hreal).1
    linarith only [hlow, hcre]
  have hcount :=
    completedLFunction_local_zero_count_le_LFunction_polynomial_bound hq hχ (r := 1) (R := 3 / 2)
      (by norm_num only) (by norm_num only) hc hcircle
  have hcount' :
    (Int.cast
          (∑ᶠ u : ℂ,
            MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall c 1)
              u) :
        ℝ) ≤
      Real.log (max (1 : ℝ) (2 * (q : ℝ) * (‖c‖ + 3 / 2)) / ‖DirichletCharacter.LFunction χ c‖) /
        Real.log (3 / 2) := by
    rw [abs_of_pos (by norm_num only : (0 : ℝ) < 1)] at hcount
    simpa only [abs_of_pos (by norm_num only : (0 : ℝ) < (3 / 2 : ℝ)), div_one] using hcount
  have hMpos : 0 < max (1 : ℝ) (2 * (q : ℝ) * (‖c‖ + 3 / 2)) :=
    lt_of_lt_of_le (by norm_num only) (le_max_left _ _)
  have hLpos : 0 < ‖DirichletCharacter.LFunction χ c‖ := lt_of_lt_of_le (by norm_num only) hcenter'
  have hratio :
    max (1 : ℝ) (2 * (q : ℝ) * (‖c‖ + 3 / 2)) / ‖DirichletCharacter.LFunction χ c‖ ≤
      2 * max (1 : ℝ) (2 * (q : ℝ) * (‖c‖ + 3 / 2)) := by
    calc
      _ ≤ max (1 : ℝ) (2 * (q : ℝ) * (‖c‖ + 3 / 2)) / (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_left (le_of_lt hMpos) (by norm_num only) hcenter'
      _ = _ := by ring
  have hlog := Real.log_le_log (div_pos hMpos hLpos) hratio
  have hlogDen : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num only)
  calc
    _ ≤ _ := hcount'
    _ ≤ _ := div_le_div_of_nonneg_right hlog hlogDen.le

/--
Inputs: a nontrivial completed Dirichlet `L`-function, a closed rectangle, and a closed disk that
contains the rectangle.
Claim: the multiplicity-weighted rectangle count is bounded by the divisor sum on the disk.
Proof: identify each analytic order with the disk divisor and enlarge the finite zero ledger to
the finite support of that divisor.
Role: connects the public rectangle counting convention to the local Jensen estimates.
-/
theorem completedZeroMultiplicityCountInRectangle_le_ball_divisor_sum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (z w c : ℂ) (R : ℝ)
    (hbox : ∀ ρ ∈ dirichletCompletedLFunctionRectangleBox z w, ρ ∈ Metric.closedBall c R) :
    completedZeroMultiplicityCountInRectangle χ hχ z w ≤
      (Int.cast
          (∑ᶠ u : ℂ,
            MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall c R)
              u) :
        ℝ) := by
  classical
  let F : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  let U : Set ℂ := Metric.closedBall c R
  let D := MeromorphicOn.divisor F U
  let S := completedZerosInRectangle χ hχ z w
  have hf : D.support.Finite := by
    exact (MeromorphicOn.divisor F U).finiteSupport (isCompact_closedBall (x := c) (r := R))
  have ha : AnalyticOnNhd ℂ F U := fun u _ => by
    exact (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt u
  have hn (u : ℂ) : (D u : ℝ) ≥ 0 := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha u
  have hsub : Function.support (fun u : ℂ => (D u : ℝ)) ⊆ (hf.toFinset : Set ℂ) := by
    intro u hu
    change (D u : ℝ) ≠ 0 at hu
    apply hf.mem_toFinset.mpr
    intro hzero
    apply hu
    rw [hzero]
    simp only [Int.cast_zero]
  change (∑ ρ ∈ S, (analyticOrderNatAt F ρ : ℝ)) ≤ (Int.castRingHom ℝ) (∑ᶠ u : ℂ, D u)
  rw [map_finsum (Int.castRingHom ℝ) hf]
  change (∑ ρ ∈ S, (analyticOrderNatAt F ρ : ℝ)) ≤ ∑ᶠ u : ℂ, (D u : ℝ)
  rw [finsum_eq_sum_of_support_subset _ hsub]
  have hpoint : ∀ ρ ∈ S, (analyticOrderNatAt F ρ : ℝ) ≤ (D ρ : ℝ) := by
    intro ρ hρ
    have hρbox := (mem_completedZerosInRectangle_iff.mp hρ).1
    have hρU : ρ ∈ U := hbox ρ hρbox
    have hdiv : D ρ = (analyticOrderNatAt F ρ : ℤ) := by
      rw [show D = MeromorphicOn.divisor F U from rfl,
        MeromorphicOn.AnalyticOnNhd.divisor_apply ha hρU]
      change
        ((analyticOrderAt F ρ).map (fun k : ℕ => (k : ℤ))).untop₀ =
          ((analyticOrderAt F ρ).toNat : ℤ)
      induction analyticOrderAt F ρ using ENat.recTopCoe
      · rfl
      · rfl
    rw [hdiv]
    exact_mod_cast le_rfl
  have hfirst : (∑ ρ ∈ S, (analyticOrderNatAt F ρ : ℝ)) ≤ ∑ ρ ∈ S, (D ρ : ℝ) := by
    apply Finset.sum_le_sum
    intro ρ hρ
    exact hpoint ρ hρ
  have hle : (∑ ρ ∈ S, (D ρ : ℝ)) ≤ ∑ ρ ∈ S ∪ hf.toFinset, (D ρ : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      (by
        intro ρ hρ hρ'; exact hn ρ)
  have he : (∑ ρ ∈ S ∪ hf.toFinset, (D ρ : ℝ)) = ∑ ρ ∈ hf.toFinset, (D ρ : ℝ) := by
    symm
    apply Finset.sum_subset Finset.subset_union_right
    intro ρ _ hρ
    have hzero : D ρ = 0 := by
      by_contra hne
      exact hρ (hf.mem_toFinset.mpr hne)
    rw [hzero, Int.cast_zero]
  exact hfirst.trans (hle.trans_eq he)

/--
Inputs: a nontrivial completed Dirichlet `L`-function, a closed rectangle, and coordinate bounds
placing every point of the rectangle inside a closed disk.
Claim: its multiplicity-weighted zero count is bounded by the disk divisor sum.
Proof: convert the coordinate inequality to closed-ball membership, then apply the finite-ledger
comparison theorem.
Role: gives a real-coordinate interface for covering rectangular zero regions by Jensen disks.
-/
theorem completedZeroMultiplicityCountInRectangle_le_ball_divisor_sum_of_coordinates {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (z w c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcoord :
      ∀ x ∈ Set.uIcc z.re w.re, ∀ y ∈ Set.uIcc z.im w.im, (x - c.re) ^ 2 + (y - c.im) ^ 2 ≤ R ^ 2) :
    completedZeroMultiplicityCountInRectangle χ hχ z w ≤
      (Int.cast
          (∑ᶠ u : ℂ,
            MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall c R)
              u) :
        ℝ) := by
  apply completedZeroMultiplicityCountInRectangle_le_ball_divisor_sum χ hχ z w c R
  intro ρ hρ
  change ρ.re ∈ Set.uIcc z.re w.re ∧ ρ.im ∈ Set.uIcc z.im w.im at hρ
  rw [Metric.mem_closedBall, dist_eq_norm, Complex.norm_eq_sqrt_sq_add_sq, Complex.sub_re,
    Complex.sub_im]
  exact Real.sqrt_le_iff.mpr ⟨hR, hcoord ρ.re hρ.1 ρ.im hρ.2⟩

/--
Inputs: a nontrivial Dirichlet character, a rectangle inside an inner disk, and a nonvanishing
center value with a half-plane bound on the outer circle.
Claim: the completed zero count in the rectangle is at most the explicit Jensen logarithmic bound.
Proof: compare the rectangle count with the inner-disk divisor sum, then apply the polynomial
growth Jensen estimate for the ordinary Dirichlet `L`-function.
Role: combines geometric coverage and local analytic growth in the interface used for height
slabs.
-/
theorem completedZeroMultiplicityCountInRectangle_le_LFunction_Jensen_bound {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 1 < q) (hχ : χ ≠ 1) (z w c : ℂ) {r R : ℝ} (hr : 0 < |r|)
    (hrR : |r| < |R|) (hc : DirichletCharacter.LFunction χ c ≠ 0)
    (hcircle : ∀ z ∈ Metric.sphere c |R|, 1 / 2 ≤ z.re)
    (hcoord :
      ∀ x ∈ Set.uIcc z.re w.re,
        ∀ y ∈ Set.uIcc z.im w.im, (x - c.re) ^ 2 + (y - c.im) ^ 2 ≤ |r| ^ 2) :
    completedZeroMultiplicityCountInRectangle χ hχ z w ≤
      Real.log (max (1 : ℝ) (2 * (q : ℝ) * (‖c‖ + |R|)) / ‖DirichletCharacter.LFunction χ c‖) /
        Real.log (R / r) := by
  calc
    _ ≤
        (Int.cast
            (∑ᶠ u : ℂ,
              MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                (Metric.closedBall c |r|) u) :
          ℝ) :=
      completedZeroMultiplicityCountInRectangle_le_ball_divisor_sum_of_coordinates χ hχ z w c |r|
        (abs_nonneg r) hcoord
    _ ≤ _ :=
      completedLFunction_local_zero_count_le_LFunction_polynomial_bound hq hχ hr hrR hc hcircle

/--
Inputs: a nontrivial Dirichlet character, a height slab with nonnegative half-width, an inner
radius large enough to contain that slab, and the usual Jensen hypotheses at center `2 + I * y`.
Claim: the completed zero count in the slab is bounded by the polynomial-growth Jensen expression.
Proof: bound the squared coordinate distance from the center by the inner radius squared, then use
the rectangle-to-disk Jensen interface.
Role: supplies a uniform local estimate for each short height interval in a zero-density covering.
-/
theorem completedZeroMultiplicityCountInTwoLineSlab_le_Jensen_bound {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 1 < q) (hχ : χ ≠ 1) (sigma y v : ℝ) (hσ : sigma ≤ 1)
    (hv : 0 ≤ v) {r R : ℝ} (hr : 0 < |r|) (hrR : |r| < |R|)
    (hc : DirichletCharacter.LFunction χ (⟨2, y⟩ : ℂ) ≠ 0)
    (hcircle : ∀ z ∈ Metric.sphere (⟨2, y⟩ : ℂ) |R|, 1 / 2 ≤ z.re)
    (hgeom : (2 - sigma) ^ 2 + v ^ 2 ≤ |r| ^ 2) :
    completedZeroMultiplicityCountInRectangle χ hχ (⟨sigma, y - v⟩ : ℂ) (⟨1, y + v⟩ : ℂ) ≤
      Real.log
          (max (1 : ℝ) (2 * (q : ℝ) * (‖(⟨2, y⟩ : ℂ)‖ + |R|)) /
            ‖DirichletCharacter.LFunction χ (⟨2, y⟩ : ℂ)‖) /
        Real.log (R / r) := by
  apply
    completedZeroMultiplicityCountInRectangle_le_LFunction_Jensen_bound hq hχ _ _ (⟨2, y⟩ : ℂ) hr
      hrR hc hcircle
  intro x hx t ht
  have hx' : sigma ≤ x ∧ x ≤ 1 := by simpa only [Set.uIcc_of_le hσ, Set.mem_Icc] using hx
  have horder : y - v ≤ y + v := by linarith only [hv]
  have ht' : y - v ≤ t ∧ t ≤ y + v := by simpa only [Set.uIcc_of_le horder, Set.mem_Icc] using ht
  change (x - 2) ^ 2 + (t - y) ^ 2 ≤ |r| ^ 2
  nlinarith only [hσ, hv, hgeom, hx'.1, hx'.2, ht'.1, ht'.2]

/--
Inputs: a nontrivial Dirichlet character and a closed disk centered at an arbitrary complex
point.

Claim: the divisor support of its completed L-function in the open disk is finite.

Proof: the completed L-function is analytic on the corresponding closed disk; compactness of that
disk and finiteness of analytic divisors give the result.

Role: makes the zeros with their analytic multiplicities into finite data for local power-sum
arguments.
-/
theorem completedLFunction_local_zero_support_finite {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (c : ℂ) (R : ℝ) :
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.ball c |R|)).support.Finite := by
  have hanalytic :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.closedBall c |R|) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  exact hanalytic.meromorphicOn.divisor_ball_support_finite

/--
Inputs: a complex zero location `u` and a derivative order `n`.
Claim: the `n`th derivative of the reciprocal affine factor is `(-1)^n n! (z-u)^(-1-n)`.
Proof: translate the global reciprocal derivative formula on an open set to the point `u`.
Role: gives the explicit higher inverse-distance powers contributed by each local zero factor.
-/
theorem iteratedDeriv_sub_const_inv (u : ℂ) (n : ℕ) :
    iteratedDeriv n (fun z : ℂ => (z - u)⁻¹) =
      (fun z => (-1 : ℂ) ^ n * (n.factorial : ℂ) * (z - u) ^ (-1 - n : ℤ)) := by
  rw [iteratedDeriv_comp_sub_const]
  have h := iteratedDerivWithin_one_div (𝕜 := ℂ) (s := Set.univ) n isOpen_univ
  funext z
  simpa only [Set.mem_univ, iteratedDerivWithin_univ, one_div] using h (Set.mem_univ (z - u))

/--
Inputs: complex numbers `z,u` and an iterated derivative order `n`.
Claim: The integer power in the iterated derivative of a zero factor equals the corresponding
natural power of its reciprocal.
Proof: Rewrite the exponent `-1-n` as `Int.negSucc n` and convert to a reciprocal power.
Role: matches the central logarithmic-derivative formula with Turán's weighted power sum.
-/
theorem zpow_neg_one_sub_nat_eq_inv_pow (z u : ℂ) (n : ℕ) :
    (z - u) ^ (-1 - (n : ℤ) : ℤ) = (z - u)⁻¹ ^ (n + 1) := by
  rw [show (-1 - (n : ℤ)) = Int.negSucc n by
      simp only [sub_eq_add_neg, Int.negSucc_eq, neg_add, add_comm]]
  simp only [zpow_negSucc, inv_pow]

/--
Inputs: complex numbers `z,u` and natural numbers `M,l`.
Claim: Turán's exponent `M+1+l` is the reciprocal-power exponent corresponding to derivative
order `M+l`.
Proof: Use the exponent conversion for iterated derivatives and reassociate natural-number
addition.
Role: applies Turán's finite power-sum estimate to iterated logarithmic derivatives at the center.
-/
theorem zpow_neg_one_sub_add_eq_inv_pow (z u : ℂ) (M l : ℕ) :
    (z - u) ^ (-1 - ((M + l : ℕ) : ℤ)) = (z - u)⁻¹ ^ (M + 1 + l) := by
  rw [zpow_neg_one_sub_nat_eq_inv_pow]
  congr 1
  calc
    M + l + 1 = M + (l + 1) := Nat.add_assoc M l 1
    _ = M + (1 + l) := congrArg (fun k : ℕ => M + k) (Nat.add_comm l 1)
    _ = M + 1 + l := (Nat.add_assoc M 1 l).symm

/--
Inputs: a finite set of complex points and an ambient open set.
Claim: away from a discrete subset of the open set, the variable differs from every point in the
finite set.
Proof: the exceptional set is finite and therefore locally finite in the open set.
Role: supplies regular points for differentiating finite sums of reciprocal factors.
-/
theorem eventually_forall_ne_of_finset (s : Finset ℂ) (U : Set ℂ) :
    ∀ᶠ z in Filter.codiscreteWithin U, ∀ u ∈ s, z ≠ u := by
  apply codiscreteWithin_iff_locallyFiniteComplementWithin.2
  intro z hz
  refine ⟨Set.univ, Filter.univ_mem, ?_⟩
  apply s.finite_toSet.subset
  intro w hw
  simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_univ] at hw
  by_contra hws
  apply hw.2.2
  intro u hu hwu
  apply hws
  simpa [hwu] using hu

/--
Inputs: a finite set `s`, complex weights `m`, a set `U`, a derivative order `n`, and the
filter statement that points in `U` avoid `s` generically.
Claim: the `n`th derivative of the finite reciprocal sum is the weighted sum of inverse powers.
Proof: differentiate the finite sum at points outside `s` and use the affine reciprocal derivative
formula term by term.
Role: converts finite local zero contributions into the power sums used by Turan estimates.
-/
theorem iteratedDeriv_finset_reciprocal_sum (s : Finset ℂ) (m : ℂ → ℂ) (n : ℕ) (U : Set ℂ)
    (havoid : ∀ᶠ z in Filter.codiscreteWithin U, ∀ u ∈ s, z ≠ u) :
    iteratedDeriv n (fun z : ℂ => ∑ u ∈ s, m u * (z - u)⁻¹) =ᶠ[Filter.codiscreteWithin U]
      (fun z => ∑ u ∈ s, m u * ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (z - u) ^ (-1 - n : ℤ))) := by
  have hsum : (fun z : ℂ => ∑ u ∈ s, m u * (z - u)⁻¹) = ∑ u ∈ s, fun w : ℂ => m u * (w - u)⁻¹ := by
    funext z
    exact (Finset.sum_apply z s (fun u w => m u * (w - u)⁻¹)).symm
  filter_upwards [havoid] with z hz
  rw [hsum]
  have hcont (u : ℂ) (hu : u ∈ s) : ContDiffAt ℂ n (fun w : ℂ => m u * (w - u)⁻¹) z := by
    have hzu : z - u ≠ 0 := sub_ne_zero.mpr (hz u hu)
    have hanalytic : AnalyticAt ℂ (fun w : ℂ => (w - u)⁻¹) z :=
      (analyticAt_id.sub analyticAt_const).inv hzu
    exact (analyticAt_const.mul hanalytic).contDiffAt
  rw [iteratedDeriv_sum (fun u hu => hcont u hu)]
  apply Finset.sum_congr rfl
  intro u hu
  have hzu : z - u ≠ 0 := sub_ne_zero.mpr (hz u hu)
  have hanalytic : AnalyticAt ℂ (fun w : ℂ => (w - u)⁻¹) z :=
    (analyticAt_id.sub analyticAt_const).inv hzu
  have hcontInv : ContDiffAt ℂ n (fun w : ℂ => (w - u)⁻¹) z := hanalytic.contDiffAt
  rw [iteratedDeriv_const_mul (m u) hcontInv,
    PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.iteratedDeriv_sub_const_inv]

/--
Inputs: a complex coefficient function with finite support, an open set `U`, and a derivative
order `n`.
Claim: the `n`th derivative of its finite reciprocal sum, written as a `finsum`, equals the
corresponding weighted inverse-power `finsum` away from a discrete subset of `U`.
Proof: reduce both `finsum`s to the finite support and apply the finite-sum derivative formula.
Role: provides the higher-order zero contribution in the local completed-L-function decomposition.
-/
theorem iteratedDeriv_finsum_reciprocal_sum (m : ℂ → ℂ) (hfinite : m.support.Finite) (n : ℕ)
    (U : Set ℂ) :
    iteratedDeriv n (fun z : ℂ => ∑ᶠ u, m u * (z - u)⁻¹) =ᶠ[Filter.codiscreteWithin U]
      (fun z => ∑ᶠ u, m u * ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (z - u) ^ (-1 - n : ℤ))) := by
  let s := hfinite.toFinset
  have hsum (z : ℂ) : (∑ᶠ u, m u * (z - u)⁻¹) = ∑ u ∈ s, m u * (z - u)⁻¹ := by
    rw [finsum_eq_sum_of_support_subset _ (s := s)]
    intro u hu
    simp only [Function.mem_support] at hu
    have hmu : m u ≠ 0 := by
      intro hm
      apply hu
      simp only [hm, zero_mul]
    exact (Set.Finite.mem_toFinset hfinite).mpr (by simpa only [Function.mem_support] using hmu)
  have hsumFun : (fun z : ℂ => ∑ᶠ u, m u * (z - u)⁻¹) = ∑ u ∈ s, fun w : ℂ => m u * (w - u)⁻¹ := by
    funext z
    simpa only [Finset.sum_apply] using hsum z
  have hpower (z : ℂ) :
    (∑ᶠ u, m u * ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (z - u) ^ (-1 - n : ℤ))) =
      ∑ u ∈ s, m u * ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (z - u) ^ (-1 - n : ℤ)) := by
    rw [finsum_eq_sum_of_support_subset _ (s := s)]
    intro u hu
    simp only [Function.mem_support] at hu
    have hmu : m u ≠ 0 := by
      intro hm
      apply hu
      simp only [hm, zero_mul]
    exact (Set.Finite.mem_toFinset hfinite).mpr (by simpa only [Function.mem_support] using hmu)
  have hlocal := iteratedDeriv_finset_reciprocal_sum s m n U (eventually_forall_ne_of_finset s U)
  filter_upwards [hlocal] with z hz
  calc
    iteratedDeriv n (fun w : ℂ => ∑ᶠ u, m u * (w - u)⁻¹) z =
        iteratedDeriv n (fun w : ℂ => ∑ u ∈ s, m u * (w - u)⁻¹) z :=
      by exact congrArg (fun f : ℂ → ℂ => iteratedDeriv n f z) (funext hsum)
    _ = ∑ u ∈ s, m u * ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (z - u) ^ (-1 - n : ℤ)) := hz
    _ = ∑ᶠ u, m u * ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (z - u) ^ (-1 - n : ℤ)) := (hpower z).symm

/--
Inputs: a function analytic on the whole complex plane and a disk center where its value is
nonzero.
Claim: Extract the divisor in the disk as a finite product and obtain a local factorization with
a zero-free analytic factor.
Proof: The nonzero value at the specified point gives finite analytic order; use connectedness
and the local factorization theorem.
Role: provides the local Turán factorization beyond the completed `L` function.
-/
theorem exists_analytic_local_zero_factorization {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F Set.univ)
    (z₀ : ℂ) (hz₀ : F z₀ ≠ 0) (c : ℂ) (R : ℝ) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (Metric.ball c |R|) ∧
        (∀ u : Metric.ball c |R|, g u ≠ 0) ∧
        F =ᶠ[Filter.codiscreteWithin (Metric.ball c |R|)]
          (∏ᶠ u, (· - u) ^ MeromorphicOn.divisor F (Metric.ball c |R|) u) • g := by
  have hz₀Order : analyticOrderAt F z₀ ≠ ⊤ := by
    rw [(hF z₀ trivial).analyticOrderAt_eq_zero.mpr hz₀]
    exact ENat.natCast_ne_top 0
  have hcOrder : analyticOrderAt F c ≠ ⊤ :=
    hF.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ trivial trivial hz₀Order
  have horder (z : ℂ) : analyticOrderAt F z ≠ ⊤ :=
    hF.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ trivial trivial hcOrder
  have hnotTop (u : Metric.ball c |R|) : meromorphicOrderAt F u ≠ ⊤ := by
    rw [(hF u.1 trivial).meromorphicOrderAt_eq]
    intro hu
    exact horder u.1 (ENat.map_eq_top_iff.mp hu)
  have hball : AnalyticOnNhd ℂ F (Metric.closedBall c |R|) := by
    intro z _
    exact hF z trivial
  have hopen : AnalyticOnNhd ℂ F (Metric.ball c |R|) := by
    intro z hz
    exact hball z (Metric.ball_subset_closedBall hz)
  have hfinite : (MeromorphicOn.divisor F (Metric.ball c |R|)).support.Finite :=
    hball.meromorphicOn.divisor_ball_support_finite
  exact hopen.meromorphicOn.extract_zeros_poles hnotTop hfinite

/--
Inputs: a nontrivial Dirichlet character and a disk in the complex plane.

Claim: on that disk the completed L-function factors, up to equality away from a discrete set, as
its divisor factors times an analytic function that never vanishes.

Proof: its value at one is nonzero, so connectedness makes its analytic order finite everywhere;
the local meromorphic factorization theorem then extracts the finite divisor in the disk.

Role: isolates the local zero contribution before estimating the remaining analytic logarithmic
derivative.
-/
theorem exists_completedLFunction_local_zero_factorization {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (c : ℂ) (R : ℝ) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (Metric.ball c |R|) ∧
        (∀ u : Metric.ball c |R|, g u ≠ 0) ∧
        DirichletCharacter.completedLFunction χ =ᶠ[Filter.codiscreteWithin (Metric.ball c |R|)]
          (∏ᶠ u,
              (· - u) ^
                MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |R|)
                  u) •
            g := by
  let F := DirichletCharacter.completedLFunction χ
  have hF : AnalyticOnNhd ℂ F Set.univ := fun z _ =>
    (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have h1nz : F 1 ≠ 0 := dirichletCompletedLFunction_one_ne_zero_of_ne_one hχ
  obtain ⟨g, hg, hgn, hfactor⟩ := exists_analytic_local_zero_factorization hF 1 h1nz c R
  refine ⟨g, hg, hgn, ?_⟩
  simpa only [F] using hfactor

/--
Inputs: a nontrivial character, a completed `L` zero, and a ball containing that zero.
Claim: the zero belongs to the support of the completed function's divisor on the ball.
Content: analyticity and finite meromorphic order identify the zero set with the divisor support.
Proof: rewrite membership through `MeromorphicNFOn.zero_set_eq_divisor_support`.
Role: supplies the local support witness required by Turán's zero-detection estimate.
-/
theorem completedLFunction_zero_mem_local_divisor_support {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {c : ℂ} {R : ℝ} {u : ℂ} (hu : u ∈ Metric.ball c |R|)
    (hzero : DirichletCharacter.completedLFunction χ u = 0) :
    u ∈
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.ball c |R|)).support := by
  let F := DirichletCharacter.completedLFunction χ
  let U := Metric.ball c |R|
  have hFanalytic : AnalyticOnNhd ℂ F U := fun z _ =>
    (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have hnormal : MeromorphicNFOn F U := hFanalytic.meromorphicNFOn
  have hmem : u ∈ U ∩ F ⁻¹' {0} := ⟨hu, hzero⟩
  rw [hnormal.zero_set_eq_divisor_support fun v =>
      meromorphicOrderAt_dirichletCompletedLFunction_ne_top χ hχ v] at hmem
  change u ∈ (MeromorphicOn.divisor F U).support
  exact hmem

/--
Inputs: a nontrivial character and a zero of its completed `L` function.
Claim: there is a ball of radius at most one containing the zero whose center is not a zero.
Content: finite analytic order rules out local vanishing identically; isolated zeros then provide
a nonzero center within distance one half, and a ball of twice that distance contains the zero.
Proof: apply the analytic isolated-zero theorem and the identity principle at the point two.
Role: produces the geometric local input for the completed `L` Turán derivative bound.
-/
theorem exists_completedLFunction_nonzero_center_ball_of_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {ρ : ℂ}
    (hzero : DirichletCharacter.completedLFunction χ ρ = 0) :
    ∃ c : ℂ,
      ∃ R : ℝ,
        0 < R ∧ R ≤ 1 ∧ DirichletCharacter.completedLFunction χ c ≠ 0 ∧ ρ ∈ Metric.ball c R := by
  let F := DirichletCharacter.completedLFunction χ
  have hF : AnalyticOnNhd ℂ F Set.univ := fun z _ =>
    (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have htwo_ne : F 2 ≠ 0 := dirichletCompletedLFunction_two_ne_zero χ hχ
  have htwo_ord : analyticOrderAt F (2 : ℂ) = 0 :=
    (hF 2 trivial).analyticOrderAt_eq_zero.mpr htwo_ne
  have htwo_notTop : analyticOrderAt F (2 : ℂ) ≠ ⊤ := by
    rw [htwo_ord]
    exact ENat.natCast_ne_top 0
  have horder : analyticOrderAt F ρ ≠ ⊤ :=
    hF.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ trivial trivial htwo_notTop
  have hlocal : ¬∀ᶠ z in nhds ρ, F z = 0 := by
    intro hevent
    exact horder (analyticOrderAt_eq_top.mpr hevent)
  have hanalyticAt : AnalyticAt ℂ F ρ :=
    (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt ρ
  have hnonzero : ∀ᶠ z in nhdsWithin ρ ({ρ}ᶜ), F z ≠ 0 :=
    hanalyticAt.eventually_eq_zero_or_eventually_ne_zero.resolve_left hlocal
  have hradius : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num only
  have hnearBase : ∀ᶠ z in nhds ρ, z ∈ Metric.ball ρ (1 / 2 : ℝ) := Metric.ball_mem_nhds ρ hradius
  have hnearBall : ∀ᶠ z in nhdsWithin ρ ({ρ}ᶜ), z ∈ Metric.ball ρ (1 / 2 : ℝ) :=
    hnearBase.filter_mono nhdsWithin_le_nhds
  have hnear : ∀ᶠ z in nhdsWithin ρ ({ρ}ᶜ), dist z ρ < (1 / 2 : ℝ) := by
    simpa only [Metric.mem_ball] using hnearBall
  obtain ⟨c, hc⟩ := hnonzero.and hnear |>.exists
  have hne : c ≠ ρ := by
    intro heq
    apply hc.1
    rw [heq]
    exact hzero
  have hdist : 0 < dist c ρ := dist_pos.mpr hne
  let R : ℝ := 2 * dist c ρ
  have hRpos : 0 < R := by
    dsimp [R]
    positivity
  have hRle : R ≤ 1 := by
    dsimp [R]
    nlinarith only [hc.2]
  have hρ : ρ ∈ Metric.ball c R := by
    rw [Metric.mem_ball, dist_comm]
    dsimp [R]
    nlinarith only [hdist]
  exact ⟨c, R, hRpos, hRle, hc.1, hρ⟩

/--
Inputs: a nontrivial character, a completed `L` zero `ρ`, and a real number `σ` with
`3/4 ≤ σ ≤ re ρ`.
Claim: the zero lies in an explicit ball of radius at most one centered at
`2 - σ + im(ρ) I`, and the completed `L` function is nonzero at that center.
Content: the center has real part `2 - σ > 1`, where completed `L` nonvanishing applies;
the zero's real part bounds its distance from the center by `2(1 - σ)`.
Proof: compute both coordinates, use the zero-free half-plane, then compare the distance with
the chosen radius.
Role: replaces an arbitrary nearby center and radius with parameters determined by the zero
region, for later uniform local zero estimates.
-/
theorem exists_completedLFunction_explicit_center_ball_of_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ : ℝ} {ρ : ℂ} (hσ : (3 / 4 : ℝ) ≤ σ) (hρ : σ ≤ ρ.re)
    (hzero : DirichletCharacter.completedLFunction χ ρ = 0) :
    ∃ c : ℂ,
      ∃ R : ℝ,
        R = 4 * (1 - σ) ∧
          0 < R ∧
          R ≤ 1 ∧
          c.re = 2 - σ ∧
          c.im = ρ.im ∧ DirichletCharacter.completedLFunction χ c ≠ 0 ∧ ρ ∈ Metric.ball c R := by
  let c : ℂ := (2 - σ : ℝ) + ρ.im * Complex.I
  let R : ℝ := 4 * (1 - σ)
  have hρlt : ρ.re < 1 :=
    PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedLFunction_zero_re_lt_one hχ hzero
  have hσlt : σ < 1 := lt_of_le_of_lt hρ hρlt
  have hRpos : 0 < R := by
    dsimp only [R]
    nlinarith only [hσlt]
  have hRle : R ≤ 1 := by
    dsimp only [R]
    nlinarith only [hσ]
  have hcre : c.re = 2 - σ := by
    change (((2 - σ : ℝ) : ℂ) + ρ.im * Complex.I).re = 2 - σ
    rw [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im]
    norm_num only [mul_zero, zero_mul, one_mul, sub_self, add_zero]
  have hcim : c.im = ρ.im := by
    change (((2 - σ : ℝ) : ℂ) + ρ.im * Complex.I).im = ρ.im
    rw [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re]
    norm_num only [mul_zero, zero_mul, mul_one, add_zero, zero_add]
  have hc : DirichletCharacter.completedLFunction χ c ≠ 0 := by
    apply completedLFunction_ne_zero_of_one_le_re hχ
    rw [hcre]
    linarith only [hσlt]
  have hsubre : (c - ρ).re = 2 - σ - ρ.re := by rw [Complex.sub_re, hcre]
  have hsubim : (c - ρ).im = 0 := by
    calc
      (c - ρ).im = c.im - ρ.im := Complex.sub_im _ _
      _ = 0 := by rw [hcim, sub_self]
  have hsub : c - ρ = ((2 - σ - ρ.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simpa only [Complex.ofReal_re] using hsubre
    · simpa only [Complex.ofReal_im] using hsubim
  have hreal : 0 ≤ 2 - σ - ρ.re := by linarith only [hρ, hρlt]
  have hdist : dist ρ c = 2 - σ - ρ.re := by
    rw [dist_comm, dist_eq_norm, hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hreal]
  refine ⟨c, R, rfl, hRpos, hRle, hcre, hcim, hc, ?_⟩
  rw [Metric.mem_ball]
  dsimp only [R]
  nlinarith only [hdist, hρ, hσlt]

/--
Inputs: a center with `re c = 2 - σ`, a threshold `13/14 ≤ σ < 1`, and a point on the
circle of radius `8(1 - σ)` around `c`.
Claim: the point has real part at least `1/2`.
Content: the circle extends at most `8(1 - σ)` to the left of a center whose real part is
`2 - σ`; the threshold `13/14` makes this left edge at least `1/2`.
Proof: bound the real-coordinate difference by the complex distance and apply the threshold.
Role: verifies the outer-circle hypothesis needed to apply the polynomial-growth Jensen estimate
to the explicit local ball.
-/
theorem explicit_center_outer_circle_re_ge_half {σ : ℝ} {c z : ℂ} (hcre : c.re = 2 - σ)
    (hσ : (13 / 14 : ℝ) ≤ σ) (hσlt : σ < 1) (hz : z ∈ Metric.sphere c (8 * (1 - σ))) :
    (1 / 2 : ℝ) ≤ z.re := by
  have hR : 0 < 8 * (1 - σ) := by nlinarith only [hσlt]
  have hdist : dist z c = 8 * (1 - σ) := by simpa only [Metric.mem_sphere, abs_of_pos hR] using hz
  have hnorm : ‖z - c‖ = 8 * (1 - σ) := by rwa [← dist_eq_norm]
  have hcoord : |z.re - c.re| ≤ 8 * (1 - σ) := by
    rw [← Complex.sub_re]
    exact (Complex.abs_re_le_norm (z - c)).trans_eq hnorm
  have hleft := (abs_le.mp hcoord).1
  nlinarith only [hcre, hσ, hleft]

/-- The outer-circle half-plane bound for the radius `16(1 - σ)` at `σ ≥ 29/30`. -/
theorem explicit_center_outer_circle_re_ge_half_of_scale16 {σ : ℝ} {c z : ℂ} (hcre : c.re = 2 - σ)
    (hσ : (29 / 30 : ℝ) ≤ σ) (hσlt : σ < 1) (hz : z ∈ Metric.sphere c (16 * (1 - σ))) :
    (1 / 2 : ℝ) ≤ z.re := by
  have hR : 0 < 16 * (1 - σ) := by nlinarith only [hσlt]
  have hdist : dist z c = 16 * (1 - σ) := by simpa only [Metric.mem_sphere, abs_of_pos hR] using hz
  have hnorm : ‖z - c‖ = 16 * (1 - σ) := by rwa [← dist_eq_norm]
  have hcoord : |z.re - c.re| ≤ 16 * (1 - σ) := by
    rw [← Complex.sub_re]
    exact (Complex.abs_re_le_norm (z - c)).trans_eq hnorm
  have hleft := (abs_le.mp hcoord).1
  nlinarith only [hcre, hσ, hleft]

/--
Inputs: a nontrivial character of modulus greater than one, a center with `re c = 2 - σ`,
`13/14 ≤ σ < 1`, a nonzero ordinary `L`-value at the center, and a rectangle contained in
the disk of radius `4(1 - σ)`.
Claim: the completed zero count in the rectangle satisfies the explicit polynomial-growth
Jensen bound with outer radius `8(1 - σ)`.
Content: the outer circle lies in `re s ≥ 1/2`, and the ratio of outer to inner radii is two.
Proof: establish the outer-circle half-plane condition above and apply the rectangle-to-disk
Jensen estimate.
Role: supplies a Jensen bound for local zero sets around the explicit centers used near `Re s=1`.
-/
theorem completedZeroMultiplicityCountInRectangle_le_explicit_center_Jensen_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 1 < q) {σ : ℝ} {c : ℂ} (hcre : c.re = 2 - σ)
    (hσ : (13 / 14 : ℝ) ≤ σ) (hσlt : σ < 1) (hc : DirichletCharacter.LFunction χ c ≠ 0) (z w : ℂ)
    (hcoord :
      ∀ x ∈ Set.uIcc z.re w.re,
        ∀ y ∈ Set.uIcc z.im w.im, (x - c.re) ^ 2 + (y - c.im) ^ 2 ≤ (4 * (1 - σ)) ^ 2) :
    completedZeroMultiplicityCountInRectangle χ hχ z w ≤
      Real.log
          (max (1 : ℝ) (2 * (q : ℝ) * (‖c‖ + |8 * (1 - σ)|)) / ‖DirichletCharacter.LFunction χ c‖) /
        Real.log ((8 * (1 - σ)) / (4 * (1 - σ))) := by
  have hinner : 0 < 4 * (1 - σ) := by nlinarith only [hσlt]
  have houter : 4 * (1 - σ) < 8 * (1 - σ) := by nlinarith only [hinner]
  have houterPos : 0 < 8 * (1 - σ) := by nlinarith only [hinner]
  have hinnerAbs : 0 < |4 * (1 - σ)| := by simpa only [abs_of_pos hinner] using hinner
  have hratio : |4 * (1 - σ)| < |8 * (1 - σ)| := by
    rw [abs_of_pos hinner, abs_of_pos houterPos]
    exact houter
  have hcircle : ∀ v ∈ Metric.sphere c |8 * (1 - σ)|, 1 / 2 ≤ v.re := by
    intro v hv
    have hv' : v ∈ Metric.sphere c (8 * (1 - σ)) := by simpa only [abs_of_pos houterPos] using hv
    exact explicit_center_outer_circle_re_ge_half hcre hσ hσlt hv'
  have hcoord' :
    ∀ x ∈ Set.uIcc z.re w.re,
      ∀ y ∈ Set.uIcc z.im w.im, (x - c.re) ^ 2 + (y - c.im) ^ 2 ≤ |4 * (1 - σ)| ^ 2 := by
    simpa only [abs_of_pos hinner] using hcoord
  exact
    completedZeroMultiplicityCountInRectangle_le_LFunction_Jensen_bound hq hχ z w c (r :=
      4 * (1 - σ)) (R := 8 * (1 - σ)) hinnerAbs hratio hc hcircle hcoord'

/--
Inputs: a nontrivial character, an explicit center with `1 - σ < ε`, and a rectangle inside
the inner Jensen disk.
Claim: the completed zero count has a bound depending only on the outer growth, conductor, and
the local pole constant `C`, with the center-value denominator removed.
Proof: use the three-L-function lower bound at `1 + (1 - σ) + it`, then compare logarithms in
the explicit-center Jensen estimate.
Role: provides a quantitative center estimate for the near-one local zero-density step.
-/
theorem exists_completedZeroMultiplicityCountInRectangle_le_explicit_center_Jensen_bound_of_near_one
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 1 < q) :
    ∃ C ε : ℝ,
      0 < C ∧
        0 < ε ∧
        ε ≤ 1 ∧
        ∀ {σ : ℝ} {c : ℂ},
          c.re = 2 - σ →
            (13 / 14 : ℝ) ≤ σ →
            σ < 1 →
            1 - σ < ε →
            ∀ z w : ℂ,
              (∀ x ∈ Set.uIcc z.re w.re,
                  ∀ y ∈ Set.uIcc z.im w.im, (x - c.re) ^ 2 + (y - c.im) ^ 2 ≤ (4 * (1 - σ)) ^ 2) →
                completedZeroMultiplicityCountInRectangle χ hχ z w ≤
                  Real.log
                      (max (1 : ℝ) (2 * (q : ℝ) * (‖c‖ + |8 * (1 - σ)|)) *
                        (2 * (q : ℝ) * C / (1 - σ))) /
                    Real.log 2 := by
  obtain ⟨C, ε, hC, hε, hεle, hLlower⟩ := exists_norm_LFunction_lower_bound_one_add (N := q) χ
  refine ⟨C, ε, hC, hε, hεle, ?_⟩
  intro σ c hcre hσ hσlt hnear z w hcoord
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  let x : ℝ := 1 - σ
  let M : ℝ := max (1 : ℝ) (2 * (q : ℝ) * (‖c‖ + |8 * (1 - σ)|))
  let K : ℝ := 2 * (q : ℝ) * C / x
  let B : ℝ := ‖DirichletCharacter.LFunction χ c‖
  have hx : 0 < x := by
    dsimp only [x]; linarith only [hσlt]
  have hxε : x < ε := by
    dsimp only [x]; exact hnear
  have hcenter := hLlower x c.im hx hxε
  have hcarg : c = 1 + (x : ℂ) + Complex.I * c.im := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, zero_mul]
      rw [hcre]
      dsimp only [x]
      ring
    · simp only [Complex.add_im, Complex.one_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, mul_zero, add_zero]
      ring
  have hcenter' : x / (2 * (q : ℝ) * C) ≤ B := by
    dsimp only [B]
    rw [hcarg]
    exact hcenter
  have hB : 0 < B :=
    lt_of_lt_of_le (div_pos hx (mul_pos (mul_pos (by norm_num only) hqpos) hC)) hcenter'
  have hc : DirichletCharacter.LFunction χ c ≠ 0 := by
    intro hz
    have hzero : B = 0 := by
      dsimp only [B]; rw [hz, norm_zero]
    linarith only [hB, hzero]
  have hJ :=
    completedZeroMultiplicityCountInRectangle_le_explicit_center_Jensen_bound χ hχ hq hcre hσ hσlt
      hc z w hcoord
  have hM : 0 < M := by
    dsimp only [M]
    exact lt_of_lt_of_le (by norm_num only) (le_max_left _ _)
  have hK : 0 < K := by
    dsimp only [K, x]
    exact div_pos (mul_pos (mul_pos (by norm_num only) hqpos) hC) (by linarith only [hσlt])
  have hApos : 0 < 2 * (q : ℝ) * C := mul_pos (mul_pos (by norm_num only) hqpos) hC
  have hKcenter : 1 ≤ K * B := by
    have hmul : x ≤ B * (2 * (q : ℝ) * C) := (div_le_iff₀ hApos).1 hcenter'
    dsimp only [K]
    calc
      1 = (x / (2 * (q : ℝ) * C)) * ((2 * (q : ℝ) * C) / x) := by
        field_simp [ne_of_gt hx, ne_of_gt hApos]
      _ ≤ B * ((2 * (q : ℝ) * C) / x) := mul_le_mul_of_nonneg_right hcenter' (le_of_lt hK)
      _ = ((2 * (q : ℝ) * C) / x) * B := by ring
  have hquot : M / B ≤ M * K := by
    apply (div_le_iff₀ hB).2
    calc
      M = M * 1 := by ring
      _ ≤ M * (K * B) := mul_le_mul_of_nonneg_left hKcenter (le_of_lt hM)
      _ = (M * K) * B := by ring
  have hlog : Real.log (M / B) ≤ Real.log (M * K) := Real.log_le_log (div_pos hM hB) hquot
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have hratio : (8 * (1 - σ)) / (4 * (1 - σ)) = 2 := by
    dsimp only [x] at hx
    field_simp [ne_of_gt hx]
    ring
  have hJ' :
    completedZeroMultiplicityCountInRectangle χ hχ z w ≤ Real.log (M / B) / Real.log 2 := by
    simpa only [M, B, hratio] using hJ
  have hfinal := div_le_div_of_nonneg_right hlog (le_of_lt hlog2)
  dsimp only [M, K, x] at hfinal
  exact le_trans hJ' hfinal

/--
Inputs: a center with `re c = 2 - σ`, `29/30 ≤ σ < 1`, a nonzero center value, and a
rectangle contained in the disk of radius `8(1 - σ)`.
Claim: its completed zero count is bounded by the polynomial-growth Jensen estimate with outer
radius `16(1 - σ)`.
Content: the outer circle stays in `re s ≥ 1/2`, and the outer-to-inner radius ratio is two.
Proof: use the scale-16 circle bound and the rectangle-to-disk Jensen theorem.
Role: bounds the zero count in a square that contains the explicit local divisor ball.
-/
theorem completedZeroMultiplicityCountInRectangle_le_explicit_center_Jensen_bound_of_scale8 {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 1 < q) {σ : ℝ} {c : ℂ}
    (hcre : c.re = 2 - σ) (hσ : (29 / 30 : ℝ) ≤ σ) (hσlt : σ < 1)
    (hc : DirichletCharacter.LFunction χ c ≠ 0) (z w : ℂ)
    (hcoord :
      ∀ x ∈ Set.uIcc z.re w.re,
        ∀ y ∈ Set.uIcc z.im w.im, (x - c.re) ^ 2 + (y - c.im) ^ 2 ≤ (8 * (1 - σ)) ^ 2) :
    completedZeroMultiplicityCountInRectangle χ hχ z w ≤
      Real.log
          (max (1 : ℝ) (2 * (q : ℝ) * (‖c‖ + |16 * (1 - σ)|)) /
            ‖DirichletCharacter.LFunction χ c‖) /
        Real.log ((16 * (1 - σ)) / (8 * (1 - σ))) := by
  have hinner : 0 < 8 * (1 - σ) := by nlinarith only [hσlt]
  have houter : 8 * (1 - σ) < 16 * (1 - σ) := by nlinarith only [hinner]
  have houterPos : 0 < 16 * (1 - σ) := by nlinarith only [hinner]
  have hinnerAbs : 0 < |8 * (1 - σ)| := by simpa only [abs_of_pos hinner] using hinner
  have hratio : |8 * (1 - σ)| < |16 * (1 - σ)| := by
    rw [abs_of_pos hinner, abs_of_pos houterPos]
    exact houter
  have hcircle : ∀ v ∈ Metric.sphere c |16 * (1 - σ)|, 1 / 2 ≤ v.re := by
    intro v hv
    have hv' : v ∈ Metric.sphere c (16 * (1 - σ)) := by simpa only [abs_of_pos houterPos] using hv
    exact explicit_center_outer_circle_re_ge_half_of_scale16 hcre hσ hσlt hv'
  have hcoord' :
    ∀ x ∈ Set.uIcc z.re w.re,
      ∀ y ∈ Set.uIcc z.im w.im, (x - c.re) ^ 2 + (y - c.im) ^ 2 ≤ |8 * (1 - σ)| ^ 2 := by
    simpa only [abs_of_pos hinner] using hcoord
  exact
    completedZeroMultiplicityCountInRectangle_le_LFunction_Jensen_bound hq hχ z w c (r :=
      8 * (1 - σ)) (R := 16 * (1 - σ)) hinnerAbs hratio hc hcircle hcoord'

/--
Inputs: a nontrivial completed Dirichlet `L`-function, a disk, and a point in the disk.
Claim: the divisor multiplicity in the disk equals the global completed-function divisor
multiplicity at that point.
Proof: apply the analytic divisor formula on the disk and on the whole plane; both values are the
same analytic order of the completed function.
Role: identifies finite local zero sums with the corresponding part of the global zero sum.
-/
theorem completedLFunction_local_divisor_eq_global_at {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (c : ℂ) (R : ℝ) {ρ : ℂ} (hρ : ρ ∈ Metric.ball c |R|) :
    MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |R|) ρ =
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ := by
  have hF : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ := by
    intro z hz
    exact (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have hFlocal : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.ball c |R|) := by
    intro z hz
    exact hF z (Set.mem_univ z)
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hFlocal hρ,
    MeromorphicOn.AnalyticOnNhd.divisor_apply hF (Set.mem_univ ρ)]

/--
Inputs: a nontrivial character, a local ball, and a rectangle containing every point in the
ball's completed-function divisor support.
Claim: the number of distinct divisor-support points is at most the rectangle's
multiplicity-weighted completed zero count.
Content: every support point is a zero in the rectangle, and each analytic zero order is positive.
Proof: map the finite divisor support into the rectangle's finite zero ledger, then use
`Finset.card_nsmul_le_sum` and nonnegativity of all remaining multiplicities.
Role: converts local divisor support size, which controls the Turán derivative order, into the
standard multiplicity-weighted zero-counting interface.
-/
theorem completedLFunction_local_divisor_support_card_le_rectangle_count {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (c : ℂ) (R : ℝ) (z w : ℂ)
    (hbox :
      ∀ u,
        u ∈
            (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                (Metric.ball c |R|)).support →
          u ∈ dirichletCompletedLFunctionRectangleBox z w) :
    (((completedLFunction_local_zero_support_finite χ hχ c R).toFinset.card : ℕ) : ℝ) ≤
      completedZeroMultiplicityCountInRectangle χ hχ z w := by
  classical
  let F : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  let U := Metric.ball c |R|
  let D : ℂ → ℤ := MeromorphicOn.divisor F U
  let hfinite : D.support.Finite := completedLFunction_local_zero_support_finite χ hχ c R
  let S := hfinite.toFinset
  let Z := completedZerosInRectangle χ hχ z w
  have hFanalytic : AnalyticOnNhd ℂ F U := by
    intro u hu
    exact (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt u
  have hFglobal : AnalyticOnNhd ℂ F Set.univ := by
    intro u hu
    exact (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt u
  have hnormal : MeromorphicNFOn F U := hFanalytic.meromorphicNFOn
  have hs : ∀ u ∈ S, u ∈ Z := by
    intro u hu
    have huD : u ∈ D.support := (Set.Finite.mem_toFinset hfinite).mp hu
    have hzmem : u ∈ U ∩ F ⁻¹' {0} := by
      rw [hnormal.zero_set_eq_divisor_support
          (fun v => meromorphicOrderAt_dirichletCompletedLFunction_ne_top χ hχ v)]
      exact huD
    have hz : F u = 0 := hzmem.2
    exact (mem_completedZerosInRectangle_iff).2 ⟨hbox u huD, hz⟩
  have horderpos : ∀ u ∈ Z, 0 < analyticOrderNatAt F u := by
    intro u hu
    have hz : F u = 0 := (mem_completedZerosInRectangle_iff.mp hu).2
    have hA := (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt u
    have hAorder : analyticOrderAt F u ≠ 0 := hA.analyticOrderAt_ne_zero.mpr hz
    have htop : analyticOrderAt F u ≠ ⊤ := by
      intro heq
      have htop' := meromorphicOrderAt_dirichletCompletedLFunction_ne_top χ hχ u
      rw [hA.meromorphicOrderAt_eq, heq, ENat.map_top] at htop'
      exact htop' rfl
    have hnat : analyticOrderNatAt F u ≠ 0 := by
      intro hzeroNat
      have hzeroOrder : analyticOrderAt F u = 0 := by
        rw [← Nat.cast_analyticOrderNatAt htop]
        simp only [hzeroNat, Nat.cast_zero]
      exact hAorder hzeroOrder
    exact Nat.pos_of_ne_zero hnat
  have hcard : S.card ≤ ∑ u ∈ S, analyticOrderNatAt F u := by
    have hsum :=
      S.card_nsmul_le_sum (fun u => analyticOrderNatAt F u) 1
        (fun u hu => Nat.succ_le_iff.mpr (horderpos u (hs u hu)))
    simpa only [Nat.nsmul_eq_mul, Nat.mul_one] using hsum
  have hcardReal : (S.card : ℝ) ≤ ∑ u ∈ S, (analyticOrderNatAt F u : ℝ) := by exact_mod_cast hcard
  have hsum : (∑ u ∈ S, (analyticOrderNatAt F u : ℝ)) ≤ ∑ u ∈ Z, (analyticOrderNatAt F u : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro u hu
        exact hs u hu)
      (by
        intro u huS huZ
        exact Nat.cast_nonneg _)
  unfold completedZeroMultiplicityCountInRectangle
  simpa only [S, Z, D, F, U] using hcardReal.trans hsum

/--
Inputs: a nontrivial completed Dirichlet `L`-function, a local divisor ball, and a rectangle
containing its divisor support.

Claim: the total analytic multiplicity in the local divisor support is bounded by the
multiplicity-weighted zero count in the rectangle.

Proof: identify each local divisor order with the analytic zero order, then extend the finite sum
to the full rectangle zero set using nonnegativity.

Role: supplies the total-multiplicity bound needed to place local zero power sums in a fixed
multiple exponent block.
-/
theorem completedLFunction_local_divisor_support_multiplicity_le_rectangle_count {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (c : ℂ) (R : ℝ) (z w : ℂ)
    (hbox :
      ∀ u,
        u ∈
            (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                (Metric.ball c |R|)).support →
          u ∈ dirichletCompletedLFunctionRectangleBox z w) :
    (∑ u ∈ (completedLFunction_local_zero_support_finite χ hχ c R).toFinset,
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |R|)
              u).toNat :
          ℝ)) ≤
      completedZeroMultiplicityCountInRectangle χ hχ z w := by
  classical
  let F : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  let U := Metric.ball c |R|
  let D : ℂ → ℤ := MeromorphicOn.divisor F U
  let hfinite : D.support.Finite := completedLFunction_local_zero_support_finite χ hχ c R
  let S := hfinite.toFinset
  let Z := completedZerosInRectangle χ hχ z w
  have hFanalytic : AnalyticOnNhd ℂ F U := by
    intro u hu
    exact (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt u
  have hFglobal : AnalyticOnNhd ℂ F Set.univ := by
    intro u hu
    exact (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt u
  have hnormal : MeromorphicNFOn F U := hFanalytic.meromorphicNFOn
  have hs : ∀ u ∈ S, u ∈ Z := by
    intro u hu
    have huD : u ∈ D.support := (Set.Finite.mem_toFinset hfinite).mp hu
    have hzmem : u ∈ U ∩ F ⁻¹' {0} := by
      rw [hnormal.zero_set_eq_divisor_support
          (fun v => meromorphicOrderAt_dirichletCompletedLFunction_ne_top χ hχ v)]
      exact huD
    exact (mem_completedZerosInRectangle_iff).2 ⟨hbox u huD, hzmem.2⟩
  have horder : ∀ u ∈ S, D u = (analyticOrderNatAt F u : ℤ) := by
    intro u hu
    have huD : u ∈ D.support := (Set.Finite.mem_toFinset hfinite).mp hu
    have huU : u ∈ U := by
      change u ∈ (MeromorphicOn.divisor F U).support at huD
      exact (MeromorphicOn.divisor F U).supportWithinDomain huD
    have hlocalGlobal := completedLFunction_local_divisor_eq_global_at χ hχ c R huU
    rw [show D = MeromorphicOn.divisor F U from rfl, hlocalGlobal,
      MeromorphicOn.AnalyticOnNhd.divisor_apply hFglobal (Set.mem_univ u)]
    change
      ((analyticOrderAt F u).map (fun k : ℕ => (k : ℤ))).untop₀ = ((analyticOrderAt F u).toNat : ℤ)
    induction analyticOrderAt F u using ENat.recTopCoe
    · rfl
    · rfl
  have hsum : (∑ u ∈ S, (analyticOrderNatAt F u : ℝ)) ≤ ∑ u ∈ Z, (analyticOrderNatAt F u : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hs
      (by
        intro u huS huZ
        exact Nat.cast_nonneg _)
  calc
    (∑ u ∈ (completedLFunction_local_zero_support_finite χ hχ c R).toFinset,
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |R|)
                u).toNat :
            ℝ)) =
        ∑ u ∈ S, (analyticOrderNatAt F u : ℝ) :=
      by
      apply Finset.sum_congr rfl
      intro u hu
      have huS : u ∈ S := by simpa only [S] using hu
      rw [show
          MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.ball c |R|) = D by
          rfl,
        horder u huS]
      have htoNat : ((analyticOrderNatAt F u : ℤ).toNat : ℤ) = (analyticOrderNatAt F u : ℤ) :=
        Int.toNat_of_nonneg (by positivity)
      exact_mod_cast htoNat
    _ ≤ completedZeroMultiplicityCountInRectangle χ hχ z w := by
      unfold completedZeroMultiplicityCountInRectangle
      simpa only [Z, F] using hsum

/--
Inputs: a completed-function divisor ball of positive radius and a point in its divisor support.
Claim: every point in the support lies in the axis-aligned square with half-width equal to the
ball radius.
Content: each coordinate difference is bounded by the complex distance, which is strictly less
than the radius inside the ball.
Proof: apply the real- and imaginary-coordinate norm inequalities and rewrite the rectangle as
the product of its two closed intervals.
Role: gives the geometric covering needed to turn a local divisor-support cardinality into a
rectangular zero count.
-/
theorem completedLFunction_local_divisor_support_mem_centered_square {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (c : ℂ) {R : ℝ} (hR : 0 < R) {u : ℂ}
    (hu :
      u ∈
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.ball c R)).support) :
    u ∈
      dirichletCompletedLFunctionRectangleBox (⟨c.re - R, c.im - R⟩ : ℂ)
        (⟨c.re + R, c.im + R⟩ : ℂ) := by
  have huB : u ∈ Metric.ball c R :=
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.ball c R)).supportWithinDomain
      hu
  have hdist : dist u c < R := Metric.mem_ball.mp huB
  have hnorm : ‖u - c‖ < R := by simpa only [dist_eq_norm] using hdist
  have hreNorm : |u.re - c.re| ≤ ‖u - c‖ := by
    rw [← Complex.sub_re]
    exact Complex.abs_re_le_norm (u - c)
  have himNorm : |u.im - c.im| ≤ ‖u - c‖ := by
    rw [← Complex.sub_im]
    exact Complex.abs_im_le_norm (u - c)
  have hre : c.re - R ≤ u.re ∧ u.re ≤ c.re + R := by
    have h := abs_le.mp hreNorm
    constructor <;> linarith only [h.1, h.2, hnorm]
  have him : c.im - R ≤ u.im ∧ u.im ≤ c.im + R := by
    have h := abs_le.mp himNorm
    constructor <;> linarith only [h.1, h.2, hnorm]
  change u.re ∈ Set.uIcc (c.re - R) (c.re + R) ∧ u.im ∈ Set.uIcc (c.im - R) (c.im + R)
  rw [Set.uIcc_of_le (by linarith only [hR]), Set.uIcc_of_le (by linarith only [hR])]
  exact ⟨hre, him⟩

/--
Inputs: a positive shift `η`, a real height `t`, and a zero `ρ` lying within `η / 4` of
`1 + it`, with real part below one.
Claim: the real part of the shifted reciprocal kernel at `1 + η + it` is at least `1 / (2η)`.
Content: the shifted denominator has real part at least `η` and norm at most `5η / 4`, so its
reciprocal has the stated positive lower bound.
Role: supplies the pointwise contribution of each nearby zero in the unconditional local
multiplicity estimate.
-/
theorem re_inv_ge_half_inv_of_near_one_zero {η : ℝ} (hη : 0 < η) {t : ℝ} {ρ : ℂ}
    (hclose : ‖ρ - ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ η / 4) (hρ : ρ.re < 1) :
    (1 / ((1 + η) + (t : ℂ) * Complex.I - ρ)).re ≥ 1 / (2 * η) := by
  let z : ℂ := (1 + η) + (t : ℂ) * Complex.I - ρ
  have hzre' : z.re = 1 + η - ρ.re := by
    dsimp [z]
    simp only [Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      mul_one, mul_zero, sub_zero]
    ring
  have hzre : η ≤ z.re := by
    rw [hzre']; linarith only [hρ]
  have hηnorm : ‖(η : ℂ)‖ = η := by exact (RCLike.norm_ofReal η).trans (abs_of_pos hη)
  have hcenter : ‖(1 : ℂ) + (t : ℂ) * Complex.I - ρ‖ ≤ η / 4 := by
    calc
      ‖(1 : ℂ) + (t : ℂ) * Complex.I - ρ‖ = ‖-(ρ - ((1 : ℂ) + (t : ℂ) * Complex.I))‖ := by
        congr 1
        ring
      _ = ‖ρ - ((1 : ℂ) + (t : ℂ) * Complex.I)‖ := norm_neg _
      _ ≤ η / 4 := hclose
  have hznorm : ‖z‖ ≤ (5 / 4 : ℝ) * η := by
    dsimp [z]
    calc
      ‖(1 + η) + (t : ℂ) * Complex.I - ρ‖ = ‖(η : ℂ) + ((1 : ℂ) + (t : ℂ) * Complex.I - ρ)‖ := by
        congr 1
        ring
      _ ≤ ‖(η : ℂ)‖ + ‖(1 : ℂ) + (t : ℂ) * Complex.I - ρ‖ := norm_add_le _ _
      _ ≤ η + η / 4 := add_le_add (le_of_eq hηnorm) hcenter
      _ = (5 / 4 : ℝ) * η := by ring
  have hzsq : Complex.normSq z ≤ ((5 / 4 : ℝ) * η) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    apply sq_le_sq'
    · have hnonneg := norm_nonneg z
      nlinarith only [hnonneg, hη]
    · exact hznorm
  have hzpos : 0 < Complex.normSq z := by
    apply Complex.normSq_pos.mpr
    intro hz
    rw [hz] at hzre
    exact (not_lt_of_ge hzre) hη
  rw [one_div, Complex.inv_re]
  apply (div_le_div_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 2) hη) hzpos).2
  have hmul : η * (2 * η) ≤ z.re * (2 * η) := mul_le_mul_of_nonneg_right hzre (by positivity)
  have hprod : ((5 / 4 : ℝ) * η) ^ 2 ≤ z.re * (2 * η) := by nlinarith only [hη, hmul]
  calc
    1 * Complex.normSq z ≤ ((5 / 4 : ℝ) * η) ^ 2 := by simpa only [one_mul] using hzsq
    _ ≤ z.re * (2 * η) := hprod

/--
Inputs: a nontrivial completed Dirichlet `L`-function, a zero within `η / 4` of `1 + it`, and
a positive shift `η`.
Claim: the zero's real Poisson-kernel contribution at `1 + η + it` is at least `1 / (2η)`.
Content: unconditional nonvanishing to the right of one gives `Re ρ < 1`; apply
`re_inv_ge_half_inv_of_near_one_zero` to the geometric closeness hypothesis.
Role: turns a nearby completed zero into a quantitative term for the local multiplicity estimate.
-/
theorem re_inv_ge_half_inv_of_completed_zero_near_one {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {η : ℝ} (hη : 0 < η) {t : ℝ} {ρ : ℂ}
    (hclose : ‖ρ - ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ η / 4) (hzero : χ.completedLFunction ρ = 0) :
    (1 / ((1 + η) + (t : ℂ) * Complex.I - ρ)).re ≥ 1 / (2 * η) := by
  exact re_inv_ge_half_inv_of_near_one_zero hη hclose (completedLFunction_zero_re_lt_one hχ hzero)

/--
Inputs: a primitive nonprincipal character of modulus at least two, a positive shift `η`, and a
rectangle whose completed zeros lie within `η / 4` of `1 + it`.
Claim: the rectangle's analytic multiplicity count is at most `2η` times the real centered
logarithmic derivative at `1 + η + it`.
Content: the unconditional genus expansion has nonnegative terms; each rectangle zero contributes
at least its analytic order divided by `2η` to the shifted reciprocal kernel.
Role: converts local zero multiplicity into a lower bound for the full right-half-plane genus sum.
-/
theorem completedZeroMultiplicityCountInRectangle_le_right_genus_sum {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) {η : ℝ}
    (hη : 0 < η) {t : ℝ} (z w : ℂ)
    (hbox :
      ∀ ρ ∈ dirichletCompletedLFunctionRectangleBox z w,
        ‖ρ - ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ η / 4) :
    completedZeroMultiplicityCountInRectangle χ hχ z w ≤
      2 * η *
        (logDeriv χ.completedLFunction ((1 + η) + (t : ℂ) * Complex.I) -
            logDeriv χ.completedLFunction 0).re := by
  let F : ℂ → ℂ := χ.completedLFunction
  let s : ℂ := (1 + η) + (t : ℂ) * Complex.I
  let D : ℂ → ℤ := MeromorphicOn.divisor F Set.univ
  let cterm : ℂ → ℂ := fun ρ => (D ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)
  let rterm : ℂ → ℝ := fun ρ => (cterm ρ).re
  have hs : 1 < s.re := by
    dsimp [s]
    simp only [Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      mul_zero, mul_one, sub_zero]
    linarith only [hη]
  have hseries : Summable cterm := by
    simpa only [cterm, D, F, s] using (summable_completed_genus_terms_right hq hp hχ hinv hs)
  have hrseries : Summable rterm := by
    apply Summable.of_norm_bounded hseries.norm
    intro ρ
    exact Complex.abs_re_le_norm (cterm ρ)
  have hF : AnalyticOnNhd ℂ F Set.univ := by
    have hdiff := DirichletCharacter.differentiable_completedLFunction hχ
    intro u hu
    exact hdiff.analyticAt u
  have hDnonneg (ρ : ℂ) : 0 ≤ (D ρ : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hF ρ
  have hcast (ρ : ℂ) : (D ρ : ℂ) = ((D ρ : ℝ) : ℂ) := by
    push_cast
    ring
  have hterm (ρ : ℂ) : rterm ρ = (D ρ : ℝ) * ((1 / (s - ρ)).re + (1 / ρ).re) := by
    dsimp [rterm, cterm]
    rw [hcast, Complex.re_ofReal_mul, Complex.add_re]
  have hnonneg (ρ : ℂ) : 0 ≤ rterm ρ := by
    by_cases hD : D ρ = 0
    · simp only [rterm, cterm, D, hD, Int.cast_zero, zero_mul, Complex.zero_re, le_refl]
    · have hz := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hχ hD
      have hrepos := completedLFunction_zero_re_pos hp hinv hz
      have hrelt := completedLFunction_zero_re_lt_one hχ hz
      rw [hterm]
      apply mul_nonneg (hDnonneg ρ)
      apply add_nonneg
      · rw [one_div, Complex.inv_re]
        apply div_nonneg
        · dsimp [s]
          simp only [Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_im, mul_one, mul_zero, sub_zero]
          linarith only [hη, hrelt]
        · exact Complex.normSq_nonneg _
      · rw [one_div, Complex.inv_re]
        exact div_nonneg hrepos.le (Complex.normSq_nonneg _)
  have hglobal : (logDeriv F s - logDeriv F 0).re = ∑' ρ, rterm ρ := by
    rw [completed_centered_logDeriv_eq_genusSum_right hq hp hχ hinv hs, Complex.re_tsum hseries]
  let S := completedZerosInRectangle χ hχ z w
  have hpoint (ρ : ℂ) (hρ : ρ ∈ S) : (analyticOrderNatAt F ρ : ℝ) ≤ 2 * η * rterm ρ := by
    have hmem := mem_completedZerosInRectangle_iff.mp hρ
    have hzero := hmem.2
    have hclose := hbox ρ hmem.1
    have hk : (1 / (s - ρ)).re ≥ 1 / (2 * η) := by
      simpa only [s] using re_inv_ge_half_inv_of_completed_zero_near_one hχ hη hclose hzero
    have hpos := completedLFunction_zero_re_pos hp hinv hzero
    have horder : D ρ = (analyticOrderNatAt F ρ : ℤ) := by
      rw [show D = MeromorphicOn.divisor F Set.univ from rfl,
        MeromorphicOn.AnalyticOnNhd.divisor_apply hF (Set.mem_univ ρ)]
      change
        ((analyticOrderAt F ρ).map (fun k : ℕ => (k : ℤ))).untop₀ =
          ((analyticOrderAt F ρ).toNat : ℤ)
      induction analyticOrderAt F ρ using ENat.recTopCoe
      · rfl
      · rfl
    have hm : 0 ≤ (analyticOrderNatAt F ρ : ℝ) := Nat.cast_nonneg _
    have hd : (D ρ : ℝ) = (analyticOrderNatAt F ρ : ℝ) := by
      rw [horder]
      push_cast
      rfl
    rw [hterm, hd]
    have hkernel : 0 ≤ (1 / ρ).re := by
      rw [one_div, Complex.inv_re]
      exact div_nonneg hpos.le (Complex.normSq_nonneg _)
    have hmain :
      (analyticOrderNatAt F ρ : ℝ) ≤ 2 * η * ((analyticOrderNatAt F ρ : ℝ) * (1 / (s - ρ)).re) := by
      have hden : 0 < 2 * η := mul_pos (by norm_num only : (0 : ℝ) < 2) hη
      have hmul := mul_le_mul_of_nonneg_left hk hm
      have hdiv :
        (analyticOrderNatAt F ρ : ℝ) / (2 * η) ≤
          (analyticOrderNatAt F ρ : ℝ) * (1 / (s - ρ)).re := by
        convert hmul using 1; ring
      calc
        (analyticOrderNatAt F ρ : ℝ) = ((analyticOrderNatAt F ρ : ℝ) / (2 * η)) * (2 * η) := by
          rw [div_mul_cancel₀ _ hden.ne']
        _ ≤ ((analyticOrderNatAt F ρ : ℝ) * (1 / (s - ρ)).re) * (2 * η) :=
          mul_le_mul_of_nonneg_right hdiv hden.le
        _ = _ := by ring
    calc
      (analyticOrderNatAt F ρ : ℝ) ≤ 2 * η * ((analyticOrderNatAt F ρ : ℝ) * (1 / (s - ρ)).re) :=
        hmain
      _ ≤ 2 * η * ((analyticOrderNatAt F ρ : ℝ) * ((1 / (s - ρ)).re + (1 / ρ).re)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hkernel) hm
        · exact mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) hη.le
  have hcount : (∑ ρ ∈ S, (analyticOrderNatAt F ρ : ℝ)) ≤ 2 * η * ∑' ρ, rterm ρ := by
    calc
      (∑ ρ ∈ S, (analyticOrderNatAt F ρ : ℝ)) ≤ ∑ ρ ∈ S, 2 * η * rterm ρ := by
        apply Finset.sum_le_sum
        intro ρ hρ
        exact hpoint ρ hρ
      _ = 2 * η * ∑ ρ ∈ S, rterm ρ := by rw [Finset.mul_sum]
      _ ≤ 2 * η * ∑' ρ, rterm ρ := by
        apply mul_le_mul_of_nonneg_left
        · exact hrseries.sum_le_tsum S (fun ρ _ => hnonneg ρ)
        · exact mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) hη.le
  unfold completedZeroMultiplicityCountInRectangle
  simpa only [S, F, s] using hcount.trans_eq (by rw [hglobal])

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
