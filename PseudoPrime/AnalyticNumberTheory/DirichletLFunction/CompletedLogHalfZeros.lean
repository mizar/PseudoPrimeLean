/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ZeroContribution
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HeightRectangle
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ContourRegularity
public import PseudoPrime.Analysis.FiniteSumExhaustion

/-! # Absolutely convergent completed half-scale zero series -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- The completed divisor contribution Dχ(ρ)x^ρ/ρ², with multiplicity.
The conductor N and positive scale x enter the exact logarithmic formula. -/
noncomputable def completedLogZeroTerm {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ)
    (ρ : ℂ) : ℂ :=
  (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) * (x : ℂ) ^ ρ / ρ ^ 2

/-- The combined half-scale contribution Dχ(ρ)(1-2^(-ρ))x^ρ/ρ².
Keeping this coefficient retains cancellation between the two scales. -/
noncomputable def completedLogHalfZeroTerm {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ)
    (ρ : ℂ) : ℂ :=
  (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) * (1 - (2 : ℂ) ^ (-ρ)) * (x : ℂ) ^ ρ /
    ρ ^ 2

/-- Under GRH for a primitive nonprincipal character and x>0, the completed
logarithmic zero terms are absolutely summable. Use the divisor/norm-square bound. -/
theorem summable_norm_completedLogZeroTerm {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    Summable (fun ρ : ℂ ↦ ‖completedLogZeroTerm χ x ρ‖) := by
  exact
    ((summable_divisor_div_normSq hN hGRH hp hne hinv).mul_left (Real.sqrt x)).congr
      (fun ρ ↦ (norm_completedLogZeroTerm_eq hGRH hp hne hinv hx ρ).symm)

/-- For nonnegative x the combined term equals the difference at x and x/2.
The complex-power quotient identity combines the two contributions before estimation. -/
theorem completedLogHalfZeroTerm_eq_sub {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {x : ℝ}
    (hx : 0 ≤ x) (ρ : ℂ) :
    completedLogHalfZeroTerm χ x ρ =
      completedLogZeroTerm χ x ρ - completedLogZeroTerm χ (x / 2) ρ := by
  have he := Complex.div_cpow_ofReal_nonneg hx (by norm_num only : (0 : ℝ) ≤ 2) ρ
  rw [Complex.ofReal_ofNat] at he
  dsimp only [completedLogHalfZeroTerm, completedLogZeroTerm]
  rw [Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [he, Complex.cpow_neg]
  ring

/-- Under GRH and primitivity, the combined half-zero series is summable.
Subtract the two absolutely convergent completed series. -/
theorem summable_completedLogHalfZeroTerm {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    Summable (completedLogHalfZeroTerm χ x) := by
  have h1 := (summable_norm_completedLogZeroTerm hN hGRH hp hne hinv hx).of_norm
  have h2 :=
    (summable_norm_completedLogZeroTerm hN hGRH hp hne hinv
        (div_pos hx (by norm_num only : (0 : ℝ) < 2))).of_norm
  exact (h1.sub h2).congr (fun ρ ↦ (completedLogHalfZeroTerm_eq_sub χ hx.le ρ).symm)

/-- Under GRH and primitivity, subtracting the two completed zero sums gives
the combined half-zero sum. Absolute convergence justifies the subtraction. -/
theorem tsum_completedLogHalfZeroTerm_eq_sub {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    (∑' ρ : ℂ, completedLogHalfZeroTerm χ x ρ) =
      (∑' ρ : ℂ, completedLogZeroTerm χ x ρ) - ∑' ρ : ℂ, completedLogZeroTerm χ (x / 2) ρ := by
  rw [←
    ((summable_norm_completedLogZeroTerm hN hGRH hp hne hinv hx).of_norm).tsum_sub
      ((summable_norm_completedLogZeroTerm hN hGRH hp hne hinv
          (div_pos hx (by norm_num only : (0 : ℝ) < 2))).of_norm)]
  exact tsum_congr (completedLogHalfZeroTerm_eq_sub χ hx.le)

/-- Finite nontrivial L-zero ledger with nonvanishing gamma factor.
Erase 0 and 1, then filter the finite rectangle singularities; this matches completed zeros. -/
noncomputable def completedLogRectangleLedger {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hne : χ ≠ 1) (z w : ℂ) : Finset ℂ :=
  (((dirichletLFunctionSingularitiesInRectangle χ hne z w).erase 1).erase 0).filter
    (fun ρ ↦ DirichletCharacter.gammaFactor χ ρ ≠ 0)

/-- A positive real part ensures a nonzero character gamma factor.
Use the parity formula and nonvanishing of the real gamma factor. -/
theorem gammaFactor_ne_zero_of_pos_re {N : ℕ} {χ : DirichletCharacter ℂ N} {ρ : ℂ} (hρ : 0 < ρ.re) :
    DirichletCharacter.gammaFactor χ ρ ≠ 0 := by
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos hρ
  · rw [ho.gammaFactor_def]
    exact
      Complex.Gammaℝ_ne_zero_of_re_pos
        (show 0 < (ρ + 1).re by
          rw [Complex.add_re, Complex.one_re]
          linarith only [hρ])

/-- Under primitive GRH a nonzero completed term is a critical-line zero,
distinct from 0 and 1, with nonzero gamma factor and vanishing Dirichlet L-value. -/
theorem completedLogZeroTerm_ne_zero_facts {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    {x : ℝ} {ρ : ℂ} (hnz : completedLogZeroTerm χ x ρ ≠ 0) :
    ρ.re = (1 / 2 : ℝ) ∧
      ρ ≠ 0 ∧ ρ ≠ 1 ∧ DirichletCharacter.gammaFactor χ ρ ≠ 0 ∧ χ.LFunction ρ = 0 := by
  have hD : MeromorphicOn.divisor χ.completedLFunction Set.univ ρ ≠ 0 := by
    intro h
    apply hnz
    simp only [completedLogZeroTerm, h, Int.cast_zero, zero_mul, zero_div]
  have hz := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD
  have hr := completedLFunction_zero_re_eq_half hGRH hp hne hinv hz
  have h0 : ρ ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hr
    norm_num only at hr
  have h1 : ρ ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hr
    norm_num only at hr
  refine ⟨hr, h0, h1, gammaFactor_ne_zero_of_pos_re (by linarith only [hr]), ?_⟩
  rw [dirichletLFunction_eq_completed_div_gammaFactor χ ρ (Or.inl h0), hz, zero_div]

/-- Every nonzero completed term eventually belongs to the height rectangle
ledger. The GRH critical-line support and the cofinal height sequence give membership. -/
theorem eventually_completedLogZeroTerm_mem_height_ledger {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} {ρ : ℂ} (hnz : completedLogZeroTerm χ x ρ ≠ 0) (A : ℕ)
    (hA : 2 ≤ A) :
    ∀ᶠ k : ℕ in Filter.atTop,
      ρ ∈
        completedLogRectangleLedger χ hne (primitiveHeightSeqLowerCorner hN hGRH hp hne hinv A k)
          (primitiveHeightSeqUpperCorner hN hGRH hp hne hinv k) := by
  obtain ⟨hr, h0, h1, hΓ, hz⟩ := completedLogZeroTerm_ne_zero_facts hGRH hp hne hinv hnz
  have hT :=
    (tendsto_primitiveHorizontalHeightSeq_atTop hN hGRH hp hne hinv).eventually_ge_atTop
      (|ρ.im| + 1)
  filter_upwards [hT] with k hk
  obtain ⟨hzr, hzi, hwr, hwi, _, _⟩ := primitiveHeightSeqRectangleFacts hN hGRH hp hne hinv A k hA
  have hAR : (2 : ℝ) ≤ A := by exact_mod_cast hA
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_erase.mpr ⟨h0, Finset.mem_erase.mpr ⟨h1, ?_⟩⟩, hΓ⟩
  apply mem_dirichletLFunctionSingularitiesInRectangle_iff.mpr
  refine ⟨?_, Or.inr (Or.inr hz)⟩
  rw [dirichletCompletedLFunctionRectangleBox, Rectangle.rectangleClosedBox, Complex.mem_reProdIm,
    hzr, hzi, hwr, hwi]
  refine ⟨Set.Icc_subset_uIcc ⟨?_, ?_⟩, Set.Icc_subset_uIcc ⟨?_, ?_⟩⟩
  · dsimp only [primitiveReciprocalLeftRe]
    linarith only [hr, hAR]
  · linarith only [hr]
  · linarith only [hk, neg_abs_le ρ.im]
  · linarith only [hk, le_abs_self ρ.im]

/-- Under primitive GRH, finite completed sums along the height rectangles
converge to the full sum. Apply absolute summability and eventual support membership. -/
theorem tendsto_completedLogZero_height_sum {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (A : ℕ) (hA : 2 ≤ A) :
    Filter.Tendsto
      (fun k : ℕ ↦
        ∑
          ρ ∈
            completedLogRectangleLedger χ hne
              (primitiveHeightSeqLowerCorner hN hGRH hp hne hinv A k)
              (primitiveHeightSeqUpperCorner hN hGRH hp hne hinv k),
          completedLogZeroTerm χ x ρ)
      Filter.atTop (nhds (∑' ρ : ℂ, completedLogZeroTerm χ x ρ)) := by
  exact
    Analysis.tendsto_sum_of_eventually_mem_support _
      (summable_norm_completedLogZeroTerm hN hGRH hp hne hinv hx) _
      (fun _ hnz ↦ eventually_completedLogZeroTerm_mem_height_ledger hN hGRH hp hne hinv hnz A hA)

/-- The completed half-scale coefficient multiplied by exp(i Im(ρ)v).
Under GRH its product with sqrt(x) equals the half-zero term at v=log(x). -/
noncomputable def completedLogHalfPhaseTerm {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (v : ℝ)
    (ρ : ℂ) : ℂ :=
  (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) * (1 - (2 : ℂ) ^ (-ρ)) / ρ ^ 2 *
    Complex.exp ((ρ.im * v : ℝ) * Complex.I)

/-- Under individual GRH, bound each completed half-phase term by its zero multiplicity
times an inverse quadratic height weight. The hypotheses are a primitive nonprincipal
character and its inverse being nonprincipal. The estimate feeds local zero counts into
an absolute tail bound; the divisor-zero case vanishes directly, while supported terms
lie on the critical line. The factor eight absorbs both the half-scale coefficient and
the denominator comparison. -/
theorem norm_completedLogHalfPhaseTerm_le_eight_quadratic_weight {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (v : ℝ) (ρ : ℂ) :
    ‖completedLogHalfPhaseTerm χ v ρ‖ ≤
      8 * (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) / (1 + ρ.im ^ 2) := by
  let D := MeromorphicOn.divisor χ.completedLFunction Set.univ ρ
  by_cases hD₀ : D = 0
  · simp only [completedLogHalfPhaseTerm, D, hD₀, Int.cast_zero, zero_mul, zero_div, norm_zero]
    exact div_nonneg (by norm_num only) (by nlinarith only [sq_nonneg ρ.im])
  · have hr :=
      completedLFunction_zero_re_eq_half_of_dirichletRH hRH hp hinv
        (dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD₀)
    have hD : 0 ≤ (D : ℝ) := by
      have ha : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
        (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
      exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ
    have hpw : ‖(2 : ℂ) ^ (-ρ)‖ ≤ 1 := by
      change ‖(Complex.ofReal (2 : ℝ)) ^ (-ρ)‖ ≤ 1
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num only : (0 : ℝ) < 2), Complex.neg_re, hr]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num only) (by norm_num only)
    have hsub : ‖(1 : ℂ) - (2 : ℂ) ^ (-ρ)‖ ≤ 2 := by
      have h := norm_sub_le (1 : ℂ) ((2 : ℂ) ^ (-ρ))
      have hsum : ‖(1 : ℂ)‖ + ‖(2 : ℂ) ^ (-ρ)‖ ≤ 2 := by
        rw [norm_one]
        linarith only [hpw]
      exact h.trans hsum
    have hden : ‖ρ ^ 2‖ = 1 / 4 + ρ.im ^ 2 := by
      rw [norm_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hr]
      ring
    have hexp : ‖Complex.exp ((ρ.im * v : ℝ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp_ofReal_mul_I]
    have hratio : 2 / (1 / 4 + ρ.im ^ 2) ≤ 8 / (1 + ρ.im ^ 2) := by
      have hnum : 0 < 1 / 4 + ρ.im ^ 2 := by positivity
      have hdenom : 0 < 1 + ρ.im ^ 2 := by positivity
      rw [div_le_div_iff₀ hnum hdenom]
      nlinarith only [sq_nonneg ρ.im]
    dsimp only [completedLogHalfPhaseTerm]
    rw [norm_mul, norm_div, norm_mul, Complex.norm_intCast, abs_of_nonneg hD, hden, hexp]
    have hcoef : (D : ℝ) * ‖(1 : ℂ) - (2 : ℂ) ^ (-ρ)‖ ≤ (D : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left hsub hD
    have hmain := div_le_div_of_nonneg_right hcoef (by positivity : 0 ≤ (1 / 4 + ρ.im ^ 2 : ℝ))
    calc
      (D : ℝ) * ‖(1 : ℂ) - (2 : ℂ) ^ (-ρ)‖ / (1 / 4 + ρ.im ^ 2) * 1 ≤
          (D : ℝ) * 2 / (1 / 4 + ρ.im ^ 2) :=
        by simpa only [mul_one] using hmain
      _ = (D : ℝ) * (2 / (1 / 4 + ρ.im ^ 2)) := by ring
      _ ≤ (D : ℝ) * (8 / (1 + ρ.im ^ 2)) := mul_le_mul_of_nonneg_left hratio hD
      _ = 8 * (D : ℝ) / (1 + ρ.im ^ 2) := by ring

/-- For x>0 and Re(ρ)=1/2, write x^ρ as sqrt(x) times its oscillatory phase.
Expand the complex exponential without estimating the phase. -/
theorem cpow_eq_sqrt_mul_phase_of_re_half {x : ℝ} (hx : 0 < x) {ρ : ℂ} (hr : ρ.re = (1 / 2 : ℝ)) :
    (x : ℂ) ^ ρ = (Real.sqrt x : ℂ) * Complex.exp ((ρ.im * Real.log x : ℝ) * Complex.I) := by
  have hs : (Real.sqrt x : ℂ) = Complex.exp ((Real.log x / 2 : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx, Complex.ofReal_exp]
    congr 2
    ring
  have he :
    (Real.log x : ℂ) * ρ =
      ((Real.log x / 2 : ℝ) : ℂ) + ((ρ.im * Real.log x : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.I_re,
        Complex.I_im, hr]
      ring
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im, Complex.I_re,
        Complex.I_im]
      ring
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le,
    he, Complex.exp_add, hs]

/-- Under primitive GRH each completed half-zero term factors as sqrt(x)
times its phase term. Off the divisor support both sides vanish. -/
theorem completedLogHalfZeroTerm_eq_sqrt_mul_phase {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    {x : ℝ} (hx : 0 < x) (ρ : ℂ) :
    completedLogHalfZeroTerm χ x ρ =
      (Real.sqrt x : ℂ) * completedLogHalfPhaseTerm χ (Real.log x) ρ := by
  by_cases hD : MeromorphicOn.divisor χ.completedLFunction Set.univ ρ = 0
  · simp only [completedLogHalfZeroTerm, completedLogHalfPhaseTerm, hD, Int.cast_zero, zero_mul,
      zero_div, mul_zero]
  · have hz := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD
    have hr := completedLFunction_zero_re_eq_half hGRH hp hne hinv hz
    dsimp only [completedLogHalfZeroTerm, completedLogHalfPhaseTerm]
    rw [cpow_eq_sqrt_mul_phase_of_re_half hx hr]
    ring

/-- Under primitive GRH the phase series is absolutely summable at every
real v. Recover it from the convergent half-zero series at x=exp(v). -/
theorem summable_completedLogHalfPhaseTerm {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (v : ℝ) : Summable (completedLogHalfPhaseTerm χ v) := by
  have hs :=
    (summable_completedLogHalfZeroTerm hN hGRH hp hne hinv (Real.exp_pos v)).mul_left
      ((Real.sqrt (Real.exp v) : ℂ)⁻¹)
  apply hs.congr
  intro ρ
  rw [completedLogHalfZeroTerm_eq_sqrt_mul_phase hGRH hp hne hinv (Real.exp_pos v), Real.log_exp, ←
    mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (Real.exp_pos v)).ne'), one_mul]

/-- The signed real completed-zero phase at logarithmic scale v.
It is minus the real part of the full phase series; no absolute value is taken. -/
noncomputable def logarithmicHalfPhase {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (v : ℝ) :
    ℝ :=
  -(∑' ρ : ℂ, completedLogHalfPhaseTerm χ v ρ).re

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
