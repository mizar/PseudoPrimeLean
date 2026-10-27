/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.LocalZeroCounting
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.CompletedGenusZeroSums
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.LocalZeroTuran

/-! # Uniform local zero count bounds -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/-- For a primitive character, a rectangle of zeros within `η / 4` of `1 + it` has a
multiplicity bound from the right-half-plane genus sum. The Euler estimate contributes the
constant `8`; the remaining terms isolate the gamma growth and the central logarithmic derivative.
For `η ≤ 1 / 2`, the gamma contribution has one constant uniform in the shift, modulus, and
character. -/
theorem exists_completedZeroMultiplicityCountInRectangle_le_euler_gamma_center {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2) {t : ℝ} (z w : ℂ)
    (hbox :
      ∀ ρ ∈ dirichletCompletedLFunctionRectangleBox z w,
        ‖ρ - ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ η / 4) :
    ∃ A : ℝ,
      0 < A ∧
        completedZeroMultiplicityCountInRectangle χ hχ z w ≤
          8 + 2 * η * (A * (Real.log (4 + |t|) + 1) + |(logDeriv χ.completedLFunction 0).re|) := by
  obtain ⟨A, hA, hderiv⟩ := exists_uniform_norm_completed_logDeriv_small_shift_bound
  let s : ℂ := ((1 + η : ℝ) : ℂ) + Complex.I * t
  have hgenus :=
    completedZeroMultiplicityCountInRectangle_le_right_genus_sum hq hχ hp hinv hη z w hbox
  have hnorm := hderiv χ hχ hη hη1 t
  have hPoints : (1 + (η : ℂ) + (t : ℂ) * Complex.I) = (((1 + η : ℝ) : ℂ) + Complex.I * t) := by
    rw [Complex.ofReal_add, Complex.ofReal_one]
    ring
  have hre :
    (logDeriv χ.completedLFunction s - logDeriv χ.completedLFunction 0).re ≤
      4 / η + A * (Real.log (4 + |t|) + 1) + |(logDeriv χ.completedLFunction 0).re| := by
    have hnorm' : ‖logDeriv χ.completedLFunction s‖ ≤ 4 / η + A * (Real.log (4 + |t|) + 1) := by
      simpa only [s] using hnorm
    rw [Complex.sub_re]
    have hpoint : (logDeriv χ.completedLFunction s).re ≤ ‖logDeriv χ.completedLFunction s‖ :=
      Complex.re_le_norm _
    have hcenter : -(logDeriv χ.completedLFunction 0).re ≤ |(logDeriv χ.completedLFunction 0).re| :=
      neg_le_abs _
    linarith only [hpoint, hcenter, hnorm']
  have hmul := mul_le_mul_of_nonneg_left hre (by positivity : 0 ≤ 2 * η)
  have heq :
    2 * η * (4 / η + A * (Real.log (4 + |t|) + 1) + |(logDeriv χ.completedLFunction 0).re|) =
      8 + 2 * η * (A * (Real.log (4 + |t|) + 1) + |(logDeriv χ.completedLFunction 0).re|) := by
    field_simp [ne_of_gt hη]
    ring
  refine ⟨A, hA, ?_⟩
  calc
    completedZeroMultiplicityCountInRectangle χ hχ z w ≤
        2 * η * (logDeriv χ.completedLFunction s - logDeriv χ.completedLFunction 0).re :=
      by simpa only [s, hPoints] using hgenus
    _ ≤ 2 * η * (4 / η + A * (Real.log (4 + |t|) + 1) + |(logDeriv χ.completedLFunction 0).re|) :=
      hmul
    _ = 8 + 2 * η * (A * (Real.log (4 + |t|) + 1) + |(logDeriv χ.completedLFunction 0).re|) := heq

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For primitive nonprincipal characters, the local multiplicity bound has no value at the
central point. The functional equation at `2` replaces the logarithmic derivative at `-1` by
the conductor logarithm and a fixed-shift bound for the inverse character.
Inputs: a rectangle within `η / 4` of `1 + it`, with `0 < η ≤ 1 / 2`.
Claim: the multiplicity is bounded by an absolute height term, the conductor logarithm, and
logarithmic height.
Role: supplies the unconditional local multiplicity estimate for the log-free density argument. -/
theorem exists_completedZeroMultiplicityCountInRectangle_le_euler_gamma_minus_one {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2) {t : ℝ} (z w : ℂ)
    (hbox :
      ∀ ρ ∈ dirichletCompletedLFunctionRectangleBox z w,
        ‖ρ - ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ η / 4) :
    ∃ A B : ℝ,
      0 < A ∧
        0 < B ∧
        completedZeroMultiplicityCountInRectangle χ hχ z w ≤
          8 + 2 * η * (A * (Real.log (4 + |t|) + 1) + Real.log q + 4 + B * (Real.log 4 + 1)) := by
  obtain ⟨A, hA, hderiv⟩ := exists_uniform_norm_completed_logDeriv_small_shift_bound
  obtain ⟨B, hB, hbase⟩ :=
    exists_norm_completed_logDeriv_small_shift_bound (r := 1) (by norm_num only) (by norm_num only)
  let s : ℂ := ((1 + η : ℝ) : ℂ) + Complex.I * t
  have hgenus :=
    completedZeroMultiplicityCountInRectangle_le_minus_one_genus_sum hq hχ hp hinv hη z w hbox
  have hnorm := hderiv χ hχ hη hη1 t
  let u : ℂ := ((1 + 1 : ℝ) : ℂ) + Complex.I * (0 : ℝ)
  have htwo : ‖logDeriv χ⁻¹.completedLFunction u‖ ≤ 4 + B * (Real.log 4 + 1) := by
    have hh := hbase χ⁻¹ hinv 0
    simpa only [u, abs_zero, div_one, add_zero] using hh
  have huEq : u = (2 : ℂ) := by
    dsimp only [u]
    rw [Complex.ofReal_zero, mul_zero, add_zero]
    rw [Complex.ofReal_add, Complex.ofReal_one]
    norm_num only
  have huRe : (1 : ℝ) ≤ u.re := by
    rw [huEq]
    change (1 : ℝ) ≤ 2
    norm_num only
  have hF2 : χ⁻¹.completedLFunction u ≠ 0 := completedLFunction_ne_zero_of_one_le_re hinv huRe
  have hfe := completedLFunction_logDeriv_functionalEquation_at hp hχ (s := u) hF2
  have hone : (1 : ℂ) - u = -1 := by
    rw [huEq]; norm_num only
  rw [hone] at hfe
  have hqreal : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast le_trans (by norm_num : 1 ≤ 2) hq
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hqreal
  have hlognorm : ‖Complex.log (q : ℂ)‖ = Real.log q := by
    rw [← Complex.natCast_log, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogq]
  have hcenternorm :
    ‖logDeriv χ.completedLFunction (-1)‖ ≤ Real.log q + 4 + B * (Real.log 4 + 1) := by
    calc
      ‖logDeriv χ.completedLFunction (-1)‖ = ‖-logDeriv χ.completedLFunction (-1)‖ := by
        rw [norm_neg]
      _ = ‖Complex.log (q : ℂ) + logDeriv χ⁻¹.completedLFunction u‖ := by rw [hfe]
      _ ≤ ‖Complex.log (q : ℂ)‖ + ‖logDeriv χ⁻¹.completedLFunction u‖ := norm_add_le _ _
      _ ≤ Real.log q + (4 + B * (Real.log 4 + 1)) := add_le_add hlognorm.le htwo
      _ = _ := by ring
  have hcenterre :
    |(logDeriv χ.completedLFunction (-1)).re| ≤ Real.log q + 4 + B * (Real.log 4 + 1) :=
    (Complex.abs_re_le_norm _).trans hcenternorm
  have hPoints : (1 + (η : ℂ) + (t : ℂ) * Complex.I) = (((1 + η : ℝ) : ℂ) + Complex.I * t) := by
    rw [Complex.ofReal_add, Complex.ofReal_one]
    ring
  have hre :
    (logDeriv χ.completedLFunction s - logDeriv χ.completedLFunction (-1)).re ≤
      4 / η + A * (Real.log (4 + |t|) + 1) + Real.log q + 4 + B * (Real.log 4 + 1) := by
    have hnorm' : ‖logDeriv χ.completedLFunction s‖ ≤ 4 / η + A * (Real.log (4 + |t|) + 1) := by
      simpa only [s] using hnorm
    rw [Complex.sub_re]
    have hpoint : (logDeriv χ.completedLFunction s).re ≤ ‖logDeriv χ.completedLFunction s‖ :=
      Complex.re_le_norm _
    have hcenter :
      -(logDeriv χ.completedLFunction (-1)).re ≤ |(logDeriv χ.completedLFunction (-1)).re| :=
      neg_le_abs _
    linarith only [hpoint, hcenter, hnorm', hcenterre]
  have hmul := mul_le_mul_of_nonneg_left hre (by positivity : 0 ≤ 2 * η)
  have heq :
    2 * η * (4 / η + A * (Real.log (4 + |t|) + 1) + Real.log q + 4 + B * (Real.log 4 + 1)) =
      8 + 2 * η * (A * (Real.log (4 + |t|) + 1) + Real.log q + 4 + B * (Real.log 4 + 1)) := by
    field_simp [ne_of_gt hη]
    ring
  refine ⟨A, B, hA, hB, ?_⟩
  calc
    completedZeroMultiplicityCountInRectangle χ hχ z w ≤
        2 * η * (logDeriv χ.completedLFunction s - logDeriv χ.completedLFunction (-1)).re :=
      by simpa only [s, hPoints] using hgenus
    _ ≤ 2 * η * (4 / η + A * (Real.log (4 + |t|) + 1) + Real.log q + 4 + B * (Real.log 4 + 1)) :=
      hmul
    _ = 8 + 2 * η * (A * (Real.log (4 + |t|) + 1) + Real.log q + 4 + B * (Real.log 4 + 1)) := heq

/--
Inputs: the hypotheses of the local rectangle count, uniformly over primitive nonprincipal
characters, conductors, local scales, and heights.
Claim: two positive constants bound every such local count by the same Euler and gamma estimate.
Proof: choose the uniform shifted logarithmic-derivative bounds once, then repeat the genus,
functional-equation, and Euler estimates with those fixed constants.
Role: exposes the absolute constants needed when local zero counts are summed over a finite family.
-/
theorem exists_uniform_completedZeroMultiplicityCountInRectangle_le_euler_gamma_minus_one :
    ∃ A B : ℝ,
      0 < A ∧
        0 < B ∧
        ∀ {q : ℕ} [NeZero q] (_hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
          (_hp : χ.IsPrimitive) (_hinv : χ⁻¹ ≠ 1) {η : ℝ} (_hη : 0 < η) (_hη1 : η ≤ 1 / 2) {t : ℝ}
          (z w : ℂ)
          (_hbox :
            ∀ ρ ∈ dirichletCompletedLFunctionRectangleBox z w,
              ‖ρ - ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ≤ η / 4),
          completedZeroMultiplicityCountInRectangle χ hχ z w ≤
            8 + 2 * η * (A * (Real.log (4 + |t|) + 1) + Real.log q + 4 + B * (Real.log 4 + 1)) := by
  obtain ⟨A, hA, hderiv⟩ := exists_uniform_norm_completed_logDeriv_small_shift_bound
  obtain ⟨B, hB, hbase⟩ :=
    exists_norm_completed_logDeriv_small_shift_bound (r := 1) (by norm_num only) (by norm_num only)
  refine ⟨A, B, hA, hB, ?_⟩
  intro q _ hq χ hχ hp hinv η hη hη1 t z w hbox
  let s : ℂ := ((1 + η : ℝ) : ℂ) + Complex.I * t
  have hgenus :=
    completedZeroMultiplicityCountInRectangle_le_minus_one_genus_sum hq hχ hp hinv hη z w hbox
  have hnorm := hderiv χ hχ hη hη1 t
  let u : ℂ := ((1 + 1 : ℝ) : ℂ) + Complex.I * (0 : ℝ)
  have htwo : ‖logDeriv χ⁻¹.completedLFunction u‖ ≤ 4 + B * (Real.log 4 + 1) := by
    have hh := hbase χ⁻¹ hinv 0
    simpa only [u, abs_zero, div_one, add_zero] using hh
  have huEq : u = (2 : ℂ) := by
    dsimp only [u]
    rw [Complex.ofReal_zero, mul_zero, add_zero]
    rw [Complex.ofReal_add, Complex.ofReal_one]
    norm_num only
  have huRe : (1 : ℝ) ≤ u.re := by
    rw [huEq]
    change (1 : ℝ) ≤ 2
    norm_num only
  have hF2 : χ⁻¹.completedLFunction u ≠ 0 := completedLFunction_ne_zero_of_one_le_re hinv huRe
  have hfe := completedLFunction_logDeriv_functionalEquation_at hp hχ (s := u) hF2
  have hone : (1 : ℂ) - u = -1 := by
    rw [huEq]; norm_num only
  rw [hone] at hfe
  have hqreal : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast le_trans (by norm_num : 1 ≤ 2) hq
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hqreal
  have hlognorm : ‖Complex.log (q : ℂ)‖ = Real.log q := by
    rw [← Complex.natCast_log, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogq]
  have hcenternorm :
    ‖logDeriv χ.completedLFunction (-1)‖ ≤ Real.log q + 4 + B * (Real.log 4 + 1) := by
    calc
      ‖logDeriv χ.completedLFunction (-1)‖ = ‖-logDeriv χ.completedLFunction (-1)‖ := by
        rw [norm_neg]
      _ = ‖Complex.log (q : ℂ) + logDeriv χ⁻¹.completedLFunction u‖ := by rw [hfe]
      _ ≤ ‖Complex.log (q : ℂ)‖ + ‖logDeriv χ⁻¹.completedLFunction u‖ := norm_add_le _ _
      _ ≤ Real.log q + (4 + B * (Real.log 4 + 1)) := add_le_add hlognorm.le htwo
      _ = _ := by ring
  have hcenterre :
    |(logDeriv χ.completedLFunction (-1)).re| ≤ Real.log q + 4 + B * (Real.log 4 + 1) :=
    (Complex.abs_re_le_norm _).trans hcenternorm
  have hPoints : (1 + (η : ℂ) + (t : ℂ) * Complex.I) = (((1 + η : ℝ) : ℂ) + Complex.I * t) := by
    rw [Complex.ofReal_add, Complex.ofReal_one]
    ring
  have hre :
    (logDeriv χ.completedLFunction s - logDeriv χ.completedLFunction (-1)).re ≤
      4 / η + A * (Real.log (4 + |t|) + 1) + Real.log q + 4 + B * (Real.log 4 + 1) := by
    have hnorm' : ‖logDeriv χ.completedLFunction s‖ ≤ 4 / η + A * (Real.log (4 + |t|) + 1) := by
      simpa only [s] using hnorm
    rw [Complex.sub_re]
    have hpoint : (logDeriv χ.completedLFunction s).re ≤ ‖logDeriv χ.completedLFunction s‖ :=
      Complex.re_le_norm _
    have hcenter :
      -(logDeriv χ.completedLFunction (-1)).re ≤ |(logDeriv χ.completedLFunction (-1)).re| :=
      neg_le_abs _
    linarith only [hpoint, hcenter, hnorm', hcenterre]
  have hmul := mul_le_mul_of_nonneg_left hre (by positivity : 0 ≤ 2 * η)
  have heq :
    2 * η * (4 / η + A * (Real.log (4 + |t|) + 1) + Real.log q + 4 + B * (Real.log 4 + 1)) =
      8 + 2 * η * (A * (Real.log (4 + |t|) + 1) + Real.log q + 4 + B * (Real.log 4 + 1)) := by
    field_simp [ne_of_gt hη]
    ring
  calc
    completedZeroMultiplicityCountInRectangle χ hχ z w ≤
        2 * η * (logDeriv χ.completedLFunction s - logDeriv χ.completedLFunction (-1)).re :=
      by simpa only [s, hPoints] using hgenus
    _ ≤ 2 * η * (4 / η + A * (Real.log (4 + |t|) + 1) + Real.log q + 4 + B * (Real.log 4 + 1)) :=
      hmul
    _ = 8 + 2 * η * (A * (Real.log (4 + |t|) + 1) + Real.log q + 4 + B * (Real.log 4 + 1)) := heq

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For primitive nonprincipal characters, a rectangle close to `1 + it` has multiplicity
bounded by one plus its radius times the logarithm of the conductor-height product.
Inputs: the hypotheses and rectangle containment from
`exists_completedZeroMultiplicityCountInRectangle_le_euler_gamma_minus_one`.
Claim: there is a positive constant `C` such that the count is at most
`C * (1 + η * log(q * (|t| + 3)))`.
Proof: compare `log(4 + |t|)` with twice `log(|t| + 3)`, then absorb fixed terms using
`η ≤ 1 / 2`.
Role: gives the local multiplicity estimate in the scale required by the zero-window incidence
argument. -/
theorem exists_completedZeroMultiplicityCountInRectangle_le_local_log_bound {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2) {t : ℝ} (z w : ℂ)
    (hbox :
      ∀ ρ ∈ dirichletCompletedLFunctionRectangleBox z w,
        ‖ρ - ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ η / 4) :
    ∃ C : ℝ,
      0 < C ∧
        completedZeroMultiplicityCountInRectangle χ hχ z w ≤
          C * (1 + η * Real.log ((q : ℝ) * (|t| + 3))) := by
  obtain ⟨A, B, hA, hB, hbase⟩ :=
    exists_completedZeroMultiplicityCountInRectangle_le_euler_gamma_minus_one hq hχ hp hinv hη hη1 z
      w hbox
  let H : ℝ := Real.log (|t| + 3)
  let L : ℝ := Real.log (q : ℝ) + H
  let K : ℝ := A + 4 + B * (Real.log 4 + 1)
  let D : ℝ := 2 * A + 1
  have ht0 : 0 ≤ |t| := abs_nonneg t
  have hheight : 1 ≤ |t| + 3 := by nlinarith only [ht0]
  have hH : 0 ≤ H := by
    dsimp only [H]
    exact Real.log_nonneg hheight
  have hqNat : 1 ≤ q := by omega
  have hqreal : 1 ≤ (q : ℝ) := by exact_mod_cast hqNat
  have hqpos : 0 < (q : ℝ) := lt_of_lt_of_le (by norm_num) hqreal
  have hqlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqreal
  have hL : 0 ≤ L := by
    dsimp only [L, H]
    exact add_nonneg hqlog (Real.log_nonneg hheight)
  have hmulog : Real.log ((q : ℝ) * (|t| + 3)) = Real.log (q : ℝ) + Real.log (|t| + 3) := by
    exact Real.log_mul (ne_of_gt hqpos) (ne_of_gt (by nlinarith only [ht0]))
  have hheightSquared : 4 + |t| ≤ (|t| + 3) ^ 2 := by nlinarith only [ht0, sq_nonneg |t|]
  have hlogHeight : Real.log (4 + |t|) ≤ 2 * H := by
    have hlog := Real.log_le_log (by nlinarith only [ht0]) hheightSquared
    rw [Real.log_pow] at hlog
    norm_num only at hlog
    simpa only [H] using hlog
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num only)
  have hK : 0 < K := by
    dsimp only [K]
    nlinarith only [hA, hB, hlog4]
  have hD : 0 < D := by
    dsimp only [D]
    nlinarith only [hA]
  have hAlogq : 0 ≤ A * Real.log (q : ℝ) := mul_nonneg (le_of_lt hA) hqlog
  have hinner :
    A * (Real.log (4 + |t|) + 1) + Real.log (q : ℝ) + 4 + B * (Real.log 4 + 1) ≤ D * L + K := by
    have hweighted := mul_le_mul_of_nonneg_left (add_le_add_right hlogHeight 1) (le_of_lt hA)
    dsimp only [D, L, K, H]
    nlinarith only [hA, hqlog, hH, hlogHeight, hweighted, hAlogq]
  have hηK : 2 * η * K ≤ K := by
    have hηle : 2 * η ≤ 1 := by linarith only [hη1]
    nlinarith only [hK, hηle]
  have hηL : 0 ≤ η * L := mul_nonneg (le_of_lt hη) hL
  let C : ℝ := 8 + K + 2 * D
  have hC : 0 < C := by
    dsimp only [C]
    linarith only [hK, hD]
  have hconstant : 8 + K ≤ C := by
    dsimp only [C]
    linarith only [hD]
  have hcoefficient : 2 * D ≤ C := by
    dsimp only [C]
    linarith only [hK]
  refine ⟨C, hC, ?_⟩
  calc
    completedZeroMultiplicityCountInRectangle χ hχ z w ≤
        8 + 2 * η * (A * (Real.log (4 + |t|) + 1) + Real.log (q : ℝ) + 4 + B * (Real.log 4 + 1)) :=
      hbase
    _ ≤ 8 + 2 * η * (D * L + K) := by
      exact add_le_add (le_refl 8) (mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ 2 * η))
    _ = 8 + 2 * η * K + 2 * D * (η * L) := by ring
    _ ≤ (8 + K) + (2 * D) * (η * L) := by exact add_le_add (by linarith only [hηK]) (le_refl _)
    _ ≤ C + C * (η * L) := by
      exact add_le_add hconstant (mul_le_mul_of_nonneg_right hcoefficient hηL)
    _ = C * (1 + η * Real.log ((q : ℝ) * (|t| + 3))) := by
      rw [hmulog]
      dsimp only [L, H]
      ring

/--
Inputs: the hypotheses of the local rectangle count, uniformly over primitive nonprincipal
characters, conductors, local scales, and heights.
Claim: one positive absolute constant bounds every local count by `1 + η * log(q * (|t| + 3))`.
Proof: use the uniform Euler and gamma constants from the preceding rectangle estimate and the
same logarithmic comparison, choosing the final constant before the family parameters.
Role: permits the local zero-window bound to be summed without conductor-dependent constants.
-/
theorem exists_uniform_completedZeroMultiplicityCountInRectangle_le_local_log_bound :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q] (_hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
          (_hp : χ.IsPrimitive) (_hinv : χ⁻¹ ≠ 1) {η : ℝ} (_hη : 0 < η) (_hη1 : η ≤ 1 / 2) {t : ℝ}
          (z w : ℂ)
          (_hbox :
            ∀ ρ ∈ dirichletCompletedLFunctionRectangleBox z w,
              ‖ρ - ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ≤ η / 4),
          completedZeroMultiplicityCountInRectangle χ hχ z w ≤
            C * (1 + η * Real.log ((q : ℝ) * (|t| + 3))) := by
  obtain ⟨A, B, hA, hB, hbase⟩ :=
    exists_uniform_completedZeroMultiplicityCountInRectangle_le_euler_gamma_minus_one
  let K : ℝ := A + 4 + B * (Real.log 4 + 1)
  let D : ℝ := 2 * A + 1
  let C : ℝ := 8 + K + 2 * D
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num only)
  have hK : 0 < K := by
    dsimp only [K]
    nlinarith only [hA, hB, hlog4]
  have hD : 0 < D := by
    dsimp only [D]
    nlinarith only [hA]
  have hC : 0 < C := by
    dsimp only [C]
    linarith only [hK, hD]
  refine ⟨C, hC, ?_⟩
  intro q _ hq χ hχ hp hinv η hη hη1 t z w hbox
  have hbase := hbase hq hχ hp hinv hη hη1 z w hbox
  let H : ℝ := Real.log (|t| + 3)
  let L : ℝ := Real.log (q : ℝ) + H
  have ht0 : 0 ≤ |t| := abs_nonneg t
  have hheight : 1 ≤ |t| + 3 := by nlinarith only [ht0]
  have hH : 0 ≤ H := by
    dsimp only [H]
    exact Real.log_nonneg hheight
  have hqNat : 1 ≤ q := by omega
  have hqreal : 1 ≤ (q : ℝ) := by exact_mod_cast hqNat
  have hqpos : 0 < (q : ℝ) := lt_of_lt_of_le (by norm_num only) hqreal
  have hqlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqreal
  have hL : 0 ≤ L := by
    dsimp only [L, H]
    exact add_nonneg hqlog (Real.log_nonneg hheight)
  have hmulog : Real.log ((q : ℝ) * (|t| + 3)) = Real.log (q : ℝ) + Real.log (|t| + 3) := by
    exact Real.log_mul (ne_of_gt hqpos) (ne_of_gt (by nlinarith only [ht0]))
  have hheightSquared : 4 + |t| ≤ (|t| + 3) ^ 2 := by nlinarith only [ht0, sq_nonneg |t|]
  have hlogHeight : Real.log (4 + |t|) ≤ 2 * H := by
    have hlog := Real.log_le_log (by nlinarith only [ht0]) hheightSquared
    rw [Real.log_pow] at hlog
    norm_num only at hlog
    simpa only [H] using hlog
  have hAlogq : 0 ≤ A * Real.log (q : ℝ) := mul_nonneg (le_of_lt hA) hqlog
  have hinner :
    A * (Real.log (4 + |t|) + 1) + Real.log (q : ℝ) + 4 + B * (Real.log 4 + 1) ≤ D * L + K := by
    have hweighted := mul_le_mul_of_nonneg_left (add_le_add_right hlogHeight 1) (le_of_lt hA)
    dsimp only [D, L, K, H]
    nlinarith only [hA, hqlog, hH, hlogHeight, hweighted, hAlogq]
  have hηK : 2 * η * K ≤ K := by
    have hηle : 2 * η ≤ 1 := by linarith only [hη1]
    nlinarith only [hK, hηle]
  have hηL : 0 ≤ η * L := mul_nonneg (le_of_lt hη) hL
  have hconstant : 8 + K ≤ C := by
    dsimp only [C]
    linarith only [hD]
  have hcoefficient : 2 * D ≤ C := by
    dsimp only [C]
    linarith only [hK]
  calc
    completedZeroMultiplicityCountInRectangle χ hχ z w ≤
        8 + 2 * η * (A * (Real.log (4 + |t|) + 1) + Real.log (q : ℝ) + 4 + B * (Real.log 4 + 1)) :=
      hbase
    _ ≤ 8 + 2 * η * (D * L + K) := by
      exact add_le_add (le_refl 8) (mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ 2 * η))
    _ = 8 + 2 * η * K + 2 * D * (η * L) := by ring
    _ ≤ (8 + K) + (2 * D) * (η * L) := by exact add_le_add (by linarith only [hηK]) (le_refl _)
    _ ≤ C + C * (η * L) := by
      exact add_le_add hconstant (mul_le_mul_of_nonneg_right hcoefficient hηL)
    _ = C * (1 + η * Real.log ((q : ℝ) * (|t| + 3))) := by
      rw [hmulog]
      dsimp only [L, H]
      ring

/-- The absolute constant chosen by the uniform local logarithmic zero-count estimate. -/
noncomputable def completedZeroLocalLogBoundConstant : ℝ :=
  Classical.choose exists_uniform_completedZeroMultiplicityCountInRectangle_le_local_log_bound

/-- The uniform local logarithmic zero-count constant is positive. -/
theorem completedZeroLocalLogBoundConstant_pos : 0 < completedZeroLocalLogBoundConstant :=
  (Classical.choose_spec
      exists_uniform_completedZeroMultiplicityCountInRectangle_le_local_log_bound).1

/-- Apply the same absolute local logarithmic zero-count constant to any admissible rectangle. -/
theorem completedZeroMultiplicityCountInRectangle_le_uniform_local_log_bound {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2) {t : ℝ} (z w : ℂ)
    (hbox :
      ∀ ρ ∈ dirichletCompletedLFunctionRectangleBox z w,
        ‖ρ - ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ≤ η / 4) :
    completedZeroMultiplicityCountInRectangle χ hχ z w ≤
      completedZeroLocalLogBoundConstant * (1 + η * Real.log ((q : ℝ) * (|t| + 3))) := by
  exact
    (Classical.choose_spec
          exists_uniform_completedZeroMultiplicityCountInRectangle_le_local_log_bound).2
      hq hχ hp hinv hη hη1 z w hbox

/--
Inputs: an admissible primitive-character rectangle at conductor `q` and height `t`.

Claim: its multiplicity-weighted zero count is bounded by the natural ceiling of the explicit
uniform logarithmic estimate.

Proof: apply the uniform local estimate and use the defining upper-bound property of `Nat.ceil`.

Role: converts the analytic count estimate into the natural cap used by the fixed-multiple power
sum theorem.
-/
theorem completedZeroMultiplicityCountInRectangle_le_nat_ceil_uniform_local_log_bound {q : ℕ}
    [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive)
    (hinv : χ⁻¹ ≠ 1) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2) {t : ℝ} (z w : ℂ)
    (hbox :
      ∀ ρ ∈ dirichletCompletedLFunctionRectangleBox z w,
        ‖ρ - ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ≤ η / 4) :
    completedZeroMultiplicityCountInRectangle χ hχ z w ≤
      ((Nat.ceil
            (completedZeroLocalLogBoundConstant * (1 + η * Real.log ((q : ℝ) * (|t| + 3))) : ℝ) :
          ℕ) :
        ℝ) := by
  let B := completedZeroLocalLogBoundConstant * (1 + η * Real.log ((q : ℝ) * (|t| + 3)))
  calc
    completedZeroMultiplicityCountInRectangle χ hχ z w ≤ B := by
      simpa only [B] using
        completedZeroMultiplicityCountInRectangle_le_uniform_local_log_bound hq hχ hp hinv hη hη1 z
          w hbox
    _ ≤ (Nat.ceil B : ℝ) := Nat.le_ceil B

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
