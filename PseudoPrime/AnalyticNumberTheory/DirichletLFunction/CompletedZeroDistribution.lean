/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedZeroCayley
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PoissonZeroSum

/-!
# Conductor-normalized weighted completed-zero distribution

Poisson weights have total mass log q / 2 up to a conductor-uniform bounded error.
Every nonzero integer Cayley moment vanishes after normalization by log q.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- The natural multiplicity of a completed zero divided by the norm square of
3/2-rho. Under individual RH this is multiplicity/(1+Im(rho)^2), a nonnegative
summable Poisson weight. Its sum provides the mass controlling approximation errors. -/
noncomputable def completedZeroPoissonWeight {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ρ : CompletedZero χ) : ℝ :=
  (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℝ) /
    Complex.normSq ((((3 / 2 : ℝ) : ℂ)) - (ρ : ℂ))

/-- For primitive nonprincipal characters of modulus at least two, with nonprincipal
inverse and individual RH, the Poisson weights of actual completed zeros are summable.
Rewrite norm square as squared norm and use the shifted inverse-square mass.
This supplies the finite total mass for weighted continuous test functions. -/
theorem summable_completedZeroPoissonWeight {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) : Summable (completedZeroPoissonWeight χ) := by
  change
    Summable
      (fun ρ : CompletedZero χ =>
        (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℝ) /
          Complex.normSq ((((3 / 2 : ℝ) : ℂ)) - (ρ : ℂ)))
  simpa only [Complex.normSq_eq_norm_sq, norm_sub_rev] using
    summable_completedZero_shifted_inverseSquare hq hRH hp hne hinv
      (show (1 : ℝ) ≤ 3 / 2 by norm_num only)

/-- For primitive nonprincipal characters of modulus at least two, with nonprincipal
inverse and individual RH, the total completed-zero Poisson weight is the real completed
logarithmic derivative at 3/2 plus log q / 2. Convert divisor multiplicities to natural
orders and discard the zero terms outside the actual zero subtype in the Poisson identity.
This determines the limiting normalized mass. -/
theorem completedZeroPoissonSum_eq_logDeriv_re {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : CompletedZero χ, completedZeroPoissonWeight χ ρ) =
      (logDeriv χ.completedLFunction (((3 / 2 : ℝ) : ℂ))).re + Real.log q / 2 := by
  have h :=
    completed_poissonSum_eq_logDeriv_re hq hRH hp hne hinv (s := (((3 / 2 : ℝ) : ℂ)))
      (by
        rw [Complex.ofReal_re]; norm_num only)
  simp only [Complex.ofReal_re, show (3 / 2 : ℝ) - 1 / 2 = 1 by norm_num only,
    ← div_eq_mul_one_div] at h
  rw [tsum_congr
      (fun ρ => by rw [completed_divisor_eq_analyticOrderNatAt hne, Int.cast_natCast])] at h
  rw [←
    tsum_subtype_eq_of_support_subset (s := {ρ : ℂ | χ.completedLFunction ρ = 0}) (f := fun ρ : ℂ =>
      (analyticOrderNatAt χ.completedLFunction ρ : ℝ) /
        Complex.normSq ((((3 / 2 : ℝ) : ℂ)) - ρ))] at h
  · exact h
  · intro ρ hρ
    by_contra hn
    have ho : analyticOrderNatAt χ.completedLFunction ρ = 0 := by
      rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hn), ENat.toNat_zero]
    exact hρ (by simp only [ho, Nat.cast_zero, zero_div])

/-- Each completed-zero Poisson weight is nonnegative for every character.
The natural multiplicity and norm-square denominator are nonnegative.
This positivity permits norm estimates for weighted test functions. -/
theorem completedZeroPoissonWeight_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ρ : CompletedZero χ) : 0 ≤ completedZeroPoissonWeight χ ρ :=
  div_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

/-- For every character and completed zero, the degree-zero Cayley term equals the
complex cast of its real Poisson weight. Simplify the zeroth power and real casts.
This identifies the constant test function with the total mass. -/
theorem completedZeroCayleyTerm_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ρ : CompletedZero χ) :
    completedZeroCayleyTerm χ 0 ρ = (completedZeroPoissonWeight χ ρ : ℂ) := by
  simp only [completedZeroCayleyTerm, completedZeroPoissonWeight, pow_zero, mul_one,
    Complex.ofReal_div, Complex.ofReal_natCast]

/-- For primitive nonprincipal characters of modulus at least two, with nonprincipal
inverse and individual RH, the zeroth complex Cayley moment is the real cast of the
completed logarithmic derivative's real part at 3/2 plus log q / 2.
Commute the real cast with the series and apply the Poisson identity.
This is the constant Fourier moment of the normalized zero distribution. -/
theorem completedZeroCayleySum_zero {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : CompletedZero χ, completedZeroCayleyTerm χ 0 ρ) =
      (((logDeriv χ.completedLFunction (((3 / 2 : ℝ) : ℂ))).re + Real.log q / 2 : ℝ) : ℂ) := by
  rw [tsum_congr (completedZeroCayleyTerm_zero χ), ← Complex.ofReal_tsum,
    completedZeroPoissonSum_eq_logDeriv_re hq hRH hp hne hinv]

/-- The total Poisson weight differs from log q / 2 by a positive constant uniform
over moduli and primitive nonprincipal characters with nonprincipal inverse satisfying
individual RH. Use the Poisson identity and the fixed-disk completed logarithmic-derivative
bound at its center. This controls the total mass in continuous-function approximation. -/
theorem exists_uniform_completedZeroPoissonSum_error_le :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (q : ℕ) [NeZero q],
          2 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              GRH.DirichletRiemannHypothesis χ →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                |(∑' ρ : CompletedZero χ, completedZeroPoissonWeight χ ρ) - Real.log q / 2| ≤
                  C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_norm_completed_logDeriv_disk_le
  refine ⟨C, hC, ?_⟩
  intro q _ hq χ hRH hp hne hinv
  rw [completedZeroPoissonSum_eq_logDeriv_re hq hRH hp hne hinv, add_sub_cancel_right]
  apply (Complex.abs_re_le_norm _).trans
  apply hb q χ hne
  rw [Metric.mem_closedBall, dist_self]
  norm_num only

/-- For a primitive character with nonprincipal inverse and individual RH, the
difference 3/2-rho has real part one at each completed zero.
Subtract its critical-line real part from 3/2. This verifies the Cayley circle domain. -/
theorem completedZeroShift_re_eq_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    (ρ : CompletedZero χ) : ((((3 / 2 : ℝ) : ℂ)) - (ρ : ℂ)).re = 1 := by
  rw [Complex.sub_re, Complex.ofReal_re,
    completedLFunction_zero_re_eq_half_of_dirichletRH hRH hp hinv ρ.property]
  norm_num only

/-- For a primitive character with nonprincipal inverse satisfying individual RH,
map a completed zero to (z-2)/z on the unit circle, where z = 3/2-rho.
The critical-line location gives Re z = 1 and hence unit norm.
These points support the Poisson-weighted circle test functions. -/
noncomputable def completedZeroCayleyPoint {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    (ρ : CompletedZero χ) : Circle :=
  ⟨((((3 / 2 : ℝ) : ℂ)) - (ρ : ℂ) - 2) / ((((3 / 2 : ℝ) : ℂ)) - (ρ : ℂ)),
    mem_sphere_zero_iff_norm.mpr
      (PseudoPrime.Analysis.cayley_norm (completedZeroShift_re_eq_one hRH hp hinv ρ))⟩

/-- Under individual RH for a primitive character with nonprincipal inverse,
the degree-n Cayley term is its real Poisson weight times the nth power of its circle point.
Unfold the definitions and commute natural and real casts.
This expresses the zero series as a weighted evaluation of circle monomials. -/
theorem completedZeroCayleyTerm_eq_weight_mul_pointPow {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hinv : χ⁻¹ ≠ 1) (n : ℕ) (ρ : CompletedZero χ) :
    completedZeroCayleyTerm χ n ρ =
      (completedZeroPoissonWeight χ ρ : ℂ) * (completedZeroCayleyPoint hRH hp hinv ρ : ℂ) ^ n := by
  simp only [completedZeroCayleyTerm, completedZeroPoissonWeight, completedZeroCayleyPoint,
    Complex.ofReal_div, Complex.ofReal_natCast]

/-- Under individual RH for a primitive character with nonprincipal inverse, every
natural-degree Cayley term has norm exactly its nonnegative Poisson weight.
The circle point and each of its powers have norm one.
This controls all monomial series by the same positive summable mass. -/
theorem norm_completedZeroCayleyTerm {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) (n : ℕ)
    (ρ : CompletedZero χ) : ‖completedZeroCayleyTerm χ n ρ‖ = completedZeroPoissonWeight χ ρ := by
  rw [completedZeroCayleyTerm_eq_weight_mul_pointPow hRH hp hinv, norm_mul, norm_pow,
    Circle.norm_coe, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (completedZeroPoissonWeight_nonneg χ ρ)]

/-- For primitive nonprincipal characters of modulus at least two, with nonprincipal
inverse and individual RH, all natural-degree Cayley zero series, including degree zero,
are absolutely convergent. Their norms equal the summable Poisson weights.
This supplies convergence uniformly across the monomials used in approximation. -/
theorem summable_completedZeroCayleyTerm_all {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (n : ℕ) : Summable (completedZeroCayleyTerm χ n) := by
  exact
    (summable_completedZeroPoissonWeight hq hRH hp hne hinv).of_norm_bounded
      (fun ρ => (norm_completedZeroCayleyTerm hRH hp hinv n ρ).le)

/-- For a primitive character with nonprincipal inverse satisfying individual RH,
an integer-degree weighted Cayley term is its real Poisson weight times that integer
power of its circle point. Negative powers are well-defined because the point is nonzero.
This is the monomial input for trigonometric approximation. -/
noncomputable def completedZeroCayleyZTerm {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) (k : ℤ)
    (ρ : CompletedZero χ) : ℂ :=
  (completedZeroPoissonWeight χ ρ : ℂ) * (completedZeroCayleyPoint hRH hp hinv ρ : ℂ) ^ k

/-- For a nonnegative integer degree, the weighted integer Cayley term agrees with
the previously defined natural-degree term. Rewrite the integer power as a natural power.
This transfers the positive moment estimates to integer-indexed monomials. -/
theorem completedZeroCayleyZTerm_natCast {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) (n : ℕ)
    (ρ : CompletedZero χ) :
    completedZeroCayleyZTerm hRH hp hinv (n : ℤ) ρ = completedZeroCayleyTerm χ n ρ := by
  rw [completedZeroCayleyZTerm, zpow_natCast,
    completedZeroCayleyTerm_eq_weight_mul_pointPow hRH hp hinv]

/-- For a negative natural degree, the weighted integer Cayley term is the complex
conjugate of the corresponding positive-degree term. The inverse of a unit circle point
is its conjugate and the real Poisson weight is fixed by conjugation.
This transfers positive moment estimates to negative frequencies. -/
theorem completedZeroCayleyZTerm_neg_natCast {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) (n : ℕ)
    (ρ : CompletedZero χ) :
    completedZeroCayleyZTerm hRH hp hinv (-(n : ℤ)) ρ =
      (starRingEnd ℂ) (completedZeroCayleyTerm χ n ρ) := by
  rw [completedZeroCayleyZTerm, completedZeroCayleyTerm_eq_weight_mul_pointPow hRH hp hinv,
    zpow_neg, zpow_natCast, ← inv_pow, Complex.inv_eq_conj (Circle.norm_coe _)]
  simp only [map_mul, map_pow, Complex.conj_ofReal]

/-- For every nonzero integer degree and epsilon > 0, sufficiently large moduli make
the norm of the weighted Cayley moment at most epsilon log q, uniformly over primitive
nonprincipal characters with nonprincipal inverse satisfying individual RH.
Split the degree into a positive or negative natural degree and use conjugation of
the convergent series. This supplies all nonconstant Fourier moments. -/
theorem exists_uniform_completedZeroCayleyZSum_le_log {k : ℤ} (hk : k ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ,
      2 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              ∀ hRH : GRH.DirichletRiemannHypothesis χ,
                ∀ hp : χ.IsPrimitive,
                  χ ≠ 1 →
                    ∀ hinv : χ⁻¹ ≠ 1,
                      ‖∑' ρ : CompletedZero χ, completedZeroCayleyZTerm hRH hp hinv k ρ‖ ≤
                        ε * Real.log q := by
  obtain ⟨n, hn⟩ := Int.eq_nat_or_neg k
  cases n with
  | zero => rcases hn with rfl | rfl <;> exact (hk rfl).elim
  | succ n =>
    obtain ⟨Q, hQ, hb⟩ := exists_uniform_completedZeroCayleySum_le_log n hε
    refine ⟨Q, hQ, ?_⟩
    intro q _ hq χ hRH hp hne hinv
    rcases hn with rfl | rfl
    · rw [tsum_congr (completedZeroCayleyZTerm_natCast hRH hp hinv (n + 1))]
      exact hb q hq χ hRH hp hne hinv
    · rw [tsum_congr (completedZeroCayleyZTerm_neg_natCast hRH hp hinv (n + 1)), ←
        Complex.conj_tsum, Complex.norm_conj]
      exact hb q hq χ hRH hp hne hinv

/-- For every epsilon > 0, sufficiently large moduli make the difference of the total
Poisson weight from log q / 2 at most epsilon log q, uniformly over primitive nonprincipal
characters with nonprincipal inverse satisfying individual RH. Absorb the fixed error
bound into the logarithm. This supplies the limiting constant moment alongside the
vanishing nonzero integer moments. -/
theorem exists_uniform_completedZeroPoissonSum_error_le_log {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ,
      2 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              GRH.DirichletRiemannHypothesis χ →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                |(∑' ρ : CompletedZero χ, completedZeroPoissonWeight χ ρ) - Real.log q / 2| ≤
                  ε * Real.log q := by
  obtain ⟨C, _, hb⟩ := exists_uniform_completedZeroPoissonSum_error_le
  have hl :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop (C / ε)
  obtain ⟨Q, hQ⟩ := Filter.eventually_atTop.mp hl
  refine ⟨max 2 Q, Nat.le_max_left _ _, ?_⟩
  intro q _ hq χ hRH hp hne hinv
  have hq2 := (Nat.le_max_left 2 Q).trans hq
  have hlarge := (div_le_iff₀ hε).mp (hQ q ((Nat.le_max_right 2 Q).trans hq))
  simp only [Function.comp_apply] at hlarge
  exact (hb q hq2 χ hRH hp hne hinv).trans (by nlinarith only [hlarge])

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
