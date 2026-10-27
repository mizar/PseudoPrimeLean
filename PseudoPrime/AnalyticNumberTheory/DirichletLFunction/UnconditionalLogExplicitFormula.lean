/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalLogBoundary
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalTrivialLogZeros

/-! # Unconditional exact logarithmic explicit formula for primitive characters -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For every primitive nonprincipal character with nonprincipal inverse and real
scale greater than one, the log-weighted character sum equals its origin residue
plus the explicit parity-dependent trivial correction minus the absolutely
convergent completed-zero series with multiplicities. Use the unconditional good
heights, finite contour identity, and zero-sum exhaustion, then send the negative
half-integer left edge to minus infinity. No density or RH hypothesis is assumed.
This supplies the smoothed explicit formula for the unconditional theta-supply stage. -/
theorem characterLogWeightedSum_exact_zero_formula_unconditionally {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 1 < x) :
    Arithmetic.characterLogWeightedSum x χ =
      dirichletLogResidueAt hne x 0 + logarithmicTrivialCorrection χ x -
        ∑' ρ : ℂ, completedLogZeroTerm χ x ρ := by
  classical
  obtain ⟨T, hT, hspec, hboundary⟩ :=
    exists_unconditional_logBoundary_height_sequence hq hp hne hinv
  have hTpos (k : ℕ) : 0 < T k :=
    zero_lt_one.trans_le ((le_add_of_nonneg_left (Nat.cast_nonneg k)).trans (hspec k).1)
  let c := fun m : ℕ ↦
    ∑
      ρ ∈
        (dirichletLFunctionZerosInRectangle χ hne (unconditionalHeightLowerCorner (2 * m) (T 0))
              (unconditionalHeightUpperCorner (T 0))).filter
          (fun ρ ↦ DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
      dirichletLFunctionLogZeroContribution x χ ρ
  have hconstant (m : ℕ) (hm : 1 ≤ m) (k : ℕ) :
    (∑
        ρ ∈
          (dirichletLFunctionZerosInRectangle χ hne (unconditionalHeightLowerCorner (2 * m) (T k))
                (unconditionalHeightUpperCorner (T k))).filter
            (fun ρ ↦ DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
        dirichletLFunctionLogZeroContribution x χ ρ) =
      c m := by
    rcases χ.even_or_odd with he | ho
    · exact
        (sum_even_log_trivialZeros_unconditionalRectangle_eq hp hne he x m hm (T k) (hTpos k)).trans
          (sum_even_log_trivialZeros_unconditionalRectangle_eq hp hne he x m hm (T 0)
              (hTpos 0)).symm
    · exact
        (sum_odd_log_trivialZeros_unconditionalRectangle_eq hp hne ho x m hm (T k) (hTpos k)).trans
          (sum_odd_log_trivialZeros_unconditionalRectangle_eq hp hne ho x m hm (T 0) (hTpos 0)).symm
  have hclimit : Filter.Tendsto c Filter.atTop (nhds (logarithmicTrivialCorrection χ x)) := by
    dsimp only [logarithmicTrivialCorrection]
    by_cases he : χ.Even
    · rw [ite_eq_left he]
      exact
        tendsto_sum_even_log_trivialZeros_unconditionalRectangle hp hne he hx (fun _ ↦ T 0)
          (fun _ ↦ hTpos 0)
    · rw [ite_eq_right he]
      exact
        tendsto_sum_odd_log_trivialZeros_unconditionalRectangle hp hne
          (χ.even_or_odd.resolve_left he) hx (fun _ ↦ T 0) (fun _ ↦ hTpos 0)
  have hfixed (m : ℕ) (hm : 1 ≤ m) :
    Arithmetic.characterLogWeightedSum x χ -
        ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
          ∫ t : ℝ,
            dirichletLogContourKernel x χ
              (((primitiveReciprocalLeftRe (2 * m) : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
      dirichletLogResidueAt hne x 0 + c m - ∑' ρ : ℂ, completedLogZeroTerm χ x ρ :=
    logWeightedSum_sub_left_unconditionally hq hp hne hinv T hT hTpos (fun k ↦ (hspec k).2) (2 * m)
      (Nat.mul_le_mul_left 2 hm) hx (c m) (hconstant m hm)
      (hboundary (2 * m) (Nat.mul_le_mul_left 2 hm) x hx.le)
  have hdouble : Filter.Tendsto (fun m : ℕ ↦ 2 * m) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono _ Filter.tendsto_id
    intro m
    exact Nat.le_mul_of_pos_left m (by decide : 0 < 2)
  have hleft :=
    (tendsto_dirichletLogContourKernel_leftVertical_integral_atTop hp hne hinv hx).comp hdouble
  have hweight :=
    (tendsto_const_nhds (x := Arithmetic.characterLogWeightedSum x χ)).sub
      (hleft.const_mul ((2 * Real.pi : ℝ)⁻¹ : ℂ))
  simp only [mul_zero, sub_zero] at hweight
  have hresidue :=
    ((tendsto_const_nhds (x := dirichletLogResidueAt hne x 0)).add hclimit).sub_const
      (∑' ρ : ℂ, completedLogZeroTerm χ x ρ)
  have heq :
    (fun m : ℕ ↦
        Arithmetic.characterLogWeightedSum x χ -
          ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
            ∫ t : ℝ,
              dirichletLogContourKernel x χ
                (((primitiveReciprocalLeftRe (2 * m) : ℝ) : ℂ) +
                  (t : ℂ) * Complex.I)) =ᶠ[Filter.atTop]
      (fun m : ℕ ↦ dirichletLogResidueAt hne x 0 + c m - ∑' ρ : ℂ, completedLogZeroTerm χ x ρ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    exact hfixed m hm
  exact tendsto_nhds_unique (hweight.congr' heq) hresidue

/-- For a primitive nonprincipal character and its nonprincipal inverse, the half-scale
zero terms are summable when `x ≥ 2`. Subtracting the two absolutely convergent
logarithmic zero series supplies the half-scale explicit formula. -/
theorem summable_completedLogHalfZeroTerm_unconditionally {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 2 ≤ x) : Summable (completedLogHalfZeroTerm χ x) := by
  have hfirst :=
    (summable_norm_completedLogZeroTerm_unconditionally hq hp hne hinv
        (by linarith only [hx] : 1 ≤ x)).of_norm
  have hsecond :=
    (summable_norm_completedLogZeroTerm_unconditionally hq hp hne hinv
        (by linarith only [hx] : 1 ≤ x / 2)).of_norm
  exact
    (hfirst.sub hsecond).congr
      (fun ρ ↦ (completedLogHalfZeroTerm_eq_sub χ (by linarith only [hx] : 0 ≤ x) ρ).symm)

/-- Under the primitive nonprincipal hypotheses and `x ≥ 2`, the half-scale zero sum
is the difference of the two full zero sums. Absolute convergence justifies subtraction. -/
theorem tsum_completedLogHalfZeroTerm_eq_sub_unconditionally {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 2 ≤ x) :
    (∑' ρ : ℂ, completedLogHalfZeroTerm χ x ρ) =
      (∑' ρ : ℂ, completedLogZeroTerm χ x ρ) - ∑' ρ : ℂ, completedLogZeroTerm χ (x / 2) ρ := by
  rw [←
    ((summable_norm_completedLogZeroTerm_unconditionally hq hp hne hinv
            (by linarith only [hx] : 1 ≤ x)).of_norm).tsum_sub
      ((summable_norm_completedLogZeroTerm_unconditionally hq hp hne hinv
          (by linarith only [hx] : 1 ≤ x / 2)).of_norm)]
  exact tsum_congr (completedLogHalfZeroTerm_eq_sub χ (by linarith only [hx] : 0 ≤ x))

/-- For a primitive nonprincipal character with nonprincipal inverse and `x > 2`,
the half-scale weighted sum equals the negative half-scale zero series plus its
origin and trivial-zero correction. Subtracting the unconditional exact formulas
provides the interface used in progression error estimates, without GRH. -/
theorem characterLogWeightedSum_half_exact_zero_formula_unconditionally {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    {x : ℝ} (hx : 2 < x) :
    Arithmetic.characterLogWeightedSum x χ - Arithmetic.characterLogWeightedSum (x / 2) χ =
      -(∑' ρ : ℂ, completedLogHalfZeroTerm χ x ρ) + logarithmicHalfRemainder hne x := by
  rw [characterLogWeightedSum_exact_zero_formula_unconditionally hq hp hne hinv
      (show 1 < x by linarith only [hx]),
    characterLogWeightedSum_exact_zero_formula_unconditionally hq hp hne hinv
      (show 1 < x / 2 by linarith only [hx]),
    tsum_completedLogHalfZeroTerm_eq_sub_unconditionally hq hp hne hinv hx.le]
  dsimp only [logarithmicHalfRemainder]
  ring

/-- For a primitive nonprincipal character, its nonprincipal inverse, and `x > 2`,
the half-scale character sum is bounded by the absolute completed-zero series and
the retained origin and trivial-zero remainder. The triangle inequality applied
to the unconditional half-scale formula supplies the progression-error interface. -/
theorem norm_characterLogWeightedSum_half_le_unconditionally {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 2 < x) :
    ‖Arithmetic.characterLogWeightedSum x χ - Arithmetic.characterLogWeightedSum (x / 2) χ‖ ≤
      (∑' ρ : ℂ, ‖completedLogHalfZeroTerm χ x ρ‖) + ‖logarithmicHalfRemainder hne x‖ := by
  rw [characterLogWeightedSum_half_exact_zero_formula_unconditionally hq hp hne hinv hx]
  calc
    ‖-(∑' ρ : ℂ, completedLogHalfZeroTerm χ x ρ) + logarithmicHalfRemainder hne x‖ ≤
        ‖∑' ρ : ℂ, completedLogHalfZeroTerm χ x ρ‖ + ‖logarithmicHalfRemainder hne x‖ :=
      by
      simpa only [norm_neg] using
        norm_add_le (-(∑' ρ : ℂ, completedLogHalfZeroTerm χ x ρ)) (logarithmicHalfRemainder hne x)
    _ ≤ _ :=
      add_le_add
        (norm_tsum_le_tsum_norm
          (summable_completedLogHalfZeroTerm_unconditionally hq hp hne hinv hx.le).norm)
        le_rfl

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
