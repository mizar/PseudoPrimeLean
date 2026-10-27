/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalHeightRectangle
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalLogZeroSeries
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogHalfExplicitFormula

/-! # Unconditional normalized logarithmic boundary limits -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a cofinal positive height sequence whose horizontal logarithmic edges vanish,
the normalized rectangle boundary tends to the log-weighted character sum minus
the left vertical whole-line integral. Expand the four edges, use unconditional
vertical exhaustion, and combine the limits. This is the boundary interface for
an unconditional smoothed explicit formula. -/
theorem tendsto_normalized_unconditional_logBoundary {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (T : ℕ → ℝ)
    (hT : Filter.Tendsto T Filter.atTop Filter.atTop) (hTpos : ∀ k : ℕ, 0 < T k) (A : ℕ)
    (hA : 2 ≤ A) {x : ℝ} (hx : 1 ≤ x)
    (hhor :
      Filter.Tendsto
          (fun k : ℕ ↦
            ∫ σ in (-(A : ℝ) - 1 / 2)..2, dirichletLogContourKernel x χ ((σ : ℂ) + T k * Complex.I))
          Filter.atTop (nhds 0) ∧
        Filter.Tendsto
          (fun k : ℕ ↦
            ∫ σ in (-(A : ℝ) - 1 / 2)..2, dirichletLogContourKernel x χ ((σ : ℂ) - T k * Complex.I))
          Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k : ℕ ↦
        (-Complex.I / (2 * (Real.pi : ℂ))) *
          RectangleGeometry.rectangleBoundaryIntegral (dirichletLogContourKernel x χ)
            (unconditionalHeightLowerCorner A (T k)) (unconditionalHeightUpperCorner (T k)))
      Filter.atTop
      (nhds
        (Arithmetic.characterLogWeightedSum x χ -
          ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
            ∫ t : ℝ,
              dirichletLogContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I))) := by
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hcoeffI : (-Complex.I / (2 * (Real.pi : ℂ))) * Complex.I = ((2 * Real.pi : ℝ)⁻¹ : ℂ) := by
    rw [div_mul_eq_mul_div,
      show (-Complex.I) * Complex.I = 1 from by
        rw [neg_mul, Complex.I_mul_I]
        ring]
    push_cast
    ring
  have heq :
    ∀ k : ℕ,
      (-Complex.I / (2 * (Real.pi : ℂ))) *
          RectangleGeometry.rectangleBoundaryIntegral (dirichletLogContourKernel x χ)
            (unconditionalHeightLowerCorner A (T k)) (unconditionalHeightUpperCorner (T k)) =
        (-Complex.I / (2 * (Real.pi : ℂ))) *
              ((∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
                  dirichletLogContourKernel x χ ((σ : ℂ) - T k * Complex.I)) -
                ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
                  dirichletLogContourKernel x χ ((σ : ℂ) + T k * Complex.I)) +
            ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
              (∫ t in (-(T k))..(T k),
                dirichletLogContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I)) -
          ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
            (∫ t in (-(T k))..(T k),
              dirichletLogContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    intro k
    obtain ⟨hzre, hzim, hwre, hwim, _, _⟩ := unconditionalHeightRectangleFacts A hA (T k) (hTpos k)
    unfold RectangleGeometry.rectangleBoundaryIntegral
    rw [hzre, hzim, hwre, hwim, primitiveReciprocalLeftRe]
    simp only [smul_eq_mul, Complex.ofReal_neg, neg_mul]
    linear_combination
      (∫ t in (-(T k))..(T k), dirichletLogContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I)) *
          hcoeffI -
        (∫ t in (-(T k))..(T k),
            dirichletLogContourKernel x χ (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) *
          hcoeffI
  apply Filter.Tendsto.congr (fun k => (heq k).symm)
  have hhoriz := hhor
  have hright :=
    (tendsto_intervalIntegral_dirichletLogContourKernel hxpos χ hne
          (show (1 : ℝ) < 2 by norm_num only)).comp
      hT
  have hleft :=
    (tendsto_intervalIntegral_dirichletLogContourKernel_leftVertical hprimitive hne hinv hxpos
          hA).comp
      hT
  have hweighted := characterLogWeightedSum_eq_integral χ hxpos (show (1 : ℝ) < 2 by norm_num only)
  have htarget :
    Filter.Tendsto
      (fun k : ℕ =>
        (-Complex.I / (2 * (Real.pi : ℂ))) *
              ((∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
                  dirichletLogContourKernel x χ ((σ : ℂ) - T k * Complex.I)) -
                ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
                  dirichletLogContourKernel x χ ((σ : ℂ) + T k * Complex.I)) +
            ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
              (∫ t in (-(T k))..(T k),
                dirichletLogContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I)) -
          ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
            (∫ t in (-(T k))..(T k),
              dirichletLogContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)))
      Filter.atTop
      (nhds
        ((-Complex.I / (2 * (Real.pi : ℂ))) * ((0 : ℂ) - 0) +
            ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
              (∫ t : ℝ, dirichletLogContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I)) -
          ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
            (∫ t : ℝ,
              dirichletLogContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)))) := by
    apply Filter.Tendsto.sub
    · apply Filter.Tendsto.add
      · exact Filter.Tendsto.const_mul _ (hhoriz.2.sub hhoriz.1)
      · exact Filter.Tendsto.const_mul _ hright
    · exact Filter.Tendsto.const_mul _ hleft
  simp only [sub_zero, mul_zero, zero_add] at htarget
  rw [hweighted, Complex.real_smul]
  convert htarget using 2
  push_cast
  ring

/-- Every primitive nonprincipal character with nonprincipal inverse has a cofinal
positive height sequence with nonzero central completed edges and normalized
boundary convergence on every fixed negative-half-integer contour, for every
scale at least one. Apply the proved unconditional horizontal limits and vertical
exhaustion. This discharges all horizontal-limit assumptions before residue assembly. -/
theorem exists_unconditional_logBoundary_height_sequence {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    ∃ T : ℕ → ℝ,
      Filter.Tendsto T Filter.atTop Filter.atTop ∧
        (∀ k : ℕ,
          (k : ℝ) + 1 ≤ T k ∧
            ∀ σ : ℝ,
              |σ| ≤ 2 →
                χ.completedLFunction ((σ : ℂ) + T k * Complex.I) ≠ 0 ∧
                  χ.completedLFunction ((σ : ℂ) - T k * Complex.I) ≠ 0) ∧
        ∀ A : ℕ,
          2 ≤ A →
            ∀ x : ℝ,
              1 ≤ x →
                Filter.Tendsto
                  (fun k : ℕ ↦
                    (-Complex.I / (2 * (Real.pi : ℂ))) *
                      RectangleGeometry.rectangleBoundaryIntegral (dirichletLogContourKernel x χ)
                        (unconditionalHeightLowerCorner A (T k))
                        (unconditionalHeightUpperCorner (T k)))
                  Filter.atTop
                  (nhds
                    (Arithmetic.characterLogWeightedSum x χ -
                      ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
                        ∫ t : ℝ,
                          dirichletLogContourKernel x χ
                            (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I))) := by
  obtain ⟨T, hT, hspec, hhorizontal⟩ :=
    exists_unconditional_logKernel_horizontal_height_limits hq hp hne hinv
  refine ⟨T, hT, hspec, ?_⟩
  intro A hA x hx
  exact
    tendsto_normalized_unconditional_logBoundary hp hne hinv T hT
      (fun k ↦ zero_lt_one.trans_le ((le_add_of_nonneg_left (Nat.cast_nonneg k)).trans (hspec k).1))
      A hA hx (hhorizontal A hA x hx)

/-- For a positive good-height sequence, a fixed contour with constant trivial-zero
contribution identifies the log-weighted character sum minus its left edge with
the origin residue plus that contribution minus the full completed-zero sum.
Compare the normalized boundary limit with the finite residue identity and
unconditional zero-sum exhaustion. This is the fixed-left-edge explicit formula. -/
theorem logWeightedSum_sub_left_unconditionally {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (T : ℕ → ℝ)
    (hT : Filter.Tendsto T Filter.atTop Filter.atTop) (hTpos : ∀ k : ℕ, 0 < T k)
    (hcentral :
      ∀ k : ℕ,
        ∀ σ : ℝ,
          |σ| ≤ 2 →
            χ.completedLFunction ((σ : ℂ) + T k * Complex.I) ≠ 0 ∧
              χ.completedLFunction ((σ : ℂ) - T k * Complex.I) ≠ 0)
    (A : ℕ) (hA : 2 ≤ A) {x : ℝ} (hx : 1 < x) (c : ℂ)
    (hc :
      ∀ k : ℕ,
        (∑
            ρ ∈
              (dirichletLFunctionZerosInRectangle χ hne (unconditionalHeightLowerCorner A (T k))
                    (unconditionalHeightUpperCorner (T k))).filter
                (fun ρ ↦ DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
            dirichletLFunctionLogZeroContribution x χ ρ) =
          c)
    (hboundary :
      Filter.Tendsto
        (fun k : ℕ ↦
          (-Complex.I / (2 * (Real.pi : ℂ))) *
            RectangleGeometry.rectangleBoundaryIntegral (dirichletLogContourKernel x χ)
              (unconditionalHeightLowerCorner A (T k)) (unconditionalHeightUpperCorner (T k)))
        Filter.atTop
        (nhds
          (Arithmetic.characterLogWeightedSum x χ -
            ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
              ∫ t : ℝ,
                dirichletLogContourKernel x χ
                  (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)))) :
    Arithmetic.characterLogWeightedSum x χ -
        ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
          ∫ t : ℝ,
            dirichletLogContourKernel x χ
              (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
      dirichletLogResidueAt hne x 0 + c - ∑' ρ : ℂ, completedLogZeroTerm χ x ρ := by
  have hzeros := tendsto_completedLogZero_unconditional_height_sum hq hp hne hinv T hT A hx.le
  have hright := (tendsto_const_nhds (x := dirichletLogResidueAt hne x 0 + c)).sub hzeros
  have heq :
    (fun k : ℕ ↦
        (-Complex.I / (2 * (Real.pi : ℂ))) *
          RectangleGeometry.rectangleBoundaryIntegral (dirichletLogContourKernel x χ)
            (unconditionalHeightLowerCorner A (T k)) (unconditionalHeightUpperCorner (T k))) =
      (fun k : ℕ ↦
        dirichletLogResidueAt hne x 0 + c -
          ∑
            ρ ∈
              completedLogRectangleLedger χ hne (unconditionalHeightLowerCorner A (T k))
                (unconditionalHeightUpperCorner (T k)),
            completedLogZeroTerm χ x ρ) := by
    funext k
    rw [unconditionalHeight_logFiniteContourIdentity_normalized hp hne hinv A hA (T k) (hTpos k)
        (hcentral k) (zero_lt_one.trans hx)]
    obtain ⟨hzero, hone⟩ := unconditionalHeight_mellinPoints_mem hne A hA (T k) (hTpos k)
    rw [log_residue_sum_eq_origin_add_trivial_sub_completed hne x hzero hone, hc k]
  rw [heq] at hboundary
  exact tendsto_nhds_unique hboundary hright

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
