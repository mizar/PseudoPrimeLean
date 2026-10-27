/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedLogHalfZeros
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogResidueLedger
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.TrivialZeroSeriesLimit
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GenericLogResidues

/-! # Exact logarithmic explicit formula and signed half-scale phase -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a rectangle containing 0 and 1, split the logarithmic residue sum
into origin, trivial zeros and completed zeros. The gamma filter identifies multiplicities. -/
theorem log_residue_sum_eq_origin_add_trivial_sub_completed {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) (x : ℝ) {z w : ℂ}
    (h0 : (0 : ℂ) ∈ dirichletLFunctionSingularitiesInRectangle χ hne z w)
    (h1 : (1 : ℂ) ∈ dirichletLFunctionSingularitiesInRectangle χ hne z w) :
    (∑ ρ ∈ dirichletLFunctionSingularitiesInRectangle χ hne z w, dirichletLogResidueAt hne x ρ) =
      dirichletLogResidueAt hne x 0 +
          (∑
            ρ ∈
              (dirichletLFunctionZerosInRectangle χ hne z w).filter
                (fun ρ ↦ DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
            dirichletLFunctionLogZeroContribution x χ ρ) -
        ∑ ρ ∈ completedLogRectangleLedger χ hne z w, completedLogZeroTerm χ x ρ := by
  classical
  let E := ((dirichletLFunctionSingularitiesInRectangle χ hne z w).erase 1).erase 0
  have he :
    (∑ ρ ∈ E, dirichletLogResidueAt hne x ρ) =
      ∑ ρ ∈ E, dirichletLFunctionLogZeroContribution x χ ρ := by
    refine Finset.sum_congr rfl ?_
    intro ρ hρ
    exact
      dirichletLogResidueAt_zero_ne_one hne x (Finset.mem_erase.mp hρ).1
        (Finset.mem_erase.mp (Finset.mem_erase.mp hρ).2).1
  have hs :=
    Finset.sum_filter_add_sum_filter_not E (fun ρ : ℂ ↦ DirichletCharacter.gammaFactor χ ρ = 0)
      (dirichletLFunctionLogZeroContribution x χ)
  have ht := erased_gammaZeros_eq_trivialZeroFilter hne z w
  have hc :
    (∑ ρ ∈ E.filter (fun ρ ↦ DirichletCharacter.gammaFactor χ ρ ≠ 0),
        dirichletLFunctionLogZeroContribution x χ ρ) =
      -(∑ ρ ∈ completedLogRectangleLedger χ hne z w, completedLogZeroTerm χ x ρ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro ρ hρ
    have hm :
      (dirichletLFunctionZeroMultiplicity χ ρ : ℂ) =
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) := by
      exact_mod_cast
        dirichletLFunctionZeroMultiplicity_eq_divisor_completedLFunction_of_gamma_ne_zero hne
          (Finset.mem_filter.mp hρ).2
    dsimp only [dirichletLFunctionLogZeroContribution, completedLogZeroTerm]
    rw [hm]
    ring
  rw [dirichletSplitLogSingularitySum x hne h1 h0, dirichletLogResidueAt_one hne x, zero_add, he, ←
    hs, ht, hc]
  ring

/-- Under primitive GRH and a fixed left edge, passing to cofinal heights
identifies the weighted sum minus its left-edge integral with the residue decomposition. -/
theorem logWeightedSum_sub_left_eq_origin_add_trivial_sub_zeros {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 < x) (m : ℕ) (hm : 1 ≤ m) (T : ℂ)
    (hT :
      ∀ k : ℕ,
        (∑
            ρ ∈
              (dirichletLFunctionZerosInRectangle χ hne
                    (primitiveHeightSeqLowerCorner hN hGRH hp hne hinv (2 * m) k)
                    (primitiveHeightSeqUpperCorner hN hGRH hp hne hinv k)).filter
                (fun ρ ↦ DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
            dirichletLFunctionLogZeroContribution x χ ρ) =
          T) :
    Arithmetic.characterLogWeightedSum x χ -
        (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
          ∫ t : ℝ,
            dirichletLogContourKernel x χ
              ((primitiveReciprocalLeftRe (2 * m) : ℂ) + (t : ℂ) * Complex.I)) =
      dirichletLogResidueAt hne x 0 + T - ∑' ρ : ℂ, completedLogZeroTerm χ x ρ := by
  have hA : 2 ≤ 2 * m := Nat.mul_le_mul_left 2 hm
  have hb :=
    tendsto_normalized_dirichletLogBoundary_heightSeq_of_grh hN hGRH hp hne hinv hx.le (2 * m) hA
  have hz :=
    tendsto_completedLogZero_height_sum hN hGRH hp hne hinv (zero_lt_one.trans hx) (2 * m) hA
  have hr := (tendsto_const_nhds (x := dirichletLogResidueAt hne x 0 + T)).sub hz
  have he :
    (fun k : ℕ ↦
        -Complex.I / (2 * Real.pi) *
          RectangleGeometry.rectangleBoundaryIntegral (dirichletLogContourKernel x χ)
            (primitiveHeightSeqLowerCorner hN hGRH hp hne hinv (2 * m) k)
            (primitiveHeightSeqUpperCorner hN hGRH hp hne hinv k)) =
      (fun k : ℕ ↦
        dirichletLogResidueAt hne x 0 + T -
          ∑
            ρ ∈
              completedLogRectangleLedger χ hne
                (primitiveHeightSeqLowerCorner hN hGRH hp hne hinv (2 * m) k)
                (primitiveHeightSeqUpperCorner hN hGRH hp hne hinv k),
            completedLogZeroTerm χ x ρ) := by
    funext k
    rw [dirichletLogFiniteContourIdentity_heightSeq_normalized hN hGRH hp hne hinv
        (zero_lt_one.trans hx) (2 * m) k hA]
    obtain ⟨h0, h1⟩ :=
      primitiveReciprocalMellinPoints_mem_singularities_heightSeq hN hGRH hp hne hinv (2 * m) k hA
    rw [log_residue_sum_eq_origin_add_trivial_sub_completed hne x h0 h1, hT k]
  rw [he] at hb
  exact tendsto_nhds_unique hb hr

/-- Under primitive GRH, a limiting trivial-zero correction yields the exact
weighted sum formula. Send the left edge to minus infinity after the height limit. -/
theorem logWeightedSum_eq_origin_add_trivial_sub_zeros_of_limit {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 < x) (T : ℕ → ℂ) (L : ℂ)
    (hT :
      ∀ m : ℕ,
        1 ≤ m →
          ∀ k : ℕ,
            (∑
                ρ ∈
                  (dirichletLFunctionZerosInRectangle χ hne
                        (primitiveHeightSeqLowerCorner hN hGRH hp hne hinv (2 * m) k)
                        (primitiveHeightSeqUpperCorner hN hGRH hp hne hinv k)).filter
                    (fun ρ ↦ DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
                dirichletLFunctionLogZeroContribution x χ ρ) =
              T m)
    (hL : Filter.Tendsto T Filter.atTop (nhds L)) :
    Arithmetic.characterLogWeightedSum x χ =
      dirichletLogResidueAt hne x 0 + L - ∑' ρ : ℂ, completedLogZeroTerm χ x ρ := by
  have hA : Filter.Tendsto (fun m : ℕ ↦ 2 * m) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono _ Filter.tendsto_id
    intro m
    exact Nat.le_mul_of_pos_left m (by decide : 0 < 2)
  have hl := (tendsto_dirichletLogContourKernel_leftVertical_integral_atTop hp hne hinv hx).comp hA
  have hs :=
    (tendsto_const_nhds (x := Arithmetic.characterLogWeightedSum x χ)).sub
      (hl.const_mul (((2 * Real.pi : ℝ) : ℂ)⁻¹))
  simp only [mul_zero, sub_zero] at hs
  have hr :=
    ((tendsto_const_nhds (x := dirichletLogResidueAt hne x 0)).add hL).sub_const
      (∑' ρ : ℂ, completedLogZeroTerm χ x ρ)
  have he :
    (fun m : ℕ ↦
        Arithmetic.characterLogWeightedSum x χ -
          (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
            ∫ t : ℝ,
              dirichletLogContourKernel x χ
                ((primitiveReciprocalLeftRe (2 * m) : ℂ) + (t : ℂ) * Complex.I))) =ᶠ[Filter.atTop]
      (fun m : ℕ ↦ dirichletLogResidueAt hne x 0 + T m - ∑' ρ : ℂ, completedLogZeroTerm χ x ρ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    exact
      logWeightedSum_sub_left_eq_origin_add_trivial_sub_zeros hN hGRH hp hne hinv hx m hm (T m)
        (hT m hm)
  exact tendsto_nhds_unique (hs.congr' he) hr

/-- The exact negative trivial-zero series, separated by character parity.
This correction is retained in the logarithmic explicit formula. -/
noncomputable def logarithmicTrivialCorrection {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (x : ℝ) : ℂ := by
  classical
    exact
    if χ.Even then -((∑' j : ℕ, x⁻¹ ^ (2 * (j + 1)) / ((2 * (j + 1) : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)
    else -((∑' j : ℕ, x⁻¹ ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)

/-- Under primitive GRH and x>1, the weighted character sum equals the origin
residue plus the parity-specific trivial correction minus the completed zero series.
Pass to both contour limits; no unspecified intermediate zero contribution remains. -/
theorem characterLogWeightedSum_exact_zero_formula {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 < x) :
    Arithmetic.characterLogWeightedSum x χ =
      dirichletLogResidueAt hne x 0 + logarithmicTrivialCorrection χ x -
        ∑' ρ : ℂ, completedLogZeroTerm χ x ρ := by
  classical
  let T := fun m : ℕ ↦
    ∑
      ρ ∈
        (dirichletLFunctionZerosInRectangle χ hne
              (primitiveHeightSeqLowerCorner hN hGRH hp hne hinv (2 * m) 0)
              (primitiveHeightSeqUpperCorner hN hGRH hp hne hinv 0)).filter
          (fun ρ ↦ DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
      dirichletLFunctionLogZeroContribution x χ ρ
  have hT :
    ∀ m : ℕ,
      1 ≤ m →
        ∀ k : ℕ,
          (∑
              ρ ∈
                (dirichletLFunctionZerosInRectangle χ hne
                      (primitiveHeightSeqLowerCorner hN hGRH hp hne hinv (2 * m) k)
                      (primitiveHeightSeqUpperCorner hN hGRH hp hne hinv k)).filter
                  (fun ρ ↦ DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
              dirichletLFunctionLogZeroContribution x χ ρ) =
            T m := by
    intro m hm k
    rcases χ.even_or_odd with he | ho
    · exact
        (sum_even_log_trivialZeros_primitiveRectangle_eq hN hGRH hp hne hinv he x m k hm).trans
          (sum_even_log_trivialZeros_primitiveRectangle_eq hN hGRH hp hne hinv he x m 0 hm).symm
    · exact
        (sum_odd_log_trivialZeros_primitiveRectangle_eq hN hGRH hp hne hinv ho x m k hm).trans
          (sum_odd_log_trivialZeros_primitiveRectangle_eq hN hGRH hp hne hinv ho x m 0 hm).symm
  have hlim : Filter.Tendsto T Filter.atTop (nhds (logarithmicTrivialCorrection χ x)) := by
    dsimp only [logarithmicTrivialCorrection]
    by_cases he : χ.Even
    · rw [ite_eq_left he]
      exact
        tendsto_sum_even_log_trivialZeros_primitiveRectangle hN hGRH hp hne hinv he hx (fun _ ↦ 0)
    · rw [ite_eq_right he]
      exact
        tendsto_sum_odd_log_trivialZeros_primitiveRectangle hN hGRH hp hne hinv
          (χ.even_or_odd.resolve_left he) hx (fun _ ↦ 0)
  exact logWeightedSum_eq_origin_add_trivial_sub_zeros_of_limit hN hGRH hp hne hinv hx T _ hT hlim

/-- The origin-residue difference plus the two trivial-zero corrections.
For primitive characters under GRH this is the remainder in the half-scale phase formula. -/
noncomputable def logarithmicHalfRemainder {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) (x : ℝ) : ℂ :=
  dirichletLogResidueAt hne x 0 - dirichletLogResidueAt hne (x / 2) 0 +
      logarithmicTrivialCorrection χ x -
    logarithmicTrivialCorrection χ (x / 2)

/-- Under primitive GRH and x>2, the half-scale difference equals minus the
combined zero series plus the explicit remainder. Subtract the two exact formulas. -/
theorem characterLogWeightedSum_half_exact_zero_formula {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 < x) :
    Arithmetic.characterLogWeightedSum x χ - Arithmetic.characterLogWeightedSum (x / 2) χ =
      -(∑' ρ : ℂ, completedLogHalfZeroTerm χ x ρ) + logarithmicHalfRemainder hne x := by
  have hx0 : 0 < x := by linarith only [hx]
  rw [characterLogWeightedSum_exact_zero_formula hN hGRH hp hne hinv
      (show 1 < x by linarith only [hx]),
    characterLogWeightedSum_exact_zero_formula hN hGRH hp hne hinv
      (show 1 < x / 2 by linarith only [hx]),
    tsum_completedLogHalfZeroTerm_eq_sub hN hGRH hp hne hinv hx0]
  dsimp only [logarithmicHalfRemainder]
  ring

/-- Under primitive GRH and x>2, the real half-scale difference is sqrt(x)
times the signed zero phase plus the real remainder. Factor the absolutely convergent sum. -/
theorem characterLogWeightedSum_half_phase_formula {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 < x) :
    (Arithmetic.characterLogWeightedSum x χ - Arithmetic.characterLogWeightedSum (x / 2) χ).re =
      Real.sqrt x * logarithmicHalfPhase χ (Real.log x) + (logarithmicHalfRemainder hne x).re := by
  rw [characterLogWeightedSum_half_exact_zero_formula hN hGRH hp hne hinv hx]
  have he :
    (∑' ρ : ℂ, completedLogHalfZeroTerm χ x ρ) =
      (Real.sqrt x : ℂ) * ∑' ρ : ℂ, completedLogHalfPhaseTerm χ (Real.log x) ρ := by
    rw [← tsum_mul_left]
    exact
      tsum_congr
        (completedLogHalfZeroTerm_eq_sqrt_mul_phase hGRH hp hne hinv
          (show 0 < x by linarith only [hx]))
  rw [he]
  simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, logarithmicHalfPhase]
  ring

/-- For x≥2 and f(j)≥j+1, the inverse-power square series is at most one.
Compare termwise with a geometric series; this bounds both trivial-zero parities. -/
theorem inverse_power_square_series_le_one {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℕ)
    (hf : ∀ j : ℕ, j + 1 ≤ f j) : (∑' j : ℕ, x⁻¹ ^ (f j) / (f j : ℝ) ^ 2) ≤ 1 := by
  have hx0 : 0 < x := by linarith only [hx]
  have hi0 : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0.le
  have hi : x⁻¹ ≤ (1 / 2 : ℝ) := by
    have h := one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 2) hx
    simpa only [one_div] using h
  have hi1 : x⁻¹ < 1 := by linarith only [hi]
  have ht (j : ℕ) : x⁻¹ ^ (f j) / (f j : ℝ) ^ 2 ≤ x⁻¹ ^ (j + 1) := by
    have hkN : 1 ≤ f j := (Nat.succ_le_succ (Nat.zero_le j)).trans (hf j)
    have hk : (1 : ℝ) ≤ f j := Nat.one_le_cast.mpr hkN
    exact
      (div_le_self (pow_nonneg hi0 _) (by nlinarith only [hk])).trans
        (pow_le_pow_of_le_one hi0 hi1.le (hf j))
  have hn (j : ℕ) : 0 ≤ x⁻¹ ^ (f j) / (f j : ℝ) ^ 2 := div_nonneg (pow_nonneg hi0 _) (sq_nonneg _)
  have he : (fun j : ℕ ↦ x⁻¹ ^ (j + 1)) = (fun j : ℕ ↦ x⁻¹ ^ j * x⁻¹) := by
    funext j
    exact pow_succ _ _
  have hs : Summable (fun j : ℕ ↦ x⁻¹ ^ (j + 1)) := by
    rw [he]
    exact (summable_geometric_of_lt_one hi0 hi1).mul_right x⁻¹
  have hb := Summable.tsum_le_tsum ht (Summable.of_nonneg_of_le hn ht hs) hs
  rw [he, tsum_mul_right, tsum_geometric_of_lt_one hi0 hi1] at hb
  apply hb.trans
  rw [← div_eq_inv_mul]
  apply (div_le_iff₀ (sub_pos.mpr hi1)).mpr
  linarith only [hi]

/-- For x≥2 the norm of the exact trivial correction is at most one.
Apply the inverse-power series bound separately for even and odd characters. -/
theorem norm_logarithmicTrivialCorrection_le_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {x : ℝ} (hx : 2 ≤ x) : ‖logarithmicTrivialCorrection χ x‖ ≤ 1 := by
  classical
  have hn (f : ℕ → ℕ) : 0 ≤ ∑' j : ℕ, x⁻¹ ^ (f j) / (f j : ℝ) ^ 2 :=
    tsum_nonneg
      (fun _ ↦
        div_nonneg (pow_nonneg (inv_nonneg.mpr (show 0 ≤ x by linarith only [hx])) _) (sq_nonneg _))
  dsimp only [logarithmicTrivialCorrection]
  by_cases he : χ.Even
  · rw [ite_eq_left he, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hn _)]
    exact
      inverse_power_square_series_le_one hx (fun j ↦ 2 * (j + 1))
        (fun j ↦ Nat.le_mul_of_pos_left _ (by decide : 0 < 2))
  · rw [ite_eq_right he, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hn _)]
    exact
      inverse_power_square_series_le_one hx (fun j ↦ 2 * j + 1)
        (fun j ↦ Nat.add_le_add_right (Nat.le_mul_of_pos_left j (by decide : 0 < 2)) 1)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
