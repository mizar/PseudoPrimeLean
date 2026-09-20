/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HadamardLimit
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.GoodHeight

/-!
# Finite zero-ordinate and zero-norm ledgers

Jensen's inequality in `HadamardLimit` bounds the multiplicity-counted zeros in a closed ball.
Their distinct imaginary parts, their negations, and their norms form finite ledgers with
corresponding cardinality bounds. The avoiding-point lemma in `RiemannZeta.GoodHeight`
then selects heights in `[n, 2n]` separated from ordinates, or radii separated from zero norms.
These choices supply zero-free horizontal edges and spheres for logarithmic-derivative estimates.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- The image under imaginary part of the finite divisor support in `closedBall 0 R`.
For primitive nontrivial characters this records all zero ordinates, without multiplicity,
as verified by `completedLFunction_zero_mem_divisorSupport`. -/
noncomputable def primitiveZeroOrdinatesInBall {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (R : ℝ) : Finset ℝ :=
  ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0 : ℂ) R)).finiteSupport
        (isCompact_closedBall (x := (0 : ℂ)) (r := R))).toFinset.image
    Complex.im

/-- For `N > 1`, a primitive nontrivial character with `χ⁻¹ ≠ 1`, and `R > 0`, the
number of distinct zero ordinates in the closed ball is at most the Jensen zero-count bound.
Each ordinate has a zero of positive multiplicity, so image cardinality is bounded by the
multiplicity sum. This feeds the finite-set avoiding-point construction. -/
theorem card_primitiveZeroOrdinatesInBall_le {N : ℕ} [NeZero N] (hN1 : 1 < N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {R : ℝ}
    (hR : 0 < R) :
    (primitiveZeroOrdinatesInBall χ R).card ≤
      Real.log
          (max 1 (completedLFunctionBallBound N (2 * R)) /
            ‖DirichletCharacter.completedLFunction χ 0‖) /
        Real.log 2 := by
  set U := Metric.closedBall (0 : ℂ) R with hU_def
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hAn : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) U := fun z _ =>
    hdiff.analyticAt z
  have hfin :=
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) U).finiteSupport
      (isCompact_closedBall (x := (0 : ℂ)) (r := R))
  have hdiv_pos :
    ∀ u ∈ hfin.toFinset,
      (1 : ℤ) ≤ MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) U u := by
    intro u hu
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hu
    have hnonneg : (0 : ℤ) ≤ MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) U u :=
      MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn u
    omega
  have hcard1 :
    (hfin.toFinset.card : ℝ) ≤
      Real.log
          (max 1 (completedLFunctionBallBound N (2 * R)) /
            ‖DirichletCharacter.completedLFunction χ 0‖) /
        Real.log 2 := by
    have hsum_eq :
      (∑ᶠ u, MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) U u) =
        ∑ u ∈ hfin.toFinset,
          MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) U u := by
      apply finsum_eq_finsetSum_of_support_subset
      rw [Set.Finite.coe_toFinset]
    have hstep :
      (hfin.toFinset.card : ℝ) ≤
        ((∑ᶠ u, MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) U u : ℤ) : ℝ) := by
      rw [hsum_eq]
      push_cast
      calc
        (hfin.toFinset.card : ℝ) = ∑ _u ∈ hfin.toFinset, (1 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤
            ∑ u ∈ hfin.toFinset,
              (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) U u : ℝ) :=
          by
          apply Finset.sum_le_sum
          intro u hu
          exact_mod_cast hdiv_pos u hu
    exact hstep.trans (finsum_divisor_completedLFunction_le hN1 hprimitive hne hinv hR)
  refine le_trans ?_ hcard1
  exact_mod_cast Finset.card_image_le

/-- `completedLFunction χ` is not eventually zero at any point of `closedBall 0 R`: it is entire
and nonzero at the center `0`
(`DirichletLFunction.dirichletCompletedLFunction_zero_ne_zero_of_primitive`), so the
identity theorem on the preconnected ball rules out vanishing identically near any interior
point. -/
theorem completedLFunction_analyticOrderAt_ne_top {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) {R : ℝ} (hR : 0 < R) {u : ℂ}
    (hu : u ∈ Metric.closedBall (0 : ℂ) R) :
    analyticOrderAt (DirichletCharacter.completedLFunction χ) u ≠ ⊤ := by
  intro htop
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hAn :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) R) :=
    fun z _ => hdiff.analyticAt z
  have hUconv : IsPreconnected (Metric.closedBall (0 : ℂ) R) :=
    (convex_closedBall _ _).isPreconnected
  have hcenter : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := Metric.mem_closedBall_self hR.le
  have heq0 : Set.EqOn (DirichletCharacter.completedLFunction χ) 0 (Metric.closedBall (0 : ℂ) R) :=
    hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUconv hu (analyticOrderAt_eq_top.mp htop)
  exact dirichletCompletedLFunction_zero_ne_zero_of_primitive hprimitive hne (heq0 hcenter)

/-- Any zero of `completedLFunction χ` inside `closedBall 0 R` is genuinely counted by `divisor`
(order `≠ 0`, `≠ ⊤`). -/
theorem completedLFunction_zero_mem_divisorSupport {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) {R : ℝ} (hR : 0 < R) {u : ℂ}
    (hu : u ∈ Metric.closedBall (0 : ℂ) R) (hzero : DirichletCharacter.completedLFunction χ u = 0) :
    MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) R)
        u ≠
      0 := by
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hAn :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0 : ℂ) R) :=
    fun z _ => hdiff.analyticAt z
  have hordne0 : analyticOrderAt (DirichletCharacter.completedLFunction χ) u ≠ 0 := by
    rw [Ne, (hAn u hu).analyticOrderAt_eq_zero]
    exact fun h => h hzero
  have hordnetop := completedLFunction_analyticOrderAt_ne_top hprimitive hne hR hu
  have hmap_eq_top_iff :
    ENat.map (Nat.cast : ℕ → ℤ) (analyticOrderAt (DirichletCharacter.completedLFunction χ) u) =
        (⊤ : WithTop ℤ) ↔
      analyticOrderAt (DirichletCharacter.completedLFunction χ) u = ⊤ := by
    rw [← ENat.map_top (Nat.cast : ℕ → ℤ)]
    exact ENat.map_natCast_injective.eq_iff
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hAn hu, ne_eq, WithTop.untop₀_eq_zero, not_or,
    ENat.map_natCast_eq_zero, hmap_eq_top_iff]
  exact ⟨hordne0, hordnetop⟩

/-- For a primitive nontrivial character at level `N > 1`, with `χ⁻¹ ≠ 1` and `n ≥ 1`,
choose `T ∈ [n, 2n]` separated from every zero ordinate in `closedBall 0 (2n)` by the displayed
positive margin. Apply the finite-set avoiding-point lemma to `primitiveZeroOrdinatesInBall`,
using its Jensen cardinality bound at radius `2n` and growth envelope at radius `4n`.
The resulting height protects a horizontal contour edge from zeros. -/
theorem exists_primitiveGoodHeight {N : ℕ} [NeZero N] (hN1 : 1 < N) {χ : DirichletCharacter ℂ N}
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {n : ℝ} (hn : 1 ≤ n) :
    ∃ T ∈ Set.Icc n (2 * n),
      ∀ ρ : ℂ,
        DirichletCharacter.completedLFunction χ ρ = 0 →
          ‖ρ‖ ≤ 2 * n →
          n /
              (4 *
                (Real.log
                      (max 1 (completedLFunctionBallBound N (4 * n)) /
                        ‖DirichletCharacter.completedLFunction χ 0‖) /
                    Real.log 2 +
                  1)) ≤
            |T - ρ.im| := by
  set B :=
    Real.log
        (max 1 (completedLFunctionBallBound N (4 * n)) /
          ‖DirichletCharacter.completedLFunction χ 0‖) /
      Real.log 2 with
    hB_def
  set c : ℝ := n / (4 * (B + 1)) with hc_def
  have hR2n : (0 : ℝ) < 2 * n := by linarith
  have hcard_le : ((primitiveZeroOrdinatesInBall χ (2 * n)).card : ℝ) ≤ B := by
    have hraw := card_primitiveZeroOrdinatesInBall_le hN1 hprimitive hne hinv hR2n
    rwa [show 2 * (2 * n) = 4 * n from by ring] at hraw
  have hBnonneg : (0 : ℝ) ≤ B := le_trans (Nat.cast_nonneg _) hcard_le
  have hc_pos : 0 < c := by
    rw [hc_def]; positivity
  have hc_eq : c * (4 * (B + 1)) = n := by
    rw [hc_def]; field_simp
  have hstep : c * (primitiveZeroOrdinatesInBall χ (2 * n)).card ≤ c * B :=
    mul_le_mul_of_nonneg_left hcard_le hc_pos.le
  have hlenbound : 2 * c * (primitiveZeroOrdinatesInBall χ (2 * n)).card < n := by
    nlinarith [hstep, hc_pos, hBnonneg, hc_eq]
  obtain ⟨T, hT, hTgood⟩ :=
    RiemannZeta.exists_avoiding_point_length hc_pos (show (0 : ℝ) < n by linarith) hlenbound
  refine ⟨T, by rwa [show n + n = 2 * n from by ring] at hT, fun ρ hζ hρ => ?_⟩
  have hu : ρ ∈ Metric.closedBall (0 : ℂ) (2 * n) := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hρ
  have hordne := completedLFunction_zero_mem_divisorSupport hprimitive hne hR2n hu hζ
  have hsupp :
    ρ ∈
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) (2 * n))).support :=
    hordne
  have himmem : ρ.im ∈ primitiveZeroOrdinatesInBall χ (2 * n) := by
    unfold primitiveZeroOrdinatesInBall
    rw [Finset.mem_image]
    refine ⟨ρ, ?_, rfl⟩
    rw [Set.Finite.mem_toFinset]
    exact hsupp
  exact hTgood ρ.im himmem

/--
Generalization of `DirichletLFunction.exists_primitiveGoodHeight`: the window is still `[n, 2n]`,
but the zero-free
protection extends to an independently chosen ball radius `Rmax ≥ 2n` instead of being tied to
`2n` itself. Needed when the window and the protection radius must be decoupled — e.g. the strip
argument's
horizontal-edge instantiation, where the genus sum ranges over a ball much larger than the height
window `[n, 2n]` itself.
-/
theorem exists_primitiveGoodHeightRadius {N : ℕ} [NeZero N] (hN1 : 1 < N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {n : ℝ}
    (hn : 1 ≤ n) {Rmax : ℝ} (hRmax : 2 * n ≤ Rmax) :
    ∃ T ∈ Set.Icc n (2 * n),
      ∀ ρ : ℂ,
        DirichletCharacter.completedLFunction χ ρ = 0 →
          ‖ρ‖ ≤ Rmax →
          n /
              (4 *
                (Real.log
                      (max 1 (completedLFunctionBallBound N (2 * Rmax)) /
                        ‖DirichletCharacter.completedLFunction χ 0‖) /
                    Real.log 2 +
                  1)) ≤
            |T - ρ.im| := by
  set B :=
    Real.log
        (max 1 (completedLFunctionBallBound N (2 * Rmax)) /
          ‖DirichletCharacter.completedLFunction χ 0‖) /
      Real.log 2 with
    hB_def
  set c : ℝ := n / (4 * (B + 1)) with hc_def
  have hRmaxpos : (0 : ℝ) < Rmax := by linarith
  have hcard_le : ((primitiveZeroOrdinatesInBall χ Rmax).card : ℝ) ≤ B :=
    card_primitiveZeroOrdinatesInBall_le hN1 hprimitive hne hinv hRmaxpos
  have hBnonneg : (0 : ℝ) ≤ B := le_trans (Nat.cast_nonneg _) hcard_le
  have hc_pos : 0 < c := by
    rw [hc_def]; positivity
  have hc_eq : c * (4 * (B + 1)) = n := by
    rw [hc_def]; field_simp
  have hstep : c * (primitiveZeroOrdinatesInBall χ Rmax).card ≤ c * B :=
    mul_le_mul_of_nonneg_left hcard_le hc_pos.le
  have hlenbound : 2 * c * (primitiveZeroOrdinatesInBall χ Rmax).card < n := by
    nlinarith [hstep, hc_pos, hBnonneg, hc_eq]
  obtain ⟨T, hT, hTgood⟩ :=
    RiemannZeta.exists_avoiding_point_length hc_pos (show (0 : ℝ) < n by linarith) hlenbound
  refine ⟨T, by rwa [show n + n = 2 * n from by ring] at hT, fun ρ hζ hρ => ?_⟩
  have hu : ρ ∈ Metric.closedBall (0 : ℂ) Rmax := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hρ
  have hordne := completedLFunction_zero_mem_divisorSupport hprimitive hne hRmaxpos hu hζ
  have hsupp :
    ρ ∈
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) Rmax)).support :=
    hordne
  have himmem : ρ.im ∈ primitiveZeroOrdinatesInBall χ Rmax := by
    unfold primitiveZeroOrdinatesInBall
    rw [Finset.mem_image]
    refine ⟨ρ, ?_, rfl⟩
    rw [Set.Finite.mem_toFinset]
    exact hsupp
  exact hTgood ρ.im himmem

/-- The symmetrized ledger: ordinates of zeros inside `closedBall 0 R`, together with their
negations, so that a single avoiding-point selection protects both `+iT` and `-iT` horizontal
lines simultaneously for simultaneous strip bounds. -/
noncomputable def primitiveZeroOrdinatesInBallSymm {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (R : ℝ) : Finset ℝ :=
  primitiveZeroOrdinatesInBall χ R ∪ (primitiveZeroOrdinatesInBall χ R).image (fun x => -x)

/-- The symmetrized ledger has cardinality at most twice the Jensen bound for one ledger. -/
theorem card_primitiveZeroOrdinatesInBallSymm_le {N : ℕ} [NeZero N] (hN1 : 1 < N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {R : ℝ}
    (hR : 0 < R) :
    (primitiveZeroOrdinatesInBallSymm χ R).card ≤
      2 *
        (Real.log
            (max 1 (completedLFunctionBallBound N (2 * R)) /
              ‖DirichletCharacter.completedLFunction χ 0‖) /
          Real.log 2) := by
  unfold primitiveZeroOrdinatesInBallSymm
  have hcardR := card_primitiveZeroOrdinatesInBall_le hN1 hprimitive hne hinv hR
  have hunion_le :
    ((primitiveZeroOrdinatesInBall χ R ∪
            (primitiveZeroOrdinatesInBall χ R).image (fun x => -x)).card :
        ℝ) ≤
      ((primitiveZeroOrdinatesInBall χ R).card : ℝ) +
        (((primitiveZeroOrdinatesInBall χ R).image (fun x => -x)).card : ℝ) := by
    exact_mod_cast Finset.card_union_le _ _
  have himg_le :
    (((primitiveZeroOrdinatesInBall χ R).image (fun x => -x)).card : ℝ) ≤
      ((primitiveZeroOrdinatesInBall χ R).card : ℝ) := by
    exact_mod_cast Finset.card_image_le
  linarith [hunion_le, himg_le, hcardR]

/--
Two-sided analogue of `DirichletLFunction.exists_primitiveGoodHeightRadius`: the same `T ∈ [n, 2n]`
stays at margin `≥ n/(8(B+1))` from *both* the ordinate `ρ.im` and its negation `-ρ.im`, for every
zero `ρ` inside `closedBall 0 Rmax` — i.e. `T` simultaneously protects the horizontal lines
`Im s = T` and `Im s = -T`.
Content: identical avoiding-point construction to
`DirichletLFunction.exists_primitiveGoodHeightRadius`, applied to
the symmetrized ledger `DirichletLFunction.primitiveZeroOrdinatesInBallSymm` (cardinality doubles,
so the margin
denominator doubles from `4` to `8` to keep the same `2c·card < n` pigeonhole bound).
Role: supplies the single good height needed to bound both the top and bottom horizontal contour
edges together in the horizontal-strip estimates.
-/
theorem exists_primitiveGoodHeightRadius_twoSided {N : ℕ} [NeZero N] (hN1 : 1 < N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {n : ℝ}
    (hn : 1 ≤ n) {Rmax : ℝ} (hRmax : 2 * n ≤ Rmax) :
    ∃ T ∈ Set.Icc n (2 * n),
      ∀ ρ : ℂ,
        DirichletCharacter.completedLFunction χ ρ = 0 →
          ‖ρ‖ ≤ Rmax →
          n /
                (8 *
                  (Real.log
                        (max 1 (completedLFunctionBallBound N (2 * Rmax)) /
                          ‖DirichletCharacter.completedLFunction χ 0‖) /
                      Real.log 2 +
                    1)) ≤
              |T - ρ.im| ∧
            n /
                (8 *
                  (Real.log
                        (max 1 (completedLFunctionBallBound N (2 * Rmax)) /
                          ‖DirichletCharacter.completedLFunction χ 0‖) /
                      Real.log 2 +
                    1)) ≤
              |T + ρ.im| := by
  set B :=
    Real.log
        (max 1 (completedLFunctionBallBound N (2 * Rmax)) /
          ‖DirichletCharacter.completedLFunction χ 0‖) /
      Real.log 2 with
    hB_def
  set c : ℝ := n / (8 * (B + 1)) with hc_def
  have hRmaxpos : (0 : ℝ) < Rmax := by linarith
  have hcard_le : ((primitiveZeroOrdinatesInBallSymm χ Rmax).card : ℝ) ≤ 2 * B :=
    card_primitiveZeroOrdinatesInBallSymm_le hN1 hprimitive hne hinv hRmaxpos
  have hBnonneg : (0 : ℝ) ≤ B :=
    le_trans (Nat.cast_nonneg _)
      (card_primitiveZeroOrdinatesInBall_le hN1 hprimitive hne hinv hRmaxpos)
  have hc_pos : 0 < c := by
    rw [hc_def]; positivity
  have hc_eq : c * (8 * (B + 1)) = n := by
    rw [hc_def]; field_simp
  have hstep : c * (primitiveZeroOrdinatesInBallSymm χ Rmax).card ≤ c * (2 * B) :=
    mul_le_mul_of_nonneg_left hcard_le hc_pos.le
  have hlenbound : 2 * c * (primitiveZeroOrdinatesInBallSymm χ Rmax).card < n := by
    nlinarith [hstep, hc_pos, hBnonneg, hc_eq]
  obtain ⟨T, hT, hTgood⟩ :=
    RiemannZeta.exists_avoiding_point_length hc_pos (show (0 : ℝ) < n by linarith) hlenbound
  refine ⟨T, by rwa [show n + n = 2 * n from by ring] at hT, fun ρ hζ hρ => ?_⟩
  have hu : ρ ∈ Metric.closedBall (0 : ℂ) Rmax := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hρ
  have hordne := completedLFunction_zero_mem_divisorSupport hprimitive hne hRmaxpos hu hζ
  have hsupp :
    ρ ∈
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) Rmax)).support :=
    hordne
  have himmem : ρ.im ∈ primitiveZeroOrdinatesInBall χ Rmax := by
    unfold primitiveZeroOrdinatesInBall
    rw [Finset.mem_image]
    refine ⟨ρ, ?_, rfl⟩
    rw [Set.Finite.mem_toFinset]
    exact hsupp
  have hposmem : ρ.im ∈ primitiveZeroOrdinatesInBallSymm χ Rmax := Finset.mem_union_left _ himmem
  have hnegmem : -ρ.im ∈ primitiveZeroOrdinatesInBallSymm χ Rmax :=
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ himmem)
  refine ⟨hTgood ρ.im hposmem, ?_⟩
  have hneg := hTgood (-ρ.im) hnegmem
  rwa [show T - -ρ.im = T + ρ.im from by ring] at hneg

/-! ### the strip argument prerequisite: a "good radius" avoiding every zero norm

`DirichletLFunction.norm_centeredLogDeriv_sub_truncatedGenus_le` in `HadamardLimit` needs a radius
`R` with no zero of `completedLFunction χ` lying exactly on the sphere `‖ρ‖ = R`; this mirrors the
good-height ledger above
(`DirichletLFunction.primitiveZeroOrdinatesInBall`/`DirichletLFunction.exists_primitiveGoodHeight`)
but tracks
zero *norms* instead of *ordinates*. -/

/-- The image under norm of the finite divisor support in `closedBall 0 R`.
For primitive nontrivial characters it records all zero norms. -/
noncomputable def primitiveZeroNormsInBall {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (R : ℝ) :
    Finset ℝ :=
  ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall (0 : ℂ) R)).finiteSupport
        (isCompact_closedBall (x := (0 : ℂ)) (r := R))).toFinset.image
    norm

/-- The `norm`-tracking analogue of `DirichletLFunction.card_primitiveZeroOrdinatesInBall_le`;
identical proof. -/
theorem card_primitiveZeroNormsInBall_le {N : ℕ} [NeZero N] (hN1 : 1 < N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {R : ℝ}
    (hR : 0 < R) :
    (primitiveZeroNormsInBall χ R).card ≤
      Real.log
          (max 1 (completedLFunctionBallBound N (2 * R)) /
            ‖DirichletCharacter.completedLFunction χ 0‖) /
        Real.log 2 := by
  set U := Metric.closedBall (0 : ℂ) R with hU_def
  have hdiff := DirichletCharacter.differentiable_completedLFunction hne
  have hAn : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) U := fun z _ =>
    hdiff.analyticAt z
  have hfin :=
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) U).finiteSupport
      (isCompact_closedBall (x := (0 : ℂ)) (r := R))
  have hdiv_pos :
    ∀ u ∈ hfin.toFinset,
      (1 : ℤ) ≤ MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) U u := by
    intro u hu
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hu
    have hnonneg : (0 : ℤ) ≤ MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) U u :=
      MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn u
    omega
  have hcard1 :
    (hfin.toFinset.card : ℝ) ≤
      Real.log
          (max 1 (completedLFunctionBallBound N (2 * R)) /
            ‖DirichletCharacter.completedLFunction χ 0‖) /
        Real.log 2 := by
    have hsum_eq :
      (∑ᶠ u, MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) U u) =
        ∑ u ∈ hfin.toFinset,
          MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) U u := by
      apply finsum_eq_finsetSum_of_support_subset
      rw [Set.Finite.coe_toFinset]
    have hstep :
      (hfin.toFinset.card : ℝ) ≤
        ((∑ᶠ u, MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) U u : ℤ) : ℝ) := by
      rw [hsum_eq]
      push_cast
      calc
        (hfin.toFinset.card : ℝ) = ∑ _u ∈ hfin.toFinset, (1 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤
            ∑ u ∈ hfin.toFinset,
              (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) U u : ℝ) :=
          by
          apply Finset.sum_le_sum
          intro u hu
          exact_mod_cast hdiv_pos u hu
    exact hstep.trans (finsum_divisor_completedLFunction_le hN1 hprimitive hne hinv hR)
  refine le_trans ?_ hcard1
  exact_mod_cast Finset.card_image_le

/--
Input/assumptions: `1 < N`, a primitive nontrivial character with `χ⁻¹ ≠ 1`, and `n ≥ 1`.
Conclusion: some `R ∈ [n, 2n]` stays at distance `≥ margin` from the norm of every zero of
`completedLFunction χ` inside `closedBall 0 (2n)` — in particular no such zero has `‖ρ‖ = R`.
Content: identical construction to `DirichletLFunction.exists_primitiveGoodHeight`, tracking
`DirichletLFunction.primitiveZeroNormsInBall`
in place of `PseudoPrime.AnalyticNumberTheory.DirichletLFunction.primitiveZeroOrdinatesInBall`.
Role: supplies the finite-radius estimate's
(`DirichletLFunction.norm_centeredLogDeriv_sub_truncatedGenus_le`) zero-free-sphere hypothesis
`hzf` for the strip argument horizontal-line log-derivative bound.
-/
theorem exists_primitiveGoodRadius {N : ℕ} [NeZero N] (hN1 : 1 < N) {χ : DirichletCharacter ℂ N}
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {n : ℝ} (hn : 1 ≤ n) :
    ∃ R ∈ Set.Icc n (2 * n),
      ∀ ρ : ℂ,
        DirichletCharacter.completedLFunction χ ρ = 0 →
          ‖ρ‖ ≤ 2 * n →
          n /
              (4 *
                (Real.log
                      (max 1 (completedLFunctionBallBound N (4 * n)) /
                        ‖DirichletCharacter.completedLFunction χ 0‖) /
                    Real.log 2 +
                  1)) ≤
            |R - ‖ρ‖| := by
  set B :=
    Real.log
        (max 1 (completedLFunctionBallBound N (4 * n)) /
          ‖DirichletCharacter.completedLFunction χ 0‖) /
      Real.log 2 with
    hB_def
  set c : ℝ := n / (4 * (B + 1)) with hc_def
  have hR2n : (0 : ℝ) < 2 * n := by linarith
  have hcard_le : ((primitiveZeroNormsInBall χ (2 * n)).card : ℝ) ≤ B := by
    have hraw := card_primitiveZeroNormsInBall_le hN1 hprimitive hne hinv hR2n
    rwa [show 2 * (2 * n) = 4 * n from by ring] at hraw
  have hBnonneg : (0 : ℝ) ≤ B := le_trans (Nat.cast_nonneg _) hcard_le
  have hc_pos : 0 < c := by
    rw [hc_def]; positivity
  have hc_eq : c * (4 * (B + 1)) = n := by
    rw [hc_def]; field_simp
  have hstep : c * (primitiveZeroNormsInBall χ (2 * n)).card ≤ c * B :=
    mul_le_mul_of_nonneg_left hcard_le hc_pos.le
  have hlenbound : 2 * c * (primitiveZeroNormsInBall χ (2 * n)).card < n := by
    nlinarith [hstep, hc_pos, hBnonneg, hc_eq]
  obtain ⟨R, hR, hRgood⟩ :=
    RiemannZeta.exists_avoiding_point_length hc_pos (show (0 : ℝ) < n by linarith) hlenbound
  refine ⟨R, by rwa [show n + n = 2 * n from by ring] at hR, fun ρ hζ hρ => ?_⟩
  have hu : ρ ∈ Metric.closedBall (0 : ℂ) (2 * n) := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hρ
  have hordne := completedLFunction_zero_mem_divisorSupport hprimitive hne hR2n hu hζ
  have hsupp :
    ρ ∈
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) (2 * n))).support :=
    hordne
  have hnmem : ‖ρ‖ ∈ primitiveZeroNormsInBall χ (2 * n) := by
    unfold primitiveZeroNormsInBall
    rw [Finset.mem_image]
    refine ⟨ρ, ?_, rfl⟩
    rw [Set.Finite.mem_toFinset]
    exact hsupp
  exact hRgood ‖ρ‖ hnmem

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
