/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.Jensen
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCount

/-!
# Quantitative good-height selection

Finite interval avoidance and the Jensen zero-count bound select a height
`T ∈ [H,H+1]` a distance at least `1/(4*jensenLogConst*log(H+2))` from
all zero ordinates within distance two of `H`, for `H ≥ 8`.
The underlying avoidance lemma is independent of zeta: excluded intervals
of total length less than a given interval cannot cover it.
-/

noncomputable section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- If finitely many "forbidden" points `S` have total excluded length `2c·|S| < 1`, some point
of `[a, a+1]` lies at distance `≥ c` from every point of `S`. -/
theorem exists_avoiding_point {S : Finset ℝ} {c a : ℝ} (hc : 0 < c) (hlen : 2 * c * S.card < 1) :
    ∃ T ∈ Set.Icc a (a + 1), ∀ y ∈ S, c ≤ |T - y| := by
  by_contra hcon
  push Not at hcon
  have hsub : Set.Icc a (a + 1) ⊆ ⋃ y ∈ S, Set.Ioo (y - c) (y + c) := by
    intro T hT
    obtain ⟨y, hyS, hy⟩ := hcon T hT
    simp only [Set.mem_iUnion]
    rw [abs_lt] at hy
    exact ⟨y, hyS, by constructor <;> linarith [hy.1, hy.2]⟩
  have hsum_eq :
    ∑ y ∈ S, MeasureTheory.volume (Set.Ioo (y - c) (y + c)) = ENNReal.ofReal (2 * c) * S.card := by
    have hterm : ∀ y ∈ S, MeasureTheory.volume (Set.Ioo (y - c) (y + c)) = ENNReal.ofReal (2 * c) :=
      fun y _ => by
      rw [Real.volume_Ioo]; congr 1; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hfinal : ENNReal.ofReal 1 ≤ ENNReal.ofReal (2 * c) * (S.card : ENNReal) := by
    calc
      ENNReal.ofReal (1 : ℝ) = MeasureTheory.volume (Set.Icc a (a + 1)) := by
        rw [Real.volume_Icc]; congr 1; ring
      _ ≤ MeasureTheory.volume (⋃ y ∈ S, Set.Ioo (y - c) (y + c)) := MeasureTheory.measure_mono hsub
      _ ≤ ∑ y ∈ S, MeasureTheory.volume (Set.Ioo (y - c) (y + c)) :=
        MeasureTheory.measure_biUnion_finset_le S _
      _ = ENNReal.ofReal (2 * c) * S.card := hsum_eq
  rw [← ENNReal.ofReal_natCast S.card, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hfinal
  linarith [hfinal]

/-- Generalization of `PseudoPrime.AnalyticNumberTheory.RiemannZeta.exists_avoiding_point` to
an interval `[a, a+L]` of arbitrary positive
length `L` (not just `L = 1`). -/
theorem exists_avoiding_point_length {S : Finset ℝ} {c a L : ℝ} (hc : 0 < c) (_hL : 0 < L)
    (hlen : 2 * c * S.card < L) : ∃ T ∈ Set.Icc a (a + L), ∀ y ∈ S, c ≤ |T - y| := by
  by_contra hcon
  push Not at hcon
  have hsub : Set.Icc a (a + L) ⊆ ⋃ y ∈ S, Set.Ioo (y - c) (y + c) := by
    intro T hT
    obtain ⟨y, hyS, hy⟩ := hcon T hT
    simp only [Set.mem_iUnion]
    rw [abs_lt] at hy
    exact ⟨y, hyS, by constructor <;> linarith [hy.1, hy.2]⟩
  have hsum_eq :
    ∑ y ∈ S, MeasureTheory.volume (Set.Ioo (y - c) (y + c)) = ENNReal.ofReal (2 * c) * S.card := by
    have hterm : ∀ y ∈ S, MeasureTheory.volume (Set.Ioo (y - c) (y + c)) = ENNReal.ofReal (2 * c) :=
      fun y _ => by
      rw [Real.volume_Ioo]
      congr 1
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hfinal : ENNReal.ofReal L ≤ ENNReal.ofReal (2 * c) * (S.card : ENNReal) := by
    calc
      ENNReal.ofReal L = MeasureTheory.volume (Set.Icc a (a + L)) := by
        rw [Real.volume_Icc]; congr 1; ring
      _ ≤ MeasureTheory.volume (⋃ y ∈ S, Set.Ioo (y - c) (y + c)) := MeasureTheory.measure_mono hsub
      _ ≤ ∑ y ∈ S, MeasureTheory.volume (Set.Ioo (y - c) (y + c)) :=
        MeasureTheory.measure_biUnion_finset_le S _
      _ = ENNReal.ofReal (2 * c) * S.card := hsum_eq
  rw [← ENNReal.ofReal_natCast S.card, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hfinal
  linarith [hfinal]

/-! ### Connecting to `ζ`: zeros near a good height lie in the Jensen disk -/

/-- A zero of `ζ` with nonzero ordinate is nontrivial, hence `0 ≤ Re ρ` (the `Re ρ ≤ 1` half is
immediate from `riemannZeta_ne_zero_of_one_lt_re`; the content here is ruling out `Re ρ < 0`,
which for an actual zero would force it to be trivial, i.e. a negative even integer, which has
zero imaginary part). -/
theorem riemannZeta_zero_re_nonneg_of_im_ne_zero {ρ : ℂ} (hζ : riemannZeta ρ = 0) (him : ρ.im ≠ 0) :
    0 ≤ ρ.re := by
  by_contra h
  push Not at h
  apply him
  by_cases hnt : ∀ n : ℕ, ρ ≠ -2 * (n + 1)
  · exact absurd hζ (riemannZeta_ne_zero_of_re_neg h hnt)
  · push Not at hnt
    obtain ⟨n, hn⟩ := hnt
    rw [hn]
    simp only [neg_mul, Complex.neg_im, Complex.mul_im, Complex.re_ofNat, Complex.add_im,
      Complex.natCast_im, Complex.one_im, add_zero, mul_zero, Complex.im_ofNat, Complex.add_re,
      Complex.natCast_re, Complex.one_re, zero_mul, neg_zero]

theorem riemannZeta_zero_re_le_one {ρ : ℂ} (hζ : riemannZeta ρ = 0) : ρ.re ≤ 1 := by
  by_contra h
  push Not at h
  exact riemannZeta_ne_zero_of_one_lt_re h hζ

/-- Any zero of `ζ` whose ordinate is within `2` of a height `H ≥ 8` lies in the Jensen disk of
radius `37/10` around `PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensenCenter H`
(the same disk `PseudoPrime.AnalyticNumberTheory.RiemannZeta.finsum_divisor_riemannZeta_le_explicit`
counts zeros in). -/
theorem riemannZeta_zero_mem_jensenBall {H : ℝ} (hH : 8 ≤ H) {ρ : ℂ} (hζ : riemannZeta ρ = 0)
    (him : |ρ.im - H| ≤ 2) : ρ ∈ Metric.closedBall (jensenCenter H) (37 / 10) := by
  have himpos : (0 : ℝ) < ρ.im := by
    have h1 := (abs_le.mp him).1
    linarith
  have hre0 : 0 ≤ ρ.re := riemannZeta_zero_re_nonneg_of_im_ne_zero hζ himpos.ne'
  have hre1 : ρ.re ≤ 1 := riemannZeta_zero_re_le_one hζ
  simp only [Metric.mem_closedBall, dist_eq_norm]
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  have hre_eq : (ρ - jensenCenter H).re = ρ.re - 3 := by simp only [Complex.sub_re, jensenCenter_re]
  have him_eq : (ρ - jensenCenter H).im = ρ.im - H := by simp only [Complex.sub_im, jensenCenter_im]
  rw [hre_eq, him_eq]
  rw [show (37 / 10 : ℝ) = Real.sqrt ((37 / 10) ^ 2) from (Real.sqrt_sq (by norm_num only)).symm]
  apply Real.sqrt_le_sqrt
  have h1 : (ρ.re - 3) ^ 2 ≤ 9 := by nlinarith [hre0, hre1]
  have h2 : (ρ.im - H) ^ 2 ≤ 4 := by nlinarith [abs_le.mp him]
  nlinarith [h1, h2]

/-! ### The finite set of zero ordinates near a height `H`, with a cardinality bound -/

/-- The finite set of ordinates of zeros of `ζ` inside the Jensen disk around
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.jensenCenter H`. -/
noncomputable def zeroOrdinatesNear (H : ℝ) : Finset ℝ :=
  ((MeromorphicOn.divisor riemannZeta (Metric.closedBall (jensenCenter H) (37 / 10))).finiteSupport
        (isCompact_closedBall _ _)).toFinset.image
    Complex.im

theorem card_zeroOrdinatesNear_le {H : ℝ} (hH : 8 ≤ H) :
    (zeroOrdinatesNear H).card ≤
      ((∑ᶠ u, MeromorphicOn.divisor riemannZeta (Metric.closedBall (jensenCenter H) (37 / 10)) u :
          ℤ) :
        ℝ) := by
  set U := Metric.closedBall (jensenCenter H) (37 / 10)
  have hAn : AnalyticOnNhd ℂ riemannZeta U :=
    (jensen_analyticOnNhd (by linarith only [hH] : (4 : ℝ) ≤ H)).mono
      (Metric.closedBall_subset_closedBall (by norm_num only))
  have hfin := (MeromorphicOn.divisor riemannZeta U).finiteSupport (isCompact_closedBall _ _)
  have hdiv_pos : ∀ u ∈ hfin.toFinset, (1 : ℤ) ≤ MeromorphicOn.divisor riemannZeta U u := by
    intro u hu
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hu
    have hnonneg : (0 : ℤ) ≤ MeromorphicOn.divisor riemannZeta U u :=
      MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn u
    omega
  have hcard1 : hfin.toFinset.card ≤ ((∑ᶠ u, MeromorphicOn.divisor riemannZeta U u : ℤ) : ℝ) := by
    have hsum_eq :
      (∑ᶠ u, MeromorphicOn.divisor riemannZeta U u) =
        ∑ u ∈ hfin.toFinset, MeromorphicOn.divisor riemannZeta U u := by
      apply finsum_eq_finsetSum_of_support_subset
      rw [Set.Finite.coe_toFinset]
    rw [hsum_eq]
    push_cast
    calc
      (hfin.toFinset.card : ℝ) = ∑ _u ∈ hfin.toFinset, (1 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ u ∈ hfin.toFinset, (MeromorphicOn.divisor riemannZeta U u : ℝ) := by
        apply Finset.sum_le_sum
        intro u hu
        exact_mod_cast hdiv_pos u hu
  refine le_trans ?_ hcard1
  exact_mod_cast Finset.card_image_le

/-- `ζ` is not eventually zero at any point of the Jensen disk: since it's analytic throughout
the (preconnected) disk and nonzero at the center, the identity theorem rules out `ζ` vanishing
identically near any interior point. -/
theorem riemannZeta_analyticOrderAt_ne_top {H : ℝ} (hH : 4 ≤ H) {u : ℂ}
    (hu : u ∈ Metric.closedBall (jensenCenter H) (37 / 10)) :
    analyticOrderAt riemannZeta u ≠ ⊤ := by
  intro htop
  have hAn : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall (jensenCenter H) (37 / 10)) :=
    (jensen_analyticOnNhd hH).mono (Metric.closedBall_subset_closedBall (by norm_num only))
  have hUconv : IsPreconnected (Metric.closedBall (jensenCenter H) (37 / 10)) :=
    (convex_closedBall _ _).isPreconnected
  have hcenter : jensenCenter H ∈ Metric.closedBall (jensenCenter H) (37 / 10) :=
    Metric.mem_closedBall_self (by norm_num only)
  have heq0 : Set.EqOn riemannZeta 0 (Metric.closedBall (jensenCenter H) (37 / 10)) :=
    hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUconv hu (analyticOrderAt_eq_top.mp htop)
  exact jensen_center_ne_zero H (heq0 hcenter)

/-- Any zero of `ζ` inside the Jensen disk is genuinely counted by `divisor` (order ≠ 0, ≠ ⊤). -/
theorem riemannZeta_zero_mem_divisorSupport {H : ℝ} (hH : 4 ≤ H) {u : ℂ}
    (hu : u ∈ Metric.closedBall (jensenCenter H) (37 / 10)) (hζ : riemannZeta u = 0) :
    MeromorphicOn.divisor riemannZeta (Metric.closedBall (jensenCenter H) (37 / 10)) u ≠ 0 := by
  have hAn : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall (jensenCenter H) (37 / 10)) :=
    (jensen_analyticOnNhd hH).mono (Metric.closedBall_subset_closedBall (by norm_num only))
  have hordne0 : analyticOrderAt riemannZeta u ≠ 0 := by
    rw [Ne, (hAn u hu).analyticOrderAt_eq_zero]
    exact fun h => h hζ
  have hordnetop : analyticOrderAt riemannZeta u ≠ ⊤ := riemannZeta_analyticOrderAt_ne_top hH hu
  have hmap_eq_top_iff :
    ENat.map (Nat.cast : ℕ → ℤ) (analyticOrderAt riemannZeta u) = (⊤ : WithTop ℤ) ↔
      analyticOrderAt riemannZeta u = ⊤ := by
    rw [← ENat.map_top (Nat.cast : ℕ → ℤ)]
    exact ENat.map_natCast_injective.eq_iff
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hAn hu, ne_eq, WithTop.untop₀_eq_zero, not_or,
    ENat.map_natCast_eq_zero, hmap_eq_top_iff]
  exact ⟨hordne0, hordnetop⟩

/-- For `H ≥ 8`, choose `T ∈ [H,H+1]` whose distance from every zeta-zero
ordinate with `|ρ.im-H| ≤ 2` is at least `1/(4*jensenLogConst*log(H+2))`. -/
theorem exists_good_height {H : ℝ} (hH : 8 ≤ H) :
    ∃ T ∈ Set.Icc H (H + 1),
      ∀ ρ : ℂ,
        riemannZeta ρ = 0 →
          |ρ.im - H| ≤ 2 → 1 / (4 * jensenLogConst * Real.log (H + 2)) ≤ |T - ρ.im| := by
  have hlogpos : (0 : ℝ) < Real.log (H + 2) := Real.log_pos (by linarith only [hH])
  have hLCpos : (0 : ℝ) < jensenLogConst := by
    unfold jensenLogConst
    have h1 : (0 : ℝ) ≤ Real.log (9 + 8 * sawtoothRemainderBound (-9 / 10)) :=
      Real.log_nonneg (by linarith [sawtoothRemainderBound_nonneg (-9 / 10)])
    have h2 : (0 : ℝ) < Real.log 10 := Real.log_pos (by norm_num only)
    have h3 : (0 : ℝ) < Real.log (39 / 37) := Real.log_pos (by norm_num only)
    positivity
  set c : ℝ := 1 / (4 * jensenLogConst * Real.log (H + 2)) with hc_def
  have hc_pos : 0 < c := by positivity
  have hlenbound : 2 * c * (zeroOrdinatesNear H).card < 1 := by
    have hcard_le := card_zeroOrdinatesNear_le hH
    have hexplicit := finsum_divisor_riemannZeta_le_explicit hH
    have hcard_le' : ((zeroOrdinatesNear H).card : ℝ) ≤ jensenLogConst * Real.log (H + 2) :=
      hcard_le.trans hexplicit
    have hLpos : (0 : ℝ) < jensenLogConst * Real.log (H + 2) := by positivity
    calc
      2 * c * (zeroOrdinatesNear H).card ≤ 2 * c * (jensenLogConst * Real.log (H + 2)) :=
        mul_le_mul_of_nonneg_left hcard_le' (by positivity)
      _ = 1 / 2 := by
        rw [hc_def]; field_simp; norm_num only
      _ < 1 := by norm_num only
  obtain ⟨T, hT, hTgood⟩ := exists_avoiding_point hc_pos hlenbound
  refine ⟨T, hT, fun ρ hζ him => ?_⟩
  have hmem : ρ ∈ Metric.closedBall (jensenCenter H) (37 / 10) :=
    riemannZeta_zero_mem_jensenBall hH hζ him
  have hordne :
    MeromorphicOn.divisor riemannZeta (Metric.closedBall (jensenCenter H) (37 / 10)) ρ ≠ 0 :=
    riemannZeta_zero_mem_divisorSupport (by linarith only [hH]) hmem hζ
  have hsupp :
    ρ ∈
      (MeromorphicOn.divisor riemannZeta (Metric.closedBall (jensenCenter H) (37 / 10))).support :=
    hordne
  have himmem : ρ.im ∈ zeroOrdinatesNear H := by
    unfold zeroOrdinatesNear
    rw [Finset.mem_image]
    refine ⟨ρ, ?_, rfl⟩
    rw [Set.Finite.mem_toFinset]
    exact hsupp
  exact hTgood ρ.im himmem

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
