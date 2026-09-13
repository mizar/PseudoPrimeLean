import PseudoPrime.AnalyticNumberTheory.RiemannZeta.Growth
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.GrowthBounds
import PseudoPrime.AnalyticNumberTheory.Gamma.GrowthElementary
import PseudoPrime.AnalyticNumberTheory.General.GeometricDecay

/-! Kernel-independent estimates extracted from the contour applications. -/

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For nonzero `t`, bound `‖ζ'/ζ(σ+it)‖` uniformly over
`σ ∈ [-(2m+1),-1/2]`. The majorant has a Gamma-envelope term depending on `m`,
a term linear in `|t|`, and a hyperbolic-cotangent bound which can grow near
`t=0`. Gamma recurrence estimates later give polynomial control in `m`. -/
theorem exists_norm_logDeriv_riemannZeta_neg_add_mul_I_le_of_mem_Icc :
    ∃ C : ℝ,
      ∀ (m : ℕ) (σ t : ℝ),
        σ ∈ Set.Icc (-(2 * (m : ℝ) + 1)) (-1 / 2) →
          t ≠ 0 →
          ‖logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C +
              8 *
                Real.log
                  (max (max (Real.Gamma 1) (Real.Gamma 2))
                      (max (Real.Gamma (2 * m + 3 / 2)) (Real.Gamma (2 * m + 5 / 2))) +
                    1) +
              20 * Real.pi * |t| +
              Real.pi / 2 * Real.sqrt (1 + 1 / Real.sinh (Real.pi * t / 2) ^ 2) := by
  obtain ⟨C₁, hC₁⟩ :=
    exists_neg_log_norm_Gamma_one_add_add_mul_I_le_uniform
  refine
    ⟨Real.log (2 * Real.pi) + 8 * C₁ +
        ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ),
      fun m σ t hσ ht => ?_⟩
  obtain ⟨hσlo, hσhi⟩ := hσ
  have hσ0 : σ < 0 := by linarith
  have hbase :=
    norm_logDeriv_riemannZeta_neg_add_mul_I_le hσ0 ht
  set M0 : ℝ :=
    max (max (Real.Gamma 1) (Real.Gamma 2))
      (max (Real.Gamma (2 * m + 3 / 2)) (Real.Gamma (2 * m + 5 / 2))) with
    hM0_def
  -- Step (A): the `log(Gbound(r))` term is bounded uniformly in `σ` by `log(M0 + 1)`.
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hGamma1_le : Real.Gamma (-σ + 1 / 2) ≤ max (Real.Gamma 1) (Real.Gamma (2 * m + 3 / 2)) :=
    Real.Gamma_le_max_of_mem_Icc' (by norm_num only)
      (by linarith) (by constructor <;> linarith)
  have hGamma2_le : Real.Gamma (-σ + 3 / 2) ≤ max (Real.Gamma 2) (Real.Gamma (2 * m + 5 / 2)) :=
    Real.Gamma_le_max_of_mem_Icc' (by norm_num only)
      (by linarith) (by constructor <;> linarith)
  have hΓ1M0 : Real.Gamma 1 ≤ M0 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hΓ2M0 : Real.Gamma 2 ≤ M0 := le_trans (le_max_right _ _) (le_max_left _ _)
  have hΓ3M0 : Real.Gamma (2 * m + 3 / 2) ≤ M0 := le_trans (le_max_left _ _) (le_max_right _ _)
  have hΓ4M0 : Real.Gamma (2 * m + 5 / 2) ≤ M0 := le_trans (le_max_right _ _) (le_max_right _ _)
  have hmax_le : max (Real.Gamma (-σ + 1 / 2)) (Real.Gamma (-σ + 3 / 2)) ≤ M0 := by
    apply max_le
    · exact le_trans hGamma1_le (max_le hΓ1M0 hΓ3M0)
    · exact le_trans hGamma2_le (max_le hΓ2M0 hΓ4M0)
  have hΓ1pos : 0 < Real.Gamma (-σ + 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hmax_pos : 0 < max (Real.Gamma (-σ + 1 / 2)) (Real.Gamma (-σ + 3 / 2)) + 1 := by
    have := le_max_left (Real.Gamma (-σ + 1 / 2)) (Real.Gamma (-σ + 3 / 2))
    linarith
  have hlog_le :
    Real.log (max (Real.Gamma (-σ + 1 / 2)) (Real.Gamma (-σ + 3 / 2)) + 1) ≤ Real.log (M0 + 1) :=
    Real.log_le_log hmax_pos (by linarith)
  -- Step (B): the `-log‖Γ(1-σ-it)‖` term is bounded by the `r ≥ 0` uniform bound at `r := -σ`.
  have hr0 : (0 : ℝ) ≤ -σ := by linarith
  have hGammaB := hC₁ (-σ) (-t) hr0
  have heqB :
    (1 : ℂ) + ((-σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I =
      ((1 - σ : ℝ) : ℂ) - (t : ℂ) * Complex.I := by
    push_cast; ring
  rw [heqB] at hGammaB
  have habsB : |(-t : ℝ)| = |t| := abs_neg t
  rw [habsB] at hGammaB
  -- Step (C): the von Mangoldt tail sum is bounded by its value at the segment's right endpoint.
  have h32 : (3 / 2 : ℝ) ≤ 1 - σ := by linarith
  have hsum_le :=
    tsum_vonMangoldt_div_rpow_antitone (x := 3 / 2)
      (y := 1 - σ) (by norm_num only) h32
  linarith [hbase, hlog_le, hGammaB, hsum_le]

/-- A concrete witness constant for `exists_norm_logDeriv_riemannZeta_neg_add_mul_I_le_of_mem_Icc`,
following the `goodHeightSeq`/`PseudoPrime.AnalyticNumberTheory.RiemannZeta.exists_good_height`
`.choose`/`.choose_spec` idiom. -/
noncomputable def qMinusOneHorizontalFarLeftConst : ℝ :=
  exists_norm_logDeriv_riemannZeta_neg_add_mul_I_le_of_mem_Icc.choose

/-- The `m`-dependent term of `farLeftZetaLogDerivBound`, isolated for reuse in the diagonal-limit
construction below. -/
noncomputable def farLeftBTerm (m : ℕ) : ℝ :=
  8 *
    Real.log
      (max (max (Real.Gamma 1) (Real.Gamma 2))
          (max (Real.Gamma (2 * (m : ℝ) + 3 / 2)) (Real.Gamma (2 * (m : ℝ) + 5 / 2))) +
        1)

/-- The explicit `m`- and `t`-dependent bound on `‖ζ'/ζ‖` over the horizontal far-left segment,
as a standalone real-valued function (for readability in the kernel bounds below). -/
noncomputable def farLeftZetaLogDerivBound (m : ℕ) (t : ℝ) : ℝ :=
  qMinusOneHorizontalFarLeftConst + farLeftBTerm m + 20 * Real.pi * |t| +
    Real.pi / 2 * Real.sqrt (1 + 1 / Real.sinh (Real.pi * t / 2) ^ 2)

theorem norm_logDeriv_riemannZeta_neg_add_mul_I_le_of_mem_Icc {m : ℕ} {σ t : ℝ}
    (hσ : σ ∈ Set.Icc (-(2 * (m : ℝ) + 1)) (-1 / 2)) (ht : t ≠ 0) :
    ‖logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ farLeftZetaLogDerivBound m t :=
  exists_norm_logDeriv_riemannZeta_neg_add_mul_I_le_of_mem_Icc.choose_spec m σ t hσ ht

/-- The far-left `ζ'/ζ` bound's `m`-dependent term `farLeftBTerm m → ∞`. -/
theorem tendsto_farLeftBTerm_atTop : Filter.Tendsto farLeftBTerm Filter.atTop Filter.atTop := by
  have h1 :
    Filter.Tendsto
      (fun m : ℕ =>
        max (max (Real.Gamma 1) (Real.Gamma 2))
            (max (Real.Gamma (2 * (m : ℝ) + 3 / 2)) (Real.Gamma (2 * (m : ℝ) + 5 / 2))) +
          1)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop 1
      Gamma.tendsto_max_Gamma_halfInteger_atTop
  exact (Real.tendsto_log_atTop.comp h1).const_mul_atTop (by norm_num only)

/-- `farLeftBTerm m` is positive: its Gamma maximum includes `Γ(1)=1`. -/
theorem farLeftBTerm_pos (m : ℕ) : 0 < farLeftBTerm m := by
  unfold farLeftBTerm
  have hΓ1_le :
    Real.Gamma 1 ≤
      max (max (Real.Gamma 1) (Real.Gamma 2))
        (max (Real.Gamma (2 * (m : ℝ) + 3 / 2)) (Real.Gamma (2 * (m : ℝ) + 5 / 2))) :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hM0_ge_one :
    (1 : ℝ) ≤
      max (max (Real.Gamma 1) (Real.Gamma 2))
        (max (Real.Gamma (2 * (m : ℝ) + 3 / 2)) (Real.Gamma (2 * (m : ℝ) + 5 / 2))) := by
    linarith [Real.Gamma_one, hΓ1_le]
  have hlog_pos :
    0 <
      Real.log
        (max (max (Real.Gamma 1) (Real.Gamma 2))
            (max (Real.Gamma (2 * (m : ℝ) + 3 / 2)) (Real.Gamma (2 * (m : ℝ) + 5 / 2))) +
          1) :=
    Real.log_pos (by linarith)
  linarith

/-- The height `T_m=(m+1)*(farLeftBTerm m+1)` dominates both the segment length
and its logarithmic-derivative envelope. The far-left horizontal integral then
vanishes. Since the segment has negative real part, nonzero height already
avoids all zeta zeros there. -/
noncomputable def farLeftHeightSeq (m : ℕ) : ℝ :=
  ((m : ℝ) + 1) * (farLeftBTerm m + 1)

theorem add_one_le_farLeftHeightSeq (m : ℕ) : (m : ℝ) + 1 ≤ farLeftHeightSeq m := by
  have h1 : (1 : ℝ) ≤ farLeftBTerm m + 1 := by linarith [farLeftBTerm_pos m]
  calc
    (m : ℝ) + 1 = ((m : ℝ) + 1) * 1 := (mul_one _).symm
    _ ≤ ((m : ℝ) + 1) * (farLeftBTerm m + 1) := mul_le_mul_of_nonneg_left h1 (by positivity)

theorem farLeftBTerm_le_farLeftHeightSeq (m : ℕ) : farLeftBTerm m ≤ farLeftHeightSeq m := by
  have h1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have h2 : (0 : ℝ) ≤ farLeftBTerm m := (farLeftBTerm_pos m).le
  calc
    farLeftBTerm m = 1 * farLeftBTerm m := (one_mul _).symm
    _ ≤ ((m : ℝ) + 1) * farLeftBTerm m := mul_le_mul_of_nonneg_right h1 h2
    _ ≤ ((m : ℝ) + 1) * (farLeftBTerm m + 1) :=
      mul_le_mul_of_nonneg_left (by linarith only []) (by linarith only [h1])

theorem farLeftHeightSeq_pos (m : ℕ) : 0 < farLeftHeightSeq m :=
  lt_of_lt_of_le (by positivity) (add_one_le_farLeftHeightSeq m)

theorem one_le_farLeftHeightSeq (m : ℕ) : (1 : ℝ) ≤ farLeftHeightSeq m :=
  le_trans (by linarith only [Nat.cast_nonneg (α := ℝ) m]) (add_one_le_farLeftHeightSeq m)

theorem tendsto_farLeftHeightSeq_atTop :
    Filter.Tendsto farLeftHeightSeq Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_mono add_one_le_farLeftHeightSeq ?_
  exact Filter.tendsto_atTop_add_const_right Filter.atTop 1 tendsto_natCast_atTop_atTop

/-- **`farLeftBTerm` grows at most quadratically in `m`** (a crude, fully explicit bound, obtained
by applying `Real.log_le_sub_one_of_pos` to tame the `(2m+1)·log(2m+3)`-type term coming out of
the elementary `Γ`-upper-bound above — no Stirling asymptotic is used). This is the fact needed to
show `farLeftHeightSeq` itself grows only polynomially, hence is dominated by any exponential
decay `x^{-cm}` (`x > 1`) — the key step in reusing `farLeftHeightSeq` for the left-vertical edge
as well, unifying the two edges' diagonal-limit height sequences. -/
theorem farLeftBTerm_le_poly (m : ℕ) :
    farLeftBTerm m ≤
      8 *
          (Real.log (max (Real.Gamma 1) (Real.Gamma 2) + 4) + Real.log 2 +
            Real.log (Real.Gamma (3 / 2) + 1)) +
        8 * (2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 2) := by
  unfold farLeftBTerm
  have hCQnn : (0 : ℝ) ≤ max (Real.Gamma 1) (Real.Gamma 2) :=
    le_trans (Real.Gamma_pos_of_pos (by norm_num only : (0 : ℝ) < 1)).le (le_max_left _ _)
  have hΓ32pos : (0 : ℝ) < Real.Gamma (3 / 2) := Real.Gamma_pos_of_pos (by norm_num only)
  set CQ : ℝ := max (Real.Gamma 1) (Real.Gamma 2) with hCQ_def
  set R : ℝ := (2 * (m : ℝ) + 3) ^ (2 * m + 1) * (Real.Gamma (3 / 2) + 1) with hR_def
  have hRge1 : (1 : ℝ) ≤ R := by
    rw [hR_def]
    have hpow_ge1 : (1 : ℝ) ≤ (2 * (m : ℝ) + 3) ^ (2 * m + 1) :=
      one_le_pow₀ (by linarith only [Nat.cast_nonneg (α := ℝ) m])
    nlinarith only [hpow_ge1, hΓ32pos]
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le one_pos hRge1
  have hM0_le :
    max (max (Real.Gamma 1) (Real.Gamma 2))
        (max (Real.Gamma (2 * (m : ℝ) + 3 / 2)) (Real.Gamma (2 * (m : ℝ) + 5 / 2))) ≤
      CQ + 2 * R := by
    have hΓ3 : Real.Gamma (2 * (m : ℝ) + 3 / 2) ≤ R := by
      rw [hR_def]
      have h1 := Gamma.Gamma_two_mul_add_three_half_le m
      have h2 : (2 * (m : ℝ) + 2) ^ (2 * m) ≤ (2 * (m : ℝ) + 3) ^ (2 * m) :=
        pow_le_pow_left₀ (by positivity) (by linarith only []) _
      have h3 : (2 * (m : ℝ) + 3) ^ (2 * m) ≤ (2 * (m : ℝ) + 3) ^ (2 * m + 1) := by
        rw [pow_succ]
        exact le_mul_of_one_le_right (by positivity) (by linarith only [Nat.cast_nonneg (α := ℝ) m])
      calc
        Real.Gamma (2 * (m : ℝ) + 3 / 2) ≤ (2 * (m : ℝ) + 2) ^ (2 * m) * Real.Gamma (3 / 2) := h1
        _ ≤ (2 * (m : ℝ) + 3) ^ (2 * m) * Real.Gamma (3 / 2) :=
          mul_le_mul_of_nonneg_right h2 hΓ32pos.le
        _ ≤ (2 * (m : ℝ) + 3) ^ (2 * m + 1) * Real.Gamma (3 / 2) :=
          mul_le_mul_of_nonneg_right h3 hΓ32pos.le
        _ ≤ (2 * (m : ℝ) + 3) ^ (2 * m + 1) * (Real.Gamma (3 / 2) + 1) :=
          mul_le_mul_of_nonneg_left (by linarith only []) (by positivity)
    have hΓ4 : Real.Gamma (2 * (m : ℝ) + 5 / 2) ≤ R := by
      rw [hR_def]
      have h1 := Gamma.Gamma_two_mul_add_five_half_le m
      calc
        Real.Gamma (2 * (m : ℝ) + 5 / 2) ≤ (2 * (m : ℝ) + 3) ^ (2 * m + 1) * Real.Gamma (3 / 2) :=
          h1
        _ ≤ (2 * (m : ℝ) + 3) ^ (2 * m + 1) * (Real.Gamma (3 / 2) + 1) :=
          mul_le_mul_of_nonneg_left (by linarith only []) (by positivity)
    have hpart1 : max (Real.Gamma 1) (Real.Gamma 2) ≤ CQ + 2 * R := by
      rw [hCQ_def]; linarith only [hRpos]
    have hpart2 :
      max (Real.Gamma (2 * (m : ℝ) + 3 / 2)) (Real.Gamma (2 * (m : ℝ) + 5 / 2)) ≤ CQ + 2 * R :=
      max_le (by linarith [hΓ3]) (by linarith [hΓ4])
    exact max_le hpart1 hpart2
  have hlog_le :
    Real.log
        (max (max (Real.Gamma 1) (Real.Gamma 2))
            (max (Real.Gamma (2 * (m : ℝ) + 3 / 2)) (Real.Gamma (2 * (m : ℝ) + 5 / 2))) +
          1) ≤
      Real.log (max (Real.Gamma 1) (Real.Gamma 2) + 4) + Real.log 2 +
        Real.log (Real.Gamma (3 / 2) + 1) +
        (2 * (m : ℝ) + 1) * Real.log (2 * (m : ℝ) + 3) := by
    have hmax_pos :
      (0 : ℝ) <
        max (max (Real.Gamma 1) (Real.Gamma 2))
            (max (Real.Gamma (2 * (m : ℝ) + 3 / 2)) (Real.Gamma (2 * (m : ℝ) + 5 / 2))) +
          1 := by
      have h1le :
        Real.Gamma 1 ≤
          max (max (Real.Gamma 1) (Real.Gamma 2))
            (max (Real.Gamma (2 * (m : ℝ) + 3 / 2)) (Real.Gamma (2 * (m : ℝ) + 5 / 2))) :=
        le_trans (le_max_left _ _) (le_max_left _ _)
      have hΓ1pos := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 by norm_num only)
      linarith only [h1le, hΓ1pos]
    have hstep1 :
      max (max (Real.Gamma 1) (Real.Gamma 2))
            (max (Real.Gamma (2 * (m : ℝ) + 3 / 2)) (Real.Gamma (2 * (m : ℝ) + 5 / 2))) +
          1 ≤
        (CQ + 4) * (R + 1) := by
      nlinarith only [hM0_le, hCQnn, hRpos.le]
    have hCQ4pos : (0 : ℝ) < CQ + 4 := by linarith only [hCQnn]
    have hR1pos : (0 : ℝ) < R + 1 := by linarith only [hRpos]
    have hlog1 :
      Real.log
          (max (max (Real.Gamma 1) (Real.Gamma 2))
              (max (Real.Gamma (2 * (m : ℝ) + 3 / 2)) (Real.Gamma (2 * (m : ℝ) + 5 / 2))) +
            1) ≤
        Real.log (CQ + 4) + Real.log (R + 1) := by
      rw [← Real.log_mul hCQ4pos.ne' hR1pos.ne']
      exact Real.log_le_log hmax_pos hstep1
    have hR1_le : R + 1 ≤ 2 * R := by linarith only [hRge1]
    have hlog2 : Real.log (R + 1) ≤ Real.log 2 + Real.log R :=
      le_trans (Real.log_le_log hR1pos hR1_le) (le_of_eq (Real.log_mul two_ne_zero hRpos.ne'))
    have hlogR :
      Real.log R =
        (2 * (m : ℝ) + 1) * Real.log (2 * (m : ℝ) + 3) + Real.log (Real.Gamma (3 / 2) + 1) := by
      rw [hR_def, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      push_cast; ring
    simp only [hCQ_def] at hlog1
    linarith only [hlog1, hlog2, hlogR]
  have hlog2m3_le : Real.log (2 * (m : ℝ) + 3) ≤ 2 * (m : ℝ) + 2 := by
    have h := Real.log_le_sub_one_of_pos (x := 2 * (m : ℝ) + 3) (by positivity)
    linarith only [h]
  have hcoeff_nn : (0 : ℝ) ≤ 2 * (m : ℝ) + 1 := by positivity
  nlinarith only [hlog_le, mul_le_mul_of_nonneg_left hlog2m3_le hcoeff_nn]

/-- The far-left height sequence grows at most cubically, by the quadratic
bound on `farLeftBTerm`. Thus geometric decay for `x > 1` absorbs it in the
left-vertical integral as well. -/
theorem farLeftHeightSeq_le_poly :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ m : ℕ, farLeftHeightSeq m ≤ G * ((m : ℝ) + 1) ^ 3 := by
  set D : ℝ :=
    8 *
      (Real.log (max (Real.Gamma 1) (Real.Gamma 2) + 4) + Real.log 2 +
        Real.log (Real.Gamma (3 / 2) + 1)) with
    hD_def
  refine ⟨|D| + 97, by positivity, fun m => ?_⟩
  have hB_le := farLeftBTerm_le_poly m
  rw [← hD_def] at hB_le
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hstep1 : farLeftBTerm m ≤ (|D| + 96) * ((m : ℝ) + 1) ^ 2 := by
    nlinarith [hB_le, le_abs_self D, abs_nonneg D, mul_nonneg hmnn hmnn, hmnn]
  have hsq_ge1 : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith [hmnn]
  have hstep2 : farLeftBTerm m + 1 ≤ (|D| + 97) * ((m : ℝ) + 1) ^ 2 := by
    nlinarith [hstep1, hsq_ge1]
  have hm1nn : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  unfold farLeftHeightSeq
  calc
    ((m : ℝ) + 1) * (farLeftBTerm m + 1) ≤ ((m : ℝ) + 1) * ((|D| + 97) * ((m : ℝ) + 1) ^ 2) :=
      mul_le_mul_of_nonneg_left hstep2 hm1nn
    _ = (|D| + 97) * ((m : ℝ) + 1) ^ 3 := by ring

/-- `farLeftHeightSeq m ^ 2 · r ^ m → 0` for `0 ≤ r < 1`: combines `farLeftHeightSeq_le_poly`'s
cubic growth bound with `tendsto_add_one_pow_mul_pow_of_lt_one` (at degree `6`) to show `x > 1`'s
exponential decay dominates `farLeftHeightSeq`'s polynomial growth. -/
theorem tendsto_farLeftHeightSeq_sq_mul_pow_of_lt_one {r : ℝ} (hr : 0 ≤ r) (h'r : r < 1) :
    Filter.Tendsto (fun m : ℕ => farLeftHeightSeq m ^ 2 * r ^ m) Filter.atTop (nhds 0) := by
  obtain ⟨G, hGnn, hG⟩ := farLeftHeightSeq_le_poly
  have hbound :
    ∀ m : ℕ, farLeftHeightSeq m ^ 2 * r ^ m ≤ G ^ 2 * (((m : ℝ) + 1) ^ 3) ^ 2 * r ^ m := by
    intro m
    have h1 : farLeftHeightSeq m ≤ G * ((m : ℝ) + 1) ^ 3 := hG m
    have h2 : (0 : ℝ) ≤ farLeftHeightSeq m := (farLeftHeightSeq_pos m).le
    have h3 : farLeftHeightSeq m ^ 2 ≤ (G * ((m : ℝ) + 1) ^ 3) ^ 2 := pow_le_pow_left₀ h2 h1 2
    calc
      farLeftHeightSeq m ^ 2 * r ^ m ≤ (G * ((m : ℝ) + 1) ^ 3) ^ 2 * r ^ m :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = G ^ 2 * (((m : ℝ) + 1) ^ 3) ^ 2 * r ^ m := by ring
  have htend :
    Filter.Tendsto (fun m : ℕ => G ^ 2 * (((m : ℝ) + 1) ^ 3) ^ 2 * r ^ m) Filter.atTop
      (nhds 0) := by
    have h1 : Filter.Tendsto (fun m : ℕ => ((m : ℝ) + 1) ^ 6 * r ^ m) Filter.atTop (nhds 0) :=
      General.tendsto_add_one_pow_mul_pow_of_lt_one 6 hr h'r
    have h2 :
      (fun m : ℕ => G ^ 2 * (((m : ℝ) + 1) ^ 3) ^ 2 * r ^ m) = fun m : ℕ =>
        G ^ 2 * (((m : ℝ) + 1) ^ 6 * r ^ m) := by
      funext m; ring
    rw [h2]
    simpa only [mul_zero] using h1.const_mul (G ^ 2)
  exact squeeze_zero (fun m => by positivity) hbound htend

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
