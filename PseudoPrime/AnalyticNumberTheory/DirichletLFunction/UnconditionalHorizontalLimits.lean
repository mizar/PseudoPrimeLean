/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalHorizontalBounds

/-! # Unconditional horizontal height sequences with vanishing normalized error -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Positive scale and separation margins, quadratic height and radius lower bounds,
and logarithmic majorants imply a clean normalized horizontal-error estimate.
Compare denominators and absorb the separation inverse in the genus term.
This scalar inequality separates contour geometry from asymptotic convergence. -/
theorem horizontal_normalized_error_le_clean (n R T δ A B P H : ℝ) (hn : 0 < n) (hR : n ≤ R)
    (hT : n ≤ T) (hδ : 0 < δ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 ≤ H) (hAP : A ≤ Real.log 2 * P + 1)
    (hBP : B ≤ P) (hδinv : δ⁻¹ ≤ 8 * (P + 1) / n) :
    (768 * n * A / R ^ 2 + 8 * n * B / R ^ 2 + 4 * n * H * Real.sqrt B / δ) / T ^ 2 ≤
      (768 * (Real.log 2 * P + 1) + 8 * P) / n ^ 3 + 32 * H * (Real.sqrt P * (P + 1)) / n ^ 2 := by
  have hT2 : n ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hn.le hT 2
  have hR2 : n ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hn.le hR 2
  have hdenom : n ^ 4 ≤ R ^ 2 * T ^ 2 := by
    have h := mul_le_mul hR2 hT2 (sq_nonneg n) (sq_nonneg R)
    nlinarith only [h]
  have hswap (a : ℝ) (ha : 0 ≤ a) : a / R ^ 2 / T ^ 2 ≤ a / n ^ 4 := by
    rw [div_div]
    exact div_le_div_of_nonneg_left ha (pow_pos hn _) hdenom
  have hcancel (a : ℝ) : n * a / n ^ 4 = a / n ^ 3 := by
    rw [show n ^ 4 = n * n ^ 3 by ring, mul_div_mul_left _ _ hn.ne']
  have hterm1 : 768 * n * A / R ^ 2 / T ^ 2 ≤ 768 * (Real.log 2 * P + 1) / n ^ 3 := by
    calc
      _ ≤ (768 * n * A) / n ^ 4 := hswap _ (mul_nonneg (mul_nonneg (by norm_num only) hn.le) hA)
      _ = 768 * A / n ^ 3 := by rw [show 768 * n * A = n * (768 * A) by ring, hcancel]
      _ ≤ _ :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hAP (by norm_num only))
          (pow_nonneg hn.le _)
  have hterm2 : 8 * n * B / R ^ 2 / T ^ 2 ≤ 8 * P / n ^ 3 := by
    calc
      _ ≤ (8 * n * B) / n ^ 4 := hswap _ (mul_nonneg (mul_nonneg (by norm_num only) hn.le) hB)
      _ = 8 * B / n ^ 3 := by rw [show 8 * n * B = n * (8 * B) by ring, hcancel]
      _ ≤ _ :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hBP (by norm_num only))
          (pow_nonneg hn.le _)
  have hbase : 0 ≤ 4 * n * H := mul_nonneg (mul_nonneg (by norm_num only) hn.le) hH
  have hgenus : 4 * n * H * Real.sqrt B / δ ≤ 32 * H * (Real.sqrt P * (P + 1)) := by
    calc
      _ ≤ 4 * n * H * Real.sqrt P / δ :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hBP) hbase) hδ.le
      _ ≤ (4 * n * H * Real.sqrt P) * (8 * (P + 1) / n) :=
        mul_le_mul_of_nonneg_left hδinv (mul_nonneg hbase (Real.sqrt_nonneg _))
      _ = _ := by
        rw [← mul_div_assoc]
        rw [show 4 * n * H * Real.sqrt P * (8 * (P + 1)) = (32 * H * (Real.sqrt P * (P + 1))) * n by
            ring,
          mul_div_cancel_right₀ _ hn.ne']
  have hgenusnonneg : 0 ≤ 4 * n * H * Real.sqrt B / δ :=
    div_nonneg (mul_nonneg hbase (Real.sqrt_nonneg _)) hδ.le
  have hterm3 : 4 * n * H * Real.sqrt B / δ / T ^ 2 ≤ 32 * H * (Real.sqrt P * (P + 1)) / n ^ 2 :=
    (div_le_div_of_nonneg_left hgenusnonneg (pow_pos hn _) hT2).trans
      (div_le_div_of_nonneg_right hgenus (sq_nonneg n))
  have hsum := add_le_add (add_le_add hterm1 hterm2) hterm3
  convert hsum using 1 <;> ring

/-- For a fixed primitive nonprincipal character, one positive constant controls the
Jensen logarithm and growth numerator uniformly over all radii between one and
thirty-two times every sufficiently large scale. Compare the growth numerator
monotonically with the outer radius and use its existing logarithmic majorant.
This supplies the budgets for both the radius and ordinate separation. -/
theorem exists_uniform_horizontal_log_budget {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) :
    ∃ K : ℝ,
      0 < K ∧
        ∀ᶠ n : ℝ in Filter.atTop,
          1 ≤ n ∧
            ∀ u : ℝ,
              1 ≤ u →
                u ≤ 32 * n →
                Real.log (max 1 (completedLFunctionBallBound q u) / ‖χ.completedLFunction 0‖) /
                      Real.log 2 ≤
                    K * n * Real.log n ∧
                  (4 * (q : ℝ) + 3) * (u + 3) * Real.log (u + 3) -
                      Real.log ‖χ.completedLFunction 0‖ ≤
                    Real.log 2 * (K * n * Real.log n) := by
  obtain ⟨K, hK, hbudget⟩ := exists_K_forall_H2LogBound_thirtyTwo_le hq hp hne
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbudget, Filter.eventually_ge_atTop (1 : ℝ)] with n hn hnge
  refine ⟨hnge, ?_⟩
  intro u hu hun
  have hmono := General.add_three_mul_log_add_three_mono (zero_le_one.trans hu) hun
  have hcoef : 0 ≤ 4 * (q : ℝ) + 3 := by linarith only [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
  have hmul := mul_le_mul_of_nonneg_left hmono hcoef
  have hnum :
    (4 * (q : ℝ) + 3) * (u + 3) * Real.log (u + 3) - Real.log ‖χ.completedLFunction 0‖ ≤
      (4 * (q : ℝ) + 3) * (32 * n + 3) * Real.log (32 * n + 3) -
        Real.log ‖χ.completedLFunction 0‖ := by
    nlinarith only [hmul]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  refine
    ⟨(H2LogBound_le_explicit hq hp hne hu).trans
        ((div_le_div_of_nonneg_right hnum hlog2.le).trans hn),
      ?_⟩
  have hmain := (div_le_iff₀ hlog2).mp hn
  nlinarith only [hnum, hmain]

/-- For a fixed inverse-square mass and positive logarithmic budget coefficient,
collect the coarse height-normalized remainder and genus majorants. The first
terms decay as logarithm divided by scale squared and inverse scale cubed; the
last uses the square-root logarithmic majorant. This function controls the
unconditional horizontal errors independently of the real coordinate. -/
noncomputable def unconditionalHorizontalCleanEnvelope (M K n : ℝ) : ℝ :=
  ((768 * Real.log 2 + 8) * K) * (Real.log n / n ^ 2) + 768 / n ^ 3 +
    (32 * Real.sqrt M) * (Real.sqrt (K * n * Real.log n) * (K * n * Real.log n + 1) / n ^ 2)

/-- For fixed mass and positive budget coefficient, the clean horizontal error tends
to zero at infinity. Apply the logarithmic and square-root decay limits termwise.
This permits squeezing normalized horizontal logarithmic derivatives. -/
theorem tendsto_unconditionalHorizontalCleanEnvelope (M K : ℝ) (hK : 0 < K) :
    Filter.Tendsto (unconditionalHorizontalCleanEnvelope M K) Filter.atTop (nhds 0) := by
  have hfirst := General.tendsto_log_div_sq_atTop.const_mul ((768 * Real.log 2 + 8) * K)
  have hsecond :=
    (tendsto_inv_atTop_zero.comp
          (Filter.tendsto_pow_atTop (by norm_num only : (3 : ℕ) ≠ 0))).const_mul
      (768 : ℝ)
  have hthird := (General.tendsto_sqrt_mul_add_one_div_sq_atTop K hK).const_mul (32 * Real.sqrt M)
  have hsum := (hfirst.add hsecond).add hthird
  change
    Filter.Tendsto
      (fun n : ℝ ↦
        ((768 * Real.log 2 + 8) * K) * (Real.log n / n ^ 2) + 768 / n ^ 3 +
          (32 * Real.sqrt M) * (Real.sqrt (K * n * Real.log n) * (K * n * Real.log n + 1) / n ^ 2))
      Filter.atTop (nhds 0)
  simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero, add_zero] using hsum

/-- For a nonzero scale, divide a linear logarithmic numerator by its cube and cancel
one scale factor. This identifies the numerical bound with the clean envelope. -/
theorem horizontal_log_numerator_div_cube (a b K n : ℝ) (hn : n ≠ 0) :
    (a * (K * n * Real.log n) + b) / n ^ 3 = a * K * (Real.log n / n ^ 2) + b / n ^ 3 := by
  rw [show a * (K * n * Real.log n) + b = n * (a * K * Real.log n) + b by ring, add_div]
  congr 1
  rw [show n ^ 3 = n * n ^ 2 by ring, mul_div_mul_left _ _ hn]
  ring

/-- A pointwise centered logarithmic-derivative bound with point norm at most four
times the scale yields the normalized clean error bound. Compare its three
nonnegative coefficients and use the scalar denominator estimate.
This applies the same numerical majorant on both signed horizontal edges. -/
theorem normalized_horizontal_point_bound (F u n R T δ A B P H : ℝ) (hn : 0 < n) (hu : u ≤ 4 * n)
    (hR : n ≤ R) (hT : n ≤ T) (hδ : 0 < δ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hAP : A ≤ Real.log 2 * P + 1) (hBP : B ≤ P) (hδinv : δ⁻¹ ≤ 8 * (P + 1) / n)
    (hF : F ≤ 192 * u * A / R ^ 2 + 2 * u * B / R ^ 2 + u * H * Real.sqrt B / δ) :
    F / T ^ 2 ≤
      (768 * (Real.log 2 * P + 1) + 8 * P) / n ^ 3 + 32 * H * (Real.sqrt P * (P + 1)) / n ^ 2 := by
  have hfirst : 192 * u * A ≤ 768 * n * A := by nlinarith only [mul_le_mul_of_nonneg_right hu hA]
  have hsecond : 2 * u * B ≤ 8 * n * B := by nlinarith only [mul_le_mul_of_nonneg_right hu hB]
  have hthird : u * H * Real.sqrt B ≤ 4 * n * H * Real.sqrt B :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hu hH) (Real.sqrt_nonneg _)
  have hnum :=
    add_le_add
      (add_le_add (div_le_div_of_nonneg_right hfirst (sq_nonneg R))
        (div_le_div_of_nonneg_right hsecond (sq_nonneg R)))
      (div_le_div_of_nonneg_right hthird hδ.le)
  exact
    (div_le_div_of_nonneg_right (hF.trans hnum) (sq_nonneg T)).trans
      (horizontal_normalized_error_le_clean n R T δ A B P H hn hR hT hδ hA hB hH hAP hBP hδinv)

/-- For a fixed primitive nonprincipal character, a positive budget coefficient
works at every sufficiently large real scale: one common height gives nonvanishing
and a clean normalized bound on both signed edges of the growing real strip.
Use the unconditional separated-point genus estimate and uniform Jensen budgets.
This removes RH before the horizontal contour limit is taken. -/
theorem exists_eventually_unconditional_horizontal_clean_bound {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    ∃ K : ℝ,
      0 < K ∧
        ∀ᶠ n : ℝ in Filter.atTop,
          ∃ T ∈ Set.Icc n (2 * n),
            ∀ σ : ℝ,
              |σ| ≤ 2 * n →
                ‖logDeriv χ.completedLFunction ((σ : ℂ) + T * Complex.I) -
                          logDeriv χ.completedLFunction 0‖ /
                      T ^ 2 ≤
                    unconditionalHorizontalCleanEnvelope (completedLFunctionInverseSquareMass χ) K
                      n ∧
                  ‖logDeriv χ.completedLFunction ((σ : ℂ) - T * Complex.I) -
                          logDeriv χ.completedLFunction 0‖ /
                      T ^ 2 ≤
                    unconditionalHorizontalCleanEnvelope (completedLFunctionInverseSquareMass χ) K
                      n ∧
                  χ.completedLFunction ((σ : ℂ) + T * Complex.I) ≠ 0 ∧
                  χ.completedLFunction ((σ : ℂ) - T * Complex.I) ≠ 0 := by
  obtain ⟨K, hK, hbudget⟩ := exists_uniform_horizontal_log_budget hq hp hne
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbudget] with n hn
  obtain ⟨hnge, hb⟩ := hn
  obtain ⟨T, hT, R, hR, δ, hδ, hδeq, hbounds⟩ :=
    exists_primitiveHorizontalScaledStripLogDerivBound_unconditionally hq hp hne hinv hnge
  have hnpos : 0 < n := zero_lt_one.trans_le hnge
  have hRone : 1 ≤ R := by linarith only [hR.1, hnge]
  have hRpos : 0 < R := zero_lt_one.trans_le hRone
  have hAR := (hadamardHorizontalErrorCoeff_pos hq hp hne hinv hRone).le
  have hBR := H2LogBound_nonneg (Nat.lt_of_lt_of_le (by norm_num only : 1 < 2) hq) hp hne hinv hRpos
  obtain ⟨_, hARupper⟩ := hb R hRone (by linarith only [hR.2, hnge])
  obtain ⟨hBRupper, _⟩ := hb (2 * R) (by linarith only [hR.1, hnge]) (by linarith only [hR.2])
  obtain ⟨hB32upper, _⟩ := hb (32 * n) (by linarith only [hnge]) (le_refl _)
  have hinv : δ⁻¹ ≤ 8 * (K * n * Real.log n + 1) / n := by
    rw [hδeq, inv_div]
    have hnum :
      8 *
          (Real.log
                (max 1 (completedLFunctionBallBound q (2 * (16 * n))) / ‖χ.completedLFunction 0‖) /
              Real.log 2 +
            1) ≤
        8 * (K * n * Real.log n + 1) := by
      rw [show (2 : ℝ) * (16 * n) = 32 * n by ring]
      linarith only [hB32upper]
    exact div_le_div_of_nonneg_right hnum hnpos.le
  refine ⟨T, hT, ?_⟩
  intro σ hσ
  obtain ⟨hplus, hminus, hnplus, hnminus⟩ := hbounds σ hσ
  have hTnonneg : 0 ≤ T := (zero_le_one.trans hnge).trans hT.1
  have hnormplus : ‖(σ : ℂ) + T * Complex.I‖ ≤ 4 * n := by
    have h := norm_add_le (σ : ℂ) ((T : ℂ) * Complex.I)
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
      abs_of_nonneg hTnonneg] at h
    linarith only [h, hσ, hT.2]
  have hnormminus : ‖(σ : ℂ) - T * Complex.I‖ ≤ 4 * n := by
    have h := norm_sub_le (σ : ℂ) ((T : ℂ) * Complex.I)
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
      abs_of_nonneg hTnonneg] at h
    linarith only [h, hσ, hT.2]
  have hconvert :
    (768 * (Real.log 2 * (K * n * Real.log n) + 1) + 8 * (K * n * Real.log n)) / n ^ 3 +
        32 * Real.sqrt (completedLFunctionInverseSquareMass χ) *
            (Real.sqrt (K * n * Real.log n) * (K * n * Real.log n + 1)) /
          n ^ 2 =
      unconditionalHorizontalCleanEnvelope (completedLFunctionInverseSquareMass χ) K n := by
    rw [show
        768 * (Real.log 2 * (K * n * Real.log n) + 1) + 8 * (K * n * Real.log n) =
          (768 * Real.log 2 + 8) * (K * n * Real.log n) + 768
        by ring,
      horizontal_log_numerator_div_cube _ _ _ _ hnpos.ne']
    dsimp only [unconditionalHorizontalCleanEnvelope]
    ring
  have hpoint :=
    normalized_horizontal_point_bound (n := n) (R := R) (T := T) (δ := δ) (A :=
      (4 * (q : ℝ) + 3) * (R + 3) * Real.log (R + 3) - Real.log ‖χ.completedLFunction 0‖ + 1) (B :=
      Real.log (max 1 (completedLFunctionBallBound q (2 * R)) / ‖χ.completedLFunction 0‖) /
        Real.log 2)
      (P := K * n * Real.log n) (H := Real.sqrt (completedLFunctionInverseSquareMass χ))
  have hAR' :
    (4 * (q : ℝ) + 3) * (R + 3) * Real.log (R + 3) - Real.log ‖χ.completedLFunction 0‖ + 1 ≤
      Real.log 2 * (K * n * Real.log n) + 1 := by
    linarith only [hARupper]
  refine ⟨?_, ?_, hnplus, hnminus⟩
  · exact
      (hpoint _ _ hnpos hnormplus (by linarith only [hR.1, hnge]) hT.1 hδ hAR hBR
            (Real.sqrt_nonneg _) hAR' hBRupper hinv
            (by simpa only [div_mul_eq_mul_div] using hplus)).trans_eq
        hconvert
  · exact
      (hpoint _ _ hnpos hnormminus (by linarith only [hR.1, hnge]) hT.1 hδ hAR hBR
            (Real.sqrt_nonneg _) hAR' hBRupper hinv
            (by simpa only [div_mul_eq_mul_div] using hminus)).trans_eq
        hconvert

/-- Every primitive nonprincipal character with nonprincipal inverse admits a height
sequence tending to infinity and an error sequence tending to zero, with both
signed centered logarithmic derivatives bounded after division by height squared.
The growing strips are zero-free on these edges. Shift the eventual good-height
witnesses by one fixed natural index and compose the clean-envelope limit.
This is the unconditional height-sequence input to explicit contour formulas. -/
theorem exists_unconditional_horizontal_height_sequence {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    ∃ T ε : ℕ → ℝ,
      Filter.Tendsto T Filter.atTop Filter.atTop ∧
        Filter.Tendsto ε Filter.atTop (nhds 0) ∧
        ∀ k : ℕ,
          (k : ℝ) + 1 ≤ T k ∧
            ∀ σ : ℝ,
              |σ| ≤ 2 * ((k : ℝ) + 1) →
                ‖logDeriv χ.completedLFunction ((σ : ℂ) + T k * Complex.I) -
                          logDeriv χ.completedLFunction 0‖ /
                      (T k) ^ 2 ≤
                    ε k ∧
                  ‖logDeriv χ.completedLFunction ((σ : ℂ) - T k * Complex.I) -
                          logDeriv χ.completedLFunction 0‖ /
                      (T k) ^ 2 ≤
                    ε k ∧
                  χ.completedLFunction ((σ : ℂ) + T k * Complex.I) ≠ 0 ∧
                  χ.completedLFunction ((σ : ℂ) - T k * Complex.I) ≠ 0 := by
  classical
  obtain ⟨K, hK, hgood⟩ := exists_eventually_unconditional_horizontal_clean_bound hq hp hne hinv
  have hnseq : Filter.Tendsto (fun k : ℕ ↦ (k : ℝ) + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop 1 tendsto_natCast_atTop_atTop
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.mp (hnseq.eventually hgood)
  have hindex (k : ℕ) : k₀ ≤ k + k₀ := Nat.le_add_left k₀ k
  let T := fun k : ℕ ↦ Classical.choose (hk₀ (k + k₀) (hindex k))
  let ε := fun k : ℕ ↦
    unconditionalHorizontalCleanEnvelope (completedLFunctionInverseSquareMass χ) K
      (((k + k₀ : ℕ) : ℝ) + 1)
  have hspec (k : ℕ) := Classical.choose_spec (hk₀ (k + k₀) (hindex k))
  have hshift (k : ℕ) : (k : ℝ) + 1 ≤ ((k + k₀ : ℕ) : ℝ) + 1 := by
    push_cast
    linarith only [(Nat.cast_nonneg k₀ : (0 : ℝ) ≤ k₀)]
  have hTlower (k : ℕ) : (k : ℝ) + 1 ≤ T k := (hshift k).trans (hspec k).1.1
  have hT : Filter.Tendsto T Filter.atTop Filter.atTop := Filter.tendsto_atTop_mono hTlower hnseq
  have hnshift : Filter.Tendsto (fun k : ℕ ↦ ((k + k₀ : ℕ) : ℝ) + 1) Filter.atTop Filter.atTop := by
    have h :=
      Filter.tendsto_atTop_add_const_right Filter.atTop ((k₀ : ℝ) + 1) tendsto_natCast_atTop_atTop
    simpa only [Nat.cast_add, add_assoc] using h
  have hε : Filter.Tendsto ε Filter.atTop (nhds 0) :=
    (tendsto_unconditionalHorizontalCleanEnvelope (completedLFunctionInverseSquareMass χ) K hK).comp
      hnshift
  refine ⟨T, ε, hT, hε, ?_⟩
  intro k
  refine ⟨hTlower k, ?_⟩
  intro σ hσ
  exact
    (hspec k).2 σ (hσ.trans (mul_le_mul_of_nonneg_left (hshift k) (by norm_num only : (0 : ℝ) ≤ 2)))

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
