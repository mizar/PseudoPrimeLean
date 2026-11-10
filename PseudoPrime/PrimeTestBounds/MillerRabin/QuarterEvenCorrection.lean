/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.EndpointCorrectionIntervals
public import PseudoPrime.Analysis.LogLinearAnchor
public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEvenWitness
public import PseudoPrime.PrimeTestBounds.MillerRabin.FiniteIndexStructure
public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple

/-! # The even correction at large common scales -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The polynomial difference between the even endpoint correction numerator
and `z` times its denominator is positive for `y ≥ 150` and `z ≥ 5`.
Factoring the four positive contributions proves the arithmetic estimate used
by the large-scale local subgroup branch. -/
theorem quarter_correction_num_pos {y z : ℝ} (hy : 150 ≤ y) (hz : 5 ≤ z) :
    0 <
      LLS.PaperStatements.endpointCorrectionNum y z -
        z * LLS.PaperStatements.endpointCorrectionDen y z := by
  have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
  have hc1 : 0 < 18310000 * z - 56749471 := by linarith only [hz]
  have hc2 : 0 < 2 * y ^ 2 - y - 1 := by nlinarith only [hy, hy2]
  have hc3 : 0 < 54790099 * y ^ 2 + 16781860 * y - 158894180 := by nlinarith only [hy, hy2]
  have hc4 : 0 < 10777809 * y ^ 2 + 2824690 * y - 94877470 := by nlinarith only [hy, hy2]
  have ha : 0 < y ^ 3 * (18310000 * z - 56749471) := mul_pos (pow_pos (by linarith only [hy]) 3) hc1
  have hb : 0 ≤ 36620000 * (2 * y ^ 2 - y - 1) * z ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num only) (le_of_lt hc2)) (sq_nonneg z)
  have hc : 0 ≤ (54790099 * y ^ 2 + 16781860 * y - 158894180) * z :=
    mul_nonneg (le_of_lt hc3) (by linarith only [hz])
  have hid :
    LLS.PaperStatements.endpointCorrectionNum y z -
        z * LLS.PaperStatements.endpointCorrectionDen y z =
      y ^ 3 * (18310000 * z - 56749471) + 36620000 * (2 * y ^ 2 - y - 1) * z ^ 2 +
          (54790099 * y ^ 2 + 16781860 * y - 158894180) * z +
          10777809 * y ^ 2 +
          2824690 * y -
        94877470 := by
    unfold LLS.PaperStatements.endpointCorrectionNum LLS.PaperStatements.endpointCorrectionDen
    ring
  linarith only [ha, hb, hc, hc4, hid]

/-- The even endpoint correction strictly exceeds `log y` for `y ≥ 150`.
A rational logarithm certificate and the positive polynomial difference make
the variable-radius local witness available on the nonuniform half-line. -/
theorem log_lt_even_correction {y : ℝ} (hy : 150 ≤ y) :
    Real.log y < LLS.PaperStatements.fullEndpointEvenGapCorrection y := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 150 8 32 5 (51 / 10) = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hcert
  have hz : (5 : ℝ) ≤ Real.log y := hcert.trans (Real.log_le_log (by norm_num only) hy)
  have hy0 : 0 ≤ y := by linarith only [hy]
  have hz0 : 0 ≤ Real.log y := by linarith only [hz]
  have hq : 0 < (y + 1) ^ 2 + 2 * y * Real.log y := by
    nlinarith only [hy, sq_nonneg y, mul_nonneg hy0 hz0]
  have hd : 0 < LLS.PaperStatements.endpointCorrectionDen y (Real.log y) := by
    unfold LLS.PaperStatements.endpointCorrectionDen
    exact mul_pos (mul_pos (by norm_num only) (by linarith only [hy])) hq
  rw [LLS.PaperStatements.endpointCorrection_eq]
  apply (lt_div_iff₀ hd).2
  linarith only [quarter_correction_num_pos hy hz]

/-- Under GRH, a proper local subgroup carrying every passing residue gives
a rejecting prime below `r²` when `r ≥ 150` and its modulus has logarithm at
most `r + log r`. The logarithmic correction makes the endpoint gap positive;
the local witness then rejects the original input. -/
theorem quarter_local_variable {n q : ℕ} [NeZero q] (hn : 1 < n) (ho : Odd n) (hqn : q ∣ n)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ} (hr : 150 ≤ r)
    (hq : Real.log q ≤ r + Real.log r) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hgap :=
    even_gap_pos_of_shift (show (8 : ℝ) ≤ r by linarith only [hr]) (log_lt_even_correction hr) hq
  have hm : max r (r + Real.log r - Real.log r) = r := by
    apply max_eq_left
    linarith only []
  rw [hm] at hgap
  exact exists_prime_reject_of_local_even_gap hn ho hqn H hH hpass hGRH (by linarith only [hr]) hgap

/-- If `q² ≤ J n`, `J ≤ r²`, and `log n ≤ 2r`, the local modulus satisfies
`log q ≤ r + log r`. Logarithmic monotonicity transfers the index bound to
the variable-radius local witness. -/
theorem quarter_variable_local_log {n q J : ℕ} (hn : 0 < n) (hq : 0 < q) (hJ : 1 ≤ J)
    (hsize : q ^ 2 ≤ J * n) {r : ℝ} (hJr : (J : ℝ) ≤ r ^ 2) (hscale : Real.log n ≤ 2 * r) :
    Real.log q ≤ r + Real.log r := by
  have hR : (q : ℝ) ^ 2 ≤ (J : ℝ) * n := by exact_mod_cast hsize
  have hl := Real.log_le_log (pow_pos (Nat.cast_pos.mpr hq) 2) hR
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (Nat.zero_lt_of_lt hJ)
  rw [Real.log_pow, Real.log_mul hJpos.ne' (Nat.cast_pos.mpr hn).ne'] at hl
  have hj := Real.log_le_log hJpos hJr
  rw [Real.log_pow] at hj
  norm_num only [Nat.cast_ofNat] at hl hj
  linarith only [hl, hj, hscale]

/-- Under GRH, a nonuniform odd composite above `J³` has a rejecting prime
at most `r²` when its Fermat subgroup has index at most `J ≤ r²`, `r ≥ 150`,
and its logarithm is at most `2r`. The finite-index classification and the
variable-radius even correction handle the small-index branch. -/
theorem quarter_variable_small_index {n J : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (H : Subgroup (ZMod n)ˣ) (hH : H ≤ PrimeTest.fermatSubgroup n) (hJ : 1 ≤ J) (hi : H.index ≤ J)
    (hlarge : J ^ 3 ≤ n) (hu : ¬UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ} (hr : 150 ≤ r)
    (hJr : (J : ℝ) ≤ r ^ 2) (hscale : Real.log n ≤ 2 * r) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  rcases localSubgroup_or_uniformKorseltTriple hn ho hc H hH hJ hlarge hi with hlocal | ht
  · obtain ⟨q, hq, hqn, hsize, K, hproper, hpass⟩ := hlocal
    have hqpos : 0 < q := lt_of_lt_of_le (by decide : 0 < 2) hq
    let : NeZero q := ⟨Nat.ne_zero_of_lt hqpos⟩
    exact
      quarter_local_variable hn ho hqn K hproper hpass hGRH hr
        (quarter_variable_local_log (Nat.zero_lt_of_lt hn) hqpos hJ hsize hJr hscale)
  · exact False.elim (hu ht)

/-- If `n ≤ J³`, `J ≤ r²` and `r ≥ 150`, the global 0.28 maximum cutoff is
at most `r²`. A logarithm tangent bound at 150 absorbs the small-input branch
of the variable-index proof into the quarter-square common scale. -/
theorem quarter_variable_small_cutoff {n J : ℕ} (hn : 1 < n) (hsmall : n ≤ J ^ 3) {r : ℝ}
    (hr : 150 ≤ r) (hJr : (J : ℝ) ≤ r ^ 2) : max 2 ((7 / 25 : ℝ) * Real.log n ^ 2) ≤ r ^ 2 := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 150 8 32 5 (51 / 10) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hlogr : Real.log r ≤ (17 / 500 : ℝ) * r := by
    apply Analysis.log_le_mul_of_anchor (a := 150) (by norm_num only) hr
    · nlinarith only [hcert]
    · norm_num only
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hnR : (n : ℝ) ≤ (r ^ 2) ^ 3 := by
    calc
      (n : ℝ) ≤ (J : ℝ) ^ 3 := by exact_mod_cast hsmall
      _ ≤ (r ^ 2) ^ 3 := pow_le_pow_left₀ hJ0 hJr 3
  have hl := Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn)) hnR
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hn0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (Nat.le_of_lt hn))
  have hb : Real.log n ≤ (51 / 250 : ℝ) * r := by linarith only [hl, hlogr]
  have hs := mul_self_le_mul_self hn0 hb
  have hr2 : (150 : ℝ) ^ 2 ≤ r ^ 2 := by nlinarith only [hr]
  apply max_le
  · nlinarith only [hr2]
  · nlinarith only [hs, sq_nonneg r]

end PseudoPrime.PrimeTestBounds.MillerRabin
