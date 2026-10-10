/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaConductorBounds
public import PseudoPrime.LLS.PrimePowerSubgroupBounds

/-! # Small-index prime bounds from conductor savings

For indices four through six, a conductor-logarithm sum at most half the
ambient cost already reaches the original Theorem 1.3 leading coefficient.
The estimate applies to arbitrary moduli; it does not assert that every
subgroup satisfies this conductor-saving condition.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For indices four through six, the refined gamma certificates share the
conductor coefficient sqrt(6571/10000)/(h-1). The index-five and index-six
certificates are sharper; monotonicity of the positive squared denominator
permits the common certificate. The threshold is uniform in subgroups. -/
theorem gamma_small_index_conductor_bound
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (h : ℕ) (hh4 : 4 ≤ h) (hh6 : h ≤ 6)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : ℕ,
      20000 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ (H : Subgroup (ZMod q)ˣ),
              H.index = h →
                ∃ p : ℕ,
                  IsLeast (primesOutside q H) p ∧
                    (p : ℝ) ≤
                      (Real.sqrt (6571 / 10000) / ((h : ℝ) - 1) * subgroupConductorLogSum H +
                          ε * Real.log q) ^
                        2 := by
  rcases Nat.eq_or_lt_of_le hh4 with he | he
  · subst h
    exact gamma_conductor_bound_of_index_four hg hε
  · rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt he) with he5 | he5
    · subst h
      apply
        gamma_prime_bound_of_conductor_certificate hg 5 (by norm_num only) (l := (171 / 100 : ℝ))
          (c := (6571 / 10000 : ℝ)) (by norm_num only) (by norm_num only) hε
      · have he := refined_gamma_five_exp_bound
        norm_num only
        linarith only [he]
      · have hc := refined_gamma_five_coefficient
        norm_num only at hc ⊢
        nlinarith only [hc, sq_nonneg (4 - 5 * Real.exp (-(171 / 100 : ℝ)))]
    · have he6 : h = 6 := Nat.le_antisymm hh6 (Nat.succ_le_of_lt he5)
      subst h
      apply
        gamma_prime_bound_of_conductor_certificate hg 6 (by norm_num only) (l := (1633 / 1000 : ℝ))
          (c := (6571 / 10000 : ℝ)) (by norm_num only) (by norm_num only) hε
      · have he := refined_gamma_six_exp_bound
        norm_num only
        linarith only [he]
      · have hc := refined_gamma_six_coefficient
        norm_num only at hc ⊢
        nlinarith only [hc, sq_nonneg (5 - 6 * Real.exp (-(1633 / 1000 : ℝ)))]

/-- For indices four through six, a conductor-logarithm sum at most half
the ambient cost suffices for the original leading coefficient of Theorem
1.3. Use the common gamma certificate with allowance 1/10000, bound its
square-root coefficient by 811/1000, and compare with the already certified
659/4000 margin. This proves an additional branch for arbitrary moduli. -/
theorem theorem13_small_index_of_conductor_sum_le_half
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (h : ℕ) (hh4 : 4 ≤ h)
    (hh6 : h ≤ 6) :
    ∃ Q : ℕ,
      20000 ≤ Q ∧
        ∀ (q : ℕ) [NeZero q],
          Q ≤ q →
            ∀ (H : Subgroup (ZMod q)ˣ),
              H.index = h →
                subgroupConductorLogSum H ≤ (((h : ℝ) - 1) / 2) * Real.log q →
                ∃ p : ℕ,
                  IsLeast (primesOutside q H) p ∧
                    (p : ℝ) <
                      (1 / 4) * (1 - 1 / (h : ℝ)) ^ 2 *
                        (Real.log (2 * (h : ℝ)) / (Real.log (2 * (h : ℝ)) - 4)) ^ 2 *
                        (Real.log q) ^ 2 := by
  obtain ⟨Q, hQ, hb⟩ :=
    gamma_small_index_conductor_bound hg h hh4 hh6 (by norm_num only : (0 : ℝ) < 1 / 10000)
  refine ⟨Q, hQ, ?_⟩
  intro q _ hq H hi hsum
  obtain ⟨p, hp, hbound⟩ := hb q hq H hi
  have hhR : (1 : ℝ) < h := by exact_mod_cast (lt_of_lt_of_le (by norm_num only : 1 < 4) hh4)
  have hlog : 0 < Real.log q :=
    Real.log_pos (by exact_mod_cast ((by norm_num only : 2 ≤ 20000).trans (hQ.trans hq)))
  have hcoef : 0 ≤ Real.sqrt (6571 / 10000 : ℝ) / ((h : ℝ) - 1) :=
    div_nonneg (Real.sqrt_nonneg _) (sub_pos.mpr hhR).le
  have hmul := mul_le_mul_of_nonneg_left hsum hcoef
  have hid :
    (Real.sqrt (6571 / 10000 : ℝ) / ((h : ℝ) - 1)) * (((h : ℝ) - 1) / 2) =
      Real.sqrt (6571 / 10000 : ℝ) / 2 := by
    rw [← mul_div_assoc, div_mul_cancel₀ _ (sub_pos.mpr hhR).ne']
  rw [← mul_assoc, hid] at hmul
  have hs : Real.sqrt (6571 / 10000 : ℝ) ≤ 811 / 1000 := by
    have hs0 := Real.sqrt_nonneg (6571 / 10000 : ℝ)
    have hsq := Real.sq_sqrt (by norm_num only : (0 : ℝ) ≤ 6571 / 10000)
    nlinarith only [hs0, hsq]
  have hrad :
    Real.sqrt (6571 / 10000 : ℝ) / ((h : ℝ) - 1) * subgroupConductorLogSum H +
        (1 / 10000) * Real.log q ≤
      (2028 / 5000) * Real.log q := by
    have hu := mul_le_mul_of_nonneg_right hs hlog.le
    nlinarith only [hmul, hu]
  have hbase :
    0 ≤
      Real.sqrt (6571 / 10000 : ℝ) / ((h : ℝ) - 1) * subgroupConductorLogSum H +
        (1 / 10000) * Real.log q :=
    add_nonneg (mul_nonneg hcoef (subgroupConductorLogSum_nonneg H))
      (mul_nonneg (by norm_num only) hlog.le)
  have hsquare := mul_self_le_mul_self hbase hrad
  have hprime : (p : ℝ) ≤ (659 / 4000) * (Real.log q) ^ 2 := by
    nlinarith only [hbound, hsquare, sq_nonneg (Real.log q)]
  have hpaper :=
    mul_lt_mul_of_pos_right (proper_prime_power_coefficient_lt_small_index hh4 hh6)
      (sq_pos_of_pos hlog)
  exact ⟨p, hp, hprime.trans_lt hpaper⟩

end PseudoPrime.LLS.PaperStatements
