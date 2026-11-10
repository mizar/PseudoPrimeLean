/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterInterior68

/-! # Nonuniform witnesses at interior scales -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The difference between the explicit interior lower bound and its upper
cost at common scale `2r`. Positivity contradicts the no-witness inequality. -/
private noncomputable def interiorMargin (r : ℝ) : ℝ :=
  (36 - 4 * Real.log r - (137 / 330 : ℝ)) * r -
    (1486 / 15 - (38 / 5 : ℝ) * Real.log r) * Real.sqrt r -
    ((98717 / 12000 : ℝ) * (48 - 2 * Real.log r - Real.log 16) - 59 / 5) -
    (137 / 330 : ℝ) / r -
    (4 / 15 : ℝ) / Real.sqrt r -
    15 / 11

/-- Differentiate the interior margin at a positive radius using the
logarithm, square-root and reciprocal derivatives. -/
private theorem margin_deriv {r : ℝ} (hr : 0 < r) :
    HasDerivAt interiorMargin
      (32 - 4 * Real.log r - (137 / 330 : ℝ) -
          (1258 / 15 - (38 / 5 : ℝ) * Real.log r) / (2 * Real.sqrt r) +
        (98717 / 6000 : ℝ) / r +
        (137 / 330 : ℝ) / r ^ 2 +
        (2 / 15 : ℝ) / (r * Real.sqrt r))
      r := by
  have hR : r ≠ 0 := hr.ne'
  have hS : Real.sqrt r ≠ 0 := (Real.sqrt_pos.2 hr).ne'
  have hs2 := Real.sq_sqrt hr.le
  have hlog := Real.hasDerivAt_log hR
  have hs := Real.hasDerivAt_sqrt hR
  have hid := hasDerivAt_id r
  have h1 := ((hlog.const_mul 4).const_sub (36 - (137 / 330 : ℝ))).mul hid
  have h2 := ((hlog.const_mul (38 / 5 : ℝ)).const_sub (1486 / 15 : ℝ)).mul hs
  have h3 :=
    (((hlog.const_mul 2).const_sub (48 - Real.log 16)).const_mul (98717 / 12000 : ℝ)).sub_const
      (59 / 5 : ℝ)
  have h4 := (hasDerivAt_const r (137 / 330 : ℝ)).div hid hR
  have h5 := (hasDerivAt_const r (4 / 15 : ℝ)).div hs hS
  have hd := (((h1.sub h2).sub h3).sub h4).sub h5 |>.sub_const (15 / 11 : ℝ)
  convert hd using 1
  · funext t
    dsimp only [interiorMargin, id, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]
    ring
  · simp only [id_eq, zero_mul, mul_one]
    rw [← hs2, Real.sqrt_sq (Real.sqrt_nonneg r)]
    field_simp
    ring

/-- The interior margin has positive derivative from radius 34 to 100.
The logarithm and square-root bounds dominate the negative derivative term. -/
private theorem deriv_pos {r : ℝ} (hr : 34 ≤ r) (hupper : r ≤ 100) :
    0 < deriv interiorMargin r := by
  have hr0 : 0 < r := by linarith only [hr]
  have hs0 : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  have hs : (5 : ℝ) ≤ Real.sqrt r :=
    (Real.le_sqrt (by norm_num only) (by linarith only [hr])).2 (by linarith only [hr])
  have hl : 0 ≤ Real.log r := Real.log_nonneg (by linarith only [hr])
  have hlog : Real.log r ≤ (463 / 100 : ℝ) :=
    (Real.log_le_log hr0 hupper).trans Analysis.log_hundred_le_fourHundredSixtyThree_hundredths
  have hf : (1258 / 15 - (38 / 5 : ℝ) * Real.log r) / (2 * Real.sqrt r) ≤ 9 := by
    apply (div_le_iff₀ (by linarith only [hs0] : 0 < 2 * Real.sqrt r)).2
    linarith only [hl, hs]
  have hp1 : 0 ≤ (98717 / 6000 : ℝ) / r := div_nonneg (by norm_num only) hr0.le
  have hp2 : 0 ≤ (137 / 330 : ℝ) / r ^ 2 := div_nonneg (by norm_num only) (sq_nonneg r)
  have hp3 : 0 ≤ (2 / 15 : ℝ) / (r * Real.sqrt r) :=
    div_nonneg (by norm_num only) (mul_nonneg hr0.le hs0.le)
  rw [(margin_deriv hr0).deriv]
  linarith only [hlog, hf, hp1, hp2, hp3]

/-- The certified common-scale-68 gap makes the interior margin positive at
radius 34. Rewrite the logarithm of the square and collect terms. -/
private theorem margin34 : 0 < interiorMargin 34 := by
  have h := quarter_interior_gap68
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  unfold interiorMargin
  norm_num only
  simp only [div_eq_mul_inv] at h ⊢
  linarith only [h]

/-- The interior margin is nondecreasing between radii 34 and 100. Apply the
positive derivative and continuity on the closed interval. -/
private theorem margin_mono {r : ℝ} (hr : 34 ≤ r) (hupper : r ≤ 100) :
    interiorMargin 34 ≤ interiorMargin r := by
  have hc : ContinuousOn interiorMargin (Set.Icc 34 100) := by
    intro x hx
    have hx0 : 0 < x := by linarith only [hx.1]
    exact (margin_deriv hx0).continuousAt.continuousWithinAt
  have hd : ∀ x ∈ interior (Set.Icc (34 : ℝ) 100), 0 < deriv interiorMargin x := by
    intro x hx
    have hx' : x ∈ Set.Icc (34 : ℝ) 100 := interior_subset hx
    exact deriv_pos hx'.1 hx'.2
  have hm := strictMonoOn_of_deriv_pos (convex_Icc (34 : ℝ) 100) hc hd
  have h34 : (34 : ℝ) ∈ Set.Icc 34 100 := ⟨le_rfl, by norm_num only⟩
  have hr' : r ∈ Set.Icc (34 : ℝ) 100 := ⟨hr, hupper⟩
  exact hm.monotoneOn h34 hr' hr

/-- Under GRH, a positive odd input with Fermat index at least 33000 and
logarithm at most `2r` has a rejecting prime below `r²` for radii from
34 through 100. The monotone interior margin contradicts the no-witness
scalar inequality. -/
theorem quarter_interior_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) {r : ℝ} (hr : 34 ≤ r)
    (hupper : r ≤ 100) (hscale : Real.log n ≤ 2 * r)
    (hindex : 33000 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  have hr0 : 0 < r := by linarith only [hr]
  have hlogr : Real.log r ≤ (463 / 100 : ℝ) :=
    (Real.log_le_log hr0 hupper).trans Analysis.log_hundred_le_fourHundredSixtyThree_hundredths
  have hlog : Real.log (r ^ 2) ≤ 16 := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [hlogr]
  have hpos : 0 < interiorMargin r := lt_of_lt_of_le margin34 (margin_mono hr hupper)
  by_contra hnone
  have h :=
    quarter_interior_reduced hn ho (r := r) (T := 2 * r) (by linarith only [hr]) hlog
      (by linarith only [hr]) hscale hindex hGRH hnone
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  unfold interiorMargin at hpos
  simp only [div_eq_mul_inv] at h hpos
  nlinarith only [h, hpos]

/-- Under GRH, every nonuniform odd composite with logarithm at most
`T ∈ [68, 200]` has a rejecting prime at most `T² / 4`. Split at Fermat
index 33000 and use the small-index and interior large-index witnesses. -/
theorem quarter_common_nonuniform_mid {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hu : ¬UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {T : ℝ} (hT : 68 ≤ T) (hupper : T ≤ 200) (hscale : Real.log n ≤ T) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * T ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  by_cases hi : (PrimeTest.fermatSubgroup n).index ≤ 33000
  · exact quarter_common_index_le hn ho hc (PrimeTest.fermatSubgroup n) le_rfl hi hu hGRH hT hscale
  · obtain ⟨p, hp, hb, hf⟩ :=
      quarter_interior_witness hn ho (r := T / 2) (by linarith only [hT])
        (by linarith only [hupper]) (by linarith only [hscale]) (Nat.le_of_lt (Nat.lt_of_not_ge hi))
        hGRH
    refine ⟨p, hp, ?_, hf⟩
    nlinarith only [hb]

end PseudoPrime.PrimeTestBounds.MillerRabin
