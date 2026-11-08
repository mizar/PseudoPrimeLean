/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028LogSixIntegral

/-! # Logarithmic moments for the reflected Euler series -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The nonnegative logarithmic moment with exponent `79/50`. Its natural
values form the scalar series in the reflected Euler term. -/
noncomputable def target028LogMoment (k : ℕ) (x : ℝ) : ℝ :=
  Real.log x ^ k * x ^ (-(79 / 50 : ℝ))

/-- Logarithmic substitution transforms the moment into a Gamma density of
rate `29/50`. The powers combine at every positive argument. -/
theorem target028_log_moment_change (k : ℕ) {x : ℝ} (hx : 0 < x) :
    x⁻¹ * (Real.log x ^ k * Real.exp (-((29 / 50 : ℝ) * Real.log x))) = target028LogMoment k x := by
  rw [show -((29 / 50 : ℝ) * Real.log x) = Real.log x * (-(29 / 50 : ℝ)) by ring, ←
    Real.rpow_def_of_pos hx, ← Real.rpow_neg_one]
  dsimp only [target028LogMoment]
  have he : (-1 : ℝ) + (-(29 / 50 : ℝ)) = -(79 / 50 : ℝ) := by norm_num only
  calc
    _ = Real.log x ^ k * (x ^ (-1 : ℝ) * x ^ (-(29 / 50 : ℝ))) := by ring
    _ = _ := by rw [← Real.rpow_add hx, he]

/-- Every natural logarithmic moment is integrable above one. Apply the
integrability of the Gamma density after the logarithmic substitution. -/
theorem target028_log_moment_integrable (k : ℕ) :
    MeasureTheory.IntegrableOn (target028LogMoment k) (Set.Ioi 1) := by
  have hi :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (s := (k : ℝ)) (p := 1) (b := (29 / 50 : ℝ))
      (by
        have h : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith only [h])
      (by norm_num only) (by norm_num only)
  have hi' :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ t ^ k * Real.exp (-((29 / 50 : ℝ) * t)))
      (Set.Ioi 0) := by
    change
      MeasureTheory.IntegrableOn
        (fun t : ℝ ↦ t ^ ((k : ℕ) : ℝ) * Real.exp (-(29 / 50 : ℝ) * t ^ (1 : ℝ))) _ at hi
    simpa only [Real.rpow_natCast, Real.rpow_one, neg_mul] using hi
  have h :=
    (MeasureTheory.integrableOn_comp_log_Ioi (fun t : ℝ ↦ t ^ k * Real.exp (-((29 / 50 : ℝ) * t)))
          (a := 1) zero_lt_one).2
      (by simpa only [Real.log_one] using hi')
  apply h.congr_fun _ measurableSet_Ioi
  intro x hx
  simpa only [smul_eq_mul] using target028_log_moment_change k (lt_trans zero_lt_one hx)

/-- The integral of the `k`th logarithmic moment equals the corresponding
Gamma value `k!/(29/50)^(k+1)`. -/
theorem target028_log_moment_integral (k : ℕ) :
    (∫ x : ℝ in Set.Ioi 1, target028LogMoment k x) =
      (k.factorial : ℝ) / (29 / 50 : ℝ) ^ (k + 1) := by
  have h :=
    MeasureTheory.integral_comp_log_Ioi (fun t : ℝ ↦ t ^ k * Real.exp (-((29 / 50 : ℝ) * t))) (a :=
      1) zero_lt_one
  simp only [Real.log_one] at h
  have he :
    (∫ x : ℝ in Set.Ioi 1, x⁻¹ * (Real.log x ^ k * Real.exp (-((29 / 50 : ℝ) * Real.log x)))) =
      ∫ x : ℝ in Set.Ioi 1, target028LogMoment k x := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact target028_log_moment_change k (lt_trans zero_lt_one hx)
  rw [show
      (∫ x : ℝ in Set.Ioi 1, x⁻¹ • (Real.log x ^ k * Real.exp (-((29 / 50 : ℝ) * Real.log x)))) =
        ∫ x : ℝ in Set.Ioi 1, target028LogMoment k x
      by simpa only [smul_eq_mul] using he] at h
  have hg :=
    Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (r := (29 / 50 : ℝ))
      (by
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith only [hk])
      (by norm_num only)
  have hg' :
    (∫ t : ℝ in Set.Ioi 0, t ^ k * Real.exp (-((29 / 50 : ℝ) * t))) =
      (k.factorial : ℝ) / (29 / 50 : ℝ) ^ (k + 1) := by
    rw [show (k : ℝ) + 1 - 1 = (k : ℝ) by ring] at hg
    simp only [Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at hg
    rw [show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by
        push_cast; ring,
      Real.rpow_natCast, one_div, inv_pow] at hg
    simpa only [div_eq_mul_inv, mul_comm] using hg
  exact h.trans hg'

/-- The derivative of the `(k+1)`st moment has the sign of
`k+1-(79/50) log x`. This identifies its increasing and decreasing ranges. -/
theorem target028_log_moment_derivative (k : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (target028LogMoment (k + 1))
      (Real.log x ^ k * x ^ (-(129 / 50 : ℝ)) * ((k + 1 : ℕ) - (79 / 50 : ℝ) * Real.log x)) x := by
  have hd :=
    ((Real.hasDerivAt_log hx.ne').pow (k + 1)).mul
      (Real.hasDerivAt_rpow_const (Or.inl hx.ne') (p := -(79 / 50 : ℝ)))
  have he :
    (k + 1 : ℕ) * Real.log x ^ (k + 1 - 1) * x⁻¹ * x ^ (-(79 / 50 : ℝ)) +
        Real.log x ^ (k + 1) * (-(79 / 50 : ℝ) * x ^ (-(79 / 50 : ℝ) - 1)) =
      Real.log x ^ k * x ^ (-(129 / 50 : ℝ)) * ((k + 1 : ℕ) - (79 / 50 : ℝ) * Real.log x) := by
    have hp : x ^ (-(129 / 50 : ℝ)) = x ^ (-(79 / 50 : ℝ)) * x⁻¹ := by
      rw [← show -(79 / 50 : ℝ) - 1 = -(129 / 50 : ℝ) by norm_num only, Real.rpow_sub_one hx.ne']
      rw [div_eq_mul_inv]
    rw [show -(79 / 50 : ℝ) - 1 = -(129 / 50 : ℝ) by norm_num only, hp]
    simp only [Nat.add_sub_cancel, pow_succ]
    ring
  exact he ▸ hd

/-- The logarithmic moment increases up to any point at or before its
turning point. The derivative criterion reduces this to the endpoint bound. -/
theorem target028_log_moment_increasing (k : ℕ) {a : ℝ}
    (hturn : (79 / 50 : ℝ) * Real.log a ≤ (k + 1 : ℕ)) :
    MonotoneOn (target028LogMoment (k + 1)) (Set.Icc 1 a) := by
  apply
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 1 a)
      (fun x hx ↦
        (target028_log_moment_derivative k
            (by linarith only [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx ↦
        (target028_log_moment_derivative k
            (by
              have h := interior_subset hx; linarith only [h.1])).hasDerivWithinAt)
  intro x hx
  have hm : x ∈ Set.Icc (1 : ℝ) a := interior_subset hx
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hm.1
  have hl := Real.log_le_log (by linarith only [hm.1]) hm.2
  have hs : 0 ≤ (k + 1 : ℕ) - (79 / 50 : ℝ) * Real.log x := by linarith only [hl, hturn]
  exact mul_nonneg (mul_nonneg (pow_nonneg hl0 _) (Real.rpow_nonneg (by linarith only [hm.1]) _)) hs

/-- The logarithmic moment decreases from any point at or after its turning
point. The explicit derivative has nonpositive final factor on that half-line. -/
theorem target028_log_moment_decreasing (k : ℕ) {a : ℝ} (ha : 1 ≤ a)
    (hturn : (k + 1 : ℕ) ≤ (79 / 50 : ℝ) * Real.log a) :
    AntitoneOn (target028LogMoment (k + 1)) (Set.Ici a) := by
  apply
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici a)
      (fun x hx ↦
        (target028_log_moment_derivative k
            (by
              have h : a ≤ x := hx; linarith only [ha, h])).continuousAt.continuousWithinAt)
      (fun x hx ↦
        (target028_log_moment_derivative k
            (by
              have h : a ≤ x := interior_subset hx; linarith only [ha, h])).hasDerivWithinAt)
  intro x hx
  have hm : a ≤ x := interior_subset hx
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith only [ha, hm])
  have hl := Real.log_le_log (by linarith only [ha]) hm
  have hs : (k + 1 : ℕ) - (79 / 50 : ℝ) * Real.log x ≤ 0 := by linarith only [hl, hturn]
  exact
    mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (pow_nonneg hl0 _) (Real.rpow_nonneg (by linarith only [ha, hm]) _)) hs

/-- Split a logarithmic-moment series around two adjacent integers enclosing
its turning point. The increasing and decreasing pieces are bounded by their
integrals; the two boundary values use the supplied common upper bound. -/
theorem target028_log_moment_sum_bound (k N : ℕ) (hN : 1 ≤ N)
    (hleft : (79 / 50 : ℝ) * Real.log N ≤ (k + 1 : ℕ))
    (hright : (k + 1 : ℕ) ≤ (79 / 50 : ℝ) * Real.log (N + 1 : ℕ)) {C : ℝ}
    (hNval : target028LogMoment (k + 1) N ≤ C)
    (hN1val : target028LogMoment (k + 1) (N + 1 : ℕ) ≤ C) :
    (∑' n : ℕ, target028LogMoment (k + 1) n) ≤
      ((k + 1).factorial : ℝ) / (29 / 50 : ℝ) ^ (k + 2) + 2 * C := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn (x : ℝ) (hx : 1 ≤ x) : 0 ≤ target028LogMoment (k + 1) x := by
    exact
      mul_nonneg (pow_nonneg (Real.log_nonneg hx) _) (Real.rpow_nonneg (by linarith only [hx]) _)
  have hpre :
    (∑ n ∈ Finset.Ico (1 : ℕ) N, target028LogMoment (k + 1) (n : ℝ)) ≤
      ∫ x : ℝ in (1 : ℝ)..N, target028LogMoment (k + 1) x := by
    have hmono := target028_log_moment_increasing k hleft
    have hmono' : MonotoneOn (target028LogMoment (k + 1)) (Set.Icc ((1 : ℕ) : ℝ) (N : ℝ)) := by
      simpa only [Nat.cast_one] using hmono
    simpa only [Nat.cast_one] using MonotoneOn.sum_le_integral_Ico hN hmono'
  have hi := target028_log_moment_integrable (k + 1)
  have hiN := hi.mono_set (Set.Ioi_subset_Ioi (by linarith only [hNR] : (1 : ℝ) ≤ N + 1))
  have hdec :=
    target028_log_moment_decreasing k
      (by
        simp only [Nat.cast_add, Nat.cast_one]; linarith only [hNR])
      hright
  have htail :=
    hdec.tsum_comp_add_le_integral (N + 1) (by simpa only [Nat.cast_add, Nat.cast_one] using hiN)
      (fun x hx ↦
        hn x
          (by
            have h : ((N + 1 : ℕ) : ℝ) < x := Set.mem_Ioi.mp hx
            simp only [Nat.cast_add, Nat.cast_one] at h
            linarith only [hNR, h]))
  have hsum := (refined_log_power_summable (k + 1)).sum_add_tsum_nat_add (N + 2)
  have hpart :
    (∑ n ∈ Finset.range (N + 2), target028LogMoment (k + 1) (n : ℝ)) =
      (∑ n ∈ Finset.Ico (1 : ℕ) N, target028LogMoment (k + 1) (n : ℝ)) +
        target028LogMoment (k + 1) N +
        target028LogMoment (k + 1) (N + 1 : ℕ) := by
    rw [show N + 2 = (N + 1) + 1 by simp only [Nat.add_assoc, Nat.reduceAdd], Finset.sum_range_succ,
      Finset.sum_range_succ]
    congr 2
    rw [Finset.sum_Ico_eq_sub _ hN]
    simp only [Finset.sum_range_one, Nat.cast_zero, target028LogMoment, Real.log_zero,
      zero_pow (Nat.succ_ne_zero k), zero_mul, sub_zero]
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hi hNR
  have hiN0 := hi.mono_set (Set.Ioi_subset_Ioi hNR)
  have hsplit2 :=
    intervalIntegral.integral_Ioi_sub_Ioi hiN0 (show (N : ℝ) ≤ (N : ℝ) + 1 by linarith only)
  have hmid : 0 ≤ ∫ x : ℝ in (N : ℝ)..(N : ℝ) + 1, target028LogMoment (k + 1) x := by
    apply intervalIntegral.integral_nonneg (by linarith only)
    intro x hx
    exact hn x (by linarith only [hNR, hx.1])
  change
    (∑ n ∈ Finset.range (N + 2), target028LogMoment (k + 1) (n : ℝ)) +
        (∑' n : ℕ, target028LogMoment (k + 1) ((n + (N + 2) : ℕ) : ℝ)) =
      ∑' n : ℕ, target028LogMoment (k + 1) (n : ℝ) at hsum
  rw [← hsum, hpart]
  have htail' :
    (∑' n : ℕ, target028LogMoment (k + 1) ((n + (N + 2) : ℕ) : ℝ)) ≤
      ∫ x : ℝ in Set.Ioi ((N : ℝ) + 1), target028LogMoment (k + 1) x := by
    simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.cast_add, Nat.cast_one] using htail
  rw [target028_log_moment_integral] at hsplit
  simpa only [Nat.add_assoc, Nat.reduceAdd] using
    (show
      (∑ n ∈ Finset.Ico (1 : ℕ) N, target028LogMoment (k + 1) (n : ℝ)) +
          target028LogMoment (k + 1) N +
          target028LogMoment (k + 1) (N + 1 : ℕ) +
          (∑' n : ℕ, target028LogMoment (k + 1) ((n + (N + 2) : ℕ) : ℝ)) ≤
        ((k + 1).factorial : ℝ) / (29 / 50 : ℝ) ^ ((k + 1) + 1) + 2 * C
      by linarith only [hpre, htail', hNval, hN1val, hsplit, hsplit2, hmid])

/-- A logarithm upper bound and a negative-power upper bound control one
natural-index moment. Both factors are nonnegative, so their product can be
compared separately. -/
theorem target028_log_moment_point (k n : ℕ) {L P : ℝ} (hL : Real.log n ≤ L)
    (hP : (n : ℝ) ^ (-(79 / 50 : ℝ)) ≤ P) : target028LogMoment k n ≤ L ^ k * P := by
  have hl0 := Real.log_natCast_nonneg n
  have hp0 : 0 ≤ (n : ℝ) ^ (-(79 / 50 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  dsimp only [target028LogMoment]
  exact mul_le_mul (pow_le_pow_left₀ hl0 hL k) hP hp0 (pow_nonneg (hl0.trans hL) k)

end PseudoPrime.PrimeTestBounds.MillerRabin
