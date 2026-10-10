/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.CosetRadiusComparison

/-!
# The explicit coarse coset bound and Theorem 1.4

Absorb the character-average errors under the absence of primes below the cutoff.
The resulting coarse radius and its numerical comparison prove the original
least-prime bound for every proper subgroup index.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- A nonnegative subgroup scale and cutoff logarithm satisfying the decay certificate
bound the scaled norm error. Use the square-root bound for the level logarithm and
absorb the linear and quadratic cutoff terms. This controls the nonprincipal errors. -/
private theorem scaled_coset_error {d s t L A M : ℝ} (hd : 0 ≤ d) (ht : 0 ≤ t) (hscale : d * L ≤ s)
    (hdec : (7 / 2 : ℝ) * t + t ^ 2 / 3 ≤ s / 100) (hA : A ≤ L) (hM : M ≤ L + 1 + t) :
    d * (t ^ 2 + ((2 / 3 : ℝ) * A + 4) * t + t / 2 * M) ≤
      (7 / 6 : ℝ) * s * t + (3 / 50 : ℝ) * d * s := by
  have hs0 : 0 ≤ s := by nlinarith only [hdec, ht, sq_nonneg t]
  have hds := mul_nonneg hd hs0
  have ht1 : t ≤ s / 350 := by nlinarith only [hdec, sq_nonneg t]
  have ht2 : t ^ 2 ≤ (3 / 100 : ℝ) * s := by nlinarith only [hdec, ht]
  have hl := mul_le_mul_of_nonneg_right hscale ht
  have hAt := mul_le_mul_of_nonneg_left hA (mul_nonneg hd ht)
  have hMt :=
    mul_le_mul_of_nonneg_left hM (div_nonneg (mul_nonneg hd ht) (by norm_num only : (0 : ℝ) ≤ 2))
  have ht1d := mul_le_mul_of_nonneg_left ht1 hd
  have ht2d := mul_le_mul_of_nonneg_left ht2 hd
  simp only [div_eq_mul_inv] at hl hAt hMt ht1d ht2d ⊢
  nlinarith only [hl, hAt, hMt, ht1d, ht2d, hds]

/-- A nonnegative square-root scale and Euler constant, with a small endpoint correction,
bound the principal reciprocal contribution. Insert the endpoint cap and logarithmic
decay certificate to retain the constant saving needed for the coset radius. -/
private theorem scaled_principal_reciprocal {s t gamma u : ℝ} (hs : 0 ≤ s) (ht : t ≤ s / 350)
    (hg : 0 ≤ gamma) (hu : u ≤ 1 / 100) :
    2 * (s + 19 / 6) * (t - (1 + gamma) + u) ≤ 2 * s * t - (19 / 10 : ℝ) * s := by
  have hQ : t - (1 + gamma) + u ≤ t - 99 / 100 := by linarith only [hg, hu]
  have hm :=
    mul_le_mul_of_nonneg_left hQ
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2)
        (add_nonneg hs (by norm_num only : (0 : ℝ) ≤ 19 / 6)))
  nlinarith only [hm, ht, hs]

/-- A scaled coset sandwich with index-minus-one scale at least one, square-root cutoff
at least 31600 and logarithm at least four implies the coarse Section 4 radius.
Combine the norm error, reciprocal correction and principal losses, then cancel the
positive square root. This connects the character comparison to the radius bootstrap. -/
private theorem coarse_radius_of_sandwich {d s t L A M P gamma u R : ℝ} (hd : 1 ≤ d)
    (hs : 31600 ≤ s) (ht : 4 ≤ t) (hscale : d * L ≤ s)
    (hdec : (7 / 2 : ℝ) * t + t ^ 2 / 3 ≤ s / 100) (hA : A ≤ L) (hM : M ≤ L + 1 + t) (hP : P ≤ 2)
    (hg : 0 ≤ gamma) (hu : u ≤ 1 / 100)
    (hbound :
      s ^ 2 - P * t - 1 - (s + 1) / 20 - s * R ≤
        (d + 1) * (11 / 5 : ℝ) * s +
          d * ((s + 19 / 6) * (L - 51 / 50) + t ^ 2 + ((2 / 3 : ℝ) * A + 4) * t + t / 2 * M) +
          2 * (s + 19 / 6) * (t - (1 + gamma) + u)) :
    s ≤ d * L + (5 / 4 : ℝ) * (d + 2) + (7 / 2 : ℝ) * t + R := by
  have hd0 := (by norm_num only : (0 : ℝ) ≤ 1).trans hd
  have hs0 := (by norm_num only : (0 : ℝ) ≤ 31600).trans hs
  have ht0 := (by norm_num only : (0 : ℝ) ≤ 4).trans ht
  have ht1 : t ≤ s / 350 := by nlinarith only [hdec, sq_nonneg t]
  have hE := scaled_coset_error hd0 ht0 hscale hdec hA hM
  have hQ := scaled_principal_reciprocal hs0 ht1 hg hu
  have hPt := mul_le_mul_of_nonneg_right hP ht0
  have hloss : P * t + 1 + (s + 1) / 20 ≤ (7 / 100 : ℝ) * s := by nlinarith only [hPt, ht1, hs]
  have hbase :
    d * (s + 19 / 6) * (L - 51 / 50) ≤ d * s * L - (51 / 50 : ℝ) * d * s + 19 / 6 * s := by
    nlinarith only [hscale, hd0]
  have hds := mul_nonneg hd0 hs0
  have hst := mul_le_mul_of_nonneg_left ht hs0
  apply (mul_le_mul_iff_right₀ (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 31600) hs)).mp
  simp only [div_eq_mul_inv] at hbound hE hQ hloss hbase hst ⊢
  nlinarith only [hbound, hE, hQ, hloss, hbase, hds, hst, hs0]

/-- For modulus at least twenty thousand and cutoff at least one billion, the logarithm
of the parity maximum is at most the level logarithm plus one plus the cutoff logarithm.
Bound both entries by the level times twice the cutoff. This majorizes the norm error. -/
private theorem coset_log_max_bound {q : ℕ} (hq : 20000 ≤ q) {x : ℝ} (hx : 1000000000 ≤ x) :
    Real.log (max ((q : ℝ) / Real.pi) (2 * x)) ≤ Real.log q + 1 + Real.log x := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by linarith only [hq] : 1 ≤ q)
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans_le hq1
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only) hx
  have hx1 : (1 : ℝ) ≤ 2 * x := by linarith only [hx]
  have hp1 : (1 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_three]
  have hqp : (q : ℝ) / Real.pi ≤ q :=
    (div_le_iff₀ Real.pi_pos).mpr
      (by
        have hm := mul_le_mul_of_nonneg_left hp1 hq0.le
        simpa only [mul_one] using hm)
  have hleft : (q : ℝ) / Real.pi ≤ (q : ℝ) * (2 * x) :=
    hqp.trans
      (by
        have hm := mul_le_mul_of_nonneg_left hx1 hq0.le
        simpa only [mul_one] using hm)
  have hright : 2 * x ≤ (q : ℝ) * (2 * x) := by
    have hm := mul_le_mul_of_nonneg_right hq1 (mul_pos (by norm_num only : (0 : ℝ) < 2) hx0).le
    simpa only [one_mul] using hm
  have he :=
    Real.log_le_log
      (lt_of_lt_of_le (mul_pos (by norm_num only : (0 : ℝ) < 2) hx0) (le_max_right _ _))
      (max_le hleft hright)
  rw [Real.log_mul hq0.ne' (mul_pos (by norm_num only : (0 : ℝ) < 2) hx0).ne',
    Real.log_mul (by norm_num only) hx0.ne'] at he
  linarith only [he, Real.log_two_lt_d9]

/-- At cutoff at least one billion, the principal reciprocal endpoint correction is at
most one hundredth. Use the upper bound for the logarithm of twice pi and the square-root
lower bound 31600. This supplies the constant saving in the explicit coset sandwich. -/
private theorem coset_reciprocal_endpoint_small {x : ℝ} (hx : 1000000000 ≤ x) :
    Real.log (2 * Real.pi) / x + 1 / (20 * Real.sqrt x) ≤ (1 / 100 : ℝ) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only) hx
  have hs : (31600 : ℝ) ≤ Real.sqrt x :=
    Real.le_sqrt_of_sq_le ((by norm_num only : (31600 : ℝ) ^ 2 ≤ 1000000000).trans hx)
  have hP : Real.log (2 * Real.pi) ≤ (2 : ℝ) := by linarith only [Analysis.log_two_mul_pi_lt]
  have he :=
    (div_le_div_of_nonneg_right hP hx0.le).trans
      (div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 2)
        (by norm_num only : (0 : ℝ) < 1000000000) hx)
  have hf :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 1)
      (by norm_num only : (0 : ℝ) < 20 * 31600)
      (mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 20))
  norm_num only at he hf ⊢
  linarith only [he, hf]

theorem coset_coarse_bound_of_no_prime
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} [NeZero q]
    (hq : 20000 ≤ q) (H : Subgroup (ZMod q)ˣ) (hh : 1 < H.index) (a : (ZMod q)ˣ) {x : ℝ}
    (hx : 1000000000 ≤ x) (hno : ∀ p : ℕ, p ∈ primesInCoset q H a → ¬(p : ℝ) ≤ x) :
    Real.sqrt x ≤
      ((H.index : ℝ) - 1) * Real.log q + (5 / 4 : ℝ) * ((H.index : ℝ) + 1) +
        (7 / 2 : ℝ) * Real.log x +
        (Real.log x) ^ 2 / (3 * ((H.index : ℝ) - 1)) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only) hx
  have hd : (1 : ℝ) ≤ (H.index : ℝ) - 1 := by
    have hr : (2 : ℝ) ≤ H.index := by exact_mod_cast Nat.succ_le_of_lt hh
    linarith only [hr]
  have hd0 : (0 : ℝ) < (H.index : ℝ) - 1 := zero_lt_one.trans_le hd
  have ht : (4 : ℝ) ≤ Real.log x := by
    have he :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 81)
        ((by norm_num only : (81 : ℝ) ≤ 1000000000).trans hx)
    rw [show (81 : ℝ) = 3 ^ 4 by norm_num only, Real.log_pow] at he
    norm_num only at he
    linarith only [he, Real.log_three_gt_d9]
  by_cases hscale : ((H.index : ℝ) - 1) * Real.log q ≤ Real.sqrt x
  · have hb :
      x - Real.log (2 * Real.pi) * Real.log x - 1 - (Real.sqrt x + 1) / 20 -
          Real.sqrt x / (3 * ((H.index : ℝ) - 1)) * (Real.log x) ^ 2 ≤
        (H.index : ℝ) * ((11 / 5 : ℝ) * Real.sqrt x) + cosetNonprincipalUpper q H x := by
      apply le_of_not_gt
      intro hgap
      obtain ⟨p, hp, hpx⟩ :=
        exists_least_prime_in_coset_le_of_scaled_gap H a hq hGRH hx hh hscale hgap
      exact hno p hp.1 hpx
    have hs : (31600 : ℝ) ≤ Real.sqrt x :=
      Real.le_sqrt_of_sq_le ((by norm_num only : (31600 : ℝ) ^ 2 ≤ 1000000000).trans hx)
    have hA : Real.log ((q : ℝ) / Real.pi) ≤ Real.log q := by
      rw [Real.log_div (Nat.cast_ne_zero.mpr (NeZero.ne q)) Real.pi_pos.ne']
      have hp : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith only [Real.pi_gt_three])
      linarith only [hp]
    have hP : Real.log (2 * Real.pi) ≤ (2 : ℝ) := by linarith only [Analysis.log_two_mul_pi_lt]
    have hg : 0 ≤ Real.eulerMascheroniConstant := by
      linarith only [Analysis.twentyThree_fortieths_lt_eulerMascheroniConstant]
    have hb' :
      (Real.sqrt x) ^ 2 - Real.log (2 * Real.pi) * Real.log x - 1 - (Real.sqrt x + 1) / 20 -
          Real.sqrt x * ((Real.log x) ^ 2 / (3 * ((H.index : ℝ) - 1))) ≤
        (((H.index : ℝ) - 1) + 1) * (11 / 5 : ℝ) * Real.sqrt x +
          ((H.index : ℝ) - 1) *
            ((Real.sqrt x + 19 / 6) * (Real.log q - 51 / 50) + (Real.log x) ^ 2 +
              ((2 / 3 : ℝ) * Real.log ((q : ℝ) / Real.pi) + 4) * Real.log x +
              Real.log x / 2 * Real.log (max ((q : ℝ) / Real.pi) (2 * x))) +
          2 * (Real.sqrt x + 19 / 6) *
            (Real.log x - (1 + Real.eulerMascheroniConstant) +
              (Real.log (2 * Real.pi) / x + 1 / (20 * Real.sqrt x))) := by
      dsimp only [cosetNonprincipalUpper, cosetCharacterNormError] at hb
      rw [Real.sq_sqrt hx0.le]
      convert hb using 1 <;> ring
    have hc :=
      coarse_radius_of_sandwich hd hs ht hscale (Analysis.log_error_le_sqrt_hundredth hx) hA
        (coset_log_max_bound hq hx) hP hg (coset_reciprocal_endpoint_small hx) hb'
    nlinarith only [hc]
  · have hr : Real.sqrt x ≤ ((H.index : ℝ) - 1) * Real.log q := (le_of_not_ge hscale)
    have hR : 0 ≤ (Real.log x) ^ 2 / (3 * ((H.index : ℝ) - 1)) :=
      div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num only) hd0.le)
    have hi : (0 : ℝ) ≤ H.index := Nat.cast_nonneg H.index
    nlinarith only [hr, ht, hR, hi]

/-- GRH implies Theorem 1.4 with its original modulus threshold, exceptional bound of
one billion, coefficient and least-prime condition. Combine the proved coarse no-prime
inequality with the radius comparison. A least prime above both bounds contradicts
the square root of their maximum cutoff. -/
theorem theorem14 : lls_theorem14 := by
  apply theorem14_of_coarse_bounds
  intro hGRH q _ hq H hh a x hx hno
  exact coset_coarse_bound_of_no_prime hGRH hq H hh a hx hno

end PseudoPrime.LLS.PaperStatements
