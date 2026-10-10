/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.CosetRadiusNumerics

/-! # The final explicit coset-radius comparison

Finite small-index logarithmic certificates and a large-index polynomial margin
compare the refined radius with the coefficient in Theorem 1.4.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For scales at least sixteen and log-levels at least two, the polynomial margin
of the affine logarithmic cap is strictly positive. Expand around the lower bounds;
all remaining factors are nonnegative. This certifies the large-index comparison. -/
private theorem large_radius_polynomial {d v : ℝ} (hd : 16 ≤ d) (hv : 2 ≤ v) :
    (7 / 4 : ℝ) * d ^ 2 + (7 / 2 : ℝ) * d + (5 / 2 : ℝ) * d * v ^ 2 - 7 * d * (v + d / 8 + 3 / 2) -
        (4 / 3 : ℝ) * (v + d / 8 + 3 / 2) ^ 2 >
      0 := by
  have ha : 0 ≤ d - 16 := sub_nonneg.mpr hd
  have hb : 0 ≤ v - 2 := sub_nonneg.mpr hv
  have hab := mul_nonneg ha hb
  have hab2 := mul_nonneg ha (sq_nonneg (v - 2))
  nlinarith only [ha, hb, hab, hab2, sq_nonneg (d - 16), sq_nonneg (v - 2)]

/-- For a scale at least sixteen, the logarithm of twice the scale is at most
one eighth of the scale plus three halves. Use the tangent line at thirty-two and
the rational bound for the logarithm of two. This controls the large-index logarithm. -/
private theorem log_twice_scale_le {d : ℝ} (hd : 16 ≤ d) : Real.log (2 * d) ≤ d / 8 + 3 / 2 := by
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num only) hd
  have he :=
    Analysis.log_le_log_add_sub_div (a := (32 : ℝ)) (y := 2 * d) (by norm_num only)
      (mul_pos (by norm_num only) hd0)
  rw [show (32 : ℝ) = 2 ^ 5 by norm_num only, Real.log_pow] at he
  norm_num only at he
  linarith only [he, hd, Real.log_two_lt_d9]

/-- For scales at least sixteen and levels at least nine, the logarithmic terms
of the refined coset radius fit strictly inside the remaining paper coefficient.
Insert the affine logarithmic cap and the polynomial certificate, then cancel the
positive scale. This handles subgroup indices at least seventeen. -/
private theorem large_coset_radius_comparison {d L : ℝ} (hd : 16 ≤ d) (hL : 9 ≤ L) :
    7 * Real.log (2 * d * L) + 4 * (Real.log (2 * d * L)) ^ 2 / (3 * d) <
      (7 / 4 : ℝ) * (d + 2) + (5 / 2 : ℝ) * (Real.log L) ^ 2 := by
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num only) hd
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num only) hL
  have hv : 2 ≤ Real.log L := by
    have he := Real.log_le_log (by norm_num only : (0 : ℝ) < 9) hL
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num only, Real.log_pow] at he
    norm_num only at he
    linarith only [he, Real.log_three_gt_d9]
  have hw0 : 0 ≤ Real.log (2 * d) := Real.log_nonneg (by linarith only [hd])
  have hw := log_twice_scale_le hd
  have hsum0 := add_nonneg (show 0 ≤ Real.log L by linarith only [hv]) hw0
  have hsum : Real.log L + Real.log (2 * d) ≤ Real.log L + d / 8 + 3 / 2 := by linarith only [hw]
  have hs := mul_self_le_mul_self hsum0 hsum
  have hm := mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 7) hd0.le)
  have hn := large_radius_polynomial hd hv
  rw [Real.log_mul (mul_pos (by norm_num only) hd0).ne' hL0.ne']
  have he (v w : ℝ) :
    7 * (v + w) + 4 * (v + w) ^ 2 / (3 * d) =
      (7 * d * (v + w) + (4 / 3 : ℝ) * (v + w) ^ 2) / d := by
    apply (eq_div_iff hd0.ne').mpr
    rw [mul_comm (3 : ℝ) d]
    simp only [add_mul, div_eq_mul_inv, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hd0.ne', mul_one]
    ring
  rw [add_comm (Real.log (2 * d)) (Real.log L), he]
  apply (div_lt_iff₀ hd0).mpr
  nlinarith only [hs, hm, hn]

/-- For scales between four and sixteen and levels at least nine whose product
is at least 15800, the refined logarithmic terms fit strictly inside the paper coefficient.
The product forces the log-level above six; cap the scale logarithm by seven halves
and the reciprocal scale by one quarter. This handles the intermediate indices. -/
private theorem medium_coset_radius_comparison {d L : ℝ} (hd : 4 ≤ d) (hd' : d ≤ 16) (hL : 9 ≤ L)
    (hp : 15800 ≤ d * L) :
    7 * Real.log (2 * d * L) + 4 * (Real.log (2 * d * L)) ^ 2 / (3 * d) <
      (7 / 4 : ℝ) * (d + 2) + (5 / 2 : ℝ) * (Real.log L) ^ 2 := by
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num only) hd
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num only) hL
  have hLP := mul_le_mul_of_nonneg_right hd' hL0.le
  have h729 : (729 : ℝ) ≤ L := by nlinarith only [hp, hLP]
  have hv : 6 ≤ Real.log L := by
    have he := Real.log_le_log (by norm_num only : (0 : ℝ) < 729) h729
    rw [show (729 : ℝ) = 3 ^ 6 by norm_num only, Real.log_pow] at he
    norm_num only at he
    linarith only [he, Real.log_three_gt_d9]
  have hw0 : 0 ≤ Real.log (2 * d) := Real.log_nonneg (by linarith only [hd])
  have hw : Real.log (2 * d) ≤ (7 / 2 : ℝ) := by
    have he :=
      Real.log_le_log (mul_pos (by norm_num only) hd0)
        (show 2 * d ≤ (32 : ℝ) by linarith only [hd'])
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num only, Real.log_pow] at he
    norm_num only at he
    linarith only [he, Real.log_two_lt_d9]
  have hsum0 := add_nonneg (show 0 ≤ Real.log L by linarith only [hv]) hw0
  have hsum : Real.log L + Real.log (2 * d) ≤ Real.log L + 7 / 2 := by linarith only [hw]
  have hs := mul_self_le_mul_self hsum0 hsum
  have hm :=
    mul_nonneg (show 0 ≤ d - 4 by linarith only [hd]) (sq_nonneg (Real.log L + Real.log (2 * d)))
  have hf :
    4 * (Real.log L + Real.log (2 * d)) ^ 2 / (3 * d) ≤ (Real.log L + Real.log (2 * d)) ^ 2 / 3 :=
    (div_le_div_iff₀ (mul_pos (by norm_num only) hd0) (by norm_num only)).mpr
      (by nlinarith only [hm])
  have hs' := div_le_div_of_nonneg_right hs (show (0 : ℝ) ≤ 3 by norm_num only)
  have hv0 : 0 ≤ Real.log L - 6 := by linarith only [hv]
  have hn :
    7 * (Real.log L + 7 / 2) + (Real.log L + 7 / 2) ^ 2 / 3 <
      (21 / 2 : ℝ) + (5 / 2 : ℝ) * (Real.log L) ^ 2 := by
    nlinarith only [hv0, sq_nonneg (Real.log L - 6)]
  rw [Real.log_mul (mul_pos (by norm_num only) hd0).ne' hL0.ne',
    add_comm (Real.log (2 * d)) (Real.log L)]
  nlinarith only [hs', hf, hn, hsum, hd]

/-- If a real level is at least the nth power of three, its logarithm is at least n.
Take logarithms and use the lower bound of one for the logarithm of three.
This supplies the small-index log-level certificates. -/
private theorem log_level_ge_nat {L : ℝ} (n : ℕ) (hn : (3 : ℝ) ^ n ≤ L) : (n : ℝ) ≤ Real.log L := by
  have he := Real.log_le_log (pow_pos (by norm_num only : (0 : ℝ) < 3) n) hn
  rw [Real.log_pow] at he
  have hm :=
    mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      (show 0 ≤ Real.log 3 - 1 by linarith only [Real.log_three_gt_d9])
  nlinarith only [he, hm]

/-- For positive subgroup scales and levels, a cap on the scale logarithm transfers
a polynomial margin to the actual refined radius. Both logarithms are nonnegative,
so the linear and squared terms are monotone. This packages the small-index certificates. -/
private theorem radius_comparison_of_log_cap {d L C : ℝ} (hd : 1 ≤ d) (hL : 9 ≤ L)
    (hw : Real.log (2 * d) ≤ C)
    (hc :
      7 * (Real.log L + C) + 4 * (Real.log L + C) ^ 2 / (3 * d) <
        (7 / 4 : ℝ) * (d + 2) + (5 / 2 : ℝ) * (Real.log L) ^ 2) :
    7 * Real.log (2 * d * L) + 4 * (Real.log (2 * d * L)) ^ 2 / (3 * d) <
      (7 / 4 : ℝ) * (d + 2) + (5 / 2 : ℝ) * (Real.log L) ^ 2 := by
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num only) hL
  have hv0 : 0 ≤ Real.log L := Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 9).trans hL)
  have hw0 : 0 ≤ Real.log (2 * d) := Real.log_nonneg (by linarith only [hd])
  have hsum : Real.log L + Real.log (2 * d) ≤ Real.log L + C := by linarith only [hw]
  have hs := mul_self_le_mul_self (add_nonneg hv0 hw0) hsum
  have hs' :=
    mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hs (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 3) hd0.le))
      (show (0 : ℝ) ≤ 4 by norm_num only)
  rw [Real.log_mul (mul_pos (by norm_num only) hd0).ne' hL0.ne',
    add_comm (Real.log (2 * d)) (Real.log L)]
  simp only [← pow_two, ← mul_div_assoc] at hs'
  nlinarith only [hs', hc, hsum]

/-- For indices two through four, a level at least nine and scale-level product
at least 15800 imply the strict refined-radius comparison. The product forces the
log-level above eight at index two and above seven at the other indices. Rational
caps for the logarithms of two, four and six finish the finite cases. -/
private theorem small_coset_radius_comparison {h : ℕ} (hh : 2 ≤ h) (hh' : h ≤ 4) {L : ℝ}
    (hL : 9 ≤ L) (hp : 15800 ≤ ((h : ℝ) - 1) * L) :
    7 * Real.log (2 * ((h : ℝ) - 1) * L) +
        4 * (Real.log (2 * ((h : ℝ) - 1) * L)) ^ 2 / (3 * ((h : ℝ) - 1)) <
      (7 / 4 : ℝ) * ((h : ℝ) + 1) + (5 / 2 : ℝ) * (Real.log L) ^ 2 := by
  interval_cases h
  · norm_num only at hp ⊢
    have hv :=
      log_level_ge_nat 8
        (show (3 : ℝ) ^ 8 ≤ L by
          norm_num only; linarith only [hp])
    have hw : Real.log (2 * (1 : ℝ)) ≤ 7 / 10 := by
      norm_num only
      linarith only [Real.log_two_lt_d9]
    have hc :
      7 * (Real.log L + (7 / 10 : ℝ)) + 4 * (Real.log L + (7 / 10 : ℝ)) ^ 2 / (3 * (1 : ℝ)) <
        (7 / 4 : ℝ) * ((1 : ℝ) + 2) + (5 / 2 : ℝ) * (Real.log L) ^ 2 := by
      norm_num only at hv ⊢
      nlinarith only [hv, sq_nonneg (Real.log L - 8)]
    have ht := radius_comparison_of_log_cap (by norm_num only : (1 : ℝ) ≤ 1) hL hw hc
    norm_num only at ht
    exact ht
  · norm_num only at hp ⊢
    have hv :=
      log_level_ge_nat 7
        (show (3 : ℝ) ^ 7 ≤ L by
          norm_num only; linarith only [hp])
    have hw : Real.log (2 * (2 : ℝ)) ≤ 7 / 5 := by
      norm_num only
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
      norm_num only
      linarith only [Real.log_two_lt_d9]
    have hc :
      7 * (Real.log L + (7 / 5 : ℝ)) + 4 * (Real.log L + (7 / 5 : ℝ)) ^ 2 / (3 * (2 : ℝ)) <
        (7 / 4 : ℝ) * ((2 : ℝ) + 2) + (5 / 2 : ℝ) * (Real.log L) ^ 2 := by
      norm_num only at hv ⊢
      nlinarith only [hv, sq_nonneg (Real.log L - 7)]
    have ht := radius_comparison_of_log_cap (by norm_num only : (1 : ℝ) ≤ 2) hL hw hc
    norm_num only at ht
    exact ht
  · norm_num only at hp ⊢
    have hv :=
      log_level_ge_nat 7
        (show (3 : ℝ) ^ 7 ≤ L by
          norm_num only; linarith only [hp])
    have hw : Real.log (2 * (3 : ℝ)) ≤ 9 / 5 := by
      norm_num only
      rw [show (6 : ℝ) = 2 * 3 by norm_num only, Real.log_mul (by norm_num only) (by norm_num only)]
      linarith only [Real.log_two_lt_d9, Real.log_three_lt_d9]
    have hc :
      7 * (Real.log L + (9 / 5 : ℝ)) + 4 * (Real.log L + (9 / 5 : ℝ)) ^ 2 / (3 * (3 : ℝ)) <
        (7 / 4 : ℝ) * ((3 : ℝ) + 2) + (5 / 2 : ℝ) * (Real.log L) ^ 2 := by
      norm_num only at hv ⊢
      nlinarith only [hv, sq_nonneg (Real.log L - 7)]
    have ht := radius_comparison_of_log_cap (by norm_num only : (1 : ℝ) ≤ 3) hL hw hc
    norm_num only at ht
    exact ht

/-- For any natural index at least two, a level at least nine and scale-level product
at least 15800, the refined logarithmic terms fit strictly inside the remaining
Theorem 1.4 coefficient. Combine the small, intermediate and large-index certificates.
This removes every extra numerical premise from the final radius comparison. -/
theorem coset_radius_comparison {h : ℕ} (hh : 2 ≤ h) {L : ℝ} (hL : 9 ≤ L)
    (hp : 15800 ≤ ((h : ℝ) - 1) * L) :
    7 * Real.log (2 * ((h : ℝ) - 1) * L) +
        4 * (Real.log (2 * ((h : ℝ) - 1) * L)) ^ 2 / (3 * ((h : ℝ) - 1)) <
      (7 / 4 : ℝ) * ((h : ℝ) + 1) + (5 / 2 : ℝ) * (Real.log L) ^ 2 := by
  by_cases hl : 17 ≤ h
  · have hd : (16 : ℝ) ≤ (h : ℝ) - 1 := by
      have hr : (17 : ℝ) ≤ h := by exact_mod_cast hl
      linarith only [hr]
    have hc := large_coset_radius_comparison hd hL
    nlinarith only [hc]
  · by_cases hs : h ≤ 4
    · exact small_coset_radius_comparison hh hs hL hp
    · have hd : (4 : ℝ) ≤ (h : ℝ) - 1 := by
        have hr : (5 : ℝ) ≤ h := by exact_mod_cast Nat.succ_le_of_lt (lt_of_not_ge hs)
        linarith only [hr]
      have hd' : (h : ℝ) - 1 ≤ 16 := by
        have hr : (h : ℝ) ≤ 16 := by exact_mod_cast Nat.le_of_lt_succ (lt_of_not_ge hl)
        linarith only [hr]
      have hc := medium_coset_radius_comparison hd hd' hL hp
      nlinarith only [hc]

/-- At modulus at least twenty thousand, index at least two and cutoff at least
one billion, the coarse Section 4 inequality gives a square root strictly below
Theorem 1.4's radius. Bootstrap the cutoff, use its lower bound to obtain the required
scale-level product, then apply the complete coefficient comparison.
Only the displayed coarse inequality remains an input. -/
theorem coset_cutoff_lt_paper_radius {q h : ℕ} (hq : 20000 ≤ q) (hh : 2 ≤ h) {x : ℝ}
    (hx : 1000000000 ≤ x)
    (hc :
      Real.sqrt x ≤
        ((h : ℝ) - 1) * Real.log q + (5 / 4 : ℝ) * ((h : ℝ) + 1) + (7 / 2 : ℝ) * Real.log x +
          (Real.log x) ^ 2 / (3 * ((h : ℝ) - 1))) :
    Real.sqrt x < cosetBoundRadius q h := by
  have hr := coset_refined_radius_of_coarse_bound hq hh hx hc
  have hb := coset_cutoff_le_twice_scale hq hh hx hc
  have hs : (31600 : ℝ) ≤ Real.sqrt x :=
    Real.le_sqrt_of_sq_le ((by norm_num only : (31600 : ℝ) ^ 2 ≤ 1000000000).trans hx)
  have hp : (15800 : ℝ) ≤ ((h : ℝ) - 1) * Real.log q := by linarith only [hs, hb]
  have hl :=
    log_level_ge_nat 9
      (show (3 : ℝ) ^ 9 ≤ (q : ℝ) by
        norm_num only
        exact_mod_cast (by linarith only [hq] : 19683 ≤ q))
  have ht :=
    coset_radius_comparison hh
      (by
        norm_num only at hl; exact hl)
      hp
  unfold cosetBoundRadius
  nlinarith only [hr, ht]

theorem theorem14_of_coarse_bounds
    (hcoarse :
      AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
        ∀ (q : ℕ) [NeZero q],
          20000 ≤ q →
            ∀ H : Subgroup (ZMod q)ˣ,
              1 < H.index →
                ∀ a : (ZMod q)ˣ,
                  ∀ x : ℝ,
                    1000000000 ≤ x →
                      (∀ p : ℕ, p ∈ primesInCoset q H a → ¬(p : ℝ) ≤ x) →
                      Real.sqrt x ≤
                        ((H.index : ℝ) - 1) * Real.log q + (5 / 4 : ℝ) * ((H.index : ℝ) + 1) +
                          (7 / 2 : ℝ) * Real.log x +
                          (Real.log x) ^ 2 / (3 * ((H.index : ℝ) - 1))) :
    lls_theorem14 := by
  intro hGRH q _ hq H hh a
  obtain ⟨p, hp⟩ := exists_least_prime_in_coset H a
  refine ⟨p, hp, ?_⟩
  by_contra hn
  have hn' : ¬((p : ℝ) ≤ 1000000000 ∨ (p : ℝ) ≤ (cosetBoundRadius q H.index) ^ 2) := by
    norm_num only at hn
    exact hn
  let x := max (1000000000 : ℝ) ((cosetBoundRadius q H.index) ^ 2)
  have hpX : x < (p : ℝ) := lt_of_not_ge (fun hpx ↦ hn' (le_max_iff.mp hpx))
  have hno (r : ℕ) (hr : r ∈ primesInCoset q H a) (hrx : (r : ℝ) ≤ x) : False :=
    (not_le_of_gt hpX) ((Nat.cast_le.mpr (hp.2 hr)).trans hrx)
  have hx : (1000000000 : ℝ) ≤ x := le_max_left _ _
  have hc := hcoarse hGRH q hq H hh a x hx hno
  have hs := coset_cutoff_lt_paper_radius hq (Nat.succ_le_of_lt hh) hx hc
  have hb : cosetBoundRadius q H.index ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (le_max_right _ _)
  exact (not_lt_of_ge hb) hs

end PseudoPrime.LLS.PaperStatements
