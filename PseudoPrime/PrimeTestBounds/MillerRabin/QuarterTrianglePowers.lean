/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrimeWindow576

/-! # Prime powers in the section 86 triangle window -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On the section 86 radius interval, the prime base of every square in the
wide triangle belongs to the fixed range from 288 through 3600. -/
theorem triangle_square_base_576 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 288) {p : ℕ} (hp : p.Prime)
    (hlo : r ^ 2 < (p : ℝ) ^ 2) (hhi : (p : ℝ) ^ 2 ≤ Real.exp 5 * r ^ 2) :
    p ∈ (Finset.Ioc 287 3600).filter Nat.Prime := by
  have hr : 0 ≤ r := by linarith only [hl]
  have hsmall := lt_of_pow_lt_pow_left₀ 2 (Nat.cast_nonneg p) hlo
  have he : Real.exp 5 < (25 / 2 : ℝ) ^ 2 := by
    have h :=
      pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num only : (5 : ℕ) ≠ 0)
    rw [← Real.exp_natCast_mul] at h
    norm_num only [Nat.cast_ofNat, mul_one] at h
    exact h.trans (by norm_num only)
  have hb :=
    hhi.trans
      ((mul_le_mul_of_nonneg_right he.le (sq_nonneg r)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hu 2) (sq_nonneg _)))
  have hpu : (p : ℝ) ≤ 3600 := by
    apply le_of_not_gt
    intro hgt
    have hsq :=
      pow_lt_pow_left₀ hgt (by norm_num only : (0 : ℝ) ≤ 3600) (by norm_num only : (2 : ℕ) ≠ 0)
    linarith only [hsq, hb]
  exact
    Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨by exact_mod_cast hl.trans_lt hsmall, by exact_mod_cast hpu⟩, hp⟩

/-- The shifted triangle weight of a prime square never exceeds its
unweighted reciprocal-prime contribution. -/
theorem triangle_square_weight_le (p : ℕ) (x : ℝ) :
    Real.log p * (shiftedTriangle (5 / 2) x / Real.sqrt ((p : ℝ) ^ 2)) ≤ Real.log p / p := by
  have ht : shiftedTriangle (5 / 2) x ≤ 1 := by
    unfold shiftedTriangle
    exact max_le zero_le_one (sub_le_self _ (div_nonneg (abs_nonneg _) (by norm_num only)))
  rw [Real.sqrt_sq (Nat.cast_nonneg p), ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left ht (Real.log_natCast_nonneg p)

/-- The square part of the wide triangle is bounded by a fixed sum over
prime bases, uniformly in the radius and in the triangle coordinates. -/
theorem triangle_square_majorant_576 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 288) (s : Finset ℕ)
    (x : ℕ → ℝ) (hp : ∀ p ∈ s, p.Prime) (hlo : ∀ p ∈ s, r ^ 2 < (p : ℝ) ^ 2)
    (hhi : ∀ p ∈ s, (p : ℝ) ^ 2 ≤ Real.exp 5 * r ^ 2) :
    (∑ p ∈ s, Real.log p * (shiftedTriangle (5 / 2) (x p) / Real.sqrt ((p : ℝ) ^ 2))) ≤
      ∑ p ∈ (Finset.Ioc 287 3600).filter Nat.Prime, Real.log p / p := by
  apply (Finset.sum_le_sum (fun p _ => triangle_square_weight_le p (x p))).trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact fun p h => triangle_square_base_576 hl hu (hp p h) (hlo p h) (hhi p h)
  · exact fun p _ _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

/-- Integer upper weight for candidates coprime to the product of primes through 59. -/
private def squareSieve (p : ℕ) : ℕ :=
  if p.gcd 1922760350154212639070 = 1 then 90000 / p + 1 else 0

/-- The enclosing interval has total integer weight at most 32500. -/
private theorem square_sieve_total : ∑ p ∈ Finset.Ioc 287 3600, squareSieve p ≤ 32500 := by
  decide +kernel

/-- The square contribution on the section 86 window is bounded using
an integer majorant for each reciprocal prime in its fixed enclosing interval. -/
private theorem triangle_square_sum_of_sieve (s : Finset ℕ) (N C : ℕ) (hN : N ≤ 3913)
    (hC : ∑ p ∈ Finset.Ioc 287 N, squareSieve p ≤ C)
    (hs : s ⊆ (Finset.Ioc 287 N).filter Nat.Prime) : ∑ p ∈ s, Real.log p / p ≤ (C : ℝ) / 10000 := by
  let primes := (Finset.Ioc 287 N).filter Nat.Prime
  have hc : (∑ p ∈ primes, (90000 / p + 1 : ℕ)) ≤ C := by
    apply le_trans _ hC
    dsimp only [primes]
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro p hp
    split_ifs with hpr
    · have hlo := (Finset.mem_Ioc.mp hp).1
      have hsmall {q : ℕ} (hq : 0 < q) (ht : q ≤ 287) : p.Coprime q :=
        hpr.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hq (ht.trans_lt hlo))
      have hcop :
        p.Coprime
          (2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 * 29 * 31 * 37 * 41 * 43 * 47 * 53 * 59) := by
        repeat' apply Nat.Coprime.mul_right
        all_goals exact hsmall (by decide) (by decide)
      unfold squareSieve
      rw [ite_eq_left (show p.gcd 1922760350154212639070 = 1 from hcop)]
    · exact Nat.zero_le _
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 3913) (j := 12) (n := 24) (lo := 8) (hi := 9)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat] at hlog
  have hh (p : ℕ) (hp : p ∈ primes) : Real.log p / p ≤ ((90000 / p + 1 : ℕ) : ℝ) / 10000 := by
    have hmem := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    have hpos := (Finset.mem_filter.mp hp).2.pos
    have hx : (0 : ℝ) < p := Nat.cast_pos.mpr hpos
    have ht := Real.log_le_log hx (show (p : ℝ) ≤ 3913 by exact_mod_cast hmem.2.trans hN)
    have hd : (90000 : ℝ) < p * ((90000 / p + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_mul_div_succ 90000 hpos
    apply (div_le_iff₀ hx).2
    linarith only [ht, hlog, hd]
  have hsub :=
    Finset.sum_le_sum_of_subset_of_nonneg hs
      (fun p _ _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
  apply hsub.trans ((Finset.sum_le_sum hh).trans _)
  rw [← Finset.sum_div, ← Nat.cast_sum]
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hc) (by norm_num only)

/-- The section 86 reciprocal-prime sum is at most 13/4 by the square sieve. -/
theorem triangle_square_sum_576 (s : Finset ℕ) (hs : s ⊆ (Finset.Ioc 287 3600).filter Nat.Prime) :
    ∑ p ∈ s, Real.log p / p ≤ 13 / 4 := by
  exact
    (triangle_square_sum_of_sieve s 3600 32500 (by decide) square_sieve_total hs).trans
      (by norm_num only)

/-- On section 86 the prime-square contribution to the wide triangle is at
most 13/4, by the fixed reciprocal-prime certificate. -/
theorem triangle_square_bound_576 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 288) (s : Finset ℕ) (x : ℕ → ℝ)
    (hp : ∀ p ∈ s, p.Prime) (hlo : ∀ p ∈ s, r ^ 2 < (p : ℝ) ^ 2)
    (hhi : ∀ p ∈ s, (p : ℝ) ^ 2 ≤ Real.exp 5 * r ^ 2) :
    (∑ p ∈ s, Real.log p * (shiftedTriangle (5 / 2) (x p) / Real.sqrt ((p : ℝ) ^ 2))) ≤ 13 / 4 := by
  exact
    (triangle_square_majorant_576 hl hu s x hp hlo hhi).trans
      (triangle_square_sum_576 _ (fun _ h => h))

/-- Scaled integer majorant for one higher power in the fixed enclosing window. -/
private def higherWeight (p k : ℕ) : ℕ :=
  let n := p ^ k
  if 82369 < n ∧ n ≤ 15307657 then 60000 / n.sqrt + 1 else 0

/-- Summing over all integer bases already gives a higher-power bound below 1.7. -/
private theorem higher_total :
    (∑ p ∈ Finset.Icc 2 248, ∑ k ∈ Finset.Icc 3 23, higherWeight p k) ≤ 16650 := by decide +kernel

/-- Each higher-power triangle weight in the enclosing window is bounded
by its rounded integer weight divided by 10000. -/
private theorem higher_weight_le {p k : ℕ} (hp0 : 0 < p) (hp : p ≤ 248)
    (hn : 82369 < p ^ k ∧ p ^ k ≤ 15307657) (x : ℝ) :
    Real.log p * (shiftedTriangle (5 / 2) x / Real.sqrt (p ^ k : ℕ)) ≤
      (higherWeight p k : ℝ) / 10000 := by
  let n := p ^ k
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn.1
  have hpos := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn0)
  have hs : (n.sqrt : ℝ) ≤ Real.sqrt n :=
    (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).2 (by exact_mod_cast Nat.sqrt_le' n)
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 248) (j := 8) (n := 24) (lo := 5) (hi := 6)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat] at hlog
  have hv := (Real.log_le_log (Nat.cast_pos.mpr hp0) (by exact_mod_cast hp)).trans hlog
  have ht : shiftedTriangle (5 / 2) x ≤ 1 :=
    max_le zero_le_one (sub_le_self _ (div_nonneg (abs_nonneg _) (by norm_num only)))
  have hd : (60000 : ℝ) ≤ n.sqrt * ((60000 / n.sqrt + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.lt_mul_div_succ 60000 (Nat.sqrt_pos.mpr hn0)).le
  have hb := hd.trans (mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg _))
  rw [← mul_div_assoc, higherWeight, ite_eq_left hn]
  apply (div_le_iff₀ hpos).2
  have ht' := mul_le_mul_of_nonneg_left ht (Real.log_natCast_nonneg p)
  dsimp only [n] at hb
  linarith only [ht', hv, hb]

/-- A higher power in the fixed window has base at most 248 and exponent
at most 23, by comparing its cube and the corresponding power of two. -/
private theorem higher_mem {p k : ℕ} (hp : 2 ≤ p) (hk : 3 ≤ k) (hn : p ^ k ≤ 15307657) :
    p ≤ 248 ∧ k ≤ 23 := by
  have h1 : 1 ≤ p := (by decide : 1 ≤ 2).trans hp
  have hcube := (pow_le_pow_right₀ h1 hk).trans hn
  have ht := (Nat.pow_le_pow_left hp k).trans hn
  constructor
  · apply le_of_not_gt
    intro h
    exact (by decide : ¬249 ^ 3 ≤ 15307657) ((Nat.pow_le_pow_left h 3).trans hcube)
  · apply le_of_not_gt
    intro h
    exact (by decide : ¬2 ^ 24 ≤ 15307657) ((Nat.pow_le_pow_right (by decide) h).trans ht)

/-- The total contribution of any set of distinct higher powers indexed by
base and exponent in the enclosing window is at most 333/200. -/
private theorem triangle_higher_bound_wide (s : Finset (ℕ × ℕ)) (x : ℕ × ℕ → ℝ)
    (hp : ∀ q ∈ s, 2 ≤ q.1) (hk : ∀ q ∈ s, 3 ≤ q.2)
    (hn : ∀ q ∈ s, 82369 < q.1 ^ q.2 ∧ q.1 ^ q.2 ≤ 15307657) :
    (∑ q ∈ s, Real.log q.1 * (shiftedTriangle (5 / 2) (x q) / Real.sqrt (q.1 ^ q.2 : ℕ))) ≤
      333 / 200 := by
  have hm (q : ℕ × ℕ) (hq : q ∈ s) := higher_mem (hp q hq) (hk q hq) (hn q hq).2
  have hw :=
    Finset.sum_le_sum
      (fun q hq =>
        higher_weight_le ((by decide : 0 < 2).trans_le (hp q hq)) (hm q hq).1 (hn q hq) (x q))
  apply hw.trans
  rw [← Finset.sum_div, ← Nat.cast_sum]
  have hsub : s ⊆ (Finset.Icc 2 248) ×ˢ (Finset.Icc 3 23) := by
    intro q hq
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨hp q hq, (hm q hq).1⟩, hk q hq, (hm q hq).2⟩
  have ha :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun q => higherWeight q.1 q.2)
      (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_product] at ha
  have hb : ((∑ q ∈ s, higherWeight q.1 q.2 : ℕ) : ℝ) ≤ 16650 := by
    exact_mod_cast ha.trans higher_total
  linarith only [hb]

/-- The total contribution of any set of distinct higher powers indexed by
base and exponent in the enclosing window is at most 17/10. -/
theorem triangle_higher_bound_300 (s : Finset (ℕ × ℕ)) (x : ℕ × ℕ → ℝ) (hp : ∀ q ∈ s, 2 ≤ q.1)
    (hk : ∀ q ∈ s, 3 ≤ q.2) (hn : ∀ q ∈ s, 82369 < q.1 ^ q.2 ∧ q.1 ^ q.2 ≤ 14062500) :
    (∑ q ∈ s, Real.log q.1 * (shiftedTriangle (5 / 2) (x q) / Real.sqrt (q.1 ^ q.2 : ℕ))) ≤
      17 / 10 := by
  exact
    (triangle_higher_bound_wide s x hp hk
          (fun q h => ⟨(hn q h).1, (hn q h).2.trans (by decide)⟩)).trans
      (by norm_num only)

/-- Restrict the higher-power bound to the section 86 integer window. -/
theorem triangle_higher_bound_576 (s : Finset (ℕ × ℕ)) (x : ℕ × ℕ → ℝ) (hp : ∀ q ∈ s, 2 ≤ q.1)
    (hk : ∀ q ∈ s, 3 ≤ q.2) (hn : ∀ q ∈ s, 82369 < q.1 ^ q.2 ∧ q.1 ^ q.2 ≤ 12960000) :
    (∑ q ∈ s, Real.log q.1 * (shiftedTriangle (5 / 2) (x q) / Real.sqrt (q.1 ^ q.2 : ℕ))) ≤
      17 / 10 := by
  exact triangle_higher_bound_300 s x hp hk (fun q h => ⟨(hn q h).1, (hn q h).2.trans (by decide)⟩)

/-- Through radius 300 the square sieve in the enclosing base interval costs at most 3.29. -/
private theorem triangle_square_sum_300 (s : Finset ℕ)
    (hs : s ⊆ (Finset.Ioc 287 3750).filter Nat.Prime) : ∑ p ∈ s, Real.log p / p ≤ 329 / 100 := by
  exact
    (triangle_square_sum_of_sieve s 3750 32900 (by decide) (by decide +kernel) hs).trans
      (by norm_num only)

/-- On the radii 287 through 300 radius interval, the prime base of every square in the
wide triangle belongs to the fixed range from 288 through 3750. -/
theorem triangle_square_base_300 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 300) {p : ℕ} (hp : p.Prime)
    (hlo : r ^ 2 < (p : ℝ) ^ 2) (hhi : (p : ℝ) ^ 2 ≤ Real.exp 5 * r ^ 2) :
    p ∈ (Finset.Ioc 287 3750).filter Nat.Prime := by
  have hr : 0 ≤ r := by linarith only [hl]
  have hsmall := lt_of_pow_lt_pow_left₀ 2 (Nat.cast_nonneg p) hlo
  have he : Real.exp 5 < (25 / 2 : ℝ) ^ 2 := by
    have h :=
      pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num only : (5 : ℕ) ≠ 0)
    rw [← Real.exp_natCast_mul] at h
    norm_num only [Nat.cast_ofNat, mul_one] at h
    exact h.trans (by norm_num only)
  have hb :=
    hhi.trans
      ((mul_le_mul_of_nonneg_right he.le (sq_nonneg r)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hu 2) (sq_nonneg _)))
  have hpu : (p : ℝ) ≤ 3750 := by
    apply le_of_not_gt
    intro hgt
    have hsq :=
      pow_lt_pow_left₀ hgt (by norm_num only : (0 : ℝ) ≤ 3750) (by norm_num only : (2 : ℕ) ≠ 0)
    linarith only [hsq, hb]
  exact
    Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨by exact_mod_cast hl.trans_lt hsmall, by exact_mod_cast hpu⟩, hp⟩

/-- The square part of the wide triangle is bounded by a fixed sum over
prime bases, uniformly in the radius and in the triangle coordinates. -/
theorem triangle_square_majorant_300 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 300) (s : Finset ℕ)
    (x : ℕ → ℝ) (hp : ∀ p ∈ s, p.Prime) (hlo : ∀ p ∈ s, r ^ 2 < (p : ℝ) ^ 2)
    (hhi : ∀ p ∈ s, (p : ℝ) ^ 2 ≤ Real.exp 5 * r ^ 2) :
    (∑ p ∈ s, Real.log p * (shiftedTriangle (5 / 2) (x p) / Real.sqrt ((p : ℝ) ^ 2))) ≤
      ∑ p ∈ (Finset.Ioc 287 3750).filter Nat.Prime, Real.log p / p := by
  apply (Finset.sum_le_sum (fun p _ => triangle_square_weight_le p (x p))).trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact fun p h => triangle_square_base_300 hl hu (hp p h) (hlo p h) (hhi p h)
  · exact fun p _ _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

/-- On radii 287 through 300 the prime-square contribution to the wide triangle is at
most 329/100, by the fixed reciprocal-prime certificate. -/
theorem triangle_square_bound_300 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 300) (s : Finset ℕ) (x : ℕ → ℝ)
    (hp : ∀ p ∈ s, p.Prime) (hlo : ∀ p ∈ s, r ^ 2 < (p : ℝ) ^ 2)
    (hhi : ∀ p ∈ s, (p : ℝ) ^ 2 ≤ Real.exp 5 * r ^ 2) :
    (∑ p ∈ s, Real.log p * (shiftedTriangle (5 / 2) (x p) / Real.sqrt ((p : ℝ) ^ 2))) ≤
      329 / 100 := by
  exact
    (triangle_square_majorant_300 hl hu s x hp hlo hhi).trans
      (triangle_square_sum_300 _ (fun _ h => h))

/-- For radii 287 through 300 every power in the real triangle window belongs to the
integer interval used by the higher-power certificate. -/
theorem triangle_power_window_300 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 300) {n : ℕ} (ha : r ^ 2 < n)
    (hb : (n : ℝ) ≤ Real.exp 5 * r ^ 2) : 82369 < n ∧ n ≤ 14062500 := by
  have hr : 0 ≤ r := by linarith only [hl]
  have he :=
    pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num only : (5 : ℕ) ≠ 0)
  rw [← Real.exp_natCast_mul] at he
  norm_num only [Nat.cast_ofNat, mul_one] at he
  have ht : Real.exp 5 ≤ (25 / 2 : ℝ) ^ 2 := he.le.trans (by norm_num only)
  constructor
  · exact_mod_cast
      (show (82369 : ℝ) < n from
        (by norm_num only : (82369 : ℝ) ≤ 287 ^ 2).trans_lt
          ((pow_le_pow_left₀ (by norm_num only) hl 2).trans_lt ha))
  · exact_mod_cast
      (show (n : ℝ) ≤ 14062500 from
        hb.trans
          ((mul_le_mul ht (pow_le_pow_left₀ hr hu 2) (sq_nonneg _) (sq_nonneg _)).trans
            (by norm_num only)))

/-- For section 86 every power in the real triangle window belongs to the
integer interval used by the higher-power certificate. -/
theorem triangle_power_window_576 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 288) {n : ℕ} (ha : r ^ 2 < n)
    (hb : (n : ℝ) ≤ Real.exp 5 * r ^ 2) : 82369 < n ∧ n ≤ 12960000 := by
  have hr : 0 ≤ r := by linarith only [hl]
  have he :=
    pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num only : (5 : ℕ) ≠ 0)
  rw [← Real.exp_natCast_mul] at he
  norm_num only [Nat.cast_ofNat, mul_one] at he
  have ht : Real.exp 5 ≤ (25 / 2 : ℝ) ^ 2 := he.le.trans (by norm_num only)
  constructor
  · exact_mod_cast
      (show (82369 : ℝ) < n from
        (by norm_num only : (82369 : ℝ) ≤ 287 ^ 2).trans_lt
          ((pow_le_pow_left₀ (by norm_num only) hl 2).trans_lt ha))
  · exact_mod_cast
      (show (n : ℝ) ≤ 12960000 from
        hb.trans
          ((mul_le_mul ht (pow_le_pow_left₀ hr hu 2) (sq_nonneg _) (sq_nonneg _)).trans
            (by norm_num only)))

/-- Throughout radii 287 through 300 the sum of the square and higher-power contributions
is strictly below five for any sets of eligible bases and exponents. -/
theorem triangle_nonprime_bound_300 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 300) (s : Finset ℕ)
    (u : Finset (ℕ × ℕ)) (x : ℕ → ℝ) (y : ℕ × ℕ → ℝ) (hp : ∀ p ∈ s, p.Prime)
    (ha : ∀ p ∈ s, r ^ 2 < (p : ℝ) ^ 2) (hb : ∀ p ∈ s, (p : ℝ) ^ 2 ≤ Real.exp 5 * r ^ 2)
    (hq : ∀ q ∈ u, 2 ≤ q.1) (hk : ∀ q ∈ u, 3 ≤ q.2) (hc : ∀ q ∈ u, r ^ 2 < (q.1 ^ q.2 : ℕ))
    (hd : ∀ q ∈ u, ((q.1 ^ q.2 : ℕ) : ℝ) ≤ Real.exp 5 * r ^ 2) :
    (∑ p ∈ s, Real.log p * (shiftedTriangle (5 / 2) (x p) / Real.sqrt ((p : ℝ) ^ 2))) +
        (∑ q ∈ u, Real.log q.1 * (shiftedTriangle (5 / 2) (y q) / Real.sqrt (q.1 ^ q.2 : ℕ))) <
      5 := by
  have h2 := triangle_square_bound_300 hl hu s x hp ha hb
  have h3 :=
    triangle_higher_bound_300 u y hq hk
      (fun q h => triangle_power_window_300 hl hu (hc q h) (hd q h))
  linarith only [h2, h3]

/-- Restrict the prime-power bound through radius 300 to section 86. -/
theorem triangle_nonprime_bound_576 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 288) (s : Finset ℕ)
    (u : Finset (ℕ × ℕ)) (x : ℕ → ℝ) (y : ℕ × ℕ → ℝ) (hp : ∀ p ∈ s, p.Prime)
    (ha : ∀ p ∈ s, r ^ 2 < (p : ℝ) ^ 2) (hb : ∀ p ∈ s, (p : ℝ) ^ 2 ≤ Real.exp 5 * r ^ 2)
    (hq : ∀ q ∈ u, 2 ≤ q.1) (hk : ∀ q ∈ u, 3 ≤ q.2) (hc : ∀ q ∈ u, r ^ 2 < (q.1 ^ q.2 : ℕ))
    (hd : ∀ q ∈ u, ((q.1 ^ q.2 : ℕ) : ℝ) ≤ Real.exp 5 * r ^ 2) :
    (∑ p ∈ s, Real.log p * (shiftedTriangle (5 / 2) (x p) / Real.sqrt ((p : ℝ) ^ 2))) +
        (∑ q ∈ u, Real.log q.1 * (shiftedTriangle (5 / 2) (y q) / Real.sqrt (q.1 ^ q.2 : ℕ))) <
      5 := by
  exact triangle_nonprime_bound_300 hl (hu.trans (by norm_num only)) s u x y hp ha hb hq hk hc hd

/-- Every nonprime index with nonzero Mangoldt coefficient is a prime power
with exponent at least two. Its coefficient is the logarithm of the prime base. -/
private theorem nonprime_power_rep {n : ℕ} (hn : ¬n.Prime)
    (h : ArithmeticFunction.vonMangoldt n ≠ 0) :
    ∃ q : ℕ × ℕ,
      q.1.Prime ∧ 2 ≤ q.2 ∧ q.1 ^ q.2 = n ∧ ArithmeticFunction.vonMangoldt n = Real.log q.1 := by
  obtain ⟨p, k, hp, hk, rfl⟩ :=
    (isPrimePow_nat_iff n).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h)
  have hk1 : k ≠ 1 := fun he => hn (by simpa only [he, pow_one] using hp)
  exact
    ⟨(p, k), hp, Nat.succ_le_of_lt (lt_of_le_of_ne hk (Ne.symm hk1)), rfl,
      (ArithmeticFunction.vonMangoldt_apply_pow hk.ne').trans
        (ArithmeticFunction.vonMangoldt_apply_prime hp)⟩

/-- Reindex the nonzero coefficients of a finite nonprime sum by prime bases
and exponents. Taking powers recovers each original index and gives injectivity. -/
private theorem nonprime_mangoldt_reindex (s : Finset ℕ) (hn : ∀ n ∈ s, ¬n.Prime) (w : ℕ → ℝ) :
    ∃ u : Finset (ℕ × ℕ),
      (∀ q ∈ u, q.1.Prime ∧ 2 ≤ q.2 ∧ q.1 ^ q.2 ∈ s) ∧
        (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * w n) =
          ∑ q ∈ u, Real.log q.1 * w (q.1 ^ q.2) := by
  classical
  let t := s.filter (fun n => ArithmeticFunction.vonMangoldt n ≠ 0)
  have hex (n : ℕ) (h : n ∈ t) :=
    nonprime_power_rep (hn n (Finset.mem_filter.mp h).1) (Finset.mem_filter.mp h).2
  let f (n : ℕ) := if h : n ∈ t then (hex n h).choose else (0, 0)
  have hf (n : ℕ) (h : n ∈ t) :
    (f n).1.Prime ∧
      2 ≤ (f n).2 ∧
      (f n).1 ^ (f n).2 = n ∧ ArithmeticFunction.vonMangoldt n = Real.log (f n).1 := by
    simpa only [f, dite_eq_left h] using (hex n h).choose_spec
  refine ⟨t.image f, ?_, ?_⟩
  · intro q hq
    obtain ⟨n, h, rfl⟩ := Finset.mem_image.mp hq
    exact
      ⟨(hf n h).1, (hf n h).2.1, by
        rw [(hf n h).2.2.1]; exact (Finset.mem_filter.mp h).1⟩
  · rw [Finset.sum_image
        (fun i hi j hj he =>
          (hf i hi).2.2.1.symm.trans
            ((congrArg (fun q : ℕ × ℕ => q.1 ^ q.2) he).trans (hf j hj).2.2.1))]
    have he :
      (∑ n ∈ t, ArithmeticFunction.vonMangoldt n * w n) =
        ∑ n ∈ s, ArithmeticFunction.vonMangoldt n * w n :=
      Finset.sum_filter_of_ne (fun _ _ h => left_ne_zero_of_mul h)
    rw [← he]
    exact Finset.sum_congr rfl (fun n h => by rw [(hf n h).2.2.1, (hf n h).2.2.2])

/-- Under the radii 287 through 300 radius limits the nonprime part of any finite
triangle-weighted Mangoldt sum supported in the window is strictly below five. -/
theorem triangle_mangoldt_nonprime_300 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 300) (s : Finset ℕ)
    (hn : ∀ n ∈ s, ¬n.Prime) (x : ℕ → ℝ) (ha : ∀ n ∈ s, r ^ 2 < n)
    (hb : ∀ n ∈ s, (n : ℝ) ≤ Real.exp 5 * r ^ 2) :
    (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * (shiftedTriangle (5 / 2) (x n) / Real.sqrt n)) <
      5 := by
  obtain ⟨u, hmem, he⟩ :=
    nonprime_mangoldt_reindex s hn (fun n => shiftedTriangle (5 / 2) (x n) / Real.sqrt n)
  let t := u.filter (fun q => q.2 = 2)
  let z := u.filter (fun q => q.2 ≠ 2)
  have ht (q : ℕ × ℕ) (h : q ∈ t) := Finset.mem_filter.mp h
  have hz (q : ℕ × ℕ) (h : q ∈ z) := Finset.mem_filter.mp h
  have hs (p : ℕ) (h : p ∈ t.image Prod.fst) : p.Prime ∧ p ^ 2 ∈ s := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h
    have hh := hmem q (ht q hq).1
    exact ⟨hh.1, (ht q hq).2 ▸ hh.2.2⟩
  have hbound :=
    triangle_nonprime_bound_300 hl hu (t.image Prod.fst) z (fun p => x (p ^ 2))
      (fun q => x (q.1 ^ q.2)) (fun p h => (hs p h).1)
      (fun p h => by exact_mod_cast ha _ (hs p h).2) (fun p h => by exact_mod_cast hb _ (hs p h).2)
      (fun q h => (hmem q (hz q h).1).1.two_le)
      (fun q h => Nat.succ_le_of_lt (lt_of_le_of_ne (hmem q (hz q h).1).2.1 (Ne.symm (hz q h).2)))
      (fun q h => ha _ (hmem q (hz q h).1).2.2) (fun q h => hb _ (hmem q (hz q h).1).2.2)
  rw [Finset.sum_image
      (fun i hi j hj hij => Prod.ext hij ((ht i hi).2.trans (ht j hj).2.symm))] at hbound
  rw [he, ← Finset.sum_filter_add_sum_filter_not u (fun q => q.2 = 2)]
  apply lt_of_eq_of_lt _ hbound
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  simp only [(ht q hq).2, Nat.cast_pow]

/-- Restrict the prime-power bound through radius 300 to section 86. -/
theorem triangle_mangoldt_nonprime_576 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 288) (s : Finset ℕ)
    (hn : ∀ n ∈ s, ¬n.Prime) (x : ℕ → ℝ) (ha : ∀ n ∈ s, r ^ 2 < n)
    (hb : ∀ n ∈ s, (n : ℝ) ≤ Real.exp 5 * r ^ 2) :
    (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * (shiftedTriangle (5 / 2) (x n) / Real.sqrt n)) <
      5 := by
  exact triangle_mangoldt_nonprime_300 hl (hu.trans (by norm_num only)) s hn x ha hb

/-- On the radii 287 through 316 radius interval, the prime base of every square in the
wide triangle belongs to the fixed range from 288 through 3913. -/
theorem triangle_square_base_316 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 316) {p : ℕ} (hp : p.Prime)
    (hlo : r ^ 2 < (p : ℝ) ^ 2) (hhi : (p : ℝ) ^ 2 ≤ Real.exp 5 * r ^ 2) :
    p ∈ (Finset.Ioc 287 3913).filter Nat.Prime := by
  have hr : 0 ≤ r := by linarith only [hl]
  have hsmall := lt_of_pow_lt_pow_left₀ 2 (Nat.cast_nonneg p) hlo
  have he : Real.exp 5 < (3913 / 316 : ℝ) ^ 2 := by
    have hExp : Real.exp 1 < (68 / 25 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num only)
    have h := pow_lt_pow_left₀ hExp (Real.exp_pos 1).le (by norm_num only : (5 : ℕ) ≠ 0)
    rw [← Real.exp_natCast_mul] at h
    norm_num only [Nat.cast_ofNat, mul_one] at h
    exact h.trans (by norm_num only)
  have hb :=
    hhi.trans
      ((mul_le_mul_of_nonneg_right he.le (sq_nonneg r)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hu 2) (sq_nonneg _)))
  have hpu : (p : ℝ) ≤ 3913 := by
    apply le_of_not_gt
    intro hgt
    have hsq :=
      pow_lt_pow_left₀ hgt (by norm_num only : (0 : ℝ) ≤ 3913) (by norm_num only : (2 : ℕ) ≠ 0)
    linarith only [hsq, hb]
  exact
    Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨by exact_mod_cast hl.trans_lt hsmall, by exact_mod_cast hpu⟩, hp⟩

/-- The square part of the wide triangle is bounded by a fixed sum over
prime bases, uniformly in the radius and in the triangle coordinates. -/
theorem triangle_square_majorant_316 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 316) (s : Finset ℕ)
    (x : ℕ → ℝ) (hp : ∀ p ∈ s, p.Prime) (hlo : ∀ p ∈ s, r ^ 2 < (p : ℝ) ^ 2)
    (hhi : ∀ p ∈ s, (p : ℝ) ^ 2 ≤ Real.exp 5 * r ^ 2) :
    (∑ p ∈ s, Real.log p * (shiftedTriangle (5 / 2) (x p) / Real.sqrt ((p : ℝ) ^ 2))) ≤
      ∑ p ∈ (Finset.Ioc 287 3913).filter Nat.Prime, Real.log p / p := by
  apply (Finset.sum_le_sum (fun p _ => triangle_square_weight_le p (x p))).trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact fun p h => triangle_square_base_316 hl hu (hp p h) (hlo p h) (hhi p h)
  · exact fun p _ _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

/-- For radii 287 through 316 every power in the real triangle window belongs to the
integer interval used by the higher-power certificate. -/
theorem triangle_power_window_316 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 316) {n : ℕ} (ha : r ^ 2 < n)
    (hb : (n : ℝ) ≤ Real.exp 5 * r ^ 2) : 82369 < n ∧ n ≤ 15307657 := by
  have hr : 0 ≤ r := by linarith only [hl]
  have hExp : Real.exp 1 < (68 / 25 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num only)
  have he := pow_lt_pow_left₀ hExp (Real.exp_pos 1).le (by norm_num only : (5 : ℕ) ≠ 0)
  rw [← Real.exp_natCast_mul] at he
  norm_num only [Nat.cast_ofNat, mul_one] at he
  have ht : Real.exp 5 ≤ (15307657 / 316 ^ 2 : ℝ) := he.le.trans (by norm_num only)
  constructor
  · exact_mod_cast
      (show (82369 : ℝ) < n from
        (by norm_num only : (82369 : ℝ) ≤ 287 ^ 2).trans_lt
          ((pow_le_pow_left₀ (by norm_num only) hl 2).trans_lt ha))
  · exact_mod_cast
      (show (n : ℝ) ≤ 15307657 from
        hb.trans
          ((mul_le_mul ht (pow_le_pow_left₀ hr hu 2) (sq_nonneg _) (by norm_num only)).trans
            (by norm_num only)))

/-- Throughout radii 287 through 316 the sum of the square and higher-power contributions
is strictly below five for any sets of eligible bases and exponents. -/
theorem triangle_nonprime_bound_316 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 316) (s : Finset ℕ)
    (u : Finset (ℕ × ℕ)) (x : ℕ → ℝ) (y : ℕ × ℕ → ℝ) (hp : ∀ p ∈ s, p.Prime)
    (ha : ∀ p ∈ s, r ^ 2 < (p : ℝ) ^ 2) (hb : ∀ p ∈ s, (p : ℝ) ^ 2 ≤ Real.exp 5 * r ^ 2)
    (hq : ∀ q ∈ u, 2 ≤ q.1) (hk : ∀ q ∈ u, 3 ≤ q.2) (hc : ∀ q ∈ u, r ^ 2 < (q.1 ^ q.2 : ℕ))
    (hd : ∀ q ∈ u, ((q.1 ^ q.2 : ℕ) : ℝ) ≤ Real.exp 5 * r ^ 2) :
    (∑ p ∈ s, Real.log p * (shiftedTriangle (5 / 2) (x p) / Real.sqrt ((p : ℝ) ^ 2))) +
        (∑ q ∈ u, Real.log q.1 * (shiftedTriangle (5 / 2) (y q) / Real.sqrt (q.1 ^ q.2 : ℕ))) <
      5 := by
  have h2 :=
    (triangle_square_majorant_316 hl hu s x hp ha hb).trans
      (triangle_square_sum_of_sieve _ 3913 33300 le_rfl (by decide +kernel) (fun _ h => h))
  have h3 :=
    triangle_higher_bound_wide u y hq hk
      (fun q h => triangle_power_window_316 hl hu (hc q h) (hd q h))
  linarith only [h2, h3]

/-- Under the radii 287 through 316 radius limits the nonprime part of any finite
triangle-weighted Mangoldt sum supported in the window is strictly below five. -/
theorem triangle_mangoldt_nonprime_316 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 316) (s : Finset ℕ)
    (hn : ∀ n ∈ s, ¬n.Prime) (x : ℕ → ℝ) (ha : ∀ n ∈ s, r ^ 2 < n)
    (hb : ∀ n ∈ s, (n : ℝ) ≤ Real.exp 5 * r ^ 2) :
    (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * (shiftedTriangle (5 / 2) (x n) / Real.sqrt n)) <
      5 := by
  obtain ⟨u, hmem, he⟩ :=
    nonprime_mangoldt_reindex s hn (fun n => shiftedTriangle (5 / 2) (x n) / Real.sqrt n)
  let t := u.filter (fun q => q.2 = 2)
  let z := u.filter (fun q => q.2 ≠ 2)
  have ht (q : ℕ × ℕ) (h : q ∈ t) := Finset.mem_filter.mp h
  have hz (q : ℕ × ℕ) (h : q ∈ z) := Finset.mem_filter.mp h
  have hs (p : ℕ) (h : p ∈ t.image Prod.fst) : p.Prime ∧ p ^ 2 ∈ s := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h
    have hh := hmem q (ht q hq).1
    exact ⟨hh.1, (ht q hq).2 ▸ hh.2.2⟩
  have hbound :=
    triangle_nonprime_bound_316 hl hu (t.image Prod.fst) z (fun p => x (p ^ 2))
      (fun q => x (q.1 ^ q.2)) (fun p h => (hs p h).1)
      (fun p h => by exact_mod_cast ha _ (hs p h).2) (fun p h => by exact_mod_cast hb _ (hs p h).2)
      (fun q h => (hmem q (hz q h).1).1.two_le)
      (fun q h => Nat.succ_le_of_lt (lt_of_le_of_ne (hmem q (hz q h).1).2.1 (Ne.symm (hz q h).2)))
      (fun q h => ha _ (hmem q (hz q h).1).2.2) (fun q h => hb _ (hmem q (hz q h).1).2.2)
  rw [Finset.sum_image
      (fun i hi j hj hij => Prod.ext hij ((ht i hi).2.trans (ht j hj).2.symm))] at hbound
  rw [he, ← Finset.sum_filter_add_sum_filter_not u (fun q => q.2 = 2)]
  apply lt_of_eq_of_lt _ hbound
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  simp only [(ht q hq).2, Nat.cast_pow]

/-- On the radii 287 through 313 radius interval, the prime base of every square in the
wide triangle belongs to the fixed range from 288 through 3913. -/
theorem triangle_square_base_313 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 313) {p : ℕ} (hp : p.Prime)
    (hlo : r ^ 2 < (p : ℝ) ^ 2) (hhi : (p : ℝ) ^ 2 ≤ Real.exp 5 * r ^ 2) :
    p ∈ (Finset.Ioc 287 3913).filter Nat.Prime := by
  exact triangle_square_base_316 hl (hu.trans (by norm_num only)) hp hlo hhi

/-- The square part of the wide triangle is bounded by a fixed sum over
prime bases, uniformly in the radius and in the triangle coordinates. -/
theorem triangle_square_majorant_313 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 313) (s : Finset ℕ)
    (x : ℕ → ℝ) (hp : ∀ p ∈ s, p.Prime) (hlo : ∀ p ∈ s, r ^ 2 < (p : ℝ) ^ 2)
    (hhi : ∀ p ∈ s, (p : ℝ) ^ 2 ≤ Real.exp 5 * r ^ 2) :
    (∑ p ∈ s, Real.log p * (shiftedTriangle (5 / 2) (x p) / Real.sqrt ((p : ℝ) ^ 2))) ≤
      ∑ p ∈ (Finset.Ioc 287 3913).filter Nat.Prime, Real.log p / p := by
  exact triangle_square_majorant_316 hl (hu.trans (by norm_num only)) s x hp hlo hhi

/-- For radii 287 through 313 every power in the real triangle window belongs to the
integer interval used by the higher-power certificate. -/
theorem triangle_power_window_313 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 313) {n : ℕ} (ha : r ^ 2 < n)
    (hb : (n : ℝ) ≤ Real.exp 5 * r ^ 2) : 82369 < n ∧ n ≤ 15307657 := by
  exact triangle_power_window_316 hl (hu.trans (by norm_num only)) ha hb

/-- Throughout radii 287 through 313 the sum of the square and higher-power contributions
is strictly below five for any sets of eligible bases and exponents. -/
theorem triangle_nonprime_bound_313 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 313) (s : Finset ℕ)
    (u : Finset (ℕ × ℕ)) (x : ℕ → ℝ) (y : ℕ × ℕ → ℝ) (hp : ∀ p ∈ s, p.Prime)
    (ha : ∀ p ∈ s, r ^ 2 < (p : ℝ) ^ 2) (hb : ∀ p ∈ s, (p : ℝ) ^ 2 ≤ Real.exp 5 * r ^ 2)
    (hq : ∀ q ∈ u, 2 ≤ q.1) (hk : ∀ q ∈ u, 3 ≤ q.2) (hc : ∀ q ∈ u, r ^ 2 < (q.1 ^ q.2 : ℕ))
    (hd : ∀ q ∈ u, ((q.1 ^ q.2 : ℕ) : ℝ) ≤ Real.exp 5 * r ^ 2) :
    (∑ p ∈ s, Real.log p * (shiftedTriangle (5 / 2) (x p) / Real.sqrt ((p : ℝ) ^ 2))) +
        (∑ q ∈ u, Real.log q.1 * (shiftedTriangle (5 / 2) (y q) / Real.sqrt (q.1 ^ q.2 : ℕ))) <
      5 := by
  exact triangle_nonprime_bound_316 hl (hu.trans (by norm_num only)) s u x y hp ha hb hq hk hc hd

/-- Under the radii 287 through 313 radius limits the nonprime part of any finite
triangle-weighted Mangoldt sum supported in the window is strictly below five. -/
theorem triangle_mangoldt_nonprime_313 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 313) (s : Finset ℕ)
    (hn : ∀ n ∈ s, ¬n.Prime) (x : ℕ → ℝ) (ha : ∀ n ∈ s, r ^ 2 < n)
    (hb : ∀ n ∈ s, (n : ℝ) ≤ Real.exp 5 * r ^ 2) :
    (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * (shiftedTriangle (5 / 2) (x n) / Real.sqrt n)) <
      5 := by
  exact triangle_mangoldt_nonprime_316 hl (hu.trans (by norm_num only)) s hn x ha hb

/-- The upper edge of the translated window through radius 322 lies
below the integer ceiling used for the extra power check. -/
private theorem triangle_window_ceiling_322 {r : ℝ} (hr : r ∈ Set.Icc 316 322) :
    Real.exp 5 * r ^ 2 ≤ 15400000 := by
  have h₁ : Real.exp 1 ≤ (27183 / 10000 : ℝ) := Real.exp_one_lt_d9.le.trans (by norm_num only)
  have h₂ := pow_le_pow_left₀ (Real.exp_pos 1).le h₁ 5
  rw [← Real.exp_natCast_mul] at h₂
  norm_num only [Nat.cast_ofNat, mul_one] at h₂
  have hR := pow_le_pow_left₀ (by linarith only [hr.1] : 0 ≤ r) hr.2 2
  exact (mul_le_mul h₂ hR (sq_nonneg r) (by norm_num only)).trans (by norm_num only)

/-- No higher power reaches the extra strip between the old certificate
ceiling and the new window ceiling. Check the adjacent integer bases for
each exponent that can occur. -/
private theorem triangle_higher_ceiling_322 {p k : ℕ} (hp : 2 ≤ p) (hk : 3 ≤ k)
    (h : p ^ k ≤ 15400000) : p ^ k ≤ 15307657 := by
  have hK : k ≤ 23 := by
    apply le_of_not_gt
    intro hgt
    have h₁ := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.succ_le_of_lt hgt)
    have h₂ := Nat.pow_le_pow_left hp k
    exact (by decide : ¬2 ^ 24 ≤ 15400000) (h₁.trans (h₂.trans h))
  let B : Array ℕ := #[248, 62, 27, 15, 10, 7, 6, 5, 4, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2]
  have hcheck :
    ∀ j ∈ Finset.Icc 3 23, B[j - 3]! ^ j ≤ 15307657 ∧ 15400000 < (B[j - 3]! + 1) ^ j := by
    decide +kernel
  obtain ⟨hb, hnext⟩ := hcheck k (Finset.mem_Icc.mpr ⟨hk, hK⟩)
  have hpb : p ≤ B[k - 3]! :=
    le_of_not_gt
      (fun hgt ↦ (not_le_of_gt hnext) ((Nat.pow_le_pow_left (Nat.succ_le_of_lt hgt) k).trans h))
  exact (Nat.pow_le_pow_left hpb k).trans hb

/-- Extend the square certificate by the eleven possible integer bases
above 3913. Bounding all eleven, including composites, costs less than 0.03. -/
private theorem triangle_square_sum_322 (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime)
    (hl : ∀ p ∈ s, 287 < p) (hu : ∀ p ∈ s, p ≤ 3924) : (∑ p ∈ s, Real.log p / (p : ℝ)) ≤ 3.36 := by
  let t := s.filter (fun p ↦ p ≤ 3913)
  let u := s.filter (fun p ↦ ¬p ≤ 3913)
  have ht : (∑ p ∈ t, Real.log p / (p : ℝ)) ≤ 3.33 :=
    (triangle_square_sum_of_sieve t 3913 33300 le_rfl (by decide +kernel)
          (fun p h ↦
            Finset.mem_filter.mpr
              ⟨Finset.mem_Ioc.mpr ⟨hl p (Finset.mem_filter.mp h).1, (Finset.mem_filter.mp h).2⟩,
                hp p (Finset.mem_filter.mp h).1⟩)).trans
      (by norm_num only [Nat.cast_ofNat])
  have hsub : u ⊆ Finset.Ioc 3913 3924 := fun p h ↦
    Finset.mem_Ioc.mpr
      ⟨Nat.lt_of_not_ge (Finset.mem_filter.mp h).2, hu p (Finset.mem_filter.mp h).1⟩
  have hlb :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 3924 12 24 8 9 = true by decide +kernel)).2
  norm_num only [Rat.cast_ofNat] at hlb
  have hU : (∑ p ∈ u, Real.log p / (p : ℝ)) ≤ (11 : ℝ) * (9 / 3913) := by
    have h :=
      Finset.sum_le_sum (s := u)
        (fun p h ↦ by
          obtain ⟨hl', hu'⟩ := Finset.mem_Ioc.mp (hsub h)
          have hpos : 0 < (p : ℝ) := Nat.cast_pos.mpr ((by decide : 0 ≤ 3913).trans_lt hl')
          have hlog := (Real.log_le_log hpos (Nat.cast_le.mpr hu')).trans hlb
          exact
            (div_le_div_of_nonneg_right hlog hpos.le).trans
              (div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 9)
                (by norm_num only : (0 : ℝ) < 3913) (Nat.cast_le.mpr hl'.le)))
    rw [Finset.sum_const, nsmul_eq_mul] at h
    have hc : u.card ≤ 11 := (Finset.card_le_card hsub).trans (by decide)
    exact h.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (by norm_num only))
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not s (fun p ↦ p ≤ 3913) (fun p ↦ Real.log p / (p : ℝ))
  change (∑ p ∈ t, Real.log p / (p : ℝ)) + (∑ p ∈ u, Real.log p / (p : ℝ)) = _ at hsplit
  linarith only [hsplit, ht, hU]

private theorem triangle_nonprime_bound_322 {r : ℝ} (hr : r ∈ Set.Icc 316 322) (s : Finset ℕ)
    (u : Finset (ℕ × ℕ)) (x : ℕ → ℝ) (y : ℕ × ℕ → ℝ) (hp : ∀ p ∈ s, p.Prime)
    (ha : ∀ p ∈ s, r ^ 2 < (p : ℝ) ^ 2) (hb : ∀ p ∈ s, (p : ℝ) ^ 2 ≤ Real.exp 5 * r ^ 2)
    (hq : ∀ q ∈ u, 2 ≤ q.1) (hk : ∀ q ∈ u, 3 ≤ q.2) (hc : ∀ q ∈ u, r ^ 2 < (q.1 ^ q.2 : ℕ))
    (hd : ∀ q ∈ u, ((q.1 ^ q.2 : ℕ) : ℝ) ≤ Real.exp 5 * r ^ 2) :
    (∑ p ∈ s, Real.log p * (shiftedTriangle (5 / 2) (x p) / Real.sqrt ((p : ℝ) ^ 2))) +
        (∑ q ∈ u, Real.log q.1 * (shiftedTriangle (5 / 2) (y q) / Real.sqrt (q.1 ^ q.2 : ℕ))) <
      5.1 := by
  have hX := triangle_window_ceiling_322 hr
  have hlo : ∀ p ∈ s, 287 < p := fun p h ↦ by
    have hh := lt_of_pow_lt_pow_left₀ 2 (Nat.cast_nonneg p) (ha p h)
    exact_mod_cast ((by linarith only [hr.1] : (287 : ℝ) ≤ r).trans_lt hh)
  have hhi : ∀ p ∈ s, p ≤ 3924 := fun p h ↦ by
    apply le_of_not_gt
    intro hgt
    have hh : (3925 : ℝ) ≤ p := by exact_mod_cast Nat.succ_le_of_lt hgt
    have hu := pow_le_pow_left₀ (by norm_num only) hh 2
    linarith only [hu, (hb p h).trans hX]
  have h₂ :=
    (Finset.sum_le_sum (fun p _ ↦ triangle_square_weight_le p (x p))).trans
      (triangle_square_sum_322 s hp hlo hhi)
  have h₃ :=
    triangle_higher_bound_wide u y hq hk
      (fun q h ↦ by
        have hqlo : (82369 : ℝ) < (q.1 ^ q.2 : ℕ) :=
          ((by norm_num only : (82369 : ℝ) ≤ 316 ^ 2).trans
                (pow_le_pow_left₀ (by norm_num only) hr.1 2)).trans_lt
            (hc q h)
        exact
          ⟨by exact_mod_cast hqlo,
            triangle_higher_ceiling_322 (hq q h) (hk q h) (by exact_mod_cast (hd q h).trans hX)⟩)
  linarith only [h₂, h₃]

/-- For radii 316 through 322 the nonprime part of any finite
triangle-weighted Mangoldt sum supported in the window is strictly below 5.1. -/
theorem triangle_mangoldt_nonprime_322 {r : ℝ} (hr : r ∈ Set.Icc 316 322) (s : Finset ℕ)
    (hn : ∀ n ∈ s, ¬n.Prime) (x : ℕ → ℝ) (ha : ∀ n ∈ s, r ^ 2 < n)
    (hb : ∀ n ∈ s, (n : ℝ) ≤ Real.exp 5 * r ^ 2) :
    (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * (shiftedTriangle (5 / 2) (x n) / Real.sqrt n)) <
      5.1 := by
  obtain ⟨u, hmem, he⟩ :=
    nonprime_mangoldt_reindex s hn (fun n ↦ shiftedTriangle (5 / 2) (x n) / Real.sqrt n)
  let t := u.filter (fun q ↦ q.2 = 2)
  let z := u.filter (fun q ↦ q.2 ≠ 2)
  have ht (q : ℕ × ℕ) (h : q ∈ t) := Finset.mem_filter.mp h
  have hz (q : ℕ × ℕ) (h : q ∈ z) := Finset.mem_filter.mp h
  have hs (p : ℕ) (h : p ∈ t.image Prod.fst) : p.Prime ∧ p ^ 2 ∈ s := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h
    have hh := hmem q (ht q hq).1
    exact ⟨hh.1, (ht q hq).2 ▸ hh.2.2⟩
  have hbound :=
    triangle_nonprime_bound_322 hr (t.image Prod.fst) z (fun p ↦ x (p ^ 2)) (fun q ↦ x (q.1 ^ q.2))
      (fun p h ↦ (hs p h).1) (fun p h ↦ by exact_mod_cast ha _ (hs p h).2)
      (fun p h ↦ by exact_mod_cast hb _ (hs p h).2) (fun q h ↦ (hmem q (hz q h).1).1.two_le)
      (fun q h ↦ Nat.succ_le_of_lt (lt_of_le_of_ne (hmem q (hz q h).1).2.1 (Ne.symm (hz q h).2)))
      (fun q h ↦ ha _ (hmem q (hz q h).1).2.2) (fun q h ↦ hb _ (hmem q (hz q h).1).2.2)
  rw [Finset.sum_image
      (fun i hi j hj hij ↦ Prod.ext hij ((ht i hi).2.trans (ht j hj).2.symm))] at hbound
  rw [he, ← Finset.sum_filter_add_sum_filter_not u (fun q ↦ q.2 = 2)]
  apply lt_of_eq_of_lt _ hbound
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  simp only [(ht q hq).2, Nat.cast_pow]

end PseudoPrime.PrimeTestBounds.MillerRabin
