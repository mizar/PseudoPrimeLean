/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterKernel656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterOdd574
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSquare570
public import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.Analysis.ExponentialFixedPointBounds

/-! # Support of the fixed prime powers in section 132 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Select squared prime powers by their roots and add the prescribed odd
powers. The left block uses roots in (325,1196] and the right block uses
roots in (328,1207]. The right block also includes 113 cubed. -/
def fixedPowers656 (right : Bool) : Finset ℕ :=
  let roots := if right then Finset.Ioc 328 1207 else Finset.Ioc 325 1196
  let cubes := ({53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109} : Finset ℕ)
  let oddPowers : Finset ℕ :=
    cubes.image (fun p ↦ p ^ 3) ∪ {11 ^ 5, 13 ^ 5, 17 ^ 5, 7 ^ 7, 3 ^ 11, 2 ^ 17, 2 ^ 19}
  ((roots.filter IsPrimePow).image (fun t ↦ t ^ 2)) ∪
    (if right then insert (113 ^ 3) oddPowers else oddPowers)

/-- Every selected index is a proper power of a prime below the left
cutoff, so its arithmetic credit can be recovered from passing prime bases. -/
theorem fixed_power_prime_base_656 (right : Bool) {m : ℕ} (hm : m ∈ fixedPowers656 right) :
    ∃ p k : ℕ, p.Prime ∧ p ≤ 322 ^ 2 ∧ 2 ≤ k ∧ m = p ^ k := by
  unfold fixedPowers656 at hm
  rcases Finset.mem_union.mp hm with he | ho
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hb, ht⟩ := Finset.mem_filter.mp ht
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff t).mp ht
    have hb' : p ^ k ≤ 1207 := by
      cases right
      · exact (Finset.mem_Ioc.mp hb).2.trans (by decide)
      · exact (Finset.mem_Ioc.mp hb).2
    have hp' : p ≤ p ^ k := le_self_pow₀ hp.one_lt.le hk.ne'
    exact
      ⟨p, k * 2, hp, hp'.trans (hb'.trans (by decide)), Nat.mul_le_mul_right 2 hk,
        (pow_mul p k 2).symm⟩
  · have h :
      ∀
        n ∈
          ({53 ^ 3, 59 ^ 3, 61 ^ 3, 67 ^ 3, 71 ^ 3, 73 ^ 3, 79 ^ 3,
        83 ^ 3, 89 ^ 3, 97 ^ 3, 101 ^ 3, 103 ^ 3, 107 ^ 3, 109 ^ 3, 113 ^ 3,
         11 ^ 5, 13 ^ 5, 17 ^ 5, 7 ^ 7, 3 ^ 11, 2 ^ 17, 2 ^ 19} :
            Finset ℕ),
        ∃
          p ∈
            ({2, 3, 7, 11, 13, 17, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
          101, 103, 107, 109, 113} :
              Finset ℕ),
          ∃ k ∈ ({3, 5, 7, 11, 17, 19} : Finset ℕ), p.Prime ∧ p ≤ 322 ^ 2 ∧ 2 ≤ k ∧ n = p ^ k := by
      decide +kernel
    have hm' :
      m ∈
        ({53 ^ 3, 59 ^ 3, 61 ^ 3, 67 ^ 3, 71 ^ 3, 73 ^ 3, 79 ^ 3,
        83 ^ 3, 89 ^ 3, 97 ^ 3, 101 ^ 3, 103 ^ 3, 107 ^ 3, 109 ^ 3, 113 ^ 3,
        11 ^ 5, 13 ^ 5, 17 ^ 5, 7 ^ 7, 3 ^ 11, 2 ^ 17, 2 ^ 19} :
          Finset ℕ) := by
      revert m
      cases right <;> decide +kernel
    obtain ⟨p, _, k, _, hpk⟩ := h m hm'
    exact ⟨p, k, hpk⟩

/-- At the endpoints of either broad block, every selected index lies beyond
the right cutoff and below the integer square bounding the main support. -/
private theorem fixed_power_indices_656 (right : Bool) :
    ∀ m ∈ fixedPowers656 right,
      (if right then 328 else 325 : ℕ) ^ 2 < m ∧ m ≤ (if right then 1207 else 1196 : ℕ) ^ 2 := by
  cases right <;> decide +kernel

/-- At every radius of either broad block, the selected prime powers exceed
the cutoff and lie strictly inside the forward kernel support. -/
theorem fixed_power_support_656 (right : Bool) {r : ℝ}
    (hr : r ∈ Set.Icc (if right then 325 else 322) (if right then 328 else 325)) {m : ℕ}
    (hm : m ∈ fixedPowers656 right) : r ^ 2 < (m : ℝ) ∧ Real.log ((m : ℝ) / r ^ 2) < 21 / 8 := by
  let a : ℝ := if right then 325 else 322
  let b : ℕ := if right then 328 else 325
  let c : ℕ := if right then 1207 else 1196
  have ha : 0 < a := by cases right <;> norm_num only [a, Bool.false_eq_true, ite_false, ite_true]
  have hb : r ≤ (b : ℝ) := by cases right <;> exact hr.2
  have hp := ha.trans_le hr.1
  have ⟨hlo, hhi⟩ := fixed_power_indices_656 right m hm
  have hlo' : (b : ℝ) ^ 2 < m := by exact_mod_cast hlo
  have hhi' : (m : ℝ) ≤ (c : ℝ) ^ 2 := by exact_mod_cast hhi
  have hcut := (pow_le_pow_left₀ hp.le hb 2).trans_lt hlo'
  refine ⟨hcut, ?_⟩
  rw [Real.log_lt_iff_lt_exp (div_pos ((sq_nonneg r).trans_lt hcut) (sq_pos_of_pos hp))]
  apply (div_lt_iff₀ (sq_pos_of_pos hp)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num only : 0 ≤ (21 / 8 : ℝ)) 16
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_one, Nat.cast_zero] at he
  have hcap : (c : ℝ) ^ 2 < Real.exp (21 / 8) * a ^ 2 := by
    cases right <;>
      norm_num only [a, c, Bool.false_eq_true, ite_false, ite_true, Nat.cast_ofNat] <;>
      linarith only [he]
  exact
    hhi'.trans_lt
      (hcap.trans_le
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hr.1 2) (Real.exp_pos _).le))

/-- The fourfold principal contribution of the fixed prime powers at a radius.
The same finite set is used throughout each of the two section 132 blocks. -/
noncomputable def fixedPowerGain656 (right : Bool) (r : ℝ) : ℝ :=
  4 *
    ∑ m ∈ fixedPowers656 right, (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) m).re

/-- The power credit increases on each broad block. The kernel argument
stays between zero and five because each power stays beyond the cutoff
and strictly within the support. -/
theorem fixed_power_gain_mono_656 (right : Bool) :
    MonotoneOn (fixedPowerGain656 right)
      (Set.Icc (if right then 325 else 322) (if right then 328 else 325)) := by
  intro a ha r hr har
  have hL : (0 : ℝ) < (if right then 325 else 322) := by
    cases right <;> norm_num only [Bool.false_eq_true, ite_false, ite_true]
  have ha₀ := hL.trans_le ha.1
  have hr₀ := ha₀.trans_le har
  unfold fixedPowerGain656
  apply mul_le_mul_of_nonneg_left _ (by norm_num only)
  apply Finset.sum_le_sum
  intro m hm
  obtain ⟨hma, hsa⟩ := fixed_power_support_656 right ha hm
  obtain ⟨hmr, hsr⟩ := fixed_power_support_656 right hr hm
  have hm₀ : 0 < (m : ℝ) := (sq_nonneg r).trans_lt hmr
  have hl := Real.log_nonneg ((one_le_div (sq_pos_of_pos hr₀)).mpr hmr.le)
  have hlog :=
    Real.log_le_log (div_pos hm₀ (sq_pos_of_pos hr₀))
      (div_le_div_of_nonneg_left hm₀.le (sq_pos_of_pos ha₀) (pow_le_pow_left₀ ha₀.le har 2))
  rw [quarter_summand_656 (sq_pos_of_pos ha₀) (Nat.cast_pos.mp hm₀) hsa.le,
    quarter_summand_656 (sq_pos_of_pos hr₀) (Nat.cast_pos.mp hm₀) hsr.le]
  unfold quarterWeight656
  dsimp only
  apply mul_le_mul_of_nonneg_right _ ArithmeticFunction.vonMangoldt_nonneg
  apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr (Real.sqrt_nonneg _))
  apply div_le_div_of_nonneg_right _ (by norm_num only)
  apply fifth_increasing
  · exact ⟨by linarith only [hsa], by linarith only [hl, hlog]⟩
  · exact ⟨by linarith only [hsr], by linarith only [hl]⟩
  · linarith only [hlog]

/-- The endpoint credit at radius 322 or 325 is a lower bound for the
corresponding broad block, including its right endpoint. -/
theorem fixed_power_gain_left_656 (right : Bool) {r : ℝ}
    (hr : r ∈ Set.Icc (if right then 325 else 322) (if right then 328 else 325)) :
    fixedPowerGain656 right (if right then 325 else 322) ≤ fixedPowerGain656 right r := by
  apply fixed_power_gain_mono_656 right _ hr hr.1
  cases right <;> exact ⟨le_rfl, by norm_num only [Bool.false_eq_true, ite_false, ite_true]⟩

/-- If the three characters agree on every prime up to the cutoff and
their real trace is at least -1 everywhere, their sum recovers the fixed
power credit at the left endpoint in addition to the principal prefix. -/
theorem quarter_endpoint_power_credit_656 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (right : Bool) {r : ℝ}
    (hr : r ∈ Set.Icc (if right then 325 else 322) (if right then 328 else 325))
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (ha : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    let X := r ^ 2
    let f := fun n : ℕ ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) X n).re
    4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, f n) + fixedPowerGain656 right (if right then 325 else 322) -
        (∑' n : ℕ, quarterKernel656.summand (1 : DirichletCharacter ℂ 1) X n).re ≤
      (∑' n : ℕ, quarterKernel656.summand a X n).re +
        (∑' n : ℕ, quarterKernel656.summand b X n).re +
        (∑' n : ℕ, quarterKernel656.summand c X n).re := by
  intro X f
  have h322 : 322 ≤ r := by
    cases right
    · exact hr.1
    · exact (by norm_num only : (322 : ℝ) ≤ 325).trans hr.1
  have hp : 0 < X := sq_pos_of_pos ((by norm_num only : (0 : ℝ) < 322).trans_le h322)
  have hT : ∀ m ∈ fixedPowers656 right, X < m ∧ ∃ l k : ℕ, l.Prime ∧ (l : ℝ) ≤ X ∧ m = l ^ k := by
    intro m hm
    obtain ⟨l, k, hl, hcut, _, he⟩ := fixed_power_prime_base_656 right hm
    have hcut' : (l : ℝ) ≤ (322 : ℝ) ^ 2 := by exact_mod_cast hcut
    exact
      ⟨(fixed_power_support_656 right hr hm).1, l, k, hl,
        hcut'.trans (pow_le_pow_left₀ (by norm_num only) h322 2), he⟩
  have h := kernel_recover_fixed_powers quarterKernel656 a b c hp _ hT ht ha hb hc
  have hmono :=
    add_le_add (le_refl (4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, f n))) (fixed_power_gain_left_656 right hr)
  exact
    (sub_le_sub_right hmono
          (∑' n : ℕ, quarterKernel656.summand (1 : DirichletCharacter ℂ 1) X n).re).trans
      h

/-- Enclosures of the logarithm, square root and exponential at a
nonnegative profile argument certify a lower bound on a single prime
power contribution at the left endpoint of a section 132 block. -/
theorem quarter_power_row_lower_656 {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) {r z l s e : ℝ}
    (hr : 0 < r) (hz : 0 ≤ z)
    (harg : z ≤ (11 / 10) * (21 / 8 - Real.log (((p ^ k : ℕ) : ℝ) / r ^ 2)))
    (hcut : r ^ 2 ≤ (p ^ k : ℕ)) (hl : 0 ≤ l) (hlog : l ≤ Real.log p)
    (hs : Real.sqrt (p ^ k : ℕ) ≤ s) (he : e ≤ Real.exp (-z)) :
    4 * (l / s) * (z ^ 5 * e / 120) ≤
      4 * (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) (p ^ k)).re := by
  have hm : 0 < p ^ k := pow_pos hp.pos _
  have hsq : 0 < Real.sqrt (p ^ k : ℕ) := Real.sqrt_pos.2 (Nat.cast_pos.mpr hm)
  have hs₀ := hsq.trans_le hs
  have hL := Real.log_nonneg ((one_le_div (pow_pos hr 2)).mpr hcut)
  have hS : Real.log (((p ^ k : ℕ) : ℝ) / r ^ 2) ≤ 21 / 8 := by linarith only [hz, harg]
  rw [quarter_summand_656 (pow_pos hr 2) hm hS, ArithmeticFunction.vonMangoldt_apply_pow hk,
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  let v := (11 / 10 : ℝ) * (21 / 8 - Real.log (((p ^ k : ℕ) : ℝ) / r ^ 2))
  have hv : v ∈ Set.Icc 0 5 :=
    ⟨hz.trans harg, by
      dsimp only [v]; linarith only [hL]⟩
  have hzp : z ∈ Set.Icc 0 5 := ⟨hz, harg.trans hv.2⟩
  have hf := fifth_increasing hzp hv harg
  have hw := (mul_le_mul_of_nonneg_left he (pow_nonneg hz 5)).trans hf
  have hq : l / s ≤ Real.log p / Real.sqrt (p ^ k : ℕ) :=
    (div_le_div_of_nonneg_left hl hsq hs).trans (div_le_div_of_nonneg_right hlog hsq.le)
  have hV : 0 ≤ v ^ 5 * Real.exp (-v) / 120 := by positivity
  have hh :=
    mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hw (by norm_num only))
            (div_nonneg hl hs₀.le)).trans
        (mul_le_mul_of_nonneg_right hq hV))
      (by norm_num only : (0 : ℝ) ≤ 4)
  dsimp only [quarterWeight656]
  rw [mul_assoc (4 : ℝ) (l / s)]
  refine hh.trans_eq ?_
  dsimp only [v]
  ring

/-- A positive reciprocal bound for the Taylor upper bound of the
exponential is a lower bound for the exponential at the negated argument. -/
private theorem exp_neg_taylor_lower {z e : ℝ} (hz : 0 ≤ z) (ht : z / 17 ≤ 1 / 2)
    (he :
      e *
          ((∑ k ∈ Finset.range 16, z ^ k / (k.factorial : ℝ)) +
            z ^ 16 / ((16 : ℕ).factorial : ℝ) * 2) ≤
        1) :
    e ≤ Real.exp (-z) := by
  by_cases h : 0 ≤ e
  · rw [Real.exp_neg, ← one_div, le_div_iff₀ (Real.exp_pos _)]
    exact
      (mul_le_mul_of_nonneg_left (Analysis.exp_le_taylor_add_two_next (n := 16) hz ht) h).trans he
  · exact (le_of_not_ge h).trans (Real.exp_pos _).le

/-- Rational endpoint enclosures for a prime logarithm and the kernel
profile give a real lower bound on the fourfold prime-power contribution. -/
theorem quarter_power_rational_lower_656 {p k j : ℕ} (hp : p.Prime) (hk : k ≠ 0) {r : ℝ}
    (hr : 0 < r) (hcut : r ^ 2 ≤ (p ^ k : ℕ)) {L lo hi z e s c : ℚ} (hL : (L : ℝ) ≤ Real.log r)
    (hlog : Analysis.rationalLogIntervalCheck p j 27 lo hi = true) (hlo : 0 ≤ lo) (hz : 0 ≤ z)
    (hs : 0 ≤ s) (hroot : (p ^ k : ℕ) ≤ s ^ 2)
    (harg : z ≤ (11 / 10) * (21 / 8 - ((k : ℚ) * hi - 2 * L))) (ht : z / 17 ≤ 1 / 2)
    (he :
      e *
          ((∑ i ∈ Finset.range 16, z ^ i / (i.factorial : ℚ)) +
            z ^ 16 / ((16 : ℕ).factorial : ℚ) * 2) ≤
        1)
    (hc : c ≤ 4 * (lo / s) * (z ^ 5 * e / 120)) :
    (c : ℝ) ≤ 4 * (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) (p ^ k)).re := by
  have hlog' := Analysis.rationalLogIntervalCheck_sound hlog
  simp only [Rat.cast_natCast] at hlog'
  have hratio : Real.log (((p ^ k : ℕ) : ℝ) / r ^ 2) ≤ (k : ℝ) * (hi : ℝ) - 2 * L := by
    rw [Nat.cast_pow,
      Real.log_div (pow_ne_zero _ (Nat.cast_pos.mpr hp.pos).ne') (pow_ne_zero _ hr.ne'),
      Real.log_pow, Real.log_pow, Nat.cast_ofNat]
    exact
      sub_le_sub (mul_le_mul_of_nonneg_left hlog'.2 (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hL (by norm_num only))
  have hroot' : Real.sqrt (p ^ k : ℕ) ≤ (s : ℝ) :=
    (Real.sqrt_le_iff).mpr ⟨Rat.cast_nonneg.mpr hs, by exact_mod_cast hroot⟩
  have harg' := (Rat.cast_le (K := ℝ)).mpr harg
  simp only [Rat.cast_mul, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] at harg'
  have he' := (Rat.cast_le (K := ℝ)).mpr he
  simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_sum, Rat.cast_natCast,
    Rat.cast_one, Rat.cast_ofNat] at he'
  have hc' := (Rat.cast_le (K := ℝ)).mpr hc
  simp only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] at hc'
  have ht' : (z : ℝ) / 17 ≤ 1 / 2 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using (Rat.cast_le (K := ℝ)).mpr ht
  exact
    hc'.trans
      (quarter_power_row_lower_656 hp hk hr (Rat.cast_nonneg.mpr hz)
        (by linarith only [harg', hratio]) hcut (Rat.cast_nonneg.mpr hlo) hlog'.1 hroot'
        (exp_neg_taylor_lower (Rat.cast_nonneg.mpr hz) ht' he'))

/-- Sum verified lower bounds for the distinct indices at the left
endpoint and transfer the sum to any radius in the same block. -/
theorem fixed_power_sum_lower_656 (right : Bool) {r : ℝ}
    (hr : r ∈ Set.Icc (if right then 325 else 322) (if right then 328 else 325)) (lower : ℕ → ℝ)
    (h :
      ∀ m ∈ fixedPowers656 right,
        lower m ≤
          4 *
            (quarterKernel656.summand (1 : DirichletCharacter ℂ 1)
                ((if right then 325 else 322 : ℝ) ^ 2) m).re) :
    ∑ m ∈ fixedPowers656 right, lower m ≤ fixedPowerGain656 right r := by
  apply le_trans _ (fixed_power_gain_left_656 right hr)
  rw [fixedPowerGain656, Finset.mul_sum]
  exact Finset.sum_le_sum h

end PseudoPrime.PrimeTestBounds.MillerRabin
