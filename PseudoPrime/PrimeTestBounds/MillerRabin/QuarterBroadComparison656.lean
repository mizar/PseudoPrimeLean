/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMass656
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalTrivial656
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPowerNumerics656
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaCentral656
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaEndpoints656
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxReflectTail656
import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterThetaPoly656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflected570
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSignedTail656

/-! # Arithmetic and analytic comparison on the two section 132 intervals -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- In each broad interval, agreement on the tested primes forces the
principal lower bound and the fixed power recovery to fit inside the
three-character analytic upper bound. The reflected Euler difference
and the principal Gamma term remain explicit for the scalar comparison. -/
theorem quarter_broad_comparison_656 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hs : 2 ≤ s)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (right : Bool) {r : ℝ}
    (hr : r ∈ Set.Icc (if right then 325 else 322) (if right then 328 else 325))
    (hL : Real.log p + Real.log q + Real.log s = 4 * r)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) :
    let x := r ^ 2
    let l : ℝ := if right then 325 else 322
    let u : ℝ := if right then 328 else 325
    let credit : ℝ := if right then 143458466 / 1000000000 else 139723189 / 1000000000
    0.71780481 * r - 0.002926 - 4 * (9319732 / 100000000) * 70.4 / l +
            4 * (9319731 / 100000000) * (1837 / 1000) / u -
          (0.8 + 3 * Real.log (2 * Real.pi)) * quarterWeight656 x 1 +
        credit +
        quarterAuxTheta656 r +
        quarterAuxNegPole656 / r +
        14.592123988 +
        0.00022760 * r ≤
      3 / 4 * r + 4 * signedTail656 x + 4 * r * (quarterKernel656.transform x⁻¹).re +
          3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re -
        (quarterMainEuler656 a x + quarterMainEuler656 b x + quarterMainEuler656 c x) := by
  intro x l u credit
  have h322 : (322 : ℝ) ≤ l := by
    cases right <;> norm_num only [l, Bool.false_eq_true, ite_false, ite_true]
  have h328 : u ≤ (328 : ℝ) := by
    cases right <;> norm_num only [u, Bool.false_eq_true, ite_false, ite_true]
  have hall : r ∈ Set.Icc 322 328 := ⟨h322.trans hr.1, hr.2.trans h328⟩
  have hl : 0 < l := (by norm_num only : (0 : ℝ) < 322).trans_le h322
  have hc' : credit ≤ fixedPowerGain656 right l := by
    cases right
    · exact fixed_power_gain_322_656 (r := 322) ⟨le_rfl, by norm_num only⟩
    · exact fixed_power_gain_325_656 (r := 325) ⟨le_rfl, by norm_num only⟩
  have hm := quarter_forward_mass_gain_656 ha hb hc hp hq hs hG hall hL ht hpa hpb hpc
  have hP := quarter_principal_trivial_lower_656 hG.riemann hl hr.1 hr.2 hall
  have hpow := quarter_endpoint_power_credit_656 a b c right hr (fun n ↦ (ht n).1) hpa hpb hpc
  dsimp only [x, l, u] at hc' hm hP hpow ⊢
  have hPsum :=
    quarterKernel656.summable_summand (1 : DirichletCharacter ℂ 1)
      (sq_pos_of_pos (hl.trans_le hr.1))
  rw [Complex.re_tsum hPsum] at hpow
  have hX : 1 ≤ r ^ 2 := one_le_pow₀ ((by norm_num only : (1 : ℝ) ≤ 322).trans hall.1)
  rw [quarter_level_gamma_central_656 hX] at hm
  linarith only [hm, hP, hpow, hc']

/-- For an index in the certified prefix, changing the exponent from
79/50 to 8/5 costs at most a factor of 0.84. -/
private theorem reflected_power_lower_656 {n : ℕ} (hn : n ∈ Finset.Ioc 0 2701) :
    (0.84 : ℝ) * (n : ℝ) ^ (-(79 / 50) : ℝ) ≤ (n : ℝ) ^ (-(8 / 5) : ℝ) := by
  have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr (Finset.mem_Ioc.mp hn).1
  have hn₁ : (n : ℝ) ≤ 2701 := Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2
  have hc :=
    (Analysis.rationalLogIntervalCheck_sound (N := 2701) (j := 12) (n := 24) (lo := 7) (hi := 8)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat] at hc
  have hl := (Real.log_le_log hn₀ hn₁).trans hc
  have he : (0.84 : ℝ) ≤ Real.exp (Real.log n * -(1 / 50)) := by
    linarith only [hl, Real.add_one_le_exp (Real.log n * -(1 / 50))]
  have h := mul_le_mul_of_nonneg_right he (Real.rpow_nonneg hn₀.le (-(79 / 50)))
  rw [Real.rpow_def_of_pos hn₀, ← Real.exp_add] at h
  rw [show Real.log (n : ℝ) * -(1 / 50) + Real.log n * -(79 / 50) = Real.log n * -(8 / 5) by
      ring] at h
  simpa only [Real.rpow_def_of_pos hn₀] using h

/-- The six certified log moments bound the shifted weight on the common
prefix. Each binomial coefficient is nonnegative. -/
private theorem reflected_prefix_lower_656 {z : ℝ} (hz : 14.17 ≤ z) :
    0.84 * 1561402 ≤
      ∑ n ∈ Finset.Ioc 0 2701,
        ArithmeticFunction.vonMangoldt n * ((z + Real.log n) ^ 5 / (n : ℝ) ^ (8 / 5 : ℝ)) := by
  let P := fun n : ℕ ↦
    ∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℝ) * (14.17 : ℝ) ^ (5 - j) * quarterMangoldtMoment j n
  have hf : (1561402 : ℝ) ≤ ∑ n ∈ Finset.Ioc 0 2701, P n := by
    dsimp only [P]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    have h :=
      Finset.sum_le_sum (s := Finset.range 6) fun j hj ↦
        mul_le_mul_of_nonneg_left (moment_floor j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
          (mul_nonneg (Nat.cast_nonneg (Nat.choose 5 j))
            (by positivity : (0 : ℝ) ≤ 14.17 ^ (5 - j)))
    refine le_trans ?_ h
    norm_num only [momentFloor570, Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose,
      Nat.reduceSub, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  refine (mul_le_mul_of_nonneg_left hf (by norm_num only)).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hl := Real.log_natCast_nonneg n
  have hp : (14.17 + Real.log n) ^ 5 ≤ (z + Real.log n) ^ 5 :=
    pow_le_pow_left₀ (by linarith only [hl]) (add_le_add hz le_rfl) 5
  have hw :=
    mul_le_mul hp (reflected_power_lower_656 hn) (by positivity)
      (pow_nonneg (by linarith only [hz, hl]) 5)
  have h := mul_le_mul_of_nonneg_left hw (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  rw [Real.rpow_neg (Nat.cast_nonneg n) (8 / 5 : ℝ)] at h
  dsimp only [P, quarterMangoldtMoment]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceSub,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h ⊢
  convert h using 1 <;> ring

/-- The principal series dominates its prefix through 2701, which is
sufficient for the unshifted reflected contribution. -/
private theorem principal_reflect_prefix_656 {x : ℝ} (hx : 1 ≤ x) :
    ((11 / 10 : ℝ) ^ 5 * Real.exp (-(11 / 10) * (21 / 8)) / 120 * x ^ (-(11 / 10) : ℝ)) *
        (∑ n ∈ Finset.Ioc 0 2701,
          ArithmeticFunction.vonMangoldt n *
            ((21 / 8 + Real.log x + Real.log n) ^ 5 / (n : ℝ) ^ (8 / 5 : ℝ))) ≤
      quarterMainEuler656 (1 : DirichletCharacter ℂ 1) x := by
  have h := quarter_main_euler_hasSum_656 (1 : DirichletCharacter ℂ 1) (zero_lt_one.trans_le hx)
  have hψ (n : ℕ) : ((1 : DirichletCharacter ℂ 1) n).re = 1 := by
    simp only [MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), Complex.one_re]
  simp only [hψ, one_mul, quarter_main_euler_weight_656 hx] at h
  have hs :=
    h.summable.sum_le_tsum (Finset.Ioc 0 2701) fun n _ ↦ by
      have hz :=
        add_nonneg (add_nonneg (by norm_num only : (0 : ℝ) ≤ 21 / 8) (Real.log_nonneg hx))
          (Real.log_natCast_nonneg n)
      positivity
  rwa [← Finset.mul_sum, h.tsum_eq] at hs

/-- On the broad radius range the exponential factor in the reflected
principal term at 2 is bounded below by its certified endpoint value. -/
private theorem principal_reflect_decay_656 {r : ℝ} (hr : r ∈ Set.Icc 322 328) :
    0.00000016 ≤ Real.exp (-(11 / 10) * (21 / 8 + Real.log (r ^ 2))) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 27) (lo := 5) (hi := 5.7935)
        (by decide +kernel)).2
  have hc :=
    (Analysis.rationalLogIntervalCheck_sound (N := 6250000) (j := 23) (n := 32) (lo := 15.64) (hi :=
        16) (by decide +kernel)).1
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 322).trans_le hr.1
  have hle := Real.log_le_log hr₀ hr.2
  apply (Real.log_le_iff_le_exp (by norm_num only : (0 : ℝ) < 0.00000016)).mp
  have hinv : Real.log (0.00000016 : ℝ)⁻¹ ≥ 15.64 := by
    norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hc
    norm_num only at hc ⊢
    exact hc
  rw [Real.log_inv] at hinv
  rw [Real.log_pow]
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hlog
  linarith only [hinv, hlog, hle]

/-- The certified prefix gives a uniform 0.00844 credit for three copies
of the principal Euler term on the two section 132 intervals. -/
private theorem principal_reflect_credit_656 {r : ℝ} (hr : r ∈ Set.Icc 322 328) :
    0.00844 ≤ 3 * quarterMainEuler656 (1 : DirichletCharacter ℂ 1) (r ^ 2) := by
  have hx : 1 ≤ r ^ 2 := one_le_pow₀ ((by norm_num only : (1 : ℝ) ≤ 322).trans hr.1)
  have h := principal_reflect_prefix_656 hx
  have he := principal_reflect_decay_656 hr
  have hL :=
    (Analysis.rationalLogIntervalCheck_sound (N := 322) (j := 9) (n := 27) (lo := 5.774) (hi := 6)
        (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hL
  have hz : 14.17 ≤ 21 / 8 + Real.log (r ^ 2) := by
    rw [Real.log_pow]
    linarith only [hL, Real.log_le_log (by norm_num only : (0 : ℝ) < 322) hr.1]
  have hm := reflected_prefix_lower_656 hz
  have hprod := mul_le_mul he hm (by norm_num only : 0 ≤ (0.84 : ℝ) * 1561402) (Real.exp_pos _).le
  rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hx)] at h
  have harg :
    -(11 / 10 : ℝ) * (21 / 8 + Real.log (r ^ 2)) =
      -(11 / 10) * (21 / 8) + Real.log (r ^ 2) * -(11 / 10) := by
    ring
  rw [harg, Real.exp_add] at hprod
  nlinarith only [h, hprod]

/-- The signed Abel tail is antitone, so each comparison interval uses
the value at the square of its left endpoint. -/
private theorem signed_tail_rows_656 (right : Bool) {r : ℝ}
    (hr : r ∈ Set.Icc (if right then 325 else 322) (if right then 328 else 325)) :
    signedTail656 (r ^ 2) ≤ signedTail656 ((if right then 325 else 322 : ℝ) ^ 2) := by
  let l : ℝ := if right then 325 else 322
  let u : ℝ := if right then 328 else 325
  have hl : (322 : ℝ) ≤ l := by
    cases right <;> norm_num only [l, Bool.false_eq_true, ite_false, ite_true]
  have hu : u ≤ (328 : ℝ) := by
    cases right <;> norm_num only [u, Bool.false_eq_true, ite_false, ite_true]
  have h₀ : (0 : ℝ) ≤ l := (by norm_num only : (0 : ℝ) ≤ 322).trans hl
  have h₁ := pow_le_pow_left₀ h₀ hr.1 2
  have h₂ : (2701 : ℝ) ≤ l ^ 2 :=
    (by norm_num only : (2701 : ℝ) ≤ 322 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hl 2)
  have h₃ : r ^ 2 ≤ (1000000 : ℝ) :=
    (pow_le_pow_left₀ (h₀.trans hr.1) (hr.2.trans hu) 2).trans (by norm_num only)
  exact signed_tail_antitone_656 ⟨h₂, h₁.trans h₃⟩ ⟨h₂.trans h₁, h₃⟩ h₁

/-- Prime-prefix agreement forces the section 132 comparison with the
certified Gamma, reflected Euler, Abel tail, and auxiliary conductor bounds. -/
theorem quarter_broad_gamma_comparison_656 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hs : 2 ≤ s)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (right : Bool) {r : ℝ}
    (hr : r ∈ Set.Icc (if right then 325 else 322) (if right then 328 else 325))
    (hL : Real.log p + Real.log q + Real.log s = 4 * r)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) :
    let x := r ^ 2
    let l : ℝ := if right then 325 else 322
    let u : ℝ := if right then 328 else 325
    let credit : ℝ := if right then 143458466 / 1000000000 else 139723189 / 1000000000
    0.71780481 * r - 0.002926 - 4 * (9319732 / 100000000) * 70.4 / l +
                4 * (9319731 / 100000000) * (1837 / 1000) / u -
              (0.8 + 3 * Real.log (2 * Real.pi)) * quarterWeight656 x 1 +
            credit +
            (if right then -2.434837 else -2.446546) -
          0.01 * (u - r) +
        quarterAuxNegPole656 / r +
        14.592123988 +
        0.00022760 * r ≤
      3 / 4 * r + 4 * (if right then 0.053045 else 0.053504) +
            4 * r * (quarterKernel656.transform x⁻¹).re +
            3 * (-2.16 * quarterWeight656 x 1 - (if right then 0.02411 else 0.02431)) -
          0.00844 +
        0.000242 := by
  have hbroad := quarter_broad_comparison_656 ha hb hc hp hq hs hG right hr hL ht hpa hpb hpc
  have hgamma := quarter_principal_gamma_rows_656 right hr
  have hall : r ∈ Set.Icc 322 328 := by
    cases right
    · exact ⟨hr.1, hr.2.trans (by norm_num only : (325 : ℝ) ≤ 328)⟩
    · exact ⟨(by norm_num only : (322 : ℝ) ≤ 325).trans hr.1, hr.2⟩
  have hX : (103684 : ℝ) ≤ r ^ 2 := by
    rw [show (103684 : ℝ) = 322 ^ 2 by norm_num only]
    exact pow_le_pow_left₀ (by norm_num only) hall.1 2
  have hreflect :=
    (quarter_main_reflect_cap_656 a b c hG.riemann hall.1 (B := 103684) (by norm_num only)
          (by norm_num only) hX ht hpa hpb hpc).trans
      (quarter_main_reflect_box_656 hall)
  have htail : signedTail656 (r ^ 2) ≤ (if right then 0.053045 else 0.053504) := by
    refine (signed_tail_rows_656 right hr).trans ?_
    cases right
    · exact quarter_signed_tail_322_656
    · exact quarter_signed_tail_325_656
  have htheta :
    (if right then -2.434837 else -2.446546) - 0.01 * ((if right then 328 else 325 : ℝ) - r) ≤
      quarterAuxTheta656 r := by
    cases right
    · exact theta_affine_325_656 hall.1 hr.2
    · exact theta_affine_328_656 hall.1 hr.2
  dsimp only at hbroad ⊢
  linarith only [hbroad, hgamma, hreflect, principal_reflect_credit_656 hall, htail, htheta]

/-- The logarithmic coefficient of the weight at one is bounded by the
certified Gamma coefficient. -/
private theorem broad_weight_coeff_656 : 0.8 + 3 * Real.log (2 * Real.pi) ≤ 6.48 := by
  have hπ : 2 * Real.pi ≤ 6.3 := by linarith only [Real.pi_lt_d4]
  have hlog := Real.log_le_log (by positivity : 0 < 2 * Real.pi) hπ
  have hc :=
    (Analysis.rationalLogIntervalCheck_sound (N := 63 / 10) (j := 3) (n := 24) (lo := 1) (hi :=
        1.89) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hc hlog
  linarith only [hlog, hc]

/-- Three primitive even quadratic characters with the prescribed total
conductor cannot all agree on primes up to the squared radius in either
section 132 interval. -/
theorem quarter_broad_impossible_656 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hs : 2 ≤ s)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (right : Bool) {r : ℝ}
    (hr : r ∈ Set.Icc (if right then 325 else 322) (if right then 328 else 325))
    (hL : Real.log p + Real.log q + Real.log s = 4 * r)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) : False := by
  have h := quarter_broad_gamma_comparison_656 ha hb hc hp hq hs hG right hr hL ht hpa hpb hpc
  let u : ℝ := if right then 328 else 325
  have hr₀ : 322 ≤ r := by
    cases right
    · exact hr.1
    · exact (by norm_num only : (322 : ℝ) ≤ 325).trans hr.1
  have hr₁ : 1 ≤ r := (by norm_num only : (1 : ℝ) ≤ 322).trans hr₀
  have hpole : 19.24138528 / u ≤ quarterAuxNegPole656 / r := by
    have hu : 0 < u := (zero_lt_one.trans_le hr₁).trans_le hr.2
    exact
      (div_le_div_of_nonneg_left (by norm_num only) (zero_lt_one.trans_le hr₁) hr.2).trans
        (div_le_div_of_nonneg_right quarter_aux_neg_pole_box_656.1 (zero_le_one.trans hr₁))
  have hmain :
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤
      (if right then 1.659189 else 1.666766) + 0.007 * (u - r) := by
    cases right
    · exact main_conductor_325_656 hr₀ hr.2
    · exact main_conductor_328_656 hr₀ hr.2
  have hw : 0 ≤ quarterWeight656 (r ^ 2) 1 := by
    unfold quarterWeight656
    simp only [Real.sqrt_one, div_one, one_mul, one_div, Real.log_inv, sub_neg_eq_add]
    have hl := Real.log_nonneg (one_le_pow₀ hr₁ (n := 2))
    positivity
  have hw' := mul_le_mul_of_nonneg_right broad_weight_coeff_656 hw
  have hru : r ≤ u := hr.2
  dsimp only at h
  cases right
  · norm_num only [u, Bool.false_eq_true, ite_false] at h hpole hmain hru
    linarith only [h, hpole, hmain, hru, hw']
  · norm_num only [u, ite_true] at h hpole hmain hru
    linarith only [h, hpole, hmain, hru, hw']

end PseudoPrime.PrimeTestBounds.MillerRabin
