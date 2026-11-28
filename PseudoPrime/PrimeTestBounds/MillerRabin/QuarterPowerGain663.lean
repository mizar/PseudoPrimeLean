/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPowerNumerics656
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalTail663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPowerNumerics656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPowerSupport656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerTail663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalWeights656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMass656

/-! # A fixed recovered-power set for section 137 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Reuse the preceding interval's certified powers, removing the one
square that can fall below the new cutoff. -/
def fixedPowers663 : Finset ℕ :=
  (fixedPowers656 true).erase (331 ^ 2)

/-- Every retained power has a prime base and exponent at least two. -/
theorem fixed_power_base_663 {n : ℕ} (hn : n ∈ fixedPowers663) :
    ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ n = p ^ k := by
  obtain ⟨p, k, hp, _, hk, he⟩ := fixed_power_prime_base_656 true (Finset.mem_of_mem_erase hn)
  exact ⟨p, k, hp, hk, he⟩

/-- The fixed powers stay above the tested cutoff and inside the kernel
support throughout the section 137 interval. -/
theorem fixed_power_support_lt_337 {r : ℝ} (hr : r ∈ Set.Ico 325 337) {n : ℕ}
    (hn : n ∈ fixedPowers663) : r ^ 2 < (n : ℝ) ∧ Real.log ((n : ℝ) / r ^ 2) < 21 / 8 := by
  have hN : ∀ n ∈ fixedPowers663, 337 ^ 2 ≤ n := by decide +kernel
  have hn' : (337 : ℝ) ^ 2 ≤ n := by exact_mod_cast (hN n hn)
  have hr₀ : 0 < r := by linarith only [hr.1]
  have hh := pow_lt_pow_left₀ hr.2 hr₀.le (by decide : 2 ≠ 0)
  have hlo : r ^ 2 < (n : ℝ) := hh.trans_le hn'
  have hm :=
    fixed_power_support_656 true (r := 325)
      (by norm_num only [ite_true, Set.mem_Icc, le_refl, true_and]) (Finset.mem_of_mem_erase hn)
  have hp := (sq_nonneg r).trans_lt hlo
  have hd :=
    div_le_div_of_nonneg_left hp.le (by norm_num only : (0 : ℝ) < 325 ^ 2)
      (pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 325) hr.1 2)
  exact ⟨hlo, (Real.log_le_log (div_pos hp (sq_pos_of_pos hr₀)) hd).trans_lt hm.2⟩

/-- Recover the preceding support bound on the first Gaussian radius interval. -/
theorem fixed_power_support_wide_663 {r : ℝ} (hr : r ∈ Set.Icc 325 332) {n : ℕ}
    (hn : n ∈ fixedPowers663) : r ^ 2 < (n : ℝ) ∧ Real.log ((n : ℝ) / r ^ 2) < 21 / 8 := by
  exact fixed_power_support_lt_337 ⟨hr.1, hr.2.trans_lt (by norm_num only)⟩ hn

/-- The fixed power support estimate on the original quarter-square interval. -/
theorem fixed_power_support_663 {r : ℝ} (hr : r ∈ Set.Icc 325 (663 / 2)) {n : ℕ}
    (hn : n ∈ fixedPowers663) : r ^ 2 < (n : ℝ) ∧ Real.log ((n : ℝ) / r ^ 2) < 21 / 8 := by
  exact fixed_power_support_wide_663 ⟨hr.1, hr.2.trans (by norm_num only)⟩ hn

private theorem weight_radius_mono {a r n : ℝ} (ha : 0 < a) (har : a ≤ r) (hn : r ^ 2 ≤ n)
    (hcut : Real.log (n / a ^ 2) ≤ 21 / 8) :
    quarterWeight656 (a ^ 2) n ≤ quarterWeight656 (r ^ 2) n := by
  have hr := ha.trans_le har
  have hn₀ := (sq_pos_of_pos hr).trans_le hn
  have hl := Real.log_nonneg ((one_le_div (sq_pos_of_pos hr)).mpr hn)
  have hlog :=
    Real.log_le_log (div_pos hn₀ (sq_pos_of_pos hr))
      (div_le_div_of_nonneg_left hn₀.le (sq_pos_of_pos ha) (pow_le_pow_left₀ ha.le har 2))
  unfold quarterWeight656
  dsimp only
  apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr (Real.sqrt_nonneg _))
  apply div_le_div_of_nonneg_right _ (by norm_num only)
  apply fifth_increasing
  · exact ⟨by linarith only [hcut], by linarith only [hl, hlog]⟩
  · exact ⟨by linarith only [hcut, hlog], by linarith only [hl]⟩
  · linarith only [hlog]

set_option maxRecDepth 8192 in
-- Reuse the validated rows and reduce only the filtered indices and integer credits.
private theorem fixed_power_gain_at_325 :
    0.137116529 ≤
      ∑ n ∈ fixedPowers663,
        4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (325 ^ 2) n) := by
  let rows := powerRows325.toFinset.filter (fun a ↦ a.p ^ a.k ≠ 331 ^ 2)
  have hL :=
    (Analysis.rationalLogIntervalCheck_sound (N := 325) (j := 8) (n := 27) (lo :=
        5783825180 / 1000000000) (hi := 5783825185 / 1000000000) (by decide +kernel)).1
  simp only [Rat.cast_ofNat] at hL
  have h :=
    Finset.sum_le_sum (s := rows)
      (fun a ha ↦
        PowerRow656.sound a (by norm_num only : (0 : ℝ) < (325 : ℕ)) hL
          (power_rows_valid_325 a (Finset.mem_filter.mp ha).1))
  rw [← Finset.sum_div, ← Nat.cast_sum] at h
  have hc : (∑ a ∈ rows, a.credit) = 137116529 := by decide +kernel
  rw [hc, Nat.cast_ofNat] at h
  have hset : rows.image (fun a ↦ a.p ^ a.k) = fixedPowers663 := by decide +kernel
  have hcard : (rows.image (fun a ↦ a.p ^ a.k)).card = rows.card := by decide +kernel
  have hinj := Finset.injOn_of_card_image_eq hcard
  have he (n : ℕ) (hn : n ∈ fixedPowers663) :
    (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) (325 ^ 2) n).re =
      ArithmeticFunction.vonMangoldt n * quarterWeight656 (325 ^ 2) n := by
    have hs := fixed_power_support_663 (r := 325) ⟨le_rfl, by norm_num only⟩ hn
    rw [quarter_summand_656 (by norm_num only) (Nat.cast_pos.mp ((sq_nonneg _).trans_lt hs.1))
        hs.2.le,
      mul_comm]
  have hsum :
    (∑ n ∈ fixedPowers663,
        4 * (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) (325 ^ 2) n).re) =
      ∑ a ∈ rows,
        4 * (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) (325 ^ 2) (a.p ^ a.k)).re := by
    rw [← hset, Finset.sum_image (fun _ ha _ hb hab ↦ hinj ha hb hab)]
  norm_num only at h hsum he ⊢
  rw [← hsum] at h
  exact h.trans_eq (Finset.sum_congr rfl fun n hn ↦ congrArg (fun x : ℝ ↦ 4 * x) (he n hn))

/-- The preceding verified power rows give a uniform lower bound after
removing the square below the new right endpoint. -/
theorem fixed_power_gain_lt_337 {r : ℝ} (hr : r ∈ Set.Ico 328 337) :
    0.137116529 ≤
      ∑ n ∈ fixedPowers663,
        4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n) := by
  refine fixed_power_gain_at_325.trans (Finset.sum_le_sum fun n hn ↦ ?_)
  have ha : (325 : ℝ) ≤ r := by linarith only [hr.1]
  have hs := fixed_power_support_lt_337 ⟨ha, hr.2⟩ hn
  have h₀ := fixed_power_support_663 (r := 325) ⟨le_rfl, by norm_num only⟩ hn
  exact
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (weight_radius_mono (by norm_num only) ha hs.1.le h₀.2.le)
        ArithmeticFunction.vonMangoldt_nonneg)
      (by norm_num only)

/-- The same recovered-power gain applies on the first Gaussian radius interval. -/
theorem fixed_power_gain_wide_663 {r : ℝ} (hr : r ∈ Set.Icc 328 332) :
    0.137116529 ≤
      ∑ n ∈ fixedPowers663,
        4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n) := by
  exact fixed_power_gain_lt_337 ⟨hr.1, hr.2.trans_lt (by norm_num only)⟩

/-- The two remaining K137 scales use the same recovered powers and the same gain. -/
public theorem k137_later_power_data {s L : ℝ} (hs : s ∈ Set.Icc 1 (1001 / 1000 : ℝ))
    (hL : L ∈ Set.Icc (1327 / 2 : ℝ) (2657 / 4)) :
    let y := s * L / 2
    (∀ n ∈ fixedPowers663, y ^ 2 < (n : ℝ) ∧ Real.log ((n : ℝ) / y ^ 2) ≤ 21 / 8) ∧
      0.137116529 ≤
        ∑ n ∈ fixedPowers663,
          4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (y ^ 2) n) := by
  intro y
  have hL₀ : 0 ≤ L := (by norm_num only : (0 : ℝ) ≤ 1327 / 2).trans hL.1
  have hl := mul_le_mul_of_nonneg_right hs.1 hL₀
  have hu := mul_le_mul hs.2 hL.2 hL₀ (by norm_num only : (0 : ℝ) ≤ 1001 / 1000)
  have hy : y ∈ Set.Ico (328 : ℝ) 337 := by
    dsimp only [y]
    exact ⟨by linarith only [hl, hL.1], by linarith only [hu]⟩
  have hwide : y ∈ Set.Ico (325 : ℝ) 337 := ⟨(by norm_num only : (325 : ℝ) ≤ 328).trans hy.1, hy.2⟩
  refine ⟨?_, fixed_power_gain_lt_337 hy⟩
  intro n hn
  have h := fixed_power_support_lt_337 hwide hn
  exact ⟨h.1, h.2.le⟩

/-- The fixed power gain on the original quarter-square interval. -/
theorem fixed_power_gain_663 {r : ℝ} (hr : r ∈ Set.Icc 328 (663 / 2)) :
    0.137116529 ≤
      ∑ n ∈ fixedPowers663,
        4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n) := by
  exact fixed_power_gain_wide_663 ⟨hr.1, hr.2.trans (by norm_num only)⟩

/-- Prime agreement contradicts the fixed recovered-power credit once the
signed Abel error is at most the radius-dependent budget. -/
theorem quarter_agreement_false_663 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc 328 (663 / 2)) (hL : Real.log p + Real.log q + Real.log k = 4 * r)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1)
    (hE :
      -4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) -
          4 *
            (∫ t in r ^ 2..r ^ 2 * Real.exp (21 / 8),
              (Chebyshev.psi t - t) * deriv (quarterWeight656 (r ^ 2)) t) ≤
        0.055701529 + 0.0219746789 * (663 / 2 - r) + (if 1319 / 4 ≤ r then 0.004377 else 0)) :
    False := by
  have hs (n : ℕ) (hn : n ∈ fixedPowers663) :=
    fixed_power_support_663 ⟨by linarith only [hr.1], hr.2⟩ hn
  have h :=
    quarter_numeric_comparison_663 ha hb hc hp hq hk hG hr hL ht hpa hpb hpc fixedPowers663
      (fun n hn ↦ (hs n hn).1) (fun n hn ↦ (hs n hn).2.le) (fun _ hn ↦ fixed_power_base_663 hn)
  dsimp only at h
  linarith only [h, fixed_power_gain_663 hr, hE]

private theorem summand_endpoint_le {x u : ℝ} (hx : 0 < x) (hxu : x ≤ u) {n : ℕ}
    (hn : u ≤ (n : ℝ)) :
    (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re ≤
      (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) u n).re := by
  have hu := hx.trans_le hxu
  by_cases hs : Real.log ((n : ℝ) / x) ≤ 21 / 8
  · have hn₀ := hu.trans_le hn
    have hlog := Real.log_le_log (div_pos hn₀ hu) (div_le_div_of_nonneg_left hn₀.le hx hxu)
    rw [principal_summand_eq hx, principal_summand_eq hu, ite_eq_left hs,
      ite_eq_left (hlog.trans hs)]
    have he :=
      weight_radius_mono (Real.sqrt_pos.mpr hx) (Real.sqrt_le_sqrt hxu) (n := (n : ℝ))
        (by simpa only [Real.sq_sqrt hu.le] using hn) (by simpa only [Real.sq_sqrt hx.le] using hs)
    rw [Real.sq_sqrt hx.le, Real.sq_sqrt hu.le] at he
    exact mul_le_mul_of_nonneg_left he ArithmeticFunction.vonMangoldt_nonneg
  · rw [principal_summand_eq hx, ite_eq_right hs, mul_zero]
    exact quarterKernel656.principal_summand_re_nonneg hu n

/-- If the square scale lies in the half-open interval from N to N+1,
its principal tail is bounded by the tail at N+1 with the same lower cutoff. -/
theorem quarter_tail_endpoint_663 {x : ℝ} {N : ℕ} (hx : 0 < x) (h₁ : (N : ℝ) ≤ x)
    (h₂ : x < (N : ℝ) + 1) :
    let W := fun (y : ℝ) n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) y n).re
    (∑' n : ℕ, W x n) - (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W x n) ≤
      (∑' n : ℕ, W ((N : ℝ) + 1) n) - (∑ n ∈ Finset.Ioc 0 N, W ((N : ℝ) + 1) n) := by
  intro W
  have hu := hx.trans h₂
  have hN : ⌊x⌋₊ = N := Nat.floor_eq_on_Ico N x ⟨h₁, h₂⟩
  have hs {y : ℝ} (hy : 0 < y) : Summable (W y) :=
    (Complex.hasSum_re
        (LLS.PaperStatements.MellinKernel.summable_summand quarterKernel656
            (1 : DirichletCharacter ℂ 1) hy).hasSum).summable
  have hz {y : ℝ} (hy : 0 < y) : W y 0 = 0 := by
    simp only [W, principal_summand_eq hy, ArithmeticFunction.map_zero, zero_mul]
  rw [hN, ← tsum_above_eq (hs hx) (hz hx), ← tsum_above_eq (hs hu) (hz hu)]
  exact
    ((hs hx).subtype (fun n ↦ N < n)).tsum_le_tsum
      (fun n ↦ summand_endpoint_le hx h₂.le (by exact_mod_cast Nat.succ_le_of_lt n.property))
      ((hs hu).subtype _)

private theorem tail_mass_nonneg : 0 ≤ quarterTailMass663 := by
  unfold quarterTailMass663
  apply intervalIntegral.integral_nonneg (Real.one_le_exp (by norm_num only))
  intro u hu
  exact
    div_nonneg (quarterKernel656.mellin_nonneg u (zero_lt_one.trans_le hu.1)) (Real.sqrt_nonneg u)

/-- For every real scale between consecutive integers, one right-endpoint
tail and the left-endpoint continuous mass bound the signed Abel error. -/
theorem quarter_abel_endpoint_663 {x : ℝ} {N : ℕ} (hx : 0 < x) (h₁ : (N : ℝ) ≤ x)
    (h₂ : x < (N : ℝ) + 1) :
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) ((N : ℝ) + 1) n).re
    (-4 : ℝ) * (Chebyshev.psi x - x) * quarterWeight656 x x -
        4 *
          (∫ t in x..x * Real.exp (21 / 8), (Chebyshev.psi t - t) * deriv (quarterWeight656 x) t) ≤
      4 * ((∑' n : ℕ, W n) - (∑ n ∈ Finset.Ioc 0 N, W n) - Real.sqrt N * quarterTailMass663) := by
  intro W
  have hy := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 21 / 8))
  have hI := quarter_scale_integral_656 hx hx hy le_rfl
  rw [div_self hx.ne', mul_div_cancel_left₀ _ hx.ne'] at hI
  change _ = Real.sqrt x * quarterTailMass663 at hI
  have hM := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h₁) tail_mass_nonneg
  have he := quarter_tail_endpoint_663 hx h₁ h₂
  have ha := quarter_principal_abel_663 hx
  dsimp only [W] at he ha ⊢
  linarith only [he, ha, hM, hI]

/-- Integer endpoint certificates for the finite Mangoldt sums imply the
required signed Abel error bound at every real radius of section 137. -/
theorem quarter_abel_of_integer_bounds_663 {r : ℝ} (hr : r ∈ Set.Icc 328 (663 / 2))
    (hcert :
      ∀ N ∈ Finset.Icc (107584 : ℕ) 109892,
        let u := (N : ℝ) + 1
        4 *
            ((∑ n ∈ Finset.Ioc N ⌊u * Real.exp (21 / 8)⌋₊,
                ArithmeticFunction.vonMangoldt n * quarterWeight656 u n) -
              Real.sqrt N * 0.088044185448) ≤
          0.055701529 + 0.0219746789 * (663 / 2 - Real.sqrt u) +
            (if 108736 ≤ N then 0.004377 else 0)) :
    let x := r ^ 2
    (-4 : ℝ) * (Chebyshev.psi x - x) * quarterWeight656 x x -
        4 *
          (∫ t in x..x * Real.exp (21 / 8), (Chebyshev.psi t - t) * deriv (quarterWeight656 x) t) ≤
      0.055701529 + 0.0219746789 * (663 / 2 - r) + (if 1319 / 4 ≤ r then 0.004377 else 0) := by
  intro x
  let N := ⌊x⌋₊
  have hr₀ : 0 < r := by linarith only [hr.1]
  have hx : 0 < x := sq_pos_of_pos hr₀
  have h₁ : (N : ℝ) ≤ x := Nat.floor_le hx.le
  have h₂ : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hL : (107584 : ℝ) ≤ x := by
    rw [show (107584 : ℝ) = 328 ^ 2 by norm_num only]
    exact pow_le_pow_left₀ (by norm_num only) hr.1 2
  have hU : x < (109893 : ℝ) := (pow_le_pow_left₀ hr₀.le hr.2 2).trans_lt (by norm_num only)
  have hn : N ∈ Finset.Icc (107584 : ℕ) 109892 :=
    Finset.mem_Icc.mpr
      ⟨(Nat.le_floor_iff hx.le).mpr (by exact_mod_cast hL),
        Nat.lt_succ_iff.mp ((Nat.floor_lt hx.le).mpr (by exact_mod_cast hU))⟩
  have h := quarter_abel_endpoint_663 hx h₁ h₂
  dsimp only at h
  rw [quarter_endpoint_tail_finite_663 (hx.trans h₂) N] at h
  have hc := hcert N hn
  dsimp only at hc
  have hM := mul_le_mul_of_nonneg_left quarter_tail_mass_lower_663 (Real.sqrt_nonneg (N : ℝ))
  have hs := Real.sqrt_le_sqrt h₂.le
  change Real.sqrt (r ^ 2) ≤ _ at hs
  rw [Real.sqrt_sq hr₀.le] at hs
  have hg :
    (if 108736 ≤ N then (0.004377 : ℝ) else 0) ≤ (if 1319 / 4 ≤ r then (0.004377 : ℝ) else 0) := by
    by_cases hn' : 108736 ≤ N
    · have hnR : (108736 : ℝ) ≤ N := by exact_mod_cast hn'
      have ht : (1319 / 4 : ℝ) ^ 2 ≤ r ^ 2 :=
        (by norm_num only : (1319 / 4 : ℝ) ^ 2 ≤ 108736).trans (hnR.trans h₁)
      have ht' := Real.sqrt_le_sqrt ht
      rw [Real.sqrt_sq (by norm_num only : (0 : ℝ) ≤ 1319 / 4), Real.sqrt_sq hr₀.le] at ht'
      rw [ite_eq_left hn', ite_eq_left ht']
    · rw [ite_eq_right hn']
      split <;> norm_num only [le_refl]
  linarith only [h, hc, hM, hs, hg]

/-- The cumulative Mangoldt moment centered at 12. Each endpoint uses the
same sequence of six moments, including all prime powers. -/
noncomputable def quarterMangoldtPrefix663 (B j : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 B,
    (n : ℝ) ^ (3 / 5 : ℝ) * ArithmeticFunction.vonMangoldt n * (12 - Real.log n) ^ j

private theorem mangoldt_moment_window {N B : ℕ} (hNB : N ≤ B) (j : ℕ) :
    (∑ n ∈ Finset.Ioc N B,
        (n : ℝ) ^ (3 / 5 : ℝ) * ArithmeticFunction.vonMangoldt n * (12 - Real.log n) ^ j) =
      quarterMangoldtPrefix663 B j - quarterMangoldtPrefix663 N j := by
  unfold quarterMangoldtPrefix663
  rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le N) hNB,
    Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl), add_sub_cancel_left]

/-- Compute an endpoint's weighted Mangoldt sum from two cumulative
moment vectors. The same prefix arithmetic serves every endpoint. -/
theorem quarter_endpoint_moments_663 {u : ℝ} (hu : 0 < u) {N B : ℕ} (hNB : N ≤ B) :
    (∑ n ∈ Finset.Ioc N B, ArithmeticFunction.vonMangoldt n * quarterWeight656 u n) =
      ((11 / 10 : ℝ) ^ 5 / 120 * Real.exp (-(11 / 10) * (21 / 8)) * u ^ (-(11 / 10) : ℝ)) *
        ∑ j ∈ Finset.range 6,
          (Nat.choose 5 j : ℝ) * (21 / 8 + Real.log u - 12) ^ (5 - j) *
            (quarterMangoldtPrefix663 B j - quarterMangoldtPrefix663 N j) := by
  simp only [← mangoldt_moment_window hNB, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.range 6)]
  apply Finset.sum_congr rfl
  intro n hn
  have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1)
  rw [forward_weight_factor hu hn₀]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceSub,
    Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]
  ring

/-- Enlarge the support to the certified upper integer and bound the
weighted sum using outward cumulative-moment differences. The signed
moments are multiplied by nonnegative coefficients after centering. -/
theorem quarter_endpoint_rational_le_663 {u : ℝ} (hu : 0 < u) {N B : ℕ} (hNB : N ≤ B)
    (hB : ⌊u * Real.exp (21 / 8)⌋₊ ≤ B) {z K : ℚ} (hz₀ : 0 ≤ z)
    (hz : 21 / 8 + Real.log u - 12 ≤ (z : ℝ))
    (hK :
      (11 / 10 : ℝ) ^ 5 / 120 * Real.exp (-(11 / 10) * (21 / 8)) * u ^ (-(11 / 10) : ℝ) ≤ (K : ℝ))
    (hBz : (B : ℝ) ≤ Real.exp ((z : ℝ) + 12)) (M : ℕ → ℚ)
    (hM :
      ∀ j ∈ Finset.range 6,
        quarterMangoldtPrefix663 B j - quarterMangoldtPrefix663 N j ≤ (M j : ℝ)) :
    (∑ n ∈ Finset.Ioc N ⌊u * Real.exp (21 / 8)⌋₊,
        ArithmeticFunction.vonMangoldt n * quarterWeight656 u n) ≤
      ((K * ∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℚ) * z ^ (5 - j) * M j : ℚ) : ℝ) := by
  let C := (11 / 10 : ℝ) ^ 5 / 120 * Real.exp (-(11 / 10) * (21 / 8)) * u ^ (-(11 / 10) : ℝ)
  let G := fun n : ℕ ↦
    (n : ℝ) ^ (3 / 5 : ℝ) * ArithmeticFunction.vonMangoldt n * ((z : ℝ) + 12 - Real.log n) ^ 5
  have hC : 0 ≤ C := by
    dsimp only [C]; positivity
  have hK₀ := hC.trans hK
  have hS (n : ℕ) (hn : n ∈ Finset.Ioc N ⌊u * Real.exp (21 / 8)⌋₊) :
    ArithmeticFunction.vonMangoldt n * quarterWeight656 u n ≤ (K : ℝ) * G n := by
    have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr ((Nat.zero_le N).trans_lt (Finset.mem_Ioc.mp hn).1)
    have hn' := (Nat.le_floor_iff (mul_pos hu (Real.exp_pos _)).le).mp (Finset.mem_Ioc.mp hn).2
    have hlog := Real.log_le_log hn₀ hn'
    rw [Real.log_mul hu.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
    have ha : 0 ≤ 21 / 8 + Real.log u - Real.log n := by linarith only [hlog]
    have hb : 21 / 8 + Real.log u - Real.log n ≤ (z : ℝ) + 12 - Real.log n := by linarith only [hz]
    rw [forward_weight_factor hu hn₀]
    change _ ≤ (K : ℝ) * G n
    calc
      _ =
          C *
            ((n : ℝ) ^ (3 / 5 : ℝ) * ArithmeticFunction.vonMangoldt n *
              (21 / 8 + Real.log u - Real.log n) ^ 5) :=
        by ring
      _ ≤ _ :=
        mul_le_mul hK
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hb 5)
            (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
              ArithmeticFunction.vonMangoldt_nonneg))
          (by positivity) hK₀
  have hT : (∑ n ∈ Finset.Ioc N ⌊u * Real.exp (21 / 8)⌋₊, G n) ≤ ∑ n ∈ Finset.Ioc N B, G n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc le_rfl hB) ?_
    intro n hn _
    have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr ((Nat.zero_le N).trans_lt (Finset.mem_Ioc.mp hn).1)
    have h :=
      (Real.log_le_iff_le_exp hn₀).mpr ((Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans hBz)
    dsimp only [G]
    exact
      mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) ArithmeticFunction.vonMangoldt_nonneg)
        (pow_nonneg (sub_nonneg.mpr h) 5)
  have he :
    (∑ n ∈ Finset.Ioc N B, G n) =
      ∑ j ∈ Finset.range 6,
        (Nat.choose 5 j : ℝ) * (z : ℝ) ^ (5 - j) *
          (quarterMangoldtPrefix663 B j - quarterMangoldtPrefix663 N j) := by
    simp only [← mangoldt_moment_window hNB, Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.range 6)]
    apply Finset.sum_congr rfl
    intro n _
    norm_num only [G, Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceSub,
      Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]
    ring
  have hm :=
    Finset.sum_le_sum (s := Finset.range 6) fun j hj ↦
      mul_le_mul_of_nonneg_left (hM j hj)
        (mul_nonneg (Nat.cast_nonneg (Nat.choose 5 j))
          (pow_nonneg (Rat.cast_nonneg.mpr hz₀) (5 - j)))
  rw [← he] at hm
  simp only [Rat.cast_mul, Rat.cast_sum, Rat.cast_pow, Rat.cast_natCast]
  exact
    (Finset.sum_le_sum hS).trans
      (by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hT.trans hm) hK₀)

end PseudoPrime.PrimeTestBounds.MillerRabin
