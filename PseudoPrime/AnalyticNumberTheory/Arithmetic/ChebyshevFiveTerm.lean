/-
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from PrimeNumberTheoremAnd contributors; see the source attribution below.
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Log.Sum
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Elementary five-term Chebyshev estimates

The weight at `1, 2, 3, 5, 30` gives a lower bound for `psi` and an upper bound for
`psi x - psi (x / 6)`. The proof only uses logarithmic sum bounds and a periodic floor mask.
No prime enumeration, analytic hypothesis, or additional axiom is used.

Adapted from `PrimeNumberTheoremAnd/IEANTN/Chebyshev.lean` at commit
`a5154676af9aa3095150ee410cdda80555aa0642` of
https://github.com/AlexKontorovich/PrimeNumberTheoremAnd.
The logarithmic sum estimates are reused from mathlib. Keeping the constant term `-1`
in the five-term sum sharpens the difference upper bound from `-5` to `-7`.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

open Real Finsupp Finset
open ArithmeticFunction hiding log
open scoped Chebyshev

/-- The classical Chebyshev slope from the weights at `1, 2, 3, 5, 30`.
It is approximately `0.921292`; the logarithms remain exact in all bounds. -/
noncomputable def chebyshevSlope : ℝ :=
  (7 / 15) * log 2 + (3 / 10) * log 3 + (1 / 6) * log 5

/-- A rational enclosure of the classical Chebyshev slope, using mathlib log bounds. -/
theorem chebyshevSlope_bounds :
    92129 / 100000 ≤ chebyshevSlope ∧ chebyshevSlope ≤ 92130 / 100000 := by
  unfold chebyshevSlope
  constructor <;> nlinarith only [log_two_gt_d9, log_two_lt_d9, log_three_gt_d9,
    log_three_lt_d9, log_five_gt_d9, log_five_lt_d9]

private theorem Ioc_zero_eq_Icc (n : ℕ) : Ioc 0 n = Icc 1 n :=
  (Icc_add_one_left_eq_Ioc 0 n).symm

private noncomputable def T (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, log n

private theorem T_bounds {x : ℝ} (hx : 1 ≤ x) :
    x * log x - x + 1 - log x ≤ T x ∧
      T x ≤ x * log x - x + 1 + log x := by
  have hl := le_sum_log hx
  have hu := sum_log_le hx
  rw [Ioc_zero_eq_Icc] at hl hu
  dsimp [T]
  constructor <;> linarith only [hl, hu]

private theorem T.eq_sum_Lambda (x : ℝ) :
    T x = ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * ⌊x / n⌋₊ := by
  unfold T
  simp_rw [← log_apply, ← vonMangoldt_mul_zeta]
  rw [← Ioc_zero_eq_Icc, sum_Ioc_mul_zeta_eq_sum]
  simp [Nat.floor_div_natCast]

private noncomputable def E (ν : ℕ →₀ ℝ) (x : ℝ) : ℝ := ν.sum (fun m w ↦ w * ⌊ x / m ⌋₊)

private theorem T.weighted_eq_sum (ν : ℕ →₀ ℝ) (x : ℝ) :
    ν.sum (fun m w ↦ w * T (x / m)) = ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * E ν (x / n) := by
  simp_rw [T.eq_sum_Lambda, E, Finsupp.mul_sum]
  rw [← sum_finsetSum_comm]
  apply Finsupp.sum_congr fun y hy ↦ ?_
  rw [Finset.mul_sum]
  by_cases hy : y = 0
  · simp [hy]
  have one_le_y : 1 ≤ (y : ℝ) := by grind [Nat.one_le_cast]
  by_cases hx : x < 1
  · simp [hx, show x / y < 1 from div_lt_one (by linarith)|>.mpr (by linarith)]
  apply sum_subset_zero_on_sdiff
  · apply Icc_subset_Icc_right
    gcongr
    exact div_le_self (by linarith) one_le_y
  · intro t ht
    simp only [mem_sdiff, mem_Icc, not_and, not_le] at ht
    simp only [mul_eq_zero, Nat.cast_eq_zero, Nat.floor_eq_zero]
    right
    right
    apply div_lt_one (by linarith)|>.mpr
    have := ht.2 ht.1.1
    apply div_lt_iff₀ (by simp; grind)|>.mpr
    rw [Nat.floor_lt <| div_nonneg (by linarith) (by linarith)] at this
    have := div_lt_iff₀ (by linarith)|>.mp this
    rwa [mul_comm] at this
  · grind

private noncomputable def ν : ℕ →₀ ℝ :=
  single 1 1 - single 2 1 - single 3 1 - single 5 1 + single 30 1

/-- Unfold `ν.sum (fun m w ↦ w * f m)` into its five-term expansion.
This avoids repeating the `sum_add_index` / `sum_sub_index` chain every time
we need to compute a `ν`-weighted sum. -/
private lemma ν_sum_mul (f : ℕ → ℝ) :
    ν.sum (fun m w ↦ w * f m) = f 1 - f 2 - f 3 - f 5 + f 30 := by
  rw [ν, sum_add_index (by simp) (by intros; ring)]
  grind only [sum_single_index, sum_sub_index]

/-- Unfold `E ν y` into an explicit expression in terms of floors of `y / k`.
This is the key formula repeatedly used to analyse `E ν`. -/
private lemma E_nu_expand (y : ℝ) :
    E ν y = ⌊y⌋₊ - ⌊y / 2⌋₊ - ⌊y / 3⌋₊ - ⌊y / 5⌋₊ + ⌊y / 30⌋₊ := by
  rw [E, ν, sum_add_index' (by grind) (by grind)]
  grind [sum_single_index, sum_sub_index]

/-- The classical sandwich `k * ⌊y/k⌋₊ ≤ ⌊y⌋₊ < k * ⌊y/k⌋₊ + k` for `k ≥ 1` and `y ≥ 0`. -/
private lemma floor_div_bounds {y : ℝ} (hy : 0 ≤ y) {k : ℕ} (hk : 1 ≤ k) :
    k * ⌊y / k⌋₊ ≤ ⌊y⌋₊ ∧ ⌊y⌋₊ < k * ⌊y / k⌋₊ + k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hdivnn : 0 ≤ y / k := div_nonneg hy hk'.le
  refine ⟨Nat.le_floor ?_, ?_⟩
  · push_cast
    have := Nat.floor_le hdivnn
    calc ((k : ℝ) * ⌊y / k⌋₊) = k * (y / k) - k * (y / k - ⌊y / k⌋₊) := by ring
      _ ≤ k * (y / k) := by nlinarith [Nat.floor_le hdivnn]
      _ = y := mul_div_cancel₀ _ hk'.ne'
  · have hlt : y / k < ⌊y / k⌋₊ + 1 := Nat.lt_floor_add_one (y / k)
    have hy_lt : y < (k : ℝ) * (⌊y / k⌋₊ + 1) := by linarith [(div_lt_iff₀ hk').mp hlt]
    have : (⌊y⌋₊ : ℝ) < (k : ℝ) * (⌊y / k⌋₊ + 1) := (Nat.floor_le hy).trans_lt hy_lt
    exact_mod_cast this

private theorem E_nu_eq_one (x : ℝ) (hx : x ∈ Set.Ico 1 6) : E ν x = 1 := by
  obtain ⟨h1, h6⟩ := hx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  simp only [E_nu_expand, Nat.floor_eq_zero.mpr (by linarith : x / 30 < 1)]
  have hflb : 1 ≤ ⌊x⌋₊ := by rwa [Nat.one_le_floor_iff]
  have hfub : ⌊x⌋₊ ≤ 5 := Nat.lt_succ_iff.mp (Nat.floor_lt' (by grind) |>.mpr h6)
  have h2 := floor_div_bounds hx0 (k := 2) (by norm_num)
  have h3 := floor_div_bounds hx0 (k := 3) (by norm_num)
  have h5 := floor_div_bounds hx0 (k := 5) (by norm_num)
  push_cast at h2 h3 h5
  rw [show ⌊x⌋₊ = ⌊x / 2⌋₊ + ⌊x / 3⌋₊ + ⌊x / 5⌋₊ + 1 by omega]
  grind

private theorem E_nu_period (x : ℝ) (hx : x ≥ 0) : E ν (x + 30) = E ν x := by
  have h (k : ℝ) : (x + 30) / k = x / k + (30 / k) := by ring
  simp_rw [E_nu_expand, h 2, h 3, h 5, h 30]
  norm_num
  repeat rw [Nat.floor_add_ofNat (by positivity)]
  rw [Nat.floor_add_one (by positivity)]
  grind

private theorem E_nu_bound (x : ℝ) (hx : x ≥ 0) : 0 ≤ E ν x ∧ E ν x ≤ 1 := by
  have : ∀ y, 0 ≤ y → y < 30 → 0 ≤ E ν y ∧ E ν y ≤ 1 := fun y hy0 hy30 ↦ by
    simp only [E_nu_expand, Nat.floor_eq_zero.mpr (by linarith : y / 30 < 1),
      Nat.cast_zero, add_zero]
    have h2 := floor_div_bounds hy0 (k := 2) (by norm_num)
    have h3 := floor_div_bounds hy0 (k := 3) (by norm_num)
    have h5 := floor_div_bounds hy0 (k := 5) (by norm_num)
    push_cast at h2 h3 h5
    have hfy : ⌊y⌋₊ < 30 := Nat.floor_lt' (by norm_num) |>.mpr (by exact_mod_cast hy30)
    have hlb : ⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ ≤ ⌊y⌋₊ := by omega
    have hub : ⌊y⌋₊ ≤ ⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ + 1 := by omega
    have hlb' : ((⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by
      exact_mod_cast hlb
    have hub' : ((⌊y⌋₊ : ℕ) : ℝ) ≤ ((⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ + 1 : ℕ) : ℝ) := by
      exact_mod_cast hub
    push_cast at hlb' hub'
    refine ⟨by linarith, by linarith⟩
  let y := x - ⌊x / 30⌋₊ * 30
  have hy : 0 ≤ y ∧ y < 30 := ⟨by linarith [Nat.floor_le (by positivity : 0 ≤ x/30)], by
    linarith [Nat.lt_floor_add_one (x/30)]⟩
  have hxy : E ν x = E ν y := by
    have : x = y + ⌊x/30⌋₊ * 30 := by ring
    rw [this]; induction ⌊x/30⌋₊ with
    | zero => simp
    | succ n ih => simp [add_mul, ← add_assoc, E_nu_period _ (by linarith : y + n * 30 ≥ 0), ih]
  exact hxy ▸ this y hy.1 hy.2

private noncomputable def U (x : ℝ) : ℝ := ν.sum (fun m w ↦ w * T (x/m))

private theorem psi_ge_weighted (x : ℝ) (hx : x > 0) : ψ x ≥ U x := by
  unfold U Chebyshev.psi
  rw [T.weighted_eq_sum, ← Ioc_zero_eq_Icc]
  gcongr with i
  have := E_nu_bound (x / i) (div_nonneg hx.le (by simp))
  grw [this.2, mul_one]

private theorem psi_diff_le_weighted (x : ℝ) (hx : x > 0) : ψ x - ψ (x / 6) ≤ U x := by
  unfold U Chebyshev.psi
  rw [T.weighted_eq_sum, ← Ioc_zero_eq_Icc]
  have subset : Ioc 0 ⌊x / 6⌋₊ ⊆ Ioc 0 ⌊x⌋₊ := by
    apply Ioc_subset_Ioc_right
    gcongr
    exact div_le_self hx.le (by norm_num)
  rw [← sum_sdiff_eq_sub subset, ← sum_sdiff subset]
  refine le_add_of_le_of_nonneg (sum_le_sum fun n hn ↦ ?_)
    (sum_nonneg fun n hn ↦ mul_nonneg vonMangoldt_nonneg ?_)
  · rw [E_nu_eq_one, mul_one]
    simp_all only [gt_iff_lt, Finset.mem_sdiff, Finset.mem_Ioc, not_and, not_le, Set.mem_Ico]
    refine ⟨one_le_div (by simp; grind)|>.mpr <| Nat.le_floor_iff hx.le |>.mp hn.1.2, ?_⟩
    have := hn.2 hn.1.1
    apply div_lt_iff₀ (by simp; grind)|>.mpr
    rw [Nat.floor_lt <| div_nonneg (by linarith) (by linarith)] at this
    have := div_lt_iff₀ (by linarith)|>.mp this
    rwa [mul_comm] at this
  · exact E_nu_bound _ (div_nonneg hx.le (by simp))|>.1

private theorem U_bounds {x : ℝ} (hx : 30 ≤ x) :
    chebyshevSlope * x - 5 * log x + 5 ≤ U x ∧
      U x ≤ chebyshevSlope * x + 5 * log x - 7 := by
  have hxpos : 0 < x := by linarith only [hx]
  have h1 := T_bounds (x := x) (by linarith only [hx])
  have h2 := T_bounds (x := x / 2) (by linarith only [hx])
  have h3 := T_bounds (x := x / 3) (by linarith only [hx])
  have h5 := T_bounds (x := x / 5) (by linarith only [hx])
  have h30 := T_bounds (x := x / 30) (by linarith only [hx])
  have hlog30 : log 30 = log 2 + log 3 + log 5 := by
    rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, log_mul (by norm_num) (by norm_num),
      log_mul (by norm_num) (by norm_num)]
  simp only [log_div hxpos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at h2
  simp only [log_div hxpos.ne' (by norm_num : (3 : ℝ) ≠ 0)] at h3
  simp only [log_div hxpos.ne' (by norm_num : (5 : ℝ) ≠ 0)] at h5
  simp only [log_div hxpos.ne' (by norm_num : (30 : ℝ) ≠ 0), hlog30] at h30
  rw [U, ν_sum_mul]
  norm_num only [Nat.cast_one, Nat.cast_ofNat, div_one]
  unfold chebyshevSlope
  constructor <;> nlinarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h5.1, h5.2,
    h30.1, h30.2, log_two_gt_d9, log_three_gt_d9, log_five_gt_d9]

/-- The unconditional five-term lower bound for `psi` on `x ≥ 30`.
The periodic floor mask lies in `[0, 1]`, so its Mangoldt sum is bounded by `psi`. -/
theorem psi_lower_fiveTerm {x : ℝ} (hx : 30 ≤ x) :
    chebyshevSlope * x - 5 * log x + 5 ≤ Chebyshev.psi x :=
  (U_bounds hx).1.trans (psi_ge_weighted x (by linarith only [hx]))

/-- The unconditional five-term upper bound for the scale-six increment of `psi`.
The mask is one on `[1, 6)`; retaining the constant term improves the usual `-5` to `-7`. -/
theorem psi_diff_upper_fiveTerm {x : ℝ} (hx : 30 ≤ x) :
    Chebyshev.psi x - Chebyshev.psi (x / 6) ≤
      chebyshevSlope * x + 5 * log x - 7 :=
  (psi_diff_le_weighted x (by linarith only [hx])).trans (U_bounds hx).2

end PseudoPrime.AnalyticNumberTheory.Arithmetic
