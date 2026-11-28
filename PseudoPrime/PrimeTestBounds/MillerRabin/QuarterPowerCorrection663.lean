/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterProfileTail663
import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3

/-! # Prime-power correction for the section 137 Euler recovery -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Candidate pairs for the correction, obtained from small bases and
exponents. Only powers in the fixed window enter the arithmetic sum. -/
private def correctionPairs : Finset (ℕ × ℕ) :=
  (((Finset.Icc 2 1300).filter Nat.Prime) ×ˢ (Finset.Icc 2 20)).filter fun pk ↦
    107584 < pk.1 ^ pk.2 ∧ pk.1 ^ pk.2 ≤ 1600000

/-- The natural indices of the finite prime-power correction in (137.26). -/
def quarterCorrectionSet663 : Finset ℕ :=
  correctionPairs.image fun pk ↦ pk.1 ^ pk.2

attribute [local irreducible] correctionPairs

/-- The main kernel support through radius 337 lies below 1600000. -/
private theorem support_lt_663 {r t : ℝ} (hr : r ∈ Set.Icc 328 337) (ht : 0 < t)
    (h : Real.log (t / r ^ 2) ≤ 21 / 8) : t < 1600000 := by
  have h₀ := (by norm_num only : (0 : ℝ) < 328).trans_le hr.1
  have hx := sq_pos_of_pos h₀
  have hU := pow_le_pow_left₀ h₀.le hr.2 2
  have hc :=
    (Analysis.rationalLogIntervalCheck_sound (N := 14) (j := 4) (n := 20) (lo := 21 / 8) (hi := 3)
        (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have he := (Real.le_log_iff_exp_le (by norm_num only : (0 : ℝ) < 14)).mp hc
  have ht' := (div_le_iff₀ hx).mp ((Real.log_le_iff_le_exp (div_pos ht hx)).mp h)
  have hmul := mul_le_mul he hU hx.le (by norm_num only : (0 : ℝ) ≤ 14)
  linarith only [ht', hmul]

/-- Every retained prime power of exponent at least two lies in the fixed
correction set if it is above the tested cutoff and inside the main support. -/
theorem quarter_power_in_window_663 {r : ℝ} (hr : r ∈ Set.Icc 328 337) {p k : ℕ} (hp : p.Prime)
    (hk : 2 ≤ k) (hlo : r ^ 2 < ((p ^ k : ℕ) : ℝ))
    (hhi : Real.log (((p ^ k : ℕ) : ℝ) / r ^ 2) ≤ 21 / 8) : p ^ k ∈ quarterCorrectionSet663 := by
  have hUpper := support_lt_663 hr (Nat.cast_pos.mpr (pow_pos hp.pos _)) hhi
  have hn : p ^ k ≤ 1600000 := Nat.cast_le.mp hUpper.le
  have hbase : p ≤ 1300 := by
    have hsq := Nat.pow_le_pow_right hp.pos hk
    by_contra! H
    have h := Nat.pow_le_pow_left (show 1301 ≤ p from H) 2
    exact (by decide : ¬1301 ^ 2 ≤ 1600000) (h.trans (hsq.trans hn))
  have hkp : k ≤ 20 := by
    by_contra! H
    have h :=
      (Nat.pow_le_pow_right (by decide : 0 < 2) (show 21 ≤ k from H)).trans
        (Nat.pow_le_pow_left hp.two_le k)
    exact (by decide : ¬2 ^ 21 ≤ 1600000) (h.trans hn)
  have hs : (107584 : ℝ) ≤ r ^ 2 := by
    rw [show (107584 : ℝ) = 328 ^ 2 by norm_num only]
    exact pow_le_pow_left₀ (by norm_num only) hr.1 2
  have hm : (p, k) ∈ correctionPairs := by
    rw [correctionPairs, Finset.mem_filter, Finset.mem_product]
    refine
      ⟨⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hbase⟩, hp⟩,
          Finset.mem_Icc.mpr ⟨hk, hkp⟩⟩,
        ?_⟩
    exact ⟨Nat.cast_lt.mp (hs.trans_lt hlo), hn⟩
  simp only [quarterCorrectionSet663, Finset.mem_image]
  exact ⟨(p, k), hm, rfl⟩

/-- At the quarter-square radii through 663/2, every retained power inside
the support and above the tested cutoff belongs to the correction set. -/
theorem quarter_power_in_correction_663 {r : ℝ} (hr : r ∈ Set.Icc 328 (663 / 2)) {p k : ℕ}
    (hp : p.Prime) (hk : 2 ≤ k) (hlo : r ^ 2 < ((p ^ k : ℕ) : ℝ))
    (hhi : Real.log (((p ^ k : ℕ) : ℝ) / r ^ 2) ≤ 21 / 8) : p ^ k ∈ quarterCorrectionSet663 := by
  exact quarter_power_in_window_663 ⟨hr.1, hr.2.trans (by norm_num only)⟩ hp hk hlo hhi

/-- Since the reflected correction is nonnegative as a cost, any retained
set contained in the fixed power window can pay the same uniform cost. -/
theorem quarter_correction_mono_663 {K : Finset ℕ} (hK : K ⊆ quarterCorrectionSet663) :
    (∑ n ∈ K, 80 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(8 / 5) : ℝ))) ≤
      ∑ n ∈ quarterCorrectionSet663,
        80 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(8 / 5) : ℝ)) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hK
  intro n _ _
  positivity

/-- Prime-prefix agreement forces trace three on the entire correction
window, since every generating prime is below the squared radius. -/
theorem quarter_correction_trace_663 {p q s : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) {r : ℝ} (hr : 328 ≤ r)
    (ha : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) {n : ℕ} (hn : n ∈ quarterCorrectionSet663) :
    3 - ((a n).re + (b n).re + (c n).re) = 0 := by
  simp only [quarterCorrectionSet663, Finset.mem_image] at hn
  obtain ⟨⟨m, k⟩, hm, rfl⟩ := hn
  simp only [correctionPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hm
  have hcut : (m : ℝ) ≤ r ^ 2 :=
    (Nat.cast_le.mpr hm.1.1.1.2).trans
      ((by norm_num only : (1300 : ℝ) ≤ 328 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hr 2))
  have hpow {d : ℕ} (χ : DirichletCharacter ℂ d) (h : χ m = 1) : χ (↑(m ^ k) : ZMod d) = 1 := by
    rw [Nat.cast_pow, map_pow, h, one_pow]
  rw [hpow a (ha m hm.1.1.2 hcut), hpow b (hb m hm.1.1.2 hcut), hpow c (hc m hm.1.1.2 hcut),
    Complex.one_re]
  norm_num only

/-- The fixed correction pays for any retained set of known passing
prime powers in the main support. The uncorrected forward gains are kept. -/
theorem quarter_power_recovery_of_tail {r : ℝ} (hr : r ∈ Set.Icc 328 337) (a : ℕ → ℝ)
    (ha : ∀ n, a n ∈ Set.Icc 0 4) (K : Finset ℕ) (hK : ∀ n ∈ K, r ^ 2 < (n : ℝ))
    (hU : ∀ n ∈ K, Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8)
    (hpow : ∀ n ∈ K, ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ n = p ^ k) (hpass : ∀ n ∈ K, a n = 0) {E : ℝ}
    {T : ℝ}
    (hmain :
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterDensity663 n) -
          ∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, ArithmeticFunction.vonMangoldt n * quarterDensity663 n ≤
        T)
    (hE :
      (∑ n ∈ quarterCorrectionSet663,
          80 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(8 / 5) : ℝ))) ≤
        E) :
    let w := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n *
        ((4 - a n) *
            (if Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n else 0) -
          a n * quarterDensity663 n)
    (-4 * T) - E + (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n)) ≤
      (∑' n : ℕ, w n) - ∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, w n := by
  intro w
  have hsub : K ⊆ quarterCorrectionSet663 := by
    intro n hn
    obtain ⟨p, k, hp, hk, rfl⟩ := hpow n hn
    exact quarter_power_in_window_663 hr hp hk (hK _ hn) (hU _ hn)
  have hcap := (quarter_correction_mono_663 hsub).trans hE
  have h := quarter_euler_retained_of_tail hr.1 a ha K hK hpass hmain
  dsimp only at h
  have hf :
    (∑ n ∈ K,
        4 *
          (ArithmeticFunction.vonMangoldt n *
            (if Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n else 0))) =
      ∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n) :=
    Finset.sum_congr rfl fun n hn ↦ by rw [ite_eq_left (hU n hn)]
  rw [hf] at h
  dsimp only [w]
  linarith only [h, hcap]

/-- Recover prime powers with the certified quarter-square tail bound. -/
theorem quarter_power_recovery_663 (hRH : RiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc 328 (663 / 2)) (a : ℕ → ℝ) (ha : ∀ n, a n ∈ Set.Icc 0 4) (K : Finset ℕ)
    (hK : ∀ n ∈ K, r ^ 2 < (n : ℝ)) (hU : ∀ n ∈ K, Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8)
    (hpow : ∀ n ∈ K, ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ n = p ^ k) (hpass : ∀ n ∈ K, a n = 0) {E : ℝ}
    (hE :
      (∑ n ∈ quarterCorrectionSet663,
          80 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(8 / 5) : ℝ))) ≤
        E) :
    let w := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n *
        ((4 - a n) *
            (if Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n else 0) -
          a n * quarterDensity663 n)
    (-0.010816 : ℝ) - E +
        (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n)) ≤
      (∑' n : ℕ, w n) - ∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, w n := by
  have h :=
    quarter_power_recovery_of_tail ⟨hr.1, hr.2.trans (by norm_num only)⟩ a ha K hK hU hpow hpass
      (quarter_signed_tail_663 hRH hr) hE
  dsimp only at h ⊢
  linarith only [h]

/-- Integer lower bounds on bases in each exponent fiber. -/
private def baseLo : ℕ → ℕ
  | 2 => 329
  | 3 => 48
  | 4 => 19
  | 5 => 11
  | 6 => 7
  | 7 => 6
  | 8 => 5
  | 9 | 10 => 4
  | 11 | 12 | 13 | 14 | 15 | 16 => 3
  | _ => 2

/-- Integer upper bounds on bases in each exponent fiber. -/
private def baseHi : ℕ → ℕ
  | 2 => 1264
  | 3 => 116
  | 4 => 35
  | 5 => 17
  | 6 => 10
  | 7 => 7
  | 8 => 5
  | 9 | 10 => 4
  | 11 | 12 | 13 => 3
  | _ => 2

/-- Only the 19 power cutoffs need checking. Monotonicity in the base
then places every pair in its integer interval. -/
private theorem base_box {p k : ℕ} (hk : k ∈ Finset.Icc 2 20) (hl : 107584 < p ^ k)
    (hu : p ^ k ≤ 1600000) : p ∈ Finset.Icc (baseLo k) (baseHi k) := by
  have h :
    ∀ i : Fin 19,
      (baseLo (i.val + 2) - 1) ^ (i.val + 2) ≤ 107584 ∧
        1600000 < (baseHi (i.val + 2) + 1) ^ (i.val + 2) := by
    decide +kernel
  have h₂ := (Finset.mem_Icc.mp hk).1
  have h₂₀ := (Finset.mem_Icc.mp hk).2
  have hlt : k < 19 + 2 := Nat.lt_succ_of_le h₂₀
  let i : Fin 19 := ⟨k - 2, Nat.sub_lt_left_of_lt_add h₂ hlt⟩
  have hi : i.val + 2 = k := Nat.sub_add_cancel h₂
  have hb := h i
  rw [hi] at hb
  apply Finset.mem_Icc.mpr
  constructor
  · by_contra! hp
    exact (not_le_of_gt hl) ((Nat.pow_le_pow_left (Nat.le_sub_one_of_lt hp) k).trans hb.1)
  · by_contra! hp
    exact (not_le_of_gt hb.2) ((Nat.pow_le_pow_left (Nat.succ_le_of_lt hp) k).trans hu)

/-- The second coordinate fixes each fiber, so projection into the
short interval of bases bounds the fiber cardinality. -/
private theorem correction_fiber_le {k : ℕ} (hk : k ∈ Finset.Icc 2 20) :
    (correctionPairs.filter (fun pk ↦ pk.2 = k)).card ≤ baseHi k + 1 - baseLo k := by
  rw [← Nat.card_Icc]
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro pk hm
    have hp := Finset.mem_filter.mp hm
    have hb := hp.1
    simp only [correctionPairs, Finset.mem_filter, Finset.mem_product] at hb
    rw [← hp.2] at hk ⊢
    exact base_box hk hb.2.1 hb.2.2
  · intro pk hp qk hq he
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    exact Prod.ext he (hp'.trans hq'.symm)

/-- In the exponent-two fiber, mapping an odd base to its half quotient
halves the integer interval used for the cardinality estimate. -/
private theorem square_fiber_le : (correctionPairs.filter (fun pk ↦ pk.2 = 2)).card ≤ 469 := by
  have hp (pk : ℕ × ℕ) (hm : pk ∈ correctionPairs.filter (fun pk ↦ pk.2 = 2)) :
    pk.2 = 2 ∧ pk.1.Prime ∧ 329 ≤ pk.1 ∧ pk.1 ≤ 1264 := by
    have h := Finset.mem_filter.mp hm
    have hb := h.1
    simp only [correctionPairs, Finset.mem_filter, Finset.mem_product] at hb
    rw [h.2] at hb
    have hh := Finset.mem_Icc.mp (base_box (by decide : 2 ∈ Finset.Icc 2 20) hb.2.1 hb.2.2)
    exact ⟨h.2, hb.1.1.2, hh.1, hh.2⟩
  have hcard : (Finset.Icc 164 632).card = 469 := by rw [Nat.card_Icc]
  rw [← hcard]
  apply Finset.card_le_card_of_injOn (fun pk ↦ pk.1 / 2)
  · intro pk hk
    have h := hp pk hk
    exact
      Finset.mem_Icc.mpr
        ⟨(Nat.div_le_div_right h.2.2.1 : 329 / 2 ≤ pk.1 / 2),
          (Nat.div_le_div_right h.2.2.2 : pk.1 / 2 ≤ 1264 / 2)⟩
  · intro pk hk qk hq he
    have hp' := hp pk hk
    have hq' := hp qk hq
    have hodd (m : ℕ) (hm : m.Prime) (hlo : 329 ≤ m) : m % 2 = 1 :=
      Nat.odd_iff.mp (hm.odd_of_ne_two (ne_of_gt ((by decide : 2 < 329).trans_le hlo)))
    have hpEq := Nat.div_add_mod pk.1 2
    have hqEq := Nat.div_add_mod qk.1 2
    change pk.1 / 2 = qk.1 / 2 at he
    rw [hodd _ hp'.2.1 hp'.2.2.1, he] at hpEq
    exact
      Prod.ext
        (hpEq.symm.trans
          (by
            rw [hodd _ hq'.2.1 hq'.2.2.1] at hqEq
            exact hqEq))
        (hp'.1.trans hq'.1.symm)

/-- Uniform cardinality allowances for the exponent fibers. -/
private def fiberCap (k : ℕ) : ℕ :=
  if k = 2 then 469 else baseHi k + 1 - baseLo k

/-- Count squares by odd bases, and the other powers by their integer
base intervals. -/
private theorem correction_fiber_cap {k : ℕ} (hk : k ∈ Finset.Icc 2 20) :
    (correctionPairs.filter (fun pk ↦ pk.2 = k)).card ≤ fiberCap k := by
  by_cases he : k = 2
  · rw [he, fiberCap, ite_eq_left (show (2 : ℕ) = 2 from rfl)]
    exact square_fiber_le
  · rw [fiberCap, ite_eq_right he]
    exact correction_fiber_le hk

/-- The size bound comes from the 19 integer intervals and does not
enumerate the prime bases or the pairs in the correction set. -/
private theorem correction_card : quarterCorrectionSet663.card ≤ 578 := by
  have he : correctionPairs.filter (fun pk ↦ pk.2 ∈ Finset.Icc 2 20) = correctionPairs := by
    apply Finset.filter_true_of_mem
    intro pk hk
    simp only [correctionPairs, Finset.mem_filter, Finset.mem_product] at hk
    exact hk.1.2
  have hsum := Finset.sum_card_fiberwise_eq_card_filter correctionPairs (Finset.Icc 2 20) Prod.snd
  rw [he] at hsum
  have hb := Finset.sum_le_sum (s := Finset.Icc 2 20) fun _ hk ↦ correction_fiber_cap hk
  have hc : (∑ j ∈ Finset.Icc 2 20, fiberCap j) ≤ 578 := by decide +kernel
  have hd : correctionPairs.card ≤ 578 := hsum.symm.le.trans (hb.trans hc)
  rw [quarterCorrectionSet663]
  exact Finset.card_image_le.trans hd

/-- Each correction atom has Mangoldt weight at most 7.2 and its
inverse power is at most 8.9 times ten to the minus nine. -/
private theorem correction_atom_cap {n : ℕ} (hn : n ∈ quarterCorrectionSet663) :
    80 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(8 / 5) : ℝ)) ≤
      80 * (7.2 * 0.0000000089) := by
  simp only [quarterCorrectionSet663, Finset.mem_image] at hn
  obtain ⟨⟨p, k⟩, hm, rfl⟩ := hn
  simp only [correctionPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hm
  have hp := hm.1.1.2
  have hk : k ≠ 0 := Nat.ne_of_gt ((by decide : 0 < 2).trans_le hm.1.2.1)
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1300) (j := 11) (n := 24) (lo := 7) (hi := 7.2)
        (by decide +kernel)).2
  have hnR : (107584 : ℝ) ≤ ↑(p ^ k) := Nat.cast_le.mpr hm.2.1.le
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 107584) (p := 8) (d :=
        5) (lo := 0) (hi := 0.0000000089) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hl hpow
  have hpLog := (Real.log_le_log (Nat.cast_pos.mpr hp.pos) (Nat.cast_le.mpr hm.1.1.1.2)).trans hl
  have hdecay :=
    (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 107584) hnR
          (by norm_num only : (-(8 / 5) : ℝ) ≤ 0)).trans
      hpow
  rw [ArithmeticFunction.vonMangoldt_apply_pow hk, ArithmeticFunction.vonMangoldt_apply_prime hp]
  exact
    mul_le_mul_of_nonneg_left
      (mul_le_mul (show Real.log p ≤ 7.2 by linarith only [hpLog])
        (show ((p ^ k : ℕ) : ℝ) ^ (-(8 / 5) : ℝ) ≤ 0.0000000089 by linarith only [hdecay])
        (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by norm_num only))
      (by norm_num only)

/-- A uniform rational upper bound for the finite correction, obtained
without prime enumeration. -/
theorem quarter_correction_upper_663 :
    (∑ n ∈ quarterCorrectionSet663,
        80 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(8 / 5) : ℝ))) ≤
      0.00297 := by
  refine (Finset.sum_le_sum (fun n hn ↦ correction_atom_cap hn)).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have h : (quarterCorrectionSet663.card : ℝ) ≤ 578 := by exact_mod_cast correction_card
  linarith only [h]

private def correctionPrimeCount (k : ℕ) : ℕ :=
  ((Finset.Icc (baseLo k) (baseHi k)).filter (fun p ↦ 2 ≤ p ∧ p.minFac = p)).card

private theorem correction_fiber_prime_count {k : ℕ} (hk : k ∈ Finset.Icc 2 20) :
    (correctionPairs.filter (fun pk ↦ pk.2 = k)).card ≤ correctionPrimeCount k := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro pk hm
    obtain ⟨hm, he⟩ := Finset.mem_filter.mp hm
    simp only [correctionPairs, Finset.mem_filter, Finset.mem_product] at hm
    rw [← he] at hk ⊢
    exact Finset.mem_filter.mpr ⟨base_box hk hm.2.1 hm.2.2, Nat.prime_def_minFac.mp hm.1.1.2⟩
  · intro pk hp qk hq he
    exact Prod.ext he ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)

set_option maxRecDepth 8192 in
-- The closed check counts primes in just the nineteen base intervals.
private theorem correction_prime_counts :
    (∑ k ∈ Finset.Icc 2 20, correctionPrimeCount k) ≤ 171 := by decide +kernel

private theorem correction_card_sharp : quarterCorrectionSet663.card ≤ 171 := by
  have he : correctionPairs.filter (fun pk ↦ pk.2 ∈ Finset.Icc 2 20) = correctionPairs := by
    apply Finset.filter_true_of_mem
    intro pk hk
    simp only [correctionPairs, Finset.mem_filter, Finset.mem_product] at hk
    exact hk.1.2
  have hsum := Finset.sum_card_fiberwise_eq_card_filter correctionPairs (Finset.Icc 2 20) Prod.snd
  rw [he] at hsum
  have hb := Finset.sum_le_sum (s := Finset.Icc 2 20) fun _ hk ↦ correction_fiber_prime_count hk
  exact Finset.card_image_le.trans (hsum.symm.le.trans (hb.trans correction_prime_counts))

/-- For the bridge through log 663, count the actual prime-power candidates
and use the same logarithm and decay bounds for every retained atom. -/
theorem quarter_bridge_correction_upper :
    (∑ n ∈ quarterCorrectionSet663,
        80 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(8 / 5) : ℝ))) ≤
      0.000877 := by
  refine (Finset.sum_le_sum (fun n hn ↦ correction_atom_cap hn)).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have h : (quarterCorrectionSet663.card : ℝ) ≤ 171 := by exact_mod_cast correction_card_sharp
  linarith only [h]

/-- Through radius 337, a retained set of prime powers in the main support
has zero trace deficit and its total correction cost is at most 0.00297. -/
theorem quarter_retained_window_663 {p q s : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) {r : ℝ} (hr : r ∈ Set.Icc 328 337)
    (ha : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) (K : Finset ℕ)
    (hK : ∀ n ∈ K, r ^ 2 < (n : ℝ)) (hU : ∀ n ∈ K, Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8)
    (hpow : ∀ n ∈ K, ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ n = p ^ k) :
    (∀ n ∈ K, 3 - ((a n).re + (b n).re + (c n).re) = 0) ∧
      (∑ n ∈ K, 80 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(8 / 5) : ℝ))) ≤ 0.00297 := by
  have hsub : K ⊆ quarterCorrectionSet663 := by
    intro n hn
    obtain ⟨p, k, hp, hk, rfl⟩ := hpow n hn
    exact quarter_power_in_window_663 hr hp hk (hK _ hn) (hU _ hn)
  exact
    ⟨fun _ hn ↦ quarter_correction_trace_663 a b c hr.1 ha hb hc (hsub hn),
      (quarter_correction_mono_663 hsub).trans quarter_correction_upper_663⟩

/-- For pair characters agreeing on the tested primes, the explicit
correction gives a numerical lower bound while retaining the forward gains. -/
theorem quarter_recovery_trace_663 (hRH : RiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc 328 (663 / 2)) {p q s : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (ha : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) (K : Finset ℕ)
    (hK : ∀ n ∈ K, r ^ 2 < (n : ℝ)) (hU : ∀ n ∈ K, Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8)
    (hpow : ∀ n ∈ K, ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ n = p ^ k) :
    let d := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
    let w := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n *
        ((4 - d n) *
            (if Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n else 0) -
          d n * quarterDensity663 n)
    (-0.013786 : ℝ) +
        (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n)) ≤
      (∑' n : ℕ, w n) - ∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, w n := by
  intro d w
  have hd (n : ℕ) : d n ∈ Set.Icc 0 4 :=
    ⟨sub_nonneg.mpr (ht n).2, by
      dsimp only [d]; linarith only [(ht n).1]⟩
  have hwide : r ∈ Set.Icc 328 337 := ⟨hr.1, hr.2.trans (by norm_num only)⟩
  have hpass := (quarter_retained_window_663 a b c hwide ha hb hc K hK hU hpow).1
  have h := quarter_power_recovery_663 hRH hr d hd K hK hU hpow hpass quarter_correction_upper_663
  have he : (-0.010816 : ℝ) - 0.00297 = -0.013786 := by norm_num only
  simpa only [he] using h

/-- Recover prime powers on the quarter-square bridge using the sharper
correction obtained by counting the candidates in the fixed window. -/
theorem quarter_bridge_recovery {p q s : ℕ} (hRH : RiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc 328 (663 / 2)) (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ s) (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (ha : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) (K : Finset ℕ)
    (hK : ∀ n ∈ K, r ^ 2 < (n : ℝ)) (hU : ∀ n ∈ K, Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8)
    (hpow : ∀ n ∈ K, ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ n = p ^ k) :
    let d := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
    let w := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n *
        ((4 - d n) *
            (if Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n else 0) -
          d n * quarterDensity663 n)
    (-0.011693 : ℝ) +
        (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n)) ≤
      (∑' n : ℕ, w n) - ∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, w n := by
  intro d w
  have hd (n : ℕ) : d n ∈ Set.Icc 0 4 :=
    ⟨sub_nonneg.mpr (ht n).2, by
      dsimp only [d]; linarith only [(ht n).1]⟩
  have hwide : r ∈ Set.Icc 328 337 := ⟨hr.1, hr.2.trans (by norm_num only)⟩
  have hpass := (quarter_retained_window_663 a b c hwide ha hb hc K hK hU hpow).1
  have h :=
    quarter_power_recovery_of_tail hwide d hd K hK hU hpow hpass (quarter_signed_tail_663 hRH hr)
      quarter_bridge_correction_upper
  dsimp only at h ⊢
  linarith only [h]

/-- Recover prime powers at Gaussian radii through 333, retaining the tighter
signed tail allowance through radius 332. -/
theorem quarter_recovery_trace_gaussian (hRH : RiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc (663 / 2) 333) {p q s : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (ha : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) (K : Finset ℕ)
    (hK : ∀ n ∈ K, r ^ 2 < (n : ℝ)) (hU : ∀ n ∈ K, Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8)
    (hpow : ∀ n ∈ K, ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ n = p ^ k) :
    let d := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
    let w := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n *
        ((4 - d n) *
            (if Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n else 0) -
          d n * quarterDensity663 n)
    (if r ≤ 332 then -0.014026 else -0.014534 : ℝ) +
        (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n)) ≤
      (∑' n : ℕ, w n) - ∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, w n := by
  intro d w
  have hd (n : ℕ) : d n ∈ Set.Icc 0 4 :=
    ⟨sub_nonneg.mpr (ht n).2, by
      dsimp only [d]; linarith only [(ht n).1]⟩
  have hwide : r ∈ Set.Icc 328 337 :=
    ⟨(by norm_num only : (328 : ℝ) ≤ 663 / 2).trans hr.1, hr.2.trans (by norm_num only)⟩
  have hpass := (quarter_retained_window_663 a b c hwide ha hb hc K hK hU hpow).1
  have htail :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterDensity663 n) -
        ∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, ArithmeticFunction.vonMangoldt n * quarterDensity663 n ≤
      (if r ≤ 332 then 0.002764 else 0.002891) := by
    by_cases hs : r ≤ 332
    · rw [ite_eq_left hs]
      exact quarter_signed_tail_gaussian hRH ⟨hr.1, hs⟩
    · rw [ite_eq_right hs]
      exact quarter_signed_tail_gaussian_wide hRH hr
  have h :=
    quarter_power_recovery_of_tail hwide d hd K hK hU hpow hpass htail quarter_correction_upper_663
  dsimp only at h ⊢
  by_cases hs : r ≤ 332
  · rw [ite_eq_left hs] at h ⊢
    linarith only [h]
  · rw [ite_eq_right hs] at h ⊢
    linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
