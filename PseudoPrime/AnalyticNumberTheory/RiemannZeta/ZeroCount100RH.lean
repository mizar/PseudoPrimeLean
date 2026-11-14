/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountBudgetRH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCriticalEnumeration
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountArgumentRH
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountConjugation
import PseudoPrime.Analysis.LogTaylorBounds

/-! # A certified coarse zero count at height 100 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, the positive-height zero count at 100 is less than 33.
The explicit count error and kernel-checked logarithm intervals supply the
numerical comparison. -/
theorem positive_zero_count_100_lt_33 (hRH : RiemannHypothesis) : positiveZeroCount 100 < 33 := by
  have hbase : 2 * Real.pi * Real.exp 1 ≤ 100 := by
    nlinarith only [Real.pi_lt_d4, Real.exp_one_lt_three, Real.pi_pos, Real.exp_pos 1]
  have h := positive_zero_count_budget_of_RH hRH 100 hbase
  have hL :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 100 6 64 (460517 / 100000) (460518 / 100000) = true
        from by decide +kernel)
  have h16 :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 16 4 64 (27725 / 10000) (27727 / 10000) = true from by
        decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hL h16
  have hq0 : (0 : ℝ) < 100 / (2 * Real.pi) :=
    div_pos (by norm_num only) (mul_pos (by norm_num only) Real.pi_pos)
  have hq : (100 : ℝ) / (2 * Real.pi) ≤ 16 := by
    apply (div_le_iff₀ (mul_pos (by norm_num only) Real.pi_pos)).2
    nlinarith only [Real.pi_gt_d4]
  have hlog := Real.log_le_log hq0 hq
  have hlogu : Real.log (100 / (2 * Real.pi)) - 1 ≤ (17727 / 10000 : ℝ) := by
    linarith only [hlog, h16.2]
  have hmul := mul_le_mul_of_nonneg_left hlogu hq0.le
  have hmul' := mul_le_mul_of_nonneg_right hq (show (0 : ℝ) ≤ 17727 / 10000 by norm_num only)
  have hb := (abs_le.mp h).2
  nlinarith only [hmul, hmul', hb, hL.2]

/-- Under RH, at most 32 positive-height zeta zeros occur through height 100,
counting multiplicity. The positive count is a natural-number sum, so the
strict numerical bound can be rounded down without a numerical table. -/
theorem positive_zero_count_100_le_32 (hRH : RiemannHypothesis) : positiveZeroCount 100 ≤ 32 := by
  have h := positive_zero_count_100_lt_33 hRH
  unfold positiveZeroCount at h ⊢
  rw [← Nat.cast_sum] at h ⊢
  have hn :
    (∑ ρ ∈ (zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im), riemannZetaZeroMultiplicity ρ) < 33 := by
    exact_mod_cast h
  exact_mod_cast Nat.lt_succ_iff.mp hn

/-- Under RH, the symmetric zero count through height 100 is at most 64.
Conjugation pairs the positive and negative zero ledgers. -/
theorem zero_count_100_le_64 (hRH : RiemannHypothesis) : zeroCount 100 ≤ 64 := by
  rw [zeroCount_eq_two_positive hRH (by norm_num only : (0 : ℝ) ≤ 100)]
  have h := positive_zero_count_100_le_32 hRH
  linarith only [h]

/-- The Riemann–von Mangoldt main term at height 100 is at most `117/4`.
The comparison uses a rational logarithm enclosure and an elementary bound
for π, without any zero data. -/
private theorem count_main_100_le :
    (100 / (2 * Real.pi)) * (Real.log (100 / (2 * Real.pi)) - 1) + 7 / 8 ≤ (117 / 4 : ℝ) := by
  have h16 :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 16 4 64 (27725 / 10000) (27727 / 10000) = true from by
        decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h16
  have hq0 : (0 : ℝ) < 100 / (2 * Real.pi) :=
    div_pos (by norm_num only) (mul_pos (by norm_num only) Real.pi_pos)
  have hq : (100 : ℝ) / (2 * Real.pi) ≤ 16 := by
    apply (div_le_iff₀ (mul_pos (by norm_num only) Real.pi_pos)).2
    nlinarith only [Real.pi_gt_d4]
  have hlog := Real.log_le_log hq0 hq
  have hlogu : Real.log (100 / (2 * Real.pi)) - 1 ≤ (17727 / 10000 : ℝ) := by
    linarith only [hlog, h16.2]
  have hmul := mul_le_mul_of_nonneg_left hlogu hq0.le
  have hmul' := mul_le_mul_of_nonneg_right hq (show (0 : ℝ) ≤ 17727 / 10000 by norm_num only)
  nlinarith only [hmul, hmul']

/-- If the count-normalized zeta argument at height 100 is at most `1/2`,
the positive-height count is strictly below 30. The existing Gamma remainder
and a rational comparison bound the remaining terms. -/
private theorem positive_count_100_lt_30_of_arg (harg : zetaArgCount 100 ≤ 1 / 2) :
    positiveZeroCount 100 < 30 := by
  have htheta := (abs_le.mp (thetaError_twice_le (show (100 : ℝ) ≤ 100 by norm_num only))).2
  have hid :
    positiveZeroCount 100 =
      (100 / (2 * Real.pi) * (Real.log (100 / (2 * Real.pi)) - 1) + 7 / 8) + zetaArgCount 100 +
        backlundThetaError 100 := by
    simp only [zetaArgCount, backlundThetaError, backlundThetaMain]
    field_simp
    ring
  rw [hid]
  nlinarith only [count_main_100_le, harg, htheta]

/-- Under RH, an upper bound `1/2` for the count-normalized zeta argument
at height 100 implies that the two-sided zero count is at most 58. The
positive count is integer-valued, and conjugation supplies the other half. -/
theorem count_100_le_58_of_arg (hRH : RiemannHypothesis) (harg : zetaArgCount 100 ≤ 1 / 2) :
    zeroCount 100 ≤ 58 := by
  have hlt := positive_count_100_lt_30_of_arg harg
  have hn :
    (∑ ρ ∈ (zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im), riemannZetaZeroMultiplicity ρ) < 30 := by
    unfold positiveZeroCount at hlt
    exact_mod_cast hlt
  have hle : positiveZeroCount 100 ≤ 29 := by
    unfold positiveZeroCount
    exact_mod_cast (Nat.lt_succ_iff.mp hn)
  rw [zeroCount_eq_two_positive hRH (by norm_num only : (0 : ℝ) ≤ 100)]
  linarith only [hle]

/-- Under RH, the positive-height zero ledger through 100 contains at most
32 distinct points. Each point has positive analytic multiplicity, so its
cardinality is bounded by the certified multiplicity count. -/
theorem positive_ledger_100_card_le_32 (hRH : RiemannHypothesis) :
    ((zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im)).card ≤ 32 := by
  classical
  let s := (zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im)
  have hw : ∀ ρ ∈ s, 1 ≤ riemannZetaZeroMultiplicity ρ := by
    intro ρ hρ
    have hh := Finset.mem_filter.mp hρ
    have hne : ρ ≠ 1 := by
      intro he
      rw [he, Complex.one_im] at hh
      exact (lt_irrefl 0) hh.2
    exact
      riemannZetaZeroMultiplicity_pos hne
        ((mem_zerosUpTo (by norm_num only : (0 : ℝ) ≤ 100)).mp hh.1).1
  have hle : (s.card : ℝ) ≤ ∑ ρ ∈ s, (riemannZetaZeroMultiplicity ρ : ℝ) := by
    calc
      (s.card : ℝ) = ∑ ρ ∈ s, (1 : ℝ) := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ ρ ∈ s, (riemannZetaZeroMultiplicity ρ : ℝ) :=
        Finset.sum_le_sum (fun ρ hρ ↦ by exact_mod_cast hw ρ hρ)
  have hb := positive_zero_count_100_le_32 hRH
  unfold positiveZeroCount at hb
  change (∑ ρ ∈ s, (riemannZetaZeroMultiplicity ρ : ℝ)) ≤ 32 at hb
  exact_mod_cast hle.trans hb

/-- Under RH, 29 distinct certified positive ledger zeros leave at most three
distinct points unaccounted for below height 100. This is a search budget;
it does not assert that the given points exhaust the ledger. -/
theorem positive_ledger_100_remaining_le_3 (hRH : RiemannHypothesis) (z : Fin 29 → ℂ)
    (hinj : Function.Injective z) (hz : ∀ i, z i ∈ (zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im)) :
    (((zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im)) \ Finset.univ.image z).card ≤ 3 := by
  classical
  have hs : Finset.univ.image z ⊆ (zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im) := by
    intro ρ hρ
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hρ
    exact hz i
  have hc : (Finset.univ.image z).card = 29 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have ht := positive_ledger_100_card_le_32 hRH
  have he := Finset.card_sdiff_add_card_eq_card hs
  have hsum :
    (((zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im)) \ Finset.univ.image z).card + 29 ≤ 3 + 29 := by
    calc
      _ = ((zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im)).card := by simpa only [hc] using he
      _ ≤ 3 + 29 := ht
  exact Nat.le_of_add_le_add_right hsum

/-- Under RH, after removing 29 distinct positive ledger zeros through 100,
the sum of the multiplicities of all remaining zeros is at most three. Each
selected zero contributes at least one to the existing count bound of 32. -/
theorem positive_ledger_remaining_mult_le_3 (hRH : RiemannHypothesis) (z : Fin 29 → ℂ)
    (hinj : Function.Injective z) (hz : ∀ i, z i ∈ (zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im)) :
    (∑ ρ ∈ ((zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im)) \ Finset.univ.image z,
        riemannZetaZeroMultiplicity ρ) ≤
      3 := by
  classical
  let s := (zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im)
  let u := Finset.univ.image z
  have hs : u ⊆ s := by
    intro ρ hρ
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hρ
    exact hz i
  have hc : u.card = 29 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hw : ∀ ρ ∈ u, 1 ≤ riemannZetaZeroMultiplicity ρ := by
    intro ρ hρ
    have hh := Finset.mem_filter.mp (hs hρ)
    have hne : ρ ≠ 1 := by
      intro he
      rw [he, Complex.one_im] at hh
      exact (lt_irrefl 0) hh.2
    exact
      riemannZetaZeroMultiplicity_pos hne
        ((mem_zerosUpTo (by norm_num only : (0 : ℝ) ≤ 100)).mp hh.1).1
  have hknown : 29 ≤ ∑ ρ ∈ u, riemannZetaZeroMultiplicity ρ := by
    calc
      29 = ∑ _ρ ∈ u, (1 : ℕ) := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hc, Nat.cast_ofNat]
      _ ≤ ∑ ρ ∈ u, riemannZetaZeroMultiplicity ρ := Finset.sum_le_sum hw
  have htot : (∑ ρ ∈ s, riemannZetaZeroMultiplicity ρ) ≤ 32 := by
    have h := positive_zero_count_100_le_32 hRH
    unfold positiveZeroCount at h
    change (∑ ρ ∈ s, (riemannZetaZeroMultiplicity ρ : ℝ)) ≤ 32 at h
    exact_mod_cast h
  have hsplit := Finset.sum_sdiff hs (f := riemannZetaZeroMultiplicity)
  have hsum : (∑ ρ ∈ s \ u, riemannZetaZeroMultiplicity ρ) + 29 ≤ 3 + 29 := by
    calc
      _ ≤ (∑ ρ ∈ s \ u, riemannZetaZeroMultiplicity ρ) + ∑ ρ ∈ u, riemannZetaZeroMultiplicity ρ :=
        Nat.add_le_add_left hknown _
      _ = ∑ ρ ∈ s, riemannZetaZeroMultiplicity ρ := hsplit
      _ ≤ 3 + 29 := htot
  exact Nat.le_of_add_le_add_right hsum

/-- For a finite multiplicity ledger of total at most 32, 29 selected
positive-weight entries leave at most three units for unselected weight and
for the excess weights of selected entries combined. -/
private theorem remaining_excess_budget {α : Type} [DecidableEq α] (s u : Finset α) (m : α → ℕ)
    (hs : u ⊆ s) (hw : ∀ x ∈ u, 1 ≤ m x) (hc : u.card = 29) (htot : (∑ x ∈ s, m x) ≤ 32) :
    (∑ x ∈ s \ u, m x) + (∑ x ∈ u, (m x - 1)) ≤ 3 := by
  have hweight : (∑ x ∈ u, m x) = (∑ x ∈ u, (m x - 1)) + 29 := by
    calc
      _ = ∑ x ∈ u, ((m x - 1) + 1) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact (Nat.sub_add_cancel (hw x hx)).symm
      _ = (∑ x ∈ u, (m x - 1)) + 29 := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, hc,
          Nat.cast_ofNat]
  have hsplit := Finset.sum_sdiff hs (f := m)
  have hsum : ((∑ x ∈ s \ u, m x) + ∑ x ∈ u, (m x - 1)) + 29 ≤ 3 + 29 := by
    calc
      _ = (∑ x ∈ s \ u, m x) + ∑ x ∈ u, m x := by rw [hweight, Nat.add_assoc]
      _ = ∑ x ∈ s, m x := hsplit
      _ ≤ 3 + 29 := htot
  exact Nat.le_of_add_le_add_right hsum

/-- Under RH, 29 distinct positive zeros through height 100 leave at most
three units of multiplicity in total for unselected zeros and for excess
multiplicity at the selected zeros. This sharpens the remaining-count budget. -/
theorem positive_ledger_remaining_budget_le_3 (hRH : RiemannHypothesis) (z : Fin 29 → ℂ)
    (hinj : Function.Injective z) (hz : ∀ i, z i ∈ (zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im)) :
    (∑ ρ ∈ ((zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im)) \ Finset.univ.image z,
          riemannZetaZeroMultiplicity ρ) +
        (∑ ρ ∈ Finset.univ.image z, (riemannZetaZeroMultiplicity ρ - 1)) ≤
      3 := by
  classical
  let s := (zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im)
  let u := Finset.univ.image z
  have hs : u ⊆ s := by
    intro ρ hρ
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hρ
    exact hz i
  have hc : u.card = 29 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hw : ∀ ρ ∈ u, 1 ≤ riemannZetaZeroMultiplicity ρ := by
    intro ρ hρ
    have hh := Finset.mem_filter.mp (hs hρ)
    have hne : ρ ≠ 1 := by
      intro he
      rw [he, Complex.one_im] at hh
      exact (lt_irrefl 0) hh.2
    exact
      riemannZetaZeroMultiplicity_pos hne
        ((mem_zerosUpTo (by norm_num only : (0 : ℝ) ≤ 100)).mp hh.1).1
  have htot : (∑ ρ ∈ s, riemannZetaZeroMultiplicity ρ) ≤ 32 := by
    have h := positive_zero_count_100_le_32 hRH
    unfold positiveZeroCount at h
    change (∑ ρ ∈ s, (riemannZetaZeroMultiplicity ρ : ℝ)) ≤ 32 at h
    exact_mod_cast h
  exact remaining_excess_budget s u riemannZetaZeroMultiplicity hs hw hc htot

/-- Under RH, the two-sided count through 100 is at most 58 exactly when
29 distinct selected positive zeros have neither unselected positive zeros
nor excess multiplicity. The equality accounts for multiplicity on both sides. -/
theorem count_100_le_58_iff_no_excess (hRH : RiemannHypothesis) (z : Fin 29 → ℂ)
    (hinj : Function.Injective z) (hz : ∀ i, z i ∈ (zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im)) :
    zeroCount 100 ≤ 58 ↔
      (∑ ρ ∈ ((zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im)) \ Finset.univ.image z,
            riemannZetaZeroMultiplicity ρ) +
          (∑ ρ ∈ Finset.univ.image z, (riemannZetaZeroMultiplicity ρ - 1)) =
        0 := by
  classical
  let s := (zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im)
  let u := Finset.univ.image z
  have hs : u ⊆ s := by
    intro ρ hρ
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hρ
    exact hz i
  have hc : u.card = 29 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hw : ∀ ρ ∈ u, 1 ≤ riemannZetaZeroMultiplicity ρ := by
    intro ρ hρ
    have hh := Finset.mem_filter.mp (hs hρ)
    have hne : ρ ≠ 1 := by
      intro he
      rw [he, Complex.one_im] at hh
      exact (lt_irrefl 0) hh.2
    exact
      riemannZetaZeroMultiplicity_pos hne
        ((mem_zerosUpTo (by norm_num only : (0 : ℝ) ≤ 100)).mp hh.1).1
  have hweight :
    (∑ x ∈ u, riemannZetaZeroMultiplicity x) =
      (∑ x ∈ u, (riemannZetaZeroMultiplicity x - 1)) + 29 := by
    calc
      _ = ∑ x ∈ u, ((riemannZetaZeroMultiplicity x - 1) + 1) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact (Nat.sub_add_cancel (hw x hx)).symm
      _ = (∑ x ∈ u, (riemannZetaZeroMultiplicity x - 1)) + 29 := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, hc,
          Nat.cast_ofNat]
  have hsplit := Finset.sum_sdiff hs (f := riemannZetaZeroMultiplicity)
  have hn :
    (∑ ρ ∈ s, riemannZetaZeroMultiplicity ρ) =
      ((∑ ρ ∈ s \ u, riemannZetaZeroMultiplicity ρ) +
          ∑ ρ ∈ u, (riemannZetaZeroMultiplicity ρ - 1)) +
        29 := by
    rw [← hsplit, hweight, Nat.add_assoc]
  have hp :
    positiveZeroCount 100 =
      (((∑ ρ ∈ s \ u, riemannZetaZeroMultiplicity ρ) +
            ∑ ρ ∈ u, (riemannZetaZeroMultiplicity ρ - 1)) +
          29 :
        ℕ) := by
    unfold positiveZeroCount
    change (∑ ρ ∈ s, (riemannZetaZeroMultiplicity ρ : ℝ)) = _
    exact_mod_cast hn
  rw [zeroCount_eq_two_positive hRH (by norm_num only : (0 : ℝ) ≤ 100), hp]
  norm_num only [Nat.cast_add, Nat.cast_ofNat]
  constructor
  · intro h
    have he :
      (((∑ ρ ∈ s \ u, riemannZetaZeroMultiplicity ρ) +
              ∑ ρ ∈ u, (riemannZetaZeroMultiplicity ρ - 1) :
            ℕ) :
          ℝ) ≤
        0 := by
      rw [Nat.cast_add]
      linarith only [h]
    exact_mod_cast (le_antisymm he (Nat.cast_nonneg _))
  · intro h
    have hr :
      (((∑ ρ ∈ s \ u, riemannZetaZeroMultiplicity ρ) +
              ∑ ρ ∈ u, (riemannZetaZeroMultiplicity ρ - 1) :
            ℕ) :
          ℝ) =
        0 := by
      exact_mod_cast h
    rw [Nat.cast_add] at hr
    linarith only [hr]

/-- Under RH, a complete injective enumeration of 29 simple positive ledger
zeros through height 100 gives the two-sided count bound 58. This turns an
independent completeness and simplicity certificate into the counting input. -/
theorem count_100_le_58_of_complete_simple (hRH : RiemannHypothesis) (z : Fin 29 → ℂ)
    (hinj : Function.Injective z) (hz : ∀ i, z i ∈ (zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im))
    (hcomplete : (zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im) ⊆ Finset.univ.image z)
    (hsimple : ∀ i, riemannZetaZeroMultiplicity (z i) = 1) : zeroCount 100 ≤ 58 := by
  classical
  apply (count_100_le_58_iff_no_excess hRH z hinj hz).2
  rw [Finset.sdiff_eq_empty_iff_subset.mpr hcomplete, Finset.sum_empty, zero_add]
  apply Finset.sum_eq_zero
  intro ρ hρ
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hρ
  rw [hsimple i]
  exact Nat.sub_self 1

/-- Under RH, the two-sided count through height 100 is at most 58 exactly
when 29 distinct positive ledger zeros are complete and simple. Positivity
of analytic multiplicities turns the zero excess budget into both properties. -/
theorem count_100_le_58_iff_complete_simple (hRH : RiemannHypothesis) (z : Fin 29 → ℂ)
    (hinj : Function.Injective z) (hz : ∀ i, z i ∈ (zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im)) :
    zeroCount 100 ≤ 58 ↔
      (zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im) ⊆ Finset.univ.image z ∧
        (∀ i, riemannZetaZeroMultiplicity (z i) = 1) := by
  classical
  constructor
  · intro hcount
    have hbudget := (count_100_le_58_iff_no_excess hRH z hinj hz).1 hcount
    obtain ⟨hleft, hright⟩ := Nat.add_eq_zero_iff.mp hbudget
    constructor
    · intro ρ hρ
      by_contra hnot
      have hrem : ρ ∈ (zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im) \ Finset.univ.image z :=
        Finset.mem_sdiff.mpr ⟨hρ, hnot⟩
      have hzero := (Finset.sum_eq_zero_iff.mp hleft) ρ hrem
      have hh := Finset.mem_filter.mp hρ
      have hne : ρ ≠ 1 := by
        intro he
        rw [he, Complex.one_im] at hh
        exact (lt_irrefl 0) hh.2
      have hpos :=
        riemannZetaZeroMultiplicity_pos hne
          ((mem_zerosUpTo (by norm_num only : (0 : ℝ) ≤ 100)).mp hh.1).1
      exact (Nat.ne_of_gt hpos) hzero
    · intro i
      have hmem : z i ∈ Finset.univ.image z := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      have hsub := (Finset.sum_eq_zero_iff.mp hright) (z i) hmem
      have hle : riemannZetaZeroMultiplicity (z i) ≤ 1 := Nat.sub_eq_zero_iff_le.mp hsub
      have hh := Finset.mem_filter.mp (hz i)
      have hne : z i ≠ 1 := by
        intro he
        rw [he, Complex.one_im] at hh
        exact (lt_irrefl 0) hh.2
      have hpos :=
        riemannZetaZeroMultiplicity_pos hne
          ((mem_zerosUpTo (by norm_num only : (0 : ℝ) ≤ 100)).mp hh.1).1
      exact Nat.le_antisymm hle hpos
  · rintro ⟨hcomplete, hsimple⟩
    exact count_100_le_58_of_complete_simple hRH z hinj hz hcomplete hsimple

/-- Under RH, 29 distinct critical-line zeros with ordinates in `(0, 100]`
leave at most three distinct positive-height ledger points unaccounted for.
This connects the count budget to the ordinate hypotheses used by the
piecewise ψ estimate. -/
theorem critical_zeros_100_remaining_le_3 (hRH : RiemannHypothesis) (g : Fin 29 → ℝ)
    (hmono : StrictMono g) (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0) :
    (((zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im)) \
          Finset.univ.image (fun i ↦ ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I)).card ≤
      3 := by
  apply positive_ledger_100_remaining_le_3 hRH _ (critical_points_injective g hmono.injective)
  intro i
  apply Finset.mem_filter.mpr
  have hre : (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I).re = 1 / 2 := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have him : (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I).im = g i := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  constructor
  · apply (mem_zerosUpTo (by norm_num only : (0 : ℝ) ≤ 100)).2
    refine ⟨hzero i, ?_, ?_⟩
    · rw [hre]
      norm_num only
    · rw [him, abs_of_pos (hpos i)]
      exact hheight i
  · rw [him]
    exact hpos i

/-- Under RH, 29 distinct critical-line zeros in `(0, 100]` leave at most
three units of multiplicity outside their image. The ordinate assumptions
place every selected zero in the positive closed-height ledger. -/
theorem critical_zeros_remaining_mult_le_3 (hRH : RiemannHypothesis) (g : Fin 29 → ℝ)
    (hmono : StrictMono g) (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0) :
    (∑
        ρ ∈
          ((zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im)) \
            Finset.univ.image (fun i ↦ ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I),
        riemannZetaZeroMultiplicity ρ) ≤
      3 := by
  apply positive_ledger_remaining_mult_le_3 hRH _ (critical_points_injective g hmono.injective)
  intro i
  apply Finset.mem_filter.mpr
  have hre : (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I).re = 1 / 2 := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have him : (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I).im = g i := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  constructor
  · apply (mem_zerosUpTo (by norm_num only : (0 : ℝ) ≤ 100)).2
    refine ⟨hzero i, ?_, ?_⟩
    · rw [hre]
      norm_num only
    · rw [him, abs_of_pos (hpos i)]
      exact hheight i
  · rw [him]
    exact hpos i

/-- Under RH, 29 distinct critical-line zeros through height 100 leave at
most three units jointly for additional zeros and excess multiplicities at
the selected zeros. This is the remaining completeness-and-simplicity budget. -/
theorem critical_zeros_remaining_budget_le_3 (hRH : RiemannHypothesis) (g : Fin 29 → ℝ)
    (hmono : StrictMono g) (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0) :
    (∑
          ρ ∈
            ((zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im)) \
              Finset.univ.image (fun i ↦ ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I),
          riemannZetaZeroMultiplicity ρ) +
        (∑ ρ ∈ Finset.univ.image (fun i ↦ ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I),
          (riemannZetaZeroMultiplicity ρ - 1)) ≤
      3 := by
  apply positive_ledger_remaining_budget_le_3 hRH _ (critical_points_injective g hmono.injective)
  intro i
  apply Finset.mem_filter.mpr
  have hre : (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I).re = 1 / 2 := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have him : (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I).im = g i := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  constructor
  · apply (mem_zerosUpTo (by norm_num only : (0 : ℝ) ≤ 100)).2
    refine ⟨hzero i, ?_, ?_⟩
    · rw [hre]
      norm_num only
    · rw [him, abs_of_pos (hpos i)]
      exact hheight i
  · rw [him]
    exact hpos i

/-- Under RH and the count bound `N(100) ≤ 58`, any 29 strictly ordered
critical-line zeros with ordinates in `(0,100]` exhaust the positive-height
ledger and each has analytic multiplicity one. This supplies the Z100
completeness and simplicity bridge once the 29 existence certificates and
the count bound are available. -/
theorem critical_zeros_complete_simple (hRH : RiemannHypothesis) (hc : zeroCount 100 ≤ 58)
    (g : Fin 29 → ℝ) (hmono : StrictMono g) (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0) :
    ((zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im)) ⊆
        Finset.univ.image (fun i ↦ ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) ∧
      ∀ i, riemannZetaZeroMultiplicity (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 1 := by
  apply
    (count_100_le_58_iff_complete_simple hRH _ (critical_points_injective g hmono.injective) ?_).1
      hc
  intro i
  apply Finset.mem_filter.mpr
  have hre : (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I).re = 1 / 2 := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have him : (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I).im = g i := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  constructor
  · apply (mem_zerosUpTo (by norm_num only : (0 : ℝ) ≤ 100)).2
    refine ⟨hzero i, ?_, ?_⟩
    · rw [hre]
      norm_num only
    · rw [him, abs_of_pos (hpos i)]
      exact hheight i
  · rw [him]
    exact hpos i

/-- Under RH, 29 distinct positive-height ledger zeros through height 100
force the two-sided zero count to be at least 58. Each selected zero has
positive multiplicity and conjugation accounts for the negative side. -/
theorem positive_ledger_29_count_lower (hRH : RiemannHypothesis) (z : Fin 29 → ℂ)
    (hinj : Function.Injective z) (hz : ∀ i, z i ∈ (zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im)) :
    58 ≤ zeroCount 100 := by
  classical
  let u := Finset.univ.image z
  let s := (zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im)
  have hs : u ⊆ s := by
    intro ρ hρ
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hρ
    exact hz i
  have hc : u.card = 29 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hw : ∀ ρ ∈ u, 1 ≤ riemannZetaZeroMultiplicity ρ := by
    intro ρ hρ
    have hh := Finset.mem_filter.mp (hs hρ)
    have hne : ρ ≠ 1 := by
      intro he
      rw [he, Complex.one_im] at hh
      exact (lt_irrefl 0) hh.2
    exact
      riemannZetaZeroMultiplicity_pos hne
        ((mem_zerosUpTo (by norm_num only : (0 : ℝ) ≤ 100)).mp hh.1).1
  have hknown : 29 ≤ ∑ ρ ∈ u, riemannZetaZeroMultiplicity ρ := by
    calc
      29 = ∑ _ρ ∈ u, (1 : ℕ) := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hc, Nat.cast_ofNat]
      _ ≤ ∑ ρ ∈ u, riemannZetaZeroMultiplicity ρ := Finset.sum_le_sum hw
  have htotal : 29 ≤ ∑ ρ ∈ s, riemannZetaZeroMultiplicity ρ :=
    hknown.trans (Finset.sum_le_sum_of_subset hs)
  have hp : (29 : ℝ) ≤ positiveZeroCount 100 := by
    unfold positiveZeroCount
    change (29 : ℝ) ≤ ∑ ρ ∈ s, (riemannZetaZeroMultiplicity ρ : ℝ)
    exact_mod_cast htotal
  rw [zeroCount_eq_two_positive hRH (by norm_num only : (0 : ℝ) ≤ 100)]
  linarith only [hp]

/-- Under RH, 29 ordered critical-line zeros in `(0,100]` and the upper
bound `N(100) ≤ 58` give the exact two-sided count `N(100) = 58`. -/
theorem critical_zeros_count_eq_58 (hRH : RiemannHypothesis) (hc : zeroCount 100 ≤ 58)
    (g : Fin 29 → ℝ) (hmono : StrictMono g) (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0) :
    zeroCount 100 = 58 := by
  apply le_antisymm hc
  apply positive_ledger_29_count_lower hRH _ (critical_points_injective g hmono.injective)
  intro i
  apply Finset.mem_filter.mpr
  have hre : (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I).re = 1 / 2 := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have him : (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I).im = g i := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  constructor
  · apply (mem_zerosUpTo (by norm_num only : (0 : ℝ) ≤ 100)).2
    refine ⟨hzero i, ?_, ?_⟩
    · rw [hre]
      norm_num only
    · rw [him, abs_of_pos (hpos i)]
      exact hheight i
  · rw [him]
    exact hpos i

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
