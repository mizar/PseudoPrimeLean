/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterThetaPoly663
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxReflectTail656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterThetaPoly663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterProfile663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxReflection656

/-! # Pairing of reflected tails in section 137 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The coefficient remaining after pairing a positive reflection at i
with a negative reflection at j, as in (137.29). -/
noncomputable def quarterPairLoss663 (i j : Fin 6) : ℝ :=
  -(quarterCoeff663 j : ℝ) -
    (quarterCoeff663 i : ℝ) * Real.exp (-(11 / 10) * ((quarterShift663 j : ℝ) - quarterShift663 i))

/-- Pair the reflections at (0,1) and (4,5), leaving the negative
coefficients at 2 and 3 unchanged. -/
theorem quarter_reflection_pairs_663 (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4) {r : ℝ} (hr : 0 < r)
    (hlog : (7 : ℝ) ≤ 2 * Real.log r) :
    let F := fun i : Fin 6 ↦ quarterAuxReflection656 α r (quarterShift663 i : ℝ)
    (-quarterPairLoss663 0 1) * F 1 + (quarterCoeff663 2 : ℝ) * F 2 +
          (quarterCoeff663 3 : ℝ) * F 3 -
        quarterPairLoss663 4 5 * F 5 ≤
      ∑ i, (quarterCoeff663 i : ℝ) * F i := by
  intro F
  have hu : ∀ i, quarterShift663 i ≤ 7 := by decide +kernel
  have horder : ∀ i j, i ≤ j → quarterShift663 i ≤ quarterShift663 j := by decide +kernel
  have hc : ∀ i, i = 0 ∨ i = 4 → 0 ≤ quarterCoeff663 i := by decide +kernel
  have hp (i j : Fin 6) (hij : i ≤ j) (hi : i = 0 ∨ i = 4) :=
    quarter_aux_reflection_pair_656 α hα hr (u := (quarterShift663 i : ℝ)) (v :=
      (quarterShift663 j : ℝ)) (by exact_mod_cast horder i j hij)
      ((by exact_mod_cast hu j : (quarterShift663 j : ℝ) ≤ 7).trans hlog) (c :=
      (quarterCoeff663 i : ℝ)) (d := (quarterCoeff663 j : ℝ)) (by exact_mod_cast hc i hi)
  have h₁ := hp 0 1 (by decide) (Or.inl rfl)
  have h₂ := hp 4 5 (by decide) (Or.inr rfl)
  change
    _ ≤
      (quarterCoeff663 0 : ℝ) * F 0 +
        ((quarterCoeff663 1 : ℝ) * F 1 +
          ((quarterCoeff663 2 : ℝ) * F 2 +
            ((quarterCoeff663 3 : ℝ) * F 3 +
              ((quarterCoeff663 4 : ℝ) * F 4 + ((quarterCoeff663 5 : ℝ) * F 5 + 0)))))
  unfold quarterPairLoss663
  dsimp only [F]
  linarith only [h₁, h₂]

private theorem pair_exp_box :
    Real.exp (-(11 / 100 : ℝ)) ∈ Set.Icc 0.89583413529 0.89583413530 := by
  have he := profile_exp_error (-(11 / 100 : ℚ)) (by norm_num only)
  have hq :
    profileExpTaylor (-(11 / 100 : ℚ)) ∈
      Set.Icc (895834135296 / 10 ^ 12) (895834135297 / 10 ^ 12) := by
    decide +kernel
  have hl := (Rat.cast_le (K := ℝ)).mpr hq.1
  have hu := (Rat.cast_le (K := ℝ)).mpr hq.2
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_ofNat] at he hl hu
  exact ⟨by linarith only [(abs_le.mp he).1, hl], by linarith only [(abs_le.mp he).2, hu]⟩

private theorem pair_loss_box (i j : Fin 6) {a b : ℚ} {l u : ℝ} (ha : quarterCoeff663 i = a)
    (hb : quarterCoeff663 j = b) (hs : quarterShift663 j - quarterShift663 i = 1 / 10)
    (hpos : 0 ≤ (a : ℝ)) (hl : l ≤ -(b : ℝ) - (a : ℝ) * 0.89583413530)
    (hu : -(b : ℝ) - (a : ℝ) * 0.89583413529 ≤ u) : quarterPairLoss663 i j ∈ Set.Icc l u := by
  have hsR := congrArg (fun x : ℚ ↦ (x : ℝ)) hs
  simp only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] at hsR
  unfold quarterPairLoss663
  rw [ha, hb, hsR, show -(11 / 10 : ℝ) * (1 / 10) = -(11 / 100) by norm_num only]
  exact
    ⟨hl.trans (sub_le_sub_left (mul_le_mul_of_nonneg_left pair_exp_box.2 hpos) _),
      (sub_le_sub_left (mul_le_mul_of_nonneg_left pair_exp_box.1 hpos) _).trans hu⟩

/-- The two residual coefficients are positive and have rational upper
bounds. These control the amount charged at each of the two paired shifts. -/
theorem quarter_pair_loss_boxes_663 :
    quarterPairLoss663 0 1 ∈ Set.Icc 0.07452037559 0.07452037560 ∧
      quarterPairLoss663 4 5 ∈ Set.Icc 0.00000002447 0.00000002449 := by
  constructor
  · apply pair_loss_box (a := 493098778 / 10 ^ 9) (b := -516255093 / 10 ^ 9)
    all_goals
      first
      | decide +kernel
      | norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_ofNat]
  · apply pair_loss_box (a := 154985393 / 10 ^ 9) (b := -138841230 / 10 ^ 9)
    all_goals
      first
      | decide +kernel
      | norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_ofNat]

private theorem reflection_nonneg (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n) {r h : ℝ} (hr : 0 < r)
    (hh : h ≤ 2 * Real.log r) : 0 ≤ quarterAuxReflection656 α r h := by
  unfold quarterAuxReflection656
  apply mul_nonneg (by positivity)
  exact
    tsum_nonneg fun n ↦
      mul_nonneg
        (mul_nonneg (hα n)
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (Real.rpow_nonneg (Nat.cast_nonneg n) _)))
        (pow_nonneg (add_nonneg (sub_nonneg.mpr hh) (Real.log_natCast_nonneg n)) _)

/-- A common zero-deficit prefix gives the four remaining reflection
charges in (137.31) via the six shared Abel moments. -/
theorem quarter_reflection_tail_663 (hRH : RiemannHypothesis) {B : ℕ} (hB : 103684 ≤ (B : ℝ))
    (hU : (B : ℝ) ≤ 1000000) (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4)
    (hprefix : ∀ n ∈ Finset.Ioc 0 B, ArithmeticFunction.vonMangoldt n ≠ 0 → α n = 0) {r : ℝ}
    (hr : 0 < r) (hlog : 7 ≤ 2 * Real.log r) :
    let C := fun i : Fin 6 ↦ quarterAuxReflectCap656 r (quarterShift663 i : ℝ) B
    (-0.07452037560) * C 1 + (quarterCoeff663 2 : ℝ) * C 2 + (quarterCoeff663 3 : ℝ) * C 3 -
        0.00000002449 * C 5 ≤
      ∑ i, (quarterCoeff663 i : ℝ) * quarterAuxReflection656 α r (quarterShift663 i : ℝ) := by
  intro C
  have hs : ∀ i, quarterShift663 i ≤ 7 := by decide +kernel
  have hh (i : Fin 6) := ((by exact_mod_cast hs i : (quarterShift663 i : ℝ) ≤ 7)).trans hlog
  have hn i := reflection_nonneg α (fun n ↦ (hα n).1) hr (hh i)
  have hcap i := quarter_aux_reflect_tail_cap_656 hRH hB hU α hα hprefix hr (hh i)
  have hc : ∀ i, i = 2 ∨ i = 3 → quarterCoeff663 i ≤ 0 := by decide +kernel
  have hcR (i : Fin 6) (hi : i = 2 ∨ i = 3) : (quarterCoeff663 i : ℝ) ≤ 0 := by
    exact_mod_cast hc i hi
  have h₂ := mul_le_mul_of_nonpos_left (hcap 2) (hcR 2 (Or.inl rfl))
  have h₃ := mul_le_mul_of_nonpos_left (hcap 3) (hcR 3 (Or.inr rfl))
  have h₁ := mul_le_mul quarter_pair_loss_boxes_663.1.2 (hcap 1) (hn 1) (by norm_num only)
  have h₅ := mul_le_mul quarter_pair_loss_boxes_663.2.2 (hcap 5) (hn 5) (by norm_num only)
  have h := quarter_reflection_pairs_663 α hα hr hlog
  dsimp only [C] at h ⊢
  linarith only [h, h₁, h₂, h₃, h₅]

/-- The remaining reflection charges after using the two positive coefficients. -/
noncomputable def quarterReflectLower663 (r : ℝ) (B : ℕ) : ℝ :=
  let C := fun i : Fin 6 ↦ quarterAuxReflectCap656 r (quarterShift663 i : ℝ) B
  (-0.07452037560) * C 1 + (quarterCoeff663 2 : ℝ) * C 2 + (quarterCoeff663 3 : ℝ) * C 3 -
    0.00000002449 * C 5

/-- Combine the conductor and pole interval bounds with the four Abel tail
charges in (137.31), for radii at least 328 and a zero-deficit prefix. -/
theorem quarter_shift_residual_lower_663 (hRH : RiemannHypothesis) {B : ℕ} (hB : 103684 ≤ (B : ℝ))
    (hU : (B : ℝ) ≤ 1000000) (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4)
    (hprefix : ∀ n ∈ Finset.Ioc 0 B, ArithmeticFunction.vonMangoldt n ≠ 0 → α n = 0) {r R l u M : ℝ}
    (hr : 328 ≤ r) (hR : r ≤ R) (hl : 0 ≤ l) (hv : 2 * Real.log r - 23 / 2 ∈ Set.Icc l u)
    (hM : r ^ (-(6 / 5) : ℝ) ≤ M) (hP : 0 ≤ thetaIntervalUpper663 l u) :
    -(11 / 10) ^ 5 / 30 * M * thetaIntervalUpper663 l u + 18.29172549 / R +
        quarterReflectLower663 r B ≤
      quarterAuxTheta663 r + quarterAuxNegPole663 / r +
        ∑ i, (quarterCoeff663 i : ℝ) * quarterAuxReflection656 α r (quarterShift663 i : ℝ) := by
  have hr₀ : 0 < r := by linarith only [hr]
  have hlog : 7 ≤ 2 * Real.log r := by linarith only [hl, hv.1]
  exact
    add_le_add (theta_pole_lower_663 hr₀ hR hl hv hM hP)
      (quarter_reflection_tail_663 hRH hB hU α hα hprefix hr₀ hlog)

end PseudoPrime.PrimeTestBounds.MillerRabin
