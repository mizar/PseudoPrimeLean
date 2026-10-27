/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.QNeOneCorrections
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.FinerLLSConstants

/-! # Refined reciprocal input retaining the quadratic value at two -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- At Y>=1 and positive exponent k, a natural p in the root cutoff through
floor(Y^(1/k)) is at most Y after real casting. Bound the exponent by one.
This adapts ordinary odd-prime triviality to existing prime-power ledgers. -/
theorem cast_le_of_mem_root_cutoff {Y : ℝ} (hY : 1 ≤ Y) {k p : ℕ} (hk : 1 ≤ k)
    (hp : p ∈ Finset.Ioc 0 ⌊Y ^ ((1 : ℝ) / k)⌋₊) : (p : ℝ) ≤ Y := by
  have hk1 : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr hk
  have hk0 : (0 : ℝ) < k := zero_lt_one.trans_le hk1
  have he := Real.rpow_le_self_of_one_le hY ((div_le_one hk0).mpr hk1)
  exact
    ((Nat.cast_le.mpr (Finset.mem_Ioc.mp hp).2).trans
          (Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hY) _))).trans
      he

/-- Reciprocal cost selected by the quadratic value c at two: log 2 at zero,
zero at one, and (4/3)log 2 in the remaining branch. Real output is defined for all
complex c; the comparison theorem uses quadraticity to identify the last branch
with minus one. Retaining c avoids the uniform twice-log-two loss. -/
noncomputable def quadraticTwoReciprocalCost (c : ℂ) : ℝ :=
  if c = 0 then Real.log 2 else if c = 1 then 0 else (4 / 3 : ℝ) * Real.log 2

open AnalyticNumberTheory.Arithmetic AnalyticNumberTheory.RiemannZeta in
/-- Under RH,Y>=2 and odd-prime triviality for a quadratic primitive inducing
character, its reciprocal real sum is at least log Y-31551/20000 minus the branch
cost at two. Reuse the exact two-adic identity and the zero, one and minus-one
correction bounds. No new arithmetic certificate or modulus restriction is used. -/
theorem reciprocalSum_re_ge_of_quadratic_two_branch {q : ℕ} (χ : DirichletCharacter ℂ q) {Y : ℝ}
    (hY : 2 ≤ Y) (hRH : RiemannHypothesis) (hquad : χ.primitiveCharacter.IsQuadratic)
    (ht : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ Y → χ.primitiveCharacter p = 1) :
    Real.log Y - (31551 / 20000 : ℝ) - quadraticTwoReciprocalCost (χ.primitiveCharacter 2) ≤
      (characterReciprocalWeightedSum Y χ.primitiveCharacter).re := by
  have hy1 : 1 ≤ Y := by linarith only [hY]
  have hy0 : 0 < Y := by linarith only [hY]
  have ho :
    ∀ {k p : ℕ},
      k ∈ Finset.Icc 1 ⌊Real.log Y / Real.log 2⌋₊ →
        p ∈ Finset.Ioc 0 ⌊Y ^ ((1 : ℝ) / k)⌋₊ → p.Prime → Odd p → χ.primitiveCharacter p = 1 := by
    intro k p hk hp hprime hodd
    exact ht p hprime hodd (cast_le_of_mem_root_cutoff hy1 (Finset.mem_Icc.mp hk).1 hp)
  have he := reciprocalWeightedSum_sub_re_eq_twoAdicCorrection_of_eq_one Y χ hY ho
  have hr := reciprocalWeightedMangoldtSum_ge_log_sub_31551_div_20000 hRH hY
  rcases hquad (2 : ZMod χ.conductor) with h0 | h1 | hm
  · have hc := twoAdicReciprocalCorrection_le_log_two_of_apply_two_eq_zero Y χ hy0 h0
    rw [quadraticTwoReciprocalCost, ite_eq_left h0]
    linarith only [he, hr, hc]
  · have hc := twoAdicReciprocalCorrection_eq_zero_of_apply_two_eq_one Y χ h1
    have hn0 : χ.primitiveCharacter 2 ≠ 0 := by
      rw [h1]; exact one_ne_zero
    rw [quadraticTwoReciprocalCost, ite_eq_right hn0, ite_eq_left h1]
    linarith only [he, hr, hc]
  · have hc := twoAdicReciprocalCorrection_le_four_thirds_log_two_of_apply_two_eq_neg_one Y χ hY hm
    have hn0 : χ.primitiveCharacter 2 ≠ 0 := by
      rw [hm]; exact neg_ne_zero.mpr one_ne_zero
    have hn1 : χ.primitiveCharacter 2 ≠ 1 := by
      rw [hm]
      norm_num only
    rw [quadraticTwoReciprocalCost, ite_eq_right hn0, ite_eq_right hn1]
    linarith only [he, hr, hc]

/-- For any complex input, the selected reciprocal branch cost is at most
(4/3)log 2. Check the definition's zero, one and remaining branches using log 2>0.
This supplies a uniform bound when the value at two is not retained. -/
theorem quadraticTwoReciprocalCost_le_four_thirds (c : ℂ) :
    quadraticTwoReciprocalCost c ≤ (4 / 3 : ℝ) * Real.log 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num only : (1 : ℝ) < 2)
  unfold quadraticTwoReciprocalCost
  split_ifs with h0 h1
  · nlinarith only [hl]
  · exact mul_nonneg (by norm_num only) hl.le
  · exact le_refl _

end PseudoPrime.LLS.PaperStatements
