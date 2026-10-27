/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.OddEndpointArithmetic
public import PseudoPrime.LLS.OddEndpointReciprocalBranches

/-! # Logarithmic character defects controlling gap kernels and two-adic branches -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open AnalyticNumberTheory.Arithmetic in
/-- For any character, positive gap and scale x>0, the principal-minus-character
gap sum is at most the logarithmic defect divided by sqrt x. Each coefficient
1-Re chi(n) is nonnegative, so multiply the termwise gap upper bound and sum.
No odd-prime triviality, primitivity or GRH is needed for this comparison. -/
theorem reciprocalGap_defect_le_log_defect {q : ℕ} (χ : DirichletCharacter ℂ q) {h x : ℝ}
    (hh : 0 < h) (hx : 0 < x) :
    (reciprocalGapCharacterSum h (1 : DirichletCharacter ℂ 1) x).re -
        (reciprocalGapCharacterSum h χ x).re ≤
      (logWeightedMangoldtSum x - (characterLogWeightedSum x χ).re) / Real.sqrt x := by
  have hs :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (1 - (χ n).re) * reciprocalGapPrincipalWeight h x n) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (1 - (χ n).re) * (logWeightedMangoldtTerm x n / Real.sqrt x) := by
    apply Finset.sum_le_sum
    intro n hn
    have hc : 0 ≤ 1 - (χ n).re :=
      sub_nonneg.mpr ((Complex.re_le_norm (χ n)).trans (χ.norm_le_one n))
    exact
      mul_le_mul_of_nonneg_left
        (reciprocalGapPrincipalWeight_le_log_term hh hx (Finset.mem_Ioc.mp hn).1) hc
  have hg :
    (reciprocalGapCharacterSum h (1 : DirichletCharacter ℂ 1) x).re -
        (reciprocalGapCharacterSum h χ x).re =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (1 - (χ n).re) * reciprocalGapPrincipalWeight h x n := by
    rw [reciprocalGap_principal_re_eq_sum, reciprocalGapCharacterSum_re_eq_weighted, ←
      Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hl :
    (logWeightedMangoldtSum x - (characterLogWeightedSum x χ).re) / Real.sqrt x =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (1 - (χ n).re) * (logWeightedMangoldtTerm x n / Real.sqrt x) := by
    unfold logWeightedMangoldtSum characterLogWeightedSum characterLogWeightedTerm
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hg, hl]
  exact hs

open AnalyticNumberTheory.Arithmetic in
/-- Under RH,h>0,x>1 and a bound D on the logarithmic character defect, the gap
character sum has the displayed analytic lower bound with loss D/sqrt x.
Combine the principal RH lower estimate with the generic defect comparison.
This accepts any improved arithmetic correction without changing the kernel. -/
theorem reciprocalGapSum_re_ge_of_log_defect_le {q : ℕ} (χ : DirichletCharacter ℂ q) {h x D : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hRH : RiemannHypothesis)
    (hD : logWeightedMangoldtSum x - (characterLogWeightedSum x χ).re ≤ D) :
    (x - Real.sqrt x / 20 - (1839 / 1000 : ℝ) * Real.log x - 21 / 20) /
          (Real.sqrt x * (1 + h * Real.log x)) -
        D / Real.sqrt x ≤
      (reciprocalGapCharacterSum h χ x).re := by
  have hd := reciprocalGap_defect_le_log_defect χ hh (zero_lt_one.trans hx)
  have he := div_le_div_of_nonneg_right hD (Real.sqrt_nonneg x)
  have hl := logSum_div_le_gapSum hh hx.le (Finset.Ioc 0 ⌊x⌋₊) (fun _ hn ↦ hn)
  change logWeightedMangoldtSum x / (Real.sqrt x * (1 + h * Real.log x)) ≤ _ at hl
  rw [← reciprocalGap_principal_re_eq_sum] at hl
  have hp : 0 ≤ Real.sqrt x * (1 + h * Real.log x) :=
    mul_nonneg (Real.sqrt_nonneg x) (by nlinarith only [hh, Real.log_pos hx])
  have hr :=
    div_le_div_of_nonneg_right (PseudoPrime.LLS.logWeightedMangoldtSum_ge_rational_refined hRH hx)
      hp
  linarith only [hd, he, hl, hr]

/-- Principal logarithmic defect cost selected by the quadratic value c at two:
half (log x)^2 at zero, zero at one, and the refined half-square plus log-two
correction otherwise. The comparison uses quadraticity to identify the last
branch with minus one; the definition is total for all x and complex c. -/
noncomputable def quadraticTwoLogCost (x : ℝ) (c : ℂ) : ℝ :=
  if c = 0 then (Real.log x) ^ 2 / 2
  else if c = 1 then 0 else (Real.log x) ^ 2 / 2 + Real.log 2 * (Real.log x - Real.log 2)

open AnalyticNumberTheory.Arithmetic in
/-- For x>=4, a quadratic primitive associate trivial at all odd primes through x
has logarithmic defect at most its selected two-adic branch cost. Reuse the exact
prime-power decomposition and existing zero, one and refined minus-one estimates.
This is the principal-side counterpart of the reciprocal branch bound. -/
theorem log_defect_le_quadratic_two_branch {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 4 ≤ x)
    (hquad : χ.primitiveCharacter.IsQuadratic)
    (ht : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ x → χ.primitiveCharacter p = 1) :
    logWeightedMangoldtSum x - (characterLogWeightedSum x χ.primitiveCharacter).re ≤
      quadraticTwoLogCost x (χ.primitiveCharacter 2) := by
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hx2 : 2 ≤ x := by linarith only [hx]
  have hx0 : x ≠ 0 := (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 4) hx).ne'
  have ho :
    ∀ {k p : ℕ},
      k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊ →
        p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ → p.Prime → Odd p → χ.primitiveCharacter p = 1 := by
    intro k p hk hp hprime hodd
    exact ht p hprime hodd (cast_le_of_mem_root_cutoff hx1 (Finset.mem_Icc.mp hk).1 hp)
  rw [logWeightedMangoldtSum_sub_characterLogWeightedSum_re_eq_twoAdicCorrection_of_eq_one x χ hx2
      ho]
  rcases hquad (2 : ZMod χ.conductor) with h0 | h1 | hm
  · rw [quadraticTwoLogCost, ite_eq_left h0]
    exact twoAdicLogCorrection_le_half_log_sq_of_apply_two_eq_zero x χ hx0 h0
  · have hn0 : χ.primitiveCharacter 2 ≠ 0 := by
      rw [h1]; exact one_ne_zero
    rw [quadraticTwoLogCost, ite_eq_right hn0, ite_eq_left h1]
    exact (twoAdicLogCorrection_eq_zero_of_apply_two_eq_one x χ hx0 h1).le
  · have hn0 : χ.primitiveCharacter 2 ≠ 0 := by
      rw [hm]; exact neg_ne_zero.mpr one_ne_zero
    have hn1 : χ.primitiveCharacter 2 ≠ 1 := by
      rw [hm]; norm_num only
    rw [quadraticTwoLogCost, ite_eq_right hn0, ite_eq_right hn1]
    exact
      twoAdicLogCorrection_le_half_log_sq_add_log_two_mul_log_half_of_apply_two_eq_neg_one x χ hx hm

/-- For x>=4 and any complex branch input, the logarithmic cost is at most the
common minus-one envelope. Log x>=log 2 makes the extra term nonnegative.
This removes the value-at-two input when a uniform sufficient condition is desired. -/
theorem quadraticTwoLogCost_le_envelope {x : ℝ} (hx : 4 ≤ x) (c : ℂ) :
    quadraticTwoLogCost x c ≤ (Real.log x) ^ 2 / 2 + Real.log 2 * (Real.log x - Real.log 2) := by
  have hl : Real.log 2 ≤ Real.log x :=
    Real.log_le_log (by norm_num only) (le_trans (by norm_num only) hx)
  have hp : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num only : (1 : ℝ) < 2)).le
  have hm := mul_nonneg hp (sub_nonneg.mpr hl)
  unfold quadraticTwoLogCost
  split_ifs with h0 h1
  · linarith only [hm]
  · nlinarith only [hm, sq_nonneg (Real.log x)]
  · exact le_refl _

/-- For every real x, the common logarithmic envelope is strictly below (log x)^2.
Its difference is half the sum of (log x-log 2)^2 and (log 2)^2. Positivity of
log 2 makes the comparison strict, independently of the cutoff. -/
theorem quadraticTwoLog_envelope_lt_square (x : ℝ) :
    (Real.log x) ^ 2 / 2 + Real.log 2 * (Real.log x - Real.log 2) < (Real.log x) ^ 2 := by
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num only : (1 : ℝ) < 2)
  nlinarith only [sq_nonneg (Real.log x - Real.log 2), sq_pos_of_pos hp]

end PseudoPrime.LLS.PaperStatements
