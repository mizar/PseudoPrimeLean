/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TaperedPrimePowerCost
public import PseudoPrime.LLS.OddEndpointTwoCostWitness

/-! # Finite-cutoff reciprocal costs for odd quadratic witnesses -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- At cutoff Y, the quadratic value at two selects a reciprocal cost retaining
the taper subtraction: K log 2/Y at zero, zero at one and 2J log 2/Y at minus one.
K is the exponent cutoff and J counts its odd exponents. Used by the endpoint
witness comparison instead of the infinite geometric-tail constants. -/
noncomputable def taperedTwoReciprocalCost (Y : ℝ) (c : ℂ) : ℝ :=
  if c = 0 then Real.log 2 - (⌊Real.log Y / Real.log 2⌋₊ : ℝ) * Real.log 2 / Y
  else
    if c = 1 then 0
    else
      (4 / 3 : ℝ) * Real.log 2 -
        ((Finset.Icc 1 ⌊Real.log Y / Real.log 2⌋₊).filter Odd).card * (2 * Real.log 2) / Y

open AnalyticNumberTheory.Arithmetic in
/-- For a quadratic primitive associate at any real cutoff, its exact two-adic
reciprocal correction is at most the tapered cost. Check the three values at two
and use the finite geometric bounds or exact vanishing. This feeds reciprocal input. -/
theorem twoAdicReciprocalCorrection_le_tapered {N : ℕ} (χ : DirichletCharacter ℂ N) (Y : ℝ)
    (hquad : χ.primitiveCharacter.IsQuadratic) :
    twoAdicReciprocalCorrection Y χ ≤ taperedTwoReciprocalCost Y (χ.primitiveCharacter 2) := by
  rcases hquad (2 : ZMod χ.conductor) with h0 | h1 | hm
  · rw [taperedTwoReciprocalCost, ite_eq_left h0]
    exact twoAdicReciprocalCorrection_le_tapered_zero Y χ h0
  · have hn0 : χ.primitiveCharacter 2 ≠ 0 := by
      rw [h1]; exact one_ne_zero
    rw [taperedTwoReciprocalCost, ite_eq_right hn0, ite_eq_left h1]
    exact (twoAdicReciprocalCorrection_eq_zero_of_apply_two_eq_one Y χ h1).le
  · have hn0 : χ.primitiveCharacter 2 ≠ 0 := by
      rw [hm]
      exact neg_ne_zero.mpr one_ne_zero
    have hn1 : χ.primitiveCharacter 2 ≠ 1 := by
      rw [hm]; norm_num only
    rw [taperedTwoReciprocalCost, ite_eq_right hn0, ite_eq_right hn1]
    exact twoAdicReciprocalCorrection_le_tapered_neg_one Y χ hm

/-- At Y>=2, every non-one value at two saves at least log 2/Y over the old
constant cost. Exponent one belongs to both the full and odd exponent sets.
This is a strict finite-scale improvement with no enumeration of input moduli. -/
theorem taperedTwoReciprocalCost_le_sub_log_div {Y : ℝ} (hY : 2 ≤ Y) (c : ℂ) (hc : c ≠ 1) :
    taperedTwoReciprocalCost Y c ≤ quadraticTwoReciprocalCost c - Real.log 2 / Y := by
  have hy : 0 < Y := by linarith only [hY]
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have hlog := Real.log_le_log (by norm_num only : (0 : ℝ) < 2) hY
  have hK : 1 ≤ ⌊Real.log Y / Real.log 2⌋₊ :=
    (Nat.one_le_floor_iff _).mpr ((le_div_iff₀ hl).mpr (by simpa only [one_mul] using hlog))
  have hKR : (1 : ℝ) ≤ (⌊Real.log Y / Real.log 2⌋₊ : ℝ) := Nat.one_le_cast.mpr hK
  have hmem : 1 ∈ (Finset.Icc 1 ⌊Real.log Y / Real.log 2⌋₊).filter Odd :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hK⟩, by decide⟩
  have hJR : (1 : ℝ) ≤ (((Finset.Icc 1 ⌊Real.log Y / Real.log 2⌋₊).filter Odd).card : ℝ) :=
    Nat.one_le_cast.mpr (Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨1, hmem⟩))
  have hd := (div_pos hl hy).le
  by_cases h0 : c = 0
  · simp only [taperedTwoReciprocalCost, quadraticTwoReciprocalCost, ite_eq_left h0]
    simp only [mul_div_assoc]
    have hm := mul_le_mul_of_nonneg_right hKR hd
    nlinarith only [hm]
  · simp only [taperedTwoReciprocalCost, quadraticTwoReciprocalCost, ite_eq_right h0,
      ite_eq_right hc]
    simp only [mul_div_assoc]
    have hm := mul_le_mul_of_nonneg_right hJR hd
    nlinarith only [hm, hd]

open AnalyticNumberTheory.Arithmetic AnalyticNumberTheory.RiemannZeta in
/-- Under RH and odd-prime triviality through Y>=2, any upper bound c on the
exact two-adic correction gives the stated reciprocal lower bound. Apply the
exact difference identity before inserting the Riemann lower bound. No quadratic
branch or infinite-tail bound is imposed here. -/
theorem reciprocalSum_re_ge_of_twoAdicCorrection_le {N : ℕ} (χ : DirichletCharacter ℂ N) {Y c : ℝ}
    (hY : 2 ≤ Y) (hRH : RiemannHypothesis)
    (ht : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ Y → χ.primitiveCharacter p = 1)
    (hC : twoAdicReciprocalCorrection Y χ ≤ c) :
    Real.log Y - 31551 / 20000 - c ≤
      (characterReciprocalWeightedSum Y χ.primitiveCharacter).re := by
  have hy1 : 1 ≤ Y := by linarith only [hY]
  have ho :
    ∀ {k p : ℕ},
      k ∈ Finset.Icc 1 ⌊Real.log Y / Real.log 2⌋₊ →
        p ∈ Finset.Ioc 0 ⌊Y ^ ((1 : ℝ) / k)⌋₊ → p.Prime → Odd p → χ.primitiveCharacter p = 1 := by
    intro k p hk hp hprime hodd
    exact ht p hprime hodd (cast_le_of_mem_root_cutoff hy1 (Finset.mem_Icc.mp hk).1 hp)
  have he := reciprocalWeightedSum_sub_re_eq_twoAdicCorrection_of_eq_one Y χ hY ho
  have hr := reciprocalWeightedMangoldtSum_ge_log_sub_31551_div_20000 hRH hY
  linarith only [he, hr, hC]

/-- For x>=1,Y>=2 and a non-one value at two, substituting the tapered cost
strictly decreases the endpoint limit at the same x,Y,D. Its reciprocal-cost
coefficient is positive. This verifies an analytic improvement of the criterion. -/
theorem taperedTwoCostLimit_lt_constant (q : ℕ) {x Y : ℝ} (hx : 1 ≤ x) (hY : 2 ≤ Y) (c : ℂ)
    (hc : c ≠ 1) (D : ℝ) :
    oddEndpointTwoCostLimit q x Y (taperedTwoReciprocalCost Y c) D <
      oddEndpointTwoCostLimit q x Y (quadraticTwoReciprocalCost c) D := by
  have hy : 0 < Y := by linarith only [hY]
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have hcost :=
    (taperedTwoReciprocalCost_le_sub_log_div hY c hc).trans_lt (sub_lt_self _ (div_pos hl hy))
  have hs : 1 < Real.sqrt Y := by nlinarith only [Real.sq_sqrt hy.le, Real.sqrt_nonneg Y, hY]
  have hd : 0 < 1 - 1 / Real.sqrt Y :=
    sub_pos.mpr (by simpa only [one_div] using inv_lt_one_of_one_lt₀ hs)
  have hk : 0 < 2 + (Real.log x + 2) / Real.sqrt x :=
    lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2)
      (le_add_of_nonneg_right
        (div_nonneg (by linarith only [Real.log_nonneg hx]) (Real.sqrt_nonneg x)))
  have hm := mul_lt_mul_of_pos_left (div_lt_div_of_pos_right hcost (sq_pos_of_pos hd)) hk
  dsimp only [oddEndpointTwoCostLimit, oddEndpointCostLimit]
  linarith only [hm]

/-- At Y>=2, the tapered cost for every value at two is at most
(4/3)log 2-log 2/Y. The non-one branches use the retained saving; the value-one
cost is zero and the proposed envelope is nonnegative. This removes character
values and exponent counts from a sufficient endpoint criterion. -/
theorem taperedTwoReciprocalCost_le_uniform {Y : ℝ} (hY : 2 ≤ Y) (c : ℂ) :
    taperedTwoReciprocalCost Y c ≤ (4 / 3 : ℝ) * Real.log 2 - Real.log 2 / Y := by
  by_cases hc : c = 1
  · simp only [taperedTwoReciprocalCost, hc, one_ne_zero, ite_false, ite_true]
    have hy : 0 < Y := by linarith only [hY]
    have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num only)
    have hm := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ Y by linarith only [hY]) hl
    have hd : Real.log 2 / Y ≤ Real.log 2 := (div_le_iff₀ hy).mpr (by simpa only [mul_one] using hm)
    linarith only [hd, hl]
  · exact
      (taperedTwoReciprocalCost_le_sub_log_div hY c hc).trans
        (sub_le_sub_right (quadraticTwoReciprocalCost_le_four_thirds c) _)

end PseudoPrime.LLS.PaperStatements
