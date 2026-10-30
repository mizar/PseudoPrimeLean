/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RationalPoleFiniteEntrance

/-! # Explicit finite entrance for the fourth-pole quadratic bound -/

public section

namespace PseudoPrime.LLS.PaperStatements

/-- The exact fourth-pole principal gap is at least 28379/100000.
Rewrite the public cutoff certificate into its closed form.
This supplies the sharper principal margin for the explicit coefficient 777/1000. -/
theorem fourPole_sharp_principal_gap :
    (28379 / 100000 : ℝ) ≤
      2 * ((484820459 / 528581976 : ℝ) * Real.exp (-(14 / 13))) -
        (2 * (13 / 25 : ℝ) * Real.exp (14 / 25) / (1 + 13 / 25) ^ 4) := by
  have hA := rationalPole_four_principal_gap
  have he :
    (rationalPoleFourKernel.function (1 / 2)).re =
      2 * (13 / 25 : ℝ) * Real.exp (14 / 25) / (1 + 13 / 25) ^ 4 := by
    rw [rationalPoleFourKernel, rationalPole_half_value]
  rw [rationalPole_four_cutoff, he] at hA
  exact hA

/-- For logarithm parameter at least two, scale `x=(777/1000)L^2` has explicit
square-root, quarter-power, negative-power and logarithmic comparison bounds. -/
theorem fourPole_sharp_finite_scale_bounds {L : ℝ} (hL : 2 ≤ L) :
    let x := (777 / 1000 : ℝ) * L ^ 2
    L ≤ x ∧
      x ≤ L ^ 2 ∧
      (8814 / 10000 : ℝ) * L ≤ Real.sqrt x ∧
      Real.sqrt x ≤ L ∧
      x ^ (1 / 4 : ℝ) ≤ Real.sqrt L ∧
      x ^ (-3 / 4 : ℝ) ≤ 1 / Real.sqrt L ∧ Real.log x ≤ 4 * Real.sqrt L := by
  let x := (777 / 1000 : ℝ) * L ^ 2
  have hL0 : 0 < L := (by norm_num only : (0 : ℝ) < 2).trans_le hL
  have hL1 : 1 ≤ L := (by norm_num only : (1 : ℝ) ≤ 2).trans hL
  have hxl : L ≤ x := by
    dsimp only [x]
    nlinarith only [sq_nonneg (L - 2), hL]
  have hxu : x ≤ L ^ 2 := by
    dsimp only [x]
    nlinarith only [sq_nonneg L]
  have hx0 : 0 < x := hL0.trans_le hxl
  have hsl : (8814 / 10000 : ℝ) * L ≤ Real.sqrt x := by
    apply (Real.le_sqrt (mul_nonneg (by norm_num only) hL0.le) hx0.le).mpr
    dsimp only [x]
    nlinarith only [sq_nonneg L]
  have hsu : Real.sqrt x ≤ L := Real.sqrt_le_iff.mpr ⟨hL0.le, hxu⟩
  have hp : x ^ (1 / 4 : ℝ) ≤ Real.sqrt L := by
    have h := Real.rpow_le_rpow hx0.le hxu (by norm_num only : (0 : ℝ) ≤ 1 / 4)
    rw [← Real.rpow_natCast L 2, ← Real.rpow_mul hL0.le] at h
    norm_num only at h
    simpa only [Real.sqrt_eq_rpow] using h
  have hn : x ^ (-3 / 4 : ℝ) ≤ 1 / Real.sqrt L := by
    have h :=
      (Real.rpow_le_rpow_of_nonpos hL0 hxl (by norm_num only : (-3 / 4 : ℝ) ≤ 0)).trans
        (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num only : (-3 / 4 : ℝ) ≤ -(1 / 2)))
    rw [Real.rpow_neg hL0.le] at h
    change x ^ (-3 / 4 : ℝ) ≤ (L ^ (1 / 2 : ℝ))⁻¹ at h
    simpa only [Real.sqrt_eq_rpow, one_div] using h
  have hlog : Real.log x ≤ 4 * Real.sqrt L := by
    have h := Real.log_le_log hx0 hxu
    rw [Real.log_pow] at h
    have hr := Real.log_le_rpow_div hL0.le (by norm_num only : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at hr
    norm_num only [Nat.cast_ofNat] at h hr
    linarith only [h, hr]
  exact ⟨hxl, hxu, hsl, hsu, hp, hn, hlog⟩

/-- If conductor and ambient logarithms are at most `L+2`, the full scalar
fourth-pole budget at scale `(777/1000)L^2` is at most `(2501/10000)L+3000 sqrt L`. -/
theorem fourPole_sharp_finite_budget_le {L F G : ℝ} (hL : 2 ≤ L) (hF : F ≤ L + 2) (hG : G ≤ L + 2) :
    let x := (777 / 1000 : ℝ) * L ^ 2
    (2501 / 10000 : ℝ) * F + 1003 + (24 * F + 793) * x ^ (-3 / 4 : ℝ) +
        (65 * x ^ (1 / 4 : ℝ) + 120 / Real.sqrt x) +
        (20 / Real.sqrt x) * (Real.log x / Real.log 2) * G ≤
      (2501 / 10000 : ℝ) * L + 3000 * Real.sqrt L := by
  let x := (777 / 1000 : ℝ) * L ^ 2
  obtain ⟨hxl, hxu, hsl, hsu, hp, hn, hlog⟩ := fourPole_sharp_finite_scale_bounds hL
  have hL0 : 0 < L := (by norm_num only : (0 : ℝ) < 2).trans_le hL
  have hx0 : 0 < x := hL0.trans_le hxl
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hs1 : 1 ≤ Real.sqrt L :=
    (Real.le_sqrt (by norm_num only) hL0.le).mpr (by nlinarith only [hL])
  have hsx1 : 1 ≤ Real.sqrt x := by linarith only [hsl, hL]
  have hc : (24 * F + 793) * x ^ (-3 / 4 : ℝ) ≤ 1000 * Real.sqrt L := by
    have hcoeff : 24 * F + 793 ≤ 1000 * L := by linarith only [hF, hL]
    calc
      _ ≤ (1000 * L) * x ^ (-3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hx0.le _)
      _ ≤ (1000 * L) * (1 / Real.sqrt L) :=
        mul_le_mul_of_nonneg_left hn (mul_nonneg (by norm_num only) hL0.le)
      _ = _ := by rw [mul_one_div, mul_div_assoc, Real.div_sqrt]
  have hi : 120 / Real.sqrt x ≤ (120 : ℝ) := by
    apply (div_le_iff₀ hsx).mpr
    linarith only [hsx1]
  have hlog0 : 0 ≤ Real.log x :=
    Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 2).trans (hL.trans hxl))
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have htwo0 : 0 < Real.log 2 := (by norm_num only : (0 : ℝ) < 1 / 2).trans_le htwo
  have hlogcap : Real.log x / Real.log 2 ≤ 8 * Real.sqrt L := by
    apply (div_le_iff₀ htwo0).mpr
    nlinarith only [hlog, mul_le_mul_of_nonneg_right htwo hsL.le]
  have hden : 20 / Real.sqrt x ≤ 40 / L := by
    apply (div_le_div_iff₀ hsx hL0).mpr
    change (8814 / 10000 : ℝ) * L ≤ Real.sqrt x at hsl
    linarith only [hsl, hL0]
  have hlocal : (20 / Real.sqrt x) * (Real.log x / Real.log 2) * G ≤ 640 * Real.sqrt L := by
    calc
      _ ≤ (20 / Real.sqrt x) * (Real.log x / Real.log 2) * (2 * L) :=
        mul_le_mul_of_nonneg_left (by linarith only [hG, hL])
          (mul_nonneg (div_nonneg (by norm_num only) hsx.le) (div_nonneg hlog0 htwo0.le))
      _ ≤ (20 / Real.sqrt x) * (8 * Real.sqrt L) * (2 * L) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlogcap (div_nonneg (by norm_num only) hsx.le))
          (mul_nonneg (by norm_num only) hL0.le)
      _ ≤ (40 / L) * (8 * Real.sqrt L) * (2 * L) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hden (mul_nonneg (by norm_num only) hsL.le))
          (mul_nonneg (by norm_num only) hL0.le)
      _ = _ := by
        calc
          _ = (L * L⁻¹) * (640 * Real.sqrt L) := by ring
          _ = _ := by rw [mul_inv_cancel₀ hL0.ne', one_mul]
  have hmain := mul_le_mul_of_nonneg_left hF (by norm_num only : (0 : ℝ) ≤ 2501 / 10000)
  have hpow := mul_le_mul_of_nonneg_left hp (by norm_num only : (0 : ℝ) ≤ 65)
  nlinarith only [hmain, hpow, hc, hi, hlocal, hs1]

/-- For `L ≥ 10^18`, the explicit scalar budget is strictly below the full principal
main gap at scale `(777/1000)L^2`. The square-root error is absorbed by the rational
linear margin, without finite enumeration. -/
theorem fourPole_sharp_finite_scalar_gap {L F G : ℝ} (hL : (10 : ℝ) ^ 18 ≤ L) (hF : F ≤ L + 2)
    (hG : G ≤ L + 2) :
    let x := (777 / 1000 : ℝ) * L ^ 2
    (2501 / 10000 : ℝ) * F + 1003 + (24 * F + 793) * x ^ (-3 / 4 : ℝ) +
        (65 * x ^ (1 / 4 : ℝ) + 120 / Real.sqrt x) +
        (20 / Real.sqrt x) * (Real.log x / Real.log 2) * G <
      Real.sqrt x *
        (2 * ((484820459 / 528581976 : ℝ) * Real.exp (-(14 / 13))) -
          (2 * (13 / 25 : ℝ) * Real.exp (14 / 25) / (1 + 13 / 25) ^ 4)) := by
  let x := (777 / 1000 : ℝ) * L ^ 2
  have hL2 : 2 ≤ L := by
    norm_num only at hL; linarith only [hL]
  have hL0 : 0 < L := (by norm_num only : (0 : ℝ) < 2).trans_le hL2
  have hb := fourPole_sharp_finite_budget_le hL2 hF hG
  have hsbig : (10 : ℝ) ^ 9 ≤ Real.sqrt L := by
    apply (Real.le_sqrt (by norm_num only) hL0.le).mpr
    norm_num only at hL ⊢
    exact hL
  have hspos := Real.sqrt_pos.mpr hL0
  have hsmul := mul_le_mul_of_nonneg_right hsbig hspos.le
  have hsq := Real.sq_sqrt hL0.le
  have herr : (2501 / 10000 : ℝ) * L + 3000 * Real.sqrt L < (25013 / 100000 : ℝ) * L := by
    norm_num only at hsmul
    nlinarith only [hsmul, hsq, hL0]
  obtain ⟨hxl, _, hsl, _, _, _, _⟩ := fourPole_sharp_finite_scale_bounds hL2
  change (8814 / 10000 : ℝ) * L ≤ Real.sqrt x at hsl
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr (hL0.trans_le hxl)
  have hmain := mul_le_mul_of_nonneg_left fourPole_sharp_principal_gap hsx.le
  have hlow : (25013 / 100000 : ℝ) * L ≤ Real.sqrt x * (28379 / 100000 : ℝ) := by
    linarith only [hsl, hL0]
  exact hb.trans_lt (herr.trans_le (hlow.trans hmain))

/-- Under GRH, every odd nonsquare with `log n ≥ 10^18` has an odd prime
negative Jacobi witness at most `(777/1000)(log n)^2`.
The primitive conductor divides `4*n`, so both logarithmic inputs are at most
`log n+2`; apply the certified scalar entrance. -/
theorem fourPole_sharp_jacobi_explicit_entrance {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (10 : ℝ) ^ 18 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (777 / 1000 : ℝ) * (Real.log n) ^ 2 ∧ jacobiSym n p = -1 := by
  let : NeZero (4 * n) := ⟨(Nat.mul_pos (by norm_num only : (0 : ℕ) < 4) hn.pos).ne'⟩
  have hL2 : 2 ≤ Real.log n := by
    norm_num only at hL; linarith only [hL]
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn.pos
  have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 2)
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num only, Real.log_pow]
    norm_num only at h ⊢
    linarith only [h]
  have hG : Real.log (4 * (n : ℝ)) ≤ Real.log n + 2 := by
    rw [Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) hnR.ne']
    linarith only [hlog4]
  have hcon : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ 4 * n :=
    Nat.le_of_dvd (Nat.mul_pos (by norm_num only : (0 : ℕ) < 4) hn.pos)
      (DirichletCharacter.conductor_dvd_level (NumberTheory.complexQuadraticCharacter n hn))
  have hcon0 : 0 < (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    Nat.pos_of_ne_zero (NumberTheory.complexQuadraticCharacter n hn).conductor_ne_zero
  have hF : Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ Real.log n + 2 := by
    have h := Real.log_le_log (Nat.cast_pos.mpr hcon0) (Nat.cast_le.mpr hcon)
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at h
    exact h.trans hG
  obtain ⟨hxl, _, _, _, _, _, _⟩ := fourPole_sharp_finite_scale_bounds hL2
  apply fourPole_exists_jacobi_scalar bridge hGRH (hL2.trans hxl)
  exact fourPole_sharp_finite_scalar_gap hL hF hG

/-- Under GRH, every odd nonsquare with `log n ≥ 10^18` has an actual negative
odd-prime witness through `(777/1000)(log n)^2`, without a supplied arithmetic bridge. -/
theorem fourPole_sharp_jacobi_finite_witness {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (10 : ℝ) ^ 18 ≤ Real.log n) :
    ∃ p : ℕ,
      p ∈ NumberTheory.primeNegOneWitnessSet n ∧ (p : ℝ) ≤ (777 / 1000 : ℝ) * (Real.log n) ^ 2 := by
  obtain ⟨bridge⟩ := NumberTheory.exists_jacobiCharacterArithmeticData hn.pos hn hns
  obtain ⟨p, hp, ho, hb, hj⟩ := fourPole_sharp_jacobi_explicit_entrance bridge hGRH hL
  exact ⟨p, ⟨hp, ho, hj⟩, hb⟩

/-- Under the explicit logarithmic entrance, the least actual negative odd-prime
Jacobi witness obeys the certified coefficient `777/1000`. Minimize the witness set. -/
theorem fourPole_sharp_jacobi_finite_least {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (10 : ℝ) ^ 18 ≤ Real.log n)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (777 / 1000 : ℝ) * (Real.log n) ^ 2 := by
  obtain ⟨p, hp, hb⟩ := fourPole_sharp_jacobi_finite_witness hn hns hGRH hL
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw hp)).trans hb

end PseudoPrime.LLS.PaperStatements
