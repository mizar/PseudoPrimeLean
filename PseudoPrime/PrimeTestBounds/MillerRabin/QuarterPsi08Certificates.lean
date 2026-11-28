/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsi08Gap
import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.Analysis.LogPowerTailIntegral
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PowerLogMomentAbel
import Mathlib.Tactic.GCongr

/-! # Rational inputs for the central quarter comparison -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A rational upper bound for a negative rational power can be checked
by clearing the exponent denominator and testing natural powers only. -/
theorem quarter_rpow_upper {r U : ℝ} {p q : ℕ} (hr : 0 < r) (hU : 0 ≤ U) (hq : 0 < q)
    (h : 1 ≤ U ^ q * r ^ p) : r ^ (-((p : ℝ) / q)) ≤ U := by
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg hr.le _) hU hq').1
  rw [Real.rpow_natCast, Real.rpow_natCast, ← Real.rpow_natCast (r ^ (-((p : ℝ) / q))) q, ←
    Real.rpow_mul hr.le,
    show -((p : ℝ) / q) * q = -(p : ℝ) by rw [neg_mul, div_mul_cancel₀ _ hq'.ne'],
    Real.rpow_neg hr.le, Real.rpow_natCast, ← one_div]
  exact (div_le_iff₀ (pow_pos hr _)).2 h

/-- The right endpoint of the central interval has the certified logarithm
and three negative-power upper bounds from the paper certificate. -/
theorem quarter_psi08_right_inputs :
    let X : ℝ := (533 / 2) ^ 2
    Real.log X ≤ 44683 / 4000 ∧
      X ^ (-(27 / 25 : ℝ)) ≤ 577 / 100000000 ∧
      X ^ (-(29 / 50 : ℝ)) ≤ 15353 / 10000000 ∧ X ^ (-(83 / 100 : ℝ)) ≤ 1881 / 20000000 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h :=
      (Analysis.rationalLogIntervalCheck_sound (N := 284089 / 4) (j := 17) (n := 30) (lo :=
          558537 / 50000) (hi := 44683 / 4000) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
    convert h using 1
    norm_num only
  · simpa only [Nat.cast_ofNat] using
      quarter_rpow_upper (p := 27) (q := 25) (by norm_num only) (by norm_num only) (by decide)
        (by norm_num only)
  · simpa only [Nat.cast_ofNat] using
      quarter_rpow_upper (p := 29) (q := 50) (by norm_num only) (by norm_num only) (by decide)
        (by norm_num only)
  · simpa only [Nat.cast_ofNat] using
      quarter_rpow_upper (p := 83) (q := 100) (by norm_num only) (by norm_num only) (by decide)
        (by norm_num only)

/-- A single closed moment can be bounded by its value at upper inputs for
the logarithm and both decaying powers. -/
private theorem moment_upper {X l S T : ℝ} (hX : 1 ≤ X) (hl : Real.log X ≤ l)
    (hS : X ^ (-(29 / 50 : ℝ)) ≤ S) (hT : X ^ (-(83 / 100 : ℝ)) ≤ T) (k : ℕ) :
    quarterMomentClosedTail k X ≤
      2 * T * l ^ k + S * Analysis.logPowerTailPoly (29 / 50) k l +
        3 / 4 * (T * Analysis.logPowerTailPoly (83 / 100) k l) := by
  have hx := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) hX
  have hz := Real.log_nonneg hX
  have he := Real.rpow_add hx (-(79 / 50 : ℝ)) (3 / 4)
  rw [show -(79 / 50 : ℝ) + 3 / 4 = -(83 / 100 : ℝ) by norm_num only] at he
  unfold quarterMomentClosedTail AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight
  rw [show
      2 * (X ^ (-(79 / 50 : ℝ)) * Real.log X ^ k) * X ^ (3 / 4 : ℝ) =
        2 * X ^ (-(83 / 100 : ℝ)) * Real.log X ^ k
      by
      rw [he]; ring]
  have hu₁ := Analysis.log_power_tail_poly_mono (by norm_num only : (0 : ℝ) < 29 / 50) hz hl k
  have hu₂ := Analysis.log_power_tail_poly_mono (by norm_num only : (0 : ℝ) < 83 / 100) hz hl k
  have hv₁ := Analysis.log_power_tail_poly_nonneg (by norm_num only : (0 : ℝ) < 29 / 50) hz k
  have hv₂ := Analysis.log_power_tail_poly_nonneg (by norm_num only : (0 : ℝ) < 83 / 100) hz k
  have hT0 := (Real.rpow_nonneg hx.le _).trans hT
  have hS0 := (Real.rpow_nonneg hx.le _).trans hS
  gcongr

/-- The rational endpoint inputs certify the positive right-end gap. -/
theorem quarter_psi08_gap_right : (1 / 2000 : ℝ) < quarterPsi08Gap (533 / 2) := by
  let r : ℝ := 533 / 2
  let l : ℝ := 44683 / 4000
  let P : ℝ := 577 / 100000000
  let S : ℝ := 15353 / 10000000
  let T : ℝ := 1881 / 20000000
  obtain ⟨hl, hP, hS, hT⟩ := quarter_psi08_right_inputs
  change Real.log (r ^ 2) ≤ l at hl
  change (r ^ 2) ^ (-(27 / 25 : ℝ)) ≤ P at hP
  change (r ^ 2) ^ (-(29 / 50 : ℝ)) ≤ S at hS
  change (r ^ 2) ^ (-(83 / 100 : ℝ)) ≤ T at hT
  have hx : 1 ≤ r ^ 2 := by norm_num only [r]
  have h₀ := moment_upper hx hl hS hT 0
  have h₁ := moment_upper hx hl hS hT 1
  have h₂ := moment_upper hx hl hS hT 2
  rw [Real.log_pow, Nat.cast_ofNat] at hl
  rw [← Real.rpow_two r, ← Real.rpow_mul (by norm_num only [r]),
    show 2 * -(27 / 25 : ℝ) = -(54 / 25 : ℝ) by norm_num only] at hP
  let z : ℝ := 21 / 8 + 2 * Real.log r
  let Z : ℝ := 21 / 8 + l
  have hz : 0 ≤ z := by
    have h := Real.log_nonneg (show 1 ≤ r by norm_num only [r])
    dsimp only [z]
    linarith only [h]
  have hZ : z ≤ Z := by exact add_le_add (le_refl _) hl
  have hp : 0 ≤ r ^ (-(54 / 25 : ℝ)) := Real.rpow_nonneg (by norm_num only [r]) _
  have hpow : r ^ (-(54 / 25 : ℝ)) * z ^ 5 ≤ P * Z ^ 5 :=
    mul_le_mul hP (pow_le_pow_left₀ hz hZ 5) (pow_nonneg hz _) (hp.trans hP)
  have hpoly :
    r ^ (-(54 / 25 : ℝ)) * quarterMomentPolynomial z ≤ P * quarterMomentPolynomial Z := by
    apply mul_le_mul hP (quarter_moment_polynomial_le hz hZ) _ (hp.trans hP)
    unfold quarterMomentPolynomial
    positivity
  change 1 / 2000 < quarterPsi08Gap r
  unfold quarterPsi08Gap quarterEulerClosedTailCap
  dsimp only [z] at hpow hpoly
  norm_num only [r, P, S, T, l, Z, quarterMomentPolynomial, Analysis.logPowerTailPoly,
    Nat.cast_ofNat, Nat.cast_one] at h₀ h₁ h₂ hpow hpoly ⊢
  linarith only [h₀, h₁, h₂, hpow, hpoly]

/-- Evaluate the gap from below using a radius interval and upper inputs for
the logarithm and three negative powers. -/
private theorem gap_lower_of_inputs {r a b l P S T : ℝ} (ha : 0 < a) (har : a ≤ r) (hrb : r ≤ b)
    (hx : 1 ≤ r ^ 2) (hl : Real.log (r ^ 2) ≤ l) (hP : (r ^ 2) ^ (-(27 / 25 : ℝ)) ≤ P)
    (hS : (r ^ 2) ^ (-(29 / 50 : ℝ)) ≤ S) (hT : (r ^ 2) ^ (-(83 / 100 : ℝ)) ≤ T) :
    let A : ℝ := 27 / 25
    let C : ℝ := A ^ 5 / 120 * (58721 / 10 ^ 6)
    let Z : ℝ := 21 / 8 + l
    let M := fun k : ℕ ↦
      2 * T * l ^ k + S * Analysis.logPowerTailPoly (29 / 50) k l +
        3 / 4 * (T * Analysis.logPowerTailPoly (83 / 100) k l)
    A ^ 5 * (3117 / 400 - 1151 / 5000 - 351 / (200 * a)) - (3 / 4 - A ^ 5 * (24439 / 50000)) * b -
        39 / 1000 * A ^ 2 -
        (4 * b + 5517 / 1000) * C * P * Z ^ 5 -
        C * P * quarterMomentPolynomial Z -
        4 * (3 / 8 * M 0 + 81 / 200 * M 1 + 729 / 5000 * M 2) ≤
      quarterPsi08Gap r := by
  have hr := ha.trans_le har
  have h₀ := moment_upper hx hl hS hT 0
  have h₁ := moment_upper hx hl hS hT 1
  have h₂ := moment_upper hx hl hS hT 2
  rw [Real.log_pow, Nat.cast_ofNat] at hl
  rw [← Real.rpow_two r, ← Real.rpow_mul hr.le,
    show 2 * -(27 / 25 : ℝ) = -(54 / 25 : ℝ) by norm_num only] at hP
  let z : ℝ := 21 / 8 + 2 * Real.log r
  let Z : ℝ := 21 / 8 + l
  have hz : 0 ≤ z := by
    have h := Real.log_nonneg hx
    rw [Real.log_pow, Nat.cast_ofNat] at h
    dsimp only [z]
    linarith only [h]
  have hZ : z ≤ Z := by exact add_le_add (le_refl _) hl
  have hp : 0 ≤ r ^ (-(54 / 25 : ℝ)) := Real.rpow_nonneg hr.le _
  have hpow : r ^ (-(54 / 25 : ℝ)) * z ^ 5 ≤ P * Z ^ 5 :=
    mul_le_mul hP (pow_le_pow_left₀ hz hZ 5) (pow_nonneg hz _) (hp.trans hP)
  have hpoly :
    r ^ (-(54 / 25 : ℝ)) * quarterMomentPolynomial z ≤ P * quarterMomentPolynomial Z := by
    apply mul_le_mul hP (quarter_moment_polynomial_le hz hZ) _ (hp.trans hP)
    unfold quarterMomentPolynomial
    positivity
  have hrec : (351 : ℝ) / (200 * r) ≤ 351 / (200 * a) :=
    div_le_div_of_nonneg_left (by norm_num only) (mul_pos (by norm_num only) ha)
      (mul_le_mul_of_nonneg_left har (by norm_num only))
  have hcond :
    (4 * r + 5517 / 1000) * (r ^ (-(54 / 25 : ℝ)) * z ^ 5) ≤ (4 * b + 5517 / 1000) * (P * Z ^ 5) :=
    mul_le_mul (by linarith only [hrb]) hpow (mul_nonneg hp (pow_nonneg hz _))
      (by linarith only [hr, hrb])
  dsimp only [quarterPsi08Gap, quarterEulerClosedTailCap]
  dsimp only [z, Z] at hcond hpoly
  linarith only [h₀, h₁, h₂, hrec, hcond, hpoly, hrb]

/-- The upper logarithm bound at radius 42 is shared by both left comparisons. -/
private theorem log_square_42_upper : Real.log ((42 : ℝ) ^ 2) ≤ 373767 / 50000 := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1764) (j := 11) (n := 20) (lo := 747533 / 100000)
        (hi := 373767 / 50000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  convert h using 1
  norm_num only

/-- The central comparison exceeds 2 on the single lower-radius box. -/
theorem quarter_psi08_gap_box {r : ℝ} (hr : r ∈ Set.Icc 37 42) : 2 < quarterPsi08Gap r := by
  have hmin : (37 : ℝ) ≤ r := hr.1
  have hmax : r ≤ (42 : ℝ) := hr.2
  have ha : (0 : ℝ) < 37 := by norm_num only
  have hxa : (0 : ℝ) < (37 : ℝ) ^ 2 := sq_pos_of_pos ha
  have hx₁ : (37 : ℝ) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ ha.le hmin 2
  have hx₂ : r ^ 2 ≤ (42 : ℝ) ^ 2 := pow_le_pow_left₀ (ha.le.trans hmin) hmax 2
  have hx : 1 ≤ r ^ 2 := (by norm_num only : (1 : ℝ) ≤ (37 : ℝ) ^ 2).trans hx₁
  have hl := (Real.log_le_log (hxa.trans_le hx₁) hx₂).trans log_square_42_upper
  have hp0 : (r ^ 2) ^ (-(27 / 25 : ℝ)) ≤ 40991 / 100000000 := by
    apply (Real.rpow_le_rpow_of_nonpos hxa hx₁ (by norm_num only)).trans
    simpa only [Nat.cast_ofNat] using
      quarter_rpow_upper (p := 27) (q := 25) hxa (by norm_num only) (by decide) (by norm_num only)
  have hp1 : (r ^ 2) ^ (-(29 / 50 : ℝ)) ≤ 1516653 / 100000000 := by
    apply (Real.rpow_le_rpow_of_nonpos hxa hx₁ (by norm_num only)).trans
    simpa only [Nat.cast_ofNat] using
      quarter_rpow_upper (p := 29) (q := 50) hxa (by norm_num only) (by decide) (by norm_num only)
  have hp2 : (r ^ 2) ^ (-(83 / 100 : ℝ)) ≤ 249337 / 100000000 := by
    apply (Real.rpow_le_rpow_of_nonpos hxa hx₁ (by norm_num only)).trans
    simpa only [Nat.cast_ofNat] using
      quarter_rpow_upper (p := 83) (q := 100) hxa (by norm_num only) (by decide) (by norm_num only)
  have hg := gap_lower_of_inputs ha hmin hmax hx hl hp0 hp1 hp2
  norm_num only [quarterMomentPolynomial, Analysis.logPowerTailPoly, Nat.cast_ofNat,
    Nat.cast_one] at hg
  linarith only [hg]

/-- The left endpoint of the concavity interval clears the sharper bound. -/
theorem quarter_psi08_gap_left : (3.65 : ℝ) < quarterPsi08Gap 42 := by
  let r : ℝ := 42
  change 3.65 < quarterPsi08Gap r
  have hmin : (42 : ℝ) ≤ r := le_refl _
  have hmax : r ≤ (42 : ℝ) := le_refl _
  have ha : (0 : ℝ) < 42 := by norm_num only
  have hxa : (0 : ℝ) < (42 : ℝ) ^ 2 := sq_pos_of_pos ha
  have hx₁ : (42 : ℝ) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ ha.le hmin 2
  have hx₂ : r ^ 2 ≤ (42 : ℝ) ^ 2 := pow_le_pow_left₀ (ha.le.trans hmin) hmax 2
  have hx : 1 ≤ r ^ 2 := (by norm_num only : (1 : ℝ) ≤ (42 : ℝ) ^ 2).trans hx₁
  have hl := (Real.log_le_log (hxa.trans_le hx₁) hx₂).trans log_square_42_upper
  have hp0 : (r ^ 2) ^ (-(27 / 25 : ℝ)) ≤ 15587 / 50000000 := by
    apply (Real.rpow_le_rpow_of_nonpos hxa hx₁ (by norm_num only)).trans
    simpa only [Nat.cast_ofNat] using
      quarter_rpow_upper (p := 27) (q := 25) hxa (by norm_num only) (by decide) (by norm_num only)
  have hp1 : (r ^ 2) ^ (-(29 / 50 : ℝ)) ≤ 52371 / 4000000 := by
    apply (Real.rpow_le_rpow_of_nonpos hxa hx₁ (by norm_num only)).trans
    simpa only [Nat.cast_ofNat] using
      quarter_rpow_upper (p := 29) (q := 50) hxa (by norm_num only) (by decide) (by norm_num only)
  have hp2 : (r ^ 2) ^ (-(83 / 100 : ℝ)) ≤ 101013 / 50000000 := by
    apply (Real.rpow_le_rpow_of_nonpos hxa hx₁ (by norm_num only)).trans
    simpa only [Nat.cast_ofNat] using
      quarter_rpow_upper (p := 83) (q := 100) hxa (by norm_num only) (by decide) (by norm_num only)
  have hg := gap_lower_of_inputs ha hmin hmax hx hl hp0 hp1 hp2
  norm_num only [quarterMomentPolynomial, Analysis.logPowerTailPoly, Nat.cast_ofNat,
    Nat.cast_one] at hg
  linarith only [hg]

/-- The three certified comparisons and concavity give positivity on [76,533]. -/
theorem quarter_psi08_gap_positive {L : ℝ} (hL : L ∈ Set.Icc 76 533) :
    0 < quarterPsi08Gap (L / 2) := by
  exact
    quarter_psi08_gap_pos hL (fun _ hr ↦ quarter_psi08_gap_box hr) quarter_psi08_gap_concave
      quarter_psi08_gap_left quarter_psi08_gap_right

end PseudoPrime.PrimeTestBounds.MillerRabin
