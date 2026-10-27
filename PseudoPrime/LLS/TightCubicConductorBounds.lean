/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.CubicSquareFactorBounds

/-! # Tight cubic budgets and conductor radii with constants 63/2 and 28 -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For q≥2 and x≥1, retain the exact constant terms of the cubic budget.
The reflected term is bounded by 207/100 and the nonnegative profile is
discarded only after multiplying by sqrt x. This avoids the earlier
constant relaxations and supplies the tight character estimate. -/
theorem cubicGapRationalBudget_le_tight {q : ℕ} (hq : 2 ≤ q) {x : ℝ} (hx : 1 ≤ x) :
    cubicGapRationalBudget q x ≤
      ((5 / 13 : ℝ) * Real.log q + 97 / 130) +
        ((2 / 5 : ℝ) * Real.log q + 103729 / 15000) / Real.sqrt x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (le_trans (by decide : 1 ≤ 2) hq)
  have hL := Real.log_nonneg hq1
  have hp0 : 0 ≤ x ^ (-(3 : ℝ)) := Real.rpow_nonneg hx0.le _
  have hp1 : x ^ (-(3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num only)
  have hleft : x ^ (-(3 : ℝ)) * ((207 / 100 : ℝ) - Real.log q) ≤ 207 / 100 := by
    have ha :=
      mul_le_mul_of_nonneg_left
        (show (207 / 100 : ℝ) - Real.log q ≤ 207 / 100 by linarith only [hL]) hp0
    have hb := mul_le_mul_of_nonneg_right hp1 (by norm_num only : (0 : ℝ) ≤ 207 / 100)
    exact ha.trans (by simpa only [one_mul] using hb)
  have hprof := mul_nonneg (reciprocalGapProfile_nonneg (by norm_num only : (0 : ℝ) < 3) x) hs.le
  have he :
    cubicGapRationalBudget q x * Real.sqrt x =
      ((5 / 13 : ℝ) * Real.log q + 97 / 130) * Real.sqrt x + (2 / 5 : ℝ) * Real.log q +
          25879 / 15000 +
          x ^ (-(3 : ℝ)) * ((207 / 100 : ℝ) - Real.log q) / 3 +
          9 / 2 -
        (3 / 4 : ℝ) * reciprocalGapProfile 3 x * Real.sqrt x := by
    unfold cubicGapRationalBudget reciprocalGapScalarPoleBudget reciprocalGapRealAxisBudget
      reciprocalGapSignedGammaBudget
    rw [reciprocalGap_left_power_factor (h := 3) hx0, Real.sqrt_inv]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring_nf
    simp only [mul_inv_cancel₀ hs.ne', mul_inv_cancel_right₀ hs.ne', one_mul]
    ring
  apply (mul_le_mul_iff_right₀ hs).mp
  simp only [mul_comm (Real.sqrt x)]
  rw [he]
  simp only [add_mul, div_mul_cancel₀ _ hs.ne']
  nlinarith only [hleft, hprof]

/-- Primitive nonprincipal GRH data satisfy the cubic character upper bound
with constants 97/130 and 103729/15000. Compose the rational budget with its
tight scalar estimate and remove square-root normalization. -/
theorem sqrt_mul_reciprocalGapCharacterSum_three_re_le_tight {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    Real.sqrt x * (reciprocalGapCharacterSum 3 χ x).re ≤
      ((5 / 13 : ℝ) * Real.log q + 97 / 130) * Real.sqrt x + (2 / 5 : ℝ) * Real.log q +
        103729 / 15000 := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr (zero_lt_one.trans_le hx)
  have hm :=
    mul_le_mul_of_nonneg_right
      ((reciprocalGapCharacterSum_three_re_le_rational hq hGRH hp hne hinv hx).trans
        (cubicGapRationalBudget_le_tight hq hx))
      hs.le
  rw [add_mul, div_mul_cancel₀ _ hs.ne'] at hm
  nlinarith only [hm]

/-- Radius A+sqrt(A²+(8/5)G+28+(4/3)E), where A=(10/13)G+63/2.
G bounds the conductor logarithm and E bounds the character-sensitive cost.
Its square gives the witness upper bound in the subsequent extraction. -/
noncomputable def tightCubicExclusionRadius (G E : ℝ) : ℝ :=
  ((10 / 13 : ℝ) * G + 63 / 2) +
    Real.sqrt ((((10 / 13 : ℝ) * G + 63 / 2) ^ 2) + (8 / 5 : ℝ) * G + 28 + (4 / 3 : ℝ) * E)

/-- Nonnegative conductor and exclusion envelopes give a radius at least 63 / 2
and its exact quadratic identity. Nonnegativity of the radicand justifies
squaring the square root. These facts provide numerical separation. -/
theorem tightCubicExclusionRadius_data {G E : ℝ} (hG : 0 ≤ G) (hE : 0 ≤ E) :
    63 / 2 ≤ tightCubicExclusionRadius G E ∧
      (tightCubicExclusionRadius G E) ^ 2 =
        2 * ((10 / 13 : ℝ) * G + 63 / 2) * tightCubicExclusionRadius G E + (8 / 5 : ℝ) * G + 28 +
          (4 / 3 : ℝ) * E := by
  have hr : 0 ≤ (((10 / 13 : ℝ) * G + 63 / 2) ^ 2) + (8 / 5 : ℝ) * G + 28 + (4 / 3 : ℝ) * E := by
    nlinarith only [sq_nonneg ((10 / 13 : ℝ) * G + 63 / 2), hG, hE]
  have hs := Real.sq_sqrt hr
  unfold tightCubicExclusionRadius
  constructor
  · linarith only [hG,
      Real.sqrt_nonneg
        ((((10 / 13 : ℝ) * G + 63 / 2) ^ 2) + (8 / 5 : ℝ) * G + 28 + (4 / 3 : ℝ) * E)]
  · nlinarith only [hs]

/-- Under primitive nonprincipal GRH, envelopes for the conductor logarithm and
character-sensitive exclusion cost give an outside prime below the squared
cubic radius. Combine the exact defect with the two analytic bounds and the
radius identity. This permits arbitrary later upper bounds for E_chi(m). -/
theorem exists_prime_outside_le_tight_cubic_exclusion_radius {f m : ℕ} [NeZero f]
    (χ : DirichletCharacter ℂ f) (hf : 2 ≤ f) (hm : m ≠ 0)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) {G E : ℝ} (hlog : Real.log f ≤ G)
    (hcost : AnalyticNumberTheory.Arithmetic.characterExclusionCost χ m ≤ E) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (tightCubicExclusionRadius G E) ^ 2 ∧ ¬p ∣ m ∧ χ p ≠ 1 := by
  have hf0 : 0 ≤ Real.log (f : ℝ) :=
    Real.log_nonneg (Nat.one_le_cast.mpr (hf.trans' (by decide : 1 ≤ 2)))
  have hd :=
    tightCubicExclusionRadius_data (hf0.trans hlog)
      ((AnalyticNumberTheory.Arithmetic.characterExclusionCost_nonneg χ m).trans hcost)
  have hr : 0 ≤ tightCubicExclusionRadius G E := (by norm_num only : (0 : ℝ) ≤ 63 / 2).trans hd.1
  have hx : 1 < (tightCubicExclusionRadius G E) ^ 2 := by nlinarith only [hd.1]
  have hs := Real.sqrt_sq hr
  have hmul := mul_le_mul_of_nonneg_right hlog hr
  by_contra hn
  have ht :
    ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (tightCubicExclusionRadius G E) ^ 2 → ¬p ∣ m → χ p = 1 := by
    intro p hp hpx hpm
    by_contra hv
    exact hn ⟨p, hp, hpx, hpm, hv⟩
  have hdef := sqrt_mul_cubic_defect_le_sensitive χ hm hx.le ht
  have hu :=
    sqrt_mul_reciprocalGapCharacterSum_three_re_le_tight hf hGRH hp hne
      (fun h ↦ hne (inv_eq_one.mp h)) hx.le
  have hl :=
    mul_le_mul_of_nonneg_left (reciprocalGap_principal_three_ge hGRH.riemann hx)
      (Real.sqrt_nonneg ((tightCubicExclusionRadius G E) ^ 2))
  rw [hs] at hdef hu hl
  nlinarith only [hd.1, hd.2, hlog, hmul, hcost, hdef, hu, hl]

/-- Radius B+sqrt(B²+(8/3)E), with B=(10/13)G+65/2.
It absorbs the ramified cost G while retaining the square-factor cost E.
Its quadratic identity is used for Jacobi and Selfridge transfers. -/
noncomputable def tightCubicSquareFactorRadius (G E : ℝ) : ℝ :=
  ((10 / 13 : ℝ) * G + 65 / 2) + Real.sqrt ((((10 / 13 : ℝ) * G + 65 / 2) ^ 2) + (8 / 3 : ℝ) * E)

/-- For nonnegative G,E, increasing the radius constant from 63/2 to 65/2 absorbs
the conductor-linear part of the exclusion cost G+2E. Compare the nonnegative
square roots by their squares. This yields the explicit square-factor radius. -/
theorem tightCubicExclusionRadius_le_square_factor {G E : ℝ} (hG : 0 ≤ G) (hE : 0 ≤ E) :
    tightCubicExclusionRadius G (G + 2 * E) ≤ tightCubicSquareFactorRadius G E := by
  have ht :
    ((10 / 13 : ℝ) * G + 65 / 2) ≤
      Real.sqrt ((((10 / 13 : ℝ) * G + 65 / 2) ^ 2) + (8 / 3 : ℝ) * E) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [hE])
  have hrad :
    0 ≤ (((10 / 13 : ℝ) * G + 63 / 2) ^ 2) + (8 / 5 : ℝ) * G + 28 + (4 / 3 : ℝ) * (G + 2 * E) := by
    nlinarith only [sq_nonneg ((10 / 13 : ℝ) * G + 63 / 2), hG, hE]
  have hrad' : 0 ≤ (((10 / 13 : ℝ) * G + 65 / 2) ^ 2) + (8 / 3 : ℝ) * E := by
    nlinarith only [sq_nonneg ((10 / 13 : ℝ) * G + 65 / 2), hE]
  have hs := Real.sq_sqrt hrad
  have hs' := Real.sq_sqrt hrad'
  have hn :=
    Real.sqrt_nonneg
      ((((10 / 13 : ℝ) * G + 63 / 2) ^ 2) + (8 / 5 : ℝ) * G + 28 + (4 / 3 : ℝ) * (G + 2 * E))
  dsimp only [tightCubicExclusionRadius, tightCubicSquareFactorRadius]
  nlinarith only [hs, hs', hn, ht, hG]

/-- Nonnegative budgets give a radius at least 65 solving r²=2Br+(8/3)E.
Use the square-root identity and sqrt(B²+(8/3)E) at least B. The identity
supports comparisons with arbitrary positive target radii. -/
theorem tightCubicSquareFactorRadius_data {G E : ℝ} (hG : 0 ≤ G) (hE : 0 ≤ E) :
    65 ≤ tightCubicSquareFactorRadius G E ∧
      (tightCubicSquareFactorRadius G E) ^ 2 =
        2 * ((10 / 13 : ℝ) * G + 65 / 2) * tightCubicSquareFactorRadius G E + (8 / 3 : ℝ) * E := by
  have hr : 0 ≤ (((10 / 13 : ℝ) * G + 65 / 2) ^ 2) + (8 / 3 : ℝ) * E := by
    nlinarith only [sq_nonneg ((10 / 13 : ℝ) * G + 65 / 2), hE]
  have hs := Real.sq_sqrt hr
  have ht :
    ((10 / 13 : ℝ) * G + 65 / 2) ≤
      Real.sqrt ((((10 / 13 : ℝ) * G + 65 / 2) ^ 2) + (8 / 3 : ℝ) * E) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [hE])
  unfold tightCubicSquareFactorRadius
  constructor <;> nlinarith only [hs, ht, hG]

/-- A positive target radius T dominates the square-factor radius whenever
T² is at least 2BT+(8/3)E, for nonnegative G,E. Compare the quadratic identities
on the increasing branch. This is a generic interface for subquadratic targets. -/
theorem tightCubicSquareFactorRadius_le_of_quadratic {G E T : ℝ} (hG : 0 ≤ G) (hE : 0 ≤ E)
    (hT : 0 < T) (hquad : 2 * ((10 / 13 : ℝ) * G + 65 / 2) * T + (8 / 3 : ℝ) * E ≤ T ^ 2) :
    tightCubicSquareFactorRadius G E ≤ T := by
  have hd := tightCubicSquareFactorRadius_data hG hE
  have htB : 2 * ((10 / 13 : ℝ) * G + 65 / 2) ≤ T := by
    by_contra h
    have hm := mul_pos hT (sub_pos.mpr (lt_of_not_ge h))
    nlinarith only [hquad, hE, hm]
  by_contra hn
  have hlt := lt_of_not_ge hn
  have hm :=
    mul_pos (sub_pos.mpr hlt)
      (show 0 < tightCubicSquareFactorRadius G E + T - 2 * ((10 / 13 : ℝ) * G + 65 / 2) by
        linarith only [hd.1, htB])
  nlinarith only [hd.2, hquad, hm]

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS

/-- Under GRH, a nonprincipal character has a prime non-one value outside its
level below the tight cubic radius squared. Transfer primitive character
values on units; the inputs are conductor and sensitive-cost envelopes. -/
theorem exists_prime_ne_one_le_tight_cubic_sensitive_radius {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {G E : ℝ}
    (hlog : Real.log χ.conductor ≤ G)
    (hcost : AnalyticNumberTheory.Arithmetic.characterExclusionCost χ.primitiveCharacter q ≤ E) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (PaperStatements.tightCubicExclusionRadius G E) ^ 2 ∧ ¬p ∣ q ∧ χ p ≠ 1 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hc := NumberTheory.three_le_conductor_of_ne_one χ hχ
  have hn := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    PaperStatements.exists_prime_outside_le_tight_cubic_exclusion_radius χ.primitiveCharacter
      (le_trans (by decide : 2 ≤ 3) hc) (NeZero.ne q) hGRH χ.primitiveCharacter_isPrimitive hn hlog
      hcost
  have he := χ.primitiveCharacter_apply_of_isCoprime (hp.coprime_iff_not_dvd.mpr hd).isCoprime
  simp only [Int.cast_natCast] at he
  exact ⟨p, hp, hb, hd, fun h ↦ hv (he.trans h)⟩

end PseudoPrime.LLS
