/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.CubicGapConductorWitness
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterSensitiveExclusion

/-! # Cubic conductor bounds retaining character-sensitive exclusions -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open AnalyticNumberTheory.Arithmetic in
/-- Prime triviality outside nonzero m bounds the unnormalized cubic defect by
E_chi(m)/3+12sqrt x for x at least one. Verify the cubic weights and identify
the finite defect exactly before using the character-sensitive weighted estimate. -/
theorem sqrt_mul_cubic_defect_le_sensitive {f m : ℕ} (χ : DirichletCharacter ℂ f) (hm : m ≠ 0)
    {x : ℝ} (hx : 1 ≤ x) (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → ¬p ∣ m → χ p = 1) :
    Real.sqrt x *
        ((reciprocalGapCharacterSum 3 (1 : DirichletCharacter ℂ 1) x).re -
          (reciprocalGapCharacterSum 3 χ x).re) ≤
      characterExclusionCost χ m / 3 + 12 * Real.sqrt x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx0).ne'
  let w := fun n : ℕ ↦ (1 - ((n : ℝ) / x) ^ 3) / 3
  have hw : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, 0 ≤ w n ∧ w n ≤ 1 / 3 := by
    intro n hn
    have hn0 : 0 ≤ (n : ℝ) / x := div_nonneg (Nat.cast_nonneg n) hx0.le
    have hnle : (n : ℝ) ≤ x :=
      (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le hx0.le)
    have hr : (n : ℝ) / x ≤ 1 := (div_le_one hx0).mpr hnle
    have hp : ((n : ℝ) / x) ^ 3 ≤ 1 := pow_le_one₀ hn0 hr
    dsimp only [w]
    constructor <;> nlinarith only [hp, pow_nonneg hn0 3]
  have hb := weighted_character_defect_le_sensitive χ hm hx w hw hsmall
  have he :
    Real.sqrt x *
        ((reciprocalGapCharacterSum 3 (1 : DirichletCharacter ℂ 1) x).re -
          (reciprocalGapCharacterSum 3 χ x).re) =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (1 - (χ n).re) * ArithmeticFunction.vonMangoldt n * w n := by
    rw [reciprocalGap_principal_re_eq_sum, reciprocalGapCharacterSum_re_eq_weighted, ←
      Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    simp only [reciprocalGapPrincipalWeight, Real.rpow_ofNat]
    dsimp only [w]
    field_simp [hs]
  rw [he]
  exact hb

/-- Cubic radius for a conductor logarithm envelope G and a character-sensitive
exclusion envelope E. It is A+sqrt(A²+(8/5)G+33+(4/3)E), A=(10/13)G+34.
Keeping E as a real parameter permits later arithmetic support estimates. -/
noncomputable def cubicExclusionRadius (G E : ℝ) : ℝ :=
  ((10 / 13 : ℝ) * G + 34) +
    Real.sqrt ((((10 / 13 : ℝ) * G + 34) ^ 2) + (8 / 5 : ℝ) * G + 33 + (4 / 3 : ℝ) * E)

/-- Nonnegative conductor and exclusion envelopes give a radius at least 34
and its exact quadratic identity. Nonnegativity of the radicand justifies
squaring the square root. These facts provide numerical separation. -/
theorem cubicExclusionRadius_data {G E : ℝ} (hG : 0 ≤ G) (hE : 0 ≤ E) :
    34 ≤ cubicExclusionRadius G E ∧
      (cubicExclusionRadius G E) ^ 2 =
        2 * ((10 / 13 : ℝ) * G + 34) * cubicExclusionRadius G E + (8 / 5 : ℝ) * G + 33 +
          (4 / 3 : ℝ) * E := by
  have hr : 0 ≤ (((10 / 13 : ℝ) * G + 34) ^ 2) + (8 / 5 : ℝ) * G + 33 + (4 / 3 : ℝ) * E := by
    nlinarith only [sq_nonneg ((10 / 13 : ℝ) * G + 34), hG, hE]
  have hs := Real.sq_sqrt hr
  unfold cubicExclusionRadius
  constructor
  · linarith only [hG,
      Real.sqrt_nonneg ((((10 / 13 : ℝ) * G + 34) ^ 2) + (8 / 5 : ℝ) * G + 33 + (4 / 3 : ℝ) * E)]
  · nlinarith only [hs]

open AnalyticNumberTheory.Arithmetic in
/-- Under primitive nonprincipal GRH, envelopes for the conductor logarithm and
character-sensitive exclusion cost give an outside prime below the squared
cubic radius. Combine the exact defect with the two analytic bounds and the
radius identity. This permits arbitrary later upper bounds for E_chi(m). -/
theorem exists_prime_outside_le_cubic_exclusion_radius {f m : ℕ} [NeZero f]
    (χ : DirichletCharacter ℂ f) (hf : 2 ≤ f) (hm : m ≠ 0)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) {G E : ℝ} (hlog : Real.log f ≤ G) (hcost : characterExclusionCost χ m ≤ E) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (cubicExclusionRadius G E) ^ 2 ∧ ¬p ∣ m ∧ χ p ≠ 1 := by
  have hf0 : 0 ≤ Real.log (f : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hf.trans' (by decide : 1 ≤ 2))
  have hd :=
    cubicExclusionRadius_data (hf0.trans hlog) ((characterExclusionCost_nonneg χ m).trans hcost)
  have hr : 0 ≤ cubicExclusionRadius G E := (by norm_num only : (0 : ℝ) ≤ 34).trans hd.1
  have hx : 1 < (cubicExclusionRadius G E) ^ 2 := by nlinarith only [hd.1]
  have hs := Real.sqrt_sq hr
  have hmul := mul_le_mul_of_nonneg_right hlog hr
  by_contra hn
  have ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (cubicExclusionRadius G E) ^ 2 → ¬p ∣ m → χ p = 1 := by
    intro p hp hpx hpm
    by_contra hv
    exact hn ⟨p, hp, hpx, hpm, hv⟩
  have hdef := sqrt_mul_cubic_defect_le_sensitive χ hm hx.le ht
  have hu :=
    sqrt_mul_reciprocalGapCharacterSum_three_re_le hf hGRH hp hne (fun h ↦ hne (inv_eq_one.mp h))
      hx.le
  have hl :=
    mul_le_mul_of_nonneg_left (reciprocalGap_principal_three_ge hGRH.riemann hx)
      (Real.sqrt_nonneg ((cubicExclusionRadius G E) ^ 2))
  rw [hs] at hdef hu hl
  nlinarith only [hd.1, hd.2, hlog, hmul, hcost, hdef, hu, hl]

open AnalyticNumberTheory.Arithmetic in
/-- For nonnegative G, the exact character-sensitive squared radius is no
larger than the uniform cubic conductor radius. Bound E_chi by twice the prime
logarithm sum and use nonnegative-radius monotonicity before squaring. -/
theorem cubicExclusionRadius_sq_le_uniform {f : ℕ} (χ : DirichletCharacter ℂ f) (m : ℕ) {G : ℝ}
    (hG : 0 ≤ G) :
    (cubicExclusionRadius G (characterExclusionCost χ m)) ^ 2 ≤ (cubicConductorRadius G m) ^ 2 := by
  have hc := characterExclusionCost_le_twice χ m
  have hr : cubicExclusionRadius G (characterExclusionCost χ m) ≤ cubicConductorRadius G m := by
    dsimp only [cubicExclusionRadius, cubicConductorRadius]
    apply add_le_add le_rfl
    apply Real.sqrt_le_sqrt
    linarith only [hc]
  have hn := (cubicExclusionRadius_data hG (characterExclusionCost_nonneg χ m)).1
  nlinarith only [hr, hn]

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS

open AnalyticNumberTheory.Arithmetic in
/-- A general nonprincipal character under GRH has a unit-prime non-one witness
within the cubic radius for any envelope of its primitive exclusion cost.
Transfer primitive values on units of the original level. This exposes the
refined bound without requiring the caller to construct a primitive character. -/
theorem exists_prime_ne_one_le_cubic_sensitive_radius {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {G E : ℝ}
    (hlog : Real.log χ.conductor ≤ G) (hcost : characterExclusionCost χ.primitiveCharacter q ≤ E) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ (PaperStatements.cubicExclusionRadius G E) ^ 2 ∧ ¬p ∣ q ∧ χ p ≠ 1 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hc := NumberTheory.three_le_conductor_of_ne_one χ hχ
  have hn := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    PaperStatements.exists_prime_outside_le_cubic_exclusion_radius χ.primitiveCharacter
      (le_trans (by decide : 2 ≤ 3) hc) (NeZero.ne q) hGRH χ.primitiveCharacter_isPrimitive hn hlog
      hcost
  have he := χ.primitiveCharacter_apply_of_isCoprime (hp.coprime_iff_not_dvd.mpr hd).isCoprime
  simp only [Int.cast_natCast] at he
  exact ⟨p, hp, hb, hd, fun h ↦ hv (he.trans h)⟩

end PseudoPrime.LLS
