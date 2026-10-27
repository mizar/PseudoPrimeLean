/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.FullEndpointPolynomial
public import PseudoPrime.LLS.OddEndpointElementaryCosts
public import PseudoPrime.LLS.GammaSignedPrefixCharacterBounds
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # Continuous endpoint bounds through sixty-one and eighty-one percent -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For radius 81/10<=y<=117/5, the endpoint polynomial with L=(10/9)y
and logarithm lower line 699y/10000+3/2 is positive. Bound the shifted quadratic by
(153/10) times its argument and retain nonnegative cubic and quartic terms.
This certifies the full radius interval with one rational polynomial argument. -/
theorem fullEndpoint_eightyOne_base_pos {y : ℝ} (hya : (81 / 10 : ℝ) ≤ y)
    (hyb : y ≤ (117 / 5 : ℝ)) :
    0 <
      fullEndpointPolynomial ((10 / 9 : ℝ) * y) (2096 / 1831) y
        ((699 / 10000 : ℝ) * y + 3 / 2) := by
  have ht : 0 ≤ y - 81 / 10 := by linarith only [hya]
  have hu : y - 81 / 10 ≤ (153 / 10 : ℝ) := by linarith only [hyb]
  have hsq : (y - 81 / 10) ^ 2 ≤ (153 / 10 : ℝ) * (y - 81 / 10) := by nlinarith only [ht, hu]
  dsimp only [fullEndpointPolynomial]
  nlinarith only [ht, hu, hsq, pow_nonneg ht 3, pow_nonneg ht 4]

/-- For 8<=y<=24, log y is at least 699y/10000+3/2. Use concavity of log
and the certified logarithms of two and three at endpoints eight and twenty-four.
This provides a uniform logarithm lower bound without numerical subdivision. -/
theorem fullEndpoint_log_chord {y : ℝ} (hy8 : 8 ≤ y) (hy24 : y ≤ 24) :
    (699 / 10000 : ℝ) * y + 3 / 2 ≤ Real.log y := by
  have h24 : (3972 / 1250 : ℝ) ≤ Real.log 24 := by
    rw [show (24 : ℝ) = 2 ^ 3 * 3 by norm_num only,
      Real.log_mul (by norm_num only : (2 : ℝ) ^ 3 ≠ 0) (by norm_num only : (3 : ℝ) ≠ 0),
      Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_gt_d9, Real.log_three_gt_d9]
  have h8 : (1287 / 625 : ℝ) ≤ Real.log 8 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_gt_d9]
  have ha : 0 ≤ (24 - y) / 16 := div_nonneg (sub_nonneg.mpr hy24) (by norm_num only)
  have hb : 0 ≤ (y - 8) / 16 := div_nonneg (sub_nonneg.mpr hy8) (by norm_num only)
  have hs : (24 - y) / 16 + (y - 8) / 16 = 1 := by ring
  have hc :=
    strictConcaveOn_log_Ioi.concaveOn.2 (show (8 : ℝ) ∈ Set.Ioi 0 by norm_num only [Set.mem_Ioi])
      (show (24 : ℝ) ∈ Set.Ioi 0 by norm_num only [Set.mem_Ioi]) ha hb hs
  simp only [smul_eq_mul] at hc
  have he : (24 - y) / 16 * 8 + (y - 8) / 16 * 24 = y := by ring
  rw [he] at hc
  have hA := mul_le_mul_of_nonneg_left h8 ha
  have hB := mul_le_mul_of_nonneg_left h24 hb
  linarith only [hc, hA, hB]

/-- For y>=1,z>=0 and L<=K, the endpoint polynomial at K is at most its value
at L. Factor the level difference into nonnegative factors. This transfers a single
upper ambient-level certificate to every smaller conductor logarithm. -/
theorem fullEndpointPolynomial_antitone_level {L K P y z : ℝ} (hy : 1 ≤ y) (hz : 0 ≤ z)
    (hLK : L ≤ K) : fullEndpointPolynomial K P y z ≤ fullEndpointPolynomial L P y z := by
  have hc : 0 ≤ (y - 1) ^ 2 * z + (2 * y + 2 * z + 2) * ((1 / 2 : ℝ) * (y ^ 2 - 1)) := by
    have hs : 0 ≤ y ^ 2 - 1 := by nlinarith only [hy]
    exact
      add_nonneg (mul_nonneg (sq_nonneg _) hz)
        (mul_nonneg (by linarith only [hy, hz]) (mul_nonneg (by norm_num only) hs))
  have hm := mul_nonneg hc (sub_nonneg.mpr hLK)
  dsimp only [fullEndpointPolynomial]
  nlinarith only [hm]

/-- For 81/10<=y<=117/5 and z above the logarithm lower line, the endpoint
polynomial at L=(10/9)y is positive. Retain the nonnegative linear and quadratic
logarithm slack after the base polynomial. This removes an upper-logarithm condition. -/
theorem fullEndpoint_eightyOne_polynomial_pos {y z : ℝ} (hya : (81 / 10 : ℝ) ≤ y)
    (hyb : y ≤ (117 / 5 : ℝ)) (hz : (699 / 10000 : ℝ) * y + 3 / 2 ≤ z) :
    0 < fullEndpointPolynomial ((10 / 9 : ℝ) * y) (2096 / 1831) y z := by
  have hp := fullEndpoint_eightyOne_base_pos hya hyb
  have hy0 : 0 ≤ y := by linarith only [hya]
  have hu : 0 ≤ z - ((699 / 10000 : ℝ) * y + 3 / 2) := sub_nonneg.mpr hz
  have hc :
    0 ≤
      ((4 - 20 / 9 + 8 * (699 / 10000)) : ℝ) * y ^ 3 + (2395033451 / 164790000 : ℝ) * y ^ 2 +
          (1089 / 250 : ℝ) * y -
        3041959 / 915500 := by
    nlinarith only [hya, pow_nonneg hy0 3, sq_nonneg y]
  have hm := mul_nonneg hu hc
  have hs := mul_nonneg (sq_nonneg y) (sq_nonneg (z - ((699 / 10000 : ℝ) * y + 3 / 2)))
  dsimp only [fullEndpointPolynomial] at hp ⊢
  nlinarith only [hp, hm, hs]

/-- For every real 9<=L<=26, the endpoint polynomial at y=(9/10)L,z=log y
is positive. Supply the radius interval and logarithmic chord. This certifies a continuous
coefficient-81/100 witness interval without enumerating input moduli. -/
theorem fullEndpoint_polynomial_pos_eightyOne_log_interval {L : ℝ} (hL9 : 9 ≤ L) (hL26 : L ≤ 26) :
    0 <
      fullEndpointPolynomial L (2096 / 1831) ((9 / 10 : ℝ) * L) (Real.log ((9 / 10 : ℝ) * L)) := by
  let y := (9 / 10 : ℝ) * L
  have hya : (81 / 10 : ℝ) ≤ y := by
    dsimp only [y]; linarith only [hL9]
  have hyb : y ≤ (117 / 5 : ℝ) := by
    dsimp only [y]; linarith only [hL26]
  have hl :=
    fullEndpoint_log_chord (by linarith only [hya] : (8 : ℝ) ≤ y)
      (by linarith only [hyb] : y ≤ (24 : ℝ))
  have hp := fullEndpoint_eightyOne_polynomial_pos hya hyb hl
  have he : (10 / 9 : ℝ) * y = L := by
    dsimp only [y]; ring
  rw [he] at hp
  exact hp

/-- For every real L<=9, the endpoint polynomial at radius eight is positive.
Certify the upper level nine and use level antitonicity. This supplies a fixed prime
cutoff sixty-four for all smaller positive conductor levels. -/
theorem fullEndpoint_polynomial_pos_at_eight {L : ℝ} (hL9 : L ≤ 9) :
    0 < fullEndpointPolynomial L (2096 / 1831) 8 (Real.log 8) := by
  have hz : (207 / 100 : ℝ) ≤ Real.log 8 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_gt_d9]
  have hp : 0 < fullEndpointPolynomial 9 (2096 / 1831) 8 (Real.log 8) := by
    dsimp only [fullEndpointPolynomial]
    nlinarith only [hz, sq_nonneg (Real.log 8 - 207 / 100)]
  have hm :=
    fullEndpointPolynomial_antitone_level (P := (2096 / 1831 : ℝ)) (by norm_num only : (1 : ℝ) ≤ 8)
      (by linarith only [hz] : 0 ≤ Real.log 8) hL9
  exact hp.trans_le hm

/-- For a nonprincipal character under GRH, radius at least eight and positive
endpoint polynomial at its original level, a non-one prime lies through the squared radius.
Use conductor monotonicity and the primitive witness, then transfer value one back by contradiction.
Nonunit primes remain valid; no primitivity premise is required from callers. -/
theorem exists_prime_ne_one_of_fullEndpointPolynomial_original {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hpoly : 0 < fullEndpointPolynomial (Real.log q) (2096 / 1831) y (Real.log y)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ y ^ 2 ∧ χ p ≠ 1 := by
  let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψ : χ.primitiveCharacter ≠ 1 :=
    AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hq : 2 ≤ χ.conductor :=
    (Nat.two_le_iff _).mpr
      ⟨χ.conductor_ne_zero, fun he ↦ hne (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr he)⟩
  have hx : 1 < y ^ 2 := by nlinarith only [hy]
  have hY : 64 ≤ y ^ 2 := by nlinarith only [hy]
  have hlim :=
    fullEndpointLimit_neg_of_rational_polynomial_pos q (by linarith only [hy] : 1 < y) hpoly
  have hm :=
    fullEndpointLimit_mono_level (Nat.pos_of_ne_zero χ.conductor_ne_zero)
      (Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level) hx.le hY
  obtain ⟨p, hp, hb, hv⟩ :=
    exists_prime_not_one_of_fullEndpointLimit_neg hq hGRH χ.primitiveCharacter_isPrimitive hψ
      (inv_ne_one.mpr hψ) hx hY le_rfl (hm.trans_lt hlim)
  refine ⟨p, hp, hb, ?_⟩
  intro hone
  exact hv (primitiveCharacter_apply_one_of_apply_one χ hone)

/-- For a nonprincipal character under GRH with 9<=log q<=26, a non-one prime
lies through (81/100)(log q)^2. Apply the continuous endpoint polynomial certificate.
This is the original-level character consumer for the improved finite-scale radius. -/
theorem exists_prime_ne_one_le_eightyOne_log_sq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL9 : 9 ≤ Real.log q) (hL26 : Real.log q ≤ 26) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (81 / 100 : ℝ) * (Real.log q) ^ 2 ∧ χ p ≠ 1 := by
  obtain ⟨p, hp, hb, hv⟩ :=
    exists_prime_ne_one_of_fullEndpointPolynomial_original χ hne hGRH
      (by linarith only [hL9] : (8 : ℝ) ≤ (9 / 10 : ℝ) * Real.log q)
      (fullEndpoint_polynomial_pos_eightyOne_log_interval hL9 hL26)
  refine ⟨p, hp, ?_, hv⟩
  nlinarith only [hb]

/-- For a nonprincipal character under GRH with log q<=9, a non-one prime at most
sixty-one exists. Apply the fixed radius eight certificate, then kernel-check the primes
through sixty-four. No modulus enumeration or finite input certificate is used. -/
theorem exists_prime_ne_one_le_sixty_one_of_log_le_nine {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL9 : Real.log q ≤ 9) :
    ∃ p : ℕ, p.Prime ∧ p ≤ 61 ∧ χ p ≠ 1 := by
  obtain ⟨p, hp, hb, hv⟩ :=
    exists_prime_ne_one_of_fullEndpointPolynomial_original χ hne hGRH
      (by norm_num only : (8 : ℝ) ≤ 8) (fullEndpoint_polynomial_pos_at_eight hL9)
  have hp64 : p ≤ 64 := by exact_mod_cast hb
  have hsmall : ∀ p ∈ Finset.range 65, p.Prime → p ≤ 61 := by decide +kernel
  exact ⟨p, hp, hsmall p (Finset.mem_range.mpr (Nat.lt_succ_of_le hp64)) hp, hv⟩

end PseudoPrime.LLS.PaperStatements
