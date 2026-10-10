/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.CosetCharacterAverage
public import PseudoPrime.LLS.CosetLogWeightedBounds
public import PseudoPrime.NumberTheory.DirichletCharacterSmallLevels
public import PseudoPrime.NumberTheory.DirichletCharacterParity
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrincipalCharacterSums
public import PseudoPrime.LLS.RiemannWeightedBounds
public import PseudoPrime.LLS.RiemannWeightedUpperBounds

/-! # Average of nonprincipal character norm bounds

Subgroup orthogonality bounds the sum of reciprocal corrections below by the
negative principal contribution. The remaining errors are multiplied by the
number of nonprincipal characters, which is the subgroup index minus one.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open Classical in
/-- For modulus greater than two and cutoff at least 100, average primitive
reciprocal corrections over all nonprincipal full-level characters using exact parity counts.
Primitive normalization preserves parity; even and odd upper bounds have coefficients
`totient/2 - 1` and `totient/2`. Expanding the average retains the logarithm-of-two
and gamma savings needed for smaller-modulus residue comparisons. -/
theorem sum_nonprincipal_reciprocalCorrection_le_parity_average {q : ℕ} [NeZero q] (hq : 2 < q)
    {x : ℝ} (hx : 100 ≤ x) :
    2 *
        (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          reciprocalCorrection χ.primitiveCharacter x) ≤
      -((q.totient : ℝ) - 2) * Real.log 2 - ((q.totient : ℝ) - 1) * Real.eulerMascheroniConstant +
        (((q.totient : ℝ) - 2) * (Real.log x + 1 + Real.eulerMascheroniConstant / 2) +
            (q.totient : ℝ) * (Real.log 2 + Real.eulerMascheroniConstant / 2)) /
          x := by
  have hs :=
    NumberTheory.sum_nonprincipal_dirichletCharacters_le_parity_average hq
      (fun χ ↦ reciprocalCorrection χ.primitiveCharacter x)
      (fun χ _ he ↦
        reciprocalCorrection_le_even χ.primitiveCharacter
          ((NumberTheory.primitiveCharacter_even_iff χ).mpr he) hx)
      (fun χ _ ho ↦
        reciprocalCorrection_le_odd χ.primitiveCharacter
          ((NumberTheory.primitiveCharacter_odd_iff χ).mpr ho) hx)
  convert mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 2) using 1
  ring

/-- The common error in the coset logarithmic norm estimate at modulus `q`
and cutoff `x`: the squared logarithm, ambient endpoint term, and parity
majorant. This real quantity is used once per nonprincipal character in the
annihilator average; the principal zero-mass contribution is kept separate. -/
noncomputable def cosetCharacterNormError (q : ℕ) (x : ℝ) : ℝ :=
  (Real.log x) ^ 2 + ((2 / 3 : ℝ) * Real.log ((q : ℝ) / Real.pi) + 4) * Real.log x +
    Real.log x / 2 * Real.log (max ((q : ℝ) / Real.pi) (2 * x))

open Classical in
/-- Under GRH, for modulus at least `64` and cutoff at least `65536`,
the sum of logarithmic norms over the nonprincipal annihilator characters
is at most their common majorant times `index-1`, plus the principal reciprocal
contribution. Sum the individual norm estimates, use the conductor lower bound,
and cancel reciprocal terms by subgroup orthogonality.
This is the averaged norm estimate used in the coset prime comparison. -/
theorem nonprincipal_logWeightedNorm_sum_le {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hq : 64 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 65536 ≤ x) :
    (∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H),
        ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ.val‖) ≤
      ((H.index : ℝ) - 1) *
          ((Real.sqrt x + 19 / 6) * (Real.log q - 51 / 50) + cosetCharacterNormError q x) +
        2 * (Real.sqrt x + 19 / 6) *
          (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x
              (1 : DirichletCharacter ℂ q)).re := by
  classical
  let S := Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H)
  let A := Real.sqrt x + 19 / 6
  let C := Real.log q - 51 / 50
  let E := cosetCharacterNormError q x
  let R := fun χ : NumberTheory.subgroupAnnihilator H =>
    (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ.val).re
  have hR :=
    subgroup_reciprocal_average_nonneg H (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 65536) hx)
  have herase := Finset.sum_erase_add Finset.univ R (Finset.mem_univ 1)
  have hr : -(R 1) ≤ ∑ χ ∈ S, R χ := by
    change 0 ≤ ∑ χ, R χ at hR
    change (∑ χ ∈ S, R χ) + R 1 = ∑ χ, R χ at herase
    linarith only [hR, herase]
  have hbound :
    (∑ χ ∈ S, ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ.val‖) ≤
      ∑ χ ∈ S, (A * (C - 2 * R χ) + E) := by
    apply Finset.sum_le_sum
    intro χ hχ
    have hne : χ.val ≠ 1 := by
      intro h
      exact (Finset.mem_erase.mp hχ).1 (Subtype.ext h)
    let : NeZero χ.val.conductor := ⟨χ.val.conductor_ne_zero⟩
    have h :=
      norm_characterLogWeightedSum_le_coset χ.val hq
        (NumberTheory.three_le_conductor_of_ne_one χ.val hne) hGRH hx
    change _ ≤ A * (C - 2 * R χ) + E
    unfold A C E cosetCharacterNormError R
    linarith only [h]
  have hid :
    (∑ χ ∈ S, (A * (C - 2 * R χ) + E)) = (S.card : ℝ) * (A * C + E) - 2 * A * ∑ χ ∈ S, R χ := by
    simp only [mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have hcard : (S.card : ℝ) = (H.index : ℝ) - 1 := by
    have hpos : 1 ≤ Fintype.card (NumberTheory.subgroupAnnihilator H) :=
      Nat.succ_le_iff.mpr (Fintype.card_pos_iff.mpr ⟨1⟩)
    dsimp only [S]
    rw [Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ, Nat.cast_sub hpos,
      NumberTheory.card_subgroupAnnihilator, Nat.cast_one]
  have hscale :=
    mul_le_mul_of_nonneg_left hr
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2)
        (add_nonneg (Real.sqrt_nonneg x) (by norm_num only : (0 : ℝ) ≤ 19 / 6)))
  rw [hid, hcard] at hbound
  change _ ≤ ((H.index : ℝ) - 1) * (A * C + E) + 2 * A * R 1
  change 2 * A * -(R 1) ≤ 2 * A * ∑ χ ∈ S, R χ at hscale
  nlinarith only [hbound, hscale]

/-- The principal logarithmic lower bound under RH at cutoff `x>1`.
The unsigned sum loses its zero and constant corrections and at most
`log² x/2` per prime divisor of `q`. This is the lower side of the coset gap. -/
noncomputable def cosetPrincipalLower (q : ℕ) (x : ℝ) : ℝ :=
  x - Real.log (2 * Real.pi) * Real.log x - 1 - (Real.sqrt x + 1) / 20 -
    (1 / 2 : ℝ) * q.primeFactors.card * (Real.log x) ^ 2

/-- The nonprincipal logarithmic norm majorant for a subgroup `H` at cutoff `x`.
The common norm error occurs `index-1` times; the principal reciprocal term is
bounded by its RH explicit formula with zero mass at most `1/40`.
This is the norm contribution in the explicit coset gap. -/
noncomputable def cosetNonprincipalUpper (q : ℕ) (H : Subgroup (ZMod q)ˣ) (x : ℝ) : ℝ :=
  ((H.index : ℝ) - 1) *
      ((Real.sqrt x + 19 / 6) * (Real.log q - 51 / 50) + cosetCharacterNormError q x) +
    2 * (Real.sqrt x + 19 / 6) *
      (Real.log x - (1 + Real.eulerMascheroniConstant) + Real.log (2 * Real.pi) / x +
        1 / (20 * Real.sqrt x))

/-- Under RH and `x>1`, the principal logarithmic sum is at least its explicit
coset lower bound. Split off noncoprime indices, apply the Riemann lower bound,
and use the zero-mass and common-factor estimates.
This supplies the principal side of the coset comparison. -/
theorem cosetPrincipalLower_le {q : ℕ} [NeZero q] (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    cosetPrincipalLower q x ≤
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x
          (1 : DirichletCharacter ℂ q)).re := by
  have hr := llsRiemannWeightedLowerBound_of_riemannHypothesis hRH x hx
  have hm :=
    mul_le_mul_of_nonneg_right AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_one_fortieth
      (add_nonneg (Real.sqrt_nonneg x) zero_le_one)
  have he :=
    AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum_le (NeZero.ne q)
      (zero_lt_one.trans hx)
  rw [AnalyticNumberTheory.Arithmetic.characterLogWeightedSum_one_re_eq]
  unfold cosetPrincipalLower
  nlinarith only [hr, hm, he]

open Classical in
/-- Under GRH and the modulus and cutoff lower bounds, the nonprincipal norm
sum is at most `cosetNonprincipalUpper`. Bound the remaining principal
reciprocal term by the unsigned sum and its RH explicit estimate.
This removes every character sum from the upper majorant. -/
theorem nonprincipal_logWeightedNorm_sum_le_explicit {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hq : 64 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 65536 ≤ x) :
    (∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H),
        ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ.val‖) ≤
      cosetNonprincipalUpper q H x := by
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num only) hx
  have hx0 := zero_lt_one.trans hx1
  have hs := nonprincipal_logWeightedNorm_sum_le H hq hGRH hx
  have hr :=
    (Complex.re_le_norm _).trans
      (AnalyticNumberTheory.Arithmetic.norm_characterReciprocalWeightedSum_le
        (1 : DirichletCharacter ℂ q) hx0)
  have he := reciprocalWeightedMangoldtSum_le_explicit hGRH.riemann hx1
  have hm :=
    div_le_div_of_nonneg_right AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_one_fortieth
      (Real.sqrt_nonneg x)
  have hbound :
    (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x
          (1 : DirichletCharacter ℂ q)).re ≤
      Real.log x - (1 + Real.eulerMascheroniConstant) + Real.log (2 * Real.pi) / x +
        1 / (20 * Real.sqrt x) := by
    simp only [div_eq_mul_inv, mul_inv_rev] at he hm ⊢
    nlinarith only [hr, he, hm]
  have hscale :=
    mul_le_mul_of_nonneg_left hbound
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2)
        (add_nonneg (Real.sqrt_nonneg x) (by norm_num only : (0 : ℝ) ≤ 19 / 6)))
  unfold cosetNonprincipalUpper
  linarith only [hs, hscale]

/-- Under GRH and the modulus and cutoff lower bounds, a strict gap between
the explicit principal lower bound and the composite-root and nonprincipal
majorants produces the least prime in any prescribed coset below `x`.
Insert the analytic estimates into the character-average prime criterion.
This leaves only real inequalities and a finite root sum to prove. -/
theorem exists_least_prime_in_coset_le_of_explicit_root_gap {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (a : (ZMod q)ˣ) (hq : 64 ≤ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 65536 ≤ x)
    (hgap :
      (H.index : ℝ) *
            (∑ k ∈ Finset.Icc 2 ⌊Real.log x / Real.log 2⌋₊,
              (k : ℝ) * (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20)) +
          cosetNonprincipalUpper q H x <
        cosetPrincipalLower q x) :
    ∃ p : ℕ, IsLeast (primesInCoset q H a) p ∧ (p : ℝ) ≤ x := by
  classical
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num only) hx
  have hn := nonprincipal_logWeightedNorm_sum_le_explicit H hq hGRH hx
  have hp := cosetPrincipalLower_le (q := q) hGRH.riemann hx1
  have hc := compositePrimePowerLogWeightedSum_le_explicit_root_sums hGRH.riemann hx1
  have hm := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg H.index : (0 : ℝ) ≤ H.index)
  apply exists_least_prime_in_coset_le_of_principal_gap H a (zero_lt_one.trans hx1)
  linarith only [hgap, hn, hp, hm]

open Classical in
/-- Under GRH, modulus at least 64, and cutoff at least 65536, bound the sum
of all nonprincipal character logarithmic norms with the exact parity savings.
Average the primitive reciprocal corrections with even count `totient/2 - 1`
and odd count `totient/2`; subgroup orthogonality bounds the reciprocal sum below
by the negative principal contribution. This keeps the `log pi + gamma` saving
for small-modulus residue certificates. -/
theorem nonprincipal_logWeightedNorm_sum_le_parity_average {q : ℕ} [NeZero q] (hq : 64 ≤ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 65536 ≤ x) :
    (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ‖) ≤
      (Real.sqrt x + 19 / 6) *
          (((q.totient : ℝ) - 1) * (Real.log q - Real.log Real.pi - Real.eulerMascheroniConstant) +
            Real.log 2 +
            (((q.totient : ℝ) - 1) / 20 +
                ((q.totient : ℝ) - 2) * (Real.log x + 1 + Real.eulerMascheroniConstant / 2) +
                (q.totient : ℝ) * (Real.log 2 + Real.eulerMascheroniConstant / 2)) /
              x) +
        ((q.totient : ℝ) - 1) * cosetCharacterNormError q x +
        2 * (Real.sqrt x + 19 / 6) *
          (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x
              (1 : DirichletCharacter ℂ q)).re := by
  let S := Finset.univ.erase (1 : DirichletCharacter ℂ q)
  let A := Real.sqrt x + 19 / 6
  let C := Real.log q - Real.log Real.pi + Real.log 2 + 1 / (20 * x)
  let E := fun χ : DirichletCharacter ℂ q ↦ reciprocalCorrection χ.primitiveCharacter x
  let R := fun χ : DirichletCharacter ℂ q ↦
    (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ).re
  have hA : 0 ≤ A := add_nonneg (Real.sqrt_nonneg x) (by norm_num only)
  have hR :=
    subgroup_reciprocal_average_nonneg (⊥ : Subgroup (ZMod q)ˣ)
      (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 65536) hx)
  change 0 ≤ ∑ χ : NumberTheory.subgroupAnnihilator (⊥ : Subgroup (ZMod q)ˣ), R χ.val at hR
  rw [NumberTheory.sum_subgroupAnnihilator_bot R] at hR
  have herase := Finset.sum_erase_add Finset.univ R (Finset.mem_univ 1)
  have hr : -(R 1) ≤ ∑ χ ∈ S, R χ := by
    change 0 ≤ ∑ χ, R χ at hR
    change (∑ χ ∈ S, R χ) + R 1 = ∑ χ, R χ at herase
    linarith only [hR, herase]
  have hb :
    (∑ χ ∈ S, ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ‖) ≤
      ∑ χ ∈ S, (A * (C + 2 * E χ - 2 * R χ) + cosetCharacterNormError q x) := by
    apply Finset.sum_le_sum
    intro χ hχ
    let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hs :=
      norm_characterLogWeightedSum_le_coset_parity χ hq
        (NumberTheory.three_le_conductor_of_ne_one χ (Finset.mem_erase.mp hχ).1) hGRH hx
    dsimp only [A, C, E, R]
    dsimp only [cosetCharacterNormError]
    nlinarith only [hs]
  have hid :
    (∑ χ ∈ S, (A * (C + 2 * E χ - 2 * R χ) + cosetCharacterNormError q x)) =
      (S.card : ℝ) * (A * C + cosetCharacterNormError q x) + A * (2 * ∑ χ ∈ S, E χ) -
        2 * A * ∑ χ ∈ S, R χ := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have hcard : (S.card : ℝ) = (q.totient : ℝ) - 1 := by
    have hpos : 1 ≤ Fintype.card (DirichletCharacter ℂ q) :=
      Nat.succ_le_iff.mpr (Fintype.card_pos_iff.mpr ⟨1⟩)
    dsimp only [S]
    rw [Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ, Nat.cast_sub hpos,
      Nat.card_eq_fintype_card.symm,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q, Nat.cast_one]
  have he :=
    sum_nonprincipal_reciprocalCorrection_le_parity_average
      (lt_of_lt_of_le (by norm_num only : (2 : ℕ) < 64) hq)
      ((by norm_num only : (100 : ℝ) ≤ 65536).trans hx)
  have hmE := mul_le_mul_of_nonneg_left he hA
  have hmR := mul_le_mul_of_nonneg_left hr (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) hA)
  rw [hid, hcard] at hb
  dsimp only [S, E, R, A, C] at hb hmE hmR ⊢
  simp only [div_eq_mul_inv, mul_inv_rev] at hb hmE hmR ⊢
  nlinarith only [hb, hmE, hmR]

/-- Under RH and cutoff greater than one, the principal character reciprocal
sum is bounded by the unsigned Mangoldt sum and its explicit formula.
The zero-mass bound gives the rational square-root error `1/(20*sqrt x)`.
This removes the principal contribution from parity-averaged norm estimates. -/
theorem principal_characterReciprocalWeightedSum_re_le_explicit {q : ℕ} [NeZero q]
    (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x
          (1 : DirichletCharacter ℂ q)).re ≤
      Real.log x - (1 + Real.eulerMascheroniConstant) + Real.log (2 * Real.pi) / x +
        1 / (20 * Real.sqrt x) := by
  have hr :=
    (Complex.re_le_norm _).trans
      (AnalyticNumberTheory.Arithmetic.norm_characterReciprocalWeightedSum_le
        (1 : DirichletCharacter ℂ q) (zero_lt_one.trans hx))
  have he := reciprocalWeightedMangoldtSum_le_explicit hRH hx
  have hm :=
    div_le_div_of_nonneg_right AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_one_fortieth
      (Real.sqrt_nonneg x)
  simp only [div_eq_mul_inv, mul_inv_rev] at he hm ⊢
  nlinarith only [hr, he, hm]

/-- The all-character norm majorant at modulus `q` and cutoff `x`, with exact
even and odd reciprocal corrections averaged before simplification.
It contains the common endpoint error once per nonprincipal character and the
RH upper bound for the principal reciprocal sum.
This real expression supplies the refined small-modulus residue gap. -/
noncomputable def residueNonprincipalParityUpper (q : ℕ) (x : ℝ) : ℝ :=
  (Real.sqrt x + 19 / 6) *
      (((q.totient : ℝ) - 1) * (Real.log q - Real.log Real.pi - Real.eulerMascheroniConstant) +
        Real.log 2 +
        (((q.totient : ℝ) - 1) / 20 +
            ((q.totient : ℝ) - 2) * (Real.log x + 1 + Real.eulerMascheroniConstant / 2) +
            (q.totient : ℝ) * (Real.log 2 + Real.eulerMascheroniConstant / 2)) /
          x) +
    ((q.totient : ℝ) - 1) * cosetCharacterNormError q x +
    2 * (Real.sqrt x + 19 / 6) *
      (Real.log x - (1 + Real.eulerMascheroniConstant) + Real.log (2 * Real.pi) / x +
        1 / (20 * Real.sqrt x))

open Classical in
/-- Under GRH, modulus at least 64, and cutoff at least 65536, bound the
nonprincipal residue-character norm sum by the explicit parity majorant.
Identify the identity subgroup's annihilator with all characters, apply the
parity average, and replace the principal reciprocal sum by its RH upper bound.
No character sums remain in the majorant used by numerical certificates. -/
theorem nonprincipal_residue_logWeightedNorm_sum_le_parity_explicit {q : ℕ} [NeZero q] (hq : 64 ≤ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 65536 ≤ x) :
    (∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator (⊥ : Subgroup (ZMod q)ˣ)),
        ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ.val‖) ≤
      residueNonprincipalParityUpper q x := by
  rw [NumberTheory.sum_nonprincipal_subgroupAnnihilator_bot
      (fun χ ↦ ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ‖)]
  have hs := nonprincipal_logWeightedNorm_sum_le_parity_average hq hGRH hx
  have hr :=
    principal_characterReciprocalWeightedSum_re_le_explicit (q := q) hGRH.riemann
      (lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 65536) hx)
  have hm :=
    mul_le_mul_of_nonneg_left hr
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2)
        (add_nonneg (Real.sqrt_nonneg x) (by norm_num only : (0 : ℝ) ≤ 19 / 6)))
  dsimp only [residueNonprincipalParityUpper]
  linarith only [hs, hm]

end PseudoPrime.LLS.PaperStatements
