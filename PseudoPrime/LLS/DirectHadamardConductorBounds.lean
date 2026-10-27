/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.EndpointConductorBounds
public import PseudoPrime.NumberTheory.DirichletCharacterParity
public import PseudoPrime.LLS.Extensions.RetainedEvenReciprocalBounds
public import PseudoPrime.Analysis.PrecisePiLogBound

/-! # Direct Hadamard bounds from the real reciprocal formula -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under RH, the principal reciprocal sum at 100 is at most 789/250.
Retain the explicit Euler-constant and zero-mass bounds. This supplies a small
fixed arithmetic cap without enumerating input integers or characters. -/
theorem reciprocal_hundred_le_789_div_250 (hRH : RiemannHypothesis) :
    AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum 100 ≤ (789 / 250 : ℝ) := by
  have h := LLS.reciprocalWeightedMangoldtSum_le_explicit hRH (by norm_num only : (1 : ℝ) < 100)
  norm_num only at h
  have hpi :=
    Real.log_le_log (mul_pos (by norm_num only) Real.pi_pos)
      (mul_le_mul_of_nonneg_left Real.pi_lt_four.le (by norm_num only : (0 : ℝ) ≤ 2))
  rw [show (2 : ℝ) * 4 = 2 ^ (3 : ℕ) by norm_num only, Real.log_pow] at hpi
  norm_num only at hpi
  linarith only [h, hpi, Analysis.log_hundred_le_fourHundredSixtyThree_hundredths,
    AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_one_fortieth, Real.log_two_lt_d9,
    Real.one_half_lt_eulerMascheroniConstant]

/-- Under GRH for primitive χ of level q ≥ 3, its absolute Hadamard constant
is at most (11/18)log(q)+29/10. Combine the real reciprocal upper formula at 100
with the principal lower norm bound and the certified logarithm of pi.
This bypasses the loss from bounding the real term by the endpoint norm. -/
theorem abs_primitiveBRe_le_direct_reciprocal {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| ≤
      (11 / 18 : ℝ) * Real.log q + 29 / 10 := by
  have hne := primitiveCharacter_ne_one_of_three_le hq hp
  have hr :=
    LLS.primitiveReciprocalRaw (le_trans (by norm_num only : 2 ≤ 3) hq) hGRH hp hne
      (inv_ne_one.mpr hne) (x := 100) (by norm_num only)
  norm_num only at hr
  have hn :=
    AnalyticNumberTheory.Arithmetic.norm_characterReciprocalWeightedSum_le χ
      (by norm_num only : (0 : ℝ) < 100)
  have he :=
    (abs_le.mp
        (Complex.abs_re_le_norm
          (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum 100 χ))).1
  linarith only [hr, hn, he, reciprocal_hundred_le_789_div_250 hGRH.riemann,
    Analysis.log_pi_ge_2096_div_1831]

/-- Under GRH for primitive even χ of level q ≥ 3, its absolute Hadamard
constant is at most (11/18)log(q)+21/10. Use the retained even reciprocal remainder
and the same principal arithmetic cap. This is the sharper positive-input quadratic case. -/
theorem abs_primitiveBRe_even_le_direct_reciprocal {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 3 ≤ q) (hp : χ.IsPrimitive) (heven : χ.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| ≤
      (11 / 18 : ℝ) * Real.log q + 21 / 10 := by
  have hne := primitiveCharacter_ne_one_of_three_le hq hp
  have hr :=
    Extensions.primitiveReciprocalRaw_even_le_neg_179_div_200
      (le_trans (by norm_num only : 2 ≤ 3) hq) hGRH hp hne heven (x := 100) (by norm_num only)
  norm_num only at hr
  have hn :=
    AnalyticNumberTheory.Arithmetic.norm_characterReciprocalWeightedSum_le χ
      (by norm_num only : (0 : ℝ) < 100)
  have he :=
    (abs_le.mp
        (Complex.abs_re_le_norm
          (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum 100 χ))).1
  linarith only [hr, hn, he, reciprocal_hundred_le_789_div_250 hGRH.riemann,
    Analysis.log_pi_ge_2096_div_1831]

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH for primitive χ and x ≥ 100, the logarithmic sum norm is at
most ((347/180)log(q)+1213/100)sqrt(x). Pass the direct real Hadamard cap and
the independent endpoint cap to the generic norm theorem. -/
theorem norm_characterLogWeightedSum_le_direct_hadamard {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 100 ≤ x) :
    ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ‖ ≤
      ((347 / 180 : ℝ) * Real.log q + 1213 / 100) * Real.sqrt x := by
  have h :=
    norm_characterLogWeightedSum_le_endpoint_caps hq hp hGRH hx
      (abs_primitiveBRe_le_direct_reciprocal hq hp hGRH)
      (norm_logDeriv_xi_zero_le_refined_uniform hq hp hGRH)
  have he (L : ℝ) :
    (11 / 5 : ℝ) * ((11 / 18) * L + 29 / 10) + ((2 / 3) * L + 9 / 2) / 2 + L / 4 + 7 / 2 =
      (347 / 180 : ℝ) * L + 1213 / 100 := by
    ring
  rw [he] at h
  exact h

/-- Under GRH for primitive even χ and x ≥ 100, the logarithmic sum norm is
at most ((347/180)log(q)+1037/100)sqrt(x). Retain the even Hadamard gain while
using the common endpoint bound. This improves the quadratic witness input. -/
theorem norm_characterLogWeightedSum_even_le_direct_hadamard {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 3 ≤ q) (hp : χ.IsPrimitive) (heven : χ.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 100 ≤ x) :
    ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ‖ ≤
      ((347 / 180 : ℝ) * Real.log q + 1037 / 100) * Real.sqrt x := by
  have h :=
    norm_characterLogWeightedSum_le_endpoint_caps hq hp hGRH hx
      (abs_primitiveBRe_even_le_direct_reciprocal hq hp heven hGRH)
      (norm_logDeriv_xi_zero_le_refined_uniform hq hp hGRH)
  have he (L : ℝ) :
    (11 / 5 : ℝ) * ((11 / 18) * L + 21 / 10) + ((2 / 3) * L + 9 / 2) / 2 + L / 4 + 7 / 2 =
      (347 / 180 : ℝ) * L + 1037 / 100 := by
    ring
  rw [he] at h
  exact h

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH for primitive χ of level q ≥ 3 and excluded m ≠ 0, a non-one
prime outside m lies below the root bound with radius (2429/720)log(q)+19171/400.
Instantiate the generic norm-cap extractor with the direct Hadamard norm estimate. -/
theorem exists_prime_ne_one_le_direct_conductor_root {q m : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hm : m ≠ 0) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          ((2429 / 720 : ℝ) * Real.log q + 19171 / 400 +
              Real.sqrt
                (((2429 / 720 : ℝ) * Real.log q + 19171 / 400) ^ 2 +
                  (14 / 5 : ℝ) * (∑ r ∈ m.primeFactors, Real.log r))) ^
            2 ∧
        ¬p ∣ m ∧ χ p ≠ 1 := by
  obtain ⟨p, hp', hb, hd, hv⟩ :=
    exists_prime_ne_one_le_norm_cap_root χ hGRH.riemann hm (F :=
      (347 / 180 : ℝ) * Real.log q + 1213 / 100) (by linarith only [Real.log_natCast_nonneg q])
      (fun _ hx ↦ norm_characterLogWeightedSum_le_direct_hadamard hq hp hGRH hx)
  have he :
    (7 / 4 : ℝ) * ((347 / 180 : ℝ) * Real.log q + 1213 / 100) + 267 / 10 =
      (2429 / 720 : ℝ) * Real.log q + 19171 / 400 := by
    ring
  rw [he] at hb
  exact ⟨p, hp', hb, hd, hv⟩

/-- Under GRH for primitive even χ and m ≠ 0, a non-one prime outside m lies
below the root bound with radius (2429/720)log(q)+17939/400. Use the parity-refined
norm cap in the generic extractor. This retains the stronger constant for even characters. -/
theorem exists_prime_ne_one_le_even_direct_conductor_root {q m : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q) (hp : χ.IsPrimitive) (heven : χ.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hm : m ≠ 0) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          ((2429 / 720 : ℝ) * Real.log q + 17939 / 400 +
              Real.sqrt
                (((2429 / 720 : ℝ) * Real.log q + 17939 / 400) ^ 2 +
                  (14 / 5 : ℝ) * (∑ r ∈ m.primeFactors, Real.log r))) ^
            2 ∧
        ¬p ∣ m ∧ χ p ≠ 1 := by
  obtain ⟨p, hp', hb, hd, hv⟩ :=
    exists_prime_ne_one_le_norm_cap_root χ hGRH.riemann hm (F :=
      (347 / 180 : ℝ) * Real.log q + 1037 / 100) (by linarith only [Real.log_natCast_nonneg q])
      (fun _ hx ↦ norm_characterLogWeightedSum_even_le_direct_hadamard hq hp heven hGRH hx)
  have he :
    (7 / 4 : ℝ) * ((347 / 180 : ℝ) * Real.log q + 1037 / 100) + 267 / 10 =
      (2429 / 720 : ℝ) * Real.log q + 17939 / 400 := by
    ring
  rw [he] at hb
  exact ⟨p, hp', hb, hd, hv⟩

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS

/-- Under GRH, a nonprincipal character at nonzero level q has a unit-prime
non-one witness below the direct Hadamard root bound in its primitive conductor.
Apply the primitive theorem with exclusion q and transfer the value on units. -/
theorem exists_prime_ne_one_le_direct_conductor_root {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          (((2429 / 720 : ℝ) * Real.log χ.conductor + 19171 / 400 +
              Real.sqrt
                (((2429 / 720 : ℝ) * Real.log χ.conductor + 19171 / 400) ^ 2 +
                  (14 / 5 : ℝ) * (∑ r ∈ q.primeFactors, Real.log r))) ^
            2) ∧
        ¬p ∣ q ∧ χ p ≠ 1 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hc := NumberTheory.three_le_conductor_of_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    PaperStatements.exists_prime_ne_one_le_direct_conductor_root χ.primitiveCharacter hc
      χ.primitiveCharacter_isPrimitive hGRH (NeZero.ne q)
  have he := χ.primitiveCharacter_apply_of_isCoprime (hp.coprime_iff_not_dvd.mpr hd).isCoprime
  simp only [Int.cast_natCast] at he
  exact ⟨p, hp, hb, hd, fun h ↦ hv (he.trans h)⟩

/-- Under GRH, a nonprincipal character trivial on a subgroup supplies a
unit-prime outside its image below the direct Hadamard root bound.
Transfer the proved character nontriviality to exclusion from the subgroup image. -/
theorem exists_prime_outside_le_direct_character_conductor {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (ht : ∀ u : (ZMod q)ˣ, u ∈ H → χ (u : ZMod q) = 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        (p : ℝ) ≤
          (((2429 / 720 : ℝ) * Real.log χ.conductor + 19171 / 400 +
              Real.sqrt
                (((2429 / 720 : ℝ) * Real.log χ.conductor + 19171 / 400) ^ 2 +
                  (14 / 5 : ℝ) * (∑ r ∈ q.primeFactors, Real.log r))) ^
            2) ∧
        ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  obtain ⟨p, hp, hb, hd, hv⟩ := exists_prime_ne_one_le_direct_conductor_root χ hχ hGRH
  refine ⟨p, hp, hd, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  exact hv (he ▸ ht u hu)

/-- Under GRH, a nonprincipal even character at nonzero level q has a
unit-prime non-one witness below the parity-refined root bound in its conductor.
Preserve evenness through primitivization and transfer the unit value. -/
theorem exists_prime_ne_one_le_even_direct_conductor_root {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (heven : χ.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          (((2429 / 720 : ℝ) * Real.log χ.conductor + 17939 / 400 +
              Real.sqrt
                (((2429 / 720 : ℝ) * Real.log χ.conductor + 17939 / 400) ^ 2 +
                  (14 / 5 : ℝ) * (∑ r ∈ q.primeFactors, Real.log r))) ^
            2) ∧
        ¬p ∣ q ∧ χ p ≠ 1 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hc := NumberTheory.three_le_conductor_of_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    PaperStatements.exists_prime_ne_one_le_even_direct_conductor_root χ.primitiveCharacter hc
      χ.primitiveCharacter_isPrimitive ((NumberTheory.primitiveCharacter_even_iff χ).mpr heven) hGRH
      (NeZero.ne q)
  have he := χ.primitiveCharacter_apply_of_isCoprime (hp.coprime_iff_not_dvd.mpr hd).isCoprime
  simp only [Int.cast_natCast] at he
  exact ⟨p, hp, hb, hd, fun h ↦ hv (he.trans h)⟩

end PseudoPrime.LLS

namespace PseudoPrime.LLS.PaperStatements

/-- For L ≥ 0 and real E, the direct Hadamard root bound is at most the
preceding endpoint root bound. Compare the smaller radius coefficient and
constant by the established generic monotonicity theorem. -/
theorem direct_hadamard_conductor_root_le_previous {L E : ℝ} (hL : 0 ≤ L) :
    ((2429 / 720 : ℝ) * L + 19171 / 400 +
          Real.sqrt (((2429 / 720 : ℝ) * L + 19171 / 400) ^ 2 + (14 / 5 : ℝ) * E)) ^
        2 ≤
      ((287 / 80 : ℝ) * L + 4327 / 80 +
          Real.sqrt (((287 / 80 : ℝ) * L + 4327 / 80) ^ 2 + (14 / 5 : ℝ) * E)) ^
        2 := by
  apply root_radius_sq_mono
  · linarith only [hL]
  · linarith only [hL]
  · exact le_refl _

end PseudoPrime.LLS.PaperStatements
