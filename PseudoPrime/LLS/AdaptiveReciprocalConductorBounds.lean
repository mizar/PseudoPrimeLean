/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.VariableReciprocalConductorBounds

/-! # Explicit adaptive reciprocal conductor bounds -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under RH at x ≥ 64, the principal reciprocal Mangoldt sum is at most log(x).
Use its explicit formula, the Euler constant lower bound and the zeta zero-mass cap.
This removes the finite sum from the adaptive Hadamard estimate. -/
theorem reciprocalWeightedMangoldtSum_le_log_of_ge_sixtyFour (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 64 ≤ x) :
    AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum x ≤ Real.log x := by
  have hx0 : 0 < x := by linarith only [hx]
  have hs : (8 : ℝ) ≤ Real.sqrt x :=
    Real.le_sqrt_of_sq_le
      (by
        norm_num only at hx ⊢; exact hx)
  have hp :=
    Real.log_le_log (mul_pos (by norm_num only) Real.pi_pos)
      (mul_le_mul_of_nonneg_left Real.pi_lt_four.le (by norm_num only : (0 : ℝ) ≤ 2))
  rw [show (2 : ℝ) * 4 = 2 ^ (3 : ℕ) by norm_num only, Real.log_pow] at hp
  norm_num only at hp
  have hd : Real.log (2 * Real.pi) / x ≤ (3 / 64 : ℝ) := by
    apply (div_le_iff₀ hx0).mpr
    linarith only [hp, Real.log_two_lt_d9, hx]
  have hz : 2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass / Real.sqrt x ≤ (1 / 160 : ℝ) := by
    apply (div_le_iff₀ (show 0 < Real.sqrt x by linarith only [hs])).mpr
    linarith only [hs, AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_one_fortieth]
  have hr := LLS.reciprocalWeightedMangoldtSum_le_explicit hRH (show 1 < x by linarith only [hx])
  linarith only [hr, hd, hz, Real.one_half_lt_eulerMascheroniConstant]

/-- For y ≥ 8, log(y) ≤ y/4+1/10. Use the logarithm tangent at eight and
the certified bound log(2) < 7/10. This controls the adaptive reciprocal quotient. -/
theorem log_le_quarter_add_tenth_of_ge_eight {y : ℝ} (hy : 8 ≤ y) :
    Real.log y ≤ y / 4 + 1 / 10 := by
  have ht :=
    Analysis.log_le_log_add_sub_div (a := (8 : ℝ)) (by norm_num only)
      (show 0 < y by linarith only [hy])
  have h8 : Real.log (8 : ℝ) ≤ (21 / 10 : ℝ) := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9]
  linarith only [ht, h8, hy]

/-- For y ≥ 8, the reciprocal quotient with L=y-8 is at most L/2+2log(y)+2.
Clear the positive denominators and use the tangent bound multiplied by y.
This is the scalar comparison for the conductor-dependent cutoff y². -/
theorem reciprocal_adaptive_quotient_le {y : ℝ} (hy : 8 ≤ y) :
    ((1 / 2 : ℝ) * (1 - 1 / y ^ 2) * (y - 8) + 2 * Real.log y) / (1 - 1 / y) ^ 2 ≤
      (1 / 2 : ℝ) * (y - 8) + 2 * Real.log y + 2 := by
  have hy0 : 0 < y := by linarith only [hy]
  have hi : 1 / y < 1 := by
    simpa only [one_div] using inv_lt_one_of_one_lt₀ (show 1 < y by linarith only [hy])
  apply (div_le_iff₀ (sq_pos_of_pos (sub_pos.mpr hi))).mpr
  have hl := log_le_quarter_add_tenth_of_ge_eight hy
  have hl0 := Real.log_nonneg (show 1 ≤ y by linarith only [hy])
  have hm := mul_le_mul_of_nonneg_right hl hy0.le
  field_simp [hy0.ne']
  nlinarith only [hm, hl0, hy]

/-- Under RH, for any level q and nonnegative reciprocal saving η, choosing
x=(log(q)+8)² bounds the Hadamard quotient by log(q)/2+2log(log(q)+8)+2.
Use the principal logarithmic cap, retain the positive denominator and apply
the scalar quotient lemma. No finite sum remains in the resulting expression. -/
theorem reciprocalHadamardCap_adaptive_le (q : ℕ) (hRH : RiemannHypothesis) {η : ℝ} (hη : 0 ≤ η) :
    reciprocalHadamardCap q ((Real.log q + 8) ^ 2) η ≤
      (1 / 2 : ℝ) * Real.log q + 2 * Real.log (Real.log q + 8) + 2 := by
  have hL := Real.log_natCast_nonneg q
  have hy : 8 ≤ Real.log q + 8 := by linarith only [hL]
  have hy0 : 0 < Real.log q + 8 := by linarith only [hy]
  have hx : 64 ≤ (Real.log q + 8) ^ 2 := by nlinarith only [hy]
  have hx0 : 0 < (Real.log q + 8) ^ 2 := by linarith only [hx]
  have hr := reciprocalWeightedMangoldtSum_le_log_of_ge_sixtyFour hRH hx
  rw [Real.log_pow] at hr
  norm_num only [Nat.cast_ofNat] at hr
  have hi : 1 / (Real.log q + 8) ^ 2 ≤ (1 : ℝ) := by
    apply (div_le_iff₀ hx0).mpr
    linarith only [hx]
  have hm :=
    mul_nonneg (sub_nonneg.mpr hi)
      (show 0 ≤ Real.log Real.pi by linarith only [Analysis.log_pi_ge_2096_div_1831])
  have hn :
    (1 / 2 : ℝ) * (1 - 1 / (Real.log q + 8) ^ 2) * (Real.log q - Real.log Real.pi) - η +
        AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum ((Real.log q + 8) ^ 2) ≤
      (1 / 2 : ℝ) * (1 - 1 / (Real.log q + 8) ^ 2) * Real.log q +
        2 * Real.log (Real.log q + 8) := by
    linarith only [hr, hm, hη]
  have hd := reciprocalHadamardCap_den_pos hx
  rw [Real.sqrt_sq hy0.le] at hd
  have hb := div_le_div_of_nonneg_right hn hd.le
  dsimp only [reciprocalHadamardCap]
  rw [Real.sqrt_sq hy0.le]
  have hs := reciprocal_adaptive_quotient_le hy
  norm_num only [add_sub_cancel_right] at hs
  exact hb.trans hs

/-- Under GRH for primitive χ at level q ≥ 3, its absolute Hadamard constant
is at most log(q)/2+2log(log(q)+8)+2. Choose the adaptive reciprocal cutoff
in the previously proved raw formula. This lowers the leading conductor coefficient. -/
theorem abs_primitiveBRe_le_adaptive_reciprocal {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| ≤
      (1 / 2 : ℝ) * Real.log q + 2 * Real.log (Real.log q + 8) + 2 := by
  have hx : 64 ≤ (Real.log q + 8) ^ 2 := by nlinarith only [Real.log_natCast_nonneg q]
  exact
    (abs_primitiveBRe_le_variable_reciprocal hq hp hGRH hx).trans
      (reciprocalHadamardCap_adaptive_le q hGRH.riemann (by norm_num only : (0 : ℝ) ≤ 1 / 4))

/-- Under primitive GRH at q ≥ 3 and x ≥ 100, bound the actual logarithmic sum
by ((101/60)log(q)+(22/5)log(log(q)+8)+203/20)sqrt(x).
Pass the adaptive Hadamard cap and independent xi endpoint cap to the norm interface. -/
theorem norm_characterLogWeightedSum_le_adaptive_reciprocal {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 100 ≤ x) :
    ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ‖ ≤
      ((101 / 60 : ℝ) * Real.log q + (22 / 5) * Real.log (Real.log q + 8) + 203 / 20) *
        Real.sqrt x := by
  have h :=
    norm_characterLogWeightedSum_le_endpoint_caps hq hp hGRH hx
      (abs_primitiveBRe_le_adaptive_reciprocal hq hp hGRH)
      (norm_logDeriv_xi_zero_le_refined_uniform hq hp hGRH)
  have he (L : ℝ) :
    (11 / 5 : ℝ) * ((1 / 2) * L + 2 * Real.log (L + 8) + 2) + ((2 / 3) * L + 9 / 2) / 2 + L / 4 +
        7 / 2 =
      (101 / 60 : ℝ) * L + (22 / 5) * Real.log (L + 8) + 203 / 20 := by
    ring
  rw [he] at h
  exact h

/-- For conductor logarithm L, define (707/240)L+(77/10)log(L+8)+3557/80.
This is the positive radius coefficient produced by the generic witness extractor
from the adaptive reciprocal norm bound. Later sign results assume L ≥ 0. -/
noncomputable def adaptiveReciprocalRadius (L : ℝ) : ℝ :=
  (707 / 240) * L + (77 / 10) * Real.log (L + 8) + 3557 / 80

/-- For conductor f and excluded integer m, define the squared positive root
using the adaptive radius and the distinct-prime logarithmic cost of m.
This is the finite-sum-free-in-the-cutoff witness bound; the exclusion cost remains. -/
noncomputable def adaptiveReciprocalWitnessBound (f m : ℕ) : ℝ :=
  (adaptiveReciprocalRadius (Real.log f) +
      Real.sqrt
        ((adaptiveReciprocalRadius (Real.log f)) ^ 2 +
          (14 / 5 : ℝ) * (∑ r ∈ m.primeFactors, Real.log r))) ^
    2

/-- Under GRH for primitive χ at q ≥ 3 and excluded m ≠ 0, there is a prime
outside m with χ(p) ≠ 1 below the adaptive reciprocal root.
Apply the generic norm-cap extractor and identify the radius coefficient. -/
theorem exists_prime_ne_one_le_adaptive_reciprocal_root {q m : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hm : m ≠ 0) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ adaptiveReciprocalWitnessBound q m ∧ ¬p ∣ m ∧ χ p ≠ 1 := by
  have hL := Real.log_natCast_nonneg q
  have hl : 0 ≤ Real.log (Real.log q + 8) :=
    Real.log_nonneg (show 1 ≤ Real.log q + 8 by linarith only [hL])
  obtain ⟨p, hp', hb, hd, hv⟩ :=
    exists_prime_ne_one_le_norm_cap_root χ hGRH.riemann hm (F :=
      (101 / 60 : ℝ) * Real.log q + (22 / 5) * Real.log (Real.log q + 8) + 203 / 20)
      (by linarith only [hL, hl])
      (fun _ hx ↦ norm_characterLogWeightedSum_le_adaptive_reciprocal hq hp hGRH hx)
  have he :
    (7 / 4 : ℝ) * ((101 / 60 : ℝ) * Real.log q + (22 / 5) * Real.log (Real.log q + 8) + 203 / 20) +
        267 / 10 =
      adaptiveReciprocalRadius (Real.log q) := by
    dsimp only [adaptiveReciprocalRadius]
    ring
  rw [he] at hb
  exact ⟨p, hp', hb, hd, hv⟩

/-- For L ≥ 100, the adaptive radius plus 77/20 is at most the preceding fixed
even radius. Use the logarithm tangent at 108 and log(108) < 5.
This certifies a domain where the new structural bound improves even the parity-refined one. -/
theorem adaptiveReciprocalRadius_le_even_fixed_of_ge_hundred {L : ℝ} (hL : 100 ≤ L) :
    adaptiveReciprocalRadius L + 77 / 20 ≤ (2429 / 720 : ℝ) * L + 17939 / 400 := by
  have ht :=
    Analysis.log_le_log_add_sub_div (a := (108 : ℝ)) (by norm_num only)
      (show 0 < L + 8 by linarith only [hL])
  have h108 :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 108) (by norm_num only : (108 : ℝ) ≤ 2 ^ (7 : ℕ))
  rw [Real.log_pow] at h108
  norm_num only [Nat.cast_ofNat] at h108
  have hb : (1 / 2 : ℝ) * L + 2 * Real.log (L + 8) + 2 + 1 ≤ (11 / 18 : ℝ) * L + 21 / 10 := by
    linarith only [ht, h108, Real.log_two_lt_d9, hL]
  dsimp only [adaptiveReciprocalRadius]
  linarith only [hb]

/-- For log(f) ≥ 100, the adaptive witness root is at most the preceding fixed
even root with the same exclusion cost. Compare nonnegative radii using the
certified large-conductor inequality. The general fixed root is larger still. -/
theorem adaptiveReciprocalWitnessBound_le_even_fixed {f m : ℕ} (hL : 100 ≤ Real.log f) :
    adaptiveReciprocalWitnessBound f m ≤
      ((2429 / 720 : ℝ) * Real.log f + 17939 / 400 +
          Real.sqrt
            (((2429 / 720 : ℝ) * Real.log f + 17939 / 400) ^ 2 +
              (14 / 5 : ℝ) * (∑ r ∈ m.primeFactors, Real.log r))) ^
        2 := by
  have hl := Real.log_nonneg (show 1 ≤ Real.log f + 8 by linarith only [hL])
  apply root_radius_sq_mono
  · dsimp only [adaptiveReciprocalRadius]
    linarith only [hL, hl]
  · linarith only [adaptiveReciprocalRadius_le_even_fixed_of_ge_hundred hL]
  · exact le_rfl

/-- For L ≥ 0, the adaptive radius is at least (707/240)L+3557/80.
Use nonnegativity of log(L+8). This absorbs squarefree-part exclusion costs. -/
theorem adaptiveReciprocalRadius_lower_bound {L : ℝ} (hL : 0 ≤ L) :
    (707 / 240 : ℝ) * L + 3557 / 80 ≤ adaptiveReciprocalRadius L := by
  have hl := Real.log_nonneg (show 1 ≤ L + 8 by linarith only [hL])
  dsimp only [adaptiveReciprocalRadius]
  linarith only [hl]

/-- For L ≥ 0, the adaptive radius is nonnegative. Apply its linear lower bound.
This supplies the sign required by root and square monotonicity. -/
theorem adaptiveReciprocalRadius_nonneg {L : ℝ} (hL : 0 ≤ L) : 0 ≤ adaptiveReciprocalRadius L := by
  linarith only [adaptiveReciprocalRadius_lower_bound hL, hL]

/-- For 0 ≤ L₁ ≤ L₂, the adaptive radius is increasing. Apply logarithm
monotonicity to L+8 and compare the positive coefficients.
This transfers actual conductors to the squarefree-part conductor bound. -/
theorem adaptiveReciprocalRadius_mono {L₁ L₂ : ℝ} (hL₁ : 0 ≤ L₁) (hL : L₁ ≤ L₂) :
    adaptiveReciprocalRadius L₁ ≤ adaptiveReciprocalRadius L₂ := by
  have hl :=
    Real.log_le_log (show 0 < L₁ + 8 by linarith only [hL₁])
      (show L₁ + 8 ≤ L₂ + 8 by linarith only [hL])
  dsimp only [adaptiveReciprocalRadius]
  linarith only [hL, hl]

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS

/-- Under GRH for a nonprincipal character at nonzero level q, a unit-prime
non-one witness lies below the adaptive bound in its primitive conductor.
Exclude the original level and transfer the primitive value on units. -/
theorem exists_prime_ne_one_le_adaptive_reciprocal_root {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ PaperStatements.adaptiveReciprocalWitnessBound χ.conductor q ∧
        ¬p ∣ q ∧ χ p ≠ 1 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hc := NumberTheory.three_le_conductor_of_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    PaperStatements.exists_prime_ne_one_le_adaptive_reciprocal_root χ.primitiveCharacter hc
      χ.primitiveCharacter_isPrimitive hGRH (NeZero.ne q)
  have he := χ.primitiveCharacter_apply_of_isCoprime (hp.coprime_iff_not_dvd.mpr hd).isCoprime
  simp only [Int.cast_natCast] at he
  exact ⟨p, hp, hb, hd, fun h ↦ hv (he.trans h)⟩

/-- Under GRH, a nonprincipal character trivial on H gives a unit-prime
outside H below the adaptive conductor bound. Transfer the non-one value to
exclusion from the subgroup image. This is the proper-subgroup witness interface. -/
theorem exists_prime_outside_le_adaptive_character_conductor {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (ht : ∀ u : (ZMod q)ˣ, u ∈ H → χ (u : ZMod q) = 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        (p : ℝ) ≤ PaperStatements.adaptiveReciprocalWitnessBound χ.conductor q ∧
        ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  obtain ⟨p, hp, hb, hd, hv⟩ := exists_prime_ne_one_le_adaptive_reciprocal_root χ hχ hGRH
  refine ⟨p, hp, hd, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  exact hv (he ▸ ht u hu)

end PseudoPrime.LLS
