/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.AffineConductorWitnessBounds

/-! # Separate endpoint caps and conductor-sensitive prime witnesses -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH for primitive χ of level q ≥ 3, the xi endpoint norm is at most
(2/3)log(q)+9/2. Retain the sharper large-level coefficient and bound the small
levels by the reciprocal majorant without enumerating characters.
This supplies a uniform conductor-sensitive endpoint input. -/
theorem norm_logDeriv_xi_zero_le_refined_uniform {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ‖logDeriv (xi χ) 0‖ ≤ (2 / 3 : ℝ) * Real.log q + 9 / 2 := by
  by_cases h8 : 8 ≤ q
  · have hb := norm_logDeriv_xi_zero_le_log_level h8 hp hGRH
    rw [Real.log_div (Nat.cast_ne_zero.mpr (NeZero.ne q)) Real.pi_ne_zero] at hb
    have hpi := Real.log_nonneg (by linarith only [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi)
    linarith only [hb, hpi]
  · have hb := norm_logDeriv_xi_zero_le_cutoff100 hq hp hGRH
    have hm := reciprocal_cutoff_hundred_majorant_le_max χ hGRH.riemann
    have hL := log_level_div_pi_small_bounds hq (Nat.lt_of_not_ge h8)
    have hmax :
      max ((789 / 250 : ℝ) + (99 / 200 : ℝ) * Real.log ((q : ℝ) / Real.pi))
          ((41 / 10 : ℝ) - (99 / 200 : ℝ) * Real.log ((q : ℝ) / Real.pi)) ≤
        413 / 100 := by
      apply max_le <;> linarith only [hL.1, hL.2]
    have hcap : ‖logDeriv (xi χ) 0‖ ≤ (523 / 100 : ℝ) := by linarith only [hb, hm, hmax]
    have hlog :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 3) (show (3 : ℝ) ≤ q by exact_mod_cast hq)
    linarith only [hcap, hlog, Real.log_three_gt_d9]

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH for primitive χ and x ≥ 100, separate caps b on its absolute primitive B term
and d on its xi endpoint norm give the displayed logarithmic sum estimate.
Retain the half-square-root logarithm bound and sqrt(x) ≥ 10.
This generic interface permits independent improvement of the two analytic inputs. -/
theorem norm_characterLogWeightedSum_le_endpoint_caps {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b d : ℝ} (hx : 100 ≤ x)
    (hBcap : |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| ≤ b)
    (hDcap : ‖logDeriv (xi χ) 0‖ ≤ d) :
    ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ‖ ≤
      ((11 / 5 : ℝ) * b + d / 2 + Real.log q / 4 + 7 / 2) * Real.sqrt x := by
  have hx1 : 1 < x := (by norm_num only : (1 : ℝ) < 100).trans_le hx
  have hs : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx1.le
  have hl0 := (Real.log_pos hx1).le
  have hls := log_sq_le_three_sqrt_of_ge_eightyOne ((by norm_num only : (81 : ℝ) ≤ 100).trans hx)
  have hs10 : (10 : ℝ) ≤ Real.sqrt x :=
    Real.le_sqrt_of_sq_le
      (by
        norm_num only at hx ⊢; exact hx)
  have hl := log_le_half_sqrt_of_ge_eightyOne ((by norm_num only : (81 : ℝ) ≤ 100).trans hx)
  have hq0 := Real.log_natCast_nonneg q
  have hnorm := norm_characterLogWeightedSum_le_explicit hq hp hGRH hx1
  have hb0 := (abs_nonneg (AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ)).trans hBcap
  have hd0 := (norm_nonneg (logDeriv (xi χ) 0)).trans hDcap
  have hb := mul_le_mul_of_nonneg_right hBcap (show 0 ≤ 2 * Real.sqrt x + 2 by linarith only [hs])
  have hd := mul_le_mul_of_nonneg_right hDcap hl0
  have hc := abs_logCorrection_le_log_sq_of_ge_hundred χ hx
  have hlog := abs_log_level_div_pi_le_log_add_two (q := q)
  have hcorr :
    |Real.log ((q : ℝ) / Real.pi) * Real.log x / 2 + logCorrection χ x| ≤
      (Real.log q + 2) * Real.log x / 2 + (Real.log x) ^ 2 := by
    have ha := abs_add_le (Real.log ((q : ℝ) / Real.pi) * Real.log x / 2) (logCorrection χ x)
    rw [abs_div, abs_mul, abs_of_nonneg hl0] at ha
    rw [abs_of_pos (by norm_num only : (0 : ℝ) < 2)] at ha
    have hm := mul_le_mul_of_nonneg_right hlog hl0
    linarith only [ha, hc, hm]
  have hprod := mul_nonneg hq0 (show 0 ≤ Real.sqrt x / 2 - Real.log x by linarith only [hl])
  have hprod2 := mul_nonneg hb0 (sub_nonneg.mpr hs10)
  have hprodD := mul_nonneg hd0 (show 0 ≤ Real.sqrt x / 2 - Real.log x by linarith only [hl])
  nlinarith only [hnorm, hb, hd, hcorr, hl, hs10, hq0, hls, hprod, hprod2, hprodD]

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH for primitive χ of level q ≥ 3 and x ≥ 100, its logarithmic sum
has norm at most ((41/20)log(q)+313/20)sqrt(x). Pass the refined endpoint estimate
to both caps, using the real zero mass comparison. This closes the actual analytic input. -/
theorem norm_characterLogWeightedSum_le_refined_endpoint {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 100 ≤ x) :
    ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ‖ ≤
      ((41 / 20 : ℝ) * Real.log q + 313 / 20) * Real.sqrt x := by
  have hD := norm_logDeriv_xi_zero_le_refined_uniform hq hp hGRH
  have h :=
    norm_characterLogWeightedSum_le_endpoint_caps hq hp hGRH hx
      ((abs_primitiveBRe_le_norm_logDeriv_xi_zero hq hp hGRH).trans hD) hD
  have he (L : ℝ) :
    (11 / 5 : ℝ) * ((2 / 3) * L + 9 / 2) + ((2 / 3) * L + 9 / 2) / 2 + L / 4 + 7 / 2 =
      (41 / 20 : ℝ) * L + 313 / 20 := by
    ring
  rw [he] at h
  exact h

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements

/-- Assume RH and a nonnegative global square-root norm cap F for χ at cutoffs
at least 100. If no non-one prime outside nonzero m occurs through y ≥ 200,
the displayed half-log comparison follows. Retain the half-scale root ratio and
log two. No primitive-character or GRH assumption is needed once the cap is supplied. -/
theorem log_half_no_witness_of_norm_cap {q m : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hRH : RiemannHypothesis) (hm : m ≠ 0) {F : ℝ} (hF : 0 ≤ F)
    (hNorm :
      ∀ x : ℝ,
        100 ≤ x → ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ‖ ≤ F * Real.sqrt x)
    {y : ℝ} (hy : 200 ≤ y) (hno : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ y → ¬p ∣ m → χ p = 1) :
    y / 2 ≤
      ((7 / 4 : ℝ) * F + 257 / 10) * Real.sqrt y +
        (7 / 5 : ℝ) * (∑ p ∈ m.primeFactors, Real.log p) := by
  have hy0 : 0 < y := (by norm_num only : (0 : ℝ) < 200).trans_le hy
  have hh : 100 ≤ y / 2 := by linarith only [hy]
  have hhalf : y / 2 ≤ y := by linarith only [hy0]
  have hb :=
    AnalyticNumberTheory.Arithmetic.log_difference_prime_exclusion χ hm
      (div_pos hy0 (by norm_num only : (0 : ℝ) < 2)) hhalf hno
  have hr : y / (y / 2) = 2 := by field_simp [hy0.ne']
  rw [hr] at hb
  have hP := principal_log_half_difference_lower_half_sqrt hRH hy
  have hR := hNorm y ((by norm_num only : (100 : ℝ) ≤ 200).trans hy)
  have hL := hNorm (y / 2) hh
  have hs : Real.sqrt (y / 2) ≤ (3 / 4 : ℝ) * Real.sqrt y := by
    apply Real.sqrt_le_iff.mpr
    exact
      ⟨mul_nonneg (by norm_num only) (Real.sqrt_nonneg y), by
        nlinarith only [Real.sq_sqrt hy0.le, hy0]⟩
  have hcoef : 0 ≤ F := hF
  have hLs := mul_le_mul_of_nonneg_left hs hcoef
  have hnorm :=
    (Complex.re_le_norm
          (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum y χ -
            AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y / 2) χ)).trans
      (norm_sub_le _ _)
  have ht := psi_sub_theta_le_eighteen_sqrt ((by norm_num only : (1 : ℝ) ≤ 200).trans hy)
  have hsum : 0 ≤ ∑ p ∈ m.primeFactors, Real.log p :=
    Finset.sum_nonneg (fun p _ ↦ Real.log_natCast_nonneg p)
  have htail := Chebyshev.theta_le_psi y
  have hln2 : Real.log (2 : ℝ) ≤ 7 / 10 := by linarith only [Real.log_two_lt_d9]
  have hscale1 :=
    mul_le_mul_of_nonneg_right hln2
      (show 0 ≤ (∑ p ∈ m.primeFactors, Real.log p) + Chebyshev.psi y - Chebyshev.theta y by
        linarith only [hsum, htail])
  nlinarith only [hb, hP, hR, hL, hLs, hnorm, ht, hscale1]

/-- Assume RH and the square-root norm cap F ≥ 0 for χ at cutoffs at least 100.
For nonzero excluded m, a non-one prime outside m lies below the stated root
radius. Its cutoff automatically exceeds 200 and violates the generic comparison.
This extracts witnesses from any actual norm cap without fixing conductor coefficients. -/
theorem exists_prime_ne_one_le_norm_cap_root {q m : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hRH : RiemannHypothesis) (hm : m ≠ 0) {F : ℝ} (hF : 0 ≤ F)
    (hNorm :
      ∀ x : ℝ,
        100 ≤ x → ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ‖ ≤ F * Real.sqrt x) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          ((7 / 4 : ℝ) * F + 267 / 10 +
              Real.sqrt
                (((7 / 4 : ℝ) * F + 267 / 10) ^ 2 +
                  (14 / 5 : ℝ) * (∑ r ∈ m.primeFactors, Real.log r))) ^
            2 ∧
        ¬p ∣ m ∧ χ p ≠ 1 := by
  classical
  let y :=
    ((7 / 4 : ℝ) * F + 267 / 10 +
        Real.sqrt
          (((7 / 4 : ℝ) * F + 267 / 10) ^ 2 + (14 / 5 : ℝ) * (∑ r ∈ m.primeFactors, Real.log r))) ^
      2
  have hB : 267 / 10 ≤ (7 / 4 : ℝ) * F + 267 / 10 := by linarith only [hF]
  have hy :
    (200 : ℝ) ≤
      ((7 / 4 : ℝ) * F + 267 / 10 +
          Real.sqrt
            (((7 / 4 : ℝ) * F + 267 / 10) ^ 2 +
              (14 / 5 : ℝ) * (∑ r ∈ m.primeFactors, Real.log r))) ^
        2 := by
    nlinarith only [hB,
      Real.sqrt_nonneg
        (((7 / 4 : ℝ) * F + 267 / 10) ^ 2 + (14 / 5 : ℝ) * (∑ r ∈ m.primeFactors, Real.log r))]
  by_contra hnone
  have hno (p : ℕ) (hp : p.Prime) (hb : (p : ℝ) ≤ y) (hd : ¬p ∣ m) : χ p = 1 := by
    by_contra hne
    exact hnone ⟨p, hp, hb, hd, hne⟩
  have hc := log_half_no_witness_of_norm_cap χ hRH hm hF hNorm hy hno
  have h :=
    conductor_exclusion_unclipped_root_gap (A := (7 / 4 : ℝ) * F + 257 / 10) (E :=
      (7 / 10 : ℝ) * (∑ r ∈ m.primeFactors, Real.log r)) (by linarith only [hF])
      (mul_nonneg (by norm_num only) (Finset.sum_nonneg (fun p _ ↦ Real.log_natCast_nonneg p)))
  have ha : (7 / 4 : ℝ) * F + 257 / 10 + 1 = (7 / 4 : ℝ) * F + 267 / 10 := by ring
  have htwo (E : ℝ) : 2 * ((7 / 10 : ℝ) * E) = (7 / 5 : ℝ) * E := by ring
  have hfour (E : ℝ) : 4 * ((7 / 10 : ℝ) * E) = (14 / 5 : ℝ) * E := by ring
  simp only [ha, htwo, hfour] at h
  exact hc.not_gt h

/-- Under GRH for primitive χ of level q ≥ 3 and m ≠ 0, a non-one prime outside
m lies below the displayed root bound with radius (287/80)log(q)+4327/80.
Instantiate the generic norm-cap theorem with the proved endpoint-sensitive norm bound.
This is the concrete improved conductor witness theorem. -/
theorem exists_prime_ne_one_le_endpoint_conductor_root {q m : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hm : m ≠ 0) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          ((287 / 80 : ℝ) * Real.log q + 4327 / 80 +
              Real.sqrt
                (((287 / 80 : ℝ) * Real.log q + 4327 / 80) ^ 2 +
                  (14 / 5 : ℝ) * (∑ r ∈ m.primeFactors, Real.log r))) ^
            2 ∧
        ¬p ∣ m ∧ χ p ≠ 1 := by
  obtain ⟨p, hp', hb, hd, hv⟩ :=
    exists_prime_ne_one_le_norm_cap_root χ hGRH.riemann hm (F :=
      (41 / 20 : ℝ) * Real.log q + 313 / 20) (by linarith only [Real.log_natCast_nonneg q])
      (fun _ hx ↦ norm_characterLogWeightedSum_le_refined_endpoint hq hp hGRH hx)
  have he :
    (7 / 4 : ℝ) * ((41 / 20 : ℝ) * Real.log q + 313 / 20) + 267 / 10 =
      (287 / 80 : ℝ) * Real.log q + 4327 / 80 := by
    ring
  rw [he] at hb
  exact ⟨p, hp', hb, hd, hv⟩

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS

/-- Under GRH, a nonprincipal character at nonzero level q has a unit-prime
non-one witness below the displayed root bound in its primitive conductor and
ambient exclusion cost. Primitivize and transfer the unit value back to χ.
This is the original-level interface for the smaller-scale conductor estimate. -/
theorem exists_prime_ne_one_le_endpoint_conductor_root {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          (((287 / 80 : ℝ) * Real.log χ.conductor + 4327 / 80 +
              Real.sqrt
                (((287 / 80 : ℝ) * Real.log χ.conductor + 4327 / 80) ^ 2 +
                  (14 / 5 : ℝ) * (∑ r ∈ q.primeFactors, Real.log r))) ^
            2) ∧
        ¬p ∣ q ∧ χ p ≠ 1 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hc := NumberTheory.three_le_conductor_of_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    PaperStatements.exists_prime_ne_one_le_endpoint_conductor_root χ.primitiveCharacter hc
      χ.primitiveCharacter_isPrimitive hGRH (NeZero.ne q)
  have he := χ.primitiveCharacter_apply_of_isCoprime (hp.coprime_iff_not_dvd.mpr hd).isCoprime
  simp only [Int.cast_natCast] at he
  exact ⟨p, hp, hb, hd, fun h ↦ hv (he.trans h)⟩

/-- Under GRH, a nonprincipal character trivial on a subgroup supplies a
unit-prime outside its image below the root conductor budget. Apply the character
witness and contradict triviality on a proposed subgroup unit.
This retains the chosen character's conductor in the subgroup conclusion. -/
theorem exists_prime_outside_le_endpoint_character_conductor {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (ht : ∀ u : (ZMod q)ˣ, u ∈ H → χ (u : ZMod q) = 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        (p : ℝ) ≤
          (((287 / 80 : ℝ) * Real.log χ.conductor + 4327 / 80 +
              Real.sqrt
                (((287 / 80 : ℝ) * Real.log χ.conductor + 4327 / 80) ^ 2 +
                  (14 / 5 : ℝ) * (∑ r ∈ q.primeFactors, Real.log r))) ^
            2) ∧
        ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  obtain ⟨p, hp, hb, hd, hv⟩ := exists_prime_ne_one_le_endpoint_conductor_root χ hχ hGRH
  refine ⟨p, hp, hd, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  exact hv (he ▸ ht u hu)

end PseudoPrime.LLS

namespace PseudoPrime.LLS.PaperStatements

/-- For L ≥ 0 and real E, the endpoint-refined root radius is no larger
than the preceding affine conductor root radius. Apply generic monotonicity
to its smaller logarithmic coefficient and additive constant. -/
theorem endpoint_conductor_root_le_previous {L E : ℝ} (hL : 0 ≤ L) :
    ((287 / 80 : ℝ) * L + 4327 / 80 +
          Real.sqrt (((287 / 80 : ℝ) * L + 4327 / 80) ^ 2 + (14 / 5 : ℝ) * E)) ^
        2 ≤
      ((21 / 4 : ℝ) * L + 617 / 10 +
          Real.sqrt (((21 / 4 : ℝ) * L + 617 / 10) ^ 2 + (14 / 5 : ℝ) * E)) ^
        2 := by
  apply root_radius_sq_mono
  · linarith only [hL]
  · linarith only [hL]
  · exact le_refl _

end PseudoPrime.LLS.PaperStatements
