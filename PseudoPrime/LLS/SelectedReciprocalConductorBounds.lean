/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.AdaptiveReciprocalConductorBounds

/-! # Selected half-conductor reciprocal cutoffs and explicit envelopes -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under RH and x≥64, the principal reciprocal Mangoldt sum is at most
log(x)-7/5. Retain the Euler constant saving in its explicit formula and bound
the two positive errors. This supplies the selected-cutoff Hadamard numerator. -/
theorem reciprocalWeightedMangoldtSum_le_log_sub_seven_fifths (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 64 ≤ x) :
    AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum x ≤ Real.log x - 7 / 5 := by
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

/-- For L≥16, log(L)≤L/16+9/5. Apply the logarithm tangent at sixteen and
the certified bound log(2)<7/10. This controls the half-conductor quotient. -/
theorem log_le_sixteenth_add_nine_fifths {L : ℝ} (hL : 16 ≤ L) : Real.log L ≤ L / 16 + 9 / 5 := by
  have ht :=
    Analysis.log_le_log_add_sub_div (a := (16 : ℝ)) (by norm_num only)
      (show 0 < L by linarith only [hL])
  have h16 : Real.log (16 : ℝ) ≤ (14 / 5 : ℝ) := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9]
  linarith only [ht, h16]

/-- For L≥16, the half-conductor reciprocal quotient with principal saving 7/5,
pi logarithm lower bound one and character saving 1/4 is at most L/2+2log(L).
Clear positive denominators and use the tangent bound times L.
This removes the additive constant from the previous adaptive Hadamard estimate. -/
theorem half_conductor_reciprocal_quotient_le {L : ℝ} (hL : 16 ≤ L) :
    ((1 / 2 : ℝ) * (1 - 1 / (L / 2) ^ 2) * (L - 1) - 1 / 4 + 2 * Real.log (L / 2) - 7 / 5) /
        (1 - 1 / (L / 2)) ^ 2 ≤
      (1 / 2 : ℝ) * L + 2 * Real.log L := by
  have hL0 : 0 < L := by linarith only [hL]
  have hi : 1 / (L / 2) < (1 : ℝ) := by
    simpa only [one_div] using inv_lt_one_of_one_lt₀ (show 1 < L / 2 by linarith only [hL])
  apply (div_le_iff₀ (sq_pos_of_pos (sub_pos.mpr hi))).mpr
  rw [Real.log_div hL0.ne' (by norm_num only : (2 : ℝ) ≠ 0)]
  have ht := log_le_sixteenth_add_nine_fifths hL
  have hm := mul_le_mul_of_nonneg_right ht hL0.le
  have hl0 := Real.log_nonneg (show 1 ≤ L by linarith only [hL])
  have hsq : 16 * L ≤ L ^ 2 := by nlinarith only [hL]
  field_simp [hL0.ne']
  nlinarith only [hm, hl0, hsq, hL, Real.log_two_gt_d9]

/-- Under RH, log(q)≥16 and η≥1/4, the reciprocal cap at (log(q)/2)² is at
most log(q)/2+2log(log(q)). Retain the negative principal constant and pi term.
The positive denominator permits transfer of the scalar selected-cutoff comparison. -/
theorem reciprocalHadamardCap_half_conductor_le {q : ℕ} (hL : 16 ≤ Real.log q)
    (hRH : RiemannHypothesis) {η : ℝ} (hη : (1 / 4 : ℝ) ≤ η) :
    reciprocalHadamardCap q ((Real.log q / 2) ^ 2) η ≤
      (1 / 2 : ℝ) * Real.log q + 2 * Real.log (Real.log q) := by
  have hy : 8 ≤ Real.log q / 2 := by linarith only [hL]
  have hy0 : 0 < Real.log q / 2 := by linarith only [hy]
  have hx : 64 ≤ (Real.log q / 2) ^ 2 := by nlinarith only [hy]
  have hx0 : 0 < (Real.log q / 2) ^ 2 := by linarith only [hx]
  have hr := reciprocalWeightedMangoldtSum_le_log_sub_seven_fifths hRH hx
  rw [Real.log_pow] at hr
  norm_num only [Nat.cast_ofNat] at hr
  have hi : 1 / (Real.log q / 2) ^ 2 ≤ (1 : ℝ) := by
    apply (div_le_iff₀ hx0).mpr
    linarith only [hx]
  have hp :=
    mul_nonneg (sub_nonneg.mpr hi)
      (show 0 ≤ Real.log Real.pi - 1 by linarith only [Analysis.log_pi_ge_2096_div_1831])
  have hn :
    (1 / 2 : ℝ) * (1 - 1 / (Real.log q / 2) ^ 2) * (Real.log q - Real.log Real.pi) - η +
        AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum ((Real.log q / 2) ^ 2) ≤
      (1 / 2 : ℝ) * (1 - 1 / (Real.log q / 2) ^ 2) * (Real.log q - 1) - 1 / 4 +
          2 * Real.log (Real.log q / 2) -
        7 / 5 := by
    linarith only [hr, hp, hη]
  have hd := reciprocalHadamardCap_den_pos hx
  rw [Real.sqrt_sq hy0.le] at hd
  have hb := div_le_div_of_nonneg_right hn hd.le
  dsimp only [reciprocalHadamardCap]
  rw [Real.sqrt_sq hy0.le]
  exact hb.trans (half_conductor_reciprocal_quotient_le hL)

/-- Under primitive GRH at q≥3, any envelope G≥16 with log(q)≤G bounds the
absolute Hadamard constant by G/2+2log(G). At large conductors choose (log(q)/2)²;
at smaller conductors use the existing fixed cap. The envelope handles small
actual conductors inside a large squarefree-part bound. -/
theorem abs_primitiveBRe_le_selected_envelope {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 3 ≤ q) (hp : χ.IsPrimitive) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {G : ℝ} (hG : 16 ≤ G) (hlog : Real.log q ≤ G) :
    |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| ≤
      (1 / 2 : ℝ) * G + 2 * Real.log G := by
  by_cases hL : 16 ≤ Real.log q
  · have hx : 64 ≤ (Real.log q / 2) ^ 2 := by nlinarith only [hL]
    have h :=
      (abs_primitiveBRe_le_variable_reciprocal hq hp hGRH hx).trans
        (reciprocalHadamardCap_half_conductor_le hL hGRH.riemann (le_refl (1 / 4 : ℝ)))
    have hl := Real.log_le_log (show 0 < Real.log q by linarith only [hL]) hlog
    linarith only [h, hlog, hl]
  · have hb := abs_primitiveBRe_le_direct_reciprocal hq hp hGRH
    have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 16) hG
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num only, Real.log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hl
    linarith only [hb, hl, Real.log_two_gt_d9, hG, lt_of_not_ge hL]

/-- For level q, define max(8,log(q)/2)² as the reciprocal-formula cutoff.
The lower truncation keeps it at least 64. It is independent of the witness cutoff
and is used with the existing minimum-based variable norm cap. -/
noncomputable def halfConductorReciprocalCutoff (q : ℕ) : ℝ :=
  (max 8 (Real.log q / 2)) ^ 2

/-- For every level q, the selected reciprocal cutoff is at least 64.
Square max(8,log(q)/2)≥8. This verifies the raw formula's entrance condition. -/
theorem halfConductorReciprocalCutoff_ge_sixtyFour (q : ℕ) :
    64 ≤ halfConductorReciprocalCutoff q := by
  have h := le_max_left (8 : ℝ) (Real.log q / 2)
  dsimp only [halfConductorReciprocalCutoff]
  nlinarith only [h]

/-- Under primitive GRH at q≥3 and exclusion m≠0, a non-one prime outside m
lies below the variable root at max(8,log(q)/2)². Instantiate the existing
variable-cutoff extractor, retaining its minimum with the fixed Hadamard cap. -/
theorem exists_prime_ne_one_le_selected_reciprocal_root {q m : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hm : m ≠ 0) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          variableReciprocalWitnessBound q m (halfConductorReciprocalCutoff q) (1 / 4) (29 / 10) ∧
        ¬p ∣ m ∧ χ p ≠ 1 := by
  exact
    exists_prime_ne_one_le_variable_reciprocal_root χ hq hp hGRH hm
      (halfConductorReciprocalCutoff_ge_sixtyFour q)

/-- Under primitive GRH, the selected variable root is no larger than the fixed
general Hadamard root with the same exclusion cost. Apply the proved minimum-cap
comparison and identify its rational intercept. The selected cutoff never worsens this bound. -/
theorem selected_reciprocal_root_le_fixed {q m : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    variableReciprocalWitnessBound q m (halfConductorReciprocalCutoff q) (1 / 4) (29 / 10) ≤
      ((2429 / 720 : ℝ) * Real.log q + 19171 / 400 +
          Real.sqrt
            (((2429 / 720 : ℝ) * Real.log q + 19171 / 400) ^ 2 +
              (14 / 5 : ℝ) * (∑ r ∈ m.primeFactors, Real.log r))) ^
        2 := by
  have h :=
    variableReciprocalWitnessBound_le_fixed (m := m)
      (variableReciprocalNormCap_nonneg (abs_primitiveBRe_le_direct_reciprocal hq hp hGRH)
        (abs_primitiveBRe_le_variable_reciprocal hq hp hGRH
          (halfConductorReciprocalCutoff_ge_sixtyFour q)))
  have he : (77 / 20 : ℝ) * (29 / 10) + 2941 / 80 = 19171 / 400 := by norm_num only
  rw [add_assoc ((2429 / 720 : ℝ) * Real.log q), he] at h
  exact h

/-- Under primitive GRH, log(q)≤G, G≥16 and x≥100, the logarithmic-sum norm
is at most ((101/60)G+(22/5)log(G)+23/4)sqrt(x). Pass the selected Hadamard cap
to the independent endpoint interface, then increase the remaining log(q) terms to G. -/
theorem norm_characterLogWeightedSum_le_selected_envelope {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {G x : ℝ} (hG : 16 ≤ G)
    (hlog : Real.log q ≤ G) (hx : 100 ≤ x) :
    ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ‖ ≤
      ((101 / 60 : ℝ) * G + (22 / 5) * Real.log G + 23 / 4) * Real.sqrt x := by
  have h :=
    norm_characterLogWeightedSum_le_endpoint_caps hq hp hGRH hx
      (abs_primitiveBRe_le_selected_envelope hq hp hGRH hG hlog)
      (norm_logDeriv_xi_zero_le_refined_uniform hq hp hGRH)
  have hc :
    (11 / 5 : ℝ) * ((1 / 2) * G + 2 * Real.log G) + ((2 / 3) * Real.log q + 9 / 2) / 2 +
        Real.log q / 4 +
        7 / 2 ≤
      (101 / 60 : ℝ) * G + (22 / 5) * Real.log G + 23 / 4 := by
    linarith only [hlog]
  exact h.trans (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg x))

/-- For envelope G, define (707/240)G+(77/10)log(G)+2941/80.
It is the radius coefficient produced by the generic witness extractor from
the selected-cutoff norm estimate. Its applications assume G≥16. -/
noncomputable def selectedReciprocalRadius (G : ℝ) : ℝ :=
  (707 / 240) * G + (77 / 10) * Real.log G + 2941 / 80

/-- For an envelope G and excluded integer m, define the squared positive root
using the selected radius and distinct-prime logarithmic exclusion cost.
This gives the explicit witness bound without evaluating a reciprocal finite sum. -/
noncomputable def selectedReciprocalWitnessBound (G : ℝ) (m : ℕ) : ℝ :=
  (selectedReciprocalRadius G +
      Real.sqrt
        ((selectedReciprocalRadius G) ^ 2 + (14 / 5 : ℝ) * (∑ r ∈ m.primeFactors, Real.log r))) ^
    2

/-- Under primitive GRH at q≥3, G≥16, log(q)≤G and m≠0, a non-one prime
outside m lies below the selected-envelope root. Apply the generic norm-cap
extractor and identify the rational radius. No finite certificate is used. -/
theorem exists_prime_ne_one_le_selected_envelope_root {q m : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hm : m ≠ 0) {G : ℝ}
    (hG : 16 ≤ G) (hlog : Real.log q ≤ G) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ selectedReciprocalWitnessBound G m ∧ ¬p ∣ m ∧ χ p ≠ 1 := by
  have hl := Real.log_nonneg (show 1 ≤ G by linarith only [hG])
  obtain ⟨p, hp', hb, hd, hv⟩ :=
    exists_prime_ne_one_le_norm_cap_root χ hGRH.riemann hm (F :=
      (101 / 60 : ℝ) * G + (22 / 5) * Real.log G + 23 / 4) (by linarith only [hG, hl])
      (fun _ hx ↦ norm_characterLogWeightedSum_le_selected_envelope hq hp hGRH hG hlog hx)
  have he :
    (7 / 4 : ℝ) * ((101 / 60 : ℝ) * G + (22 / 5) * Real.log G + 23 / 4) + 267 / 10 =
      selectedReciprocalRadius G := by
    dsimp only [selectedReciprocalRadius]
    ring
  rw [he] at hb
  exact ⟨p, hp', hb, hd, hv⟩

/-- For G≥1, the selected radius is at least (707/240)G+2941/80.
Use log(G)≥0. This absorbs squarefree-part and two-prime exclusion costs. -/
theorem selectedReciprocalRadius_lower_bound {G : ℝ} (hG : 1 ≤ G) :
    (707 / 240 : ℝ) * G + 2941 / 80 ≤ selectedReciprocalRadius G := by
  have hl := Real.log_nonneg hG
  dsimp only [selectedReciprocalRadius]
  linarith only [hl]

/-- For G≥1, the selected radius is nonnegative. Apply its affine lower bound.
This supplies the sign needed for root and square comparisons. -/
theorem selectedReciprocalRadius_nonneg {G : ℝ} (hG : 1 ≤ G) : 0 ≤ selectedReciprocalRadius G := by
  linarith only [selectedReciprocalRadius_lower_bound hG, hG]

/-- For G≥16, the selected radius plus 77/10 is at most the previous adaptive
radius. Compare log(G) with log(G+8) and the exact rational constants.
This certifies improvement throughout the selected explicit envelope's domain. -/
theorem selectedReciprocalRadius_le_previous {G : ℝ} (hG : 16 ≤ G) :
    selectedReciprocalRadius G + 77 / 10 ≤ adaptiveReciprocalRadius G := by
  have hl := Real.log_le_log (show 0 < G by linarith only [hG]) (show G ≤ G + 8 by linarith only)
  dsimp only [selectedReciprocalRadius, adaptiveReciprocalRadius]
  linarith only [hl]

/-- For G≥57, the selected radius is at most the preceding direct even Hadamard
radius. Use the logarithm tangent at 57 and log(57)≤6log(2).
This gives a certified sufficient comparison domain without locating the exact crossing. -/
theorem selectedReciprocalRadius_le_even_fixed {G : ℝ} (hG : 57 ≤ G) :
    selectedReciprocalRadius G ≤ (2429 / 720 : ℝ) * G + 17939 / 400 := by
  have ht :=
    Analysis.log_le_log_add_sub_div (a := (57 : ℝ)) (by norm_num only)
      (show 0 < G by linarith only [hG])
  have h57 :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 57) (by norm_num only : (57 : ℝ) ≤ 2 ^ (6 : ℕ))
  rw [Real.log_pow] at h57
  norm_num only [Nat.cast_ofNat] at h57
  dsimp only [selectedReciprocalRadius]
  linarith only [ht, h57, Real.log_two_lt_d9, hG]

/-- For 1≤G₁≤G₂, the selected radius is increasing. Apply logarithm
monotonicity and compare the positive coefficients. This validates envelope
increases after the analytic entrance without a numerical grid. -/
theorem selectedReciprocalRadius_mono {G₁ G₂ : ℝ} (hG₁ : 1 ≤ G₁) (hG : G₁ ≤ G₂) :
    selectedReciprocalRadius G₁ ≤ selectedReciprocalRadius G₂ := by
  have hl := Real.log_le_log (show 0 < G₁ by linarith only [hG₁]) hG
  dsimp only [selectedReciprocalRadius]
  linarith only [hG, hl]

/-- For 1≤G₁≤G₂ and fixed excluded m, the selected witness bound is increasing.
Use nonnegative-radius and squared-root monotonicity. This transports the
explicit envelope to any larger admissible conductor bound. -/
theorem selectedReciprocalWitnessBound_mono {G₁ G₂ : ℝ} (m : ℕ) (hG₁ : 1 ≤ G₁) (hG : G₁ ≤ G₂) :
    selectedReciprocalWitnessBound G₁ m ≤ selectedReciprocalWitnessBound G₂ m := by
  exact
    root_radius_sq_mono (selectedReciprocalRadius_nonneg hG₁) (selectedReciprocalRadius_mono hG₁ hG)
      le_rfl

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS

/-- Under GRH for a nonprincipal character at nonzero level q and G≥16 with
log(conductor)≤G, a unit-prime non-one witness lies below the selected envelope.
Apply the primitive theorem with exclusion q and transfer the value on units. -/
theorem exists_prime_ne_one_le_selected_envelope_root {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {G : ℝ} (hG : 16 ≤ G)
    (hlog : Real.log χ.conductor ≤ G) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ PaperStatements.selectedReciprocalWitnessBound G q ∧ ¬p ∣ q ∧ χ p ≠ 1 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hc := NumberTheory.three_le_conductor_of_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    PaperStatements.exists_prime_ne_one_le_selected_envelope_root χ.primitiveCharacter hc
      χ.primitiveCharacter_isPrimitive hGRH (NeZero.ne q) hG hlog
  have he := χ.primitiveCharacter_apply_of_isCoprime (hp.coprime_iff_not_dvd.mpr hd).isCoprime
  simp only [Int.cast_natCast] at he
  exact ⟨p, hp, hb, hd, fun h ↦ hv (he.trans h)⟩

/-- Under GRH for a nonprincipal character at nonzero level q, a unit-prime
non-one witness lies below the selected variable root in its conductor.
The existing minimum-based cap keeps the fixed estimate as a candidate. -/
theorem exists_prime_ne_one_le_selected_reciprocal_root {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          PaperStatements.variableReciprocalWitnessBound χ.conductor q
            (PaperStatements.halfConductorReciprocalCutoff χ.conductor) (1 / 4) (29 / 10) ∧
        ¬p ∣ q ∧ χ p ≠ 1 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hc := NumberTheory.three_le_conductor_of_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    PaperStatements.exists_prime_ne_one_le_selected_reciprocal_root χ.primitiveCharacter hc
      χ.primitiveCharacter_isPrimitive hGRH (NeZero.ne q)
  have he := χ.primitiveCharacter_apply_of_isCoprime (hp.coprime_iff_not_dvd.mpr hd).isCoprime
  simp only [Int.cast_natCast] at he
  exact ⟨p, hp, hb, hd, fun h ↦ hv (he.trans h)⟩

/-- Under GRH, a nonprincipal character trivial on a subgroup gives a unit-prime
outside its image below the selected envelope, assuming G≥16 and log(conductor)≤G.
Transfer the proved non-one value to subgroup nonmembership. -/
theorem exists_prime_outside_le_selected_envelope {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ht : ∀ u : (ZMod q)ˣ, u ∈ H → χ (u : ZMod q) = 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {G : ℝ} (hG : 16 ≤ G)
    (hlog : Real.log χ.conductor ≤ G) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        (p : ℝ) ≤ PaperStatements.selectedReciprocalWitnessBound G q ∧
        ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  obtain ⟨p, hp, hb, hd, hv⟩ := exists_prime_ne_one_le_selected_envelope_root χ hχ hGRH hG hlog
  refine ⟨p, hp, hd, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  exact hv (he ▸ ht u hu)

end PseudoPrime.LLS
