/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.DirectHadamardConductorBounds

/-! # Variable reciprocal cutoffs for conductor-sensitive witness bounds -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- At level q and reciprocal cutoff x, the real reciprocal formula with saving η
bounds the Hadamard constant by this quotient. The numerator retains the actual
principal reciprocal sum; later theorems require x ≥ 64 and the certified saving. -/
noncomputable def reciprocalHadamardCap (q : ℕ) (x η : ℝ) : ℝ :=
  ((1 / 2) * (1 - 1 / x) * (Real.log q - Real.log Real.pi) - η +
      AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum x) /
    (1 - 1 / Real.sqrt x) ^ 2

/-- For reciprocal cutoff x ≥ 64, the Hadamard quotient denominator is positive.
Use sqrt(x) > 1 and reciprocal monotonicity. This justifies division in the raw formula. -/
theorem reciprocalHadamardCap_den_pos {x : ℝ} (hx : 64 ≤ x) : 0 < (1 - 1 / Real.sqrt x) ^ 2 := by
  have hs : 1 < Real.sqrt x := Real.lt_sqrt_of_sq_lt (by linarith only [hx])
  have hi : 1 / Real.sqrt x < 1 := by simpa only [one_div] using inv_lt_one_of_one_lt₀ hs
  exact sq_pos_of_pos (sub_pos.mpr hi)

/-- Given x ≥ 64 and a real reciprocal upper formula with saving η, bound the
absolute primitive Hadamard constant by the variable quotient. Compare the real
part with the principal reciprocal sum and divide by the positive denominator. -/
theorem abs_primitiveBRe_le_reciprocalHadamardCap_of_raw {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x η : ℝ} (hx : 64 ≤ x)
    (hraw :
      (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ).re ≤
        (1 / 2) * (1 - 1 / x) * (Real.log q - Real.log Real.pi) - η -
          (1 - 1 / Real.sqrt x) ^ 2 * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ|) :
    |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| ≤ reciprocalHadamardCap q x η := by
  have hn :=
    AnalyticNumberTheory.Arithmetic.norm_characterReciprocalWeightedSum_le χ
      (show 0 < x by linarith only [hx])
  have he :=
    (abs_le.mp
        (Complex.abs_re_le_norm
          (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ))).1
  apply (le_div_iff₀ (reciprocalHadamardCap_den_pos hx)).mpr
  linarith only [hraw, hn, he]

/-- Under GRH for a primitive character of level q ≥ 3 and any x ≥ 64,
the general-saving quotient bounds its absolute Hadamard constant.
Apply the proved raw reciprocal formula; no new analytic assumption is introduced. -/
theorem abs_primitiveBRe_le_variable_reciprocal {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 3 ≤ q) (hp : χ.IsPrimitive) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x : ℝ} (hx : 64 ≤ x) :
    |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| ≤
      reciprocalHadamardCap q x (1 / 4) := by
  have hne := primitiveCharacter_ne_one_of_three_le hq hp
  exact
    abs_primitiveBRe_le_reciprocalHadamardCap_of_raw χ hx
      (LLS.primitiveReciprocalRaw (le_trans (by norm_num only : 2 ≤ 3) hq) hGRH hp hne
        (inv_ne_one.mpr hne) hx)

/-- Under GRH for a primitive even character of level q ≥ 3 and any x ≥ 64,
the even-saving quotient bounds its absolute Hadamard constant.
Retain the certified 179/200 saving for the quadratic witness application. -/
theorem abs_primitiveBRe_even_le_variable_reciprocal {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 3 ≤ q) (hp : χ.IsPrimitive) (heven : χ.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 64 ≤ x) :
    |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| ≤
      reciprocalHadamardCap q x (179 / 200) := by
  have hne := primitiveCharacter_ne_one_of_three_le hq hp
  exact
    abs_primitiveBRe_le_reciprocalHadamardCap_of_raw χ hx
      (Extensions.primitiveReciprocalRaw_even_le_neg_179_div_200
        (le_trans (by norm_num only : 2 ≤ 3) hq) hGRH hp hne heven hx)

/-- At level q, cutoff x, saving η and fixed intercept c, combine the smaller
of the fixed and variable Hadamard caps with the independent xi endpoint cap.
This is the square-root norm coefficient used by the witness extractor. -/
noncomputable def variableReciprocalNormCap (q : ℕ) (x η c : ℝ) : ℝ :=
  (11 / 5) * min ((11 / 18) * Real.log q + c) (reciprocalHadamardCap q x η) +
    ((2 / 3) * Real.log q + 9 / 2) / 2 +
    Real.log q / 4 +
    7 / 2

/-- If both the fixed and variable quantities bound the absolute Hadamard constant,
the combined norm coefficient is nonnegative. Use nonnegativity of the absolute
value and log(q). This supplies the sign needed by the root extractor. -/
theorem variableReciprocalNormCap_nonneg {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {x η c : ℝ}
    (hb : |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| ≤ (11 / 18 : ℝ) * Real.log q + c)
    (hv : |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| ≤ reciprocalHadamardCap q x η) :
    0 ≤ variableReciprocalNormCap q x η c := by
  have hm :=
    (abs_nonneg (AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ)).trans (le_min hb hv)
  dsimp only [variableReciprocalNormCap]
  linarith only [hm, Real.log_natCast_nonneg q]

/-- Under primitive GRH at q ≥ 3, two Hadamard caps give a logarithmic-sum norm
bound at every t ≥ 100. Apply the generic endpoint theorem to their minimum.
The reciprocal cutoff x is independent of the witness comparison cutoff t. -/
theorem norm_characterLogWeightedSum_le_variable_reciprocal {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x η c t : ℝ} (ht : 100 ≤ t)
    (hb : |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| ≤ (11 / 18 : ℝ) * Real.log q + c)
    (hv : |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| ≤ reciprocalHadamardCap q x η) :
    ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum t χ‖ ≤
      variableReciprocalNormCap q x η c * Real.sqrt t := by
  exact
    norm_characterLogWeightedSum_le_endpoint_caps hq hp hGRH ht (le_min hb hv)
      (norm_logDeriv_xi_zero_le_refined_uniform hq hp hGRH)

/-- Under primitive GRH, two certified Hadamard caps and nonzero exclusion m
produce a non-one prime outside m below the variable root bound.
Pass their nonnegative norm coefficient to the generic witness extractor. -/
theorem exists_prime_ne_one_le_variable_reciprocal_root_of_bounds {q m : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hm : m ≠ 0) {x η c : ℝ}
    (hb : |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| ≤ (11 / 18 : ℝ) * Real.log q + c)
    (hv : |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| ≤ reciprocalHadamardCap q x η) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          ((7 / 4 : ℝ) * variableReciprocalNormCap q x η c + 267 / 10 +
              Real.sqrt
                (((7 / 4 : ℝ) * variableReciprocalNormCap q x η c + 267 / 10) ^ 2 +
                  (14 / 5 : ℝ) * (∑ r ∈ m.primeFactors, Real.log r))) ^
            2 ∧
        ¬p ∣ m ∧ χ p ≠ 1 := by
  exact
    exists_prime_ne_one_le_norm_cap_root χ hGRH.riemann hm (variableReciprocalNormCap_nonneg hb hv)
      (fun _ ht ↦ norm_characterLogWeightedSum_le_variable_reciprocal hq hp hGRH ht hb hv)

/-- Under GRH for primitive χ at q ≥ 3, m ≠ 0 and x ≥ 64, a prime outside m
has χ(p) ≠ 1 below the variable reciprocal root. Combine the fixed general cap
and the proved variable cap, then apply the common extractor. -/
theorem exists_prime_ne_one_le_variable_reciprocal_root {q m : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hm : m ≠ 0) {x : ℝ}
    (hx : 64 ≤ x) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          ((7 / 4 : ℝ) * variableReciprocalNormCap q x (1 / 4) (29 / 10) + 267 / 10 +
              Real.sqrt
                (((7 / 4 : ℝ) * variableReciprocalNormCap q x (1 / 4) (29 / 10) + 267 / 10) ^ 2 +
                  (14 / 5 : ℝ) * (∑ r ∈ m.primeFactors, Real.log r))) ^
            2 ∧
        ¬p ∣ m ∧ χ p ≠ 1 := by
  exact
    exists_prime_ne_one_le_variable_reciprocal_root_of_bounds χ hq hp hGRH hm
      (abs_primitiveBRe_le_direct_reciprocal hq hp hGRH)
      (abs_primitiveBRe_le_variable_reciprocal hq hp hGRH hx)

/-- Under GRH for primitive even χ at q ≥ 3, m ≠ 0 and x ≥ 64, a prime outside m
has χ(p) ≠ 1 below the variable even root. Preserve evenness and the 179/200
saving when applying the common extractor. -/
theorem exists_prime_ne_one_le_even_variable_reciprocal_root {q m : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q) (hp : χ.IsPrimitive) (heven : χ.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hm : m ≠ 0) {x : ℝ}
    (hx : 64 ≤ x) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          ((7 / 4 : ℝ) * variableReciprocalNormCap q x (179 / 200) (21 / 10) + 267 / 10 +
              Real.sqrt
                (((7 / 4 : ℝ) * variableReciprocalNormCap q x (179 / 200) (21 / 10) + 267 / 10) ^
                    2 +
                  (14 / 5 : ℝ) * (∑ r ∈ m.primeFactors, Real.log r))) ^
            2 ∧
        ¬p ∣ m ∧ χ p ≠ 1 := by
  exact
    exists_prime_ne_one_le_variable_reciprocal_root_of_bounds χ hq hp hGRH hm
      (abs_primitiveBRe_even_le_direct_reciprocal hq hp heven hGRH)
      (abs_primitiveBRe_even_le_variable_reciprocal hq hp heven hGRH hx)

/-- For any level and cutoff parameters, the minimum-based norm cap is at most
the old fixed coefficient. Compare the minimum with its first argument.
This ensures choosing a reciprocal cutoff cannot worsen the norm bound. -/
theorem variableReciprocalNormCap_le_fixed (q : ℕ) (x η c : ℝ) :
    variableReciprocalNormCap q x η c ≤ (347 / 180 : ℝ) * Real.log q + (11 / 5) * c + 23 / 4 := by
  have hm := min_le_left ((11 / 18 : ℝ) * Real.log q + c) (reciprocalHadamardCap q x η)
  dsimp only [variableReciprocalNormCap]
  linarith only [hm]

/-- For conductor q, excluded integer m and reciprocal parameters, define the
squared positive root obtained from the norm coefficient and prime-factor log cost.
The expression is the upper bound in the public variable-cutoff witness theorems. -/
noncomputable def variableReciprocalWitnessBound (q m : ℕ) (x η c : ℝ) : ℝ :=
  ((7 / 4 : ℝ) * variableReciprocalNormCap q x η c + 267 / 10 +
      Real.sqrt
        (((7 / 4 : ℝ) * variableReciprocalNormCap q x η c + 267 / 10) ^ 2 +
          (14 / 5 : ℝ) * (∑ r ∈ m.primeFactors, Real.log r))) ^
    2

/-- If the variable norm coefficient is nonnegative, its witness root is at most
the fixed Hadamard root with the same exclusion cost. Combine the coefficient
comparison with monotonicity of the squared root radius. -/
theorem variableReciprocalWitnessBound_le_fixed {q m : ℕ} {x η c : ℝ}
    (hF : 0 ≤ variableReciprocalNormCap q x η c) :
    variableReciprocalWitnessBound q m x η c ≤
      ((2429 / 720 : ℝ) * Real.log q + (77 / 20) * c + 2941 / 80 +
          Real.sqrt
            (((2429 / 720 : ℝ) * Real.log q + (77 / 20) * c + 2941 / 80) ^ 2 +
              (14 / 5 : ℝ) * (∑ r ∈ m.primeFactors, Real.log r))) ^
        2 := by
  apply root_radius_sq_mono
  · linarith only [hF]
  · have h := variableReciprocalNormCap_le_fixed q x η c
    linarith only [h]
  · exact le_rfl

/-- Under RH, the even variable quotient at 100 is at most (11/18)log(q)+523/250.
Retain the principal arithmetic cap and the certified pi logarithm, without rounding
the intercept to 21/10. This certifies a strict gain at an already supported cutoff. -/
theorem reciprocalHadamardCap_hundred_even_le (q : ℕ) (hRH : RiemannHypothesis) :
    reciprocalHadamardCap q 100 (179 / 200) ≤ (11 / 18 : ℝ) * Real.log q + 523 / 250 := by
  dsimp only [reciprocalHadamardCap]
  norm_num only
  linarith only [reciprocal_hundred_le_789_div_250 hRH, Analysis.log_pi_ge_2096_div_1831]

/-- Under RH, the even norm coefficient at reciprocal cutoff 100 is at most
(347/180)log(q)+25881/2500. Compare the minimum with its variable argument.
Its intercept is 11/625 smaller than the preceding fixed even norm intercept. -/
theorem variableReciprocalNormCap_hundred_even_le (q : ℕ) (hRH : RiemannHypothesis) :
    variableReciprocalNormCap q 100 (179 / 200) (21 / 10) ≤
      (347 / 180 : ℝ) * Real.log q + 25881 / 2500 := by
  have hm :=
    min_le_right ((11 / 18 : ℝ) * Real.log q + 21 / 10) (reciprocalHadamardCap q 100 (179 / 200))
  have hc := reciprocalHadamardCap_hundred_even_le q hRH
  dsimp only [variableReciprocalNormCap]
  linarith only [hm, hc]

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS

/-- Under GRH for any nonprincipal χ of nonzero level q and cutoff x ≥ 64,
a unit-prime non-one witness lies below the variable bound in its conductor.
Exclude the original level and transfer the primitive value on units. -/
theorem exists_prime_ne_one_le_variable_reciprocal_root {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 64 ≤ x) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ PaperStatements.variableReciprocalWitnessBound χ.conductor q x (1 / 4) (29 / 10) ∧
        ¬p ∣ q ∧ χ p ≠ 1 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hc := NumberTheory.three_le_conductor_of_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    PaperStatements.exists_prime_ne_one_le_variable_reciprocal_root χ.primitiveCharacter hc
      χ.primitiveCharacter_isPrimitive hGRH (NeZero.ne q) hx
  have he := χ.primitiveCharacter_apply_of_isCoprime (hp.coprime_iff_not_dvd.mpr hd).isCoprime
  simp only [Int.cast_natCast] at he
  exact ⟨p, hp, hb, hd, fun h ↦ hv (he.trans h)⟩

/-- Under GRH for any nonprincipal even χ of nonzero level q and x ≥ 64,
a unit-prime non-one witness lies below the variable even conductor bound.
Preserve evenness under primitivization and transfer the value on units. -/
theorem exists_prime_ne_one_le_even_variable_reciprocal_root {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (heven : χ.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 64 ≤ x) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          PaperStatements.variableReciprocalWitnessBound χ.conductor q x (179 / 200) (21 / 10) ∧
        ¬p ∣ q ∧ χ p ≠ 1 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hc := NumberTheory.three_le_conductor_of_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    PaperStatements.exists_prime_ne_one_le_even_variable_reciprocal_root χ.primitiveCharacter hc
      χ.primitiveCharacter_isPrimitive ((NumberTheory.primitiveCharacter_even_iff χ).mpr heven) hGRH
      (NeZero.ne q) hx
  have he := χ.primitiveCharacter_apply_of_isCoprime (hp.coprime_iff_not_dvd.mpr hd).isCoprime
  simp only [Int.cast_natCast] at he
  exact ⟨p, hp, hb, hd, fun h ↦ hv (he.trans h)⟩

end PseudoPrime.LLS
