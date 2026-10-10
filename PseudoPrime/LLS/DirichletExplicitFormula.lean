/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveFunctionalEquation
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.TrivialZeroMultiplicity
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.TrivialZeroSeriesLimit
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogResidueLedger
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GenericLogResidues
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveGenericHorizontalEdge

/-! Level-scaled xi endpoint identities for the general-character LLS explicit formulas. -/

@[expose] public section

namespace PseudoPrime.LLS

/-- A primitive character at level at least three is nonprincipal: the principal
character has conductor one, whereas primitivity makes the conductor equal the level. -/
theorem primitiveCharacter_ne_one_of_three_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 3 ≤ q) (hp : χ.IsPrimitive) : χ ≠ 1 := by
  intro h
  have he : q = 1 := hp.symm.trans (h ▸ DirichletCharacter.conductor_one)
  exact (Nat.not_le_of_lt (of_decide_eq_true rfl : 1 < 3)) (he ▸ hq)

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For a primitive nonprincipal character of nonzero modulus, the level-scaled
xi logarithmic derivative at zero equals the completed L-function logarithmic derivative
plus `log q / 2`. Differentiate the product; nonvanishing of both factors justifies
addition of logarithmic derivatives. This converts completed endpoints to the paper's xi. -/
theorem logDeriv_xi_zero_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) :
    logDeriv (PaperStatements.xi χ) 0 = Complex.log q / 2 + logDeriv χ.completedLFunction 0 := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hpow := ((hasDerivAt_id (0 : ℂ)).div_const 2).const_cpow (c := (q : ℂ)) (Or.inl hq)
  simp only [id_eq] at hpow
  have hp0 : (q : ℂ) ^ ((0 : ℂ) / 2) ≠ 0 := by
    simp only [zero_div, Complex.cpow_zero, ne_eq, one_ne_zero, not_false_eq_true]
  unfold PaperStatements.xi
  rw [logDeriv_fun_mul 0 hp0 (dirichletCompletedLFunction_zero_ne_zero_of_primitive hp hne)
      hpow.differentiableAt (DirichletCharacter.differentiable_completedLFunction hne 0)]
  congr 1
  rw [logDeriv_apply, hpow.deriv]
  simp only [zero_div, Complex.cpow_zero, one_mul, div_one]
  ring

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- Under GRH, the real logarithmic derivative of the paper's xi at zero is
the negative absolute Hadamard constant. The level normalization cancels the half-log term. -/
theorem re_logDeriv_xi_zero_eq_neg_abs_BRe {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (logDeriv (PaperStatements.xi χ) 0).re = -|primitiveBRe χ| := by
  have hne := primitiveCharacter_ne_one_of_three_le hq hp
  have hq2 : 2 ≤ q := (of_decide_eq_true rfl : 2 ≤ 3).trans hq
  have hB :=
    completedLFunction_logDeriv_zero_re_eq_neg_abs_BRe_sub_half_log hq2 hGRH hp hne
      (inv_ne_one.mpr hne)
  rw [logDeriv_xi_zero_eq hp hne, ← Complex.ofReal_natCast, ←
    Complex.ofReal_log (Nat.cast_nonneg q), ← Complex.ofReal_ofNat 2, ← Complex.ofReal_div,
    Complex.add_re, Complex.ofReal_re, hB]
  ring

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For a primitive character of level at least three under GRH, the real
logarithmic derivative of its inverse character's level-scaled xi at zero is
`-|primitiveBRe χ|`. Apply the xi endpoint identity to the primitive inverse character
and use equality of the inverse Hadamard constants. This supplies the second endpoint
in the real reciprocal formula. -/
theorem re_logDeriv_xi_inv_zero_eq_neg_abs_BRe {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (logDeriv (PaperStatements.xi χ⁻¹) 0).re = -|primitiveBRe χ| :=
  Eq.trans (re_logDeriv_xi_zero_eq_neg_abs_BRe hq (DirichletCharacter.isPrimitive_inv hp) hGRH)
    (congrArg (fun b : ℝ ↦ -|b|)
      (primitiveBRe_inv_eq (primitiveCharacter_ne_one_of_three_le hq hp)))

/-- Taking real parts preserves the bounds on two complex error coefficients.
If the endpoint has real part `-b`, its logarithmic term supplies `b * log x`. -/
theorem real_log_formula_of_complex {S D : ℂ} {b x c : ℝ} (hD : D.re = -b)
    (h :
      ∃ θ₁ θ₂ : ℂ,
        ‖θ₁‖ ≤ 1 ∧
          ‖θ₂‖ ≤ 1 ∧
          S = (b : ℂ) * (2 * θ₁ * (Real.sqrt x : ℂ) + 2 * θ₂) - D * (Real.log x : ℂ) + (c : ℂ)) :
    ∃ θ₁ θ₂ : ℝ,
      |θ₁| ≤ 1 ∧ |θ₂| ≤ 1 ∧ S.re = b * (2 * θ₁ * Real.sqrt x + 2 * θ₂ + Real.log x) + c := by
  obtain ⟨θ₁, θ₂, h₁, h₂, he⟩ := h
  refine
    ⟨θ₁.re, θ₂.re, (Complex.abs_re_le_norm _).trans h₁, (Complex.abs_re_le_norm _).trans h₂, ?_⟩
  rw [he]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, sub_zero, hD]
  ring

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For a primitive level at least three under GRH, the complex part of Lemma 2.2
implies its real-part consequence. The two theta values are the real parts of the
complex errors and need no separate contour estimate. -/
theorem characterLogWeightedSum_real_of_complex {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 3 ≤ q) (hp : χ.IsPrimitive) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (x : ℝ)
    (h :
      ∃ θ₁ θ₂ : ℂ,
        ‖θ₁‖ ≤ 1 ∧
          ‖θ₂‖ ≤ 1 ∧
          AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ =
            ((|primitiveBRe χ| : ℝ) : ℂ) * (2 * θ₁ * (Real.sqrt x : ℂ) + 2 * θ₂) -
                logDeriv (PaperStatements.xi χ) 0 * (Real.log x : ℂ) +
              ((Real.log ((q : ℝ) / Real.pi) * Real.log x / 2 + PaperStatements.logCorrection χ x :
                  ℝ) :
                ℂ)) :
    ∃ θ₁ θ₂ : ℝ,
      |θ₁| ≤ 1 ∧
        |θ₂| ≤ 1 ∧
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ).re =
          |primitiveBRe χ| * (2 * θ₁ * Real.sqrt x + 2 * θ₂ + Real.log x) +
            Real.log ((q : ℝ) / Real.pi) * Real.log x / 2 +
            PaperStatements.logCorrection χ x := by
  simpa only [add_assoc] using
    real_log_formula_of_complex (re_logDeriv_xi_zero_eq_neg_abs_BRe hq hp hGRH) h

/-- The inverse factor in Lemma 2.3 has a strictly positive denominator for `x > 1`
and `|theta| ≤ 1`. Its lower bound is `(1 - 1/sqrt x)^2`. -/
theorem reciprocalErrorFactor_pos {x θ : ℝ} (hx : 1 < x) (hθ : |θ| ≤ 1) :
    0 < 1 + 2 * θ / Real.sqrt x + 1 / x := by
  have hx0 : 0 ≤ x := le_of_lt (lt_trans zero_lt_one hx)
  have hs : 1 < Real.sqrt x := by simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt zero_le_one hx
  have ht : 1 / Real.sqrt x < 1 := (div_lt_one (lt_trans zero_lt_one hs)).mpr hs
  have hsq : (1 / Real.sqrt x) ^ 2 = 1 / x := by rw [one_div, inv_pow, Real.sq_sqrt hx0, one_div]
  have hp := sq_pos_of_ne_zero (ne_of_gt (sub_pos.mpr ht))
  have hθlow := (abs_le.mp hθ).1
  have hθterm : 0 ≤ 2 * (θ + 1) / Real.sqrt x :=
    div_nonneg (mul_nonneg (by norm_num only) (by linarith only [hθlow])) (Real.sqrt_nonneg x)
  simp only [div_eq_mul_inv, one_mul] at hp hθterm hsq ⊢
  nlinarith only [hp, hθterm, hsq]

/-- The complex reciprocal formula gives its real inverse-factor consequence.
Equal endpoint real parts supply `b + b/x`, and `x > 1` prevents a zero denominator. -/
theorem real_reciprocal_formula_of_complex {S D E : ℂ} {b x c : ℝ} (hx : 1 < x) (hD : D.re = -b)
    (hE : E.re = -b)
    (h :
      ∃ θ : ℂ,
        ‖θ‖ ≤ 1 ∧ -E - (1 / (x : ℂ)) * D + 2 * θ / (Real.sqrt x : ℂ) * (b : ℂ) = (c : ℂ) - S) :
    ∃ θ : ℝ, |θ| ≤ 1 ∧ b = (1 + 2 * θ / Real.sqrt x + 1 / x)⁻¹ * (c - S.re) := by
  obtain ⟨θ, hθ, he⟩ := h
  have hr := congrArg Complex.re he
  simp only [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.add_re, Complex.sub_re, Complex.neg_re,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
    Complex.im_ofNat, mul_zero, zero_mul, sub_zero, add_zero, one_mul, hD, hE] at hr
  have hθre := (Complex.abs_re_le_norm θ).trans hθ
  have hc := reciprocalErrorFactor_pos hx hθre
  refine ⟨θ.re, hθre, ?_⟩
  have hreal : (1 + 2 * θ.re / Real.sqrt x + 1 / x) * b = c - S.re := by
    simp only [div_eq_mul_inv]
    nlinarith only [hr]
  rw [← hreal, inv_mul_cancel_left₀ hc.ne']

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For a primitive level at least three under GRH, the complex part of Lemma 2.3
implies its real inverse-factor consequence. The endpoint identities apply to both
the character and its inverse; the denominator is strictly positive for `x > 1`. -/
theorem characterReciprocalWeightedSum_real_of_complex {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 < x)
    (h :
      ∃ θ : ℂ,
        ‖θ‖ ≤ 1 ∧
          -logDeriv (PaperStatements.xi χ⁻¹) 0 - (1 / (x : ℂ)) * logDeriv (PaperStatements.xi χ) 0 +
              2 * θ / (Real.sqrt x : ℂ) * ((|primitiveBRe χ| : ℝ) : ℂ) =
            ((1 / 2 * (1 - 1 / x) * Real.log ((q : ℝ) / Real.pi) +
                    PaperStatements.reciprocalCorrection χ x :
                  ℝ) :
                ℂ) -
              AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ) :
    ∃ θ : ℝ,
      |θ| ≤ 1 ∧
        |primitiveBRe χ| =
          (1 + 2 * θ / Real.sqrt x + 1 / x)⁻¹ *
            (1 / 2 * (1 - 1 / x) * Real.log ((q : ℝ) / Real.pi) -
                (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ).re +
              PaperStatements.reciprocalCorrection χ x) := by
  obtain ⟨θ, hθ, he⟩ :=
    real_reciprocal_formula_of_complex hx (re_logDeriv_xi_zero_eq_neg_abs_BRe hq hp hGRH)
      (re_logDeriv_xi_inv_zero_eq_neg_abs_BRe hq hp hGRH) h
  refine ⟨θ, hθ, he.trans ?_⟩
  congr 1
  ring

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For an even primitive nonprincipal character and `x > 0`, evaluate the
logarithmic residue at zero as the negative derivative of the completed logarithmic
derivative, its logarithmic endpoint term, and the explicit even gamma correction.
The canonical local factor supplies the trigamma constant, and the cubic Mellin pole
supplies the quadratic logarithm. This exact endpoint identity does not require GRH. -/
theorem log_residue_zero_even_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (he : χ.Even) {x : ℝ} (hx : 0 < x) :
    dirichletLogResidueAt hne x 0 =
      -deriv (logDeriv χ.completedLFunction) 0 -
          logDeriv χ.completedLFunction 0 * (Real.log x : ℂ) +
        ((Real.pi ^ 2 / 24 - (Real.log Real.pi + Real.eulerMascheroniConstant) / 2 * Real.log x -
              (Real.log x) ^ 2 / 2 :
            ℝ) :
          ℂ) := by
  rw [dirichletLogResidueAt_zero_of_even hne x he,
    iteratedDeriv_two_dirichletLogEvenZeroRegularization_zero_eq hp hne hx,
    deriv_logDeriv_dirichletEvenZeroLocalFactor_zero hp hne,
    logDeriv_dirichletEvenZeroLocalFactor_zero hp hne, ← Complex.ofReal_log hx.le, ←
    Complex.ofReal_log Real.pi_nonneg]
  simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_pow, Complex.ofReal_ofNat]
  ring

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For an odd character, the gamma logarithmic derivative at zero is the
explicit complex digamma special value. This retains the whole complex
constant needed by the exact logarithmic and reciprocal residue formulas. -/
theorem logDeriv_gammaFactor_zero_odd_eq {q : ℕ} {χ : DirichletCharacter ℂ q} (ho : χ.Odd) :
    logDeriv (DirichletCharacter.gammaFactor χ) 0 =
      -Complex.log (Real.pi : ℂ) / 2 - Complex.log 2 - (Real.eulerMascheroniConstant : ℂ) / 2 := by
  rw [logDeriv_gammaFactor_eq_of_odd_of_half_ne_neg_nat ho
      (by simpa only [zero_add] using AnalyticNumberTheory.Gamma.half_ne_neg_nat),
    zero_add, Complex.digamma_one_half]
  ring

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For an odd primitive nonprincipal character and `x > 0`, evaluate the
logarithmic residue at zero as the completed logarithmic derivative endpoint and its
derivative, plus the explicit odd gamma correction. Differentiate the Mellin
regularization and insert the digamma and trigamma special values. This retains the
complete complex endpoint needed by the logarithmic explicit formula without GRH. -/
theorem log_residue_zero_odd_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (ho : χ.Odd) {x : ℝ} (hx : 0 < x) :
    dirichletLogResidueAt hne x 0 =
      -deriv (logDeriv χ.completedLFunction) 0 -
          logDeriv χ.completedLFunction 0 * (Real.log x : ℂ) +
        ((Real.pi ^ 2 / 8 -
              (Real.log Real.pi / 2 + Real.log 2 + Real.eulerMascheroniConstant / 2) * Real.log x :
            ℝ) :
          ℂ) := by
  have hbridge :
    logDeriv χ.LFunction 0 =
      logDeriv χ.completedLFunction 0 - logDeriv (DirichletCharacter.gammaFactor χ) 0 :=
    (eventuallyEq_logDeriv_LFunction_zero_of_odd hp hne ho).self_of_nhds
  have hl2 : Complex.log 2 = (Real.log 2 : ℂ) := by
    simpa only [Complex.ofReal_ofNat] using (Complex.ofReal_log (zero_le_two : (0 : ℝ) ≤ 2)).symm
  rw [dirichletLogResidueAt_zero_of_odd hne x ho,
    deriv_dirichletLogMellinZeroRegularization_zero_of_odd_eq hp hne ho hx,
    deriv_logDeriv_LFunction_zero_of_odd hp hne ho, hbridge, logDeriv_gammaFactor_zero_odd_eq ho, ←
    Complex.ofReal_log hx.le, ← Complex.ofReal_log Real.pi_nonneg, hl2]
  simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_pow, Complex.ofReal_ofNat]
  ring

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- After subtracting the origin residue and the exact trivial-zero ledger,
the logarithmic residue sum has norm at most `2*sqrt x*|Re B|` under GRH.
Both Mellin points lie in the rectangle; its remaining gamma-regular zeros
are controlled by the completed finite-subset estimate. -/
theorem norm_log_residue_sum_sub_trivial_le {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (z w : ℂ)
    (h0 : (0 : ℂ) ∈ dirichletLFunctionSingularitiesInRectangle χ hne z w)
    (h1 : (1 : ℂ) ∈ dirichletLFunctionSingularitiesInRectangle χ hne z w) :
    ‖(∑ ρ ∈ dirichletLFunctionSingularitiesInRectangle χ hne z w, dirichletLogResidueAt hne x ρ) -
          dirichletLogResidueAt hne x 0 -
          (∑
            ρ ∈
              (dirichletLFunctionZerosInRectangle χ hne z w).filter
                (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
            dirichletLFunctionLogZeroContribution x χ ρ)‖ ≤
      2 * Real.sqrt x * |primitiveBRe χ| := by
  classical
  let E := ((dirichletLFunctionSingularitiesInRectangle χ hne z w).erase 1).erase 0
  have he :
    (∑ ρ ∈ E, dirichletLogResidueAt hne x ρ) =
      ∑ ρ ∈ E, dirichletLFunctionLogZeroContribution x χ ρ := by
    refine Finset.sum_congr rfl ?_
    intro ρ hρ
    exact
      dirichletLogResidueAt_zero_ne_one hne x (Finset.mem_erase.mp hρ).1
        (Finset.mem_erase.mp (Finset.mem_erase.mp hρ).2).1
  have hs :=
    Finset.sum_filter_add_sum_filter_not E (fun ρ : ℂ => DirichletCharacter.gammaFactor χ ρ = 0)
      (dirichletLFunctionLogZeroContribution x χ)
  have ht := erased_gammaZeros_eq_trivialZeroFilter hne z w
  have hb :=
    norm_sum_logZeroContribution_of_gamma_ne_zero_le hq hGRH hp hne hinv hx
      (E.filter (fun ρ => ¬DirichletCharacter.gammaFactor χ ρ = 0))
      (fun ρ hρ => (Finset.mem_filter.mp hρ).2)
  have hid :
    (∑ ρ ∈ dirichletLFunctionSingularitiesInRectangle χ hne z w, dirichletLogResidueAt hne x ρ) -
        dirichletLogResidueAt hne x 0 -
        (∑
          ρ ∈
            (dirichletLFunctionZerosInRectangle χ hne z w).filter
              (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
          dirichletLFunctionLogZeroContribution x χ ρ) =
      ∑ ρ ∈ E.filter (fun ρ => ¬DirichletCharacter.gammaFactor χ ρ = 0),
        dirichletLFunctionLogZeroContribution x χ ρ := by
    rw [dirichletSplitLogSingularitySum x hne h1 h0, dirichletLogResidueAt_one hne x, zero_add, he,
      ← hs, ht]
    ring
  rw [hid]
  exact hb

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For a fixed expanding left edge, a height-independent exact trivial sum
passes through the generic contour limit. Under GRH and `x > 1`, the weighted
sum minus the left integral and origin residue retains the completed-zero norm bound. -/
theorem norm_logWeightedSum_sub_left_sub_origin_sub_trivial_le {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 < x) (m : ℕ) (hm : 1 ≤ m)
    (T : ℂ)
    (hT :
      ∀ k : ℕ,
        (∑
            ρ ∈
              (dirichletLFunctionZerosInRectangle χ hne
                    (primitiveHeightSeqLowerCorner hq hGRH hp hne hinv (2 * m) k)
                    (primitiveHeightSeqUpperCorner hq hGRH hp hne hinv k)).filter
                (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
            dirichletLFunctionLogZeroContribution x χ ρ) =
          T) :
    ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ -
          (((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
            (∫ t : ℝ,
              dirichletLogContourKernel x χ
                (((primitiveReciprocalLeftRe (2 * m) : ℝ) : ℂ) + (t : ℂ) * Complex.I)) -
          dirichletLogResidueAt hne x 0 -
          T‖ ≤
      2 * Real.sqrt x * |primitiveBRe χ| := by
  have hA : 2 ≤ 2 * m := Nat.mul_le_mul_left 2 hm
  have ht :=
    tendsto_normalized_dirichletLogBoundary_heightSeq_of_grh hq hGRH hp hne hinv hx.le (2 * m) hA
  have hn := ((ht.sub_const (dirichletLogResidueAt hne x 0)).sub_const T).norm
  simp only [← Complex.ofReal_inv] at hn
  refine le_of_tendsto hn ?_
  filter_upwards with k
  rw [dirichletLogFiniteContourIdentity_heightSeq_normalized hq hGRH hp hne hinv
      (zero_lt_one.trans hx) (2 * m) k hA]
  obtain ⟨h0, h1⟩ :=
    primitiveReciprocalMellinPoints_mem_singularities_heightSeq hq hGRH hp hne hinv (2 * m) k hA
  have hb :=
    norm_log_residue_sum_sub_trivial_le hq hGRH hp hne hinv (zero_lt_one.trans hx)
      (primitiveHeightSeqLowerCorner hq hGRH hp hne hinv (2 * m) k)
      (primitiveHeightSeqUpperCorner hq hGRH hp hne hinv k) h0 h1
  rw [hT k] at hb
  exact hb

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- An exact convergent family of trivial-zero sums yields the full complex
logarithmic formula error bound under GRH. The fixed-height limit is followed
by the expanding-left-edge limit, whose integral vanishes for `x > 1`. -/
theorem norm_logWeightedSum_sub_origin_sub_trivial_le {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 < x) (T : ℕ → ℂ) (L : ℂ)
    (hT :
      ∀ m : ℕ,
        1 ≤ m →
          ∀ k : ℕ,
            (∑
                ρ ∈
                  (dirichletLFunctionZerosInRectangle χ hne
                        (primitiveHeightSeqLowerCorner hq hGRH hp hne hinv (2 * m) k)
                        (primitiveHeightSeqUpperCorner hq hGRH hp hne hinv k)).filter
                    (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
                dirichletLFunctionLogZeroContribution x χ ρ) =
              T m)
    (hL : Filter.Tendsto T Filter.atTop (nhds L)) :
    ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ - dirichletLogResidueAt hne x 0 -
          L‖ ≤
      2 * Real.sqrt x * |primitiveBRe χ| := by
  have hA : Filter.Tendsto (fun m : ℕ => 2 * m) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono
      (fun m => by
        simpa only [one_mul, id_eq] using (Nat.mul_le_mul_right m (of_decide_eq_true rfl : 1 ≤ 2)))
      Filter.tendsto_id
  have hleft :=
    (tendsto_dirichletLogContourKernel_leftVertical_integral_atTop hp hne hinv hx).comp hA
  have hS :
    Filter.Tendsto (fun _ : ℕ => AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ)
      Filter.atTop (nhds (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ)) :=
    tendsto_const_nhds
  have ht :=
    (((hS.sub (hleft.const_mul (((2 * Real.pi)⁻¹ : ℝ) : ℂ))).sub_const
            (dirichletLogResidueAt hne x 0)).sub
        hL).norm
  simp only [mul_zero, sub_zero] at ht
  refine le_of_tendsto ht ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  exact
    norm_logWeightedSum_sub_left_sub_origin_sub_trivial_le hq hGRH hp hne hinv hx m hm (T m)
      (hT m hm)

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For an even primitive nonprincipal character under GRH, the complete
logarithmic sum with its origin and even correction series removed has the
sharp nontrivial-zero norm bound. Both contour limits retain the exact series. -/
theorem norm_even_logWeightedSum_sub_origin_add_series_le {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (he : χ.Even) {x : ℝ} (hx : 1 < x) :
    ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ - dirichletLogResidueAt hne x 0 +
          ((∑' j : ℕ, x⁻¹ ^ (2 * (j + 1)) / ((2 * (j + 1) : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)‖ ≤
      2 * Real.sqrt x * |primitiveBRe χ| := by
  classical
  let T := fun m : ℕ =>
    ∑
      ρ ∈
        (dirichletLFunctionZerosInRectangle χ hne
              (primitiveHeightSeqLowerCorner hq hGRH hp hne hinv (2 * m) 0)
              (primitiveHeightSeqUpperCorner hq hGRH hp hne hinv 0)).filter
          (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
      dirichletLFunctionLogZeroContribution x χ ρ
  have hT :
    ∀ m : ℕ,
      1 ≤ m →
        ∀ k : ℕ,
          (∑
              ρ ∈
                (dirichletLFunctionZerosInRectangle χ hne
                      (primitiveHeightSeqLowerCorner hq hGRH hp hne hinv (2 * m) k)
                      (primitiveHeightSeqUpperCorner hq hGRH hp hne hinv k)).filter
                  (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
              dirichletLFunctionLogZeroContribution x χ ρ) =
            T m := by
    intro m hm k
    exact
      (sum_even_log_trivialZeros_primitiveRectangle_eq hq hGRH hp hne hinv he x m k hm).trans
        (sum_even_log_trivialZeros_primitiveRectangle_eq hq hGRH hp hne hinv he x m 0 hm).symm
  have hb :=
    norm_logWeightedSum_sub_origin_sub_trivial_le hq hGRH hp hne hinv hx T _ hT
      (tendsto_sum_even_log_trivialZeros_primitiveRectangle hq hGRH hp hne hinv he hx (fun _ => 0))
  simpa only [sub_neg_eq_add] using hb

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- The odd primitive-character logarithmic formula keeps the entire odd
correction series. Height and left-edge limits transfer the finite completed
zero bound to the full weighted sum under GRH and `x > 1`. -/
theorem norm_odd_logWeightedSum_sub_origin_add_series_le {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (ho : χ.Odd) {x : ℝ} (hx : 1 < x) :
    ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ - dirichletLogResidueAt hne x 0 +
          ((∑' j : ℕ, x⁻¹ ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)‖ ≤
      2 * Real.sqrt x * |primitiveBRe χ| := by
  classical
  let T := fun m : ℕ =>
    ∑
      ρ ∈
        (dirichletLFunctionZerosInRectangle χ hne
              (primitiveHeightSeqLowerCorner hq hGRH hp hne hinv (2 * m) 0)
              (primitiveHeightSeqUpperCorner hq hGRH hp hne hinv 0)).filter
          (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
      dirichletLFunctionLogZeroContribution x χ ρ
  have hT :
    ∀ m : ℕ,
      1 ≤ m →
        ∀ k : ℕ,
          (∑
              ρ ∈
                (dirichletLFunctionZerosInRectangle χ hne
                      (primitiveHeightSeqLowerCorner hq hGRH hp hne hinv (2 * m) k)
                      (primitiveHeightSeqUpperCorner hq hGRH hp hne hinv k)).filter
                  (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
              dirichletLFunctionLogZeroContribution x χ ρ) =
            T m := by
    intro m hm k
    exact
      (sum_odd_log_trivialZeros_primitiveRectangle_eq hq hGRH hp hne hinv ho x m k hm).trans
        (sum_odd_log_trivialZeros_primitiveRectangle_eq hq hGRH hp hne hinv ho x m 0 hm).symm
  have hb :=
    norm_logWeightedSum_sub_origin_sub_trivial_le hq hGRH hp hne hinv hx T _ hT
      (tendsto_sum_odd_log_trivialZeros_primitiveRectangle hq hGRH hp hne hinv ho hx (fun _ => 0))
  simpa only [sub_neg_eq_add] using hb

/-- The natural inverse-power logarithmic series equals the paper's denominator
convention. The equality uses totalized inverses, so no extra restrictions
on the real base or natural exponent family are needed. -/
theorem log_inversePower_nat_series_eq (x : ℝ) (f : ℕ → ℕ) :
    (∑' j : ℕ, x⁻¹ ^ (f j) / ((f j : ℕ) : ℝ) ^ 2) =
      ∑' j : ℕ, 1 / (x ^ (f j) * ((f j : ℕ) : ℝ) ^ 2) := by
  apply tsum_congr
  intro j
  simp only [inv_pow, div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

/-- A complex quantity of norm at most a real bound is that bound times a
coefficient of norm at most one. The zero-bound case gives the zero quantity;
otherwise division by the positive bound produces the paper's theta parameter. -/
theorem exists_complex_theta_mul_of_norm_le {y : ℂ} {c : ℝ} (h : ‖y‖ ≤ c) :
    ∃ θ : ℂ, ‖θ‖ ≤ 1 ∧ y = θ * (c : ℂ) := by
  have hc0 : 0 ≤ c := (norm_nonneg y).trans h
  by_cases hc : c = 0
  · have hy : y = 0 := norm_eq_zero.mp (le_antisymm (hc ▸ h) (norm_nonneg y))
    refine ⟨0, ?_, ?_⟩
    · simp only [norm_zero, zero_le_one]
    · rw [hy, zero_mul]
  · have hcp : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hc)
    refine ⟨y / (c : ℂ), ?_, ?_⟩
    · simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcp]
      exact (div_le_one hcp).mpr h
    · exact (div_mul_cancel₀ y (Complex.ofReal_ne_zero.mpr hc)).symm

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- The exact logarithmic formula error relative to the paper's level-scaled
xi and full parity correction is bounded by `2*(sqrt x+1)*|Re B|` under GRH.
The trivial-zero limits and origin derivative estimate preserve both complex terms. -/
theorem norm_characterLogWeightedSum_error_le {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ +
            logDeriv (PaperStatements.xi χ) 0 * (Real.log x : ℂ) -
          ((Real.log ((q : ℝ) / Real.pi) * Real.log x / 2 + PaperStatements.logCorrection χ x : ℝ) :
            ℂ)‖ ≤
      2 * (Real.sqrt x + 1) * |primitiveBRe χ| := by
  have hne := primitiveCharacter_ne_one_of_three_le hq hp
  have hinv : χ⁻¹ ≠ 1 := inv_ne_one.mpr hne
  have hq2 : 2 ≤ q := (of_decide_eq_true rfl : 2 ≤ 3).trans hq
  have hd := norm_deriv_logDeriv_completedLFunction_zero_le_two_mul_zeroMass hGRH hp hne hinv hq2
  rw [← abs_primitiveBRe_eq_zeroMass hq2 hGRH hp hne hinv] at hd
  have hxi := logDeriv_xi_zero_eq hp hne
  have hlq : Complex.log (q : ℂ) = (Real.log (q : ℝ) : ℂ) :=
    (Complex.ofReal_log (Nat.cast_nonneg q)).symm
  have hlqp := Real.log_div (Nat.cast_ne_zero.mpr (NeZero.ne q) : (q : ℝ) ≠ 0) Real.pi_ne_zero
  let D := deriv (logDeriv χ.completedLFunction) 0
  let y :=
    AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ +
        logDeriv (PaperStatements.xi χ) 0 * (Real.log x : ℂ) -
      ((Real.log ((q : ℝ) / Real.pi) * Real.log x / 2 + PaperStatements.logCorrection χ x : ℝ) : ℂ)
  have hE : ∃ E : ℂ, ‖E‖ ≤ 2 * Real.sqrt x * |primitiveBRe χ| ∧ y = E - D := by
    rcases χ.even_or_odd with he | ho
    · let t := ∑' j : ℕ, x⁻¹ ^ (2 * (j + 1)) / ((2 * (j + 1) : ℕ) : ℝ) ^ 2
      refine ⟨_, norm_even_logWeightedSum_sub_origin_add_series_le hq2 hGRH hp hne hinv he hx, ?_⟩
      have ht : t = ∑' j : ℕ, 1 / (x ^ (2 * (j + 1)) * (2 * ((j : ℝ) + 1)) ^ 2) := by
        rw [show t = _ from log_inversePower_nat_series_eq x (fun j => 2 * (j + 1))]
        apply tsum_congr
        intro j
        simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      dsimp only [y, D]
      rw [log_residue_zero_even_eq hp hne he (zero_lt_one.trans hx), hxi, hlq,
        PaperStatements.logCorrection, ite_eq_left (show χ (-1) = 1 from he),
        PaperStatements.logCorrectionEven, ← ht, hlqp]
      simp only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_mul,
        Complex.ofReal_pow, Complex.ofReal_ofNat]
      ring
    · let t := ∑' j : ℕ, x⁻¹ ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) ^ 2
      refine ⟨_, norm_odd_logWeightedSum_sub_origin_add_series_le hq2 hGRH hp hne hinv ho hx, ?_⟩
      have ht : t = ∑' j : ℕ, 1 / (x ^ (2 * j + 1) * (2 * (j : ℝ) + 1) ^ 2) := by
        rw [show t = _ from log_inversePower_nat_series_eq x (fun j => 2 * j + 1)]
        apply tsum_congr
        intro j
        simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      dsimp only [y, D]
      rw [log_residue_zero_odd_eq hp hne ho (zero_lt_one.trans hx), hxi, hlq,
        PaperStatements.logCorrection, ite_eq_right (show χ (-1) ≠ 1 from ho.not_even),
        PaperStatements.logCorrectionOdd, ← ht, hlqp]
      simp only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_mul,
        Complex.ofReal_pow, Complex.ofReal_ofNat]
      ring
  obtain ⟨E, hb, hy⟩ := hE
  change ‖y‖ ≤ _
  rw [hy]
  calc
    ‖E - D‖ ≤ ‖E‖ + ‖D‖ := norm_sub_le E D
    _ ≤ 2 * Real.sqrt x * |primitiveBRe χ| + 2 * |primitiveBRe χ| := add_le_add hb hd
    _ = 2 * (Real.sqrt x + 1) * |primitiveBRe χ| := by ring

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- Under GRH, a primitive character of level at least three satisfies the full
complex logarithmic formula of Lemma 2.2 for `x > 1`. The norm estimate supplies
two bounded theta coefficients without adding analytic assumptions. -/
theorem characterLogWeightedSum_complex_formula {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    ∃ θ₁ θ₂ : ℂ,
      ‖θ₁‖ ≤ 1 ∧
        ‖θ₂‖ ≤ 1 ∧
        AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ =
          ((|primitiveBRe χ| : ℝ) : ℂ) * (2 * θ₁ * (Real.sqrt x : ℂ) + 2 * θ₂) -
              logDeriv (PaperStatements.xi χ) 0 * (Real.log x : ℂ) +
            ((Real.log ((q : ℝ) / Real.pi) * Real.log x / 2 + PaperStatements.logCorrection χ x :
                ℝ) :
              ℂ) := by
  obtain ⟨θ, hθ, he⟩ :=
    exists_complex_theta_mul_of_norm_le (norm_characterLogWeightedSum_error_le hq hp hGRH hx)
  refine ⟨θ, θ, hθ, hθ, ?_⟩
  simp only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_ofNat,
    Complex.ofReal_one] at he ⊢
  linear_combination he

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For a primitive nonprincipal character of level at least two under GRH,
`x > 0`, and a rectangle containing the Mellin points zero and one, subtract both
endpoint residues and the exact nonzero trivial-zero ledger from the reciprocal residue
sum. The remaining norm is at most `2*|primitiveBRe χ|/sqrt x`. Split off the gamma-zero
terms and apply the completed finite-subset bound to the remainder. This estimate is
uniform in the rectangle and is preserved by the contour limits. -/
theorem norm_reciprocal_residue_sum_sub_trivial_le {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (z w : ℂ)
    (h0 : (0 : ℂ) ∈ dirichletLFunctionSingularitiesInRectangle χ hne z w)
    (h1 : (1 : ℂ) ∈ dirichletLFunctionSingularitiesInRectangle χ hne z w) :
    ‖(∑ ρ ∈ dirichletLFunctionSingularitiesInRectangle χ hne z w,
            dirichletReciprocalResidueAt hne x ρ) -
          dirichletReciprocalResidueAt hne x 0 -
          dirichletReciprocalResidueAt hne x 1 -
          (∑
            ρ ∈
              (dirichletLFunctionZerosInRectangle χ hne z w).filter
                (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
            dirichletLFunctionReciprocalZeroContribution x χ ρ)‖ ≤
      2 * |primitiveBRe χ| / Real.sqrt x := by
  classical
  let E := ((dirichletLFunctionSingularitiesInRectangle χ hne z w).erase 1).erase 0
  have he :
    (∑ ρ ∈ E, dirichletReciprocalResidueAt hne x ρ) =
      ∑ ρ ∈ E, dirichletLFunctionReciprocalZeroContribution x χ ρ := by
    refine Finset.sum_congr rfl ?_
    intro ρ hρ
    exact
      dirichletReciprocalResidueAt_zero_ne_one hne x (Finset.mem_erase.mp hρ).1
        (Finset.mem_erase.mp (Finset.mem_erase.mp hρ).2).1
  have hs :=
    Finset.sum_filter_add_sum_filter_not E (fun ρ : ℂ => DirichletCharacter.gammaFactor χ ρ = 0)
      (dirichletLFunctionReciprocalZeroContribution x χ)
  have ht := erased_gammaZeros_eq_trivialZeroFilter hne z w
  have hb :=
    norm_sum_reciprocalZeroContribution_of_gamma_ne_zero_le hq hGRH hp hne hinv hx
      (E.filter (fun ρ => ¬DirichletCharacter.gammaFactor χ ρ = 0))
      (fun ρ hρ => (Finset.mem_filter.mp hρ).2)
  have hid :
    (∑ ρ ∈ dirichletLFunctionSingularitiesInRectangle χ hne z w,
          dirichletReciprocalResidueAt hne x ρ) -
        dirichletReciprocalResidueAt hne x 0 -
        dirichletReciprocalResidueAt hne x 1 -
        (∑
          ρ ∈
            (dirichletLFunctionZerosInRectangle χ hne z w).filter
              (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
          dirichletLFunctionReciprocalZeroContribution x χ ρ) =
      ∑ ρ ∈ E.filter (fun ρ => ¬DirichletCharacter.gammaFactor χ ρ = 0),
        dirichletLFunctionReciprocalZeroContribution x χ ρ := by
    rw [dirichletSplitReciprocalSingularitySum x hne h1 h0, he, ← hs, ht]
    ring
  rw [hid]
  exact hb

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For a primitive nonprincipal character of level at least two under GRH,
`x > 1`, and left-edge index `m ≥ 1`, assume the nonzero trivial-zero sum is the same
complex value `T` at every height. The reciprocal weighted sum minus the normalized left
integral, the residues at zero and one, and `T` has norm at most
`2*|primitiveBRe χ|/sqrt x`. Pass the finite residue estimate through the height limit.
This supplies the fixed-left-edge step before sending the left edge to infinity. -/
theorem norm_reciprocalWeightedSum_sub_left_sub_origin_sub_trivial_le {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 < x) (m : ℕ) (hm : 1 ≤ m) (T : ℂ)
    (hT :
      ∀ k : ℕ,
        (∑
            ρ ∈
              (dirichletLFunctionZerosInRectangle χ hne
                    (primitiveHeightSeqLowerCorner hq hGRH hp hne hinv (2 * m) k)
                    (primitiveHeightSeqUpperCorner hq hGRH hp hne hinv k)).filter
                (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
            dirichletLFunctionReciprocalZeroContribution x χ ρ) =
          T) :
    ‖AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ -
          (((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
            (∫ t : ℝ,
              dirichletReciprocalContourKernel x χ
                (((primitiveReciprocalLeftRe (2 * m) : ℝ) : ℂ) + (t : ℂ) * Complex.I)) -
          dirichletReciprocalResidueAt hne x 0 -
          dirichletReciprocalResidueAt hne x 1 -
          T‖ ≤
      2 * |primitiveBRe χ| / Real.sqrt x := by
  have hA : 2 ≤ 2 * m := Nat.mul_le_mul_left 2 hm
  have ht :=
    tendsto_normalized_dirichletReciprocalBoundary_heightSeq hq hGRH hp hne hinv hx.le (2 * m) hA
  have hn :=
    (((ht.sub_const (dirichletReciprocalResidueAt hne x 0)).sub_const
            (dirichletReciprocalResidueAt hne x 1)).sub_const
        T).norm
  simp only [← Complex.ofReal_inv] at hn
  refine le_of_tendsto hn ?_
  filter_upwards with k
  rw [dirichletReciprocalFiniteContourIdentity_heightSeq_normalized hq hGRH hp hne hinv
      (zero_lt_one.trans hx) (2 * m) k hA
      (primitiveHeightSeq_singularities_mem_open hq hGRH hp hne hinv (2 * m) k hA)]
  obtain ⟨h0, h1⟩ :=
    primitiveReciprocalMellinPoints_mem_singularities_heightSeq hq hGRH hp hne hinv (2 * m) k hA
  have hb :=
    norm_reciprocal_residue_sum_sub_trivial_le hq hGRH hp hne hinv (zero_lt_one.trans hx)
      (primitiveHeightSeqLowerCorner hq hGRH hp hne hinv (2 * m) k)
      (primitiveHeightSeqUpperCorner hq hGRH hp hne hinv k) h0 h1
  rw [hT k] at hb
  exact hb

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For a primitive nonprincipal character of level at least two under GRH and
`x > 1`, assume exact height-independent trivial-zero sums `T m` for every `m ≥ 1`
and convergence `T m → L`. After subtracting the residues at zero and one and `L`,
the reciprocal weighted sum has norm at most `2*|primitiveBRe χ|/sqrt x`.
The height limit gives the fixed-edge bound; the left integral then vanishes as the edge
expands. This retains the exact trivial-zero limit in the full reciprocal formula. -/
theorem norm_reciprocalWeightedSum_sub_origin_sub_trivial_le {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 < x) (T : ℕ → ℂ) (L : ℂ)
    (hT :
      ∀ m : ℕ,
        1 ≤ m →
          ∀ k : ℕ,
            (∑
                ρ ∈
                  (dirichletLFunctionZerosInRectangle χ hne
                        (primitiveHeightSeqLowerCorner hq hGRH hp hne hinv (2 * m) k)
                        (primitiveHeightSeqUpperCorner hq hGRH hp hne hinv k)).filter
                    (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
                dirichletLFunctionReciprocalZeroContribution x χ ρ) =
              T m)
    (hL : Filter.Tendsto T Filter.atTop (nhds L)) :
    ‖AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ -
          dirichletReciprocalResidueAt hne x 0 -
          dirichletReciprocalResidueAt hne x 1 -
          L‖ ≤
      2 * |primitiveBRe χ| / Real.sqrt x := by
  have hA : Filter.Tendsto (fun m : ℕ => 2 * m) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono
      (fun m => by
        simpa only [one_mul, id_eq] using (Nat.mul_le_mul_right m (of_decide_eq_true rfl : 1 ≤ 2)))
      Filter.tendsto_id
  have hleft :=
    (tendsto_dirichletReciprocalContourKernel_leftVertical_integral_atTop hp hne hinv hx).comp hA
  have hS :
    Filter.Tendsto (fun _ : ℕ => AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ)
      Filter.atTop (nhds (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ)) :=
    tendsto_const_nhds
  have ht :=
    ((((hS.sub (hleft.const_mul (((2 * Real.pi)⁻¹ : ℝ) : ℂ))).sub_const
                (dirichletReciprocalResidueAt hne x 0)).sub_const
            (dirichletReciprocalResidueAt hne x 1)).sub
        hL).norm
  simp only [mul_zero, sub_zero] at ht
  refine le_of_tendsto ht ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  exact
    norm_reciprocalWeightedSum_sub_left_sub_origin_sub_trivial_le hq hGRH hp hne hinv hx m hm (T m)
      (hT m hm)

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For an even primitive nonprincipal character of level at least two under
GRH and `x > 1`, subtract the reciprocal residues at zero and one and add the positive
even trivial-zero correction series to the reciprocal weighted sum. Its norm is at most
`2*|primitiveBRe χ|/sqrt x`. Identify the height-independent finite trivial-zero sums
and pass their exact series limit through the two contour limits. This is the even
branch of the complete reciprocal error estimate. -/
theorem norm_even_reciprocalWeightedSum_sub_origin_add_series_le {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (he : χ.Even) {x : ℝ} (hx : 1 < x) :
    ‖AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ -
            dirichletReciprocalResidueAt hne x 0 -
            dirichletReciprocalResidueAt hne x 1 +
          ((∑' j : ℕ,
                x⁻¹ ^ (2 * (j + 1) + 1) /
                  (((2 * (j + 1) : ℕ) : ℝ) * (((2 * (j + 1) : ℕ) : ℝ) + 1)) :
              ℝ) :
            ℂ)‖ ≤
      2 * |primitiveBRe χ| / Real.sqrt x := by
  classical
  let T := fun m : ℕ =>
    ∑
      ρ ∈
        (dirichletLFunctionZerosInRectangle χ hne
              (primitiveHeightSeqLowerCorner hq hGRH hp hne hinv (2 * m) 0)
              (primitiveHeightSeqUpperCorner hq hGRH hp hne hinv 0)).filter
          (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
      dirichletLFunctionReciprocalZeroContribution x χ ρ
  have hT :
    ∀ m : ℕ,
      1 ≤ m →
        ∀ k : ℕ,
          (∑
              ρ ∈
                (dirichletLFunctionZerosInRectangle χ hne
                      (primitiveHeightSeqLowerCorner hq hGRH hp hne hinv (2 * m) k)
                      (primitiveHeightSeqUpperCorner hq hGRH hp hne hinv k)).filter
                  (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
              dirichletLFunctionReciprocalZeroContribution x χ ρ) =
            T m := by
    intro m hm k
    exact
      (sum_even_reciprocal_trivialZeros_primitiveRectangle_eq hq hGRH hp hne hinv he x m k hm).trans
        (sum_even_reciprocal_trivialZeros_primitiveRectangle_eq hq hGRH hp hne hinv he x m 0
            hm).symm
  have hb :=
    norm_reciprocalWeightedSum_sub_origin_sub_trivial_le hq hGRH hp hne hinv hx T _ hT
      (tendsto_sum_even_reciprocal_trivialZeros_primitiveRectangle hq hGRH hp hne hinv he hx
        (fun _ => 0))
  simpa only [sub_neg_eq_add] using hb

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- The odd primitive-character reciprocal formula keeps the entire odd
correction series. Height and left-edge limits transfer the finite completed
zero bound to the full weighted sum under GRH and `x > 1`. -/
theorem norm_odd_reciprocalWeightedSum_sub_origin_add_series_le {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (ho : χ.Odd) {x : ℝ} (hx : 1 < x) :
    ‖AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ -
            dirichletReciprocalResidueAt hne x 0 -
            dirichletReciprocalResidueAt hne x 1 +
          ((∑' j : ℕ,
                x⁻¹ ^ (2 * j + 1 + 1) / (((2 * j + 1 : ℕ) : ℝ) * (((2 * j + 1 : ℕ) : ℝ) + 1)) :
              ℝ) :
            ℂ)‖ ≤
      2 * |primitiveBRe χ| / Real.sqrt x := by
  classical
  let T := fun m : ℕ =>
    ∑
      ρ ∈
        (dirichletLFunctionZerosInRectangle χ hne
              (primitiveHeightSeqLowerCorner hq hGRH hp hne hinv (2 * m) 0)
              (primitiveHeightSeqUpperCorner hq hGRH hp hne hinv 0)).filter
          (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
      dirichletLFunctionReciprocalZeroContribution x χ ρ
  have hT :
    ∀ m : ℕ,
      1 ≤ m →
        ∀ k : ℕ,
          (∑
              ρ ∈
                (dirichletLFunctionZerosInRectangle χ hne
                      (primitiveHeightSeqLowerCorner hq hGRH hp hne hinv (2 * m) k)
                      (primitiveHeightSeqUpperCorner hq hGRH hp hne hinv k)).filter
                  (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
              dirichletLFunctionReciprocalZeroContribution x χ ρ) =
            T m := by
    intro m hm k
    exact
      (sum_odd_reciprocal_trivialZeros_primitiveRectangle_eq hq hGRH hp hne hinv ho x m k hm).trans
        (sum_odd_reciprocal_trivialZeros_primitiveRectangle_eq hq hGRH hp hne hinv ho x m 0 hm).symm
  have hb :=
    norm_reciprocalWeightedSum_sub_origin_sub_trivial_le hq hGRH hp hne hinv hx T _ hT
      (tendsto_sum_odd_reciprocal_trivialZeros_primitiveRectangle hq hGRH hp hne hinv ho hx
        (fun _ => 0))
  simpa only [sub_neg_eq_add] using hb

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For an even primitive nonprincipal character and `x > 0`, the reciprocal
residue at zero equals
`(1/x) * (logDeriv χ.completedLFunction 0 + (log pi + γ)/2 + log x + 1)`.
Differentiate the canonical local-factor regularization
and insert its logarithmic derivative. This exact scaled endpoint is used in the even
reciprocal formula without GRH. -/
theorem reciprocal_residue_zero_even_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (he : χ.Even) {x : ℝ} (hx : 0 < x) :
    dirichletReciprocalResidueAt hne x 0 =
      (1 / (x : ℂ)) *
        (logDeriv χ.completedLFunction 0 +
          ((Real.log Real.pi + Real.eulerMascheroniConstant) / 2 + Real.log x + 1 : ℝ)) := by
  obtain ⟨hg, hg0⟩ := analyticAt_and_ne_zero_dirichletEvenZeroLocalFactor hp hne
  rw [dirichletReciprocalResidueAt_zero_of_primitive_even_eq hp hne he,
    deriv_dirichletReciprocalEvenZeroRegularization_zero hx 1 hg hg0,
    logDeriv_dirichletEvenZeroLocalFactor_zero hp hne, ← Complex.ofReal_log Real.pi_nonneg, ←
    Complex.ofReal_log hx.le]
  simp only [Nat.cast_one, one_mul, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat]
  ring

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For a nonprincipal character of nonzero modulus, the ordinary logarithmic
derivative at one equals the completed one minus the explicit parity-dependent gamma
logarithmic derivative. Nonvanishing at one permits the logarithmic-derivative identity;
digamma special values evaluate each parity. This supplies the reciprocal residue at one
without a primitivity or GRH assumption. -/
theorem logDeriv_LFunction_one_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) :
    logDeriv χ.LFunction 1 =
      logDeriv χ.completedLFunction 1 -
        ((-Real.log Real.pi / 2 - Real.eulerMascheroniConstant / 2 -
              (if χ (-1) = 1 then Real.log 2 else 0) :
            ℝ) :
          ℂ) := by
  have hF := completedLFunction_ne_zero_of_one_le_re (w := (1 : ℂ)) hne (le_refl 1)
  have hl2 : Complex.log 2 = (Real.log 2 : ℂ) := by
    simpa only [Complex.ofReal_ofNat] using (Complex.ofReal_log (zero_le_two : (0 : ℝ) ≤ 2)).symm
  rcases χ.even_or_odd with he | ho
  · have hh : ∀ m : ℕ, (1 : ℂ) / 2 ≠ -(m : ℂ) := AnalyticNumberTheory.Gamma.half_ne_neg_nat
    rw [logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne hF
        (gammaFactor_ne_zero_of_even_of_half_ne_neg_nat he hh)
        (differentiableAt_gammaFactor_of_even_of_half_ne_neg_nat he hh),
      logDeriv_gammaFactor_eq_of_even_of_half_ne_neg_nat he hh, Complex.digamma_one_half,
      ite_eq_left (show χ (-1) = 1 from he), ← Complex.ofReal_log Real.pi_nonneg, hl2]
    simp only [Complex.ofReal_neg, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  · have hh : ∀ m : ℕ, ((1 : ℂ) + 1) / 2 ≠ -(m : ℂ) := by
      simpa only [add_self_div_two] using AnalyticNumberTheory.Gamma.one_ne_neg_nat
    rw [logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne hF
        (gammaFactor_ne_zero_of_odd_of_half_ne_neg_nat ho hh)
        (differentiableAt_gammaFactor_of_odd_of_half_ne_neg_nat ho hh),
      logDeriv_gammaFactor_eq_of_odd_of_half_ne_neg_nat ho hh, add_self_div_two,
      Complex.digamma_one, ite_eq_right (show χ (-1) ≠ 1 from ho.not_even), sub_zero, ←
      Complex.ofReal_log Real.pi_nonneg]
    simp only [Complex.ofReal_neg, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- The reciprocal formula error relative to the paper's two xi endpoints
and complete parity correction is bounded by `2*|Re B|/sqrt x` under GRH.
The endpoint functional equation and exact trivial-zero series fix its constants. -/
theorem norm_characterReciprocalWeightedSum_error_le {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    ‖AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ -
          logDeriv (PaperStatements.xi χ⁻¹) 0 -
          (1 / (x : ℂ)) * logDeriv (PaperStatements.xi χ) 0 -
          ((1 / 2 * (1 - 1 / x) * Real.log ((q : ℝ) / Real.pi) +
                PaperStatements.reciprocalCorrection χ x :
              ℝ) :
            ℂ)‖ ≤
      2 * |primitiveBRe χ| / Real.sqrt x := by
  have hne := primitiveCharacter_ne_one_of_three_le hq hp
  have hinv : χ⁻¹ ≠ 1 := inv_ne_one.mpr hne
  have hq2 : 2 ≤ q := (of_decide_eq_true rfl : 2 ≤ 3).trans hq
  have hxi := logDeriv_xi_zero_eq hp hne
  have hxii := logDeriv_xi_zero_eq (DirichletCharacter.isPrimitive_inv hp) hinv
  have hFE := completedLFunction_logDeriv_functionalEquation_at_zero hp hne hinv
  have hlq : Complex.log (q : ℂ) = (Real.log (q : ℝ) : ℂ) :=
    (Complex.ofReal_log (Nat.cast_nonneg q)).symm
  have hlqp := Real.log_div (Nat.cast_ne_zero.mpr (NeZero.ne q) : (q : ℝ) ≠ 0) Real.pi_ne_zero
  have h1 := dirichletReciprocalResidueAt_one_eq_neg_logDeriv hne x
  rw [logDeriv_LFunction_one_eq hne, neg_sub, sub_eq_add_neg, hFE, hlq] at h1
  rcases χ.even_or_odd with he | ho
  · let t :=
      ∑' j : ℕ, x⁻¹ ^ (2 * (j + 1) + 1) / (((2 * (j + 1) : ℕ) : ℝ) * (((2 * (j + 1) : ℕ) : ℝ) + 1))
    have ht :
      t =
        ∑' j : ℕ, 1 / (x ^ (2 * (j + 1) + 1) * (2 * ((j : ℝ) + 1)) * (2 * ((j : ℝ) + 1) + 1)) := by
      apply tsum_congr
      intro j
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, inv_pow, div_eq_mul_inv,
        mul_inv_rev, one_mul]
      ring
    have hb := norm_even_reciprocalWeightedSum_sub_origin_add_series_le hq2 hGRH hp hne hinv he hx
    have hid :
      AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ -
          logDeriv (PaperStatements.xi χ⁻¹) 0 -
          (1 / (x : ℂ)) * logDeriv (PaperStatements.xi χ) 0 -
          ((1 / 2 * (1 - 1 / x) * Real.log ((q : ℝ) / Real.pi) +
                PaperStatements.reciprocalCorrection χ x :
              ℝ) :
            ℂ) =
        AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ -
            dirichletReciprocalResidueAt hne x 0 -
            dirichletReciprocalResidueAt hne x 1 +
          (t : ℂ) := by
      rw [reciprocal_residue_zero_even_eq hp hne he (zero_lt_one.trans hx), h1, hxi, hxii, hlq,
        hlqp, PaperStatements.reciprocalCorrection, ite_eq_left (show χ (-1) = 1 from he),
        PaperStatements.reciprocalCorrectionEven, ← ht]
      simp only [Complex.ofReal_neg, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul,
        Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
        ite_eq_left (show χ (-1) = 1 from he)]
      ring
    rw [hid]
    exact hb
  · let t := ∑' j : ℕ, x⁻¹ ^ (2 * j + 1 + 1) / (((2 * j + 1 : ℕ) : ℝ) * (((2 * j + 1 : ℕ) : ℝ) + 1))
    have ht : t = ∑' j : ℕ, 1 / (x ^ (2 * j + 2) * (2 * (j : ℝ) + 1) * (2 * (j : ℝ) + 2)) := by
      apply tsum_congr
      intro j
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
        show ∀ a : ℝ, a + 1 + 1 = a + 2 from fun a => by ring, inv_pow, div_eq_mul_inv, mul_inv_rev,
        one_mul]
      ring
    have hb := norm_odd_reciprocalWeightedSum_sub_origin_add_series_le hq2 hGRH hp hne hinv ho hx
    have h0 :
      dirichletReciprocalResidueAt hne x 0 =
        (1 / (x : ℂ)) *
          (logDeriv χ.completedLFunction 0 - logDeriv (DirichletCharacter.gammaFactor χ) 0) := by
      rw [dirichletReciprocalResidueAt_zero_of_odd_eq hne (zero_lt_one.trans hx) ho]
      exact
        congrArg (fun z : ℂ => (1 / (x : ℂ)) * z)
          (eventuallyEq_logDeriv_LFunction_zero_of_odd hp hne ho).self_of_nhds
    have hl2 : Complex.log 2 = (Real.log 2 : ℂ) := by
      simpa only [Complex.ofReal_ofNat] using (Complex.ofReal_log (zero_le_two : (0 : ℝ) ≤ 2)).symm
    have hid :
      AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ -
          logDeriv (PaperStatements.xi χ⁻¹) 0 -
          (1 / (x : ℂ)) * logDeriv (PaperStatements.xi χ) 0 -
          ((1 / 2 * (1 - 1 / x) * Real.log ((q : ℝ) / Real.pi) +
                PaperStatements.reciprocalCorrection χ x :
              ℝ) :
            ℂ) =
        AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ -
            dirichletReciprocalResidueAt hne x 0 -
            dirichletReciprocalResidueAt hne x 1 +
          (t : ℂ) := by
      rw [h0, h1, hxi, hxii, hlq, hlqp, PaperStatements.reciprocalCorrection,
        ite_eq_right (show χ (-1) ≠ 1 from ho.not_even), PaperStatements.reciprocalCorrectionOdd, ←
        ht, logDeriv_gammaFactor_zero_odd_eq ho, ← Complex.ofReal_log Real.pi_nonneg, hl2]
      simp only [Complex.ofReal_neg, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul,
        Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
        ite_eq_right (show χ (-1) ≠ 1 from ho.not_even), sub_zero]
      ring
    rw [hid]
    exact hb

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- Under GRH, a primitive character of level at least three satisfies the
complex reciprocal formula of Lemma 2.3 for `x > 1`. The full zero-ledger
estimate supplies a coefficient of norm at most one. -/
theorem characterReciprocalWeightedSum_complex_formula {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    ∃ θ : ℂ,
      ‖θ‖ ≤ 1 ∧
        -logDeriv (PaperStatements.xi χ⁻¹) 0 - (1 / (x : ℂ)) * logDeriv (PaperStatements.xi χ) 0 +
            2 * θ / (Real.sqrt x : ℂ) * ((|primitiveBRe χ| : ℝ) : ℂ) =
          ((1 / 2 * (1 - 1 / x) * Real.log ((q : ℝ) / Real.pi) +
                  PaperStatements.reciprocalCorrection χ x :
                ℝ) :
              ℂ) -
            AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ := by
  obtain ⟨θ, hθ, he⟩ :=
    exists_complex_theta_mul_of_norm_le (norm_characterReciprocalWeightedSum_error_le hq hp hGRH hx)
  refine ⟨-θ, ?_, ?_⟩
  · simpa only [norm_neg] using hθ
  · simp only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_ofNat, div_eq_mul_inv] at he ⊢
    linear_combination he

end PseudoPrime.LLS
