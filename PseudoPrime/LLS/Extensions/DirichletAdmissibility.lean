/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.DirichletSpecialization
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.EulerProduct.ExpLog
public import PseudoPrime.AnalyticNumberTheory.General.EntireOrder

/-!
# Analytic admissibility of degree-one Dirichlet L-function data

Character series and Euler products, entire continuation, gamma normalization, logarithmic
growth and the conjugate functional equation verify all fields of general admissibility.
The final conditional theorem specializes the generalized logarithmic formula to Lemma 2.5.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- The degree-one Euler factor is the character Euler factor, for any index and complex argument.
Evaluate the singleton product and rewrite division as a negative complex power.
This identifies the convergent character Euler product with the general data. -/
theorem ofDirichletCharacter_eulerFactor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (p : ℕ)
    (s : ℂ) : (ofDirichletCharacter χ).eulerFactor p s = (1 - χ p * (p : ℂ) ^ (-s))⁻¹ := by
  change (∏ _j : Fin 1, (1 - χ p / (p : ℂ) ^ s)⁻¹) = _
  rw [Fin.prod_univ_one, div_eq_mul_inv, ← Complex.cpow_neg]

/-- For Re s > 1, the principal logarithms of the degree-one Euler factors are summable.
Restrict the norm-summable character series to primes. Each prime value has norm less than one,
so its complementary factor lies in the slit plane and logarithmic inversion is valid.
This supplies absolute logarithmic convergence in analytic admissibility. -/
theorem ofDirichletCharacter_logEulerFactor_summable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes ↦ Complex.log ((ofDirichletCharacter χ).eulerFactor p s)) := by
  let f := dirichletSummandHom χ (Complex.ne_zero_of_one_lt_re hs)
  have hnorm : Summable (fun n ↦ ‖f n‖) := summable_dirichletSummand χ hs
  have hsum := (hnorm.of_norm.subtype Nat.Prime).clog_one_sub.neg
  apply hsum.congr
  intro p
  have hp : ‖f (p : ℕ)‖ < 1 := hnorm.of_norm.norm_lt_one (f := f.toMonoidHom) p.property.one_lt
  have hslit : 1 - f (p : ℕ) ∈ Complex.slitPlane := by
    simpa only [sub_eq_add_neg] using
      Complex.mem_slitPlane_of_norm_lt_one ((norm_neg _).trans_lt hp)
  rw [ofDirichletCharacter_eulerFactor]
  change -Complex.log (1 - f (p : ℕ)) = Complex.log (1 - f (p : ℕ))⁻¹
  rw [Complex.log_inv _ (Complex.slitPlane_arg_ne_pi hslit)]

/-- For Re s > 1, the degree-one series and Euler product converge to the continued L-function,
and the Euler-factor logarithms are summable. Identify the local factors and apply mathlib's
character series and product formulas. No primitivity or RH is required. -/
theorem ofDirichletCharacter_convergence {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    LSeriesSummable (ofDirichletCharacter χ).coefficient s ∧
      (ofDirichletCharacter χ).L s = LSeries (ofDirichletCharacter χ).coefficient s ∧
      Multipliable (fun p : Nat.Primes ↦ (ofDirichletCharacter χ).eulerFactor p s) ∧
      Summable (fun p : Nat.Primes ↦ Complex.log ((ofDirichletCharacter χ).eulerFactor p s)) ∧
      (ofDirichletCharacter χ).L s =
        ∏' p : Nat.Primes, (ofDirichletCharacter χ).eulerFactor p s := by
  have hfac :
    (fun p : Nat.Primes ↦ (ofDirichletCharacter χ).eulerFactor p s) =
      (fun p : Nat.Primes ↦ (1 - χ p * (p : ℂ) ^ (-s))⁻¹) :=
    funext (fun p ↦ ofDirichletCharacter_eulerFactor χ p s)
  have hprod := χ.LSeries_eulerProduct_hasProd hs
  refine
    ⟨χ.LSeriesSummable_of_one_lt_re hs, χ.LFunction_eq_LSeries hs, ?_,
      ofDirichletCharacter_logEulerFactor_summable χ hs, ?_⟩
  · rw [hfac]
    exact hprod.multipliable
  · rw [hfac]
    exact (χ.LFunction_eq_LSeries hs).trans hprod.tprod_eq.symm

/-- For a nontrivial character, the normalized completion is entire.
Its conductor power is entire because the modulus is nonzero; multiply by the parity constant
and the entire character completion. This proves the continuation field of admissibility. -/
theorem ofDirichletCharacter_differentiable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) : Differentiable ℂ (ofDirichletCharacter χ).completed := by
  exact
    (((differentiable_id.div_const 2).const_cpow
              (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))).mul_const
          _).mul
      (DirichletCharacter.differentiable_completedLFunction hne)

/-- The positive square root of pi equals its complex power with exponent one half.
Use the real square-root power formula and compatibility of real and complex powers.
This converts the odd-character gamma normalization. -/
private theorem pi_half : (Real.pi : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]

/-- The general degree-one gamma factor is the character gamma factor times its parity constant.
The singleton product and even normalization are immediate; for odd parity, split the pi power
and identify its half power with sqrt pi. This identifies the prescribed completion. -/
theorem ofDirichletCharacter_gammaFactor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) :
    (ofDirichletCharacter χ).gammaFactor s =
      (if χ (-1) = 1 then 1 else (Real.sqrt Real.pi : ℂ)) * χ.gammaFactor s := by
  change
    (Real.pi : ℂ) ^ (-(((1 : ℕ) : ℂ) * s) / 2) *
        (∏ _j : Fin 1, Complex.Gamma ((s + if χ (-1) = 1 then 0 else 1) / 2)) =
      _
  rw [Fin.prod_univ_one, Nat.cast_one, one_mul]
  by_cases he : χ (-1) = 1
  · rw [ite_eq_left he, add_zero, ite_eq_left he, one_mul]
    exact ((show χ.Even from he).gammaFactor_def s).symm
  · rw [ite_eq_right he, ite_eq_right he]
    have ho : χ.Odd := (χ.even_or_odd).resolve_left he
    rw [ho.gammaFactor_def, Complex.Gammaℝ_def]
    have hx : -s / 2 = -(s + 1) / 2 + 1 / 2 := by ring
    rw [hx, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero), pi_half]
    ring

/-- The character gamma factor is nonzero on Re s > 0.
Apply right-half-plane nonvanishing of Gamma-real to either parity, shifting by one if odd.
This permits recovering the completion from the ordinary L-function. -/
private theorem character_gammaFactor_ne_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) : χ.gammaFactor s ≠ 0 := by
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · rw [ho.gammaFactor_def]
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.one_re]
    linarith only [hs]

/-- On Re s > 0, the normalized completion equals the conductor power times the general gamma
factor and the ordinary L-function. The nonzero character gamma factor permits division
cancellation; the parity normalization identifies both gamma factors.
This proves compatibility of the entire continuation with the prescribed product. -/
theorem ofDirichletCharacter_completed_eq_gamma_product {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    (ofDirichletCharacter χ).completed s =
      (q : ℂ) ^ (s / 2) * (ofDirichletCharacter χ).gammaFactor s * χ.LFunction s := by
  have hs0 : s ≠ 0 := fun h ↦ (ne_of_gt hs) (congrArg Complex.re h)
  have hL := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)
  have hF := (eq_div_iff (character_gammaFactor_ne_zero χ hs)).mp hL
  rw [ofDirichletCharacter_gammaFactor]
  change (q : ℂ) ^ (s / 2) * _ * χ.completedLFunction s = _
  rw [← hF]
  ring

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- Conjugating the normalized completion at 1-conj s gives the inverse-character completion
at 1-s with the same real normalization. Conjugation preserves positive-real complex powers
and the parity constant. This prepares the general conjugate functional equation. -/
private theorem normalized_completion_conj {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) :
    (starRingEnd ℂ) ((ofDirichletCharacter χ).completed (1 - (starRingEnd ℂ) s)) =
      (q : ℂ) ^ ((1 - s) / 2) * (if χ (-1) = 1 then 1 else (Real.sqrt Real.pi : ℂ)) *
        χ⁻¹.completedLFunction (1 - s) := by
  change
    (starRingEnd ℂ)
        ((q : ℂ) ^ ((1 - (starRingEnd ℂ) s) / 2) *
          (if χ (-1) = 1 then 1 else (Real.sqrt Real.pi : ℂ)) *
          χ.completedLFunction (1 - (starRingEnd ℂ) s)) =
      _
  have harg : (q : ℂ).arg ≠ Real.pi :=
    Complex.slitPlane_arg_ne_pi
      (Complex.mem_slitPlane_iff.mpr (Or.inl (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q))))
  have hc := Complex.conj_cpow (q : ℂ) ((1 - s) / 2) harg
  simp only [map_div₀, map_sub, map_one, map_ofNat, Complex.conj_natCast] at hc
  rw [map_mul, map_mul, ← hc, DirichletCharacter.completedLFunction_conj]
  simp only [map_sub, map_one, Complex.conj_conj]
  split_ifs
  · rw [map_one]
  · rw [Complex.conj_ofReal]

/-- For a primitive character, the normalized completion satisfies the conjugate functional
equation with the character root number. Combine reflection and conjugation of the original
completion; the conductor powers add to the reflected exponent. No RH is required. -/
theorem ofDirichletCharacter_functionalEquation {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (s : ℂ) :
    (ofDirichletCharacter χ).completed s =
      χ.rootNumber *
        (starRingEnd ℂ) ((ofDirichletCharacter χ).completed (1 - (starRingEnd ℂ) s)) := by
  rw [normalized_completion_conj]
  change (q : ℂ) ^ (s / 2) * _ * χ.completedLFunction s = _
  have hFE := hp.completedLFunction_one_sub (1 - s)
  rw [show (1 : ℂ) - (1 - s) = s from by ring] at hFE
  have hpow : (q : ℂ) ^ (s / 2) * (q : ℂ) ^ ((1 - s) - 1 / 2) = (q : ℂ) ^ ((1 - s) / 2) := by
    rw [← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr (NeZero.ne q))]
    congr 1
    ring
  rw [hFE]
  calc
    _ =
        χ.rootNumber * ((q : ℂ) ^ (s / 2) * (q : ℂ) ^ ((1 - s) - 1 / 2)) *
          (if χ (-1) = 1 then 1 else (Real.sqrt Real.pi : ℂ)) *
          χ⁻¹.completedLFunction (1 - s) :=
      by ring
    _ = _ := by
      rw [hpow]
      ring

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- The root number of a primitive nontrivial character has norm one.
Apply the normalized conjugate functional equation twice at zero and cancel its nonzero value.
The resulting squared-norm identity and nonnegativity give unit norm for admissibility. -/
theorem ofDirichletCharacter_rootNumber_norm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) : ‖χ.rootNumber‖ = 1 := by
  have h0ne : (ofDirichletCharacter χ).completed 0 ≠ 0 := fun h ↦
    dirichletCompletedLFunction_zero_ne_zero_of_primitive hp hne
      ((ofDirichletCharacter_completed_eq_zero_iff χ 0).mp h)
  have h0 := ofDirichletCharacter_functionalEquation χ hp 0
  have h1 := ofDirichletCharacter_functionalEquation χ hp 1
  simp only [map_zero, sub_zero] at h0
  simp only [map_one, sub_self] at h1
  rw [h1, map_mul, Complex.conj_conj] at h0
  have hn := congrArg norm h0
  simp only [norm_mul, Complex.norm_conj] at hn
  have he :
    1 * ‖(ofDirichletCharacter χ).completed 0‖ =
      (‖χ.rootNumber‖ * ‖χ.rootNumber‖) * ‖(ofDirichletCharacter χ).completed 0‖ := by
    rw [one_mul, mul_assoc]
    exact hn
  have hs := mul_right_cancel₀ (norm_ne_zero_iff.mpr h0ne) he
  nlinarith only [hs, norm_nonneg χ.rootNumber]

/-- The norm of the conductor power is bounded by exp(q norm s) for nonzero modulus.
Express its norm by a real power, use Re s <= norm s and log q <= q, then compare exponents.
This absorbs conductor normalization into the growth envelope. -/
private theorem conductor_scale_bound {q : ℕ} [NeZero q] (s : ℂ) :
    ‖(q : ℂ) ^ (s / 2)‖ ≤ Real.exp ((q : ℝ) * ‖s‖) := by
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (NeZero.ne q)), Complex.div_ofNat_re,
    Real.rpow_def_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q)))]
  apply Real.exp_le_exp.mpr
  have h₁ := mul_le_mul_of_nonneg_left (Complex.re_le_norm s) (Real.log_natCast_nonneg q)
  have h₂ := mul_le_mul_of_nonneg_right (Real.log_le_self (Nat.cast_nonneg q)) (norm_nonneg s)
  nlinarith only [h₁, h₂, mul_nonneg (Nat.cast_nonneg q) (norm_nonneg s)]

/-- The parity normalization is bounded in norm by exp(1+sqrt pi).
Both possible constants are at most 1+sqrt pi, which is bounded by the exponential.
This absorbs the constant normalization into the growth envelope. -/
private theorem parity_scale_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖(if χ (-1) = 1 then 1 else (Real.sqrt Real.pi : ℂ))‖ ≤ Real.exp (1 + Real.sqrt Real.pi) := by
  have h : ‖(if χ (-1) = 1 then 1 else (Real.sqrt Real.pi : ℂ))‖ ≤ 1 + Real.sqrt Real.pi := by
    split_ifs
    · rw [norm_one]
      linarith only [Real.sqrt_nonneg Real.pi]
    · rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg Real.pi)]
      linarith only
  exact
    h.trans
      ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp (1 + Real.sqrt Real.pi)))

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For a primitive nontrivial character at modulus at least two and norm s >= 1,
the normalized completion has a positive exponential envelope proportional to
(norm s+3) log(norm s+3). Combine the existing ball bound with conductor and parity bounds.
This supplies the quantitative input to order-at-most-one growth. -/
private theorem normalized_completion_envelope {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 2 ≤ q) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (s : ℂ) (hs : 1 ≤ ‖s‖) :
    ‖(ofDirichletCharacter χ).completed s‖ ≤
      Real.exp
        (((q : ℝ) + (1 + Real.sqrt Real.pi) + (4 * (q : ℝ) + 3)) *
          ((‖s‖ + 3) * Real.log (‖s‖ + 3))) := by
  have hF :=
    (norm_completedLFunction_le_completedLFunctionBallBound (Nat.lt_of_succ_le hq) hp hne
          (inv_ne_one.mpr hne) (norm_nonneg s) (le_refl ‖s‖)).trans
      (completedLFunctionBallBound_le_exp hq hs)
  have hL := one_le_log_add_three hs
  have hX : ‖s‖ ≤ (‖s‖ + 3) * Real.log (‖s‖ + 3) := by
    have h := mul_le_mul_of_nonneg_left hL (by linarith only [norm_nonneg s] : 0 ≤ ‖s‖ + 3)
    nlinarith only [h]
  have hX1 : 1 ≤ (‖s‖ + 3) * Real.log (‖s‖ + 3) := hs.trans hX
  change ‖(q : ℂ) ^ (s / 2) * _ * χ.completedLFunction s‖ ≤ _
  rw [norm_mul, norm_mul]
  calc
    _ ≤
        Real.exp ((q : ℝ) * ‖s‖) * Real.exp (1 + Real.sqrt Real.pi) *
          Real.exp ((4 * (q : ℝ) + 3) * ((‖s‖ + 3) * Real.log (‖s‖ + 3))) :=
      mul_le_mul
        (mul_le_mul (conductor_scale_bound s) (parity_scale_bound χ) (norm_nonneg _)
          (Real.exp_pos _).le)
        hF (norm_nonneg _) (by positivity)
    _ =
        Real.exp
          ((q : ℝ) * ‖s‖ + (1 + Real.sqrt Real.pi) +
            (4 * (q : ℝ) + 3) * ((‖s‖ + 3) * Real.log (‖s‖ + 3))) :=
      by rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h₁ := mul_le_mul_of_nonneg_left hX (Nat.cast_nonneg q)
      have h₂ :=
        mul_le_mul_of_nonneg_left hX1
          (by linarith only [Real.sqrt_nonneg Real.pi] : 0 ≤ 1 + Real.sqrt Real.pi)
      nlinarith only [h₁, h₂]

/-- Primitive nontrivial character data at modulus at least two have completion
of order at most one.
Apply the positive logarithmic exponential envelope and its real-power comparison.
This proves the growth field in analytic admissibility, without RH. -/
theorem ofDirichletCharacter_hasOrderAtMostOne {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 2 ≤ q) (hp : χ.IsPrimitive) (hne : χ ≠ 1) :
    AnalyticNumberTheory.General.HasOrderAtMostOne (ofDirichletCharacter χ).completed := by
  apply
    AnalyticNumberTheory.General.hasOrderAtMostOne_of_exp_norm_mul_log_bound
      (ofDirichletCharacter χ).completed
      (show 0 < (q : ℝ) + (1 + Real.sqrt Real.pi) + (4 * (q : ℝ) + 3) by
        nlinarith only [(Nat.cast_nonneg q : (0 : ℝ) ≤ q), Real.sqrt_nonneg Real.pi])
  exact normalized_completion_envelope χ hq hp hne

/-- Primitive nontrivial characters at modulus at least two give analytically admissible degree-one
L-function data. Character bounds prove the arithmetic fields; convergent series and products,
gamma compatibility, entire continuation, order-one growth and the unit-root functional equation
prove the analytic fields. This removes the admissibility premise when specializing Lemma 2.5. -/
theorem ofDirichletCharacter_isAdmissible {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 2 ≤ q) (hp : χ.IsPrimitive) (hne : χ ≠ 1) : (ofDirichletCharacter χ).IsAdmissible := by
  refine
    ⟨Nat.zero_lt_one, Nat.pos_of_ne_zero (NeZero.ne q), ?_, ?_, ?_, fun s hs ↦
      ofDirichletCharacter_convergence χ hs, fun s hs ↦
      ofDirichletCharacter_completed_eq_gamma_product χ hs,
      ofDirichletCharacter_differentiable χ hne, ofDirichletCharacter_hasOrderAtMostOne χ hq hp hne,
      χ.rootNumber, ofDirichletCharacter_rootNumber_norm χ hp hne,
      ofDirichletCharacter_functionalEquation χ hp⟩
  · change χ ((1 : ℕ) : ZMod q) = 1
    rw [Nat.cast_one, map_one]
  · intro j
    change 0 ≤ (if χ (-1) = 1 then 0 else (1 : ℂ)).re
    split_ifs
    · exact le_refl 0
    · exact zero_le_one
  · intro p _ j
    exact χ.norm_le_one p

end PseudoPrime.LLS.Extensions.GeneralLFunction

namespace PseudoPrime.LLS.PaperStatements

/-- The general logarithmic formula implies the original Lemma 2.5 with individual RH.
Prove admissibility of every primitive degree-one character datum at modulus at least three,
then apply the specialization implication. Only the general formula is an explicit premise;
the public proof of Lemma 2.5 supplies it using `lls_propL1_general_proof`. -/
theorem lls_lemma25_of_general_formula (hformula : Extensions.lls_propL1_general) :
    lls_lemma25 := by
  apply lls_lemma25_of_general hformula
  intro q _ χ hq hp
  exact
    Extensions.GeneralLFunction.ofDirichletCharacter_isAdmissible χ
      (Nat.le_trans (by norm_num only : 2 ≤ 3) hq) hp (primitiveCharacter_ne_one_of_three_le hq hp)

end PseudoPrime.LLS.PaperStatements
