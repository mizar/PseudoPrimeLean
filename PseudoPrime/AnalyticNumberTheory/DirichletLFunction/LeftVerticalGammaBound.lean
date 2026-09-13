/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LeftVerticalDigammaBound

/-!
# Left-vertical gamma-factor pair bound

Connects the quarter-lattice and positivity separation facts to the regular-point gamma-factor API
in `GammaFactorLogDeriv` at the four digamma arguments the left-vertical line
`s_A(t) := -A - 1/2 + i t` and its reflection `1 - s_A(t) = A + 3/2 - i t` feed into
`logDeriv (gammaFactor χ)` (even/odd parity × direct/reflected point), then combines the
explicit digamma bound into a single `χ`-uniform gamma-factor pair bound.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-! ### The four `hhalf` pole-avoidance facts at the left-vertical line and its reflection -/

/-- The even-parity direct-point digamma argument `s_A(t)/2 = -A/2 - 1/4 + (t/2) i` avoids every
nonpositive integer, for every `A t`. -/
theorem leftVertical_even_half_ne_neg_nat (A : ℕ) (t : ℝ) (m : ℕ) :
    (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2 ≠ -(m : ℂ) := by
  have heq :
    (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2 =
      ((-(A : ℝ) / 2 - 1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp only [one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
        Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.div_ofNat_re, Complex.add_re,
        Complex.sub_re, Complex.neg_re, Complex.natCast_re, Complex.inv_re, Complex.re_ofNat,
        Complex.normSq_ofNat, div_self_mul_self', Complex.mul_re, Complex.ofReal_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.ofReal_div,
        Complex.div_ofNat_im, zero_div]
      ring
    · simp only [one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
        Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.div_ofNat_im, Complex.add_im,
        Complex.sub_im, Complex.neg_im, Complex.natCast_im, neg_zero, Complex.inv_im,
        Complex.im_ofNat, Complex.normSq_ofNat, zero_div, sub_self, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero,
        add_zero, zero_add, Complex.ofReal_div, Complex.div_ofNat_re]
  rw [heq]
  apply
    ne_neg_nat_of_re_quarterSep (z :=
      ((-(A : ℝ) / 2 - 1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I)
  intro q
  have h := leftEven_quarterSep A q
  simpa only [one_div, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_neg,
    Complex.ofReal_natCast, Complex.ofReal_ofNat, Complex.ofReal_inv, Complex.add_re,
    Complex.sub_re, Complex.div_ofNat_re, Complex.neg_re, Complex.natCast_re, Complex.inv_re,
    Complex.re_ofNat, Complex.normSq_ofNat, div_self_mul_self', Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, mul_zero, Complex.div_ofNat_im, Complex.ofReal_im, zero_div, Complex.I_im,
    mul_one, sub_self, add_zero, ge_iff_le] using h

/-- The odd-parity direct-point digamma argument `(s_A(t) + 1)/2 = -A/2 + 1/4 + (t/2) i` avoids
every nonpositive integer, for every `A t`. -/
theorem leftVertical_odd_half_ne_neg_nat (A : ℕ) (t : ℝ) (m : ℕ) :
    ((((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) + 1) / 2 ≠ -(m : ℂ) := by
  have heq :
    ((((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) + 1) / 2 =
      ((-(A : ℝ) / 2 + 1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp only [one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
        Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.div_ofNat_re, Complex.add_re,
        Complex.sub_re, Complex.neg_re, Complex.natCast_re, Complex.inv_re, Complex.re_ofNat,
        Complex.normSq_ofNat, div_self_mul_self', Complex.mul_re, Complex.ofReal_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.one_re,
        Complex.ofReal_add, Complex.ofReal_div, Complex.div_ofNat_im, zero_div]
      ring
    · simp only [one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
        Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.div_ofNat_im, Complex.add_im,
        Complex.sub_im, Complex.neg_im, Complex.natCast_im, neg_zero, Complex.inv_im,
        Complex.im_ofNat, Complex.normSq_ofNat, zero_div, sub_self, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero,
        add_zero, zero_add, Complex.one_im, Complex.ofReal_add, Complex.ofReal_div,
        Complex.div_ofNat_re]
  rw [heq]
  apply
    ne_neg_nat_of_re_quarterSep (z :=
      ((-(A : ℝ) / 2 + 1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I)
  intro q
  have h := leftOdd_quarterSep A q
  simpa only [one_div, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_neg,
    Complex.ofReal_natCast, Complex.ofReal_ofNat, Complex.ofReal_inv, Complex.add_re,
    Complex.div_ofNat_re, Complex.neg_re, Complex.natCast_re, Complex.inv_re, Complex.re_ofNat,
    Complex.normSq_ofNat, div_self_mul_self', Complex.mul_re, Complex.ofReal_re, Complex.I_re,
    mul_zero, Complex.div_ofNat_im, Complex.ofReal_im, zero_div, Complex.I_im, mul_one, sub_self,
    add_zero, ge_iff_le] using h

/-- The even-parity reflected-point digamma argument `(1 - s_A(t))/2 = A/2 + 3/4 - (t/2) i` avoids
every nonpositive integer, for `A ≥ 2` and every `t`. -/
theorem reflectedLeftVertical_even_half_ne_neg_nat (A : ℕ) (hA : 2 ≤ A) (t : ℝ) (m : ℕ) :
    (1 - (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) / 2 ≠ -(m : ℂ) := by
  have hA' : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have heq :
    (1 - (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) / 2 =
      ((A : ℝ) / 2 + 3 / 4 : ℂ) + ((-(t / 2) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp only [one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
        Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.div_ofNat_re, Complex.sub_re,
        Complex.one_re, Complex.add_re, Complex.neg_re, Complex.natCast_re, Complex.inv_re,
        Complex.re_ofNat, Complex.normSq_ofNat, div_self_mul_self', Complex.mul_re,
        Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one,
        sub_self, add_zero, Complex.ofReal_div, neg_mul, Complex.div_ofNat_im, zero_div, neg_zero]
      ring
    · simp only [one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
        Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.div_ofNat_im, Complex.sub_im,
        Complex.one_im, Complex.add_im, Complex.neg_im, Complex.natCast_im, neg_zero,
        Complex.inv_im, Complex.im_ofNat, Complex.normSq_ofNat, zero_div, sub_self, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero,
        add_zero, zero_add, zero_sub, Complex.ofReal_div, neg_mul, Complex.div_ofNat_re]
      ring
  rw [heq]
  apply
    ne_neg_nat_of_re_quarterSep (z := ((A : ℝ) / 2 + 3 / 4 : ℂ) + ((-(t / 2) : ℝ) : ℂ) * Complex.I)
  intro q
  have hpos : (1 : ℝ) / 4 ≤ (A : ℝ) / 2 + 3 / 4 := by linarith
  have h := quarterSep_of_pos hpos q
  simpa only [one_div, Complex.ofReal_natCast, Complex.ofReal_neg, Complex.ofReal_div,
    Complex.ofReal_ofNat, neg_mul, Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re,
    Complex.re_ofNat, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
    Complex.div_ofNat_im, Complex.ofReal_im, zero_div, Complex.I_im, mul_one, sub_self, neg_zero,
    add_zero, ge_iff_le] using h

/-- The odd-parity reflected-point digamma argument `(2 - s_A(t))/2 = A/2 + 5/4 - (t/2) i` avoids
every nonpositive integer, for `A ≥ 2` and every `t`. -/
theorem reflectedLeftVertical_odd_half_ne_neg_nat (A : ℕ) (hA : 2 ≤ A) (t : ℝ) (m : ℕ) :
    ((1 - (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) + 1) / 2 ≠ -(m : ℂ) := by
  have hA' : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have heq :
    ((1 - (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) + 1) / 2 =
      ((A : ℝ) / 2 + 5 / 4 : ℂ) + ((-(t / 2) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp only [one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
        Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.div_ofNat_re, Complex.add_re,
        Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.natCast_re, Complex.inv_re,
        Complex.re_ofNat, Complex.normSq_ofNat, div_self_mul_self', Complex.mul_re,
        Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one,
        sub_self, add_zero, Complex.ofReal_div, neg_mul, Complex.div_ofNat_im, zero_div, neg_zero]
      ring
    · simp only [one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
        Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.div_ofNat_im, Complex.add_im,
        Complex.sub_im, Complex.one_im, Complex.neg_im, Complex.natCast_im, neg_zero,
        Complex.inv_im, Complex.im_ofNat, Complex.normSq_ofNat, zero_div, sub_self, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero,
        add_zero, zero_add, zero_sub, Complex.ofReal_div, neg_mul, Complex.div_ofNat_re]
      ring
  rw [heq]
  apply
    ne_neg_nat_of_re_quarterSep (z := ((A : ℝ) / 2 + 5 / 4 : ℂ) + ((-(t / 2) : ℝ) : ℂ) * Complex.I)
  intro q
  have hpos : (1 : ℝ) / 4 ≤ (A : ℝ) / 2 + 5 / 4 := by linarith
  have h := quarterSep_of_pos hpos q
  simpa only [one_div, Complex.ofReal_natCast, Complex.ofReal_neg, Complex.ofReal_div,
    Complex.ofReal_ofNat, neg_mul, Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re,
    Complex.re_ofNat, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
    Complex.div_ofNat_im, Complex.ofReal_im, zero_div, Complex.I_im, mul_one, sub_self, neg_zero,
    add_zero, ge_iff_le] using h

/-! ### The gamma-factor pair bound at the left-vertical line -/

/--
Input/assumptions: none (existence statement, uniform in `N`, `χ`, `A`, `t`).
Conclusion: there is `C ≥ 0` such that for every `A ≥ 2`, every character `χ` (any modulus, any
parity), and every `t : ℝ`, `‖logDeriv (gammaFactor χ) (s_A(t))‖ + ‖logDeriv (gammaFactor χ)
(1 - s_A(t))‖ ≤ C ((A + 5)² + 1 + log(|t| + 2))`, where `s_A(t) := -A - 1/2 + t i`.
Content: dispatches on `χ.even_or_odd`; in each parity, the exact formula
(`DirichletLFunction.logDeriv_gammaFactor_eq_of_even_of_half_ne_neg_nat`/`_odd_`) applies at both
`s_A(t)` and
`1 - s_A(t)` (pole-avoidance from the four `leftVertical_*`/`reflectedLeftVertical_*` facts), and
each digamma value is bounded via `exists_C_forall_norm_digamma_explicit_le` at real part `≤ A + 2`
in absolute value with imaginary part `± t/2` (so `2 |± t/2| + 2 = |t| + 2` matches exactly). The
constant `log π` term is absorbed since `(A + 5)² + 1 + log(|t| + 2) ≥ 1`.
Role: the gamma-factor ingredient — combined with the reflection identity, this gives the
left-vertical `L'/L` bound.
-/
theorem exists_C_forall_norm_logDeriv_gammaFactor_leftVertical_pair_le :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ A : ℕ,
          2 ≤ A →
            ∀ {N : ℕ} (χ : DirichletCharacter ℂ N) (t : ℝ),
              ‖logDeriv (DirichletCharacter.gammaFactor χ)
                      (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ +
                  ‖logDeriv (DirichletCharacter.gammaFactor χ)
                      (1 - (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ ≤
                C * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) := by
  obtain ⟨Cψ, hCψnn, hψ⟩ := exists_C_forall_norm_digamma_explicit_le
  set C : ℝ := Cψ + |Real.log Real.pi| + 10 with hC_def
  have hCnn : 0 ≤ C := by
    have := abs_nonneg (Real.log Real.pi); linarith
  refine ⟨C, hCnn, fun A hA N χ t => ?_⟩
  have hA' : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hlogpi_norm : ‖(-(Complex.log (Real.pi : ℂ)) / 2 : ℂ)‖ = |Real.log Real.pi| / 2 := by
    have h1 : (-(Complex.log (Real.pi : ℂ)) / 2 : ℂ) = ((-(Real.log Real.pi) / 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_log Real.pi_pos.le]; push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg]
    norm_num only
  have htnn : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hEA1 : (1 : ℝ) ≤ ((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2) := by nlinarith [hA', htnn]
  have hmain :
    ∀ a b : ℝ,
      |a| ≤ (A : ℝ) + 2 →
        (∀ q : ℕ, (1 : ℝ) / 4 ≤ |a + (q : ℝ)|) →
        2 * |b| = |t| →
        ‖(-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((a : ℂ) + (b : ℂ) * Complex.I) / 2 :
              ℂ)‖ ≤
          (C / 2) * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) := by
    intro a b ha hsep hb
    have hdb := hψ A hA a b ha hsep
    rw [hb] at hdb
    calc
      ‖(-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((a : ℂ) + (b : ℂ) * Complex.I) / 2 :
              ℂ)‖ ≤
          ‖(-(Complex.log (Real.pi : ℂ)) / 2 : ℂ)‖ +
            ‖(Complex.digamma ((a : ℂ) + (b : ℂ) * Complex.I) / 2 : ℂ)‖ :=
        norm_add_le _ _
      _ = |Real.log Real.pi| / 2 + ‖Complex.digamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ / 2 := by
        rw [hlogpi_norm, norm_div, Complex.norm_two]
      _ ≤ |Real.log Real.pi| / 2 + Cψ * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) / 2 := by
        gcongr
      _ ≤ (C / 2) * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) := by
        rw [hC_def]
        nlinarith [hCψnn, hEA1, abs_nonneg (Real.log Real.pi)]
  rcases χ.even_or_odd with heven | hodd
  · rw [logDeriv_gammaFactor_eq_of_even_of_half_ne_neg_nat
        heven (leftVertical_even_half_ne_neg_nat A t),
      logDeriv_gammaFactor_eq_of_even_of_half_ne_neg_nat
        heven (reflectedLeftVertical_even_half_ne_neg_nat A hA t)]
    have hform1 :
      (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2 =
        ((-(A : ℝ) / 2 - 1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext
      · simp only [one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
          Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.div_ofNat_re, Complex.add_re,
          Complex.sub_re, Complex.neg_re, Complex.natCast_re, Complex.inv_re, Complex.re_ofNat,
          Complex.normSq_ofNat, div_self_mul_self', Complex.mul_re, Complex.ofReal_re, Complex.I_re,
          mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero,
          Complex.ofReal_div, Complex.div_ofNat_im, zero_div]
        ring
      · simp only [one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
          Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.div_ofNat_im, Complex.add_im,
          Complex.sub_im, Complex.neg_im, Complex.natCast_im, neg_zero, Complex.inv_im,
          Complex.im_ofNat, Complex.normSq_ofNat, zero_div, sub_self, Complex.mul_im,
          Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero,
          add_zero, zero_add, Complex.ofReal_div, Complex.div_ofNat_re]
    have hform2 :
      (1 - (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) / 2 =
        (((A : ℝ) / 2 + 3 / 4 : ℝ) : ℂ) + ((-(t / 2) : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext
      · simp only [one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
          Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.div_ofNat_re, Complex.sub_re,
          Complex.one_re, Complex.add_re, Complex.neg_re, Complex.natCast_re, Complex.inv_re,
          Complex.re_ofNat, Complex.normSq_ofNat, div_self_mul_self', Complex.mul_re,
          Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one,
          sub_self, add_zero, Complex.ofReal_add, Complex.ofReal_div, neg_mul, Complex.div_ofNat_im,
          zero_div, neg_zero]
        ring
      · simp only [one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
          Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.div_ofNat_im, Complex.sub_im,
          Complex.one_im, Complex.add_im, Complex.neg_im, Complex.natCast_im, neg_zero,
          Complex.inv_im, Complex.im_ofNat, Complex.normSq_ofNat, zero_div, sub_self,
          Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re,
          mul_zero, add_zero, zero_add, zero_sub, Complex.ofReal_add, Complex.ofReal_div, neg_mul,
          Complex.div_ofNat_re]
        ring
    rw [hform1, hform2]
    have ha1 : |(-(A : ℝ) / 2 - 1 / 4)| ≤ (A : ℝ) + 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have ha2 : |((A : ℝ) / 2 + 3 / 4)| ≤ (A : ℝ) + 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hb1 : (2 : ℝ) * |t / 2| = |t| := by
      rw [abs_div, show |(2 : ℝ)| = 2 from by norm_num only]; ring
    have hb2 : (2 : ℝ) * |-(t / 2)| = |t| := by
      rw [abs_neg]; exact hb1
    have hsep2 : ∀ q : ℕ, (1 : ℝ) / 4 ≤ |((A : ℝ) / 2 + 3 / 4) + (q : ℝ)| := fun q =>
      quarterSep_of_pos (by linarith) q
    have h1 := hmain (-(A : ℝ) / 2 - 1 / 4) (t / 2) ha1 (leftEven_quarterSep A) hb1
    have h2 := hmain ((A : ℝ) / 2 + 3 / 4) (-(t / 2)) ha2 hsep2 hb2
    linarith [h1, h2]
  · rw [logDeriv_gammaFactor_eq_of_odd_of_half_ne_neg_nat
        hodd (leftVertical_odd_half_ne_neg_nat A t),
      logDeriv_gammaFactor_eq_of_odd_of_half_ne_neg_nat
        hodd (reflectedLeftVertical_odd_half_ne_neg_nat A hA t)]
    have hform1 :
      ((((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) + 1) / 2 =
        ((-(A : ℝ) / 2 + 1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext
      · simp only [one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
          Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.div_ofNat_re, Complex.add_re,
          Complex.sub_re, Complex.neg_re, Complex.natCast_re, Complex.inv_re, Complex.re_ofNat,
          Complex.normSq_ofNat, div_self_mul_self', Complex.mul_re, Complex.ofReal_re, Complex.I_re,
          mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.one_re,
          Complex.ofReal_add, Complex.ofReal_div, Complex.div_ofNat_im, zero_div]
        ring
      · simp only [one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
          Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.div_ofNat_im, Complex.add_im,
          Complex.sub_im, Complex.neg_im, Complex.natCast_im, neg_zero, Complex.inv_im,
          Complex.im_ofNat, Complex.normSq_ofNat, zero_div, sub_self, Complex.mul_im,
          Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero,
          add_zero, zero_add, Complex.one_im, Complex.ofReal_add, Complex.ofReal_div,
          Complex.div_ofNat_re]
    have hform2 :
      ((1 - (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) + 1) / 2 =
        (((A : ℝ) / 2 + 5 / 4 : ℝ) : ℂ) + ((-(t / 2) : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext
      · simp only [one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
          Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.div_ofNat_re, Complex.add_re,
          Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.natCast_re, Complex.inv_re,
          Complex.re_ofNat, Complex.normSq_ofNat, div_self_mul_self', Complex.mul_re,
          Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one,
          sub_self, add_zero, Complex.ofReal_add, Complex.ofReal_div, neg_mul, Complex.div_ofNat_im,
          zero_div, neg_zero]
        ring
      · simp only [one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
          Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.div_ofNat_im, Complex.add_im,
          Complex.sub_im, Complex.one_im, Complex.neg_im, Complex.natCast_im, neg_zero,
          Complex.inv_im, Complex.im_ofNat, Complex.normSq_ofNat, zero_div, sub_self,
          Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re,
          mul_zero, add_zero, zero_add, zero_sub, Complex.ofReal_add, Complex.ofReal_div, neg_mul,
          Complex.div_ofNat_re]
        ring
    rw [hform1, hform2]
    have ha1 : |(-(A : ℝ) / 2 + 1 / 4)| ≤ (A : ℝ) + 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have ha2 : |((A : ℝ) / 2 + 5 / 4)| ≤ (A : ℝ) + 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hb1 : (2 : ℝ) * |t / 2| = |t| := by
      rw [abs_div, show |(2 : ℝ)| = 2 from by norm_num only]; ring
    have hb2 : (2 : ℝ) * |-(t / 2)| = |t| := by
      rw [abs_neg]; exact hb1
    have hsep2 : ∀ q : ℕ, (1 : ℝ) / 4 ≤ |((A : ℝ) / 2 + 5 / 4) + (q : ℝ)| := fun q =>
      quarterSep_of_pos (by linarith) q
    have h1 := hmain (-(A : ℝ) / 2 + 1 / 4) (t / 2) ha1 (leftOdd_quarterSep A) hb1
    have h2 := hmain ((A : ℝ) / 2 + 5 / 4) (-(t / 2)) ha2 hsep2 hb2
    linarith [h1, h2]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
