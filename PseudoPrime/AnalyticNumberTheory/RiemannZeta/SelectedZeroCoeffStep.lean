/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.IntegerIntervalPhase

/-! # Checked coefficient steps for selected-zero phases -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Consecutive complex exponential Taylor terms differ by multiplication by
`z / (k + 1)`. This identity lets all coefficients share one center amplitude. -/
theorem phase_coeff_succ (A z : ℂ) (k : ℕ) :
    A * (z ^ (k + 1) / ((k + 1).factorial : ℂ)) =
      (A * (z ^ k / (k.factorial : ℂ))) * (z / (k + 1 : ℂ)) := by
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Checked real interval products enclose multiplication of a complex number
by an imaginary scalar. Two products suffice because the scalar has zero real part. -/
theorem phase_imag_mul_contains {R I D P Q : Analysis.IntegerInterval} {G : ℤ} {z : ℂ} {d : ℝ}
    (hz : Analysis.complexIntervalContains R I G z) (hd : D.Contains G d)
    (hp : Analysis.integerProductCheck G I.lower I.upper D.lower D.upper P.lower P.upper = true)
    (hq : Analysis.integerProductCheck G R.lower R.upper D.lower D.upper Q.lower Q.upper = true) :
    Analysis.complexIntervalContains P.neg Q G (z * ((d : ℂ) * Complex.I)) := by
  have hp' := Analysis.IntegerInterval.product_contains hp hz.2 hd
  have hq' := Analysis.IntegerInterval.product_contains hq hz.1 hd
  constructor
  · simpa only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, zero_mul, mul_zero, mul_one, zero_add, add_zero, neg_zero, sub_eq_add_neg] using
      Analysis.IntegerInterval.neg_contains hp'
  · simpa only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, zero_mul, mul_zero, mul_one, zero_add, sub_zero, add_zero] using hq'

/-- Given a checked interval for one centered coefficient, a checked interval
for the real step and two checked products enclose its successor. This permits
independent term certificates to reuse their center phase for all degrees. -/
theorem phase_coeff_step_contains {R I D P Q : Analysis.IntegerInterval} {G : ℤ} (A : ℂ) (x : ℝ)
    (k : ℕ)
    (hz :
      Analysis.complexIntervalContains R I G (A * (((x : ℂ) * Complex.I) ^ k / (k.factorial : ℂ))))
    (hd : D.Contains G (x / (k + 1)))
    (hp : Analysis.integerProductCheck G I.lower I.upper D.lower D.upper P.lower P.upper = true)
    (hq : Analysis.integerProductCheck G R.lower R.upper D.lower D.upper Q.lower Q.upper = true) :
    Analysis.complexIntervalContains P.neg Q G
      (A * (((x : ℂ) * Complex.I) ^ (k + 1) / ((k + 1).factorial : ℂ))) := by
  rw [phase_coeff_succ]
  have he : ((x : ℂ) * Complex.I) / (k + 1 : ℂ) = (((x / (k + 1) : ℝ) : ℂ) * Complex.I) := by
    simp only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
    ring
  rw [he]
  exact phase_imag_mul_contains hz hd hp hq

/-- One checked coefficient step records the real step interval and the
two signed products. The next real interval is the negated imaginary product;
the next imaginary interval is the real product. -/
structure PhaseCoeffWitness where
  step : Analysis.IntegerInterval
  imagProd : Analysis.IntegerInterval
  realProd : Analysis.IntegerInterval

/-- Check a sequence of rational coefficient steps from degree `k`. Each
recursive step consumes its witness and passes only its two output intervals
to the next step, without indexing the witness list. -/
@[expose]
def phaseCoeffCheck (G p d : ℤ) (k : ℕ) (R I : Analysis.IntegerInterval) :
    List PhaseCoeffWitness → Bool
  | [] => true
  | w :: rest =>
    Analysis.integerConstantCheck G p (d * (k + 1)) w.step.lower w.step.upper &&
      Analysis.integerProductCheck G I.lower I.upper w.step.lower w.step.upper w.imagProd.lower
        w.imagProd.upper &&
      Analysis.integerProductCheck G R.lower R.upper w.step.lower w.step.upper w.realProd.lower
        w.realProd.upper &&
      phaseCoeffCheck G p d (k + 1) w.imagProd.neg w.realProd rest

/-- Return the coordinate intervals after traversing the coefficient
witnesses. The empty sequence returns the supplied input intervals. -/
@[expose]
def phaseCoeffResult (R I : Analysis.IntegerInterval) :
    List PhaseCoeffWitness → Analysis.IntegerInterval × Analysis.IntegerInterval
  | [] => (R, I)
  | w :: rest => phaseCoeffResult w.imagProd.neg w.realProd rest

/-- A successful rational step certificate transports the initial complex
coefficient enclosure to the degree advanced by the witness count. Induction
uses the one-step interval theorem and never indexes the witness list. -/
theorem phaseCoeffCheck_sound (chain : List PhaseCoeffWitness) (G p d : ℤ) (k : ℕ)
    (R I : Analysis.IntegerInterval) (A : ℂ) (h : phaseCoeffCheck G p d k R I chain = true)
    (hz :
      Analysis.complexIntervalContains R I G
        (A * (((((p : ℝ) / d : ℝ) : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)))) :
    Analysis.complexIntervalContains (phaseCoeffResult R I chain).1 (phaseCoeffResult R I chain).2 G
      (A *
        (((((p : ℝ) / d : ℝ) : ℂ) * Complex.I) ^ (k + chain.length) /
          ((k + chain.length).factorial : ℂ))) := by
  induction chain generalizing k R I with
  | nil => simpa only [phaseCoeffResult, List.length_nil, Nat.add_zero] using hz
  | cons w rest ih =>
    have h1 := Bool.and_eq_true_iff.mp h
    have h2 := Bool.and_eq_true_iff.mp h1.1
    have h3 := Bool.and_eq_true_iff.mp h2.1
    have hd := Analysis.integerConstantCheck_sound h3.1
    have hd' : w.step.Contains G ((p : ℝ) / d / (k + 1)) := by
      simpa only [Analysis.IntegerInterval.Contains, Int.cast_mul, Int.cast_add, Int.cast_natCast,
        Int.cast_one, div_mul_eq_div_div] using hd
    have hn := phase_coeff_step_contains A ((p : ℝ) / d) k hz hd' h3.2 h2.2
    have hnext := ih (k + 1) w.imagProd.neg w.realProd h1.2 hn
    simpa only [phaseCoeffResult, List.length_cons, Nat.add_succ, Nat.succ_add] using hnext

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
