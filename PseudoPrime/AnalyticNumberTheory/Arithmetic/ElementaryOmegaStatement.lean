import PseudoPrime.AnalyticNumberTheory.Arithmetic.ElementaryOmega
import PseudoPrime.AnalyticNumberTheory.Arithmetic.OddPrimeCutoff
import PseudoPrime.NumberTheory.CharacterModulus

/-!
# The elementary, Robin-free `ω(4n)` bound

States `ElementaryOmegaStatement`, the Prop asserting that for odd `n ≥ 750` the prime-factor
count `ω(characterModulus n) = ω(4n)` is at most `(7/5) · log(4n) / loglog(4n)`, and derives from
it the rescaled inequality `elementary_prime_count_term_le` used by downstream analytic bounds.
The statement is proved unconditionally elsewhere by `ElementaryOmegaFiniteCertificates`; here it
is only declared and consumed as a hypothesis, keeping this file independent of that proof's
calculus tail and finite certificate checks.
-/

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The constant `7/5` in the elementary, Robin-free `ω(4n)` bound. -/
noncomputable def elementaryOmegaConstant : ℝ :=
  7 / 5

/--
For odd `n ≥ 750` (so that
`4n ≥ 3000`), the number of distinct prime factors of `4n` is at most
`(7/5) · log(4n) / loglog(4n)`.

This proposition uses `ω(4n) = ω(n) + 1` and the odd primorial lower bound for `n`.
It is proved by `elementaryOmegaStatement` in `ElementaryOmegaFiniteCertificates`, which
combines the calculus tail for `ω(n) ≥ 163` with certificates for `1 ≤ ω(n) < 163`.
`elementary_prime_count_term_le` consumes the proposition to bound a rescaled factor-count term.
-/
def ElementaryOmegaStatement : Prop :=
  ∀ n : ℕ,
    Odd n →
      750 ≤ n →
      ((NumberTheory.characterModulus n).primeFactors.card : ℝ) ≤
        elementaryOmegaConstant *
            Real.log (NumberTheory.characterModulus n) /
          Real.log (Real.log (NumberTheory.characterModulus n))

/-- For odd `n ≥ 750`, put `q = 4n`, `x = log q`, `y = loglog q`, and `C = 7/5`.
An `ElementaryOmegaStatement` proof gives `2 * ω(q) * y² / x ≤ 2 * C * y` by multiplying
`ω(q) ≤ C * x / y` by the nonnegative factor `2 * y² / x`. -/
theorem elementary_prime_count_term_le
    (hElem : ElementaryOmegaStatement) {n : ℕ}
    (hn : Odd n) (hn750 : 750 ≤ n) :
    2 * (NumberTheory.characterModulus n).primeFactors.card *
          (Real.log (Real.log (NumberTheory.characterModulus n))) ^ 2 /
        Real.log (NumberTheory.characterModulus n) ≤
      2 * elementaryOmegaConstant *
        Real.log (Real.log (NumberTheory.characterModulus n)) := by
  have hq : 3000 ≤ NumberTheory.characterModulus n := by
    unfold NumberTheory.characterModulus; omega
  have hpos := log_log_pos_of_le hq
  set x : ℝ := Real.log (NumberTheory.characterModulus n) with hx_def
  set y : ℝ := Real.log x with hy_def
  have hx : 0 < x := hpos.1
  have hy : 0 < y := hpos.2
  have homega := hElem n hn hn750
  have hfactor : 0 ≤ 2 * y ^ 2 / x := div_nonneg (by positivity) hx.le
  have hmul := mul_le_mul_of_nonneg_right homega hfactor
  have heqLeft :
    ((NumberTheory.characterModulus n).primeFactors.card : ℝ) * (2 * y ^ 2 / x) =
      2 * (NumberTheory.characterModulus n).primeFactors.card * y ^ 2 / x := by
    ring
  have heqRight :
    (elementaryOmegaConstant * x / y) *
        (2 * y ^ 2 / x) =
      2 * elementaryOmegaConstant * y := by
    field_simp [hx.ne', hy.ne']
  rw [← heqLeft, ← heqRight]
  exact hmul

end PseudoPrime.AnalyticNumberTheory.Arithmetic
