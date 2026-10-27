/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.Basic
public import PseudoPrime.Analysis.EulerCorrectionTailBounds
public import Mathlib.NumberTheory.LSeries.Deriv
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Complex.HalfPlane
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # Euler-series identities for higher logarithmic derivatives -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/--
Inputs: a complex sequence on the natural numbers, a derivative order, and a natural-number
argument.
Claim: Iterating `logMul` multiplies the original coefficient by the corresponding power of the
complex logarithm.
Proof: Induction matches the successor rules for function iteration and powers.
Role: converts coefficients of higher-order Euler series to real weights used in prime counting.
-/
theorem logMul_iterate_apply (n : ℕ) (f : ℕ → ℂ) (k : ℕ) :
    LSeries.logMul^[n] f k = (Complex.log k) ^ n * f k := by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq, pow_zero, one_mul]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change Complex.log k * (LSeries.logMul^[n] f k) = (Complex.log k) ^ (n + 1) * f k
    rw [ih]
    rw [pow_succ]
    ring

/--
Inputs: a Dirichlet character, a point with real part greater than `1`, and a derivative order.
Claim: The iterated derivative of the logarithmic derivative is a Dirichlet series whose
coefficients are the von Mangoldt function times powers of the complex logarithm.
Proof: Extend the Euler-product logarithmic-derivative formula on the right half-plane to
iterated derivatives and apply the corresponding mathlib formula.
Role: connects derivative lower bounds from local zero detection to the Euler series used in
zero-density estimates.
-/
theorem iteratedDeriv_logDeriv_eq_neg_twistedVonMangoldt_series {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s =
      -(((-1 : ℂ) ^ n) *
          LSeries
            (LSeries.logMul^[n]
              (fun k : ℕ ↦ χ (k : ZMod N) * (ArithmeticFunction.vonMangoldt k : ℂ)))
            s) := by
  let f : ℕ → ℂ := fun k ↦ χ (k : ZMod N) * (ArithmeticFunction.vonMangoldt k : ℂ)
  let U : Set ℂ := {z | (1 : EReal) < z.re}
  have hU : IsOpen U := by
    change IsOpen {z : ℂ | (1 : EReal) < z.re}
    exact Complex.isOpen_re_gt_EReal 1
  have hsU : s ∈ U := by
    change (1 : EReal) < (s.re : EReal)
    exact_mod_cast hs
  have hEq : Set.EqOn (LSeries f) (fun z ↦ -logDeriv (DirichletCharacter.LFunction χ) z) U := by
    intro z hz
    have hz' : 1 < z.re := by
      change (1 : EReal) < (z.re : EReal) at hz
      exact_mod_cast hz
    simpa only [f, logDeriv_apply, neg_div] using
      lSeries_twist_vonMangoldt_eq_neg_logDeriv_dirichletLFunction_of_one_lt_re χ hz'
  have hwithin := iteratedDerivWithin_congr (n := n) hEq
  have hleft := iteratedDerivWithin_of_isOpen (n := n) (f := LSeries f) hU
  have hright :=
    iteratedDerivWithin_of_isOpen (n := n) (f := fun z ↦
      -logDeriv (DirichletCharacter.LFunction χ) z) hU
  have hderiv :
    iteratedDeriv n (LSeries f) s =
      iteratedDeriv n (fun z ↦ -logDeriv (DirichletCharacter.LFunction χ) z) s := by
    calc
      iteratedDeriv n (LSeries f) s = iteratedDerivWithin n (LSeries f) U s := (hleft hsU).symm
      _ = iteratedDerivWithin n (fun z ↦ -logDeriv (DirichletCharacter.LFunction χ) z) U s :=
        hwithin hsU
      _ = iteratedDeriv n (fun z ↦ -logDeriv (DirichletCharacter.LFunction χ) z) s := hright hsU
  let τ : ℝ := (1 + s.re) / 2
  have hτ1 : 1 < τ := by
    dsimp only [τ]
    linarith only [hs]
  have hτs : τ < s.re := by
    dsimp only [τ]
    linarith only [hs]
  have hfτ : LSeriesSummable f (τ : ℂ) := by
    apply DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ
    simpa only [Complex.ofReal_re] using hτ1
  have hab : LSeries.abscissaOfAbsConv f < s.re := by
    have hle : LSeries.abscissaOfAbsConv f ≤ (τ : EReal) := by
      simpa only [Complex.ofReal_re] using hfτ.abscissaOfAbsConv_le
    have hts : (τ : EReal) < (s.re : EReal) := by exact_mod_cast hτs
    exact hle.trans_lt hts
  have hseries := LSeries_iteratedDeriv n (f := f) hab
  rw [hseries] at hderiv
  change
    (-1 : ℂ) ^ n * LSeries (LSeries.logMul^[n] f) s =
      iteratedDeriv n (-(logDeriv (DirichletCharacter.LFunction χ))) s at hderiv
  rw [iteratedDeriv_neg] at hderiv
  have hresult := congrArg (fun z : ℂ ↦ -z) hderiv.symm
  simpa only [neg_neg] using hresult

/--
Inputs: a Dirichlet character, a derivative order, and a positive natural-number coefficient.
Claim: Each term of the twisted higher-order von Mangoldt series is bounded by the untwisted
real weight $\Lambda(k)(\log k)^n/k^{\Re s}$.
Proof: Expand the coefficient using `logMul_iterate_apply` and use that character values have
norm at most `1`.
Role: provides a common nonnegative majorant when passing the iterated-derivative series to a
mean square over characters.
-/
theorem twistedVonMangoldt_log_term_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (n k : ℕ)
    {s : ℂ} (hk : 0 < k) :
    ‖LSeries.term
          (LSeries.logMul^[n] (fun j : ℕ ↦ χ (j : ZMod N) * (ArithmeticFunction.vonMangoldt j : ℂ)))
          s k‖ ≤
      ArithmeticFunction.vonMangoldt k * (Real.log k) ^ n / (k : ℝ) ^ s.re := by
  have hlog : ‖Complex.log (k : ℂ)‖ = Real.log k := by
    rw [← Complex.natCast_log]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg k)]
  have hLambda : ‖(ArithmeticFunction.vonMangoldt k : ℂ)‖ = ArithmeticFunction.vonMangoldt k := by
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hbase := DirichletCharacter.norm_le_one χ (k : ZMod N)
  rw [LSeries.term_of_ne_zero (Nat.ne_of_gt hk), logMul_iterate_apply, norm_div, norm_mul, norm_pow,
    hlog, norm_mul, hLambda, show ((k : ℂ)) = ((k : ℝ) : ℂ) from (Complex.ofReal_natCast k).symm,
    Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hk)]
  have hlogpow : 0 ≤ (Real.log k) ^ n := pow_nonneg (Real.log_natCast_nonneg k) n
  have hnumerator :
    (Real.log k) ^ n * (‖χ (k : ZMod N)‖ * ArithmeticFunction.vonMangoldt k) ≤
      ArithmeticFunction.vonMangoldt k * (Real.log k) ^ n := by
    calc
      (Real.log k) ^ n * (‖χ (k : ZMod N)‖ * ArithmeticFunction.vonMangoldt k) ≤
          (Real.log k) ^ n * (1 * ArithmeticFunction.vonMangoldt k) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hbase ArithmeticFunction.vonMangoldt_nonneg) hlogpow
      _ = ArithmeticFunction.vonMangoldt k * (Real.log k) ^ n := by ring
  have hden : 0 < (k : ℝ) ^ s.re := Real.rpow_pos_of_pos (by exact_mod_cast hk) _
  exact div_le_div_of_nonneg_right hnumerator (le_of_lt hden)

/--
Inputs: a derivative order, a positive natural index, and a complex argument `s`.

Claim: the norm of the corresponding untwisted differentiated Euler-series term equals its
positive von Mangoldt logarithmic weight at `s.re`.

Proof: rewrite the iterated logarithmic multiplier, identify the norm of the real logarithm, and
evaluate the norm of the complex power using its positive real base.

Role: transfers the coefficient energy of a finite Euler block to the real weight bound used by
the dyadic large-sieve estimate.
-/
theorem norm_vonMangoldt_logMul_term_eq (n k : ℕ) {s : ℂ} (hk : 0 < k) :
    ‖LSeries.term (LSeries.logMul^[n] (fun j : ℕ ↦ (ArithmeticFunction.vonMangoldt j : ℂ))) s k‖ =
      ArithmeticFunction.vonMangoldt k * (Real.log k) ^ n / (k : ℝ) ^ s.re := by
  have hlog : ‖Complex.log (k : ℂ)‖ = Real.log k := by
    rw [← Complex.natCast_log]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg k)]
  have hLambda : ‖(ArithmeticFunction.vonMangoldt k : ℂ)‖ = ArithmeticFunction.vonMangoldt k := by
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  rw [LSeries.term_of_ne_zero (Nat.ne_of_gt hk), logMul_iterate_apply, norm_div, norm_mul, norm_pow,
    hlog, hLambda, show ((k : ℂ)) = ((k : ℝ) : ℂ) from (Complex.ofReal_natCast k).symm,
    Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hk)]
  ring

/--
Inputs: a real number `σ > 1` and a derivative order `n`.
Claim: The weight `Λ(k) (log k)^n / k^σ` is summable over the natural numbers.
Proof: Use absolute convergence of the von Mangoldt Dirichlet series and finitely many
derivatives via `logMul`.
Role: supplies the nonnegative series used to control truncation errors for finite Dirichlet
polynomials.
-/
theorem summable_vonMangoldt_log_weight {σ : ℝ} (hσ : 1 < σ) (n : ℕ) :
    Summable (fun k : ℕ => ArithmeticFunction.vonMangoldt k * (Real.log k) ^ n / (k : ℝ) ^ σ) := by
  let g : ℕ → ℂ := fun k ↦ (ArithmeticFunction.vonMangoldt k : ℂ)
  let τ : ℝ := (1 + σ) / 2
  have hτ1 : 1 < τ := by
    dsimp only [τ]
    linarith only [hσ]
  have hτσ : τ < σ := by
    dsimp only [τ]
    linarith only [hσ]
  have hgτ : LSeriesSummable g (τ : ℂ) := by
    dsimp only [g]
    exact
      ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa only [Complex.ofReal_re] using hτ1)
  have hle : LSeries.abscissaOfAbsConv g ≤ (τ : EReal) := by
    simpa only [Complex.ofReal_re] using hgτ.abscissaOfAbsConv_le
  have hts : (τ : EReal) < (σ : EReal) := by exact_mod_cast hτσ
  have hEq := LSeries.abscissaOfAbsConv_logPowMul (f := g) (m := n)
  have hpow : LSeries.abscissaOfAbsConv (LSeries.logMul^[n] g) < σ := by
    calc
      LSeries.abscissaOfAbsConv (LSeries.logMul^[n] g) = LSeries.abscissaOfAbsConv g := hEq
      _ < σ := hle.trans_lt hts
  have hgs : LSeriesSummable (LSeries.logMul^[n] g) (σ : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa only [Complex.ofReal_re] using hpow)
  have hnormsumm : Summable (fun k : ℕ => ‖LSeries.term (LSeries.logMul^[n] g) (σ : ℂ) k‖) := by
    change Summable (fun k : ℕ => LSeries.term (LSeries.logMul^[n] g) (σ : ℂ) k) at hgs
    exact summable_norm_iff.mpr hgs
  have hterm :
    ∀ k : ℕ,
      ‖LSeries.term (LSeries.logMul^[n] g) (σ : ℂ) k‖ =
        ArithmeticFunction.vonMangoldt k * (Real.log k) ^ n / (k : ℝ) ^ σ := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp only [LSeries.term_zero, norm_zero, ArithmeticFunction.map_zero, CharP.cast_eq_zero,
        zero_mul, zero_div]
    · simpa only [Complex.ofReal_re] using
        norm_vonMangoldt_logMul_term_eq n k (s := (σ : ℂ)) (Nat.pos_of_ne_zero hk)
  exact hnormsumm.congr hterm

/--
Inputs: `σ > 1`, a derivative order `n`, and `k ≥ 2`.
Claim: Bound the von Mangoldt weight by an explicit coefficient times the power with exponent
`-(σ+1)/2`.
Proof: Use `Λ(k) ≤ log k` and `log k ≤ k^α/α`, choosing `α = (σ-1)/(2(n+1))` so the resulting
integral exponent exceeds `1`.
Role: gives a quantitative Dirichlet-series tail bound for choosing a truncation length near the
conductor.
-/
theorem vonMangoldt_log_weight_term_le_rpow {σ : ℝ} (hσ : 1 < σ) (n k : ℕ) (hk : 2 ≤ k) :
    ArithmeticFunction.vonMangoldt k * (Real.log k) ^ n / (k : ℝ) ^ σ ≤
      ((σ - 1) / (2 * ((n + 1 : ℕ) : ℝ))) ^ (-((n + 1 : ℕ) : ℝ)) * (k : ℝ) ^ (-(σ + 1) / 2) := by
  let α := (σ - 1) / (2 * ((n + 1 : ℕ) : ℝ))
  have hd : (0 : ℝ) < 2 * ((n + 1 : ℕ) : ℝ) :=
    mul_pos (by norm_num only) (Nat.cast_pos.mpr (Nat.succ_pos n))
  have hα : 0 < α := by
    dsimp only [α]
    exact div_pos (by linarith only [hσ]) hd
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hAlphaAlt : α = ((σ - 1) / 2) / ((n + 1 : ℕ) : ℝ) := by
    dsimp only [α]
    rw [← div_div]
  have hAlphaProduct : α * ((n + 1 : ℕ) : ℝ) = (σ - 1) / 2 := by
    rw [hAlphaAlt]
    exact div_mul_cancel₀ _ hn
  have hαexp : α * ((n + 1 : ℕ) : ℝ) - σ = -(σ + 1) / 2 := by
    rw [hAlphaProduct]
    ring
  have hk1 : 1 < k := lt_of_lt_of_le (by norm_num only) hk
  have hlog0 : 0 ≤ Real.log k := Real.log_natCast_nonneg k
  have hlambda : ArithmeticFunction.vonMangoldt k ≤ Real.log k :=
    ArithmeticFunction.vonMangoldt_le_log
  have hlog : Real.log k ≤ (k : ℝ) ^ α / α := Real.log_natCast_le_rpow_div k hα
  have hmajor0 : 0 ≤ (k : ℝ) ^ α / α := div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) α) hα.le
  have hpow : (Real.log k) ^ n ≤ ((k : ℝ) ^ α / α) ^ n := pow_le_pow_left₀ hlog0 hlog n
  have hnum :
    ArithmeticFunction.vonMangoldt k * (Real.log k) ^ n ≤ (((k : ℝ) ^ α) / α) ^ (n + 1) := by
    calc
      ArithmeticFunction.vonMangoldt k * (Real.log k) ^ n ≤ Real.log k * (Real.log k) ^ n :=
        mul_le_mul_of_nonneg_right hlambda (pow_nonneg hlog0 n)
      _ ≤ ((k : ℝ) ^ α / α) * ((k : ℝ) ^ α / α) ^ n :=
        mul_le_mul hlog hpow (pow_nonneg hlog0 n) hmajor0
      _ = ((k : ℝ) ^ α / α) ^ (n + 1) := by rw [← pow_succ']
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hk1
  have hden : 0 < (k : ℝ) ^ σ := Real.rpow_pos_of_pos hkpos _
  have hratio := div_le_div_of_nonneg_right hnum hden.le
  have hid :
    (((k : ℝ) ^ α / α) ^ (n + 1)) / (k : ℝ) ^ σ =
      α ^ (-((n + 1 : ℕ) : ℝ)) * (k : ℝ) ^ (-(σ + 1) / 2) := by
    rw [div_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg k) α (n + 1)]
    calc
      ((k : ℝ) ^ (α * ((n + 1 : ℕ) : ℝ)) / α ^ (n + 1)) / (k : ℝ) ^ σ =
          ((k : ℝ) ^ (α * ((n + 1 : ℕ) : ℝ)) / (k : ℝ) ^ σ) / α ^ (n + 1) :=
        by ring
      _ = (k : ℝ) ^ (α * ((n + 1 : ℕ) : ℝ) - σ) / α ^ (n + 1) := by rw [← Real.rpow_sub hkpos]
      _ = α ^ (-((n + 1 : ℕ) : ℝ)) * (k : ℝ) ^ (-(σ + 1) / 2) := by
        rw [hαexp, Real.rpow_neg hα.le, Real.rpow_natCast]
        rw [div_eq_mul_inv, mul_comm]
  simpa only [hid] using hratio

/--
Inputs: `σ > 1`, a logarithmic weight order `n`, and an integer `k ≥ 2`.
Claim: the logarithmic weight without a von Mangoldt factor is bounded by a power with exponent
`-(σ+1)/2` and an explicit coefficient.
Proof: apply `log k ≤ k^α/α` with `α = (σ-1)/(2 max(n,1))`, then use the exponent margin.
Role: supports a Chebyshev-averaged Euler-tail estimate in which the pointwise bound
`vonMangoldt k ≤ log k` is avoided.
-/
theorem log_pow_div_rpow_le_explicit {σ : ℝ} (hσ : 1 < σ) (n k : ℕ) (hk : 2 ≤ k) :
    (Real.log k) ^ n / (k : ℝ) ^ σ ≤
      ((σ - 1) / (2 * ((max n 1 : ℕ) : ℝ))) ^ (-(n : ℝ)) * (k : ℝ) ^ (-(σ + 1) / 2) := by
  let α := (σ - 1) / (2 * ((max n 1 : ℕ) : ℝ))
  have hmaxpos : 0 < ((max n 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_max_right n 1)
  have hα : 0 < α := by
    dsimp only [α]
    exact div_pos (by linarith only [hσ]) (mul_pos (by norm_num only) hmaxpos)
  have hnmax : (n : ℝ) ≤ ((max n 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_max_left n 1)
  have hratioMax : (n : ℝ) / ((max n 1 : ℕ) : ℝ) ≤ 1 := (div_le_one hmaxpos).2 hnmax
  have hαn : α * (n : ℝ) ≤ (σ - 1) / 2 := by
    dsimp only [α]
    calc
      _ = ((σ - 1) / 2) * ((n : ℝ) / ((max n 1 : ℕ) : ℝ)) := by ring
      _ ≤ (σ - 1) / 2 := mul_le_of_le_one_right (by positivity) hratioMax
  have hexp : α * (n : ℝ) - σ ≤ -(σ + 1) / 2 := by linarith only [hαn]
  have hk1 : 1 < k := lt_of_lt_of_le (by norm_num only) hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hk1
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1.le
  have hlog0 : 0 ≤ Real.log k := Real.log_natCast_nonneg k
  have hlog : Real.log k ≤ (k : ℝ) ^ α / α := Real.log_natCast_le_rpow_div k hα
  have hmajor0 : 0 ≤ (k : ℝ) ^ α / α := div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) α) hα.le
  have hpow : (Real.log k) ^ n ≤ ((k : ℝ) ^ α / α) ^ n := pow_le_pow_left₀ hlog0 hlog n
  have hden : 0 < (k : ℝ) ^ σ := Real.rpow_pos_of_pos hkpos σ
  have hratio := div_le_div_of_nonneg_right hpow hden.le
  have hid :
    ((k : ℝ) ^ α / α) ^ n / (k : ℝ) ^ σ = α ^ (-(n : ℝ)) * (k : ℝ) ^ (α * (n : ℝ) - σ) := by
    rw [div_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg k) α n]
    calc
      ((k : ℝ) ^ (α * (n : ℝ)) / α ^ n) / (k : ℝ) ^ σ =
          ((k : ℝ) ^ (α * (n : ℝ)) / (k : ℝ) ^ σ) / α ^ n :=
        by ring
      _ = (k : ℝ) ^ (α * (n : ℝ) - σ) / α ^ n := by rw [← Real.rpow_sub hkpos]
      _ = _ := by
        rw [Real.rpow_neg hα.le, Real.rpow_natCast]
        ring
  have hpower : (k : ℝ) ^ (α * (n : ℝ) - σ) ≤ (k : ℝ) ^ (-(σ + 1) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hkR hexp
  calc
    _ ≤ α ^ (-(n : ℝ)) * (k : ℝ) ^ (α * (n : ℝ) - σ) := by
      rw [← hid]
      exact hratio
    _ ≤ α ^ (-(n : ℝ)) * (k : ℝ) ^ (-(σ + 1) / 2) :=
      mul_le_mul_of_nonneg_left hpower (Real.rpow_nonneg hα.le _)

/--
Inputs: a positive exponential rate `η` and a natural logarithmic weight order `n`.
Claim: the logarithmic moment on `(1,∞)` equals `n! / η^(n+1)` after exponential damping.
Proof: substitute `y = log x` and evaluate the resulting Gamma integral at the natural
parameter `n + 1`.
Role: supplies the factorial-scale integral estimate needed to remove the extra `1/η` factor
from the pointwise Euler-tail bound.
-/
theorem integral_log_pow_exp_neg_mul_log_Ioi (η : ℝ) (n : ℕ) (hη : 0 < η) :
    (∫ x in Set.Ioi (1 : ℝ), x⁻¹ * (Real.log x) ^ n * Real.exp (-(η * Real.log x))) =
      (n.factorial : ℝ) / η ^ (n + 1) := by
  let g : ℝ → ℝ := fun y ↦ y ^ (n : ℝ) * Real.exp (-(η * y))
  have hcomp := MeasureTheory.integral_comp_log_Ioi g (a := (1 : ℝ)) zero_lt_one
  have hrewrite :
    (∫ x in Set.Ioi (1 : ℝ), x⁻¹ * (Real.log x) ^ n * Real.exp (-(η * Real.log x))) =
      ∫ x in Set.Ioi (1 : ℝ), x⁻¹ • g (Real.log x) := by
    apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioi
    filter_upwards [] with x hx
    dsimp only [g]
    rw [Real.rpow_natCast]
    simp only [smul_eq_mul, mul_assoc]
  rw [hrewrite, hcomp, Real.log_one]
  have hgamma :=
    Real.integral_rpow_mul_exp_neg_mul_Ioi (a := ((n : ℝ) + 1)) (r := η) (by positivity) hη
  have hnat : (n : ℝ) + 1 = (n + 1 : ℕ) := by norm_cast
  rw [hnat, Real.rpow_natCast] at hgamma
  rw [← hnat] at hgamma
  have hexp : (n : ℝ) + 1 - 1 = (n : ℝ) := by ring
  rw [hexp] at hgamma
  rw [Real.Gamma_nat_eq_factorial] at hgamma
  calc
    _ = (1 / η) ^ (n + 1) * (n.factorial : ℝ) := hgamma
    _ = (n.factorial : ℝ) / η ^ (n + 1) := by
      rw [one_div_pow, div_eq_mul_inv]
      ring

/-- For a positive rate `η` and order `n`, the damped logarithmic moment is integrable
on `(1,∞)`. Its positive Gamma integral rules out the nonintegrable case.
This supplies integrability for cutoff comparisons in the Euler-tail estimate. -/
theorem integrableOn_log_pow_exp_neg_mul_log_Ioi (η : ℝ) (n : ℕ) (hη : 0 < η) :
    MeasureTheory.IntegrableOn (fun x : ℝ ↦ x⁻¹ * (Real.log x) ^ n * Real.exp (-(η * Real.log x)))
      (Set.Ioi (1 : ℝ)) MeasureTheory.volume := by
  by_contra h
  have hz := MeasureTheory.integral_undef h
  rw [integral_log_pow_exp_neg_mul_log_Ioi η n hη] at hz
  exact (ne_of_gt (div_pos (Nat.cast_pos.mpr (Nat.factorial_pos n)) (pow_pos hη (n + 1)))) hz

/-- For `η > 0` and `1 ≤ N < x`, split the exponential rate in half and bound
one factor at the cutoff. Logarithm monotonicity gives the pointwise Chernoff majorant
used to compare the cutoff moment with a complete Gamma integral. -/
theorem log_pow_exp_neg_mul_log_le_half_rate_majorant (η N x : ℝ) (n : ℕ) (hη : 0 < η) (hN : 1 ≤ N)
    (hx : N < x) :
    x⁻¹ * (Real.log x) ^ n * Real.exp (-(η * Real.log x)) ≤
      Real.exp (-(η * Real.log N) / 2) *
        (x⁻¹ * (Real.log x) ^ n * Real.exp (-((η / 2) * Real.log x))) := by
  have hx1 : 1 < x := lt_of_le_of_lt hN hx
  have hxlog := Real.log_le_log (lt_of_lt_of_le zero_lt_one hN) (le_of_lt hx)
  have hcoef : 0 ≤ x⁻¹ * (Real.log x) ^ n :=
    mul_nonneg (inv_nonneg.mpr (le_of_lt (lt_trans zero_lt_one hx1)))
      (pow_nonneg (Real.log_nonneg hx1.le) n)
  have he :=
    Real.exp_le_exp.mpr
      (show -(η * Real.log x) / 2 ≤ -(η * Real.log N) / 2 by
        nlinarith only [mul_le_mul_of_nonneg_left hxlog hη.le])
  calc
    _ =
        (x⁻¹ * (Real.log x) ^ n * Real.exp (-((η / 2) * Real.log x))) *
          Real.exp (-(η * Real.log x) / 2) :=
      by
      rw [mul_assoc (x⁻¹ * (Real.log x) ^ n), ← Real.exp_add]
      congr 2
      ring
    _ ≤
        (x⁻¹ * (Real.log x) ^ n * Real.exp (-((η / 2) * Real.log x))) *
          Real.exp (-(η * Real.log N) / 2) :=
      mul_le_mul_of_nonneg_left he (mul_nonneg hcoef (Real.exp_pos _).le)
    _ = _ := mul_comm _ _

/-- For a positive rate and a cutoff `N ≥ 1`, the logarithmic moment above `N`
is at most its complete moment above one. Integrability and nonnegativity justify
restriction monotonicity. This removes the cutoff from the half-rate majorant. -/
theorem integral_log_pow_exp_neg_mul_log_Ioi_mono (η N : ℝ) (n : ℕ) (hη : 0 < η) (hN : 1 ≤ N) :
    (∫ x in Set.Ioi N, x⁻¹ * (Real.log x) ^ n * Real.exp (-(η * Real.log x))) ≤
      ∫ x in Set.Ioi (1 : ℝ), x⁻¹ * (Real.log x) ^ n * Real.exp (-(η * Real.log x)) := by
  apply MeasureTheory.setIntegral_mono_set (integrableOn_log_pow_exp_neg_mul_log_Ioi η n hη)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    exact
      mul_nonneg
        (mul_nonneg (inv_nonneg.mpr (le_of_lt (lt_trans zero_lt_one hx)))
          (pow_nonneg (Real.log_nonneg hx.le) n))
        (Real.exp_pos _).le
  · exact Filter.Eventually.of_forall (Set.Ioi_subset_Ioi hN)

/-- For a positive rate `η`, order `n`, and cutoff `N ≥ 1`, the incomplete
logarithmic moment is bounded by `exp(-η log N / 2) * n! / (η / 2)^(n+1)`.
Integrate the pointwise half-rate majorant and evaluate its complete Gamma integral.
This gives an explicit cutoff estimate for the von Mangoldt Euler tail. -/
theorem integral_log_pow_exp_neg_mul_log_Ioi_le_half_rate (η N : ℝ) (n : ℕ) (hη : 0 < η)
    (hN : 1 ≤ N) :
    (∫ x in Set.Ioi N, x⁻¹ * (Real.log x) ^ n * Real.exp (-(η * Real.log x))) ≤
      Real.exp (-(η * Real.log N) / 2) * ((n.factorial : ℝ) / (η / 2) ^ (n + 1)) := by
  have hf := (integrableOn_log_pow_exp_neg_mul_log_Ioi η n hη).mono_set (Set.Ioi_subset_Ioi hN)
  have hg :=
    (integrableOn_log_pow_exp_neg_mul_log_Ioi (η / 2) n (half_pos hη)).mono_set
      (Set.Ioi_subset_Ioi hN)
  have hfirst :=
    MeasureTheory.setIntegral_mono_on hf (hg.const_mul (Real.exp (-(η * Real.log N) / 2)))
      measurableSet_Ioi (fun x hx ↦ log_pow_exp_neg_mul_log_le_half_rate_majorant η N x n hη hN hx)
  rw [MeasureTheory.integral_const_mul] at hfirst
  have hsecond :=
    mul_le_mul_of_nonneg_left
      (integral_log_pow_exp_neg_mul_log_Ioi_mono (η / 2) N n (half_pos hη) hN)
      (Real.exp_pos (-(η * Real.log N) / 2)).le
  rw [integral_log_pow_exp_neg_mul_log_Ioi (η / 2) n (half_pos hη)] at hsecond
  exact hfirst.trans hsecond

/-- For a positive rate `η` and natural order `n`, factorial normalization
of the complete half-rate moment equals `2^(n+1)`. Cancel the nonzero rate and
factorial explicitly. This isolates the exponential loss in the normalized tail. -/
theorem log_pow_exp_half_rate_normalization (η : ℝ) (n : ℕ) (hη : 0 < η) :
    η ^ (n + 1) / (n.factorial : ℝ) * ((n.factorial : ℝ) / (η / 2) ^ (n + 1)) =
      (2 : ℝ) ^ (n + 1) := by
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [div_pow, div_div_eq_mul_div]
  calc
    _ =
        (2 : ℝ) ^ (n + 1) * (η ^ (n + 1) * (η ^ (n + 1))⁻¹) *
          ((n.factorial : ℝ) * (n.factorial : ℝ)⁻¹) :=
      by
      simp only [div_eq_mul_inv]
      ring
    _ = _ := by
      rw [mul_inv_cancel₀ (pow_ne_zero _ (ne_of_gt hη)), mul_inv_cancel₀ hf, mul_one, mul_one]

/-- For a positive rate and cutoff at least one, the factorial-normalized
incomplete logarithmic moment is at most `2^(n+1) * exp(-η log N / 2)`.
Multiply the half-rate estimate by its nonnegative normalization factor.
This estimate has no inverse-rate prefactor and feeds the quantitative Euler cutoff. -/
theorem normalized_integral_log_pow_exp_neg_mul_log_Ioi_le (η N : ℝ) (n : ℕ) (hη : 0 < η)
    (hN : 1 ≤ N) :
    η ^ (n + 1) / (n.factorial : ℝ) *
        (∫ x in Set.Ioi N, x⁻¹ * (Real.log x) ^ n * Real.exp (-(η * Real.log x))) ≤
      (2 : ℝ) ^ (n + 1) * Real.exp (-(η * Real.log N) / 2) := by
  have h :=
    mul_le_mul_of_nonneg_left (integral_log_pow_exp_neg_mul_log_Ioi_le_half_rate η N n hη hN)
      (div_nonneg (pow_nonneg hη.le (n + 1)) (Nat.cast_nonneg n.factorial))
  calc
    _ ≤
        η ^ (n + 1) / (n.factorial : ℝ) *
          (Real.exp (-(η * Real.log N) / 2) * ((n.factorial : ℝ) / (η / 2) ^ (n + 1))) :=
      h
    _ = _ := by rw [mul_left_comm, log_pow_exp_half_rate_normalization η n hη, mul_comm]

/--
Inputs: a dyadic block index, a logarithmic weight order, and a positive exponent.
Claim: the von Mangoldt-weighted block is bounded by the Chebyshev mass of the block times the
largest logarithmic weight and smallest denominator on that block.
Proof: bound each weight by its endpoint values, then apply the explicit Chebyshev bound for the
sum of the von Mangoldt function.
Role: supplies block estimates for a sharper Euler-tail bound without the pointwise
`vonMangoldt ≤ log` loss.
-/
theorem vonMangoldt_log_weight_dyadic_block_le (k n : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    (∑ m ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
        ArithmeticFunction.vonMangoldt m * (Real.log m) ^ n / (m : ℝ) ^ σ) ≤
      (Real.log 4 + 4) * (2 ^ (k + 1) : ℝ) * (Real.log (2 ^ (k + 1) : ℝ)) ^ n /
        (2 ^ k : ℝ) ^ σ := by
  let lo : ℝ := ((2 ^ k : ℕ) : ℝ)
  let hi : ℝ := ((2 ^ (k + 1) : ℕ) : ℝ)
  have hlo : 0 < lo := by
    dsimp only [lo]; positivity
  have hhi : 0 < hi := by
    dsimp only [hi]; positivity
  have hlo1 : 1 ≤ lo := by
    dsimp only [lo]
    exact_mod_cast Nat.one_le_pow k 2 (by omega)
  have hhi1 : 1 ≤ hi := by
    dsimp only [hi]
    exact_mod_cast Nat.one_le_pow (k + 1) 2 (by omega)
  have hloghi : 0 ≤ Real.log hi := Real.log_nonneg hhi1
  have hsum :
    (∑ m ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), (ArithmeticFunction.vonMangoldt m : ℝ)) ≤
      (Real.log 4 + 4) * hi := by
    calc
      _ ≤ ∑ m ∈ Finset.Icc 0 (2 ^ (k + 1)), (ArithmeticFunction.vonMangoldt m : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          simp only [Finset.mem_Ico, Finset.mem_Icc] at hm ⊢
          omega
        · intro m hm _hnot
          exact ArithmeticFunction.vonMangoldt_nonneg
      _ = Chebyshev.psi hi := by
        dsimp only [hi]
        rw [Chebyshev.psi_eq_sum_Icc]
        simp only [Nat.floor_natCast]
      _ ≤ (Real.log 4 + 4) * hi := by
        dsimp only [hi]
        exact Chebyshev.psi_le_const_mul_self (by positivity)
  have hweighted :
    ∀ m ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
      ArithmeticFunction.vonMangoldt m * (Real.log m) ^ n / (m : ℝ) ^ σ ≤
        ArithmeticFunction.vonMangoldt m * (Real.log hi) ^ n / lo ^ σ := by
    intro m hm
    have hmlo : lo ≤ (m : ℝ) := by
      dsimp only [lo]
      exact_mod_cast (Finset.mem_Ico.mp hm).1
    have hmhi : (m : ℝ) ≤ hi := by
      dsimp only [hi]
      exact_mod_cast (Finset.mem_Ico.mp hm).2.le
    have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le hlo hmlo
    have hlog : Real.log (m : ℝ) ≤ Real.log hi := Real.log_le_log hmpos hmhi
    have hpowlog : (Real.log (m : ℝ)) ^ n ≤ (Real.log hi) ^ n :=
      pow_le_pow_left₀ (Real.log_natCast_nonneg m) hlog n
    have hden : lo ^ σ ≤ (m : ℝ) ^ σ := Real.rpow_le_rpow hlo.le hmlo hσ.le
    have hdenpos : 0 < lo ^ σ := Real.rpow_pos_of_pos hlo σ
    have huppernum : 0 ≤ ArithmeticFunction.vonMangoldt m * (Real.log hi) ^ n :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (pow_nonneg hloghi n)
    calc
      _ ≤ (ArithmeticFunction.vonMangoldt m * (Real.log hi) ^ n) / (m : ℝ) ^ σ := by
        exact
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpowlog ArithmeticFunction.vonMangoldt_nonneg)
            (Real.rpow_pos_of_pos hmpos σ).le
      _ ≤ (ArithmeticFunction.vonMangoldt m * (Real.log hi) ^ n) / lo ^ σ := by
        exact div_le_div_of_nonneg_left huppernum hdenpos hden
  calc
    _ ≤
        ∑ m ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
          ArithmeticFunction.vonMangoldt m * (Real.log hi) ^ n / lo ^ σ :=
      by
      apply Finset.sum_le_sum
      intro m hm
      exact hweighted m hm
    _ =
        (Real.log hi) ^ n / lo ^ σ *
          ∑ m ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), (ArithmeticFunction.vonMangoldt m : ℝ) :=
      by
      calc
        _ =
            ∑ m ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
              ArithmeticFunction.vonMangoldt m * ((Real.log hi) ^ n / lo ^ σ) :=
          by
          apply Finset.sum_congr rfl
          intro m hm
          ring
        _ =
            (∑ m ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), (ArithmeticFunction.vonMangoldt m : ℝ)) *
              ((Real.log hi) ^ n / lo ^ σ) :=
          by rw [Finset.sum_mul]
        _ = _ := by ring
    _ ≤ (Real.log hi) ^ n / lo ^ σ * ((Real.log 4 + 4) * hi) := by
      calc
        _ =
            ((Real.log hi) ^ n / lo ^ σ) *
              (∑ m ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), (ArithmeticFunction.vonMangoldt m : ℝ)) :=
          by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
      dsimp only [lo, hi]
      norm_cast
      ring

/--
Inputs: a coefficient sequence, a differentiable weight on a finite interval, and bounds for its
partial sums.
Claim: if the weight is nonnegative at both endpoints and nonincreasing, its weighted sum is
bounded by the upper endpoint contribution and an integral against the partial-sum majorant.
Proof: apply Abel summation, discard the nonpositive lower endpoint term, and compare the integral
using the sign of the derivative.
Role: converts Chebyshev bounds for von Mangoldt partial sums into finite weighted tail estimates.
-/
theorem finite_sum_mul_le_of_partial_sum_bound (c : ℕ → ℝ) {f : ℝ → ℝ} {N M : ℕ} {C : ℝ}
    (hNM : N ≤ M) (hf_diff : ∀ t ∈ Set.Icc (N : ℝ) M, DifferentiableAt ℝ f t)
    (hf_int : MeasureTheory.IntegrableOn (deriv f) (Set.Icc (N : ℝ) M))
    (hF_int :
      MeasureTheory.IntegrableOn (fun t ↦ -deriv f t * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k))
        (Set.Ioc (N : ℝ) M))
    (hG_int : MeasureTheory.IntegrableOn (fun t ↦ -deriv f t * (C * t)) (Set.Ioc (N : ℝ) M))
    (hNf : 0 ≤ f N) (hMf : 0 ≤ f M) (hderiv : ∀ t ∈ Set.Ioc (N : ℝ) M, deriv f t ≤ 0)
    (hPN : 0 ≤ ∑ k ∈ Finset.Icc 0 N, c k) (hPM : ∑ k ∈ Finset.Icc 0 M, c k ≤ C * M)
    (hP : ∀ t ∈ Set.Ioc (N : ℝ) M, ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k ≤ C * t) :
    ∑ k ∈ Finset.Ioc N M, f k * c k ≤
      C * (f M * M) + ∫ t in Set.Ioc (N : ℝ) M, -deriv f t * (C * t) := by
  let P : ℝ → ℝ := fun t ↦ ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k
  have habelRaw := sum_mul_eq_sub_sub_integral_mul' c hNM hf_diff hf_int
  have habel :
    (∑ k ∈ Finset.Ioc N M, f k * c k) =
      f M * (∑ k ∈ Finset.Icc 0 M, c k) - f N * (∑ k ∈ Finset.Icc 0 N, c k) -
        ∫ t in Set.Ioc (N : ℝ) M, deriv f t * P t := by
    simpa only [P] using habelRaw
  have hF_eq :
    (∫ t in Set.Ioc (N : ℝ) M, -deriv f t * P t) =
      -(∫ t in Set.Ioc (N : ℝ) M, deriv f t * P t) := by
    rw [show (fun t ↦ -deriv f t * P t) = (fun t ↦ -(deriv f t * P t)) by
        funext t; simp only [neg_mul]]
    exact MeasureTheory.integral_neg _
  have habel' :
    (∑ k ∈ Finset.Ioc N M, f k * c k) =
      f M * (∑ k ∈ Finset.Icc 0 M, c k) - f N * (∑ k ∈ Finset.Icc 0 N, c k) +
        ∫ t in Set.Ioc (N : ℝ) M, -deriv f t * P t := by
    calc
      _ =
          f M * (∑ k ∈ Finset.Icc 0 M, c k) - f N * (∑ k ∈ Finset.Icc 0 N, c k) -
            ∫ t in Set.Ioc (N : ℝ) M, deriv f t * P t :=
        habel
      _ = _ := by
        rw [hF_eq]; ring
  have hmono : ∀ t ∈ Set.Ioc (N : ℝ) M, -deriv f t * P t ≤ -deriv f t * (C * t) := by
    intro t ht
    apply mul_le_mul_of_nonneg_left (hP t ht)
    exact neg_nonneg.mpr (hderiv t ht)
  have hint :
    (∫ t in Set.Ioc (N : ℝ) M, -deriv f t * P t) ≤ ∫ t in Set.Ioc (N : ℝ) M, -deriv f t * (C * t) :=
    MeasureTheory.setIntegral_mono_on hF_int hG_int measurableSet_Ioc hmono
  have hlower : 0 ≤ f N * (∑ k ∈ Finset.Icc 0 N, c k) := mul_nonneg hNf hPN
  have hendpoint :
    f M * (∑ k ∈ Finset.Icc 0 M, c k) - f N * (∑ k ∈ Finset.Icc 0 N, c k) ≤ C * (f M * M) := by
    calc
      _ ≤ f M * (∑ k ∈ Finset.Icc 0 M, c k) := sub_le_self _ hlower
      _ ≤ f M * (C * M) := mul_le_mul_of_nonneg_left hPM hMf
      _ = _ := by ring
  calc
    _ =
        f M * (∑ k ∈ Finset.Icc 0 M, c k) - f N * (∑ k ∈ Finset.Icc 0 N, c k) +
          ∫ t in Set.Ioc (N : ℝ) M, -deriv f t * P t :=
      habel'
    _ ≤ C * (f M * M) + ∫ t in Set.Ioc (N : ℝ) M, -deriv f t * (C * t) := add_le_add hendpoint hint

/--
Inputs: a nonnegative real argument.
Claim: the partial sum of the von Mangoldt function through its floor is at most
`(log 4 + 4) * x`.
Proof: rewrite the sum as Chebyshev's `psi` function and apply its explicit linear bound.
Role: supplies the partial-sum majorant required by finite Abel estimates.
-/
theorem vonMangoldt_partial_sum_le_chebyshev_bound (x : ℝ) (hx : 0 ≤ x) :
    (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt k) ≤ (Real.log 4 + 4) * x := by
  rw [← Chebyshev.psi_eq_sum_Icc]
  exact Chebyshev.psi_le_const_mul_self hx

/--
Inputs: a natural-number endpoint.
Claim: the von Mangoldt partial sum through the endpoint is nonnegative.
Proof: identify the sum with Chebyshev's `psi` function and use its nonnegativity.
Role: controls the lower endpoint term in finite Abel summation.
-/
theorem vonMangoldt_nat_partial_sum_nonneg (N : ℕ) :
    0 ≤ ∑ k ∈ Finset.Icc 0 N, ArithmeticFunction.vonMangoldt k := by
  have h := Chebyshev.psi_nonneg (N : ℝ)
  rw [Chebyshev.psi_eq_sum_Icc] at h
  simpa only [Nat.floor_natCast] using h

/--
Inputs: a differentiable weight on a finite natural interval with nonpositive derivative.
Claim: its von Mangoldt-weighted sum is bounded using Chebyshev's linear partial-sum estimate.
Proof: apply Abel summation and bound the partial sums with Chebyshev's estimate.
Role: provides the finite interval estimate needed to pass from Euler tails to Gamma integrals.
-/
theorem finite_vonMangoldt_weighted_sum_le_of_decreasing {f : ℝ → ℝ} {N M : ℕ} (hNM : N ≤ M)
    (hf_diff : ∀ t ∈ Set.Icc (N : ℝ) M, DifferentiableAt ℝ f t)
    (hf_int : MeasureTheory.IntegrableOn (deriv f) (Set.Icc (N : ℝ) M)) (hNf : 0 ≤ f N)
    (hMf : 0 ≤ f M) (hderiv : ∀ t ∈ Set.Ioc (N : ℝ) M, deriv f t ≤ 0) :
    ∑ k ∈ Finset.Ioc N M, f k * ArithmeticFunction.vonMangoldt k ≤
      (Real.log 4 + 4) * (f M * M) +
        ∫ t in Set.Ioc (N : ℝ) M, -deriv f t * ((Real.log 4 + 4) * t) := by
  have hnegint : MeasureTheory.IntegrableOn (fun t ↦ -deriv f t) (Set.Icc (N : ℝ) M) := hf_int.neg
  have hFcc :=
    integrableOn_mul_sum_Icc (m := 0) ArithmeticFunction.vonMangoldt (Nat.cast_nonneg N) hnegint
  have hF_int :
    MeasureTheory.IntegrableOn
      (fun t ↦ -deriv f t * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt k))
      (Set.Ioc (N : ℝ) M) :=
    hFcc.mono_set Set.Ioc_subset_Icc_self
  have hGcc :
    MeasureTheory.IntegrableOn (fun t ↦ -deriv f t * ((Real.log 4 + 4) * t))
      (Set.Icc (N : ℝ) M) := by
    apply hnegint.mul_continuousOn
    · fun_prop
    · exact isCompact_Icc
  have hG_int :
    MeasureTheory.IntegrableOn (fun t ↦ -deriv f t * ((Real.log 4 + 4) * t)) (Set.Ioc (N : ℝ) M) :=
    hGcc.mono_set Set.Ioc_subset_Icc_self
  have hPN := vonMangoldt_nat_partial_sum_nonneg N
  have hPM : (∑ k ∈ Finset.Icc 0 M, ArithmeticFunction.vonMangoldt k) ≤ (Real.log 4 + 4) * M := by
    have h := vonMangoldt_partial_sum_le_chebyshev_bound (M : ℝ) (Nat.cast_nonneg M)
    simpa only [Nat.floor_natCast] using h
  have hP :
    ∀ t ∈ Set.Ioc (N : ℝ) M,
      ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt k ≤ (Real.log 4 + 4) * t := by
    intro t ht
    apply vonMangoldt_partial_sum_le_chebyshev_bound
    exact le_trans (Nat.cast_nonneg N) (le_of_lt (Set.mem_Ioc.mp ht).1)
  exact
    finite_sum_mul_le_of_partial_sum_bound ArithmeticFunction.vonMangoldt hNM hf_diff hf_int hF_int
      hG_int hNf hMf hderiv hPN hPM hP

/--
Inputs: a real exponent `σ`, a natural logarithmic order, and a nonzero real argument.
Claim: the derivative of `(log x)^n * x^(-σ)` is given by the product and power rules.
Proof: differentiate the logarithmic power and real power separately, then normalize the result.
Role: supplies the derivative formula for the Chebyshev-Abel weight.
-/
theorem log_pow_mul_rpow_hasDerivAt (σ x : ℝ) (n : ℕ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ (Real.log y) ^ n * y ^ (-σ))
      (((n : ℝ) * (Real.log x) ^ (n - 1) / x) * x ^ (-σ) - σ * (Real.log x) ^ n * x ^ (-σ - 1))
      x := by
  have hlog := Real.hasDerivAt_log hx
  have hpow := hlog.pow n
  have hrpow := Real.hasDerivAt_rpow_const (x := x) (p := -σ) (Or.inl hx)
  convert hpow.mul hrpow using 1
  simp only [Pi.pow_apply]
  ring_nf

/--
Inputs: `σ ≥ 0`, `x ≥ 1`, a natural order `n`, and `n ≤ σ * log x`.
Claim: the derivative of `(log x)^n * x^(-σ)` is nonpositive at `x`.
Proof: use the explicit derivative formula and factor out nonnegative powers of `log x` and `x`.
Role: establishes the decrease condition for finite von Mangoldt tail estimates.
-/
theorem deriv_log_pow_mul_rpow_nonpos {σ x : ℝ} (hσ : 0 ≤ σ) (hx : 1 ≤ x) (n : ℕ)
    (hn : (n : ℝ) ≤ σ * Real.log x) : deriv (fun y : ℝ ↦ (Real.log y) ^ n * y ^ (-σ)) x ≤ 0 := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hxpow : 0 ≤ x ^ (-σ - 1) := Real.rpow_nonneg hxpos.le _
  have hderiv := log_pow_mul_rpow_hasDerivAt σ x n (ne_of_gt hxpos)
  rw [hderiv.deriv]
  cases n with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, pow_zero, zero_div, mul_one]
    simpa only [zero_sub] using (neg_nonpos.mpr (mul_nonneg hσ hxpow))
  | succ m =>
    have hL : 0 ≤ (Real.log x) ^ m := pow_nonneg hlog _
    have hinv : x⁻¹ = x ^ (-1 : ℝ) := by rw [Real.rpow_neg hxpos.le, Real.rpow_one]
    have hexp : x ^ (-1 : ℝ) * x ^ (-σ) = x ^ (-σ - 1) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      ring
    have hfactor :
      (↑(m + 1) * (Real.log x) ^ ((m + 1) - 1) / x) * x ^ (-σ) -
          σ * (Real.log x) ^ (m + 1) * x ^ (-σ - 1) =
        (Real.log x) ^ m * x ^ (-σ - 1) * ((↑(m + 1) : ℝ) - σ * Real.log x) := by
      rw [show (m + 1) - 1 = m by omega, pow_succ, div_eq_mul_inv, hinv]
      calc
        _ =
            (↑(m + 1) * (Real.log x) ^ m) * (x ^ (-1 : ℝ) * x ^ (-σ)) -
              σ * ((Real.log x) ^ m * Real.log x) * x ^ (-σ - 1) :=
          by ring
        _ = _ := by
          rw [hexp]; ring
    rw [hfactor]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hL hxpow) (sub_nonpos.mpr hn)

/--
Inputs: `σ ≥ 0`, a cutoff `N ≥ 1`, a natural order `n`, and `n ≤ σ * log N`.
Claim: the derivative of `(log x)^n * x^(-σ)` is nonpositive throughout every interval starting
at `N`.
Proof: use monotonicity of the logarithm to extend the derivative sign condition from `N` to each
point of the interval.
Role: supplies the monotonicity hypothesis for finite Chebyshev-Abel estimates of Euler tails.
-/
theorem deriv_log_pow_mul_rpow_nonpos_on {σ : ℝ} {N M : ℕ} (n : ℕ) (hσ : 0 ≤ σ) (hN : 1 ≤ N)
    (hn : (n : ℝ) ≤ σ * Real.log N) :
    ∀ x ∈ Set.Icc (N : ℝ) M, deriv (fun y : ℝ ↦ (Real.log y) ^ n * y ^ (-σ)) x ≤ 0 := by
  intro x hx
  apply deriv_log_pow_mul_rpow_nonpos hσ
  · exact le_trans (by exact_mod_cast hN) hx.1
  · calc
      (n : ℝ) ≤ σ * Real.log N := hn
      _ ≤ σ * Real.log x := by
        apply mul_le_mul_of_nonneg_left _ hσ
        exact Real.log_le_log (by positivity) hx.1

/--
Inputs: a real exponent `σ`, a natural logarithmic order, and an integer interval starting at
`N ≥ 1`.
Claim: the derivative of `(log x)^n * x^(-σ)` is integrable on the interval.
Proof: rewrite the derivative using its explicit formula, establish continuity away from zero, and
use integrability of continuous functions on compact intervals.
Role: discharges the finite-interval integrability condition in Chebyshev-Abel tail estimates.
-/
theorem log_pow_mul_rpow_deriv_integrableOn_Icc {σ : ℝ} {N M : ℕ} (n : ℕ) (hN : 1 ≤ N) :
    MeasureTheory.IntegrableOn (deriv (fun y : ℝ ↦ (Real.log y) ^ n * y ^ (-σ)))
      (Set.Icc (N : ℝ) M) := by
  let s : Set ℝ := Set.Icc (N : ℝ) M
  let g : ℝ → ℝ := fun x =>
    ((n : ℝ) * (Real.log x) ^ (n - 1) * x⁻¹) * x ^ (-σ) - σ * (Real.log x) ^ n * x ^ (-σ - 1)
  have hid : ContinuousOn (fun x : ℝ ↦ x) s := continuousOn_id
  have hpos : ∀ x ∈ s, 0 < x := by
    intro x hx
    exact lt_of_lt_of_le zero_lt_one (le_trans (by exact_mod_cast hN) hx.1)
  have hlog : ContinuousOn Real.log s :=
    Real.continuousOn_log.mono
      (by
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_gt (hpos x hx))
  have hinv : ContinuousOn (fun x : ℝ ↦ x⁻¹) s :=
    hid.inv₀
      (by
        intro x hx
        exact ne_of_gt (hpos x hx))
  have hrpow : ContinuousOn (fun x : ℝ ↦ x ^ (-σ)) s :=
    hid.rpow_const
      (by
        intro x hx
        exact Or.inl (ne_of_gt (hpos x hx)))
  have hrpow' : ContinuousOn (fun x : ℝ ↦ x ^ (-σ - 1)) s :=
    hid.rpow_const
      (by
        intro x hx
        exact Or.inl (ne_of_gt (hpos x hx)))
  have hlogpow : ContinuousOn (fun x : ℝ ↦ (Real.log x) ^ (n - 1)) s := hlog.pow _
  have hlogpow' : ContinuousOn (fun x : ℝ ↦ (Real.log x) ^ n) s := hlog.pow _
  have hg : ContinuousOn g s := by
    dsimp only [g]
    fun_prop
  have heq : ∀ x ∈ s, deriv (fun y : ℝ ↦ (Real.log y) ^ n * y ^ (-σ)) x = g x := by
    intro x hx
    have hd := log_pow_mul_rpow_hasDerivAt σ x n (ne_of_gt (hpos x hx))
    dsimp only [g]
    rw [hd.deriv]
    ring
  have hderiv : ContinuousOn (deriv (fun y : ℝ ↦ (Real.log y) ^ n * y ^ (-σ))) s := hg.congr heq
  have hint : MeasureTheory.IntegrableOn (deriv (fun y : ℝ ↦ (Real.log y) ^ n * y ^ (-σ))) s :=
    hderiv.integrableOn_compact isCompact_Icc
  simpa only [s] using hint

/--
Inputs: `σ ≥ 0`, integers `1 ≤ N ≤ M`, an order `n`, and `n ≤ σ * log N`.
Claim: the finite von Mangoldt sum with weight `(log k)^n * k^(-σ)` is bounded by its upper
endpoint term and a Chebyshev-Abel integral.
Proof: establish differentiability, integrability, endpoint nonnegativity, and derivative
monotonicity for the weight, then apply the finite Chebyshev-Abel estimate.
Role: gives the concrete finite-tail estimate needed before taking the cutoff to infinity.
-/
theorem finite_vonMangoldt_log_pow_rpow_le_of_decreasing {σ : ℝ} {N M : ℕ} (n : ℕ) (hσ : 0 ≤ σ)
    (hN : 1 ≤ N) (hNM : N ≤ M) (hn : (n : ℝ) ≤ σ * Real.log N) :
    (∑ k ∈ Finset.Ioc N M,
        (Real.log (k : ℝ)) ^ n * (k : ℝ) ^ (-σ) * ArithmeticFunction.vonMangoldt k) ≤
      (Real.log 4 + 4) * ((Real.log (M : ℝ)) ^ n * (M : ℝ) ^ (-σ) * M) +
        ∫ t in Set.Ioc (N : ℝ) M,
          -deriv (fun y : ℝ ↦ (Real.log y) ^ n * y ^ (-σ)) t * ((Real.log 4 + 4) * t) := by
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := le_trans hNreal (by exact_mod_cast hNM)
  have hdiff :
    ∀ t ∈ Set.Icc (N : ℝ) M, DifferentiableAt ℝ (fun y : ℝ ↦ (Real.log y) ^ n * y ^ (-σ)) t := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one (le_trans hNreal ht.1)
    exact (log_pow_mul_rpow_hasDerivAt σ t n (ne_of_gt htpos)).differentiableAt
  have hint := log_pow_mul_rpow_deriv_integrableOn_Icc (σ := σ) (N := N) (M := M) n hN
  have hNf : 0 ≤ (Real.log (N : ℝ)) ^ n * (N : ℝ) ^ (-σ) :=
    mul_nonneg (pow_nonneg (Real.log_nonneg hNreal) n) (Real.rpow_nonneg (by positivity) _)
  have hMf : 0 ≤ (Real.log (M : ℝ)) ^ n * (M : ℝ) ^ (-σ) :=
    mul_nonneg (pow_nonneg (Real.log_nonneg hMreal) n) (Real.rpow_nonneg (by positivity) _)
  apply finite_vonMangoldt_weighted_sum_le_of_decreasing hNM hdiff hint hNf hMf
  intro t ht
  exact
    deriv_log_pow_mul_rpow_nonpos_on n hσ hN hn t
      ⟨le_of_lt (Set.mem_Ioc.mp ht).1, (Set.mem_Ioc.mp ht).2⟩

/--
Inputs: integers `1 ≤ N ≤ M`, an order `n`, and an exponent `σ`.
Claim: the integral of the derivative of `x * (log x)^n * x^(-σ)` on `[N,M]` equals its endpoint
difference.
Proof: apply the interval product rule for integrals to the identity function and the logarithmic
power weight, using the explicit derivative integrability result.
Role: rewrites the Chebyshev-Abel integral into endpoint and incomplete-Gamma terms.
-/
theorem log_pow_rpow_product_integral_eq_endpoints {σ : ℝ} {N M : ℕ} (n : ℕ) (hN : 1 ≤ N)
    (hNM : N ≤ M) :
    ∫ t in (N : ℝ)..(M : ℝ),
        (Real.log t) ^ n * t ^ (-σ) + t * deriv (fun y : ℝ ↦ (Real.log y) ^ n * y ^ (-σ)) t =
      (M : ℝ) * ((Real.log (M : ℝ)) ^ n * (M : ℝ) ^ (-σ)) -
        (N : ℝ) * ((Real.log (N : ℝ)) ^ n * (N : ℝ) ^ (-σ)) := by
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hMreal : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
  have hderivint := log_pow_mul_rpow_deriv_integrableOn_Icc (σ := σ) (N := N) (M := M) n hN
  have hfderiv :
    ∀ x ∈ Set.uIcc (N : ℝ) M,
      HasDerivAt (fun y : ℝ ↦ (Real.log y) ^ n * y ^ (-σ))
        (deriv (fun y : ℝ ↦ (Real.log y) ^ n * y ^ (-σ)) x) x := by
    intro x hx
    have hinterval : Set.uIcc (N : ℝ) M = Set.Icc (N : ℝ) M := Set.uIcc_of_le hMreal
    rw [hinterval] at hx
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one (le_trans hNreal hx.1)
    have hh := log_pow_mul_rpow_hasDerivAt σ x n (ne_of_gt hxpos)
    rw [hh.deriv]
    exact hh
  have hid : ∀ x ∈ Set.uIcc (N : ℝ) M, HasDerivAt (fun y : ℝ ↦ y) 1 x := by
    intro x hx
    exact hasDerivAt_id x
  have hconst : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) MeasureTheory.volume (N : ℝ) (M : ℝ) :=
    intervalIntegrable_const
  have hdi :
    MeasureTheory.IntegrableOn (fun x : ℝ ↦ deriv (fun y : ℝ ↦ (Real.log y) ^ n * y ^ (-σ)) x)
      (Set.uIcc (N : ℝ) M) := by
    rw [Set.uIcc_of_le hMreal]
    exact hderivint
  have hprod := intervalIntegral.integral_deriv_mul_eq_sub hid hfderiv hconst hdi.intervalIntegrable
  simpa only [one_mul] using hprod

/--
Inputs: integers `1 ≤ N ≤ M`, an order `n`, and an exponent `σ`.
Claim: the integral of `-x` times the derivative of `(log x)^n * x^(-σ)` equals the lower endpoint
term minus the upper endpoint term plus the integral of the weight.
Proof: combine the product integral identity with additivity and negation of interval integrals.
Role: converts the finite Chebyshev-Abel integral into endpoint and incomplete-Gamma terms.
-/
theorem log_pow_rpow_deriv_integral_eq_tail_terms {σ : ℝ} {N M : ℕ} (n : ℕ) (hN : 1 ≤ N)
    (hNM : N ≤ M) :
    ∫ t in (N : ℝ)..(M : ℝ), -t * deriv (fun y : ℝ ↦ (Real.log y) ^ n * y ^ (-σ)) t =
      (N : ℝ) * ((Real.log (N : ℝ)) ^ n * (N : ℝ) ^ (-σ)) -
          (M : ℝ) * ((Real.log (M : ℝ)) ^ n * (M : ℝ) ^ (-σ)) +
        ∫ t in (N : ℝ)..(M : ℝ), (Real.log t) ^ n * t ^ (-σ) := by
  let f : ℝ → ℝ := fun x ↦ (Real.log x) ^ n * x ^ (-σ)
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hMreal : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
  have hs : Set.uIcc (N : ℝ) M = Set.Icc (N : ℝ) M := Set.uIcc_of_le hMreal
  have hderivint := log_pow_mul_rpow_deriv_integrableOn_Icc (σ := σ) (N := N) (M := M) n hN
  have hdi : IntervalIntegrable (fun x : ℝ ↦ deriv f x) MeasureTheory.volume (N : ℝ) (M : ℝ) := by
    have hdi' : MeasureTheory.IntegrableOn (fun x : ℝ ↦ deriv f x) (Set.uIcc (N : ℝ) M) := by
      rw [hs]
      exact hderivint
    simpa only [f] using hdi'.intervalIntegrable
  have hlog : ContinuousOn Real.log (Set.Icc (N : ℝ) M) :=
    Real.continuousOn_log.mono
      (by
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_trans (by exact_mod_cast hN) hx.1)))
  have hrpow : ContinuousOn (fun x : ℝ ↦ x ^ (-σ)) (Set.Icc (N : ℝ) M) :=
    continuousOn_id.rpow_const
      (by
        intro x hx
        exact Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_trans (by exact_mod_cast hN) hx.1))))
  have hfcont : ContinuousOn f (Set.Icc (N : ℝ) M) := by
    dsimp only [f]
    exact (hlog.pow _).mul hrpow
  have hfint : IntervalIntegrable (fun x : ℝ ↦ f x) MeasureTheory.volume (N : ℝ) (M : ℝ) := by
    have hint : MeasureTheory.IntegrableOn f (Set.Icc (N : ℝ) M) :=
      hfcont.integrableOn_compact isCompact_Icc
    have hint' : MeasureTheory.IntegrableOn f (Set.uIcc (N : ℝ) M) := by
      rw [hs]
      exact hint
    exact hint'.intervalIntegrable
  have hcont : ContinuousOn (fun x : ℝ ↦ x) (Set.uIcc (N : ℝ) M) := by
    change ContinuousOn id (Set.uIcc (N : ℝ) M)
    exact continuousOn_id
  have hmulint :
    IntervalIntegrable (fun x : ℝ ↦ x * deriv f x) MeasureTheory.volume (N : ℝ) (M : ℝ) :=
    hdi.continuousOn_mul hcont
  have hid : ∀ x ∈ Set.uIcc (N : ℝ) M, HasDerivAt (fun y : ℝ ↦ y) 1 x := by
    intro x hx
    exact hasDerivAt_id x
  have hfderiv : ∀ x ∈ Set.uIcc (N : ℝ) M, HasDerivAt f (deriv f x) x := by
    intro x hx
    rw [hs] at hx
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one (le_trans (by exact_mod_cast hN) hx.1)
    have hh := log_pow_mul_rpow_hasDerivAt σ x n (ne_of_gt hxpos)
    rw [hh.deriv]
    exact hh
  have hprod := intervalIntegral.integral_deriv_mul_eq_sub hid hfderiv intervalIntegrable_const hdi
  simp only [one_mul] at hprod
  rw [intervalIntegral.integral_add hfint hmulint] at hprod
  have hresult :
    -(∫ t in (N : ℝ)..(M : ℝ), t * deriv f t) =
      (N : ℝ) * f (N : ℝ) - (M : ℝ) * f (M : ℝ) + ∫ t in (N : ℝ)..(M : ℝ), f t := by
    linarith only [hprod]
  have hneg :
    ∫ t in (N : ℝ)..(M : ℝ), -t * deriv f t = -(∫ t in (N : ℝ)..(M : ℝ), t * deriv f t) := by
    calc
      _ = ∫ t in (N : ℝ)..(M : ℝ), -(t * deriv f t) := by
        congr 1
        funext t
        ring
      _ = _ := intervalIntegral.integral_neg
  calc
    _ = -(∫ t in (N : ℝ)..(M : ℝ), t * deriv f t) := hneg
    _ = _ := hresult

/--
Inputs: `σ ≥ 0`, integers `1 ≤ N ≤ M`, an order `n`, and `n ≤ σ * log N`.
Claim: the finite von Mangoldt tail is bounded by the cutoff term and the integral of the
logarithmic-power weight.
Proof: combine the finite Chebyshev-Abel estimate with the integration-by-parts identity and
cancel the upper endpoint terms.
Role: reduces the infinite-tail estimate to an explicit incomplete-Gamma integral.
-/
theorem finite_vonMangoldt_log_pow_rpow_tail_integral_bound {σ : ℝ} {N M : ℕ} (n : ℕ) (hσ : 0 ≤ σ)
    (hN : 1 ≤ N) (hNM : N ≤ M) (hn : (n : ℝ) ≤ σ * Real.log N) :
    (∑ k ∈ Finset.Ioc N M,
        (Real.log (k : ℝ)) ^ n * (k : ℝ) ^ (-σ) * ArithmeticFunction.vonMangoldt k) ≤
      (Real.log 4 + 4) *
        ((N : ℝ) * ((Real.log (N : ℝ)) ^ n * (N : ℝ) ^ (-σ)) +
          ∫ t in (N : ℝ)..(M : ℝ), (Real.log t) ^ n * t ^ (-σ)) := by
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hMreal : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
  have habel := finite_vonMangoldt_log_pow_rpow_le_of_decreasing n hσ hN hNM hn
  have hI :
    ∫ t in Set.Ioc (N : ℝ) M,
        -deriv (fun y : ℝ ↦ (Real.log y) ^ n * y ^ (-σ)) t * ((Real.log 4 + 4) * t) =
      (Real.log 4 + 4) *
        (∫ t in (N : ℝ)..(M : ℝ), -t * deriv (fun y : ℝ ↦ (Real.log y) ^ n * y ^ (-σ)) t) := by
    calc
      _ =
          ∫ t in Set.Ioc (N : ℝ) M,
            (Real.log 4 + 4) * (-t * deriv (fun y : ℝ ↦ (Real.log y) ^ n * y ^ (-σ)) t) :=
        by
        congr 1
        funext t
        ring
      _ =
          (Real.log 4 + 4) *
            ∫ t in Set.Ioc (N : ℝ) M, -t * deriv (fun y : ℝ ↦ (Real.log y) ^ n * y ^ (-σ)) t :=
        MeasureTheory.integral_const_mul _ _
      _ =
          (Real.log 4 + 4) *
            ∫ t in (N : ℝ)..(M : ℝ), -t * deriv (fun y : ℝ ↦ (Real.log y) ^ n * y ^ (-σ)) t :=
        by rw [← intervalIntegral.integral_of_le hMreal]
  rw [hI, log_pow_rpow_deriv_integral_eq_tail_terms n hN hNM] at habel
  nlinarith only [habel]

/-- For a positive argument, write the weight of exponent `1 + η` as a logarithmic
moment with exponential damping. The real-power addition rule separates the reciprocal
factor. This identity transfers Gamma-integral bounds to the Euler-tail weight. -/
theorem log_pow_mul_rpow_eq_exp_kernel (η x : ℝ) (n : ℕ) (hx : 0 < x) :
    (Real.log x) ^ n * x ^ (-(1 + η)) = x⁻¹ * (Real.log x) ^ n * Real.exp (-(η * Real.log x)) := by
  have he : -(1 + η) = (-1 : ℝ) + -η := by ring
  rw [he, Real.rpow_add hx, Real.rpow_neg_one, Real.rpow_def_of_pos hx]
  have hexp : Real.log x * -η = -(η * Real.log x) := by ring
  rw [hexp]
  ring

/-- For `η > 0` and `1 ≤ N ≤ M`, bound the logarithmic-power integral on `[N,M]`
by the complete half-rate Gamma moment times its cutoff exponential. Rewrite the kernel,
then use nonnegative restriction monotonicity and the Chernoff estimate.
This controls the integral term in the finite Chebyshev-Abel bound. -/
theorem integral_log_pow_mul_rpow_le_gamma_tail (η N M : ℝ) (n : ℕ) (hη : 0 < η) (hN : 1 ≤ N)
    (hNM : N ≤ M) :
    (∫ x in N..M, (Real.log x) ^ n * x ^ (-(1 + η))) ≤
      Real.exp (-(η * Real.log N) / 2) * ((n.factorial : ℝ) / (η / 2) ^ (n + 1)) := by
  rw [intervalIntegral.integral_of_le hNM]
  have hid :
    (∫ x in Set.Ioc N M, (Real.log x) ^ n * x ^ (-(1 + η))) =
      ∫ x in Set.Ioc N M, x⁻¹ * (Real.log x) ^ n * Real.exp (-(η * Real.log x)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    exact log_pow_mul_rpow_eq_exp_kernel η x n (lt_of_lt_of_le zero_lt_one (le_trans hN hx.1.le))
  rw [hid]
  have hg := (integrableOn_log_pow_exp_neg_mul_log_Ioi η n hη).mono_set (Set.Ioi_subset_Ioi hN)
  have hmono :
    (∫ x in Set.Ioc N M, x⁻¹ * (Real.log x) ^ n * Real.exp (-(η * Real.log x))) ≤
      ∫ x in Set.Ioi N, x⁻¹ * (Real.log x) ^ n * Real.exp (-(η * Real.log x)) := by
    apply MeasureTheory.setIntegral_mono_set hg
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      have hx1 : 1 ≤ x := le_trans hN hx.le
      exact
        mul_nonneg
          (mul_nonneg (inv_nonneg.mpr (le_trans zero_le_one hx1))
            (pow_nonneg (Real.log_nonneg hx1) n))
          (Real.exp_pos _).le
    · exact Filter.Eventually.of_forall (fun x hx ↦ hx.1)
  exact hmono.trans (integral_log_pow_exp_neg_mul_log_Ioi_le_half_rate η N n hη hN)

/-- A nonnegative natural-indexed series above `N` satisfies any bound shared by
all its finite initial tails. Embed each finite subtype support in a sufficiently large
interval and use the nonnegative series bound. This promotes finite Abel estimates to tails. -/
theorem nonneg_tsum_compl_range_le_of_Ioc_sum_le (f : ℕ → ℝ) (N : ℕ) (C : ℝ) (hf : ∀ k, 0 ≤ f k)
    (hbound : ∀ M : ℕ, N ≤ M → ∑ k ∈ Finset.Ioc N M, f k ≤ C) :
    (∑' k : { k // k ∉ Finset.range (N + 1) }, f k.val) ≤ C := by
  classical
  apply Real.tsum_le_of_sum_le (fun (k : { k // k ∉ Finset.range (N + 1) }) ↦ hf k.val)
  intro S
  let T := S.image Subtype.val
  let M := max N (T.sup id)
  have hsub : T ⊆ Finset.Ioc N M := by
    intro k hk
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
    have hNa : N < a.val :=
      Nat.lt_of_succ_le (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using a.property))
    exact
      Finset.mem_Ioc.mpr
        ⟨hNa,
          (Finset.le_sup (f := id) (show a.val ∈ T from Finset.mem_image.mpr ⟨a, ha, rfl⟩)).trans
            (le_max_right N (T.sup id))⟩
  have heq : (∑ k ∈ S, f k.val) = ∑ k ∈ T, f k := by
    dsimp only [T]
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact Subtype.ext hab
  rw [heq]
  exact
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k hk hkt ↦ hf k)).trans
      (hbound M (le_max_left N (T.sup id)))

/-- For a positive distance `η` from one and a cutoff past the decreasing range,
bound every finite von Mangoldt tail by its cutoff term and an explicit Gamma tail.
Combine Chebyshev-Abel summation with the incomplete-Gamma estimate.
This supplies a bound uniform in the upper endpoint for the infinite-tail passage. -/
theorem finite_vonMangoldt_log_pow_rpow_tail_le_chernoff (η : ℝ) (n N M : ℕ) (hη : 0 < η)
    (hN : 1 ≤ N) (hNM : N ≤ M) (hn : (n : ℝ) ≤ (1 + η) * Real.log N) :
    (∑ k ∈ Finset.Ioc N M,
        (Real.log (k : ℝ)) ^ n * (k : ℝ) ^ (-(1 + η)) * ArithmeticFunction.vonMangoldt k) ≤
      (Real.log 4 + 4) *
        ((N : ℝ) * ((Real.log (N : ℝ)) ^ n * (N : ℝ) ^ (-(1 + η))) +
          Real.exp (-(η * Real.log N) / 2) * ((n.factorial : ℝ) / (η / 2) ^ (n + 1))) := by
  have hbase :=
    finite_vonMangoldt_log_pow_rpow_tail_integral_bound n (show 0 ≤ 1 + η by linarith only [hη]) hN
      hNM hn
  have hint :=
    integral_log_pow_mul_rpow_le_gamma_tail η N M n hη (by exact_mod_cast hN)
      (by exact_mod_cast hNM)
  exact
    hbase.trans
      (mul_le_mul_of_nonneg_left (add_le_add_right hint _)
        (add_nonneg (Real.log_nonneg (by norm_num only)) (by norm_num only)))

/-- For `η > 0`, `N ≥ 1`, and `n ≤ (1 + η) log N`, bound the infinite von Mangoldt
logarithmic tail by the cutoff term and the half-rate Gamma majorant. Convert the weight
to negative real powers and promote the finite interval bound to the nonnegative series.
This replaces the pointwise tail estimate before factorial normalization. -/
theorem vonMangoldt_log_weight_tail_le_chernoff (η : ℝ) (n N : ℕ) (hη : 0 < η) (hN : 1 ≤ N)
    (hn : (n : ℝ) ≤ (1 + η) * Real.log N) :
    (∑' k : { k // k ∉ Finset.range (N + 1) },
        ArithmeticFunction.vonMangoldt k.val * (Real.log k.val) ^ n / (k.val : ℝ) ^ (1 + η)) ≤
      (Real.log 4 + 4) *
        ((N : ℝ) * ((Real.log (N : ℝ)) ^ n * (N : ℝ) ^ (-(1 + η))) +
          Real.exp (-(η * Real.log N) / 2) * ((n.factorial : ℝ) / (η / 2) ^ (n + 1))) := by
  have heq (k : ℕ) :
    ArithmeticFunction.vonMangoldt k * (Real.log k) ^ n / (k : ℝ) ^ (1 + η) =
      (Real.log (k : ℝ)) ^ n * (k : ℝ) ^ (-(1 + η)) * ArithmeticFunction.vonMangoldt k := by
    rw [Real.rpow_neg (Nat.cast_nonneg k), div_eq_mul_inv]
    ring
  simp only [heq]
  apply
    nonneg_tsum_compl_range_le_of_Ioc_sum_le
      (fun k ↦ (Real.log (k : ℝ)) ^ n * (k : ℝ) ^ (-(1 + η)) * ArithmeticFunction.vonMangoldt k) N
  · intro k
    exact
      mul_nonneg
        (mul_nonneg (pow_nonneg (Real.log_natCast_nonneg k) n)
          (Real.rpow_nonneg (Nat.cast_nonneg k) _))
        ArithmeticFunction.vonMangoldt_nonneg
  · intro M hNM
    exact finite_vonMangoldt_log_pow_rpow_tail_le_chernoff η n N M hη hN hNM hn

/-- For a positive rate and cutoff at least one, the factorial-normalized Abel
endpoint is at most `η * 2^n * exp(-η log N / 2)`. Cancel the cutoff reciprocal
and apply the exponential Taylor bound at half the scaled logarithm.
This controls the endpoint without introducing an inverse-rate loss. -/
theorem normalized_log_pow_rpow_cutoff_le_chernoff (η N : ℝ) (n : ℕ) (hη : 0 < η) (hN : 1 ≤ N) :
    η ^ (n + 1) / (n.factorial : ℝ) * (N * ((Real.log N) ^ n * N ^ (-(1 + η)))) ≤
      η * (2 : ℝ) ^ n * Real.exp (-(η * Real.log N) / 2) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  rw [log_pow_mul_rpow_eq_exp_kernel η N n hNpos]
  have hcancel :
    N * (N⁻¹ * (Real.log N) ^ n * Real.exp (-(η * Real.log N))) =
      (Real.log N) ^ n * Real.exp (-(η * Real.log N)) := by
    calc
      _ = (N * N⁻¹) * ((Real.log N) ^ n * Real.exp (-(η * Real.log N))) := by ring
      _ = _ := by rw [mul_inv_cancel₀ (ne_of_gt hNpos), one_mul]
  rw [hcancel]
  have htaylor :=
    Real.pow_div_factorial_le_exp (η * Real.log N / 2)
      (div_nonneg (mul_nonneg hη.le (Real.log_nonneg hN)) (by norm_num only)) n
  have hscaled :=
    mul_le_mul_of_nonneg_left htaylor
      (mul_nonneg (mul_nonneg hη.le (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 2) n))
        (Real.exp_pos (-(η * Real.log N))).le)
  have hleft :
    η * (2 : ℝ) ^ n * Real.exp (-(η * Real.log N)) *
        ((η * Real.log N / 2) ^ n / (n.factorial : ℝ)) =
      η ^ (n + 1) / (n.factorial : ℝ) * ((Real.log N) ^ n * Real.exp (-(η * Real.log N))) := by
    rw [div_pow, mul_pow]
    calc
      _ =
          (η ^ (n + 1) / (n.factorial : ℝ) * ((Real.log N) ^ n * Real.exp (-(η * Real.log N)))) *
            ((2 : ℝ) ^ n * ((2 : ℝ) ^ n)⁻¹) :=
        by
        simp only [div_eq_mul_inv, pow_succ]
        ring
      _ = _ := by rw [mul_inv_cancel₀ (pow_ne_zero _ (by norm_num only : (2 : ℝ) ≠ 0)), mul_one]
  have hright :
    η * (2 : ℝ) ^ n * Real.exp (-(η * Real.log N)) * Real.exp (η * Real.log N / 2) =
      η * (2 : ℝ) ^ n * Real.exp (-(η * Real.log N) / 2) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hleft, hright] at hscaled
  exact hscaled

/-- For `0 < η ≤ 1` and a cutoff in the decreasing range, the normalized
von Mangoldt tail is at most `3 * (log 4 + 4) * 2^n * exp(-η log N / 2)`.
Combine the normalized endpoint and half-rate Gamma bounds.
This removes the inverse-rate prefactor needed for a fixed exponential Euler cutoff. -/
theorem normalized_vonMangoldt_log_weight_tail_le_chernoff (η : ℝ) (n N : ℕ) (hη : 0 < η)
    (hηsmall : η ≤ 1) (hN : 1 ≤ N) (hn : (n : ℝ) ≤ (1 + η) * Real.log N) :
    η ^ (n + 1) / (n.factorial : ℝ) *
        (∑' k : { k // k ∉ Finset.range (N + 1) },
          ArithmeticFunction.vonMangoldt k.val * (Real.log k.val) ^ n / (k.val : ℝ) ^ (1 + η)) ≤
      3 * (Real.log 4 + 4) * (2 : ℝ) ^ n * Real.exp (-(η * Real.log N) / 2) := by
  let A := η ^ (n + 1) / (n.factorial : ℝ)
  let E := (N : ℝ) * ((Real.log (N : ℝ)) ^ n * (N : ℝ) ^ (-(1 + η)))
  let B := Real.exp (-(η * Real.log N) / 2)
  let H := (n.factorial : ℝ) / (η / 2) ^ (n + 1)
  have hA : 0 ≤ A := div_nonneg (pow_nonneg hη.le _) (Nat.cast_nonneg _)
  have hC : 0 ≤ Real.log 4 + 4 := add_nonneg (Real.log_nonneg (by norm_num only)) (by norm_num only)
  have he : A * E ≤ η * (2 : ℝ) ^ n * B :=
    normalized_log_pow_rpow_cutoff_le_chernoff η N n hη (by exact_mod_cast hN)
  have hh : A * H = (2 : ℝ) ^ (n + 1) := log_pow_exp_half_rate_normalization η n hη
  have h := mul_le_mul_of_nonneg_left (vonMangoldt_log_weight_tail_le_chernoff η n N hη hN hn) hA
  have hb : 0 ≤ (2 : ℝ) ^ n * B :=
    mul_nonneg (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 2) _) (Real.exp_pos _).le
  have heta : η * (2 : ℝ) ^ n * B ≤ (2 : ℝ) ^ n * B := by
    simpa only [one_mul, mul_assoc] using mul_le_mul_of_nonneg_right hηsmall hb
  calc
    _ ≤ A * ((Real.log 4 + 4) * (E + B * H)) := h
    _ = (Real.log 4 + 4) * (A * E + B * (A * H)) := by ring
    _ ≤ (Real.log 4 + 4) * (η * (2 : ℝ) ^ n * B + B * (2 : ℝ) ^ (n + 1)) := by
      rw [hh]
      exact mul_le_mul_of_nonneg_left (add_le_add_left he _) hC
    _ ≤ (Real.log 4 + 4) * ((2 : ℝ) ^ n * B + B * (2 : ℝ) ^ (n + 1)) :=
      mul_le_mul_of_nonneg_left (add_le_add_left heta _) hC
    _ = _ := by
      rw [pow_succ]
      ring

/-- For a positive rate at most one, a decreasing-range cutoff, and the displayed
logarithmic margin, the normalized von Mangoldt tail is at most `exp(-D K) / 8`.
Exponentiate the margin and combine it with the normalized Chernoff estimate.
This provides the quantitative Euler-truncation certificate for a prescribed cutoff. -/
theorem normalized_vonMangoldt_tail_le_detector_threshold (η D K : ℝ) (n N : ℕ) (hη : 0 < η)
    (hηsmall : η ≤ 1) (hN : 1 ≤ N) (hn : (n : ℝ) ≤ (1 + η) * Real.log N)
    (hmargin :
      Real.log (24 * (Real.log 4 + 4)) + (n : ℝ) * Real.log 2 + D * K ≤ η * Real.log N / 2) :
    η ^ (n + 1) / (n.factorial : ℝ) *
        (∑' k : { k // k ∉ Finset.range (N + 1) },
          ArithmeticFunction.vonMangoldt k.val * (Real.log k.val) ^ n / (k.val : ℝ) ^ (1 + η)) ≤
      Real.exp (-(D * K)) / 8 := by
  have hC : 0 < 24 * (Real.log 4 + 4) :=
    mul_pos (by norm_num only)
      (add_pos_of_nonneg_of_pos (Real.log_nonneg (by norm_num only)) (by norm_num only))
  have heq :
    Real.exp (Real.log (24 * (Real.log 4 + 4)) + (n : ℝ) * Real.log 2 - η * Real.log N / 2) =
      8 * (3 * (Real.log 4 + 4) * (2 : ℝ) ^ n * Real.exp (-(η * Real.log N) / 2)) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_log hC,
      Real.exp_log (by norm_num only : (0 : ℝ) < 2), neg_div]
    ring
  have he :=
    Real.exp_le_exp.mpr
      (show Real.log (24 * (Real.log 4 + 4)) + (n : ℝ) * Real.log 2 - η * Real.log N / 2 ≤ -(D * K)
        by linarith only [hmargin])
  rw [heq] at he
  exact
    (normalized_vonMangoldt_log_weight_tail_le_chernoff η n N hη hηsmall hN hn).trans
      ((le_div_iff₀ (by norm_num only : (0 : ℝ) < 8)).mpr (by linarith only [he]))

/-- For `0 < η ≤ 1`, nonnegative detector exponent and order scale, and a positive
minimum cutoff, some larger integer cutoff has normalized tail at most `exp(-D K) / 8`.
Its scaled logarithmic length is bounded explicitly by the order, detector scale, and
minimum cutoff. Choose the ceiling of an exponential and apply the Chernoff margin.
This gives quantitative finite Euler support without an inverse-rate truncation loss. -/
theorem exists_quantitative_normalized_vonMangoldt_cutoff_ge (η D K : ℝ) (n cutoffMin : ℕ)
    (hη : 0 < η) (hηsmall : η ≤ 1) (hD : 0 ≤ D) (hK : 0 ≤ K) (hmin : 1 ≤ cutoffMin) :
    ∃ N : ℕ,
      cutoffMin ≤ N ∧
        1 ≤ N ∧
        (n : ℝ) ≤ (1 + η) * Real.log N ∧
        η * Real.log ((N : ℝ) + 1) ≤
          2 * ((n : ℝ) + D * K + Real.log (24 * (Real.log 4 + 4))) + η * Real.log cutoffMin +
            η * Real.log 3 ∧
        η ^ (n + 1) / (n.factorial : ℝ) *
            (∑' k : { k // k ∉ Finset.range (N + 1) },
              ArithmeticFunction.vonMangoldt k.val * (Real.log k.val) ^ n / (k.val : ℝ) ^ (1 + η)) ≤
          Real.exp (-(D * K)) / 8 := by
  let L := Real.log (24 * (Real.log 4 + 4))
  have hL : 0 ≤ L :=
    Real.log_nonneg
      (by
        have hlog4 := Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 4)
        nlinarith only [hlog4])
  have hminreal : (1 : ℝ) ≤ cutoffMin := by exact_mod_cast hmin
  have hminpos : (0 : ℝ) < cutoffMin := lt_of_lt_of_le zero_lt_one hminreal
  have hminlog := Real.log_nonneg hminreal
  let X := 2 * ((n : ℝ) + D * K + L) / η + Real.log cutoffMin
  have hquot : 0 ≤ 2 * ((n : ℝ) + D * K + L) / η :=
    div_nonneg
      (mul_nonneg (by norm_num only)
        (add_nonneg (add_nonneg (Nat.cast_nonneg n) (mul_nonneg hD hK)) hL))
      hη.le
  have hX : 0 ≤ X := add_nonneg hquot hminlog
  let N := Nat.ceil (Real.exp X)
  have hexp : 1 ≤ Real.exp X := Real.one_le_exp_iff.mpr hX
  have hNreal : 1 ≤ (N : ℝ) := hexp.trans (Nat.le_ceil (Real.exp X))
  have hN : 1 ≤ N := by exact_mod_cast hNreal
  have hminN : cutoffMin ≤ N := by
    have hm : Real.log (cutoffMin : ℝ) ≤ X := le_add_of_nonneg_left hquot
    have he := Real.exp_le_exp.mpr hm
    rw [Real.exp_log hminpos] at he
    exact_mod_cast he.trans (Nat.le_ceil (Real.exp X))
  have hlog : X ≤ Real.log (N : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos X) (Nat.le_ceil (Real.exp X))
    rwa [Real.log_exp] at h
  have hscaled : 2 * ((n : ℝ) + D * K + L) ≤ η * Real.log (N : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlog hη.le
    dsimp only [X] at h
    rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hη)] at h
    nlinarith only [h, mul_nonneg hη.le hminlog]
  have hn : (n : ℝ) ≤ (1 + η) * Real.log (N : ℝ) := by
    have hlog0 := Real.log_nonneg hNreal
    have hDK := mul_nonneg hD hK
    nlinarith only [hscaled, hlog0, hDK, hL, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hupper : (N : ℝ) + 1 ≤ 3 * Real.exp X := by
    have hceil : (N : ℝ) < Real.exp X + 1 := Nat.ceil_lt_add_one (Real.exp_pos X).le
    linarith only [hceil, hexp]
  have hlogupper : Real.log ((N : ℝ) + 1) ≤ Real.log 3 + X := by
    have h := Real.log_le_log (by linarith only [hNreal]) hupper
    rwa [Real.log_mul (by norm_num only : (3 : ℝ) ≠ 0) (ne_of_gt (Real.exp_pos X)), Real.log_exp] at
      h
  have hlogscale :
    η * Real.log ((N : ℝ) + 1) ≤
      2 * ((n : ℝ) + D * K + L) + η * Real.log cutoffMin + η * Real.log 3 := by
    have h := mul_le_mul_of_nonneg_left hlogupper hη.le
    dsimp only [X] at h
    rw [mul_add, mul_add, mul_div_cancel₀ _ (ne_of_gt hη)] at h
    linarith only [h]
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 2)
    linarith only [h]
  have hmargin :
    Real.log (24 * (Real.log 4 + 4)) + (n : ℝ) * Real.log 2 + D * K ≤ η * Real.log N / 2 := by
    have horder := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg n)
    dsimp only [L] at hscaled
    nlinarith only [hscaled, horder]
  exact
    ⟨N, hminN, hN, hn, hlogscale,
      normalized_vonMangoldt_tail_le_detector_threshold η D K n N hη hηsmall hN hn hmargin⟩

/-- For a positive rate, a nonnegative scaled length, and a positive minimum cutoff,
choose an integer whose scaled logarithm lies above the requested length, while the
logarithm of its successor exceeds that length by at most `η log 3`.
Take the ceiling of an exponential. This supplies a common quantitative Euler cutoff. -/
theorem exists_nat_cutoff_scaled_log_bounds (η A : ℝ) (cutoffMin : ℕ) (hη : 0 < η) (hA : 0 ≤ A)
    (hmin : 1 ≤ cutoffMin) :
    ∃ N : ℕ,
      cutoffMin ≤ N ∧
        1 ≤ N ∧
        A + η * Real.log cutoffMin ≤ η * Real.log N ∧
        η * Real.log ((N : ℝ) + 1) ≤ A + η * Real.log cutoffMin + η * Real.log 3 := by
  have hmreal : (1 : ℝ) ≤ cutoffMin := by exact_mod_cast hmin
  have hmlog := Real.log_nonneg hmreal
  let X := A / η + Real.log cutoffMin
  have hX : 0 ≤ X := add_nonneg (div_nonneg hA hη.le) hmlog
  let N := Nat.ceil (Real.exp X)
  have hexp : 1 ≤ Real.exp X := Real.one_le_exp_iff.mpr hX
  have hNreal : 1 ≤ (N : ℝ) := hexp.trans (Nat.le_ceil (Real.exp X))
  have hminN : cutoffMin ≤ N := by
    have h :=
      Real.exp_le_exp.mpr
        (show Real.log (cutoffMin : ℝ) ≤ X from le_add_of_nonneg_left (div_nonneg hA hη.le))
    rw [Real.exp_log (lt_of_lt_of_le zero_lt_one hmreal)] at h
    exact_mod_cast h.trans (Nat.le_ceil (Real.exp X))
  have hlower : X ≤ Real.log (N : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos X) (Nat.le_ceil (Real.exp X))
    rwa [Real.log_exp] at h
  have hupper : Real.log ((N : ℝ) + 1) ≤ Real.log 3 + X := by
    have hc : (N : ℝ) < Real.exp X + 1 := Nat.ceil_lt_add_one (Real.exp_pos X).le
    have hN3 : (N : ℝ) + 1 ≤ 3 * Real.exp X := by linarith only [hc, hexp]
    have h := Real.log_le_log (by linarith only [hNreal]) hN3
    rwa [Real.log_mul (by norm_num only : (3 : ℝ) ≠ 0) (ne_of_gt (Real.exp_pos X)), Real.log_exp] at
      h
  have hl := mul_le_mul_of_nonneg_left hlower hη.le
  have hu := mul_le_mul_of_nonneg_left hupper hη.le
  dsimp only [X] at hl hu
  rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hη)] at hl
  rw [mul_add, mul_add, mul_div_cancel₀ _ (ne_of_gt hη)] at hu
  exact ⟨N, hminN, by exact_mod_cast hNreal, hl, by linarith only [hu]⟩

/-- For a positive rate at most one and nonnegative detector budgets, one cutoff
works for all logarithmic derivative orders up to `nmax`, with normalized tail at most
`exp(-D K)/8` and an explicit logarithmic support bound. Choose the length from the
largest order and check each Chernoff margin. This makes finite Euler support uniform. -/
theorem exists_uniform_normalized_vonMangoldt_cutoff (η D K : ℝ) (nmax cutoffMin : ℕ) (hη : 0 < η)
    (hηsmall : η ≤ 1) (hD : 0 ≤ D) (hK : 0 ≤ K) (hmin : 1 ≤ cutoffMin) :
    ∃ N : ℕ,
      cutoffMin ≤ N ∧
        1 ≤ N ∧
        η * Real.log ((N : ℝ) + 1) ≤
          2 * ((nmax : ℝ) + D * K + Real.log (24 * (Real.log 4 + 4))) + η * Real.log cutoffMin +
            η * Real.log 3 ∧
        ∀ n ≤ nmax,
          η ^ (n + 1) / (n.factorial : ℝ) *
              (∑' k : { k // k ∉ Finset.range (N + 1) },
                ArithmeticFunction.vonMangoldt k.val * (Real.log k.val) ^ n /
                  (k.val : ℝ) ^ (1 + η)) ≤
            Real.exp (-(D * K)) / 8 := by
  have hL : 0 ≤ Real.log (24 * (Real.log 4 + 4)) :=
    Real.log_nonneg
      (by
        have hlog4 := Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 4)
        nlinarith only [hlog4])
  have hA : 0 ≤ 2 * ((nmax : ℝ) + D * K + Real.log (24 * (Real.log 4 + 4))) :=
    mul_nonneg (by norm_num only)
      (add_nonneg (add_nonneg (Nat.cast_nonneg _) (mul_nonneg hD hK)) hL)
  obtain ⟨N, hminN, hN, hlower, hupper⟩ :=
    exists_nat_cutoff_scaled_log_bounds η
      (2 * ((nmax : ℝ) + D * K + Real.log (24 * (Real.log 4 + 4)))) cutoffMin hη hA hmin
  refine ⟨N, hminN, hN, hupper, ?_⟩
  intro n hn
  have hnreal : (n : ℝ) ≤ nmax := by exact_mod_cast hn
  have hminlog : 0 ≤ η * Real.log cutoffMin :=
    mul_nonneg hη.le (Real.log_nonneg (by exact_mod_cast hmin))
  have hnrange : (n : ℝ) ≤ (1 + η) * Real.log N := by
    have hlog0 := Real.log_nonneg (by exact_mod_cast hN : (1 : ℝ) ≤ N)
    nlinarith only [hlower, hnreal, hminlog, hL, hlog0, mul_nonneg hD hK,
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hlog2 : Real.log 2 ≤ 1 :=
    (Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 2)).trans (by norm_num only)
  apply normalized_vonMangoldt_tail_le_detector_threshold η D K n N hη hηsmall hN hnrange
  have horder := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg n)
  nlinarith only [hlower, hnreal, hminlog, horder]

/--
Inputs: `σ > 1`, a derivative order `n`, and an integer cutoff `N ≥ 1`.
Claim: The tail of the von Mangoldt weights above `N` is bounded by an explicit expression in
`σ` and `n`.
Proof: Compare each term with the power bound above and bound the series of exponent `-(σ+1)/2`
by an integral.
Role: replaces an existential cutoff for fixed `σ` with a quantitative estimate that tracks `σ →
1+`.
-/
theorem vonMangoldt_log_weight_tail_le_explicit {σ : ℝ} (hσ : 1 < σ) (n N : ℕ) (hN : 1 ≤ N) :
    (∑' k : { k // k ∉ Finset.range (N + 1) },
        ArithmeticFunction.vonMangoldt k.val * (Real.log k.val) ^ n / (k.val : ℝ) ^ σ) ≤
      ((σ - 1) / (2 * ((n + 1 : ℕ) : ℝ))) ^ (-((n + 1 : ℕ) : ℝ)) * (N : ℝ) ^ (-(σ - 1) / 2) /
        ((σ - 1) / 2) := by
  let α := (σ - 1) / (2 * ((n + 1 : ℕ) : ℝ))
  let p := (σ + 1) / 2
  let C := α ^ (-((n + 1 : ℕ) : ℝ))
  have hp : 1 < p := by
    dsimp only [p]; linarith only [hσ]
  have hpowSum : Summable (fun k : ℕ ↦ (k : ℝ) ^ (-p)) := by
    dsimp only [p]
    exact Real.summable_nat_rpow.mpr (by linarith only [hσ])
  have hmajorSum : Summable (fun k : ℕ ↦ C * (k : ℝ) ^ (-p)) := hpowSum.mul_left C
  have hweightSum := summable_vonMangoldt_log_weight hσ n
  have hweightTail := hweightSum.subtype (fun k ↦ k ∉ Finset.range (N + 1))
  have hmajorTail := hmajorSum.subtype (fun k ↦ k ∉ Finset.range (N + 1))
  have hcompare :
    (∑' k : { k // k ∉ Finset.range (N + 1) },
        ArithmeticFunction.vonMangoldt k.val * (Real.log k.val) ^ n / (k.val : ℝ) ^ σ) ≤
      ∑' k : { k // k ∉ Finset.range (N + 1) }, C * (k.val : ℝ) ^ (-p) := by
    apply Summable.tsum_le_tsum (fun k ↦ ?_) hweightTail hmajorTail
    have hN2 : 2 ≤ N + 1 := Nat.succ_le_succ hN
    have hkN : N + 1 ≤ k.val := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using k.property)
    have hk2 : 2 ≤ k.val := hN2.trans hkN
    change
      ArithmeticFunction.vonMangoldt k.val * (Real.log k.val) ^ n / (k.val : ℝ) ^ σ ≤
        C * (k.val : ℝ) ^ (-p)
    have hexp : -(σ + 1) / 2 = -((σ + 1) / 2) := by ring
    simpa only [p, C, α, hexp] using vonMangoldt_log_weight_term_le_rpow hσ n k.val hk2
  have hpowerSub :
    (∑' k : { k // k ∉ Finset.range (N + 1) }, (k.val : ℝ) ^ (-p)) =
      (∑' m : ℕ, ((m + N + 1 : ℕ) : ℝ) ^ (-p) : ℝ) := by
    let f : ℕ → ℝ := fun k ↦ (k : ℝ) ^ (-p)
    have hs : Summable f := by simpa only [f] using hpowSum
    have hc := hs.sum_add_tsum_compl (s := Finset.range (N + 1))
    change
      (∑ k ∈ Finset.range (N + 1), f k) + (∑' k : { k // k ∉ Finset.range (N + 1) }, f k.val) =
        ∑' k : ℕ, f k at hc
    have hshift := hs.sum_add_tsum_nat_add (N + 1)
    have hshift' :
      (∑ k ∈ Finset.range (N + 1), f k) + (∑' m : ℕ, ((m + N + 1 : ℕ) : ℝ) ^ (-p)) =
        ∑' k : ℕ, f k := by
      simpa only [f, Nat.add_assoc, Nat.add_comm N 1, Nat.add_left_comm N 1] using hshift
    have heq :
      (∑' k : { k // k ∉ Finset.range (N + 1) }, f k.val) =
        ∑' m : ℕ, ((m + N + 1 : ℕ) : ℝ) ^ (-p) := by
      linarith only [hc, hshift']
    simpa only [f] using heq
  have hNpos : 0 < N := Nat.zero_lt_of_lt hN
  have hp' : -p < -1 := by
    dsimp only [p]; linarith only [hσ]
  have htail := PseudoPrime.Analysis.EulerCorrectionBounds.rpow_tail_le N hNpos hp'
  have hpow : -p + 1 = -(p - 1) := by ring
  rw [hpow] at htail
  have hinv : -((N : ℝ) ^ (-(p - 1))) / (-(p - 1)) = (N : ℝ) ^ (-(p - 1)) / (p - 1) := by
    rw [neg_div, div_neg, neg_neg]
  rw [hinv] at htail
  have he : 1 - p = -(p - 1) := by ring
  have hαpos : 0 < α := by
    dsimp only [α]
    exact
      div_pos (by linarith only [hσ])
        (mul_pos (by norm_num only) (Nat.cast_pos.mpr (Nat.succ_pos n)))
  calc
    _ ≤ C * ∑' k : { k // k ∉ Finset.range (N + 1) }, (k.val : ℝ) ^ (-p) := by
      rw [tsum_mul_left] at hcompare
      exact hcompare
    _ ≤ C * ((N : ℝ) ^ (1 - p) / (p - 1)) := by
      apply mul_le_mul_of_nonneg_left
      · rw [hpowerSub]
        simpa only [he] using htail
      · dsimp only [C]
        exact Real.rpow_nonneg hαpos.le _
    _ =
        ((σ - 1) / (2 * ((n + 1 : ℕ) : ℝ))) ^ (-((n + 1 : ℕ) : ℝ)) * (N : ℝ) ^ (-(σ - 1) / 2) /
          ((σ - 1) / 2) :=
      by
      rw [show 1 - p = -(σ - 1) / 2 by
          dsimp only [p]; ring]
      rw [show p - 1 = (σ - 1) / 2 by
          dsimp only [p]; ring]
      dsimp only [C, α]
      rw [mul_div_assoc]

/--
Inputs: a real exponent `σ > 1` and a logarithmic weight order.
Claim: the complete von Mangoldt logarithmic-weight series is bounded by its explicit tail bound
after removing the zero terms at indices zero and one.
Proof: split the summable series at the first two indices, which contribute zero, then apply the
explicit tail estimate with cutoff one.
Role: gives a quantitative upper bound for the variation series used in mesh selection.
-/
theorem vonMangoldt_log_weight_sum_le_explicit {σ : ℝ} (hσ : 1 < σ) (n : ℕ) :
    (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ n / (k : ℝ) ^ σ) ≤
      ((σ - 1) / (2 * ((n + 1 : ℕ) : ℝ))) ^ (-((n + 1 : ℕ) : ℝ)) * (1 : ℝ) ^ (-(σ - 1) / 2) /
        ((σ - 1) / 2) := by
  let f : ℕ → ℝ := fun k => ArithmeticFunction.vonMangoldt k * (Real.log k) ^ n / (k : ℝ) ^ σ
  have hsum : Summable f := by simpa only [f] using summable_vonMangoldt_log_weight hσ n
  have hΛ0 : ArithmeticFunction.vonMangoldt 0 = 0 :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr not_isPrimePow_zero
  have hΛ1 : ArithmeticFunction.vonMangoldt 1 = 0 := ArithmeticFunction.vonMangoldt_apply_one
  have hsmall : ∑ k ∈ Finset.range 2, f k = 0 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [f, hΛ0, hΛ1, zero_mul, zero_div, add_zero]
  have hdecomp := hsum.sum_add_tsum_compl (s := Finset.range 2)
  change
    (∑ k ∈ Finset.range 2, f k) + (∑' k : { k // k ∉ Finset.range 2 }, f k.val) =
      ∑' k : ℕ, f k at hdecomp
  rw [hsmall, zero_add] at hdecomp
  have heq : (∑' k : ℕ, f k) = ∑' k : { k // k ∉ Finset.range 2 }, f k.val := hdecomp.symm
  rw [heq]
  have htail := vonMangoldt_log_weight_tail_le_explicit hσ n 1 (by omega)
  simpa only [f, Nat.reduceAdd, Nat.cast_one, Real.one_rpow] using htail

/--
Inputs: `σ > 1` and a logarithmic weight order.
Claim: the full von Mangoldt logarithmic-weight series is bounded by a simple power of the order
and the reciprocal distance from one.
Proof: rewrite the explicit full-series bound using natural powers and reciprocal algebra.
Role: makes the variation series monotone in the derivative order for a common mesh choice.
-/
theorem vonMangoldt_log_weight_sum_le_power {σ : ℝ} (hσ : 1 < σ) (r : ℕ) :
    (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ r / (k : ℝ) ^ σ) ≤
      (2 / (σ - 1)) * (2 * ((r + 1 : ℕ) : ℝ) / (σ - 1)) ^ (r + 1) := by
  let η : ℝ := σ - 1
  let m : ℕ := r + 1
  have hη : 0 < η := by
    dsimp only [η]; linarith only [hσ]
  have hbase : (η / (2 * (m : ℝ))) ^ (-(m : ℝ)) = (2 * (m : ℝ) / η) ^ m := by
    rw [Real.rpow_neg (by positivity) (m : ℝ), Real.rpow_natCast]
    rw [div_pow, inv_div, div_pow]
  have hone : (1 : ℝ) ^ (-(η / 2)) = 1 := Real.one_rpow _
  have hexp : -(σ - 1) / 2 = -((σ - 1) / 2) := by ring
  have hexplicit := vonMangoldt_log_weight_sum_le_explicit hσ r
  have hrewrite :
    ((σ - 1) / (2 * ((r + 1 : ℕ) : ℝ))) ^ (-((r + 1 : ℕ) : ℝ)) * (1 : ℝ) ^ (-(σ - 1) / 2) /
        ((σ - 1) / 2) =
      (2 / η) * (2 * ((r + 1 : ℕ) : ℝ) / η) ^ (r + 1) := by
    dsimp only [η, m] at hbase hone
    dsimp only [η, m]
    rw [hexp, hone, hbase]
    field_simp [ne_of_gt hη]
  calc
    _ ≤
        ((σ - 1) / (2 * ((r + 1 : ℕ) : ℝ))) ^ (-((r + 1 : ℕ) : ℝ)) * (1 : ℝ) ^ (-(σ - 1) / 2) /
          ((σ - 1) / 2) :=
      hexplicit
    _ = _ := hrewrite

/--
Inputs: `σ > 1`, a derivative order, and an upper bound for `σ - 1` by one.
Claim: the von Mangoldt variation series with logarithmic power `n + 1` is bounded uniformly for
all `n ≤ nmax` by an explicit expression depending only on `nmax` and `σ`.
Proof: use the explicit full-series estimate and monotonicity of its positive base and exponent.
Role: supplies a common variation bound when several derivative orders share one height mesh.
-/
theorem vonMangoldt_log_weight_sum_le_uniform_explicit {σ : ℝ} (hσ : 1 < σ) (hσsmall : σ - 1 ≤ 1)
    (n nmax : ℕ) (hn : n ≤ nmax) :
    (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ) ≤
      (2 / (σ - 1)) * (2 * ((nmax + 2 : ℕ) : ℝ) / (σ - 1)) ^ (nmax + 2) := by
  have hη : 0 < σ - 1 := by linarith only [hσ]
  have hmaxCast : (2 : ℝ) ≤ ((nmax + 2 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ nmax + 2 by omega)
  have hbaseOne : 1 ≤ 2 * ((nmax + 2 : ℕ) : ℝ) / (σ - 1) := by
    apply (le_div_iff₀ hη).2
    have hnum : (2 : ℝ) ≤ 2 * ((nmax + 2 : ℕ) : ℝ) := by nlinarith only [hmaxCast]
    simpa only [one_mul] using le_trans hσsmall (le_trans (by norm_num only) hnum)
  have hcast : ((n + 2 : ℕ) : ℝ) ≤ ((nmax + 2 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.add_le_add_right hn 2)
  have hbasele : 2 * ((n + 2 : ℕ) : ℝ) / (σ - 1) ≤ 2 * ((nmax + 2 : ℕ) : ℝ) / (σ - 1) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcast (by norm_num only)) hη.le
  have hsmall := vonMangoldt_log_weight_sum_le_power hσ (n + 1)
  have hbasepow :
    (2 * ((n + 2 : ℕ) : ℝ) / (σ - 1)) ^ (n + 2) ≤
      (2 * ((nmax + 2 : ℕ) : ℝ) / (σ - 1)) ^ (nmax + 2) := by
    calc
      _ ≤ (2 * ((nmax + 2 : ℕ) : ℝ) / (σ - 1)) ^ (n + 2) :=
        pow_le_pow_left₀ (by positivity) hbasele _
      _ ≤ _ := pow_le_pow_right₀ hbaseOne (Nat.add_le_add_right hn 2)
  calc
    _ ≤ (2 / (σ - 1)) * (2 * ((n + 2 : ℕ) : ℝ) / (σ - 1)) ^ (n + 2) := by
      simpa only [Nat.add_assoc, Nat.cast_add, Nat.cast_one, Nat.reduceAdd] using hsmall
    _ ≤ _ := mul_le_mul_of_nonneg_left hbasepow (by positivity)

/--
Inputs: `σ > 1`, a derivative order, a cutoff `N ≥ 1`, and a finite set of indices outside
`[0, N]`.
Claim: the sum of the von Mangoldt logarithmic weights over that finite set is bounded by the
explicit tail estimate above `N`.
Proof: embed the finite set into the subtype tail, compare its nonnegative sum with the full tail,
and apply `vonMangoldt_log_weight_tail_le_explicit`.
Role: bounds finite residual supports, including selected prime-power terms, by the same explicit
truncation error used for Euler derivatives.
-/
theorem finite_vonMangoldt_log_weight_subset_tail_le_explicit {σ : ℝ} (hσ : 1 < σ) (n N : ℕ)
    (hN : 1 ≤ N) (S : Finset { k // k ∉ Finset.range (N + 1) }) :
    (∑ k ∈ S, ArithmeticFunction.vonMangoldt k.val * (Real.log k.val) ^ n / (k.val : ℝ) ^ σ) ≤
      ((σ - 1) / (2 * ((n + 1 : ℕ) : ℝ))) ^ (-((n + 1 : ℕ) : ℝ)) * (N : ℝ) ^ (-(σ - 1) / 2) /
        ((σ - 1) / 2) := by
  let f : ℕ → ℝ := fun k => ArithmeticFunction.vonMangoldt k * (Real.log k) ^ n / (k : ℝ) ^ σ
  have hweight : Summable f := summable_vonMangoldt_log_weight hσ n
  have htail : Summable (fun k : { k // k ∉ Finset.range (N + 1) } => f k.val) := hweight.subtype _
  have hnonneg : ∀ k ∉ S, 0 ≤ f k.val := by
    intro k _
    dsimp only [f]
    have hkN : N + 1 ≤ k.val := Nat.not_lt.mp (by simpa only [Finset.mem_range] using k.property)
    have hkpos : 0 < k.val :=
      Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le Nat.zero_lt_one hN) (Nat.le_trans (Nat.le_succ N) hkN)
    have hkposR : (0 : ℝ) < (k.val : ℝ) := by exact_mod_cast hkpos
    exact
      div_nonneg
        (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (pow_nonneg (Real.log_natCast_nonneg k.val) n))
        (le_of_lt (Real.rpow_pos_of_pos hkposR σ))
  have hsumtail := htail.sum_le_tsum S hnonneg
  have hexplicit := vonMangoldt_log_weight_tail_le_explicit hσ n N hN
  simpa only [f] using hsumtail.trans hexplicit

/--
Inputs: `σ > 1`, a derivative order `n`, and a positive tolerance `ε`.
Claim: There is a finite cutoff for which the tail of `Λ(k) (log k)^n / k^σ` is less than `ε`.
Proof: Use summability of the nonnegative series and convergence of its tails to zero.
Role: makes the finite Dirichlet-polynomial error arbitrarily small in a fixed right half-plane.
-/
theorem exists_vonMangoldt_log_weight_tail_lt {σ : ℝ} (hσ : 1 < σ) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ,
      ∑' k : { k // k ∉ Finset.range M },
          ArithmeticFunction.vonMangoldt k.val * (Real.log k.val) ^ n / (k.val : ℝ) ^ σ <
        ε := by
  let f : ℕ → ℝ := fun k => ArithmeticFunction.vonMangoldt k * (Real.log k) ^ n / (k : ℝ) ^ σ
  have hsum : Summable f := by simpa only [f] using summable_vonMangoldt_log_weight hσ n
  have hpartial := hsum.tendsto_sum_tsum_nat
  have hconst : Filter.Tendsto (fun _ : ℕ => ∑' k : ℕ, f k) Filter.atTop (nhds (∑' k : ℕ, f k)) :=
    tendsto_const_nhds
  have hTdiff :
    Filter.Tendsto (fun M : ℕ => (∑' k : ℕ, f k) - ∑ k ∈ Finset.range M, f k) Filter.atTop
      (nhds 0) := by
    simpa only [sub_self] using hconst.sub hpartial
  have hT :
    Filter.Tendsto (fun M : ℕ => ∑' k : { k // k ∉ Finset.range M }, f k.val) Filter.atTop
      (nhds 0) := by
    have heq :
      (fun M : ℕ => (∑' k : ℕ, f k) - ∑ k ∈ Finset.range M, f k) =
        (fun M : ℕ => ∑' k : { k // k ∉ Finset.range M }, f k.val) := by
      funext M
      have hs := hsum.sum_add_tsum_compl (s := Finset.range M)
      change
        (∑ k ∈ Finset.range M, f k) + (∑' k : { k // k ∉ Finset.range M }, f k.val) =
          ∑' k : ℕ, f k at hs
      calc
        (∑' k : ℕ, f k) - ∑ k ∈ Finset.range M, f k =
            ((∑ k ∈ Finset.range M, f k) + ∑' k : { k // k ∉ Finset.range M }, f k.val) -
              ∑ k ∈ Finset.range M, f k :=
          by rw [hs]
        _ = ∑' k : { k // k ∉ Finset.range M }, f k.val := by ring
    rw [← heq]
    exact hTdiff
  have hev := hT.eventually (Iio_mem_nhds hε)
  obtain ⟨M, hM⟩ := hev.exists
  exact ⟨M, by simpa only [f] using hM⟩

/--
Inputs: a differentiable complex function on the segment between two points and a uniform bound
for its derivative along that segment.
Claim: the difference of the endpoint values is at most the segment length times the derivative
bound.
Proof: parametrize the segment on the real unit interval, apply the real mean-value estimate to
the composed function, and bound the derivative of the parametrization by the segment length.
Role: transfers a large derivative value at a zero's height to nearby fixed heights.
-/
theorem norm_sub_le_of_deriv_norm_le_segment (f : ℂ → ℂ) (s z : ℂ) (K : ℝ)
    (hf : ∀ r ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℂ f (s + (r : ℂ) * (z - s)))
    (hb : ∀ r ∈ Set.Icc (0 : ℝ) 1, ‖deriv f (s + (r : ℂ) * (z - s))‖ ≤ K) :
    ‖f z - f s‖ ≤ ‖z - s‖ * K := by
  have hderiv (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun u : ℝ => f (s + (u : ℂ) * (z - s))) (deriv f (s + (r : ℂ) * (z - s)) * (z - s))
      r := by
    have hlineC : HasDerivAt (fun u : ℂ => s + u * (z - s)) (z - s) (r : ℂ) := by
      simpa only [id_eq, one_mul] using ((hasDerivAt_id (r : ℂ)).mul_const (z - s)).const_add s
    have hline : HasDerivAt (fun u : ℝ => s + (u : ℂ) * (z - s)) (z - s) r := by
      simpa only [id_eq, one_mul] using hlineC.comp_ofReal
    exact (hf r hr).hasDerivAt.comp r hline
  have hb' :
    ∀ r ∈ Set.Ico (0 : ℝ) 1, ‖deriv f (s + (r : ℂ) * (z - s)) * (z - s)‖ ≤ K * ‖z - s‖ := by
    intro r hr
    rw [norm_mul]
    have hrcc : r ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hr
    exact mul_le_mul_of_nonneg_right (hb r hrcc) (norm_nonneg (z - s))
  have h :=
    norm_image_sub_le_of_norm_deriv_le_segment_01' (fun r hr => (hderiv r hr).hasDerivWithinAt) hb'
  have h' : ‖f (s + (z - s)) - f (s + (0 : ℂ))‖ ≤ K * ‖z - s‖ := by
    simpa only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, mul_one, zero_mul, mul_zero] using
      h
  have hs : s + (z - s) = z := by ring
  rw [hs, add_zero, mul_comm] at h'
  exact h'

/--
Inputs: a Dirichlet character, a point with real part greater than one, and a derivative order.
Claim: the norm of the corresponding logarithmic derivative is bounded by a positive real
Dirichlet series with coefficients `Λ(k) (log k)^n`.
Proof: express the derivative as its twisted Euler series, apply the norm bound for a sum, and
compare each twisted term with the untwisted positive term.
Role: turns the analytic derivative detected from local zeros into a scalar large-value input.
-/
theorem norm_iteratedDeriv_logDeriv_le_vonMangoldt_log_weight {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s‖ ≤
      ∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ n / (k : ℝ) ^ s.re := by
  let f : ℕ → ℂ := fun k ↦ χ (k : ZMod N) * (ArithmeticFunction.vonMangoldt k : ℂ)
  let g : ℕ → ℂ := fun k ↦ (ArithmeticFunction.vonMangoldt k : ℂ)
  let τ : ℝ := (1 + s.re) / 2
  have hτ1 : 1 < τ := by
    dsimp only [τ]
    linarith only [hs]
  have hτs : τ < s.re := by
    dsimp only [τ]
    linarith only [hs]
  have hfτ : LSeriesSummable f (τ : ℂ) := by
    dsimp only [f]
    exact
      DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ
        (by simpa only [Complex.ofReal_re] using hτ1)
  have habf : LSeries.abscissaOfAbsConv f < s.re := by
    have hle : LSeries.abscissaOfAbsConv f ≤ (τ : EReal) := by
      simpa only [Complex.ofReal_re] using hfτ.abscissaOfAbsConv_le
    have hts : (τ : EReal) < (s.re : EReal) := by exact_mod_cast hτs
    exact hle.trans_lt hts
  have hseries := LSeries_iteratedDeriv n (f := f) habf
  have hidentity := iteratedDeriv_logDeriv_eq_neg_twistedVonMangoldt_series χ hs n
  rw [hidentity]
  have hnormsumm : Summable (fun k : ℕ => ‖LSeries.term (LSeries.logMul^[n] g) s k‖) := by
    have hgτ : LSeriesSummable g (τ : ℂ) := by
      dsimp only [g]
      exact
        ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa only [Complex.ofReal_re] using hτ1)
    have hle : LSeries.abscissaOfAbsConv g ≤ (τ : EReal) := by
      simpa only [Complex.ofReal_re] using hgτ.abscissaOfAbsConv_le
    have hts : (τ : EReal) < (s.re : EReal) := by exact_mod_cast hτs
    have hEq := LSeries.abscissaOfAbsConv_logPowMul (f := g) (m := n)
    have hleg : LSeries.abscissaOfAbsConv (LSeries.logMul^[n] g) < s.re := by
      calc
        LSeries.abscissaOfAbsConv (LSeries.logMul^[n] g) = LSeries.abscissaOfAbsConv g := hEq
        _ < s.re := hle.trans_lt hts
    have hgs : LSeriesSummable (LSeries.logMul^[n] g) s :=
      LSeriesSummable_of_abscissaOfAbsConv_lt_re hleg
    change Summable (fun k : ℕ => LSeries.term (LSeries.logMul^[n] g) s k) at hgs
    exact summable_norm_iff.mpr hgs
  have hfnormsumm : Summable (fun k : ℕ => ‖LSeries.term (LSeries.logMul^[n] f) s k‖) := by
    have hEq := LSeries.abscissaOfAbsConv_logPowMul (f := f) (m := n)
    have hfpow : LSeries.abscissaOfAbsConv (LSeries.logMul^[n] f) < s.re := by
      calc
        LSeries.abscissaOfAbsConv (LSeries.logMul^[n] f) = LSeries.abscissaOfAbsConv f := hEq
        _ < s.re := habf
    have hfs : LSeriesSummable (LSeries.logMul^[n] f) s :=
      LSeriesSummable_of_abscissaOfAbsConv_lt_re hfpow
    change Summable (fun k : ℕ => LSeries.term (LSeries.logMul^[n] f) s k) at hfs
    exact summable_norm_iff.mpr hfs
  have hterm :
    ∀ k : ℕ,
      ‖LSeries.term (LSeries.logMul^[n] g) s k‖ =
        ArithmeticFunction.vonMangoldt k * (Real.log k) ^ n / (k : ℝ) ^ s.re := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp only [LSeries.term_zero, norm_zero, ArithmeticFunction.map_zero, CharP.cast_eq_zero,
        zero_mul, zero_div]
    · exact norm_vonMangoldt_logMul_term_eq n k (Nat.pos_of_ne_zero hk)
  have hcompare :
    ∑' k : ℕ, ‖LSeries.term (LSeries.logMul^[n] f) s k‖ ≤
      ∑' k : ℕ, ‖LSeries.term (LSeries.logMul^[n] g) s k‖ := by
    apply Summable.tsum_le_tsum (fun k => ?_) hfnormsumm hnormsumm
    by_cases hk : k = 0
    · subst k
      simp only [LSeries.term_zero, norm_zero, le_refl]
    · have hbound := twistedVonMangoldt_log_term_bound χ n k (s := s) (Nat.pos_of_ne_zero hk)
      change
        ‖LSeries.term (LSeries.logMul^[n] f) s k‖ ≤
          ArithmeticFunction.vonMangoldt k * (Real.log k) ^ n / (k : ℝ) ^ s.re at hbound
      calc
        ‖LSeries.term (LSeries.logMul^[n] f) s k‖ ≤
            ArithmeticFunction.vonMangoldt k * (Real.log k) ^ n / (k : ℝ) ^ s.re :=
          hbound
        _ = ‖LSeries.term (LSeries.logMul^[n] g) s k‖ := (hterm k).symm
  calc
    ‖-((-1 : ℂ) ^ n * LSeries (LSeries.logMul^[n] f) s)‖ = ‖LSeries (LSeries.logMul^[n] f) s‖ := by
      simp only [norm_neg, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    _ = ‖(-1 : ℂ) ^ n * LSeries (LSeries.logMul^[n] f) s‖ := by
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    _ = ‖iteratedDeriv n (LSeries f) s‖ := by rw [← hseries]
    _ ≤ ∑' k : ℕ, ‖LSeries.term (LSeries.logMul^[n] f) s k‖ := by
      rw [hseries]
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      change ‖∑' k : ℕ, LSeries.term (LSeries.logMul^[n] f) s k‖ ≤ _
      exact norm_tsum_le_tsum_norm hfnormsumm
    _ ≤ ∑' k : ℕ, ‖LSeries.term (LSeries.logMul^[n] g) s k‖ := hcompare
    _ = ∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ n / (k : ℝ) ^ s.re :=
      tsum_congr hterm

/--
Inputs: a nontrivial Dirichlet character, two points with the same real part greater than one,
and a derivative order.
Claim: the difference of the logarithmic derivatives at the two points is bounded by their
distance times the positive von Mangoldt series for the next derivative order.
Proof: the logarithmic derivative is analytic on the half-plane, and the Euler-series bound
controls its next derivative uniformly along the vertical segment; apply the segment estimate.
Role: transfers a zero-detected derivative lower bound to nearby fixed heights for family
large-sieve counting.
-/
theorem norm_iteratedDeriv_logDeriv_vertical_variation {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s t : ℂ} (hre : s.re = t.re) (hs : 1 < s.re)
    (n : ℕ) :
    ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) t -
          iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s‖ ≤
      ‖t - s‖ *
        ∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ s.re := by
  let f : ℂ → ℂ := fun w => iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) w
  have hreal (r : ℝ) : (s + (r : ℂ) * (t - s)).re = s.re := by
    rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.sub_re, hre]
    ring
  have hanalyticL (w : ℂ) : AnalyticAt ℂ (DirichletCharacter.LFunction χ) w :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt w
  have hlog (w : ℂ) (hw : 1 < w.re) :
    AnalyticAt ℂ (logDeriv (DirichletCharacter.LFunction χ)) w := by
    have hLne : DirichletCharacter.LFunction χ w ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (le_of_lt hw)
    have hfun :
      (fun x : ℂ => logDeriv (DirichletCharacter.LFunction χ) x) = fun x =>
        deriv (DirichletCharacter.LFunction χ) x / DirichletCharacter.LFunction χ x := by
      funext x
      exact logDeriv_apply _ _
    change AnalyticAt ℂ (fun x : ℂ => logDeriv (DirichletCharacter.LFunction χ) x) w
    rw [hfun]
    exact (hanalyticL w).deriv.div (hanalyticL w) hLne
  have hiter (w : ℂ) (hw : 1 < w.re) :
    AnalyticAt ℂ (iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))) w := by
    induction n with
    | zero => simpa only [iteratedDeriv_zero] using hlog w hw
    | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv
  have hf : ∀ r ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℂ f (s + (r : ℂ) * (t - s)) := by
    intro r hr
    have hpoint : 1 < (s + (r : ℂ) * (t - s)).re := by
      rw [hreal]
      exact hs
    exact (hiter _ hpoint).differentiableAt
  have hb :
    ∀ r ∈ Set.Icc (0 : ℝ) 1,
      ‖deriv f (s + (r : ℂ) * (t - s))‖ ≤
        ∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ s.re := by
    intro r hr
    change
      ‖deriv (iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)))
            (s + (r : ℂ) * (t - s))‖ ≤
        _
    rw [← iteratedDeriv_succ]
    have hpoint : 1 < (s + (r : ℂ) * (t - s)).re := by
      rw [hreal]
      exact hs
    have hbound := norm_iteratedDeriv_logDeriv_le_vonMangoldt_log_weight χ hpoint (n + 1)
    simpa only [hreal] using hbound
  have hvar := norm_sub_le_of_deriv_norm_le_segment f s t _ hf hb
  simpa only [f] using hvar

/--
Inputs: a nontrivial character, two points with the same real part greater than one, a derivative
order, and a lower bound at the first point that includes the vertical variation allowance.
Claim: the derivative norm at the second point is at least the stated lower bound.
Proof: apply the vertical variation estimate and the triangle inequality.
Role: converts a zero-dependent derivative witness into a fixed-height large-value witness.
-/
theorem iteratedDeriv_logDeriv_norm_lower_bound_nearby_vertical_point {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s t : ℂ} (hre : s.re = t.re) (hs : 1 < s.re) (n : ℕ)
    (B : ℝ)
    (hlarge :
      B +
          ‖t - s‖ *
            (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ s.re) ≤
        ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) t‖) :
    B ≤ ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s‖ := by
  have hvar := norm_iteratedDeriv_logDeriv_vertical_variation χ hχ hre hs n
  have htriangle :
    ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) t‖ ≤
      ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s‖ +
        ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) t -
            iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s‖ := by
    calc
      _ =
          ‖(iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) t -
                iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s) +
              iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s‖ :=
        by rw [sub_add_cancel]
      _ ≤ _ := by
        simpa only [add_comm] using
          norm_add_le
            (iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) t -
              iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s)
            (iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s)
  linarith only [hlarge, htriangle, hvar]

/--
Inputs: a nontrivial character, a derivative lower bound at a height, a mesh denominator, and a
window radius measured in mesh steps.
Claim: every rational mesh point within the window retains the lower bound.
Proof: bound the vertical distance by the window width and apply the derivative variation estimate.
Role: lets a zero detector contribute a block of grid incidences instead of one grid point.
-/
theorem forall_integer_height_grid_window_large {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {σ t : ℝ} (hσ : 1 < σ) (M K n : ℕ) (m : ℤ)
    (hdist : |t - (m : ℝ) / M| ≤ (K + 1 : ℝ) / M) (B : ℝ)
    (hlarge :
      B +
          ((K + 1 : ℝ) / M) *
            (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ) ≤
        ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
            ((σ : ℂ) + Complex.I * (t : ℂ))‖) :
    B ≤
      ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
          ((σ : ℂ) + Complex.I * (((m : ℝ) / M : ℝ) : ℂ))‖ := by
  let s := (σ : ℂ) + Complex.I * (((m : ℝ) / M : ℝ) : ℂ)
  let t₀ := (σ : ℂ) + Complex.I * (t : ℂ)
  have hsRe : s.re = σ := by
    dsimp only [s]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, sub_zero, mul_zero, add_zero]
  have htRe : t₀.re = σ := by
    dsimp only [t₀]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, sub_zero, mul_zero, add_zero]
  have hdistComplex : ‖t₀ - s‖ ≤ (K + 1 : ℝ) / M := by
    have heq : t₀ - s = Complex.I * ((t - (m : ℝ) / M : ℝ) : ℂ) := by
      dsimp only [t₀, s]
      push_cast
      ring
    rw [heq, Complex.norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
    exact hdist
  have hseriesNonneg :
    0 ≤ ∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ :=
    le_trans (norm_nonneg _)
      (norm_iteratedDeriv_logDeriv_le_vonMangoldt_log_weight χ (s := (σ : ℂ))
        (by simpa only [Complex.ofReal_re] using hσ) (n + 1))
  have hmargin :
    B +
        ‖t₀ - s‖ *
          (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ s.re) ≤
      ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) t₀‖ := by
    rw [hsRe]
    calc
      B +
            ‖t₀ - s‖ *
              (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ) ≤
          B +
            ((K + 1 : ℝ) / M) *
              (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ) :=
        add_le_add_right (mul_le_mul_of_nonneg_right hdistComplex hseriesNonneg) B
      _ ≤ _ := by simpa only [t₀] using hlarge
  exact
    iteratedDeriv_logDeriv_norm_lower_bound_nearby_vertical_point χ hχ (by rw [hsRe, htRe])
      (by
        rw [hsRe]; exact hσ)
      n B hmargin

/--
Inputs: a natural height bound, a positive natural mesh denominator, and a real height in the
bounded interval.
Claim: a rational grid point with denominator `M` lies in the interval and is within `1 / M` of
the given height.
Proof: take the ceiling of the height multiplied by `M`; the ceiling inequalities give both the
endpoint bounds and the approximation estimate.
Role: supplies a finite set of fixed heights to which the vertical derivative variation estimate
can transfer zero-dependent lower bounds.
-/
theorem exists_integer_height_grid_approximation {T M : ℕ} {t : ℝ} (hM : 0 < M) (hlo : -(T : ℝ) ≤ t)
    (hhi : t ≤ T) :
    ∃ m : ℤ, m ∈ Finset.Icc (-(T * M : ℤ)) (T * M : ℤ) ∧ |t - (m : ℝ) / M| ≤ 1 / M := by
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast hM
  have hscaleLo : -(T : ℝ) * M ≤ t * M := mul_le_mul_of_nonneg_right hlo hMpos.le
  have hscaleHi : t * M ≤ (T : ℝ) * M := mul_le_mul_of_nonneg_right hhi hMpos.le
  have hprodcast : ((T * M : ℤ) : ℝ) = (T : ℝ) * M := by simp only [Int.cast_mul, Int.cast_natCast]
  let m : ℤ := ⌈t * M⌉
  have hmle : t * M ≤ (m : ℝ) := by
    dsimp only [m]
    exact Int.le_ceil (t * M)
  have hmlt : (m : ℝ) < t * M + 1 := by
    dsimp only [m]
    exact Int.ceil_lt_add_one (t * M)
  refine ⟨m, Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
  · have hcast : (-(T * M : ℤ) : ℝ) ≤ (m : ℝ) := by
      calc
        (-(T * M : ℤ) : ℝ) = -(T : ℝ) * M := by
          simp only [Int.cast_mul, Int.cast_natCast]
          ring
        _ ≤ t * M := hscaleLo
        _ ≤ (m : ℝ) := hmle
    exact_mod_cast hcast
  · apply Int.ceil_le.mpr
    rw [hprodcast]
    exact hscaleHi
  · rw [abs_le]
    constructor
    · have hupper : (m : ℝ) / M < t + 1 / M := by
        apply (div_lt_iff₀ hMpos).2
        calc
          (m : ℝ) < t * M + 1 := hmlt
          _ = (t + 1 / M) * M := by rw [add_mul, div_mul_cancel₀ 1 hMpos.ne']
      linarith only [hupper]
    · have hlower : t ≤ (m : ℝ) / M := (le_div_iff₀ hMpos).2 hmle
      exact le_trans (sub_nonpos.mpr hlower) (div_nonneg (by norm_num only) hMpos.le)

/--
Inputs: a nontrivial character, a real part greater than one, a bounded zero height, a rational
height mesh, a derivative order, and a derivative lower bound with the mesh variation allowance.
Claim: one point on the finite rational height grid has the stated lower bound for the derivative.
Proof: choose the grid height within `1 / M`, use the Euler-series bound for the next derivative
order to control the variation, and apply the nearby-point lower-bound theorem.
Role: turns a zero-dependent vertical witness into one of finitely many fixed points for the
family large-sieve estimate.
-/
theorem exists_rational_height_large_logDeriv_iteratedDeriv {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (σ : ℝ) (hσ : 1 < σ) {T M : ℕ} (hM : 0 < M) {t : ℝ}
    (htlo : -(T : ℝ) ≤ t) (hthi : t ≤ T) (n : ℕ) (B : ℝ)
    (hlarge :
      B +
          (1 / (M : ℝ)) *
            (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ) ≤
        ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
            ((σ : ℂ) + Complex.I * (t : ℂ))‖) :
    ∃ m : ℤ,
      m ∈ Finset.Icc (-(T * M : ℤ)) (T * M : ℤ) ∧
        B ≤
          ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
              ((σ : ℂ) + Complex.I * (((m : ℝ) / (M : ℝ) : ℝ) : ℂ))‖ := by
  obtain ⟨m, hm, hgrid⟩ := exists_integer_height_grid_approximation hM htlo hthi
  let u : ℝ := (m : ℝ) / M
  let s₀ : ℂ := (σ : ℂ) + Complex.I * (u : ℂ)
  let t₀ : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  have hsRe : s₀.re = σ := by
    dsimp only [s₀]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, sub_zero, mul_zero, add_zero]
  have htRe : t₀.re = σ := by
    dsimp only [t₀]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, sub_zero, mul_zero, add_zero]
  have hdist : ‖t₀ - s₀‖ ≤ 1 / M := by
    have heq : t₀ - s₀ = Complex.I * ((t - u : ℝ) : ℂ) := by
      dsimp only [t₀, s₀, u]
      push_cast
      ring
    rw [heq, Complex.norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
    exact hgrid
  have hseriesBound :=
    norm_iteratedDeriv_logDeriv_le_vonMangoldt_log_weight χ (s := (σ : ℂ))
      (by simpa only [Complex.ofReal_re] using hσ) (n + 1)
  have hseriesNonneg :
    0 ≤ ∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ :=
    le_trans (norm_nonneg _) hseriesBound
  have hvariationAllowance :
    ‖t₀ - s₀‖ *
        (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ s₀.re) ≤
      (1 / (M : ℝ)) *
        (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ) := by
    rw [hsRe]
    exact mul_le_mul_of_nonneg_right hdist hseriesNonneg
  have hlarge' :
    B +
        ‖t₀ - s₀‖ *
          (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ s₀.re) ≤
      ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) t₀‖ := by
    calc
      _ ≤
          B +
            (1 / (M : ℝ)) *
              (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ) :=
        by linarith only [hvariationAllowance]
      _ ≤ _ := by simpa only [t₀] using hlarge
  have hnear :=
    iteratedDeriv_logDeriv_norm_lower_bound_nearby_vertical_point χ hχ (by rw [hsRe, htRe])
      (by
        rw [hsRe]; exact hσ)
      n B hlarge'
  exact ⟨m, hm, by simpa only [s₀, u] using hnear⟩

/--
Inputs: a scaled derivative lower bound at a center, its affine scaling identity, and a margin
that absorbs the variation allowed by the finite rational-height mesh.

Claim: one mesh point has the prescribed lower bound for the original logarithmic derivative.

Proof: divide the scaled norm bound by the positive scale power, rewrite the center as
`σ + I * t`, and apply the rational-height transfer theorem.

Role: connects Turán's scaled derivative output to the finite-height large-count interface.
-/
theorem exists_rational_height_large_of_scaled_derivative_lower_bound {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {σ t : ℝ} (hσ : 1 < σ) {T Mgrid : ℕ}
    (hMgrid : 0 < Mgrid) (htlo : -(T : ℝ) ≤ t) (hthi : t ≤ T) (n : ℕ) (R : ℝ) (hR : 0 < R) (c : ℂ)
    (hc : c = (σ : ℂ) + Complex.I * (t : ℂ)) (L B : ℝ)
    (hscale :
      iteratedDeriv n (logDeriv (fun z : ℂ => DirichletCharacter.LFunction χ (z * (R : ℂ) + c))) 0 =
        (R : ℂ) ^ (n + 1) * iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) c)
    (hbound :
      L ≤
        ‖(iteratedDeriv n (logDeriv (fun z : ℂ => DirichletCharacter.LFunction χ (z * (R : ℂ) + c)))
            0)‖)
    (hmargin :
      B +
          (1 / (Mgrid : ℝ)) *
            (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ) ≤
        L / R ^ (n + 1)) :
    ∃ m : ℤ,
      m ∈ Finset.Icc (-(T * Mgrid : ℤ)) (T * Mgrid : ℤ) ∧
        B ≤
          ‖(iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
              ((σ : ℂ) + Complex.I * (((m : ℝ) / (Mgrid : ℝ) : ℝ) : ℂ)))‖ := by
  have hscaled :
    L ≤ R ^ (n + 1) * ‖(iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) c)‖ := by
    calc
      L ≤
          ‖(iteratedDeriv n
              (logDeriv (fun z : ℂ => DirichletCharacter.LFunction χ (z * (R : ℂ) + c))) 0)‖ :=
        hbound
      _ = R ^ (n + 1) * ‖(iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) c)‖ := by
        rw [hscale, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hscaled' :
    L ≤ ‖(iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) c)‖ * R ^ (n + 1) := by
    calc
      L ≤ R ^ (n + 1) * ‖(iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) c)‖ := hscaled
      _ = _ := by ring
  have hbase :
    L / R ^ (n + 1) ≤ ‖(iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) c)‖ :=
    (div_le_iff₀ (pow_pos hR _)).2 hscaled'
  rw [hc] at hbase
  exact
    exists_rational_height_large_logDeriv_iteratedDeriv χ hχ σ hσ hMgrid htlo hthi n B
      (le_trans hmargin hbase)

/--
Inputs: a real part greater than one, a derivative order, and a positive error tolerance.
Claim: a positive integer mesh can make the Euler-series variation allowance smaller than the
tolerance.
Proof: the von Mangoldt logarithmic weight is summable and nonnegative, so its total sum divided
by the mesh size tends to zero; choose the mesh larger than that sum divided by the tolerance.
Role: supplies a finite rational-height mesh whenever a strict derivative lower-bound margin is
available.
-/
theorem exists_mesh_for_vonMangoldt_log_weight {σ : ℝ} (hσ : 1 < σ) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Mgrid : ℕ,
      0 < Mgrid ∧
        (1 / (Mgrid : ℝ)) *
            (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ) <
          ε := by
  let f : ℕ → ℝ := fun k => ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ
  have hsum : Summable f := by simpa only [f] using summable_vonMangoldt_log_weight hσ (n + 1)
  have hterm : ∀ k, 0 ≤ f k := by
    intro k
    dsimp only [f]
    apply div_nonneg
    · exact
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (pow_nonneg (Real.log_natCast_nonneg k) _)
    · exact Real.rpow_nonneg (by exact_mod_cast Nat.zero_le k) _
  have hS : 0 ≤ ∑' k : ℕ, f k := tsum_nonneg hterm
  obtain ⟨Mgrid, hMratio⟩ := exists_nat_gt ((∑' k : ℕ, f k) / ε)
  have hM : 0 < (Mgrid : ℝ) := by
    have hratio : 0 ≤ (∑' k : ℕ, f k) / ε := div_nonneg hS hε.le
    exact lt_of_le_of_lt hratio hMratio
  have hsumlt : (∑' k : ℕ, f k) / (Mgrid : ℝ) < ε := by
    apply (div_lt_iff₀ hM).2
    calc
      ∑' k : ℕ, f k < (Mgrid : ℝ) * ε := (div_lt_iff₀ hε).1 hMratio
      _ = ε * Mgrid := by ring
  refine ⟨Mgrid, Nat.cast_pos.mp hM, ?_⟩
  change (1 / (Mgrid : ℝ)) * (∑' k : ℕ, f k) < ε
  calc
    (1 / (Mgrid : ℝ)) * (∑' k : ℕ, f k) = (∑' k : ℕ, f k) / (Mgrid : ℝ) := by
      rw [one_div, div_eq_mul_inv]
      ring
    _ < ε := hsumlt

/--
Inputs: a character, a derivative order, a positive lower bound at a real height, and a window
radius measured in mesh steps.
Claim: a sufficiently fine positive integer mesh preserves half the lower bound at every mesh
point in the window.
Proof: choose the mesh so the von Mangoldt variation allowance is less than half the margin, then
apply the vertical variation estimate to each point in the window.
Role: turns one positive derivative detector into the block of grid values needed for window
incidence counting.
-/
theorem exists_mesh_for_vonMangoldt_log_weight_window {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {σ t : ℝ} (hσ : 1 < σ) (n K : ℕ) {B : ℝ} (hB : 0 < B)
    (hlarge :
      B ≤
        ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
            ((σ : ℂ) + Complex.I * (t : ℂ))‖) :
    ∃ M : ℕ,
      0 < M ∧
        ∀ m : ℤ,
          |t - (m : ℝ) / M| ≤ (K + 1 : ℝ) / M →
            B / 2 ≤
              ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                  ((σ : ℂ) + Complex.I * (((m : ℝ) / M : ℝ) : ℂ))‖ := by
  let ε : ℝ := B / (2 * (K + 1 : ℝ))
  have hε : 0 < ε := by
    dsimp only [ε]
    positivity
  obtain ⟨M, hM, hmesh⟩ := exists_mesh_for_vonMangoldt_log_weight hσ n hε
  have hK : 0 < (K + 1 : ℝ) := by positivity
  have hwindow :
    ((K + 1 : ℝ) / M) *
        (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ) <
      B / 2 := by
    calc
      _ =
          (K + 1 : ℝ) *
            ((1 / (M : ℝ)) *
              (∑' k : ℕ,
                ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ)) :=
        by field_simp
      _ < (K + 1 : ℝ) * ε := mul_lt_mul_of_pos_left hmesh hK
      _ = B / 2 := by
        dsimp only [ε]
        field_simp
  refine ⟨M, hM, ?_⟩
  intro m hdist
  apply forall_integer_height_grid_window_large χ hχ hσ M K n m hdist (B / 2)
  have hlarge' :
    B / 2 +
        ((K + 1 : ℝ) / M) *
          (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ) ≤
      ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
          ((σ : ℂ) + Complex.I * (t : ℂ))‖ := by
    linarith only [hwindow, hlarge]
  exact hlarge'

/-
Inputs: a nontrivial character, a derivative lower bound, and a minimum mesh size.
Claim: some positive mesh at least that large preserves half the derivative lower bound at every
mesh point in the prescribed window.
Proof: enlarge the mesh supplied by the variation estimate; the inverse mesh and its variation
allowance can only decrease.
Role: combines the grid lower bound with a later quantitative mesh-width requirement.
-/
theorem exists_mesh_for_vonMangoldt_log_weight_window_at_least {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {σ t : ℝ} (hσ : 1 < σ) (n K Mmin : ℕ) {B : ℝ}
    (hB : 0 < B)
    (hlarge :
      B ≤
        ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
            ((σ : ℂ) + Complex.I * (t : ℂ))‖) :
    ∃ M : ℕ,
      Mmin ≤ M ∧
        0 < M ∧
        ∀ m : ℤ,
          |t - (m : ℝ) / M| ≤ (K + 1 : ℝ) / M →
            B / 2 ≤
              ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                  ((σ : ℂ) + Complex.I * (((m : ℝ) / M : ℝ) : ℂ))‖ := by
  let S : ℝ := ∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ
  let ε : ℝ := B / (2 * (K + 1 : ℝ))
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact
      le_trans (norm_nonneg _)
        (norm_iteratedDeriv_logDeriv_le_vonMangoldt_log_weight χ (s := (σ : ℂ))
          (by simpa only [Complex.ofReal_re] using hσ) (n + 1))
  have hε : 0 < ε := by
    dsimp only [ε]; positivity
  obtain ⟨M₀, hM₀, hmesh₀⟩ := exists_mesh_for_vonMangoldt_log_weight hσ n hε
  let M := max M₀ Mmin
  have hM₀le : (M₀ : ℝ) ≤ (M : ℝ) := by exact_mod_cast le_max_left M₀ Mmin
  have hMpos : 0 < M := lt_of_lt_of_le hM₀ (le_max_left M₀ Mmin)
  have hinv : (M : ℝ)⁻¹ ≤ (M₀ : ℝ)⁻¹ := by
    have hdiv : 1 / (M : ℝ) ≤ 1 / (M₀ : ℝ) := one_div_le_one_div_of_le (Nat.cast_pos.mpr hM₀) hM₀le
    simpa only [one_div] using hdiv
  have hratio : ((K + 1 : ℝ) / M) ≤ ((K + 1 : ℝ) / M₀) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv (by positivity)
  have hvariation₀ : ((K + 1 : ℝ) / M₀) * S < B / 2 := by
    calc
      _ = (K + 1 : ℝ) * ((1 / (M₀ : ℝ)) * S) := by field_simp
      _ < (K + 1 : ℝ) * ε := mul_lt_mul_of_pos_left hmesh₀ (by positivity)
      _ = B / 2 := by
        dsimp only [ε]; field_simp
  have hvariation : ((K + 1 : ℝ) / M) * S < B / 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hratio hS) hvariation₀
  refine ⟨M, le_max_right M₀ Mmin, hMpos, ?_⟩
  intro m hdist
  apply forall_integer_height_grid_window_large χ hχ hσ M K n m hdist (B / 2)
  have hlower :
    B / 2 + ((K + 1 : ℝ) / M) * S ≤
      ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
          ((σ : ℂ) + Complex.I * (t : ℝ))‖ := by
    linarith only [hvariation, hlarge]
  exact hlower

/--
Inputs: an abscissa greater than one, a finite derivative-order range, a minimum mesh size, and
a positive lower bound for the factorial-normalized derivative.
Claim: one mesh preserves half that normalized lower bound at every nearby rational height, for
all characters and all derivative orders in the range.
Proof: multiply the vertical variation estimate by the same coefficient used in the detector,
sum the resulting finite order-dependent bounds, and choose a mesh for that common bound.
Role: retains the normalized detector signal when converting zero-height witnesses to a shared
height grid for the family large-sieve estimate.
-/
theorem exists_uniform_mesh_for_normalized_vonMangoldt_log_weight_window {σ : ℝ} (hσ : 1 < σ)
    (nmax K Mmin : ℕ) {B : ℝ} (hB : 0 < B) :
    ∃ M : ℕ,
      Mmin ≤ M ∧
        0 < M ∧
        ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (_hχ : χ ≠ 1) {t : ℝ} (n : ℕ),
          n ≤ nmax →
            B ≤
              ((σ - 1) ^ (n + 1) / (n.factorial : ℝ)) *
                ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                    ((σ : ℂ) + Complex.I * (t : ℂ))‖ →
            ∀ m : ℤ,
              |t - (m : ℝ) / M| ≤ (K + 1 : ℝ) / M →
                B / 2 ≤
                  ((σ - 1) ^ (n + 1) / (n.factorial : ℝ)) *
                    ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                        ((σ : ℂ) + Complex.I * (((m : ℝ) / M : ℝ) : ℂ))‖ := by
  let coeff : ℕ → ℝ := fun n => (σ - 1) ^ (n + 1) / (n.factorial : ℝ)
  let variationBound : ℕ → ℝ := fun n =>
    coeff n * ((2 / (σ - 1)) * (2 * ((n + 2 : ℕ) : ℝ) / (σ - 1)) ^ (n + 2))
  let Smax : ℝ := ∑ n ∈ Finset.range (nmax + 1), variationBound n
  have hη : 0 < σ - 1 := by linarith only [hσ]
  have hcoeff : ∀ n, 0 < coeff n := by
    intro n
    dsimp only [coeff]
    positivity
  have hvariationBound : ∀ n, 0 < variationBound n := by
    intro n
    dsimp only [variationBound]
    positivity
  have hSmax : 0 < Smax := by
    dsimp only [Smax]
    have hzero : 0 ∈ Finset.range (nmax + 1) := by
      simp only [Finset.mem_range]
      omega
    have hsum := Finset.single_le_sum (fun i hi => (hvariationBound i).le) hzero
    exact lt_of_lt_of_le (hvariationBound 0) hsum
  let ε : ℝ := B / (2 * (K + 1 : ℝ))
  have hε : 0 < ε := by
    dsimp only [ε]; positivity
  obtain ⟨M₀, hM₀ratio⟩ := exists_nat_gt (Smax / ε)
  have hM₀pos : 0 < (M₀ : ℝ) := by
    have hratio : 0 ≤ Smax / ε := div_nonneg hSmax.le hε.le
    exact lt_of_le_of_lt hratio hM₀ratio
  have hM₀bound : Smax / (M₀ : ℝ) < ε := by
    apply (div_lt_iff₀ hM₀pos).2
    simpa only [mul_comm] using (div_lt_iff₀ hε).1 hM₀ratio
  let M := max M₀ Mmin
  have hM₀le : (M₀ : ℝ) ≤ (M : ℝ) := by exact_mod_cast le_max_left M₀ Mmin
  have hMpos : 0 < M := lt_of_lt_of_le (Nat.cast_pos.mp hM₀pos) (le_max_left M₀ Mmin)
  have hMbound : Smax / (M : ℝ) < ε :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hSmax.le hM₀pos hM₀le) hM₀bound
  have hK : 0 < (K + 1 : ℝ) := by positivity
  have hvariation : ((K + 1 : ℝ) / M) * Smax < B / 2 := by
    calc
      _ = (K + 1 : ℝ) * (Smax / M) := by field_simp
      _ < (K + 1 : ℝ) * ε := mul_lt_mul_of_pos_left hMbound hK
      _ = B / 2 := by
        dsimp only [ε]; field_simp
  refine ⟨M, le_max_right M₀ Mmin, hMpos, ?_⟩
  intro N inst χ hχ t n hn hlarge m hdist
  have hseries := vonMangoldt_log_weight_sum_le_power hσ (n + 1)
  have hscaledSeries :
    coeff n * (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ) ≤
      Smax := by
    have hpoint := mul_le_mul_of_nonneg_left hseries (le_of_lt (hcoeff n))
    have hterm : variationBound n ≤ Smax := by
      dsimp only [Smax]
      exact
        Finset.single_le_sum (fun i hi => (hvariationBound i).le)
          (by
            simp only [Finset.mem_range]; omega)
    exact le_trans (by simpa only [variationBound] using hpoint) hterm
  have hvariationScaled :
    ((K + 1 : ℝ) / M) *
        (coeff n *
          (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ)) <
      B / 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hscaledSeries (by positivity)) hvariation
  have hmarginScaled :
    B / 2 +
        ((K + 1 : ℝ) / M) *
          (coeff n *
            (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ)) ≤
      coeff n *
        ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
            ((σ : ℂ) + Complex.I * (t : ℂ))‖ := by
    linarith only [hvariationScaled, hlarge]
  have hcoeffpos := hcoeff n
  have hmargin :
    B / (2 * coeff n) +
        ((K + 1 : ℝ) / M) *
          (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ) ≤
      ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
          ((σ : ℂ) + Complex.I * (t : ℂ))‖ := by
    have hmul :
      coeff n *
          (B / (2 * coeff n) +
            ((K + 1 : ℝ) / M) *
              (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ)) ≤
        coeff n *
          ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
              ((σ : ℂ) + Complex.I * (t : ℂ))‖ := by
      calc
        _ =
            coeff n * (B / (2 * coeff n)) +
              coeff n *
                (((K + 1 : ℝ) / M) *
                  (∑' k : ℕ,
                    ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ)) :=
          by rw [mul_add]
        _ =
            B / 2 +
              ((K + 1 : ℝ) / M) *
                (coeff n *
                  (∑' k : ℕ,
                    ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ)) :=
          by
          congr 1
          · field_simp [ne_of_gt hcoeffpos]
          · ring
        _ ≤ _ := hmarginScaled
    exact le_of_mul_le_mul_left hmul hcoeffpos
  have hraw :=
    forall_integer_height_grid_window_large χ hχ hσ M K n m hdist (B / (2 * coeff n)) hmargin
  have hmul := mul_le_mul_of_nonneg_left hraw (le_of_lt hcoeffpos)
  have hhalf : coeff n * (B / (2 * coeff n)) = B / 2 := by field_simp [ne_of_gt hcoeffpos]
  rw [hhalf] at hmul
  simpa only [coeff] using hmul

/--
Inputs: a derivative order range, a positive lower bound at a real height, and a minimum mesh size.
Claim: one positive mesh at least that large works for every character and height, and preserves
half any supplied lower bound for each derivative order in the range.
Proof: bound all variation series by an explicit function of the largest order, choose one mesh for
that bound, and apply the integer-grid variation estimate to each order.
Role: supplies a common height grid for a finite family of zero detectors with bounded orders.
-/
theorem exists_uniform_mesh_for_vonMangoldt_log_weight_window {σ : ℝ} (hσ : 1 < σ)
    (hσsmall : σ - 1 ≤ 1) (nmax K Mmin : ℕ) {B : ℝ} (hB : 0 < B) :
    ∃ M : ℕ,
      Mmin ≤ M ∧
        0 < M ∧
        ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (_hχ : χ ≠ 1) {t : ℝ} (n : ℕ),
          n ≤ nmax →
            B ≤
              ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                  ((σ : ℂ) + Complex.I * (t : ℂ))‖ →
            ∀ m : ℤ,
              |t - (m : ℝ) / M| ≤ (K + 1 : ℝ) / M →
                B / 2 ≤
                  ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                      ((σ : ℂ) + Complex.I * (((m : ℝ) / M : ℝ) : ℂ))‖ := by
  let Smax : ℝ := (2 / (σ - 1)) * (2 * ((nmax + 2 : ℕ) : ℝ) / (σ - 1)) ^ (nmax + 2)
  let ε : ℝ := B / (2 * (K + 1 : ℝ))
  have hSmax : 0 < Smax := by
    dsimp only [Smax]; positivity
  have hε : 0 < ε := by
    dsimp only [ε]; positivity
  obtain ⟨M₀, hMratio⟩ := exists_nat_gt (Smax / ε)
  have hM₀pos : 0 < (M₀ : ℝ) := by
    have hratio : 0 ≤ Smax / ε := div_nonneg hSmax.le hε.le
    exact lt_of_le_of_lt hratio hMratio
  have hM₀bound : Smax / (M₀ : ℝ) < ε := by
    apply (div_lt_iff₀ hM₀pos).2
    simpa only [mul_comm] using (div_lt_iff₀ hε).1 hMratio
  let M := max M₀ Mmin
  have hM₀le : (M₀ : ℝ) ≤ (M : ℝ) := by exact_mod_cast le_max_left M₀ Mmin
  have hMpos : 0 < M := lt_of_lt_of_le (Nat.cast_pos.mp hM₀pos) (le_max_left M₀ Mmin)
  have hMbound : Smax / (M : ℝ) < ε :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hSmax.le hM₀pos hM₀le) hM₀bound
  have hK : 0 < (K + 1 : ℝ) := by positivity
  have hvariation : ((K + 1 : ℝ) / M) * Smax < B / 2 := by
    calc
      _ = (K + 1 : ℝ) * (Smax / M) := by field_simp
      _ < (K + 1 : ℝ) * ε := mul_lt_mul_of_pos_left hMbound hK
      _ = B / 2 := by
        dsimp only [ε]; field_simp
  refine ⟨M, le_max_right M₀ Mmin, hMpos, ?_⟩
  intro N inst χ hχ t n hn hlarge m hdist
  have hseries := vonMangoldt_log_weight_sum_le_uniform_explicit hσ hσsmall n nmax hn
  have hvariationN :
    ((K + 1 : ℝ) / M) *
        (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ) <
      B / 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hseries (by positivity)) hvariation
  apply forall_integer_height_grid_window_large χ hχ hσ M K n m hdist (B / 2)
  linarith only [hvariationN, hlarge]

/--
Inputs: a nontrivial character, a derivative order, and a positive lower bound at a real height.
Claim: an explicit positive radius preserves half the derivative lower bound at every real height
within that radius.
Proof: choose the radius so the von Mangoldt variation allowance is at most half the lower bound,
then apply the nearby-height derivative estimate.
Role: turns a point detector into an interval detector for zero-height incidence arguments.
-/
theorem exists_real_height_window_large_of_derivative_lower_bound {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {σ t : ℝ} (hσ : 1 < σ) (n : ℕ) {B : ℝ} (hB : 0 < B)
    (hlarge :
      B ≤
        ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
            ((σ : ℂ) + Complex.I * (t : ℂ))‖) :
    ∃ δ : ℝ,
      0 < δ ∧
        ∀ u : ℝ,
          |t - u| ≤ δ →
            B / 2 ≤
              ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                  ((σ : ℂ) + Complex.I * (u : ℂ))‖ := by
  let S : ℝ := ∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact
      le_trans (norm_nonneg _)
        (norm_iteratedDeriv_logDeriv_le_vonMangoldt_log_weight χ (s := (σ : ℂ))
          (by simpa only [Complex.ofReal_re] using hσ) (n + 1))
  let δ : ℝ := B / (2 * (S + 1))
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  have hratio : S / (S + 1) ≤ 1 := by
    apply (div_le_one (by linarith only [hS])).2
    linarith only [hS]
  have hδS : δ * S ≤ B / 2 := by
    calc
      δ * S = (B / 2) * (S / (S + 1)) := by
        dsimp only [δ]
        field_simp
      _ ≤ (B / 2) * 1 := mul_le_mul_of_nonneg_left hratio (show 0 ≤ B / 2 by positivity)
      _ = B / 2 := by ring
  refine ⟨δ, hδ, ?_⟩
  intro u hu
  let s : ℂ := (σ : ℂ) + Complex.I * (u : ℂ)
  let t₀ : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  have hsRe : s.re = σ := by
    dsimp only [s]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, sub_zero, mul_zero, add_zero]
  have htRe : t₀.re = σ := by
    dsimp only [t₀]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, sub_zero, mul_zero, add_zero]
  have hdist : ‖t₀ - s‖ ≤ δ := by
    have heq : t₀ - s = Complex.I * ((t - u : ℝ) : ℂ) := by
      dsimp only [t₀, s]
      push_cast
      ring
    rw [heq, Complex.norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
    exact hu
  have hmargin :
    B / 2 +
        ‖t₀ - s‖ *
          (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ s.re) ≤
      ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) t₀‖ := by
    rw [hsRe]
    calc
      B / 2 + ‖t₀ - s‖ * S = ‖t₀ - s‖ * S + B / 2 := by ring
      _ ≤ δ * S + B / 2 := add_le_add_left (mul_le_mul_of_nonneg_right hdist hS) (B / 2)
      _ = B / 2 + δ * S := by ring
      _ ≤ B := by linarith only [hδS]
      _ ≤ _ := by simpa only [t₀] using hlarge
  have hnear :=
    iteratedDeriv_logDeriv_norm_lower_bound_nearby_vertical_point χ hχ (by rw [hsRe, htRe])
      (by
        rw [hsRe]; exact hσ)
      n (B / 2) hmargin
  simpa only [s] using hnear

/--
Inputs: a real part greater than one, a derivative order, a threshold, and a strict lower bound
for the scaled derivative.
Claim: there is a positive integer mesh whose variation allowance preserves that strict margin.
Proof: apply `exists_mesh_for_vonMangoldt_log_weight` with the difference between the scaled
lower bound and the threshold, then add the resulting strict allowance estimate.
Role: supplies the margin hypothesis of the scaled derivative transfer theorem.
-/
theorem exists_mesh_preserving_strict_derivative_margin {σ : ℝ} (hσ : 1 < σ) (n : ℕ) {L B R : ℝ}
    (hstrict : B < L / R ^ (n + 1)) :
    ∃ Mgrid : ℕ,
      0 < Mgrid ∧
        B +
            (1 / (Mgrid : ℝ)) *
              (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ) <
          L / R ^ (n + 1) := by
  let ε : ℝ := L / R ^ (n + 1) - B
  have hε : 0 < ε := sub_pos.mpr hstrict
  obtain ⟨Mgrid, hMgrid, hmesh⟩ := exists_mesh_for_vonMangoldt_log_weight hσ n hε
  have hmesh' :
    (1 / (Mgrid : ℝ)) *
        (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ) <
      ε := by
    simpa only [ε] using hmesh
  refine ⟨Mgrid, hMgrid, ?_⟩
  calc
    B +
          (1 / (Mgrid : ℝ)) *
            (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ) <
        B + ε :=
      add_lt_add_right hmesh' B
    _ = L / R ^ (n + 1) := by
      dsimp only [ε]
      ring

/--
Inputs: a nontrivial character, a scaled derivative lower bound, and a strict gap above the target.
Claim: some point in a finite rational-height grid has the target lower bound for the original
logarithmic derivative.
Proof: choose the mesh from the strict gap, then apply the scaled-to-unscaled finite-grid transfer.
Role: gives the direct interface from a positive Turán margin to the family large-sieve grid.
-/
theorem exists_rational_height_large_of_strict_scaled_derivative_bound {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {σ t : ℝ} (hσ : 1 < σ) {T : ℕ} (htlo : -(T : ℝ) ≤ t)
    (hthi : t ≤ T) (n : ℕ) (R : ℝ) (hR : 0 < R) (c : ℂ) (hc : c = (σ : ℂ) + Complex.I * (t : ℂ))
    (L B : ℝ)
    (hscale :
      iteratedDeriv n (logDeriv (fun z : ℂ => DirichletCharacter.LFunction χ (z * (R : ℂ) + c))) 0 =
        (R : ℂ) ^ (n + 1) * iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) c)
    (hbound :
      L ≤
        ‖(iteratedDeriv n (logDeriv (fun z : ℂ => DirichletCharacter.LFunction χ (z * (R : ℂ) + c)))
            0)‖)
    (hstrict : B < L / R ^ (n + 1)) :
    ∃ Mgrid : ℕ,
      0 < Mgrid ∧
        ∃ m : ℤ,
          m ∈ Finset.Icc (-(T * Mgrid : ℤ)) (T * Mgrid : ℤ) ∧
            B ≤
              ‖(iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                  ((σ : ℂ) + Complex.I * (((m : ℝ) / (Mgrid : ℝ) : ℝ) : ℂ)))‖ := by
  obtain ⟨Mgrid, hMgrid, hmargin⟩ := exists_mesh_preserving_strict_derivative_margin hσ n hstrict
  have hmargin' :
    B +
        (1 / (Mgrid : ℝ)) *
          (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ) ≤
      L / R ^ (n + 1) :=
    le_of_lt hmargin
  obtain ⟨m, hm, hlarge⟩ :=
    exists_rational_height_large_of_scaled_derivative_lower_bound χ hχ hσ hMgrid htlo hthi n R hR c
      hc L B hscale hbound hmargin'
  exact ⟨Mgrid, hMgrid, m, hm, hlarge⟩

/--
Inputs: a nontrivial character, a real part greater than one, a bounded height, and a strict
derivative lower bound at that height.
Claim: one point of a finite rational-height grid has the same lower bound.
Proof: choose a mesh whose vertical variation is smaller than the strict margin, then apply the
rational-height transfer theorem.
Role: converts the pointwise detector into a finite-grid witness for the family count.
-/
theorem exists_rational_height_large_of_strict_derivative_bound {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {σ t : ℝ} (hσ : 1 < σ) {T : ℕ} (htlo : -(T : ℝ) ≤ t)
    (hthi : t ≤ T) (n : ℕ) (B : ℝ)
    (hstrict :
      B <
        ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
            ((σ : ℂ) + Complex.I * (t : ℂ))‖) :
    ∃ Mgrid : ℕ,
      0 < Mgrid ∧
        ∃ m : ℤ,
          m ∈ Finset.Icc (-(T * Mgrid : ℤ)) (T * Mgrid : ℤ) ∧
            B ≤
              ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
                  ((σ : ℂ) + Complex.I * (((m : ℝ) / (Mgrid : ℝ) : ℝ) : ℂ))‖ := by
  have hmesh :=
    exists_mesh_preserving_strict_derivative_margin hσ n (L :=
      ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) ((σ : ℂ) + Complex.I * (t : ℂ))‖)
      (B := B) (R := 1) (by simpa only [one_pow, div_one] using hstrict)
  obtain ⟨Mgrid, hMgrid, hmargin⟩ := hmesh
  have hlarge :
    B +
        (1 / (Mgrid : ℝ)) *
          (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * (Real.log k) ^ (n + 1) / (k : ℝ) ^ σ) ≤
      ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ))
          ((σ : ℂ) + Complex.I * (t : ℂ))‖ := by
    exact le_of_lt (by simpa only [one_pow, div_one] using hmargin)
  obtain ⟨m, hm, hgrid⟩ :=
    exists_rational_height_large_logDeriv_iteratedDeriv χ hχ σ hσ hMgrid htlo hthi n B hlarge
  exact ⟨Mgrid, hMgrid, m, hm, hgrid⟩

/--
Inputs: a Dirichlet character, a point with real part greater than one, a derivative order, and
a finite truncation length.
Claim: the error after replacing the logarithmic derivative's Euler series by its first `M`
terms is bounded by the positive von Mangoldt tail over indices outside `Finset.range M`.
Proof: split the absolutely convergent twisted series into the finite range and its complement,
then bound the norm of each complementary term by its untwisted positive majorant.
Role: gives a uniform finite Dirichlet polynomial interface for the large-value step in zero
detection.
-/
theorem iteratedDeriv_logDeriv_finite_series_error_le_tail {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) (n M : ℕ) :
    ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s +
          (-1 : ℂ) ^ n *
            (∑ k ∈ Finset.range M,
              LSeries.term
                (LSeries.logMul^[n]
                  (fun j : ℕ ↦ χ (j : ZMod N) * (ArithmeticFunction.vonMangoldt j : ℂ)))
                s k)‖ ≤
      ∑' k : { k // k ∉ Finset.range M },
        ArithmeticFunction.vonMangoldt k.val * (Real.log k.val) ^ n / (k.val : ℝ) ^ s.re := by
  let f : ℕ → ℂ := fun k ↦ χ (k : ZMod N) * (ArithmeticFunction.vonMangoldt k : ℂ)
  let g : ℕ → ℂ := fun k ↦ (ArithmeticFunction.vonMangoldt k : ℂ)
  let τ : ℝ := (1 + s.re) / 2
  have hτ1 : 1 < τ := by
    dsimp only [τ]
    linarith only [hs]
  have hτs : τ < s.re := by
    dsimp only [τ]
    linarith only [hs]
  have hfτ : LSeriesSummable f (τ : ℂ) := by
    dsimp only [f]
    exact
      DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ
        (by simpa only [Complex.ofReal_re] using hτ1)
  have habf : LSeries.abscissaOfAbsConv f < s.re := by
    have hle : LSeries.abscissaOfAbsConv f ≤ (τ : EReal) := by
      simpa only [Complex.ofReal_re] using hfτ.abscissaOfAbsConv_le
    have hts : (τ : EReal) < (s.re : EReal) := by exact_mod_cast hτs
    exact hle.trans_lt hts
  have hEqf := LSeries.abscissaOfAbsConv_logPowMul (f := f) (m := n)
  have hfpow : LSeries.abscissaOfAbsConv (LSeries.logMul^[n] f) < s.re := by
    calc
      LSeries.abscissaOfAbsConv (LSeries.logMul^[n] f) = LSeries.abscissaOfAbsConv f := hEqf
      _ < s.re := habf
  have hfs : LSeriesSummable (LSeries.logMul^[n] f) s :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re hfpow
  have hfnormsumm : Summable (fun k : ℕ => ‖LSeries.term (LSeries.logMul^[n] f) s k‖) := by
    change Summable (fun k : ℕ => LSeries.term (LSeries.logMul^[n] f) s k) at hfs
    exact summable_norm_iff.mpr hfs
  have hnormsumm : Summable (fun k : ℕ => ‖LSeries.term (LSeries.logMul^[n] g) s k‖) := by
    have hgτ : LSeriesSummable g (τ : ℂ) := by
      dsimp only [g]
      exact
        ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa only [Complex.ofReal_re] using hτ1)
    have hle : LSeries.abscissaOfAbsConv g ≤ (τ : EReal) := by
      simpa only [Complex.ofReal_re] using hgτ.abscissaOfAbsConv_le
    have hts : (τ : EReal) < (s.re : EReal) := by exact_mod_cast hτs
    have hEqg := LSeries.abscissaOfAbsConv_logPowMul (f := g) (m := n)
    have hgpow : LSeries.abscissaOfAbsConv (LSeries.logMul^[n] g) < s.re := by
      calc
        LSeries.abscissaOfAbsConv (LSeries.logMul^[n] g) = LSeries.abscissaOfAbsConv g := hEqg
        _ < s.re := hle.trans_lt hts
    have hgs : LSeriesSummable (LSeries.logMul^[n] g) s :=
      LSeriesSummable_of_abscissaOfAbsConv_lt_re hgpow
    change Summable (fun k : ℕ => LSeries.term (LSeries.logMul^[n] g) s k) at hgs
    exact summable_norm_iff.mpr hgs
  have hterm :
    ∀ k : ℕ,
      ‖LSeries.term (LSeries.logMul^[n] g) s k‖ =
        ArithmeticFunction.vonMangoldt k * (Real.log k) ^ n / (k : ℝ) ^ s.re := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp only [LSeries.term_zero, norm_zero, ArithmeticFunction.map_zero, CharP.cast_eq_zero,
        zero_mul, zero_div]
    · exact norm_vonMangoldt_logMul_term_eq n k (Nat.pos_of_ne_zero hk)
  have hweightsumm :
    Summable (fun k : ℕ => ArithmeticFunction.vonMangoldt k * (Real.log k) ^ n / (k : ℝ) ^ s.re) :=
    hnormsumm.congr hterm
  have hsplit := hfs.sum_add_tsum_subtype_compl (Finset.range M)
  have hsplit' :
    (∑ k ∈ Finset.range M, LSeries.term (LSeries.logMul^[n] f) s k) +
        (∑' k : { k // k ∉ Finset.range M }, LSeries.term (LSeries.logMul^[n] f) s k.val) =
      LSeries (LSeries.logMul^[n] f) s := by
    simpa only [LSeries] using hsplit
  have hidentity := iteratedDeriv_logDeriv_eq_neg_twistedVonMangoldt_series χ hs n
  have hdecomp :
    iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s +
        (-1 : ℂ) ^ n * (∑ k ∈ Finset.range M, LSeries.term (LSeries.logMul^[n] f) s k) =
      -((-1 : ℂ) ^ n *
          (∑' k : { k // k ∉ Finset.range M }, LSeries.term (LSeries.logMul^[n] f) s k.val)) := by
    rw [hidentity, ← hsplit']
    ring
  have hTailNormSumm :
    Summable
      (fun k : { k // k ∉ Finset.range M } => ‖LSeries.term (LSeries.logMul^[n] f) s k.val‖) :=
    hfnormsumm.subtype _
  have hTailWeightSumm :
    Summable
      (fun k : { k // k ∉ Finset.range M } =>
        ArithmeticFunction.vonMangoldt k.val * (Real.log k.val) ^ n / (k.val : ℝ) ^ s.re) :=
    hweightsumm.subtype _
  have hTailCompare :
    ∑' k : { k // k ∉ Finset.range M }, ‖LSeries.term (LSeries.logMul^[n] f) s k.val‖ ≤
      ∑' k : { k // k ∉ Finset.range M },
        ArithmeticFunction.vonMangoldt k.val * (Real.log k.val) ^ n / (k.val : ℝ) ^ s.re := by
    apply Summable.tsum_le_tsum (fun k => ?_) hTailNormSumm hTailWeightSumm
    by_cases hk : k.val = 0
    · rw [hk]
      simp only [LSeries.term_zero, norm_zero, ArithmeticFunction.map_zero, CharP.cast_eq_zero,
        zero_mul, zero_div, le_refl]
    · exact twistedVonMangoldt_log_term_bound χ n k.val (s := s) (Nat.pos_of_ne_zero hk)
  calc
    ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s +
            (-1 : ℂ) ^ n * (∑ k ∈ Finset.range M, LSeries.term (LSeries.logMul^[n] f) s k)‖ =
        ‖∑' k : { k // k ∉ Finset.range M }, LSeries.term (LSeries.logMul^[n] f) s k.val‖ :=
      by
      rw [hdecomp]
      simp only [norm_neg, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    _ ≤ ∑' k : { k // k ∉ Finset.range M }, ‖LSeries.term (LSeries.logMul^[n] f) s k.val‖ :=
      norm_tsum_le_tsum_norm hTailNormSumm
    _ ≤
        ∑' k : { k // k ∉ Finset.range M },
          ArithmeticFunction.vonMangoldt k.val * (Real.log k.val) ^ n / (k.val : ℝ) ^ s.re :=
      hTailCompare

/-- For a positive rate at most one and a finite order range, choose one quantitative
cutoff above the prescribed minimum such that every Dirichlet character and every height
on `Re(s)=1+η` has normalized Euler-truncation error at most `exp(-D K)/8`.
Apply the common von Mangoldt tail to the character-independent series majorant.
This supplies a shared finite support for zero-family incidence and hybrid estimates. -/
theorem exists_uniform_quantitative_finite_series_cutoff (η D K : ℝ) (nmax cutoffMin : ℕ)
    (hη : 0 < η) (hηsmall : η ≤ 1) (hD : 0 ≤ D) (hK : 0 ≤ K) (hmin : 1 ≤ cutoffMin) :
    ∃ N : ℕ,
      cutoffMin ≤ N ∧
        1 ≤ N ∧
        η * Real.log ((N : ℝ) + 1) ≤
          2 * ((nmax : ℝ) + D * K + Real.log (24 * (Real.log 4 + 4))) + η * Real.log cutoffMin +
            η * Real.log 3 ∧
        ∀ n ≤ nmax,
          ∀ {q : ℕ} [NeZero q],
            ∀ χ : DirichletCharacter ℂ q,
              ∀ {s : ℂ},
                s.re = 1 + η →
                  η ^ (n + 1) / (n.factorial : ℝ) *
                      ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s +
                          (-1 : ℂ) ^ n *
                            (∑ k ∈ Finset.range (N + 1),
                              LSeries.term
                                (LSeries.logMul^[n]
                                  (fun j : ℕ ↦
                                    χ (j : ZMod q) * (ArithmeticFunction.vonMangoldt j : ℂ)))
                                s k)‖ ≤
                    Real.exp (-(D * K)) / 8 := by
  obtain ⟨N, hminN, hN, hlog, htail⟩ :=
    exists_uniform_normalized_vonMangoldt_cutoff η D K nmax cutoffMin hη hηsmall hD hK hmin
  refine ⟨N, hminN, hN, hlog, ?_⟩
  intro n hn q hq χ s hs
  have herr :=
    mul_le_mul_of_nonneg_left
      (iteratedDeriv_logDeriv_finite_series_error_le_tail χ
        (show 1 < s.re by
          rw [hs]; linarith only [hη])
        n (N + 1))
      (div_nonneg (pow_nonneg hη.le (n + 1)) (Nat.cast_nonneg n.factorial))
  rw [hs] at herr
  exact herr.trans (htail n hn)

/-- For a Dirichlet character at `Re(s) = 1 + η`, a positive rate at most one,
and nonnegative detector budgets, choose a cutoff above a prescribed minimum with
normalized Euler-series error at most `exp(-D K) / 8`. Its scaled logarithmic length
has the explicit bound inherited from the von Mangoldt cutoff.
This passes the quantitative tail certificate to differentiated finite Euler polynomials. -/
theorem exists_quantitative_normalized_finite_series_error_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1) (D K : ℝ) (hD : 0 ≤ D)
    (hK : 0 ≤ K) (n cutoffMin : ℕ) (hmin : 1 ≤ cutoffMin) {s : ℂ} (hs : s.re = 1 + η) :
    ∃ N : ℕ,
      cutoffMin ≤ N ∧
        1 ≤ N ∧
        η * Real.log ((N : ℝ) + 1) ≤
          2 * ((n : ℝ) + D * K + Real.log (24 * (Real.log 4 + 4))) + η * Real.log cutoffMin +
            η * Real.log 3 ∧
        (η ^ (n + 1) / (n.factorial : ℝ)) *
            ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s +
                (-1 : ℂ) ^ n *
                  (∑ k ∈ Finset.range (N + 1),
                    LSeries.term
                      (LSeries.logMul^[n]
                        (fun j : ℕ ↦ χ (j : ZMod q) * (ArithmeticFunction.vonMangoldt j : ℂ)))
                      s k)‖ ≤
          Real.exp (-(D * K)) / 8 := by
  obtain ⟨N, hminN, hN, hn, hlog, htail⟩ :=
    exists_quantitative_normalized_vonMangoldt_cutoff_ge η D K n cutoffMin hη hηsmall hD hK hmin
  have hre : 1 < s.re := by
    rw [hs]; linarith only [hη]
  have herr :=
    mul_le_mul_of_nonneg_left (iteratedDeriv_logDeriv_finite_series_error_le_tail χ hre n (N + 1))
      (div_nonneg (pow_nonneg hη.le (n + 1)) (Nat.cast_nonneg n.factorial))
  rw [hs] at herr
  exact ⟨N, hminN, hN, hlog, herr.trans htail⟩

/--
Inputs: a Dirichlet character, `σ > 1`, a derivative order, a cutoff, and a point satisfying
`Re(s) ≥ σ`.
Claim: Bound the error from truncating the higher logarithmic derivative by an explicit
expression in the cutoff, `σ`, and the derivative order.
Proof: Compare the tail at `Re(s)` with the nonnegative tail at `σ` and apply the integral bound
proved above.
Role: provides a quantitative finite Dirichlet-polynomial error for the character average after
zero detection.
-/
theorem iteratedDeriv_logDeriv_finite_series_error_le_explicit_of_re_ge {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ) (n cutoff : ℕ) (hcutoff : 1 ≤ cutoff) {s : ℂ}
    (hs : σ ≤ s.re) :
    ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s +
          (-1 : ℂ) ^ n *
            (∑ k ∈ Finset.range (cutoff + 1),
              LSeries.term
                (LSeries.logMul^[n]
                  (fun j : ℕ ↦ χ (j : ZMod N) * (ArithmeticFunction.vonMangoldt j : ℂ)))
                s k)‖ ≤
      ((σ - 1) / (2 * ((n + 1 : ℕ) : ℝ))) ^ (-((n + 1 : ℕ) : ℝ)) * (cutoff : ℝ) ^ (-(σ - 1) / 2) /
        ((σ - 1) / 2) := by
  have hs1 : 1 < s.re := lt_of_lt_of_le hσ hs
  have hError := iteratedDeriv_logDeriv_finite_series_error_le_tail χ hs1 n (cutoff + 1)
  have hsumσ := summable_vonMangoldt_log_weight hσ n
  have hsumS := summable_vonMangoldt_log_weight hs1 n
  have hsumTailS := hsumS.subtype (fun k ↦ k ∉ Finset.range (cutoff + 1))
  have hsumTailσ := hsumσ.subtype (fun k ↦ k ∉ Finset.range (cutoff + 1))
  have hTailCompare :
    (∑' k : { k // k ∉ Finset.range (cutoff + 1) },
        ArithmeticFunction.vonMangoldt k.val * (Real.log k.val) ^ n / (k.val : ℝ) ^ s.re) ≤
      (∑' k : { k // k ∉ Finset.range (cutoff + 1) },
        ArithmeticFunction.vonMangoldt k.val * (Real.log k.val) ^ n / (k.val : ℝ) ^ σ) := by
    apply Summable.tsum_le_tsum (fun k ↦ ?_) hsumTailS hsumTailσ
    have hcut : cutoff + 1 ≤ k.val :=
      Nat.le_of_not_gt (by simpa only [Finset.mem_range] using k.property)
    have hk2 : 2 ≤ k.val := (Nat.succ_le_succ hcutoff).trans hcut
    have hk1 : 1 ≤ k.val := le_trans (by norm_num only) hk2
    have hkR : (1 : ℝ) ≤ (k.val : ℝ) := by exact_mod_cast hk1
    have hpow : (k.val : ℝ) ^ σ ≤ (k.val : ℝ) ^ s.re := Real.rpow_le_rpow_of_exponent_le hkR hs
    have hden : 0 < (k.val : ℝ) ^ σ :=
      Real.rpow_pos_of_pos (by exact_mod_cast (Nat.zero_lt_of_lt hk1)) _
    have hnum : 0 ≤ ArithmeticFunction.vonMangoldt k.val * (Real.log k.val) ^ n :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (pow_nonneg (Real.log_natCast_nonneg k.val) n)
    exact div_le_div_of_nonneg_left hnum hden hpow
  calc
    _ ≤
        (∑' k : { k // k ∉ Finset.range (cutoff + 1) },
          ArithmeticFunction.vonMangoldt k.val * (Real.log k.val) ^ n / (k.val : ℝ) ^ s.re) :=
      hError
    _ ≤
        (∑' k : { k // k ∉ Finset.range (cutoff + 1) },
          ArithmeticFunction.vonMangoldt k.val * (Real.log k.val) ^ n / (k.val : ℝ) ^ σ) :=
      hTailCompare
    _ ≤
        ((σ - 1) / (2 * ((n + 1 : ℕ) : ℝ))) ^ (-((n + 1 : ℕ) : ℝ)) * (cutoff : ℝ) ^ (-(σ - 1) / 2) /
          ((σ - 1) / 2) :=
      vonMangoldt_log_weight_tail_le_explicit hσ n cutoff hcutoff

/--
Inputs: a real abscissa `σ > 1`, a derivative order, a minimum cutoff, and a positive tolerance.
Claim: some cutoff at least the requested minimum makes the explicit von Mangoldt Euler-tail
bound smaller than the tolerance.
Proof: write the bound as a constant times `cutoff ^ (-(σ - 1) / 2)` and use convergence of that
negative power to zero along the natural numbers.
Role: chooses a truncation long enough for prime support constraints while retaining the Euler-tail
error certificate.
-/
theorem exists_explicit_vonMangoldt_log_weight_cutoff_ge {σ : ℝ} (hσ : 1 < σ) (n cutoffMin : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ cutoff : ℕ,
      cutoffMin ≤ cutoff ∧
        ((σ - 1) / (2 * ((n + 1 : ℕ) : ℝ))) ^ (-((n + 1 : ℕ) : ℝ)) * (cutoff : ℝ) ^ (-(σ - 1) / 2) /
            ((σ - 1) / 2) <
          ε := by
  let cutoffExp := (σ - 1) / 2
  let α := (σ - 1) / (2 * ((n + 1 : ℕ) : ℝ))
  let C := α ^ (-((n + 1 : ℕ) : ℝ)) / cutoffExp
  have hcutoffExp : 0 < cutoffExp := by
    dsimp only [cutoffExp]
    linarith only [hσ]
  have hpow : Filter.Tendsto (fun m : ℕ ↦ (m : ℝ) ^ (-cutoffExp)) Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hcutoffExp).comp tendsto_natCast_atTop_atTop
  have hC : Filter.Tendsto (fun _ : ℕ ↦ C) Filter.atTop (nhds C) := tendsto_const_nhds
  have hbound : Filter.Tendsto (fun m : ℕ ↦ C * (m : ℝ) ^ (-cutoffExp)) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using hC.mul hpow
  have hsmall : ∀ᶠ m : ℕ in Filter.atTop, C * (m : ℝ) ^ (-cutoffExp) < ε :=
    hbound.eventually (Iio_mem_nhds hε)
  have hlarge : ∀ᶠ m : ℕ in Filter.atTop, cutoffMin ≤ m := Filter.eventually_ge_atTop cutoffMin
  obtain ⟨cutoff, hcutoff, hcutoffMin⟩ := (hsmall.and hlarge).exists
  have hExplicitBound :
    α ^ (-((n + 1 : ℕ) : ℝ)) * (cutoff : ℝ) ^ (-(σ - 1) / 2) / ((σ - 1) / 2) < ε := by
    have heq :
      α ^ (-((n + 1 : ℕ) : ℝ)) * (cutoff : ℝ) ^ (-(σ - 1) / 2) / ((σ - 1) / 2) =
        C * (cutoff : ℝ) ^ (-cutoffExp) := by
      dsimp only [C, α, cutoffExp]
      have hexp : -(σ - 1) / 2 = -((σ - 1) / 2) := by ring
      rw [hexp]
      ring
    rw [heq]
    exact hcutoff
  refine ⟨cutoff, hcutoffMin, ?_⟩
  simpa only [α] using hExplicitBound

/--
Inputs: a real abscissa `σ > 1`, a derivative order, and a positive tolerance.
Claim: some positive cutoff makes the explicit von Mangoldt Euler-tail bound smaller than the
tolerance.
Proof: use the minimum-cutoff form with minimum one.
Role: chooses a truncation length with a quantitative error certificate for the finite Euler sum.
-/
theorem exists_explicit_vonMangoldt_log_weight_cutoff {σ : ℝ} (hσ : 1 < σ) (n : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ cutoff : ℕ,
      1 ≤ cutoff ∧
        ((σ - 1) / (2 * ((n + 1 : ℕ) : ℝ))) ^ (-((n + 1 : ℕ) : ℝ)) * (cutoff : ℝ) ^ (-(σ - 1) / 2) /
            ((σ - 1) / 2) <
          ε := by
  obtain ⟨cutoff, hcutoff, herror⟩ := exists_explicit_vonMangoldt_log_weight_cutoff_ge hσ n 1 hε
  exact ⟨cutoff, hcutoff, herror⟩

/--
Inputs: a Dirichlet character, a fixed real threshold `σ > 1`, a derivative order, and a positive
error tolerance.
Claim: one finite truncation controls the differentiated Euler series uniformly for every point
whose real part is at least `σ`.
Proof: choose the truncation from the summable positive majorant at `σ`, then compare each tail
term at `s.re` with its value at `σ`.
Role: supplies a finite Dirichlet polynomial with a character independent error bound on a fixed
right half-plane.
-/
theorem exists_uniform_finite_series_error_lt_of_re_ge {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ,
      ∀ {s : ℂ},
        σ ≤ s.re →
          ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s +
                (-1 : ℂ) ^ n *
                  (∑ k ∈ Finset.range M,
                    LSeries.term
                      (LSeries.logMul^[n]
                        (fun j : ℕ ↦ χ (j : ZMod N) * (ArithmeticFunction.vonMangoldt j : ℂ)))
                      s k)‖ <
            ε := by
  let cutoffExp := (σ - 1) / 2
  let α := (σ - 1) / (2 * ((n + 1 : ℕ) : ℝ))
  let C := α ^ (-((n + 1 : ℕ) : ℝ)) / cutoffExp
  have hcutoffExp : 0 < cutoffExp := by
    dsimp only [cutoffExp]
    linarith only [hσ]
  have hpow : Filter.Tendsto (fun m : ℕ ↦ (m : ℝ) ^ (-cutoffExp)) Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hcutoffExp).comp tendsto_natCast_atTop_atTop
  have hC : Filter.Tendsto (fun _ : ℕ ↦ C) Filter.atTop (nhds C) := tendsto_const_nhds
  have hbound : Filter.Tendsto (fun m : ℕ ↦ C * (m : ℝ) ^ (-cutoffExp)) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using hC.mul hpow
  have hsmall : ∀ᶠ m : ℕ in Filter.atTop, C * (m : ℝ) ^ (-cutoffExp) < ε :=
    hbound.eventually (Iio_mem_nhds hε)
  have hlarge : ∀ᶠ m : ℕ in Filter.atTop, 1 ≤ m := Filter.eventually_ge_atTop 1
  obtain ⟨cutoff, hcutoff, hcutoffPos⟩ := (hsmall.and hlarge).exists
  have hExplicitBound :
    α ^ (-((n + 1 : ℕ) : ℝ)) * (cutoff : ℝ) ^ (-(σ - 1) / 2) / ((σ - 1) / 2) < ε := by
    have heq :
      α ^ (-((n + 1 : ℕ) : ℝ)) * (cutoff : ℝ) ^ (-(σ - 1) / 2) / ((σ - 1) / 2) =
        C * (cutoff : ℝ) ^ (-cutoffExp) := by
      dsimp only [C, α, cutoffExp]
      have hexp : -(σ - 1) / 2 = -((σ - 1) / 2) := by ring
      rw [hexp]
      ring
    rw [heq]
    exact hcutoff
  refine ⟨cutoff + 1, ?_⟩
  intro s hs
  have hError :=
    iteratedDeriv_logDeriv_finite_series_error_le_explicit_of_re_ge χ hσ n cutoff hcutoffPos hs
  have hExplicit :
    ((σ - 1) / (2 * ((n + 1 : ℕ) : ℝ))) ^ (-((n + 1 : ℕ) : ℝ)) * (cutoff : ℝ) ^ (-(σ - 1) / 2) /
        ((σ - 1) / 2) <
      ε := by
    simpa only [α] using hExplicitBound
  exact lt_of_le_of_lt hError hExplicit

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
