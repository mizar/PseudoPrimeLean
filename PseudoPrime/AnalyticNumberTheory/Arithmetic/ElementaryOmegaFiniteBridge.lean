/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ElementaryOmegaTail
import PseudoPrime.NumberTheory.PrimeIndexing

/-!
# The general bridge for `ElementaryOmegaFiniteStatement`

For `1 ≤ m < 163`, an inequality `m + 1 ≤ elementaryOmegaRhsReal (elementaryAnchor m)`
implies the required factor-count bound for every odd `n ≥ 750` with `ω(n) = m`.
The proof transfers the inequality along `elementaryAnchor m ≤ 4n` using monotonicity.

The identity `primePrimorialCount (m + 1) = 2 * oddPrimorial m` connects the anchor to the
count-indexed primorial certificates in `PseudoPrime.NumberTheory.PrimorialCertificates`.
-/

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- `PseudoPrime.AnalyticNumberTheory.Arithmetic.oddPrime` is
`PseudoPrime.NumberTheory.primeByIndex` shifted by one index (both unfold to the same `Nat.nth`). -/
theorem oddPrime_eq_primeByIndex_succ (k : ℕ) :
    oddPrime k =
      NumberTheory.primeByIndex (k + 1) :=
  rfl

/-- The count-indexed primorial with `m + 1` factors is twice the `m`-factor odd
primorial: `PseudoPrime.NumberTheory.primeByIndex 0 = 2` supplies the missing even prime. -/
theorem primePrimorialCount_succ_eq_two_mul_oddPrimorial (m : ℕ) :
    NumberTheory.primePrimorialCount (m + 1) =
      2 * oddPrimorial m := by
  induction m with
  | zero =>
    rw [NumberTheory.primePrimorialCount_succ,
      NumberTheory.primePrimorialCount_zero, NumberTheory.primeByIndex_zero,
      oddPrimorial_zero]
  | succ m
    ih =>
    rw [NumberTheory.primePrimorialCount_succ, ih,
      oddPrimorial_succ, ←
      oddPrime_eq_primeByIndex_succ]
    ring

/-- The real function `(7/5) * log z / loglog z`, used to transfer the elementary
factor-count bound from a primorial anchor to `z = 4n`. -/
noncomputable def elementaryOmegaRhsReal (z : ℝ) : ℝ :=
  elementaryOmegaConstant * Real.log z /
    Real.log (Real.log z)

/-- `PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryOmegaRhsReal` is monotone on
`[exp(exp 1), ∞)`: writing `u = log a`, `v = log b`,
this is `Real.log_div_self_antitoneOn` applied to `u ≤ v` (both `≥ exp 1`), cross-multiplied. -/
theorem elementaryOmegaRhsReal_mono {a b : ℝ} (ha : Real.exp (Real.exp 1) ≤ a) (hab : a ≤ b) :
    elementaryOmegaRhsReal a ≤
      elementaryOmegaRhsReal b := by
  have hepos : (0 : ℝ) < Real.exp (Real.exp 1) := Real.exp_pos _
  have hapos : 0 < a := hepos.trans_le ha
  have hbpos : 0 < b := hapos.trans_le hab
  set u : ℝ := Real.log a with hu_def
  set v : ℝ := Real.log b with hv_def
  have hu_ge : Real.exp 1 ≤ u := by
    calc
      Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := (Real.log_exp _).symm
      _ ≤ u := Real.log_le_log hepos ha
  have huv : u ≤ v := Real.log_le_log hapos hab
  have hv_ge : Real.exp 1 ≤ v := hu_ge.trans huv
  have h1e : (1 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h1u : (1 : ℝ) < u := h1e.trans_le hu_ge
  have h1v : (1 : ℝ) < v := h1e.trans_le hv_ge
  have hupos : 0 < u := by linarith
  have hvpos : 0 < v := by linarith
  have hlogu_pos : 0 < Real.log u := Real.log_pos h1u
  have hlogv_pos : 0 < Real.log v := Real.log_pos h1v
  have hsub : Real.log v / v ≤ Real.log u / u :=
    Real.log_div_self_antitoneOn (Set.mem_Ici.mpr hu_ge) (Set.mem_Ici.mpr hv_ge) huv
  have hfinal : u / Real.log u ≤ v / Real.log v := by
    rw [div_le_div_iff₀ hlogu_pos hlogv_pos]
    rw [div_le_div_iff₀ hvpos hupos] at hsub
    linarith only [hsub]
  have hCnonneg : 0 ≤ elementaryOmegaConstant := by
    unfold elementaryOmegaConstant; norm_num only
  have hscaled := mul_le_mul_of_nonneg_left hfinal hCnonneg
  unfold elementaryOmegaRhsReal
  rw [← hu_def, ← hv_def]
  calc
    elementaryOmegaConstant * u / Real.log u =
        elementaryOmegaConstant * (u / Real.log u) :=
      by ring
    _ ≤ elementaryOmegaConstant * (v / Real.log v) :=
      hscaled
    _ = elementaryOmegaConstant * v / Real.log v := by
      ring

/-- The anchor `max (4 * oddPrimorial m) 3000` for a factor count `m`.
It is at least `exp(exp 1)`. For odd `n ≥ 750` with `ω(n) = m`, both entries of the maximum
are at most `4n`, so monotonicity transfers a bound at this anchor to `4n`. -/
noncomputable def elementaryAnchor (m : ℕ) : ℝ :=
  max ((4 : ℝ) * (oddPrimorial m : ℝ)) 3000

/-- `exp(exp 1) < 3000`, so every `PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryAnchor`
lies in the monotonicity domain. -/
theorem exp_exp_one_lt_three_thousand : Real.exp (Real.exp 1) < 3000 := by
  have he : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
  calc
    Real.exp (Real.exp 1) < Real.exp (2.7182818286 : ℝ) := Real.exp_lt_exp.mpr he
    _ < 3000 := by
      have h8 : Real.exp (8 : ℝ) < (2981 : ℝ) := by
        have h1 : Real.exp (1 : ℝ) < 2.7182818286 := Real.exp_one_lt_d9
        have h8eq : Real.exp (8 : ℝ) = Real.exp 1 ^ 8 := by
          rw [← Real.exp_nat_mul]; norm_num only
        rw [h8eq]
        calc
          Real.exp 1 ^ 8 < (2.7182818286 : ℝ) ^ 8 :=
            pow_lt_pow_left₀ h1 (Real.exp_pos 1).le (by norm_num only)
          _ < 2981 := by norm_num only
      calc
        Real.exp (2.7182818286 : ℝ) < Real.exp (8 : ℝ) := Real.exp_lt_exp.mpr (by norm_num only)
        _ < 2981 := h8
        _ < 3000 := by norm_num only

/-- Every `PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryAnchor` lies in the domain where
`PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryOmegaRhsReal` is monotone. -/
theorem exp_exp_one_le_elementaryAnchor (m : ℕ) :
    Real.exp (Real.exp 1) ≤ elementaryAnchor m := exp_exp_one_lt_three_thousand.le.trans
    (le_max_right _ _)

/-- Every `PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryAnchor` is dominated by
`PseudoPrime.NumberTheory.characterModulus n`, for odd `n ≥ 750` whose
distinct-prime-factor count is `m`: the primorial term by
`PseudoPrime.AnalyticNumberTheory.Arithmetic.oddPrimorial_le_of_card_primeFactors`,
and the `3000` term directly from `750 ≤ n`. -/
theorem elementaryAnchor_le_characterModulus {n : ℕ} (hn : Odd n) (hn750 : 750 ≤ n) :
    elementaryAnchor n.primeFactors.card ≤
      (NumberTheory.characterModulus n : ℝ) := by
  have hprim : oddPrimorial n.primeFactors.card ≤ n :=
    oddPrimorial_le_of_card_primeFactors hn
  have hprimR :
    (4 : ℝ) * (oddPrimorial n.primeFactors.card : ℝ) ≤
      (NumberTheory.characterModulus n : ℝ) := by
    have hnat :
      4 * oddPrimorial n.primeFactors.card ≤
        NumberTheory.characterModulus n := by
      unfold NumberTheory.characterModulus; omega
    exact_mod_cast hnat
  have hqle : (3000 : ℝ) ≤ (NumberTheory.characterModulus n : ℝ) := by
    have hnat : (3000 : ℕ) ≤ NumberTheory.characterModulus n := by
      unfold NumberTheory.characterModulus; omega
    exact_mod_cast hnat
  exact max_le hprimR hqle

/-- **The reduction of `PseudoPrime.AnalyticNumberTheory.Arithmetic.ElementaryOmegaFiniteStatement`
to per-`m` numeric certificates.** Given a bound
`(m + 1 : ℝ) ≤ PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryOmegaRhsReal`
`(PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryAnchor m)` for every `1 ≤ m < 163`, the
finite statement follows by transferring that bound from the anchor up to the actual
`PseudoPrime.NumberTheory.characterModulus n` via
`PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryOmegaRhsReal_mono`. -/
theorem elementaryOmegaFiniteStatement_of_certificates
    (hcert : ∀ m : ℕ, 1 ≤ m → m < 163 →
      (m + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor m)) :
    ElementaryOmegaFiniteStatement := by
  intro n hn hn750 hmcard
  have hn1 : 1 < n := by omega
  have hm1 : 1 ≤ n.primeFactors.card := by
    rcases Nat.eq_zero_or_pos n.primeFactors.card with h0 | hpos
    · exfalso
      have hempty : n.primeFactors = ∅ := Finset.card_eq_zero.mp h0
      have hn0 : n ≠ 0 := by omega
      have := Nat.primeFactors_eq_empty.mp hempty
      omega
    · exact hpos
  have hcertm := hcert n.primeFactors.card hm1 hmcard
  have hmono := elementaryOmegaRhsReal_mono (exp_exp_one_le_elementaryAnchor n.primeFactors.card)
    (elementaryAnchor_le_characterModulus hn hn750)
  have hcardeq : (NumberTheory.characterModulus n).primeFactors.card =
      n.primeFactors.card + 1 := by
    have h1 := distinctPrimeFactorCount_characterModulus hn
    rwa [distinctPrimeFactorCount_eq_primeFactors_card,
      distinctPrimeFactorCount_eq_primeFactors_card] at h1
  rw [hcardeq]
  push_cast
  exact hcertm.trans hmono

end PseudoPrime.AnalyticNumberTheory.Arithmetic
