/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ReciprocalLevelChange
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimePowerCutoff

/-!
# The 2-adic correction to the character/zeta level-change ledger

Isolates the `p = 2` slice of the difference between the character-free and primitive-character
logarithmic and reciprocal Mangoldt sums, since `2` is the one prime for which the primitive
character's value need not be `1` in the ranges considered elsewhere in this development.

Defines `twoAdicLogCorrection` / `twoAdicReciprocalCorrection` (the finite sums over `2 ^ k`
alone) and the corresponding prime-power ledgers split into 2-adic and odd-prime slices
(`*PrimePowerDifferenceSum`, `twoAdic*PrimePowerDifference`, `oddPrime*PrimePowerDifference`).
Shows the odd-prime slice vanishes once the primitive character is `1` at every odd prime in the
cutoff range, so the full logarithmic/reciprocal difference reduces exactly to the 2-adic
correction (`*_eq_twoAdicCorrection_of_eq_one`). Bounds each correction case-by-case on
`χ̃(2) ∈ {0, 1, -1}`: zero and one give explicit closed-form or vanishing corrections, while
`χ̃(2) = -1` reduces the correction to its odd-exponent tail and bounds that tail by `(log x)²`
(logarithmic) and `(4/3) log 2` (reciprocal).
-/

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/--
Input: a real cutoff and a Dirichlet character.
Definition: the finite logarithmic correction supported on the prime powers `2 ^ k`
with `1 ≤ k ≤ ⌊log x / log 2⌋₊`.  The character term is evaluated at the primitive
character, matching the generic primitive level-change ledger.
Role: retains `Σ_k Λ(2^k) * log(x/2^k) * (1 - Re χ̃(2^k))` as the `p = 2` slice
of the difference between the character-free and primitive-character sums.
-/
noncomputable def twoAdicLogCorrection {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q) : ℝ :=
  ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
    (logWeightedMangoldtTerm x (2 ^ k) -
      (characterLogWeightedTerm x χ.primitiveCharacter
          (2 ^ k)).re)

/--
Input: a real cutoff and a Dirichlet character.
Definition: the finite reciprocal correction supported on the prime powers `2 ^ k`
with `1 ≤ k ≤ ⌊log x / log 2⌋₊`, using the primitive character in the character
term.  The indexing is shared with the logarithmic correction.
Role: retains `Σ_k Λ(2^k)/2^k * (1-2^k/x) * (1-Re χ̃(2^k))` for comparison with
the logarithmic correction on the same exponent range.
-/
noncomputable def twoAdicReciprocalCorrection {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q) : ℝ :=
  ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
    (reciprocalWeightedMangoldtTerm x (2 ^ k) -
      (characterReciprocalWeightedTerm x
          χ.primitiveCharacter (2 ^ k)).re)

/-- The logarithmic 2-adic correction has its prime-power closed form. -/
theorem twoAdicLogCorrection_eq_sum_of_isQuadratic {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q)
    (hχ : χ.primitiveCharacter.IsQuadratic) (hx : x ≠ 0) :
    twoAdicLogCorrection x χ =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
        (Real.log 2 * (Real.log x - k * Real.log 2) -
          Real.log 2 * (Real.log x - k * Real.log 2) *
            (if Odd k then (χ.primitiveCharacter 2).re else (χ.primitiveCharacter 2 ^ 2).re)) := by
  unfold twoAdicLogCorrection
  apply Finset.sum_congr rfl
  intro k hk
  have hkpos : k ≠ 0 := by
    have hk' := (Finset.mem_Icc.mp hk).1
    omega
  rw [logWeightedMangoldtTerm_prime_pow hx Nat.prime_two
      hkpos,
    characterLogWeightedTerm_primitive_re_prime_pow_of_isQuadratic
      x χ hχ hx Nat.prime_two hkpos]
  norm_num only

/-- The reciprocal 2-adic correction has its prime-power closed form. -/
theorem twoAdicReciprocalCorrection_eq_sum_of_isQuadratic {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hχ : χ.primitiveCharacter.IsQuadratic) :
    twoAdicReciprocalCorrection x χ =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
        (Real.log 2 / (2 : ℝ) ^ k * (1 - (2 : ℝ) ^ k / x) -
          Real.log 2 / (2 : ℝ) ^ k * (1 - (2 : ℝ) ^ k / x) *
            (if Odd k then (χ.primitiveCharacter 2).re else (χ.primitiveCharacter 2 ^ 2).re)) := by
  unfold twoAdicReciprocalCorrection
  apply Finset.sum_congr rfl
  intro k hk
  have hkpos : k ≠ 0 := by
    have hk' := (Finset.mem_Icc.mp hk).1
    omega
  rw [reciprocalWeightedMangoldtTerm_prime_pow
      Nat.prime_two hkpos,
    characterReciprocalWeightedTerm_primitive_re_prime_pow_of_isQuadratic
      x χ hχ Nat.prime_two hkpos]
  norm_num only

/-- If the quadratic primitive character has value `1` at `2` and `x ≠ 0`, the logarithmic
2-adic correction vanishes. -/
theorem twoAdicLogCorrection_eq_zero_of_apply_two_eq_one {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hχ : χ.primitiveCharacter.IsQuadratic) (hx : x ≠ 0)
    (h2 : χ.primitiveCharacter 2 = 1) :
    twoAdicLogCorrection x χ = 0 := by
  rw [twoAdicLogCorrection_eq_sum_of_isQuadratic x χ hχ
      hx]
  apply Finset.sum_eq_zero
  intro k hk
  simp only [h2, Complex.one_re, one_pow, ite_self, mul_one, sub_self]

/-- If the primitive character is trivial at `2`, the reciprocal correction vanishes. -/
theorem twoAdicReciprocalCorrection_eq_zero_of_apply_two_eq_one {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hχ : χ.primitiveCharacter.IsQuadratic)
    (h2 : χ.primitiveCharacter 2 = 1) :
    twoAdicReciprocalCorrection x χ = 0 := by
  rw [twoAdicReciprocalCorrection_eq_sum_of_isQuadratic
      x χ hχ]
  apply Finset.sum_eq_zero
  intro k hk
  simp only [h2, Complex.one_re, one_pow, ite_self, mul_one, sub_self]

/-- The real logarithmic weighted difference is an exact finite-sum decomposition. -/
theorem logWeightedMangoldtSum_sub_characterLogWeightedSum_re {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) :
    logWeightedMangoldtSum x -
        (characterLogWeightedSum x
            χ.primitiveCharacter).re =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        (logWeightedMangoldtTerm x n -
          (characterLogWeightedTerm x
              χ.primitiveCharacter n).re) := by
  simp only [logWeightedMangoldtSum,
    characterLogWeightedSum, Complex.re_sum]
  rw [Finset.sum_sub_distrib]

/-- The reciprocal weighted difference is an exact finite-sum decomposition. -/
theorem reciprocalWeightedMangoldtSum_sub_characterReciprocalWeightedSum_re {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) :
    reciprocalWeightedMangoldtSum x -
        (characterReciprocalWeightedSum x
            χ.primitiveCharacter).re =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        (reciprocalWeightedMangoldtTerm x n -
          (characterReciprocalWeightedTerm x
              χ.primitiveCharacter n).re) := by
  simp only [reciprocalWeightedMangoldtSum,
    characterReciprocalWeightedSum, Complex.re_sum]
  rw [Finset.sum_sub_distrib]

/-- A prime-power logarithmic character term agrees with the zeta term when the
character value at the underlying prime is one. -/
theorem characterLogWeightedTerm_primitive_re_prime_pow_eq_of_apply_prime_eq_one {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) {p k : ℕ} (hx : x ≠ 0) (hp : p.Prime) (hk : k ≠ 0)
    (hχp : χ.primitiveCharacter p = 1) :
    (characterLogWeightedTerm x χ.primitiveCharacter
          (p ^ k)).re =
      logWeightedMangoldtTerm x (p ^ k) := by
  rw [characterLogWeightedTerm_primitive_re_prime_pow x
      χ hx hp hk,
    logWeightedMangoldtTerm_prime_pow hx hp hk]
  simp only [hχp, one_pow, Complex.one_re, mul_one]

/-- The reciprocal analogue of the prime-power cancellation lemma. -/
theorem characterReciprocalWeightedTerm_primitive_re_prime_pow_eq_of_apply_prime_eq_one {q : ℕ}
    (x : ℝ) (χ : DirichletCharacter ℂ q) {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0)
    (hχp : χ.primitiveCharacter p = 1) :
    (characterReciprocalWeightedTerm x
          χ.primitiveCharacter (p ^ k)).re =
      reciprocalWeightedMangoldtTerm x (p ^ k) := by
  rw [characterReciprocalWeightedTerm_primitive_re_prime_pow
      x χ hp hk,
    reciprocalWeightedMangoldtTerm_prime_pow hp hk]
  simp only [hχp, one_pow, Complex.one_re, mul_one]

/-- The logarithmic prime-power ledger for the difference between the zeta and
primitive-character terms. -/
noncomputable def logPrimePowerDifferenceSum {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q) : ℝ :=
  ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
    (∑ p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
      (logWeightedMangoldtTerm x (p ^ k) -
        (characterLogWeightedTerm x χ.primitiveCharacter
            (p ^ k)).re))

/-- The `p = 2` slice of the logarithmic prime-power ledger. -/
noncomputable def twoAdicLogPrimePowerDifference {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q) : ℝ :=
  ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
    (∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter fun p ↦ p.Prime ∧ p = 2,
      (logWeightedMangoldtTerm x (p ^ k) -
        (characterLogWeightedTerm x χ.primitiveCharacter
            (p ^ k)).re))

/-- The odd-prime slice of the logarithmic prime-power ledger. -/
noncomputable def oddPrimeLogPrimePowerDifference {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q) :
    ℝ :=
  ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
    (∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter fun p ↦ p.Prime ∧ p ≠ 2,
      (logWeightedMangoldtTerm x (p ^ k) -
        (characterLogWeightedTerm x χ.primitiveCharacter
            (p ^ k)).re))

/-- The prime-power ledger splits exactly into its 2-adic and odd-prime slices. -/
theorem logPrimePowerDifferenceSum_eq_twoAdic_add_odd {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q) :
    logPrimePowerDifferenceSum x χ =
      twoAdicLogPrimePowerDifference x χ +
        oddPrimeLogPrimePowerDifference x χ := by
  unfold logPrimePowerDifferenceSum twoAdicLogPrimePowerDifference oddPrimeLogPrimePowerDifference
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  let s := (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter fun p ↦ p.Prime
  let f : ℕ → ℝ := fun p ↦
    logWeightedMangoldtTerm x (p ^ k) -
      (characterLogWeightedTerm x χ.primitiveCharacter
          (p ^ k)).re
  have hsplit := (Finset.sum_filter_add_sum_filter_not (s := s) (f := f) (p := fun p ↦ p = 2)).symm
  simpa only [s, f, one_div, Finset.sum_sub_distrib, ne_eq, Finset.filter_filter] using hsplit

/-- For `x ≠ 0`, if the primitive character has value `1` at every odd prime in each
prime-power cutoff, the odd-prime logarithmic slice vanishes. -/
theorem oddPrimeLogPrimePowerDifference_eq_zero_of_eq_one {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : x ≠ 0)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ → p.Prime → Odd p → (χ.primitiveCharacter p = 1)) :
    oddPrimeLogPrimePowerDifference x χ = 0 := by
  unfold oddPrimeLogPrimePowerDifference
  apply Finset.sum_eq_zero
  intro k hk
  apply Finset.sum_eq_zero
  intro p hp
  have hpmem : p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ := (Finset.mem_filter.mp hp).1
  have hpprime : p.Prime := (Finset.mem_filter.mp hp).2.1
  have hpne : p ≠ 2 := (Finset.mem_filter.mp hp).2.2
  have hpodd : Odd p := hpprime.odd_of_ne_two hpne
  rw [characterLogWeightedTerm_primitive_re_prime_pow_eq_of_apply_prime_eq_one
      x χ hx hpprime (Nat.ne_of_gt (Finset.mem_Icc.mp hk).1) (hodd hk hpmem hpprime hpodd)]
  simp only [sub_self]

/-- The reciprocal prime-power ledger for the zeta/character difference. -/
noncomputable def reciprocalPrimePowerDifferenceSum {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q) :
    ℝ :=
  ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
    (∑ p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
      (reciprocalWeightedMangoldtTerm x (p ^ k) -
        (characterReciprocalWeightedTerm x
            χ.primitiveCharacter (p ^ k)).re))

/-- The `p = 2` slice of the reciprocal prime-power ledger. -/
noncomputable def twoAdicReciprocalPrimePowerDifference {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) : ℝ :=
  ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
    (∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter fun p ↦ p.Prime ∧ p = 2,
      (reciprocalWeightedMangoldtTerm x (p ^ k) -
        (characterReciprocalWeightedTerm x
            χ.primitiveCharacter (p ^ k)).re))

/-- The odd-prime slice of the reciprocal prime-power ledger. -/
noncomputable def oddPrimeReciprocalPrimePowerDifference {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) : ℝ :=
  ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
    (∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter fun p ↦ p.Prime ∧ p ≠ 2,
      (reciprocalWeightedMangoldtTerm x (p ^ k) -
        (characterReciprocalWeightedTerm x
            χ.primitiveCharacter (p ^ k)).re))

/-- The reciprocal prime-power ledger splits into its 2-adic and odd-prime slices. -/
theorem reciprocalPrimePowerDifferenceSum_eq_twoAdic_add_odd {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) :
    reciprocalPrimePowerDifferenceSum x χ =
      twoAdicReciprocalPrimePowerDifference x χ +
        oddPrimeReciprocalPrimePowerDifference x χ := by
  unfold reciprocalPrimePowerDifferenceSum
    twoAdicReciprocalPrimePowerDifference
    oddPrimeReciprocalPrimePowerDifference
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  let s := (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter fun p ↦ p.Prime
  let f : ℕ → ℝ := fun p ↦
    reciprocalWeightedMangoldtTerm x (p ^ k) -
      (characterReciprocalWeightedTerm x
          χ.primitiveCharacter (p ^ k)).re
  have hsplit := (Finset.sum_filter_add_sum_filter_not (s := s) (f := f) (p := fun p ↦ p = 2)).symm
  simpa only [s, f, one_div, Finset.sum_sub_distrib, ne_eq, Finset.filter_filter] using hsplit

/-- Under prime-value-one cancellation, the odd-prime reciprocal slice vanishes. -/
theorem oddPrimeReciprocalPrimePowerDifference_eq_zero_of_eq_one {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ → p.Prime → Odd p → (χ.primitiveCharacter p = 1)) :
    oddPrimeReciprocalPrimePowerDifference x χ = 0 := by
  unfold oddPrimeReciprocalPrimePowerDifference
  apply Finset.sum_eq_zero
  intro k hk
  apply Finset.sum_eq_zero
  intro p hp
  have hpmem : p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ := (Finset.mem_filter.mp hp).1
  have hpprime : p.Prime := (Finset.mem_filter.mp hp).2.1
  have hpne : p ≠ 2 := (Finset.mem_filter.mp hp).2.2
  have hpodd : Odd p := hpprime.odd_of_ne_two hpne
  rw [characterReciprocalWeightedTerm_primitive_re_prime_pow_eq_of_apply_prime_eq_one
      x χ hpprime (Nat.ne_of_gt (Finset.mem_Icc.mp hk).1) (hodd hk hpmem hpprime hpodd)]
  simp only [sub_self]

/-- The logarithmic weighted difference is exactly its prime-power ledger. -/
theorem logWeightedMangoldtSum_sub_characterLogWeightedSum_re_eq_primePowerDifference {q : ℕ}
    (x : ℝ) (χ : DirichletCharacter ℂ q) (hx : 0 ≤ x) :
    logWeightedMangoldtSum x -
        (characterLogWeightedSum x
            χ.primitiveCharacter).re =
      logPrimePowerDifferenceSum x χ := by
  rw [logWeightedMangoldtSum_sub_characterLogWeightedSum_re
      x χ]
  let s := Finset.Ioc 0 ⌊x⌋₊
  let f : ℕ → ℝ := fun n ↦
    logWeightedMangoldtTerm x n -
      (characterLogWeightedTerm x χ.primitiveCharacter
          n).re
  have hzero : ∀ n : ℕ, ¬IsPrimePow n → f n = 0 := by
    intro n hn
    simp only [characterLogWeightedTerm, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      logWeightedMangoldtTerm_eq_zero_of_not_primePow
          hn,
      sub_self, f]
  have hcop : ∑ n ∈ s.filter fun n ↦ Nat.Coprime n 0, f n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnone : n = 1 := (Nat.coprime_zero_right n).mp (Finset.mem_filter.mp hn).2
    subst n
    simp only [logWeightedMangoldtTerm,
      characterLogWeightedTerm, Complex.ofReal_mul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.mul_im,
      zero_mul, add_zero, ArithmeticFunction.vonMangoldt_apply_one, Nat.cast_one, div_one, map_one,
      Complex.one_re, mul_one, sub_self, f]
  have hsplit :=
    (Finset.sum_filter_add_sum_filter_not (s := s) (f := f) (p := fun n ↦ ¬Nat.Coprime n 0)).symm
  have hfull : ∑ n ∈ s, f n = ∑ n ∈ s.filter fun n ↦ ¬Nat.Coprime n 0, f n := by
    calc
      ∑ n ∈ s, f n =
          (∑ n ∈ s.filter fun n ↦ ¬Nat.Coprime n 0, f n) +
            (∑ n ∈ s.filter fun n ↦ Nat.Coprime n 0, f n) :=
        by simpa only [not_not] using hsplit
      _ = ∑ n ∈ s.filter fun n ↦ ¬Nat.Coprime n 0, f n := by rw [hcop, add_zero]
  change (∑ n ∈ s, f n) = logPrimePowerDifferenceSum x χ
  rw [hfull]
  simpa only [f, Nat.coprime_zero_right, Finset.sum_sub_distrib,
    logPrimePowerDifferenceSum, one_div, dvd_zero,
    and_true] using
    (sum_not_coprime_eq_sum_prime_powers f 0 hx hzero)

/-- The reciprocal weighted difference is exactly its prime-power ledger. -/
theorem reciprocalWeightedMangoldtSum_sub_characterReciprocalWeightedSum_re_eq_primePowerDifference
    {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q) (hx : 0 ≤ x) :
    reciprocalWeightedMangoldtSum x -
        (characterReciprocalWeightedSum x
            χ.primitiveCharacter).re =
      reciprocalPrimePowerDifferenceSum x χ := by
  rw [reciprocalWeightedMangoldtSum_sub_characterReciprocalWeightedSum_re
      x χ]
  let s := Finset.Ioc 0 ⌊x⌋₊
  let f : ℕ → ℝ := fun n ↦
    reciprocalWeightedMangoldtTerm x n -
      (characterReciprocalWeightedTerm x
          χ.primitiveCharacter n).re
  have hzero : ∀ n : ℕ, ¬IsPrimePow n → f n = 0 := by
    intro n hn
    simp only [characterReciprocalWeightedTerm,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      reciprocalWeightedMangoldtTerm_eq_zero_of_not_primePow
          hn,
      sub_self, f]
  have hcop : ∑ n ∈ s.filter fun n ↦ Nat.Coprime n 0, f n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnone : n = 1 := (Nat.coprime_zero_right n).mp (Finset.mem_filter.mp hn).2
    subst n
    simp only [reciprocalWeightedMangoldtTerm,
      characterReciprocalWeightedTerm,
      Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.mul_re, Complex.div_natCast_re, Complex.ofReal_re, Complex.sub_re,
      Complex.one_re, Complex.div_ofReal_re, Complex.natCast_re, Complex.div_natCast_im,
      Complex.ofReal_im, zero_div, Complex.sub_im, Complex.one_im, Complex.div_ofReal_im,
      Complex.natCast_im, sub_self, mul_zero, sub_zero, Complex.mul_im, zero_mul, add_zero,
      ArithmeticFunction.vonMangoldt_apply_one, Nat.cast_one, div_one, one_div, map_one, mul_one, f]
  have hsplit :=
    (Finset.sum_filter_add_sum_filter_not (s := s) (f := f) (p := fun n ↦ ¬Nat.Coprime n 0)).symm
  have hfull : ∑ n ∈ s, f n = ∑ n ∈ s.filter fun n ↦ ¬Nat.Coprime n 0, f n := by
    calc
      ∑ n ∈ s, f n =
          (∑ n ∈ s.filter fun n ↦ ¬Nat.Coprime n 0, f n) +
            (∑ n ∈ s.filter fun n ↦ Nat.Coprime n 0, f n) :=
        by simpa only [not_not] using hsplit
      _ = ∑ n ∈ s.filter fun n ↦ ¬Nat.Coprime n 0, f n := by rw [hcop, add_zero]
  change
    (∑ n ∈ s, f n) =
      reciprocalPrimePowerDifferenceSum x χ
  rw [hfull]
  simpa only [f, Nat.coprime_zero_right, Finset.sum_sub_distrib,
    reciprocalPrimePowerDifferenceSum, one_div,
    dvd_zero, and_true] using
    (sum_not_coprime_eq_sum_prime_powers f 0 hx hzero)

/-- For `x ≠ 0`, value `1` at every odd prime in each prime-power cutoff leaves only
the 2-adic logarithmic slice. -/
theorem logPrimePowerDifferenceSum_eq_twoAdic_of_eq_one {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q)
    (hx : x ≠ 0)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ → p.Prime → Odd p → (χ.primitiveCharacter p = 1)) :
    logPrimePowerDifferenceSum x χ =
      twoAdicLogPrimePowerDifference x χ := by
  rw [logPrimePowerDifferenceSum_eq_twoAdic_add_odd,
    oddPrimeLogPrimePowerDifference_eq_zero_of_eq_one x
      χ hx hodd,
    add_zero]

/-- Value `1` at every odd prime in each prime-power cutoff leaves only the 2-adic
reciprocal slice. -/
theorem reciprocalPrimePowerDifferenceSum_eq_twoAdic_of_eq_one {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ → p.Prime → Odd p → (χ.primitiveCharacter p = 1)) :
    reciprocalPrimePowerDifferenceSum x χ =
      twoAdicReciprocalPrimePowerDifference x χ := by
  rw [reciprocalPrimePowerDifferenceSum_eq_twoAdic_add_odd,
    oddPrimeReciprocalPrimePowerDifference_eq_zero_of_eq_one
      x χ hodd,
    add_zero]

/-- The `p = 2` logarithmic ledger is the `2 ^ k` correction once the cutoff
membership of `2` is supplied. -/
theorem twoAdicLogPrimePowerDifference_eq_twoAdicLogCorrection_of_mem {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q)
    (hmem :
      ∀ {k : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊ → 2 ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊) :
    twoAdicLogPrimePowerDifference x χ = twoAdicLogCorrection x χ := by
  unfold twoAdicLogPrimePowerDifference twoAdicLogCorrection
  apply Finset.sum_congr rfl
  intro k hk
  have h2mem : 2 ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ := hmem hk
  apply Finset.sum_eq_single 2
  · intro p hp hne
    exact False.elim (hne (Finset.mem_filter.mp hp).2.2)
  · intro hnot
    exact False.elim (hnot (Finset.mem_filter.mpr ⟨h2mem, Nat.prime_two, rfl⟩))

/-- The reciprocal `p = 2` ledger has the same normalization interface. -/
theorem twoAdicReciprocalPrimePowerDifference_eq_twoAdicReciprocalCorrection_of_mem {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q)
    (hmem :
      ∀ {k : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊ → 2 ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊) :
    twoAdicReciprocalPrimePowerDifference x χ =
      twoAdicReciprocalCorrection x χ := by
  unfold twoAdicReciprocalPrimePowerDifference twoAdicReciprocalCorrection
  apply Finset.sum_congr rfl
  intro k hk
  have h2mem : 2 ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ := hmem hk
  apply Finset.sum_eq_single 2
  · intro p hp hne
    exact False.elim (hne (Finset.mem_filter.mp hp).2.2)
  · intro hnot
    exact False.elim (hnot (Finset.mem_filter.mpr ⟨h2mem, Nat.prime_two, rfl⟩))

/-- The logarithmic weighted difference reduces exactly to the 2-adic correction
under prime-value-one cancellation at every odd prime in the cutoff. -/
theorem logWeightedMangoldtSum_sub_characterLogWeightedSum_re_eq_twoAdicCorrection_of_eq_one {q : ℕ}
    (x : ℝ) (χ : DirichletCharacter ℂ q) (hx : 2 ≤ x)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ → p.Prime → Odd p → (χ.primitiveCharacter p = 1)) :
    logWeightedMangoldtSum x -
        (characterLogWeightedSum x
            χ.primitiveCharacter).re =
      twoAdicLogCorrection x χ := by
  rw [logWeightedMangoldtSum_sub_characterLogWeightedSum_re_eq_primePowerDifference
      x χ (by linarith)]
  rw [logPrimePowerDifferenceSum_eq_twoAdic_of_eq_one x
      χ (by linarith) hodd]
  exact
    twoAdicLogPrimePowerDifference_eq_twoAdicLogCorrection_of_mem
      x χ
      (fun hk ↦ two_mem_prime_cutoff_of_two_le hx hk)

/-- The reciprocal weighted difference has the analogous exact 2-adic reduction. -/
theorem reciprocalWeightedSum_sub_re_eq_twoAdicCorrection_of_eq_one {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 2 ≤ x)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ → p.Prime → Odd p → (χ.primitiveCharacter p = 1)) :
    reciprocalWeightedMangoldtSum x -
        (characterReciprocalWeightedSum x
            χ.primitiveCharacter).re =
      twoAdicReciprocalCorrection x χ := by
  rw [reciprocalWeightedMangoldtSum_sub_characterReciprocalWeightedSum_re_eq_primePowerDifference
      x χ (by linarith)]
  rw [reciprocalPrimePowerDifferenceSum_eq_twoAdic_of_eq_one
      x χ hodd]
  exact
    twoAdicReciprocalPrimePowerDifference_eq_twoAdicReciprocalCorrection_of_mem
      x χ
      (fun hk ↦ two_mem_prime_cutoff_of_two_le hx hk)

/-- In the `χ̃(2)=0` branch, the logarithmic correction is bounded by the
standard half-square prime-power estimate. -/
theorem twoAdicLogCorrection_le_half_log_sq_of_apply_two_eq_zero {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : x ≠ 0) (h2 : χ.primitiveCharacter 2 = 0) :
    twoAdicLogCorrection x χ ≤
      (Real.log x) ^ 2 / 2 := by
  unfold twoAdicLogCorrection
  calc
    _ =
        ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
          logWeightedMangoldtTerm x (2 ^ k) :=
      by
      apply Finset.sum_congr rfl
      intro k hk
      have hkpos : k ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hk).1
      rw [characterLogWeightedTerm_primitive_re_prime_pow
          x χ hx Nat.prime_two hkpos]
      have h2' : χ.primitiveCharacter (↑(2 : ℕ)) = 0 := by simpa only [Nat.cast_ofNat] using h2
      have h2pow : (χ.primitiveCharacter (↑(2 : ℕ)) ^ k).re = 0 := by
        rw [h2', zero_pow hkpos]
        norm_num only [Complex.zero_re]
      rw [h2pow]
      simp only [mul_zero, sub_zero]
    _ ≤ (Real.log x) ^ 2 / 2 :=
      sum_logWeightedMangoldtTerm_prime_pow_le hx
        Nat.prime_two

/-- In the `χ̃(2)=0` branch, the reciprocal correction is bounded by `log 2`. -/
theorem twoAdicReciprocalCorrection_le_log_two_of_apply_two_eq_zero {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : 0 < x) (h2 : χ.primitiveCharacter 2 = 0) :
    twoAdicReciprocalCorrection x χ ≤ Real.log 2 := by
  unfold twoAdicReciprocalCorrection
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊, Real.log 2 / (2 : ℝ) ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      have hkpos : k ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hk).1
      rw [characterReciprocalWeightedTerm_primitive_re_prime_pow
          x χ Nat.prime_two hkpos]
      have h2' : χ.primitiveCharacter (↑(2 : ℕ)) = 0 := by simpa only [Nat.cast_ofNat] using h2
      have h2pow : (χ.primitiveCharacter (↑(2 : ℕ)) ^ k).re = 0 := by
        rw [h2', zero_pow hkpos]
        norm_num only [Complex.zero_re]
      rw [h2pow]
      simpa only [Nat.cast_ofNat, mul_zero, sub_zero] using
        (reciprocalWeightedMangoldtTerm_prime_pow_le hx
          Nat.prime_two hkpos)
    _ ≤ Real.log 2 := by
      have hsum :=
        sum_log_div_prime_pow_le (p := 2) (N :=
          ⌊Real.log x / Real.log 2⌋₊) Nat.prime_two
      norm_num only [Nat.cast_ofNat] at hsum
      rw [div_one] at hsum
      exact hsum

/-- The `χ̃(2)=1` logarithmic branch has zero correction. -/
theorem twoAdicLogCorrection_le_half_log_sq_of_apply_two_eq_one {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hχ : χ.primitiveCharacter.IsQuadratic) (hx : x ≠ 0)
    (h2 : χ.primitiveCharacter 2 = 1) :
    twoAdicLogCorrection x χ ≤
      (Real.log x) ^ 2 / 2 := by
  rw [twoAdicLogCorrection_eq_zero_of_apply_two_eq_one x
      χ hχ hx h2]
  positivity

/-- The `χ̃(2)=1` reciprocal branch has zero correction. -/
theorem twoAdicReciprocalCorrection_le_log_two_of_apply_two_eq_one {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hχ : χ.primitiveCharacter.IsQuadratic)
    (h2 : χ.primitiveCharacter 2 = 1) :
    twoAdicReciprocalCorrection x χ ≤ Real.log 2 := by
  rw [twoAdicReciprocalCorrection_eq_zero_of_apply_two_eq_one
      x χ hχ h2]
  exact Real.log_nonneg (by norm_num only)

/-- In the `χ̃(2)=-1` logarithmic branch, only odd exponents contribute. -/
theorem twoAdicLogCorrection_eq_odd_sum_of_apply_two_eq_neg_one {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hχ : χ.primitiveCharacter.IsQuadratic) (hx : x ≠ 0)
    (h2 : χ.primitiveCharacter 2 = -1) :
    twoAdicLogCorrection x χ =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
        if Odd k then 2 * (Real.log 2 * (Real.log x - k * Real.log 2)) else 0 := by
  rw [twoAdicLogCorrection_eq_sum_of_isQuadratic x χ hχ
      hx]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [h2, Complex.neg_re, Complex.one_re, even_two, Even.neg_pow, one_pow, mul_ite, mul_neg,
    mul_one]
  split_ifs <;> ring

/-- In the `χ̃(2)=-1` reciprocal branch, only odd exponents contribute. -/
theorem twoAdicReciprocalCorrection_eq_odd_sum_of_apply_two_eq_neg_one {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hχ : χ.primitiveCharacter.IsQuadratic)
    (h2 : χ.primitiveCharacter 2 = -1) :
    twoAdicReciprocalCorrection x χ =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
        if Odd k then 2 * (Real.log 2 / (2 : ℝ) ^ k * (1 - (2 : ℝ) ^ k / x)) else 0 := by
  rw [twoAdicReciprocalCorrection_eq_sum_of_isQuadratic
      x χ hχ]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [h2, Complex.neg_re, Complex.one_re, even_two, Even.neg_pow, one_pow, mul_ite, mul_neg,
    mul_one]
  split_ifs <;> ring

/-! The `χ̃(2) = -1` logarithmic branch is controlled by the full weighted tail. -/

/-- The odd logarithmic correction is bounded by the square-log envelope. -/
theorem twoAdicLogCorrection_le_log_sq_of_apply_two_eq_neg_one {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hχ : χ.primitiveCharacter.IsQuadratic) (hx : 2 ≤ x)
    (h2 : χ.primitiveCharacter 2 = -1) :
    twoAdicLogCorrection x χ ≤ (Real.log x) ^ 2 := by
  rw [twoAdicLogCorrection_eq_odd_sum_of_apply_two_eq_neg_one
      x χ hχ (ne_of_gt (lt_of_lt_of_le (by norm_num only) hx)) h2]
  let K := ⌊Real.log x / Real.log 2⌋₊
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have hquot_nonneg : 0 ≤ Real.log x / Real.log 2 :=
    div_nonneg (Real.log_nonneg (by linarith)) hlog2.le
  have hfull :
    ∑ k ∈ Finset.Icc 1 K, 2 * (Real.log 2 * (Real.log x - k * Real.log 2)) ≤ (Real.log x) ^ 2 := by
    rw [← Finset.mul_sum]
    nlinarith [sum_log_weight_le_half_sq (a :=
        Real.log 2) (L := Real.log x) (K := K)]
  apply le_trans ?_ hfull
  apply Finset.sum_le_sum
  intro k hk
  split_ifs with hodd
  · rfl
  · have hklog : (k : ℝ) ≤ Real.log x / Real.log 2 := by
      apply (Nat.le_floor_iff hquot_nonneg).mp
      exact (Finset.mem_Icc.mp hk).2
    have hlog : (k : ℝ) * Real.log 2 ≤ Real.log x := (le_div_iff₀ hlog2).mp hklog
    have hnonneg : 0 ≤ Real.log 2 * (Real.log x - k * Real.log 2) :=
      mul_nonneg hlog2.le (by linarith)
    linarith

/-! The reciprocal odd tail has the corresponding explicit `4/3` constant. -/

/-- The odd reciprocal correction is bounded by `(4 / 3) * log 2`. -/
theorem twoAdicReciprocalCorrection_le_four_thirds_log_two_of_apply_two_eq_neg_one {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hχ : χ.primitiveCharacter.IsQuadratic) (hx : 2 ≤ x)
    (h2 : χ.primitiveCharacter 2 = -1) :
    twoAdicReciprocalCorrection x χ ≤
      (4 / 3) * Real.log 2 := by
  rw [twoAdicReciprocalCorrection_eq_odd_sum_of_apply_two_eq_neg_one
      x χ hχ h2]
  let K := ⌊Real.log x / Real.log 2⌋₊
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have hquot_nonneg : 0 ≤ Real.log x / Real.log 2 :=
    div_nonneg (Real.log_nonneg (by linarith)) hlog2.le
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 K, (if Odd k then 2 * (Real.log 2 / (2 : ℝ) ^ k) else 0) := by
      apply Finset.sum_le_sum
      intro k hk
      split_ifs with hodd
      · have hpow : (2 : ℝ) ^ k / x ≤ 1 := by
          have hklog : (k : ℝ) ≤ Real.log x / Real.log 2 := by
            apply (Nat.le_floor_iff hquot_nonneg).mp
            exact (Finset.mem_Icc.mp hk).2
          have hlog : (k : ℝ) * Real.log 2 ≤ Real.log x :=
            (le_div_iff₀ (Real.log_pos (by norm_num only))).mp hklog
          have hpow' : (2 : ℝ) ^ k ≤ x := by
            have hxpos : 0 < x := lt_of_lt_of_le (by norm_num only) hx
            have h :=
              Real.rpow_le_of_le_log (x := (2 : ℝ) ^ k) (y := x) (z := (1 : ℝ)) hxpos
                (by simpa only [Real.log_pow, one_mul] using hlog)
            simpa only [ge_iff_le, Real.rpow_one] using h
          have hdiv :=
            (div_le_iff₀ (lt_of_lt_of_le (by norm_num only) hx)).mpr
              (show (2 : ℝ) ^ k ≤ 1 * x by simpa only [one_mul] using hpow')
          simpa only [ge_iff_le] using hdiv
        have hnonneg : 0 ≤ Real.log 2 / (2 : ℝ) ^ k := by positivity
        have hratio : 0 ≤ (2 : ℝ) ^ k / x := by positivity
        have hfactor : 0 ≤ 1 - (2 : ℝ) ^ k / x := by linarith
        nlinarith
      · rfl
    _ = 2 * Real.log 2 * (∑ k ∈ Finset.Icc 1 K, (if Odd k then (1 : ℝ) / (2 : ℝ) ^ k else 0)) := by
      calc
        _ = ∑ k ∈ Finset.Icc 1 K, 2 * Real.log 2 * (if Odd k then (1 : ℝ) / (2 : ℝ) ^ k else 0) :=
          by
          apply Finset.sum_congr rfl
          intro k hk
          split_ifs <;> ring
        _ = _ := by rw [Finset.mul_sum]
    _ ≤ (4 / 3) * Real.log 2 := by
      have hsum := sum_odd_inv_two_pow_le K
      nlinarith [hlog2.le]

/-!
Input/assumptions: `x ≥ 2`, a quadratic primitive character, and `χ̃(2) = -1`.
Conclusion: the uniform odd-tail correction bound is absorbed by the `c=0` correction envelope
together with the `log 4` conductor saving.
Content: this is the reciprocal-side comparison used to remove the `c=-1` branch from the
analytic worst case; it compares the proved envelopes, so no identification of two characters
is required.
Proof: use the `4/3 * log 2` odd-tail bound and the positivity of `log 2`.
Role: bounds the reciprocal correction by `log 2 + (1-1/x)*log 2`;
the second term equals `(1-1/x)*log 4/2`.
-/

theorem twoAdicReciprocalCorrection_neg_one_absorbed_by_log_four_saving {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hχ : χ.primitiveCharacter.IsQuadratic) (hx : (2 : ℝ) ≤ x)
    (h2 : χ.primitiveCharacter 2 = -1) :
    twoAdicReciprocalCorrection x χ ≤
      Real.log 2 + (1 - 1 / x) * Real.log 2 := by
  have hcorr :=
    twoAdicReciprocalCorrection_le_four_thirds_log_two_of_apply_two_eq_neg_one
      x χ hχ (by linarith) h2
  have hxpos : 0 < x := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have hinv : 1 / x ≤ (2 : ℝ) / 3 := by
    apply (div_le_iff₀ hxpos).mpr
    nlinarith
  nlinarith

/-!
Input/assumptions: `x ≥ 2`, a quadratic primitive character, and one of the three possible values
  at `2`.
Conclusion: all logarithmic correction branches share a single square-log upper envelope.
Content: the zero branch uses the sharper half-square bound, the one branch is exactly zero, and
the negative-one branch uses the odd-tail bound already proved above.
Proof: split the value at `2` and apply the branch-specific correction theorem.
Role: supplies `twoAdicLogCorrection x χ ≤ (log x)²` uniformly over the three values at `2`.
-/

theorem twoAdicLogCorrection_le_log_sq_of_apply_two_mem {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q)
    (hχ : χ.primitiveCharacter.IsQuadratic) (hx : (2 : ℝ) ≤ x)
    (h2 : χ.primitiveCharacter 2 = 0 ∨ χ.primitiveCharacter 2 = 1 ∨ χ.primitiveCharacter 2 = -1) :
    twoAdicLogCorrection x χ ≤ (Real.log x) ^ 2 := by
  have hxne : x ≠ 0 := by linarith
  rcases h2 with h2 | h2 | h2
  · have h :=
      twoAdicLogCorrection_le_half_log_sq_of_apply_two_eq_zero
        x χ hxne h2
    nlinarith [sq_nonneg (Real.log x)]
  · rw [twoAdicLogCorrection_eq_zero_of_apply_two_eq_one
        x χ hχ hxne h2]
    positivity
  · exact
      twoAdicLogCorrection_le_log_sq_of_apply_two_eq_neg_one
        x χ hχ hx h2

/-! The reciprocal corrections also admit one uniform envelope over the three values at `2`. -/

/-- The three reciprocal correction branches are bounded by the odd-tail envelope. -/
theorem twoAdicReciprocalCorrection_le_four_thirds_log_two_of_apply_two_mem {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hχ : χ.primitiveCharacter.IsQuadratic) (hx : 2 ≤ x)
    (h2 : χ.primitiveCharacter 2 = 0 ∨ χ.primitiveCharacter 2 = 1 ∨ χ.primitiveCharacter 2 = -1) :
    twoAdicReciprocalCorrection x χ ≤
      (4 / 3) * Real.log 2 := by
  rcases h2 with h2 | h2 | h2
  · have h :=
      twoAdicReciprocalCorrection_le_log_two_of_apply_two_eq_zero
        x χ (lt_of_lt_of_le (by norm_num only) hx) h2
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num only)
    nlinarith
  · rw [twoAdicReciprocalCorrection_eq_zero_of_apply_two_eq_one
        x χ hχ h2]
    positivity
  · exact
      twoAdicReciprocalCorrection_le_four_thirds_log_two_of_apply_two_eq_neg_one
        x χ hχ hx h2

/-! The alternating linear finite sum used for the logarithmic correction difference. -/

/-- A finite alternating linear tail is bounded by its first positive term. -/
private lemma alternating_linear_sum_le_first {A b : ℝ} (hA : 2 * b ≤ A) (hb : 0 ≤ b) (K : ℕ)
    (hK : (K : ℝ) * b ≤ A) :
    (∑ k ∈ Finset.range K, (if Even k then A - (k + 1) * b else -(A - (k + 1) * b))) ≤ A - b := by
  have hformula :
    ∀ (K : ℕ),
      (∑ k ∈ Finset.range K, (if Even k then A - (k + 1) * b else -(A - (k + 1) * b))) =
        if Even K then (K / 2 : ℝ) * b else A - ((K + 1) / 2 : ℝ) * b := by
    intro K
    induction K using Nat.twoStepInduction with
    | zero =>
      simp only [Finset.range_zero, neg_sub, Finset.sum_empty, Even.zero, ↓reduceIte,
        CharP.cast_eq_zero, zero_div, zero_mul]
    | one =>
      have hEven0 : Even 0 := Even.zero
      have hNotEven1 : ¬Even 1 := by decide
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, hEven0, hNotEven1, Nat.cast_zero,
        Nat.cast_one, one_mul, ite_true, ite_false, zero_add]
      ring
    | more K hK0 hK1 =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, hK0]
      by_cases hEven : Even K
      · have hEven2 : Even (K + 2) := by
          obtain ⟨j, rfl⟩ := hEven
          use j + 1
          omega
        have hNotEven1 : ¬Even (K + 1) := by
          intro h
          obtain ⟨i, hi⟩ := hEven
          obtain ⟨j, hj⟩ := h
          omega
        simp only [hEven, ↓reduceIte, hNotEven1, Nat.cast_add, Nat.cast_one, neg_sub, hEven2,
          Nat.cast_ofNat]
        ring_nf
      · have hOdd : Odd K := (Nat.even_or_odd K).resolve_left hEven
        have hEven' : Even (K + 1) := by
          obtain ⟨j, rfl⟩ := hOdd
          use j + 1
          omega
        have hNotEven2 : ¬Even (K + 2) := by
          intro h
          obtain ⟨i, hi⟩ := hOdd
          obtain ⟨j, hj⟩ := h
          omega
        simp only [hEven, ↓reduceIte, neg_sub, sub_add_sub_cancel', hEven', Nat.cast_add,
          Nat.cast_one, hNotEven2, Nat.cast_ofNat]
        ring_nf
  rw [hformula]
  by_cases hEven : Even K
  · rw [ite_eq_left hEven]
    obtain ⟨j, hj⟩ := hEven
    have hj' : K = 2 * j := by omega
    have hKcast : (K : ℝ) = 2 * j := by exact_mod_cast hj'
    nlinarith
  · have hKpos : 1 ≤ K := by
      by_contra h
      have : K = 0 := by omega
      subst K
      simp only [Even.zero, not_true_eq_false] at hEven
    have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast hKpos
    rw [ite_eq_right hEven]
    nlinarith

/-- For `x ≥ 4` and `K * log 2 ≤ log x`, the alternating affine sum with first term
`log 2 * (log x - log 2)` is at most that first term. -/
theorem alternatingLogCorrection_le_log_two_mul_log_half {x : ℝ} (K : ℕ) (hx : 4 ≤ x)
    (hK : (K : ℝ) * Real.log 2 ≤ Real.log x) :
    (∑ k ∈ Finset.range K,
        (if Even k then Real.log 2 * (Real.log x - (k + 1) * Real.log 2)
        else -(Real.log 2 * (Real.log x - (k + 1) * Real.log 2)))) ≤
      Real.log 2 * (Real.log x - Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
    norm_num only
  have hxpos : 0 < x := by linarith
  have hlogx : Real.log 4 ≤ Real.log x := by
    exact Real.strictMonoOn_log.monotoneOn (by norm_num only [Set.mem_Ioi]) hxpos hx
  have hA : 2 * (Real.log 2) ^ 2 ≤ Real.log 2 * Real.log x := by
    have hmul := mul_le_mul_of_nonneg_left hlogx hlog2.le
    rw [hlog4] at hmul
    nlinarith
  have hKb : (K : ℝ) * (Real.log 2) ^ 2 ≤ Real.log 2 * Real.log x := by
    have hmul := mul_le_mul_of_nonneg_right hK hlog2.le
    calc
      (K : ℝ) * (Real.log 2) ^ 2 = ((K : ℝ) * Real.log 2) * Real.log 2 := by ring
      _ ≤ Real.log x * Real.log 2 := hmul
      _ = Real.log 2 * Real.log x := by ring
  convert
      alternating_linear_sum_le_first hA
        (sq_nonneg (Real.log 2)) K hKb using
      1 <;>
    simp only [mul_sub] <;>
    ring_nf

/-!
The same alternating estimate in the native `Icc 1 K` indexing used by the correction ledger.
The shift `k = j + 1` is exposed explicitly so later branch comparisons can consume the exact
correction without introducing a second cutoff convention.
-/

theorem alternatingLogCorrection_Icc_le_log_two_mul_log_half {x : ℝ} (K : ℕ) (hx : 4 ≤ x)
    (hK : (K : ℝ) * Real.log 2 ≤ Real.log x) :
    (∑ k ∈ Finset.Icc 1 K,
        if Odd k then Real.log 2 * (Real.log x - k * Real.log 2)
        else -(Real.log 2 * (Real.log x - k * Real.log 2))) ≤
      Real.log 2 * (Real.log x - Real.log 2) := by
  have hshift :
    (∑ k ∈ Finset.Icc 1 K,
        if Odd k then Real.log 2 * (Real.log x - k * Real.log 2)
        else -(Real.log 2 * (Real.log x - k * Real.log 2))) =
      ∑ j ∈ Finset.range K,
        if Even j then Real.log 2 * (Real.log x - (j + 1) * Real.log 2)
        else -(Real.log 2 * (Real.log x - (j + 1) * Real.log 2)) := by
    induction K with
    | zero =>
      simp only [Order.lt_one_iff, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, Finset.range_zero]
    | succ K ih =>
      have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num only)
      have hKle : (K : ℝ) * Real.log 2 ≤ (K + 1 : ℕ) * Real.log 2 := by
        gcongr
        omega
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih (hKle.trans hK)]
      congr 1
      by_cases he : Even K
      · have hodd : Odd (K + 1) := by
          apply Nat.not_even_iff_odd.mp
          intro h
          exact (Nat.even_add_one.mp h) he
        simp only [hodd, ↓reduceIte, Nat.cast_add, Nat.cast_one, he]
      · have heven : Even (K + 1) := Nat.even_add_one.mpr he
        have hnodd : ¬Odd (K + 1) := Nat.not_odd_iff_even.mpr heven
        simp only [hnodd, ↓reduceIte, Nat.cast_add, Nat.cast_one, he]
  rw [hshift]
  exact
    alternatingLogCorrection_le_log_two_mul_log_half K
      hx hK

/-!
For a quadratic primitive character with value `-1` at `2` and `x ≥ 4`, the logarithmic
correction is at most `(log x)²/2 + log 2 * (log x - log 2)`. Split twice the odd-indexed sum
into the full affine sum and its alternating sum, and bound these two sums separately.
-/

theorem twoAdicLogCorrection_le_half_log_sq_add_log_two_mul_log_half_of_apply_two_eq_neg_one {q : ℕ}
    (x : ℝ) (χ : DirichletCharacter ℂ q) (hχ : χ.primitiveCharacter.IsQuadratic) (hx : 4 ≤ x)
    (h2 : χ.primitiveCharacter 2 = -1) :
    twoAdicLogCorrection x χ ≤
      (Real.log x) ^ 2 / 2 + Real.log 2 * (Real.log x - Real.log 2) := by
  rw [twoAdicLogCorrection_eq_odd_sum_of_apply_two_eq_neg_one x χ hχ (by linarith : x ≠ 0) h2]
  let K := ⌊Real.log x / Real.log 2⌋₊
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have hquot_nonneg : 0 ≤ Real.log x / Real.log 2 :=
    div_nonneg (Real.log_nonneg (by linarith)) hlog2.le
  have hfloor : (K : ℝ) ≤ Real.log x / Real.log 2 := by
    dsimp [K]
    exact Nat.floor_le hquot_nonneg
  have hK : (K : ℝ) * Real.log 2 ≤ Real.log x := (le_div_iff₀ hlog2).mp hfloor
  have hbase :=
    sum_log_weight_le_half_sq (Real.log 2) (Real.log x)
      K
  have halt :=
    alternatingLogCorrection_Icc_le_log_two_mul_log_half
      K hx hK
  have hdecomp :
    (∑ k ∈ Finset.Icc 1 K, if Odd k then 2 * (Real.log 2 * (Real.log x - k * Real.log 2)) else 0) =
      (∑ k ∈ Finset.Icc 1 K, Real.log 2 * (Real.log x - k * Real.log 2)) +
        ∑ k ∈ Finset.Icc 1 K,
          if Odd k then Real.log 2 * (Real.log x - k * Real.log 2)
          else -(Real.log 2 * (Real.log x - k * Real.log 2)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hodd : Odd k
    · simp only [hodd, ↓reduceIte]
      ring
    · simp only [hodd, ↓reduceIte, add_neg_cancel]
  rw [hdecomp]
  nlinarith

/-!
Input/assumptions: `x ≠ 0` and two characters with quadratic primitive parts whose values at
`2` are `-1` and `0`.
Conclusion: their logarithmic correction difference equals the displayed alternating finite sum.
Content: this is the exact bridge from the branch formulas to the conductor-saving estimate.
Proof: rewrite both corrections by the quadratic closed form and compare the summands by parity.
Role: identifies the difference to which `alternatingLogCorrection_Icc_le_log_two_mul_log_half`
applies when `x ≥ 4`; this equality itself requires only `x ≠ 0`.
-/

theorem twoAdicLogCorrection_neg_one_sub_zero_eq_alternating {qz qn : ℕ} (x : ℝ)
    (χz : DirichletCharacter ℂ qz) (χn : DirichletCharacter ℂ qn)
    (hχz : χz.primitiveCharacter.IsQuadratic) (hχn : χn.primitiveCharacter.IsQuadratic) (hx : x ≠ 0)
    (h20 : χz.primitiveCharacter 2 = 0) (h2m : χn.primitiveCharacter 2 = -1) :
    twoAdicLogCorrection x χn -
        twoAdicLogCorrection x χz =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
        if Odd k then Real.log 2 * (Real.log x - k * Real.log 2)
        else -(Real.log 2 * (Real.log x - k * Real.log 2)) := by
  rw [twoAdicLogCorrection_eq_sum_of_isQuadratic x χn
      hχn hx,
    twoAdicLogCorrection_eq_sum_of_isQuadratic x χz hχz
      hx]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hodd : Odd k
  · simp only [hodd, ↓reduceIte, h2m, Complex.neg_re, Complex.one_re, mul_neg, mul_one,
      sub_neg_eq_add, h20, Complex.zero_re, mul_zero, sub_zero, add_sub_cancel_right]
  · simp only [hodd, ↓reduceIte, h2m, even_two, Even.neg_pow, one_pow, Complex.one_re, mul_one,
      sub_self, h20, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Complex.zero_re,
      mul_zero, sub_zero, zero_sub]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
