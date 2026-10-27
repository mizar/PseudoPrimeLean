/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedDifferences

/-! # Bounded weights separate prime exclusion from higher powers -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For any cutoff, the nonprime Mangoldt sum equals psi minus theta.
Split the finite positive support into prime and nonprime indices. -/
theorem nonprime_mangoldt_sum_eq_psi_sub_theta (y : ℝ) :
    (∑ n ∈ (Finset.Ioc 0 ⌊y⌋₊).filter (fun n ↦ ¬n.Prime), ArithmeticFunction.vonMangoldt n) =
      Chebyshev.psi y - Chebyshev.theta y := by
  classical
  have hp :
    (∑ n ∈ (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime, ArithmeticFunction.vonMangoldt n) =
      Chebyshev.theta y := by
    rw [Chebyshev.theta]
    apply Finset.sum_congr rfl
    intro n hn
    exact ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2
  have hs :=
    Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 ⌊y⌋₊) Nat.Prime
      ArithmeticFunction.vonMangoldt
  rw [hp, ← psi_eq_positive_sum] at hs
  linarith only [hs]

/-- A nonnegative weight bounded by T Lambda and real values at least -1
have defect at most 2T times the excluded prime logarithm sum plus psi-theta,
if all nonexcluded primes through the cutoff have value one.
Separate primes before estimating higher powers; exclusion is linear in log(rad(m)). -/
theorem bounded_weight_prime_exclusion {m : ℕ} (hm : m ≠ 0) {y T : ℝ} (hT : 0 ≤ T) (w v : ℕ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc 0 ⌊y⌋₊, 0 ≤ w n ∧ w n ≤ T * ArithmeticFunction.vonMangoldt n)
    (hv : ∀ n ∈ Finset.Ioc 0 ⌊y⌋₊, -1 ≤ v n)
    (hno : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ y → ¬p ∣ m → v p = 1) :
    (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, w n * (1 - v n)) ≤
      2 * T * ((∑ p ∈ m.primeFactors, Real.log p) + Chebyshev.psi y - Chebyshev.theta y) := by
  classical
  let S := Finset.Ioc 0 ⌊y⌋₊
  have hpoint (n : ℕ) (hn : n ∈ S) :
    w n * (1 - v n) ≤
      2 * T *
        ((if n.Prime ∧ n ∣ m then Real.log n else 0) +
          (if ¬n.Prime then ArithmeticFunction.vonMangoldt n else 0)) := by
    have hmul := mul_le_mul_of_nonneg_left (show 1 - v n ≤ 2 by linarith only [hv n hn]) (hw n hn).1
    have hb := (hw n hn).2
    by_cases hp : n.Prime
    · rw [ite_eq_right (not_not.mpr hp), add_zero]
      by_cases hd : n ∣ m
      · rw [ite_eq_left ⟨hp, hd⟩]
        rw [ArithmeticFunction.vonMangoldt_apply_prime hp] at hb
        nlinarith only [hmul, hb]
      · have hv1 :=
          hno n hp
            ((Nat.le_floor_iff' (Nat.ne_of_gt (Finset.mem_Ioc.mp hn).1)).mp
              (Finset.mem_Ioc.mp hn).2)
            hd
        rw [hv1, sub_self, mul_zero, ite_eq_right (fun h ↦ hd h.2), mul_zero]
    · rw [ite_eq_right (fun h ↦ hp h.1), ite_eq_left hp, zero_add]
      nlinarith only [hmul, hb]
  have hsum := Finset.sum_le_sum hpoint
  have hprime :
    (∑ n ∈ S, if n.Prime ∧ n ∣ m then Real.log n else 0) ≤ ∑ p ∈ m.primeFactors, Real.log p := by
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨_, hp, hd⟩ := Finset.mem_filter.mp hp
      exact Nat.mem_primeFactors.mpr ⟨hp, hd, hm⟩
    · intro p _ _
      exact Real.log_natCast_nonneg p
  have hcomp :
    (∑ n ∈ S, if ¬n.Prime then ArithmeticFunction.vonMangoldt n else 0) =
      Chebyshev.psi y - Chebyshev.theta y := by
    rw [← Finset.sum_filter]
    exact nonprime_mangoldt_sum_eq_psi_sub_theta y
  rw [← Finset.mul_sum, Finset.sum_add_distrib, hcomp] at hsum
  have hscale := mul_le_mul_of_nonneg_left hprime (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) hT)
  nlinarith only [hsum, hscale]

/-- Pad the lower character logarithmic sum with zeros to a larger cutoff.
The common support permits an exact difference without changing any summand. -/
theorem characterLogWeightedSum_eq_extended {q : ℕ} (χ : DirichletCharacter ℂ q) {x y : ℝ}
    (hxy : x ≤ y) :
    characterLogWeightedSum x χ =
      ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, if n ≤ ⌊x⌋₊ then characterLogWeightedTerm x χ n else 0 := by
  classical
  have hs :=
    Finset.sum_subset (Finset.Ioc_subset_Ioc (le_refl 0) (Nat.floor_mono hxy)) (f := fun n ↦
      if n ≤ ⌊x⌋₊ then characterLogWeightedTerm x χ n else 0)
      (fun n hnY hn ↦ ite_eq_right (fun h ↦ hn (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hnY).1, h⟩)))
  have he :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, if n ≤ ⌊x⌋₊ then characterLogWeightedTerm x χ n else 0) =
      characterLogWeightedSum x χ := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [ite_eq_left (Finset.mem_Ioc.mp hn).2]
  exact he.symm.trans hs

/-- If all nonexcluded primes have character value one, the logarithmic
finite-difference defect is at most 2 log(y/x) times the excluded prime logarithm
sum plus psi(y)-theta(y). The bounded difference weight removes log(y) from the
prime exclusion cost when the cutoff ratio is fixed. -/
theorem log_difference_prime_exclusion {q m : ℕ} (χ : DirichletCharacter ℂ q) (hm : m ≠ 0) {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hno : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ y → ¬p ∣ m → χ p = 1) :
    logWeightedMangoldtSum y - logWeightedMangoldtSum x -
        (characterLogWeightedSum y χ - characterLogWeightedSum x χ).re ≤
      2 * Real.log (y / x) *
        ((∑ p ∈ m.primeFactors, Real.log p) + Chebyshev.psi y - Chebyshev.theta y) := by
  classical
  let w := fun n ↦ logWeightedMangoldtTerm y n - if n ≤ ⌊x⌋₊ then logWeightedMangoldtTerm x n else 0
  have hT : 0 ≤ Real.log (y / x) := Real.log_nonneg ((le_div_iff₀ hx).mpr (by linarith only [hxy]))
  have hw (n : ℕ) (hn : n ∈ Finset.Ioc 0 ⌊y⌋₊) :
    0 ≤ w n ∧ w n ≤ Real.log (y / x) * ArithmeticFunction.vonMangoldt n := by
    have hb :=
      logWeightedMangoldtTerm_difference hx hxy (Finset.mem_Ioc.mp hn).1
        ((Nat.le_floor_iff (hx.trans_le hxy).le).mp (Finset.mem_Ioc.mp hn).2)
    have hz : 0 ≤ if n ≤ ⌊x⌋₊ then ArithmeticFunction.vonMangoldt n * Real.log (y / x) else 0 := by
      split
      · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hT
      · exact le_refl 0
    exact ⟨hz.trans hb.1, hb.2.trans_eq (mul_comm _ _)⟩
  have hv (n : ℕ) (_ : n ∈ Finset.Ioc 0 ⌊y⌋₊) : -1 ≤ (χ n).re :=
    (abs_le.mp ((Complex.abs_re_le_norm (χ n)).trans (χ.norm_le_one n))).1
  have hb :=
    bounded_weight_prime_exclusion hm hT w (fun n ↦ (χ n).re) hw hv
      (fun p hp hb hd ↦ by rw [hno p hp hb hd, Complex.one_re])
  have he :
    logWeightedMangoldtSum y - logWeightedMangoldtSum x -
        (characterLogWeightedSum y χ - characterLogWeightedSum x χ).re =
      ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, w n * (1 - (χ n).re) := by
    rw [logWeightedMangoldtSum_eq_extended hxy, characterLogWeightedSum_eq_extended χ hxy,
      logWeightedMangoldtSum, characterLogWeightedSum, Complex.sub_re, Complex.re_sum,
      Complex.re_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    dsimp only [w, characterLogWeightedTerm]
    by_cases hn : n ≤ ⌊x⌋₊
    · simp only [ite_eq_left hn, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero]
      ring
    · simp only [ite_eq_right hn, Complex.zero_re, sub_zero, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul]
      ring
  exact he.trans_le hb

/-- A strict finite-difference gap produces a prime outside the excluded
prime support with character value different from one. Apply the no-witness
comparison contrapositively. This is the witness interface for conductor bounds. -/
theorem exists_prime_ne_one_of_log_difference_gap {q m : ℕ} (χ : DirichletCharacter ℂ q)
    (hm : m ≠ 0) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hgap :
      2 * Real.log (y / x) *
          ((∑ p ∈ m.primeFactors, Real.log p) + Chebyshev.psi y - Chebyshev.theta y) <
        logWeightedMangoldtSum y - logWeightedMangoldtSum x -
          (characterLogWeightedSum y χ - characterLogWeightedSum x χ).re) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ y ∧ ¬p ∣ m ∧ χ p ≠ 1 := by
  classical
  by_contra hnone
  have hno (p : ℕ) (hp : p.Prime) (hb : (p : ℝ) ≤ y) (hd : ¬p ∣ m) : χ p = 1 := by
    by_contra hne
    exact hnone ⟨p, hp, hb, hd, hne⟩
  exact (not_lt_of_ge (log_difference_prime_exclusion χ hm hx hxy hno)) hgap

/-- For nonzero natural factors, the prime logarithm sum of their product
is at most the sum of the separate prime logarithm sums. The prime supports
form a union; discard its nonnegative intersection cost. This preserves radicals. -/
theorem prime_factor_log_sum_mul_le {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (∑ p ∈ (a * b).primeFactors, Real.log p) ≤
      (∑ p ∈ a.primeFactors, Real.log p) + ∑ p ∈ b.primeFactors, Real.log p := by
  rw [Nat.primeFactors_mul ha hb]
  have he :=
    Finset.sum_union_inter (s₁ := a.primeFactors) (s₂ := b.primeFactors) (f := fun p : ℕ ↦
      Real.log p)
  have hz : 0 ≤ ∑ p ∈ a.primeFactors ∩ b.primeFactors, Real.log p :=
    Finset.sum_nonneg (fun p _ ↦ Real.log_natCast_nonneg p)
  linarith only [he, hz]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
