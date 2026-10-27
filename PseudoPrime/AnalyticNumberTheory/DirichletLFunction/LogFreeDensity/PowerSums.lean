/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Polynomial.Vieta

/-! # Finite power sums for distinct complex frequencies -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/--
Inputs: finite index sets `t ⊆ s`, complex values on `s`, and a lower bound one for their norms.

Claim: the product over `t`, divided by the product over `s`, has norm at most one.

Proof: compare the norm products by adjoining the omitted factors, each of which is at least one.

Role: bounds each normalized elementary-symmetric term in the interpolation polynomial used by
Turán's power-sum estimate.
-/
theorem normalized_product_subset_norm_le_one {ι : Type} (s t : Finset ι) (z : ι → ℂ) (hts : t ⊆ s)
    (hz : ∀ i ∈ s, (1 : ℝ) ≤ ‖z i‖) : ‖(∏ i ∈ t, -z i) / (∏ i ∈ s, z i)‖ ≤ 1 := by
  classical
  have hnum : ∏ i ∈ t, ‖z i‖ ≤ ∏ i ∈ s, ‖z i‖ :=
    Finset.prod_le_prod_of_subset_of_one_le₀ hts (fun i hi => norm_nonneg _)
      (fun i hi hit => hz i hi)
  have hden : (1 : ℝ) ≤ ∏ i ∈ s, ‖z i‖ := Finset.one_le_prod₀ (fun i hi => hz i hi)
  rw [norm_div, Complex.norm_prod, Complex.norm_prod]
  simp only [norm_neg]
  exact (div_le_one₀ (lt_of_lt_of_le zero_lt_one hden)).2 hnum

/--
Inputs: a finite set of complex values with norms at least one and a coefficient index not
exceeding the set's cardinality.

Claim: the coefficient of the product `∏ (X - zᵢ)`, normalized by `∏ zᵢ`, has norm at most the
corresponding binomial coefficient.

Proof: Vieta's coefficient formula writes it as a sum over subsets; each normalized term has norm
at most one, and there are `choose |s| k` terms.

Role: supplies the coefficient bound for the finite interpolation proof of Turán's first main
theorem.
-/
theorem normalized_prod_X_sub_C_coeff_norm_le_choose {ι : Type} (s : Finset ι) (z : ι → ℂ)
    (hz : ∀ i ∈ s, (1 : ℝ) ≤ ‖z i‖) {k : ℕ} (hk : k ≤ s.card) :
    ‖(∏ i ∈ s, (Polynomial.X - Polynomial.C (z i))).coeff k / (∏ i ∈ s, z i)‖ ≤
      (Nat.choose s.card k : ℝ) := by
  classical
  have hcoeff :
    (∏ i ∈ s, (Polynomial.X - Polynomial.C (z i))).coeff k =
      ∑ t ∈ s.powersetCard (s.card - k), ∏ i ∈ t, -z i := by
    convert Finset.prod_X_add_C_coeff s (fun i => -z i) hk using 1
    simp only [map_neg, sub_eq_add_neg]
  rw [hcoeff, Finset.sum_div]
  calc
    ‖∑ t ∈ s.powersetCard (s.card - k), (∏ i ∈ t, -z i) / (∏ i ∈ s, z i)‖ ≤
        ∑ t ∈ s.powersetCard (s.card - k), ‖(∏ i ∈ t, -z i) / (∏ i ∈ s, z i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _t ∈ s.powersetCard (s.card - k), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      exact normalized_product_subset_norm_le_one s t z (Finset.mem_powersetCard.mp ht).1 hz
    _ = (Nat.choose s.card k : ℝ) := by
      simp only [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, mul_one]
      rw [Nat.choose_symm hk]

/--
Inputs: a finite family of complex values with norms at least one, an additional complex factor
with norm at least one, and a coefficient index within the family size.

Claim: dividing the normalized polynomial coefficient by the additional factor preserves the
same binomial norm bound.

Proof: the norm of the additional factor enlarges the denominator by a factor at least one.

Role: allows the interpolation coefficient estimate to include the extra node in a divided
difference.
-/
theorem normalized_prod_X_sub_C_coeff_div_extra_norm_le_choose {ι : Type} (s : Finset ι) (z : ι → ℂ)
    (c : ℂ) (hz : ∀ i ∈ s, (1 : ℝ) ≤ ‖z i‖) (hc : (1 : ℝ) ≤ ‖c‖) {k : ℕ} (hk : k ≤ s.card) :
    ‖(∏ i ∈ s, (Polynomial.X - Polynomial.C (z i))).coeff k / ((∏ i ∈ s, z i) * c)‖ ≤
      (Nat.choose s.card k : ℝ) := by
  have hden : (1 : ℝ) ≤ ‖∏ i ∈ s, z i‖ := by
    rw [Complex.norm_prod]
    exact Finset.one_le_prod₀ (fun i hi => hz i hi)
  have hcoeff := normalized_prod_X_sub_C_coeff_norm_le_choose s z hz hk
  rw [norm_div] at hcoeff
  rw [norm_div, Complex.norm_mul]
  apply le_trans ?_ hcoeff
  apply div_le_div_of_nonneg_left (norm_nonneg _)
  · exact lt_of_lt_of_le zero_lt_one hden
  · exact le_mul_of_one_le_right (norm_nonneg _) hc

/--
Inputs: a finite multiset of complex nodes, each with norm at least one.

Claim: there is a polynomial whose value at every node is its multiplicative inverse, including
when nodes repeat.

Proof: divide the constant-term-subtracted root polynomial by `X`, then normalize by its
nonzero constant coefficient.

Role: gives an interpolation identity for the initial block of pure power sums.
-/
theorem exists_polynomial_inverse_on_prod_X_sub_C_roots {ι : Type} (s : Finset ι) (z : ι → ℂ)
    (hz : ∀ i ∈ s, (1 : ℝ) ≤ ‖z i‖) :
    ∃ p : Polynomial ℂ,
      (∀ i ∈ s, z i * p.eval (z i) = 1) ∧
        ∀ k < s.card, ‖p.coeff k‖ ≤ (Nat.choose s.card (k + 1) : ℝ) := by
  classical
  let q : Polynomial ℂ := ∏ i ∈ s, (Polynomial.X - Polynomial.C (z i))
  let c : ℂ := ∏ i ∈ s, -z i
  have hq0 : q.coeff 0 = c := by
    simpa only [q, c, Nat.sub_zero, sub_eq_add_neg, map_neg, Finset.powersetCard_self,
      Finset.sum_singleton] using
      Finset.prod_X_add_C_coeff s (fun i => -z i) (k := 0) (Nat.zero_le _)
  have hc : c ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact neg_ne_zero.mpr (norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one (hz i hi)))
  have hdiv : Polynomial.X ∣ q - Polynomial.C c := by
    apply Polynomial.X_dvd_iff.mpr
    rw [Polynomial.coeff_sub, hq0]
    simp only [Polynomial.coeff_C_zero, sub_self]
  obtain ⟨r, hr⟩ := hdiv
  let p : Polynomial ℂ := -r * Polynomial.C c⁻¹
  have hid : Polynomial.X * p = Polynomial.C 1 - q * Polynomial.C c⁻¹ := by
    calc
      Polynomial.X * p = -(Polynomial.X * r) * Polynomial.C c⁻¹ := by
        dsimp only [p]
        ring
      _ = -(q - Polynomial.C c) * Polynomial.C c⁻¹ := by rw [hr]
      _ = Polynomial.C 1 - q * Polynomial.C c⁻¹ := by
        rw [neg_sub, sub_mul, ← Polynomial.C_mul, mul_inv_cancel₀ hc]
  refine ⟨p, ?_, ?_⟩
  · intro i hi
    have hroot : q.eval (z i) = 0 := by
      dsimp only [q]
      rw [Polynomial.eval_prod]
      exact
        Finset.prod_eq_zero hi
          (by simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self])
    have heval := congrArg (fun f : Polynomial ℂ => f.eval (z i)) hid
    rw [Polynomial.eval_mul, Polynomial.eval_X] at heval
    simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul, hroot, zero_mul,
      sub_zero] at heval
    exact heval
  · intro k hk
    have hrcoeff : r.coeff k = q.coeff (k + 1) := by
      have h := congrArg (fun f : Polynomial ℂ => f.coeff (k + 1)) hr
      simpa only [Polynomial.coeff_sub, Polynomial.coeff_C_succ, sub_zero,
        Polynomial.coeff_X_mul] using h.symm
    have hpcoeff : p.coeff k = -(q.coeff (k + 1)) * c⁻¹ := by
      dsimp only [p]
      rw [Polynomial.coeff_mul_C, Polynomial.coeff_neg, hrcoeff]
    have hcNorm : ‖c‖ = ‖∏ i ∈ s, z i‖ := by
      dsimp only [c]
      rw [Complex.norm_prod, Complex.norm_prod]
      simp only [norm_neg]
    have hpNorm : ‖p.coeff k‖ = ‖q.coeff (k + 1) / (∏ i ∈ s, z i)‖ := by
      calc
        ‖p.coeff k‖ = ‖q.coeff (k + 1)‖ * ‖c‖⁻¹ := by rw [hpcoeff, norm_mul, norm_neg, norm_inv]
        _ = ‖q.coeff (k + 1)‖ / ‖∏ i ∈ s, z i‖ := by rw [hcNorm, div_eq_mul_inv]
        _ = ‖q.coeff (k + 1) / (∏ i ∈ s, z i)‖ := (norm_div _ _).symm
    have hbound := normalized_prod_X_sub_C_coeff_norm_le_choose s z hz (Nat.succ_le_of_lt hk)
    change ‖q.coeff (k + 1) / (∏ i ∈ s, z i)‖ ≤ _ at hbound
    rw [hpNorm]
    exact hbound

/--
Inputs: a finite family of pairwise distinct complex numbers and coefficients that are not all
zero.

Claim: at least one of the first `n` power sums is nonzero.

Proof: the transpose Vandermonde matrix maps the coefficient vector to those power sums. Its
determinant is nonzero for distinct frequencies, so the matrix is invertible.

Role: gives the qualitative finite-power-sum separation needed before proving quantitative
Turán-type lower bounds.
-/
theorem exists_nonzero_power_sum_of_distinct_frequencies {n : ℕ} (z : Fin n → ℂ)
    (hz : Function.Injective z) (a : Fin n → ℂ) (ha : ∃ i, a i ≠ 0) :
    ∃ k : Fin n, (∑ i : Fin n, a i * z i ^ k.val) ≠ 0 := by
  have hdet : (Matrix.vandermonde z).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hz
  have hunit : IsUnit (Matrix.vandermonde z) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hinj := Matrix.vecMul_injective_of_isUnit hunit
  by_contra hsum
  push Not at hsum
  have hzero : Matrix.vecMul a (Matrix.vandermonde z) = 0 := by
    ext k
    change (∑ i : Fin n, a i * z i ^ k.val) = 0
    exact hsum k
  have hzero' :
    Matrix.vecMul a (Matrix.vandermonde z) =
      Matrix.vecMul (0 : Fin n → ℂ) (Matrix.vandermonde z) := by
    rw [hzero, Matrix.zero_vecMul]
  have ha0 : a = 0 := hinj hzero'
  obtain ⟨i, hai⟩ := ha
  exact hai (congrFun ha0 i)

/--
Inputs: pairwise distinct nonzero complex frequencies, coefficients that are not all zero, and
the first exponent of a block.

Claim: among any `n` consecutive power sums beginning at that exponent, at least one is nonzero.

Proof: absorb the initial power into each coefficient and apply the Vandermonde nonvanishing
result.

Role: provides the consecutive-block form used when a zero detector selects a short range of
exponents.
-/
theorem exists_nonzero_power_sum_in_consecutive_block_of_distinct_nonzero_frequencies {n : ℕ}
    (z : Fin n → ℂ) (hz : Function.Injective z) (hz0 : ∀ i, z i ≠ 0) (a : Fin n → ℂ)
    (ha : ∃ i, a i ≠ 0) (m : ℕ) : ∃ j : Fin n, (∑ i : Fin n, a i * z i ^ (m + j.val)) ≠ 0 := by
  have hweights : ∃ i, a i * z i ^ m ≠ 0 := by
    obtain ⟨i, hai⟩ := ha
    exact ⟨i, mul_ne_zero hai (pow_ne_zero m (hz0 i))⟩
  obtain ⟨j, hj⟩ :=
    exists_nonzero_power_sum_of_distinct_frequencies z hz (fun i => a i * z i ^ m) hweights
  refine ⟨j, ?_⟩
  calc
    (∑ i : Fin n, a i * z i ^ (m + j.val)) = ∑ i : Fin n, (a i * z i ^ m) * z i ^ j.val := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_add]
      ring
    _ ≠ 0 := hj

/--
Inputs: a finite weighted complex family, a polynomial of degree below `n`, and an exponent `m`.

Claim: summing polynomial evaluations against the weights equals a finite linear combination of
the power sums beginning at `m`.

Proof: expand the evaluation, exchange the two finite sums, and collect powers.

Role: transfers interpolation identities and root-polynomial identities to weighted power sums.
-/
theorem weighted_polynomial_eval_eq_power_sum {ι : Type} (s : Finset ι) (z a : ι → ℂ)
    (p : Polynomial ℂ) {n : ℕ} (hp : p.natDegree < n) (m : ℕ) :
    (∑ i ∈ s, a i * z i ^ m * p.eval (z i)) =
      ∑ k ∈ Finset.range n, p.coeff k * (∑ i ∈ s, a i * z i ^ (m + k)) := by
  simp only [Polynomial.eval_eq_sum_range' hp, Finset.mul_sum, pow_add]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  ring

/--
Inputs: a finite complex family, its weights, and an initial exponent.

Claim: its root polynomial annihilates the corresponding consecutive weighted power sums.
Repeated frequencies and arbitrary weights are allowed.

Proof: apply the finite evaluation identity; each evaluation contains a zero factor.

Role: supplies the exact recurrence underlying quantitative power-sum interpolation.
-/
theorem power_sum_root_polynomial_recurrence {ι : Type} (s : Finset ι) (z a : ι → ℂ) (m : ℕ) :
    ∑ k ∈ Finset.range (s.card + 1),
        (∏ i ∈ s, (Polynomial.X - Polynomial.C (z i))).coeff k * (∑ i ∈ s, a i * z i ^ (m + k)) =
      0 := by
  classical
  rw [←
    weighted_polynomial_eval_eq_power_sum s z a _
      (by
        rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card]; exact Nat.lt_succ_self _)
      m]
  apply Finset.sum_eq_zero
  intro i hi
  have hroot : (∏ j ∈ s, (Polynomial.X - Polynomial.C (z j))).eval (z i) = 0 := by
    rw [Polynomial.eval_prod]
    exact
      Finset.prod_eq_zero hi
        (by simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self])
  rw [hroot, mul_zero]

/--
Inputs: a finite weighted complex family whose frequencies have norms at least one, and an
initial exponent `m`.

Claim: the norm of its power sum at `m` is bounded by a binomially weighted sum of the next
`s.card` power-sum norms. Frequencies need not be distinct.

Proof: isolate the constant term in the root-polynomial recurrence, divide by its nonzero
norm, and apply the normalized coefficient bounds and the triangle inequality.

Role: connects the normalized polynomial estimates to a quantitative consecutive-block
inequality; iterating it alone does not give the required uniform Turán estimate.
-/
theorem power_sum_norm_le_binomial_sum {ι : Type} (s : Finset ι) (z a : ι → ℂ) (m : ℕ)
    (hz : ∀ i ∈ s, (1 : ℝ) ≤ ‖z i‖) :
    ‖∑ i ∈ s, a i * z i ^ m‖ ≤
      ∑ k ∈ Finset.range s.card,
        (Nat.choose s.card (k + 1) : ℝ) * ‖∑ i ∈ s, a i * z i ^ (m + (k + 1))‖ := by
  classical
  let q : Polynomial ℂ := ∏ i ∈ s, (Polynomial.X - Polynomial.C (z i))
  have hqnorm : ‖q.coeff 0‖ = ‖∏ i ∈ s, z i‖ := by
    simp only [q, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, zero_sub, Complex.norm_prod, norm_neg]
  have hqpos : 0 < ‖q.coeff 0‖ := by
    rw [hqnorm, Complex.norm_prod]
    exact lt_of_lt_of_le zero_lt_one (Finset.one_le_prod₀ hz)
  have hrec := power_sum_root_polynomial_recurrence s z a m
  change (∑ k ∈ Finset.range (s.card + 1), q.coeff k * (∑ i ∈ s, a i * z i ^ (m + k))) = 0 at hrec
  rw [Finset.sum_range_succ'] at hrec
  simp only [Nat.add_zero] at hrec
  have hnorm :
    ‖∑ i ∈ s, a i * z i ^ m‖ =
      ‖∑ k ∈ Finset.range s.card, q.coeff (k + 1) * (∑ i ∈ s, a i * z i ^ (m + (k + 1)))‖ /
        ‖q.coeff 0‖ := by
    have heq := eq_neg_of_add_eq_zero_right hrec
    have hn := congrArg norm heq
    rw [norm_mul, norm_neg] at hn
    exact
      (eq_div_iff (ne_of_gt hqpos)).mpr
        (by
          rw [mul_comm]; exact hn)
  rw [hnorm]
  apply le_trans (div_le_div_of_nonneg_right (norm_sum_le _ _) (le_of_lt hqpos))
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro k hk
  rw [norm_mul, mul_div_right_comm]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hb :=
    normalized_prod_X_sub_C_coeff_norm_le_choose s z hz (Nat.succ_le_of_lt (Finset.mem_range.mp hk))
  rw [norm_div] at hb
  rw [hqnorm]
  exact hb

private theorem sum_shifted_choose_real (n : ℕ) :
    (∑ k ∈ Finset.range n, (Nat.choose n (k + 1) : ℝ)) = 2 ^ n - 1 := by
  have h := Nat.sum_range_choose n
  rw [Finset.sum_range_succ', Nat.choose_zero_right] at h
  have h' : (∑ k ∈ Finset.range n, (Nat.choose n (k + 1) : ℝ)) + 1 = 2 ^ n := by exact_mod_cast h
  linarith only [h']

/--
Inputs: a finite weighted complex family with frequencies of norm at least one, and a common
upper bound `B` for the next `s.card` power-sum norms after exponent `m`.

Claim: the power-sum norm at `m` is at most `(2 ^ s.card - 1) * B`.

Proof: use the binomial recurrence and sum its nonnegative coefficient bounds.

Role: supplies the maximum-norm form of the consecutive-block estimate, including repeated nodes.
-/
theorem power_sum_norm_le_block_bound {ι : Type} (s : Finset ι) (z a : ι → ℂ) (m : ℕ)
    (hz : ∀ i ∈ s, (1 : ℝ) ≤ ‖z i‖) (B : ℝ)
    (hB : ∀ k < s.card, ‖∑ i ∈ s, a i * z i ^ (m + (k + 1))‖ ≤ B) :
    ‖∑ i ∈ s, a i * z i ^ m‖ ≤ (2 ^ s.card - 1) * B := by
  rw [← sum_shifted_choose_real]
  apply le_trans (power_sum_norm_le_binomial_sum s z a m hz)
  rw [Finset.sum_mul]
  exact
    Finset.sum_le_sum
      (fun k hk ↦ mul_le_mul_of_nonneg_left (hB k (Finset.mem_range.mp hk)) (Nat.cast_nonneg _))

/--
Inputs: a nonempty finite weighted complex family, frequencies of norm at least one, and an
initial exponent `m`.

Claim: one of the next `s.card` power sums, multiplied in norm by `2 ^ s.card - 1`, dominates
the power-sum norm at `m`.

Proof: choose a maximum norm in the next block and apply the common-bound estimate.

Role: yields a quantitative block witness without a distinctness hypothesis; at `m = 0` its
left side is the norm of the total weight.
-/
theorem exists_power_sum_norm_ge_of_previous {ι : Type} (s : Finset ι) (hs : s.Nonempty)
    (z a : ι → ℂ) (m : ℕ) (hz : ∀ i ∈ s, (1 : ℝ) ≤ ‖z i‖) :
    ∃ k ∈ Finset.range s.card,
      ‖∑ i ∈ s, a i * z i ^ m‖ ≤ (2 ^ s.card - 1) * ‖∑ i ∈ s, a i * z i ^ (m + (k + 1))‖ := by
  obtain ⟨k, hk, hmax⟩ :=
    (Finset.range s.card).exists_max_image (fun j ↦ ‖∑ i ∈ s, a i * z i ^ (m + (j + 1))‖)
      (Finset.nonempty_range_iff.mpr (ne_of_gt (Finset.card_pos.mpr hs)))
  exact
    ⟨k, hk,
      power_sum_norm_le_block_bound s z a m hz _ (fun j hj ↦ hmax j (Finset.mem_range.mpr hj))⟩

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
