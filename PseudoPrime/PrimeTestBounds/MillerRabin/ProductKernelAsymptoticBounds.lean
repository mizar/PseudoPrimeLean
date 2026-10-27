/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.ProductFermatKernel
public import PseudoPrime.PrimeTestBounds.MillerRabin.PositivePowerFermatKernelBounds

/-! # Unconditional logarithmic-power MR bounds from cofactor size or factor gap -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- SmallCofactorOrGap n tau means n=pm with p prime and either a cofactor
1<m≤p^tau or a positive gap m-p≤p^tau. The parameter tau is real.
This explicit arithmetic family supplies a small ambient Fermat kernel;
neither primality of m nor squarefreeness of n is required. -/
def SmallCofactorOrGap (n : ℕ) (τ : ℝ) : Prop :=
  ∃ p m : ℕ,
    p.Prime ∧
      n = p * m ∧ ((1 < m ∧ (m : ℝ) ≤ (p : ℝ) ^ τ) ∨ (p < m ∧ ((m - p : ℕ) : ℝ) ≤ (p : ℝ) ^ τ))

/-- A small cofactor or positive factor gap gives a prime divisor whose
ambient Fermat kernel gcd(p-1,n-1) is at most p^tau. Apply the exact
product identity and the corresponding natural bound.
This removes the kernel-size hypothesis from the product-family theorem. -/
theorem SmallCofactorOrGap.small_kernel {n : ℕ} {τ : ℝ} (h : SmallCofactorOrGap n τ) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (((p - 1).gcd (n - 1) : ℕ) : ℝ) ≤ (p : ℝ) ^ τ := by
  obtain ⟨p, m, hp, rfl, hsmall | hgap⟩ := h
  · refine ⟨p, hp, dvd_mul_right p m, ?_⟩
    exact
      (Nat.cast_le.mpr
            ((NumberTheory.gcd_predecessor_product_le_cofactor hp.pos hsmall.1).trans
              (Nat.sub_le m 1))).trans
        hsmall.2
  · exact
      ⟨p, hp, dvd_mul_right p m,
        (Nat.cast_le.mpr (NumberTheory.gcd_predecessor_product_le_gap hp.pos hgap.1)).trans hgap.2⟩

/-- For fixed 0<tau<1 and A>1/(1-tau), all sufficiently large odd n>1
in SmallCofactorOrGap n tau have least prime MR witness at most log(n)^A.
Use the proved exact small-kernel analytic theorem after the arithmetic
reduction. The threshold is uniform over the factorization and GRH is absent. -/
theorem eventually_exists_least_prime_witness_of_small_cofactor_or_gap {τ A : ℝ} (hτ0 : 0 < τ)
    (hτ1 : τ < 1) (hA : 1 / (1 - τ) < A) :
    ∀ᶠ n : ℕ in Filter.atTop,
      1 < n →
        Odd n →
        SmallCofactorOrGap n τ →
        ∃ q : ℕ,
          q.Prime ∧
            ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
            (q : ℝ) ≤ (Real.log n) ^ A ∧
            ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → q ≤ r := by
  apply (eventually_exists_least_prime_witness_of_prime_small_kernel hτ0 hτ1 hA).mono
  intro n h hn ho hfamily
  exact h hn ho hfamily.small_kernel

/-- If A<2 as well, the product-family least-prime bound is eventually
strictly below log(n)^2. Keep the same witness and compare real exponents
at log(n)>1. No finite input certificate or GRH assumption is used. -/
theorem eventually_exists_least_prime_witness_strict_of_small_cofactor_or_gap {τ A : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hA : 1 / (1 - τ) < A) (hA2 : A < 2) :
    ∀ᶠ n : ℕ in Filter.atTop,
      1 < n →
        Odd n →
        SmallCofactorOrGap n τ →
        ∃ q : ℕ,
          q.Prime ∧
            ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
            (q : ℝ) ≤ (Real.log n) ^ A ∧
            (q : ℝ) < (Real.log n) ^ 2 ∧
            ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → q ≤ r := by
  have ht : Filter.Tendsto (fun n : ℕ ↦ Real.log n) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_exists_least_prime_witness_of_small_cofactor_or_gap hτ0 hτ1 hA,
    ht.eventually_gt_atTop 1] with n h hL hn ho hfamily
  obtain ⟨q, hq, hf, hb, hleast⟩ := h hn ho hfamily
  have hs : (Real.log n) ^ A < (Real.log n) ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_lt_rpow_of_exponent_lt hL hA2
  exact ⟨q, hq, hf, hb, hb.trans_lt hs, hleast⟩

/-- For every fixed 0<tau<1/2, the cofactor-or-gap family admits a fixed
exponent A<2 for its eventual least-prime MR bound, strictly below log(n)^2.
Choose A between 1/(1-tau) and two and apply the proved family theorem.
The bound is unconditional, including squarefree products with two factors. -/
theorem exists_subquadratic_exponent_of_small_cofactor_or_gap {τ : ℝ} (hτ0 : 0 < τ)
    (hτhalf : τ < 1 / 2) :
    ∃ A : ℝ,
      0 < A ∧
        A < 2 ∧
        ∀ᶠ n : ℕ in Filter.atTop,
          1 < n →
            Odd n →
            SmallCofactorOrGap n τ →
            ∃ q : ℕ,
              q.Prime ∧
                ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
                (q : ℝ) ≤ (Real.log n) ^ A ∧
                (q : ℝ) < (Real.log n) ^ 2 ∧
                ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → q ≤ r := by
  have hτ1 : τ < 1 := lt_trans hτhalf (by norm_num only)
  have hd : 0 < 1 - τ := sub_pos.mpr hτ1
  have hbound : 1 / (1 - τ) < (2 : ℝ) := by
    apply (div_lt_iff₀ hd).mpr
    linarith only [hτhalf]
  obtain ⟨A, hA, hA2⟩ := exists_between hbound
  exact
    ⟨A, (div_pos zero_lt_one hd).trans hA, hA2,
      eventually_exists_least_prime_witness_strict_of_small_cofactor_or_gap hτ0 hτ1 hA hA2⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
