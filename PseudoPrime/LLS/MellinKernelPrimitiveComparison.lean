/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelExplicitFormula
public import PseudoPrime.LLS.SubgroupKernelComparison
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimitiveComparison
public import PseudoPrime.NumberTheory.DirichletCharacterSmallLevels

/-!
# Primitive-character comparison for general Mellin kernels

Separate the change of level from the primitive completed formula.
The correction is supported on common factors with the level-to-conductor quotient.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- At an index coprime to the level-to-conductor quotient, the kernel's arithmetic
summand agrees with its primitive source for any real scale. Apply the character-value
induction identity to the common kernel weight. This confines the primitivization error
to indices sharing a factor with the level quotient. -/
theorem summand_eq_primitive_of_coprime_quotient (K : MellinKernel) {q n : ℕ}
    (χ : DirichletCharacter ℂ q) (x : ℝ) (hcop : Nat.Coprime n (q / χ.conductor)) :
    K.summand χ x n = K.summand χ.primitiveCharacter x n := by
  rw [summand, summand,
    PseudoPrime.AnalyticNumberTheory.Arithmetic.apply_eq_primitiveCharacter_of_coprime_quotient χ
      hcop]

/-- For a nonzero level and positive scale, split the kernel's arithmetic series into
the primitive source series and their termwise difference. Both series are summable,
so subtraction commutes with the infinite sum. This identifies the correction whose
prime-power support will yield the level-change error bound in Lemma 6.1. -/
theorem tsum_summand_eq_primitive_add_difference (K : MellinKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, K.summand χ x n) =
      (∑' n : ℕ, K.summand χ.primitiveCharacter x n) +
        (∑' n : ℕ, (K.summand χ x n - K.summand χ.primitiveCharacter x n)) := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  rw [(summable_summand K χ hx).tsum_sub (summable_summand K χ.primitiveCharacter hx)]
  ring

/-- For a nonprincipal character at level at least 20000 under GRH, its primitive
source's real arithmetic sum is a bounded coefficient times the actual zero mass plus
C(1 + log q / sqrt x) error for scales at least one. Primitivity, nonprincipality and
the conductor range follow from the original character. This is the analytic part of
the level-change comparison, before adding the arithmetic correction. -/
private theorem exists_real_primitive_summand_formula (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q],
          20000 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              χ ≠ 1 →
                PseudoPrime.AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
                  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩;
                  ∀ {x : ℝ},
                    1 ≤ x →
                      ∃ θ r : ℝ,
                        |θ| ≤ 1 ∧
                          |r| ≤ C * (1 + Real.log q / Real.sqrt x) ∧
                          (∑' n : ℕ, K.summand χ.primitiveCharacter x n).re =
                            θ * (∑' ρ : ℂ, ‖K.kernelZeroTerm χ.primitiveCharacter ρ‖) + r := by
  obtain ⟨C, hC, hb⟩ := exists_real_summand_formula_zeroMass_ambient K
  refine ⟨C, hC, ?_⟩
  intro q _ hq χ hne hGRH _ x hx
  have hm := PseudoPrime.NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hn := PseudoPrime.AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  exact
    hb hq hm hmq hGRH (DirichletCharacter.primitiveCharacter_isPrimitive χ) hn (inv_ne_one.mpr hn)
      hx

/-- For a nonprincipal character of level at least 20000 under GRH and scale at least
one, the real arithmetic sum splits into a primitive zero-mass term, a real error bounded
by C(1 + log q / sqrt x), and the exact series of level-change differences. The zero-mass
coefficient has absolute value at most one and C depends only on the kernel. Combine
the primitive completed formula with summability of the two arithmetic series. This
isolates the arithmetic correction still needed for the general form of Lemma 6.1. -/
theorem exists_real_summand_formula_with_primitive_correction (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q],
          20000 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              χ ≠ 1 →
                PseudoPrime.AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
                  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩;
                  ∀ {x : ℝ},
                    1 ≤ x →
                      ∃ θ r : ℝ,
                        |θ| ≤ 1 ∧
                          |r| ≤ C * (1 + Real.log q / Real.sqrt x) ∧
                          (∑' n : ℕ, K.summand χ x n).re =
                            θ * (∑' ρ : ℂ, ‖K.kernelZeroTerm χ.primitiveCharacter ρ‖) + r +
                              (∑' n : ℕ,
                                  (K.summand χ x n - K.summand χ.primitiveCharacter x n)).re := by
  obtain ⟨C, hC, hb⟩ := exists_real_primitive_summand_formula K
  refine ⟨C, hC, ?_⟩
  intro q _ hq χ hne hGRH _ x hx
  obtain ⟨θ, r, hθ, hr, he⟩ := hb hq χ hne hGRH hx
  refine ⟨θ, r, hθ, hr, ?_⟩
  rw [tsum_summand_eq_primitive_add_difference K χ (zero_lt_one.trans_le hx), Complex.add_re, he]

/-- If an index shares a factor with the level-to-conductor quotient, the original
character's smoothed summand vanishes for any scale. The quotient divides the level,
so the character value is zero. This identifies the correction's surviving terms
as negative primitive-source terms. -/
theorem summand_eq_zero_of_not_coprime_quotient (K : MellinKernel) {q n : ℕ}
    (χ : DirichletCharacter ℂ q) (x : ℝ) (hn : ¬Nat.Coprime n (q / χ.conductor)) :
    K.summand χ x n = 0 := by
  have hnq : ¬Nat.Coprime n q := fun h =>
    hn (h.of_dvd_right (Nat.div_dvd_of_dvd χ.conductor_dvd_level))
  have hc : χ n = 0 := by
    simpa only [Int.cast_natCast] using
      (DirichletCharacter.apply_eq_zero_iff χ (n : ℤ)).mpr
        (by simpa only [Nat.isCoprime_iff_coprime] using hnq)
  rw [summand, hc, mul_zero, zero_mul]
  exact ite_self 0

/-- For any scale and index, changing a character to its primitive source changes the
kernel summand by at most the source summand's norm. Off quotient support the values
agree; on support the original term vanishes. This avoids a factor two in the arithmetic
correction majorant. -/
theorem norm_summand_sub_primitive_le (K : MellinKernel) {q n : ℕ} (χ : DirichletCharacter ℂ q)
    (x : ℝ) :
    ‖K.summand χ x n - K.summand χ.primitiveCharacter x n‖ ≤
      ‖K.summand χ.primitiveCharacter x n‖ := by
  by_cases h : Nat.Coprime n (q / χ.conductor)
  · rw [summand_eq_primitive_of_coprime_quotient K χ x h, sub_self, norm_zero]
    exact norm_nonneg _
  · rw [summand_eq_zero_of_not_coprime_quotient K χ x h, zero_sub, norm_neg]

/-- Every kernel has a positive constant bounding each level-change difference by
Lambda(n)/sqrt n times C min(sqrt(n/x), 1/sqrt(n/x)), uniformly over nonzero levels,
characters, positive scales and nonzero indices. Apply the primitive-source profile
bound to the correction norm comparison. This supplies the prime-power summation bound
needed for the conductor error without any GRH assumption. -/
theorem exists_norm_summand_sub_primitive_le_min (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ},
          0 < x →
            ∀ {n : ℕ},
              n ≠ 0 →
                ‖K.summand χ x n - K.summand χ.primitiveCharacter x n‖ ≤
                  (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
                    (C * min (Real.sqrt ((n : ℝ) / x)) (1 / Real.sqrt ((n : ℝ) / x))) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_summand_le_min K
  refine ⟨C, hC, ?_⟩
  intro q _ χ x hx n hn
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  exact (norm_summand_sub_primitive_le K χ x).trans (hb χ.primitiveCharacter hx hn)

/-- For any character, real scale and nonnegative finite cutoff y, the sum of norms of
level-change differences equals the double sum over positive exponents and primes dividing
the level-to-conductor quotient. Remove coprime indices using primitive induction, remove
non-prime-powers using Mangoldt vanishing, and apply finite prime-power reindexing. This
is the finite correction interface for the geometric-tail bound in Lemma 6.1. -/
theorem sum_norm_summand_sub_primitive_eq_prime_powers (K : MellinKernel) {q : ℕ}
    (χ : DirichletCharacter ℂ q) {x y : ℝ} (hy : 0 ≤ y) :
    ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, ‖K.summand χ x n - K.summand χ.primitiveCharacter x n‖ =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log y / Real.log 2⌋₊,
        ∑ p ∈ (Finset.Ioc 0 ⌊y ^ ((1 : ℝ) / k)⌋₊).filter (fun p => p.Prime ∧ p ∣ q / χ.conductor),
          ‖K.summand χ x (p ^ k) - K.summand χ.primitiveCharacter x (p ^ k)‖ := by
  let f := fun n : ℕ => ‖K.summand χ x n - K.summand χ.primitiveCharacter x n‖
  have hf : ∀ n : ℕ, ¬IsPrimePow n → f n = 0 := by
    intro n hn
    dsimp only [f]
    rw [summand_eq_zero_of_not_primePow K χ x hn,
      summand_eq_zero_of_not_primePow K χ.primitiveCharacter x hn, sub_self, norm_zero]
  have he :
    (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, f n) =
      ∑ n ∈ (Finset.Ioc 0 ⌊y⌋₊).filter (fun n => ¬Nat.Coprime n (q / χ.conductor)), f n := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : Nat.Coprime n (q / χ.conductor)
    · dsimp only [f]
      rw [summand_eq_primitive_of_coprime_quotient K χ x hn, sub_self, norm_zero]
      rw [ite_self]
    · simp only [hn, not_false_eq_true, ite_true]
  change (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, f n) = _
  rw [he]
  exact
    PseudoPrime.AnalyticNumberTheory.Arithmetic.sum_not_coprime_eq_sum_prime_powers f
      (q / χ.conductor) hy hf

/-- Every kernel has a positive constant bounding a finite level-change difference
sum by the prime-power profile with coefficient log p, uniformly over nonzero levels,
characters, positive scales and nonnegative cutoffs. Apply the norm triangle inequality,
reindex the correction norm sum, and substitute the prime-power Mangoldt value into the
pointwise profile bound. This reduces the total correction estimate to real finite sums
whose low powers and geometric tails can be bounded separately. -/
theorem exists_norm_sum_summand_sub_primitive_le_prime_profile (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x y : ℝ},
          0 < x →
            0 ≤ y →
            ‖∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, (K.summand χ x n - K.summand χ.primitiveCharacter x n)‖ ≤
              ∑ k ∈ Finset.Icc 1 ⌊Real.log y / Real.log 2⌋₊,
                ∑
                  p ∈
                    (Finset.Ioc 0 ⌊y ^ ((1 : ℝ) / k)⌋₊).filter
                      (fun p => p.Prime ∧ p ∣ q / χ.conductor),
                  (Real.log p / Real.sqrt ((p : ℝ) ^ k)) *
                    (C *
                      min (Real.sqrt (((p : ℝ) ^ k) / x)) (1 / Real.sqrt (((p : ℝ) ^ k) / x))) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_summand_sub_primitive_le_min K
  refine ⟨C, hC, ?_⟩
  intro q _ χ x y hx hy
  have h :=
    norm_sum_le (Finset.Ioc 0 ⌊y⌋₊) (fun n => K.summand χ x n - K.summand χ.primitiveCharacter x n)
  rw [sum_norm_summand_sub_primitive_eq_prime_powers K χ hy] at h
  refine h.trans ?_
  apply Finset.sum_le_sum
  intro k hk
  apply Finset.sum_le_sum
  intro p hp
  have hk0 : k ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1)
  have hpprime := (Finset.mem_filter.mp hp).2.1
  have hb' := hb χ hx (pow_ne_zero k hpprime.ne_zero)
  rw [ArithmeticFunction.vonMangoldt_apply_pow hk0,
    ArithmeticFunction.vonMangoldt_apply_prime hpprime, Nat.cast_pow] at hb'
  exact hb'

/-- Cancel the square-root index factor in the growing side of the correction profile. -/
private theorem profile_sqrt_identity {a x L C : ℝ} (ha : 0 < a) :
    (L / Real.sqrt a) * (C * Real.sqrt (a / x)) = C * L / Real.sqrt x := by
  rw [Real.sqrt_div ha.le]
  calc
    _ = (C * L) * Real.sqrt a / (Real.sqrt x * Real.sqrt a) := by ring
    _ = _ := mul_div_mul_right _ _ (ne_of_gt (Real.sqrt_pos.mpr ha))

/-- Combine the two square-root index factors in the decaying side of the profile. -/
private theorem profile_inverse_sqrt_identity {a x L C : ℝ} (ha : 0 < a) :
    (L / Real.sqrt a) * (C * (1 / Real.sqrt (a / x))) = C * L * Real.sqrt x / a := by
  rw [Real.sqrt_div ha.le, one_div_div]
  calc
    _ = (C * L * Real.sqrt x) / (Real.sqrt a * Real.sqrt a) := by ring
    _ = _ := by rw [← sq, Real.sq_sqrt ha.le]

/-- Nonnegative profile weights are bounded by the growing side after cancellation. -/
private theorem profile_le_constant {a x L C : ℝ} (ha : 0 < a) (hL : 0 ≤ L) (hC : 0 ≤ C) :
    (L / Real.sqrt a) * (C * min (Real.sqrt (a / x)) (1 / Real.sqrt (a / x))) ≤
      C * L / Real.sqrt x := by
  have h :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (min_le_left (Real.sqrt (a / x)) (1 / Real.sqrt (a / x))) hC)
      (div_nonneg hL (Real.sqrt_nonneg a))
  exact h.trans_eq (profile_sqrt_identity ha)

/-- Nonnegative profile weights are bounded by the decaying reciprocal-index side. -/
private theorem profile_le_reciprocal {a x L C : ℝ} (ha : 0 < a) (hL : 0 ≤ L) (hC : 0 ≤ C) :
    (L / Real.sqrt a) * (C * min (Real.sqrt (a / x)) (1 / Real.sqrt (a / x))) ≤
      C * L * Real.sqrt x / a := by
  have h :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (min_le_right (Real.sqrt (a / x)) (1 / Real.sqrt (a / x))) hC)
      (div_nonneg hL (Real.sqrt_nonneg a))
  exact h.trans_eq (profile_inverse_sqrt_identity ha)

/-- For every kernel, one positive constant bounds each level-change difference both
by C Lambda(n)/sqrt x and by C Lambda(n) sqrt x/n, uniformly over nonzero levels,
characters, positive scales and nonzero indices. Select each side of the transform
profile and cancel the square-root index factors. The first bound counts low powers;
the second supplies the geometric tail when the index exceeds the scale. -/
theorem exists_norm_summand_sub_primitive_le_split (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ},
          0 < x →
            ∀ {n : ℕ},
              n ≠ 0 →
                (‖K.summand χ x n - K.summand χ.primitiveCharacter x n‖ ≤
                    C * ArithmeticFunction.vonMangoldt n / Real.sqrt x) ∧
                  (‖K.summand χ x n - K.summand χ.primitiveCharacter x n‖ ≤
                    C * ArithmeticFunction.vonMangoldt n * Real.sqrt x / n) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_summand_sub_primitive_le_min K
  refine ⟨C, hC, ?_⟩
  intro q _ χ x hx n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  have h := hb χ hx hn
  exact
    ⟨h.trans (profile_le_constant hnpos ArithmeticFunction.vonMangoldt_nonneg hC.le),
      h.trans (profile_le_reciprocal hnpos ArithmeticFunction.vonMangoldt_nonneg hC.le)⟩

/-- For every kernel, a positive constant bounds the norm sum of one prime's
level-change terms from any positive start m through N by 2 C log p sqrt x/p^m,
uniformly over nonzero levels, characters and positive scales. Use the reciprocal-index
bound for each summand and the finite inverse-prime-power tail estimate. The upper
cutoff does not occur in the bound, allowing the correction's tail limit in Lemma 6.1. -/
theorem exists_sum_norm_summand_sub_primitive_prime_tail_le (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ},
          0 < x →
            ∀ {p m N : ℕ},
              p.Prime →
                1 ≤ m →
                ∑ k ∈ Finset.Icc m N,
                    ‖K.summand χ x (p ^ k) - K.summand χ.primitiveCharacter x (p ^ k)‖ ≤
                  2 * C * Real.log p * Real.sqrt x / (p : ℝ) ^ m := by
  obtain ⟨C, hC, hb⟩ := exists_norm_summand_sub_primitive_le_split K
  refine ⟨C, hC, ?_⟩
  intro q _ χ x hx p m N hp hm
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hscalar : 0 ≤ C * Real.log p * Real.sqrt x :=
    mul_nonneg (mul_nonneg hC.le hlog) (Real.sqrt_nonneg x)
  calc
    _ ≤ ∑ k ∈ Finset.Icc m N, C * Real.log p * Real.sqrt x / (p : ℝ) ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      have hk0 : k ≠ 0 :=
        Nat.ne_of_gt (Nat.zero_lt_one.trans_le (hm.trans (Finset.mem_Icc.mp hk).1))
      have h := (hb χ hx (pow_ne_zero k hp.ne_zero)).2
      simpa only [ArithmeticFunction.vonMangoldt_apply_pow hk0,
        ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow] using h
    _ = (C * Real.log p * Real.sqrt x) * (∑ k ∈ Finset.Icc m N, 1 / (p : ℝ) ^ k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ (C * Real.log p * Real.sqrt x) * (2 / (p : ℝ) ^ m) :=
      mul_le_mul_of_nonneg_left
        (PseudoPrime.AnalyticNumberTheory.Arithmetic.sum_inv_prime_pow_tail_le hp) hscalar
    _ = _ := by ring

/-- For every kernel, one positive constant bounds the tail of a prime's level-change
terms by 2 C log p/sqrt x whenever the first power is at least the positive scale.
The bound is uniform in the final exponent, nonzero level and character. Apply the
geometric-tail bound, compare the first prime power with x, and cancel sqrt x/x.
This is the high-power contribution to the primitivization error in Lemma 6.1. -/
theorem exists_sum_norm_summand_sub_primitive_prime_tail_le_scale (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ},
          0 < x →
            ∀ {p m N : ℕ},
              p.Prime →
                1 ≤ m →
                x ≤ (p : ℝ) ^ m →
                ∑ k ∈ Finset.Icc m N,
                    ‖K.summand χ x (p ^ k) - K.summand χ.primitiveCharacter x (p ^ k)‖ ≤
                  2 * C * Real.log p / Real.sqrt x := by
  obtain ⟨C, hC, hb⟩ := exists_sum_norm_summand_sub_primitive_prime_tail_le K
  refine ⟨C, hC, ?_⟩
  intro q _ χ x hx p m N hp hm hxm
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hscalar : 0 ≤ 2 * C * Real.log p * Real.sqrt x :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num only) hC.le) hlog) (Real.sqrt_nonneg x)
  have h := div_le_div_of_nonneg_left hscalar hx hxm
  have he : 2 * C * Real.log p * Real.sqrt x / x = 2 * C * Real.log p / Real.sqrt x := by
    rw [mul_div_assoc, Real.sqrt_div_self', ← mul_div_assoc, mul_one]
  exact (hb χ hx hp hm).trans (h.trans_eq he)

/-- For every kernel, one positive constant bounds a prime's first N level-change
terms by N C log p/sqrt x, uniformly over nonzero levels, characters and positive scales.
Apply the constant-index bound to each prime power and count the positive exponents.
This supplies the low-power part of the primitivization error before choosing a cutoff. -/
theorem exists_sum_norm_summand_sub_primitive_prime_prefix_le (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ},
          0 < x →
            ∀ {p N : ℕ},
              p.Prime →
                ∑ k ∈ Finset.Icc 1 N,
                    ‖K.summand χ x (p ^ k) - K.summand χ.primitiveCharacter x (p ^ k)‖ ≤
                  N * C * Real.log p / Real.sqrt x := by
  obtain ⟨C, hC, hb⟩ := exists_norm_summand_sub_primitive_le_split K
  refine ⟨C, hC, ?_⟩
  intro q _ χ x hx p N hp
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 N, C * Real.log p / Real.sqrt x := by
      apply Finset.sum_le_sum
      intro k hk
      have hk0 : k ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1)
      have h := (hb χ hx (pow_ne_zero k hp.ne_zero)).1
      simpa only [ArithmeticFunction.vonMangoldt_apply_pow hk0,
        ArithmeticFunction.vonMangoldt_apply_prime hp] using h
    _ = _ := by
      rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring

/-- For every kernel, a positive constant bounds a prime's first N correction terms
by (m + 2) C log p/sqrt x whenever p^(m+1) is at least the positive scale x.
The bound is uniform in N, level and character. Split at m, count the low powers and
apply the scale-normalized geometric tail. If N is smaller, enlarge its nonnegative
norm sum to the low-power prefix. This is the uniform primewise estimate to which an
integer logarithmic cutoff will be applied in the total primitivization bound. -/
theorem exists_sum_norm_summand_sub_primitive_prime_le_of_cutoff (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ},
          0 < x →
            ∀ {p m N : ℕ},
              p.Prime →
                x ≤ (p : ℝ) ^ (m + 1) →
                ∑ k ∈ Finset.Icc 1 N,
                    ‖K.summand χ x (p ^ k) - K.summand χ.primitiveCharacter x (p ^ k)‖ ≤
                  ((m : ℝ) + 2) * C * Real.log p / Real.sqrt x := by
  obtain ⟨Cl, hCl, hl⟩ := exists_sum_norm_summand_sub_primitive_prime_prefix_le K
  obtain ⟨Ct, hCt, ht⟩ := exists_sum_norm_summand_sub_primitive_prime_tail_le_scale K
  refine ⟨Cl + Ct, add_pos hCl hCt, ?_⟩
  intro q _ χ x hx p m N hp hxm
  let f := fun k : ℕ => ‖K.summand χ x (p ^ k) - K.summand χ.primitiveCharacter x (p ^ k)‖
  let W := Real.log p / Real.sqrt x
  have hW : 0 ≤ W := div_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_le)) (Real.sqrt_nonneg x)
  have hlow : (∑ k ∈ Finset.Icc 1 m, f k) ≤ (m : ℝ) * Cl * W := by
    simpa only [mul_div_assoc] using hl χ hx hp (N := m)
  have htail : (∑ k ∈ Finset.Icc (m + 1) N, f k) ≤ 2 * Ct * W := by
    simpa only [mul_div_assoc] using ht χ hx hp (Nat.le_add_left 1 m) hxm (N := N)
  have hpCl := mul_nonneg hCl.le hW
  have hpCt := mul_nonneg hCt.le hW
  have hmCt := mul_nonneg (Nat.cast_nonneg m) hpCt
  rw [mul_div_assoc]
  change (∑ k ∈ Finset.Icc 1 N, f k) ≤ ((m : ℝ) + 2) * (Cl + Ct) * W
  by_cases hmN : m ≤ N
  · have he := Finset.sum_Ico_consecutive f (Nat.le_add_left 1 m) (Nat.add_le_add_right hmN 1)
    simp only [Finset.Ico_add_one_right_eq_Icc] at he
    rw [← he]
    nlinarith only [hlow, htail, hpCl, hmCt]
  · have hNm : N ≤ m := (Nat.lt_of_not_ge hmN).le
    have hsub : Finset.Icc 1 N ⊆ Finset.Icc 1 m := by
      intro k hk
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1, (Finset.mem_Icc.mp hk).2.trans hNm⟩
    have hsum :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun k _ _ =>
          norm_nonneg (K.summand χ x (p ^ k) - K.summand χ.primitiveCharacter x (p ^ k)))
    nlinarith only [hsum, hlow, hpCl, hpCt, hmCt]

/-- For x at least two, the floor's base-two logarithm chooses a cutoff valid for
all primes, and its count plus two is at most 3 log x/log 2. Use the lower and upper
power bounds for the integer logarithm, then take real logarithms. -/
private theorem common_primePower_cutoff_bounds {x : ℝ} (hx : 2 ≤ x) :
    x ≤ (2 : ℝ) ^ (Nat.log 2 ⌊x⌋₊ + 1) ∧
      ((Nat.log 2 ⌊x⌋₊ : ℝ) + 2) ≤ 3 * Real.log x / Real.log 2 := by
  have hx0 : 0 ≤ x := (by norm_num only : (0 : ℝ) ≤ 2).trans hx
  have hx1 : (1 : ℝ) ≤ x := (by norm_num only : (1 : ℝ) ≤ 2).trans hx
  have hfloor1 : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr (by simpa only [Nat.cast_one] using hx1)
  have hfloor0 : ⌊x⌋₊ ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_one.trans_le hfloor1)
  have hlo : (2 : ℝ) ^ Nat.log 2 ⌊x⌋₊ ≤ x := by
    have h := Nat.pow_log_le_self 2 hfloor0
    have hc : (2 : ℝ) ^ Nat.log 2 ⌊x⌋₊ ≤ ⌊x⌋₊ := by exact_mod_cast h
    exact hc.trans (Nat.floor_le hx0)
  have hu : x < (2 : ℝ) ^ (Nat.log 2 ⌊x⌋₊ + 1) := by
    have h := Nat.lt_pow_succ_log_self (by norm_num only : 1 < 2) ⌊x⌋₊
    have h' := (Nat.floor_lt hx0).mp h
    exact_mod_cast h'
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have hlog := Real.log_le_log (pow_pos (by norm_num only : (0 : ℝ) < 2) _) hlo
  rw [Real.log_pow] at hlog
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num only) hx
  refine ⟨hu.le, (le_div_iff₀ hl2).mpr ?_⟩
  nlinarith only [hlog, hlx]

/-- Every kernel admits one positive constant bounding each prime's first N correction
terms by C log x log p/sqrt x for x at least two, uniformly in N, nonzero level and
character. Use the base-two logarithmic cutoff common to every prime and combine its
count bound with the primewise correction estimate. This is summed over the quotient's
prime divisors to obtain the uniform primitivization error in Lemma 6.1. -/
theorem exists_sum_norm_summand_sub_primitive_prime_le_log_scale (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ},
          2 ≤ x →
            ∀ {p N : ℕ},
              p.Prime →
                ∑ k ∈ Finset.Icc 1 N,
                    ‖K.summand χ x (p ^ k) - K.summand χ.primitiveCharacter x (p ^ k)‖ ≤
                  C * Real.log x * Real.log p / Real.sqrt x := by
  obtain ⟨C, hC, hb⟩ := exists_sum_norm_summand_sub_primitive_prime_le_of_cutoff K
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  refine ⟨3 * C / Real.log 2, div_pos (mul_pos (by norm_num only) hC) hl2, ?_⟩
  intro q _ χ x hx p N hp
  obtain ⟨hpow, hcount⟩ := common_primePower_cutoff_bounds hx
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hxp : x ≤ (p : ℝ) ^ (Nat.log 2 ⌊x⌋₊ + 1) :=
    hpow.trans (pow_le_pow_left₀ (by norm_num only) hp2 _)
  have h := hb χ ((by norm_num only : (0 : ℝ) < 2).trans_le hx) hp hxp (N := N)
  have hscalar : 0 ≤ C * Real.log p / Real.sqrt x :=
    div_nonneg (mul_nonneg hC.le (Real.log_nonneg (by exact_mod_cast hp.one_le)))
      (Real.sqrt_nonneg x)
  have h' := mul_le_mul_of_nonneg_right hcount hscalar
  calc
    _ ≤ ((Nat.log 2 ⌊x⌋₊ : ℝ) + 2) * (C * Real.log p / Real.sqrt x) := by
      simpa only [mul_div_assoc, mul_assoc] using h
    _ ≤ (3 * Real.log x / Real.log 2) * (C * Real.log p / Real.sqrt x) := h'
    _ = _ := by ring

/-- Every kernel admits a positive constant bounding the sum of correction norms
up to any nonnegative cutoff by C log q log x/sqrt x for scales x at least two,
uniformly in the cutoff, nonzero level and character. Reindex by prime powers, enlarge
the prime support to the quotient's prime divisors, exchange the finite sums, and use
the primewise bound and the sum of prime-factor logarithms. This is the absolute finite
sum estimate passed to the infinite primitivization error in Lemma 6.1. -/
theorem exists_sum_norm_summand_sub_primitive_le_log (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x y : ℝ},
          2 ≤ x →
            0 ≤ y →
            (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, ‖K.summand χ x n - K.summand χ.primitiveCharacter x n‖) ≤
              C * Real.log q * Real.log x / Real.sqrt x := by
  obtain ⟨C, hC, hb⟩ := exists_sum_norm_summand_sub_primitive_prime_le_log_scale K
  refine ⟨C, hC, ?_⟩
  intro q _ χ x y hx hy
  let m := q / χ.conductor
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hmpos : 0 < m :=
    Nat.div_pos (Nat.le_of_dvd hqpos χ.conductor_dvd_level) (Nat.pos_of_ne_zero χ.conductor_ne_zero)
  have hm0 : m ≠ 0 := hmpos.ne'
  have hmle : m ≤ q := Nat.div_le_self q χ.conductor
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hlogM : (∑ p ∈ m.primeFactors, Real.log p) ≤ Real.log q :=
    (PseudoPrime.AnalyticNumberTheory.Arithmetic.sum_log_primeFactors_le_log hm0).trans
      (Real.log_le_log hmR (by exact_mod_cast hmle))
  have hscale : 0 ≤ C * Real.log x / Real.sqrt x :=
    div_nonneg (mul_nonneg hC.le (Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 2).trans hx)))
      (Real.sqrt_nonneg x)
  let f := fun k p : ℕ => ‖K.summand χ x (p ^ k) - K.summand χ.primitiveCharacter x (p ^ k)‖
  rw [sum_norm_summand_sub_primitive_eq_prime_powers K χ hy]
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 ⌊Real.log y / Real.log 2⌋₊, ∑ p ∈ m.primeFactors, f k p := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact
          Nat.mem_primeFactors.mpr
            ⟨(Finset.mem_filter.mp hp).2.1, (Finset.mem_filter.mp hp).2.2, hm0⟩
      · intro p _ _
        exact norm_nonneg _
    _ = ∑ p ∈ m.primeFactors, ∑ k ∈ Finset.Icc 1 ⌊Real.log y / Real.log 2⌋₊, f k p :=
      Finset.sum_comm
    _ ≤ ∑ p ∈ m.primeFactors, C * Real.log x * Real.log p / Real.sqrt x := by
      apply Finset.sum_le_sum
      intro p hp
      exact hb χ hx (Nat.prime_of_mem_primeFactors hp)
    _ = (C * Real.log x / Real.sqrt x) * (∑ p ∈ m.primeFactors, Real.log p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ (C * Real.log x / Real.sqrt x) * Real.log q := mul_le_mul_of_nonneg_left hlogM hscale
    _ = _ := by ring

/-- Every kernel has a positive constant bounding the absolute correction series and
the norm of its complex sum by C log q log x/sqrt x, uniformly over nonzero levels,
characters and x at least two. The norm series is summable. Enlarge an arbitrary finite
set to its maximum's interval, remove the zero term, and use the finite uniform bound
to obtain summability and the total-sum estimate. This removes the arithmetic
primitivization error as an extra hypothesis in the general form of Lemma 6.1. -/
theorem exists_tsum_norm_summand_sub_primitive_le_log (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ},
          2 ≤ x →
            Summable (fun n : ℕ => ‖K.summand χ x n - K.summand χ.primitiveCharacter x n‖) ∧
              (∑' n : ℕ, ‖K.summand χ x n - K.summand χ.primitiveCharacter x n‖) ≤
                C * Real.log q * Real.log x / Real.sqrt x ∧
              ‖∑' n : ℕ, (K.summand χ x n - K.summand χ.primitiveCharacter x n)‖ ≤
                C * Real.log q * Real.log x / Real.sqrt x := by
  obtain ⟨C, hC, hb⟩ := exists_sum_norm_summand_sub_primitive_le_log K
  refine ⟨C, hC, ?_⟩
  intro q _ χ x hx
  let f := fun n : ℕ => ‖K.summand χ x n - K.summand χ.primitiveCharacter x n‖
  have hf0 : f 0 = 0 := by simp only [f, summand, ite_true, sub_self, norm_zero]
  have hfinite : ∀ s : Finset ℕ, (∑ n ∈ s, f n) ≤ C * Real.log q * Real.log x / Real.sqrt x := by
    intro s
    have hsub : s ⊆ Finset.Icc 0 (s.sup id) := by
      intro n hn
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le n, Finset.le_sup (f := id) hn⟩
    have h :=
      Finset.sum_le_sum_of_subset_of_nonneg (f := f) hsub
        (fun n _ _ => norm_nonneg (K.summand χ x n - K.summand χ.primitiveCharacter x n))
    rw [← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le (s.sup id)), hf0, zero_add] at h
    have h' := hb χ hx (Nat.cast_nonneg (s.sup id))
    rw [Nat.floor_natCast] at h'
    exact h.trans h'
  have hs : Summable f := summable_of_sum_le (fun n => norm_nonneg _) hfinite
  have hsum : (∑' n : ℕ, f n) ≤ C * Real.log q * Real.log x / Real.sqrt x :=
    hs.tsum_le_of_sum_le hfinite
  exact ⟨hs, hsum, (norm_tsum_le_tsum_norm hs).trans hsum⟩

/-- For a nonprincipal character of level at least 20000, GRH gives a real explicit formula
with the absolute zero sum of its primitive character. The coefficient has absolute value at
most one, and the remainder is bounded uniformly by
C * (1 + log q * log x / sqrt x) for x ≥ 2. The proof combines the primitive explicit
formula with the absolutely convergent level-change correction and absorbs both errors.
This isolates the zero-mass estimate needed for Lemma 6.1. -/
theorem exists_real_summand_formula_primitive_zeroMass (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q],
          20000 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              χ ≠ 1 →
                PseudoPrime.AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
                  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩;
                  ∀ {x : ℝ},
                    2 ≤ x →
                      ∃ θ r : ℝ,
                        |θ| ≤ 1 ∧
                          |r| ≤ C * (1 + Real.log q * Real.log x / Real.sqrt x) ∧
                          (∑' n : ℕ, K.summand χ x n).re =
                            θ * (∑' ρ : ℂ, ‖K.kernelZeroTerm χ.primitiveCharacter ρ‖) + r := by
  obtain ⟨Ca, hCa, ha⟩ := exists_real_summand_formula_with_primitive_correction K
  obtain ⟨Cd, hCd, hd⟩ := exists_tsum_norm_summand_sub_primitive_le_log K
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have hratio : 0 < Ca / Real.log 2 := div_pos hCa hl2
  refine ⟨Ca + Ca / Real.log 2 + Cd, add_pos (add_pos hCa hratio) hCd, ?_⟩
  intro q _ hq χ hne hGRH _ x hx
  obtain ⟨θ, r0, hθ, hr0, he⟩ := ha hq χ hne hGRH ((by norm_num only : (1 : ℝ) ≤ 2).trans hx)
  let D := ∑' n : ℕ, (K.summand χ x n - K.summand χ.primitiveCharacter x n)
  let V := Real.log q / Real.sqrt x
  let U := V * Real.log x
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by linarith only [hq] : 1 ≤ q)
  have hV : 0 ≤ V := div_nonneg (Real.log_nonneg hq1) (Real.sqrt_nonneg x)
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num only) hx
  have hU : 0 ≤ U := mul_nonneg hV (hl2.le.trans hlx)
  have hUEq : Real.log q * Real.log x / Real.sqrt x = U := by
    dsimp only [U, V]
    ring
  have hVU : V ≤ U / Real.log 2 := (le_div_iff₀ hl2).mpr (mul_le_mul_of_nonneg_left hlx hV)
  have hD : ‖D‖ ≤ Cd * U := by
    have h := (hd χ hx).2.2
    rw [mul_assoc, mul_div_assoc, hUEq] at h
    exact h
  have hr : |r0 + D.re| ≤ |r0| + |D.re| := by
    simpa only [Real.norm_eq_abs] using norm_add_le r0 D.re
  have hDr : |D.re| ≤ Cd * U := (Complex.abs_re_le_norm D).trans hD
  have hCV : Ca * V ≤ (Ca / Real.log 2) * U := by
    calc
      _ ≤ Ca * (U / Real.log 2) := mul_le_mul_of_nonneg_left hVU hCa.le
      _ = _ := by ring
  have hCaU := mul_nonneg hCa.le hU
  refine ⟨θ, r0 + D.re, hθ, ?_, ?_⟩
  · rw [hUEq]
    change |r0| ≤ Ca * (1 + V) at hr0
    nlinarith only [hr, hr0, hDr, hCV, hCaU, hratio, hCd]
  · simpa only [add_assoc] using he

/-- For every nonzero level and scale at least two, the principal-character arithmetic
sum differs from its level-one counterpart by at most `C * log q * log x / sqrt x`,
with a positive constant depending only on the kernel. The primitive source of a
principal character has conductor one and value one at every index. Rewrite the
absolutely convergent level-change correction using this source. This reduces the
principal-character part of Lemma 6.1 to the zeta case at level one. -/
theorem exists_norm_principal_summand_sub_level_one_le (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q] {x : ℝ},
          2 ≤ x →
            ‖(∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ q) x n) -
                  (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x n)‖ ≤
              C * Real.log q * Real.log x / Real.sqrt x := by
  obtain ⟨C, hC, hb⟩ := exists_tsum_norm_summand_sub_primitive_le_log K
  refine ⟨C, hC, ?_⟩
  intro q _ x hx
  have he :
    ∀ n : ℕ,
      K.summand (1 : DirichletCharacter ℂ q).primitiveCharacter x n =
        K.summand (1 : DirichletCharacter ℂ 1) x n := by
    intro n
    have hn : IsUnit (n : ZMod ((1 : DirichletCharacter ℂ q).conductor)) := by
      rw [DirichletCharacter.conductor_one]
      exact isUnit_of_subsingleton _
    rw [summand, summand, DirichletCharacter.primitiveCharacter_one, MulChar.one_apply hn,
      MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1))]
  have hs := (hb (1 : DirichletCharacter ℂ q) hx).2.2
  have hp : 0 < x := (by norm_num only : (0 : ℝ) < 2).trans_le hx
  rw [←
    (summable_summand K (1 : DirichletCharacter ℂ q) hp).tsum_sub
      (summable_summand K (1 : DirichletCharacter ℂ 1) hp)]
  exact (by simpa only [he] using hs)

/-- A positive uniform bound for the level-one principal arithmetic sum minus
`K(1/2) * sqrt x` implies the principal estimate at every nonzero level for scales
at least two. The bound becomes `C * (1 + log q * log x / sqrt x)`, with `C` independent
of the level and scale. Apply the triangle inequality to the level-change correction
and the assumed zeta remainder. This transfers the zeta part of Lemma 6.1 to all levels;
the level-one analytic estimate remains an explicit hypothesis. -/
theorem exists_principal_summand_remainder_le_of_level_one (K : MellinKernel) {A : ℝ} (hA : 0 < A)
    (hbase :
      ∀ {x : ℝ},
        2 ≤ x →
          ‖(∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x n) -
                K.function (1 / 2) * (Real.sqrt x : ℂ)‖ ≤
            A) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q] {x : ℝ},
          2 ≤ x →
            ‖(∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ q) x n) -
                  K.function (1 / 2) * (Real.sqrt x : ℂ)‖ ≤
              C * (1 + Real.log q * Real.log x / Real.sqrt x) := by
  obtain ⟨B, hB, hb⟩ := exists_norm_principal_summand_sub_level_one_le K
  refine ⟨A + B, add_pos hA hB, ?_⟩
  intro q _ x hx
  let S := ∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ q) x n
  let Z := ∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x n
  let P := K.function (1 / 2) * (Real.sqrt x : ℂ)
  let U := Real.log q * Real.log x / Real.sqrt x
  have ht : ‖S - P‖ ≤ ‖S - Z‖ + ‖Z - P‖ := by
    calc
      _ = ‖(S - Z) + (Z - P)‖ := by rw [sub_add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hx1 : (1 : ℝ) ≤ x := (by norm_num only : (1 : ℝ) ≤ 2).trans hx
  have hU : 0 ≤ U :=
    div_nonneg (mul_nonneg (Real.log_nonneg hq) (Real.log_nonneg hx1)) (Real.sqrt_nonneg x)
  have hAU := mul_nonneg hA.le hU
  have hd : ‖S - Z‖ ≤ B * U := by
    simpa only [S, Z, U, mul_div_assoc, mul_assoc] using hb (q := q) hx
  have hz : ‖Z - P‖ ≤ A := hbase hx
  change ‖S - P‖ ≤ (A + B) * (1 + U)
  nlinarith only [ht, hd, hz, hAU, hB]

end PseudoPrime.LLS.PaperStatements.MellinKernel
