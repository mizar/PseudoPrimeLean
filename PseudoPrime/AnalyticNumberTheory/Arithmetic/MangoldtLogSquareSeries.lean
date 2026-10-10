/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.Tactic

/-!
# Logarithmic zeta series and the square Mangoldt correction

The series `Λ(n)/(n² log n)` sums to `log(π²/6)`. A square cutoff separates
this constant into the finite comparison term and its exact loss. Bounds for
odd indices and powers of two give a loss at most `3/(2 sqrt x)` for `x ≥ 100`.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For a natural index n, define Lambda(n)/(n^2 log n), with total division
at zero and one. Prime powers give the logarithmic zeta series at two; its tails measure the
loss when the square correction in the L-value comparison is truncated. -/
noncomputable def mangoldtLogSquareTerm (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / ((n : ℝ) ^ 2 * Real.log n)

/-- The square logarithmic Mangoldt series is summable. For n >= 2, use
0 <= Lambda(n) <= log n to dominate its nonnegative terms by 1/n^2. This justifies splitting
the logarithmic zeta series into a finite square correction and its complementary tail. -/
theorem summable_mangoldtLogSquareTerm : Summable mangoldtLogSquareTerm := by
  apply
    Summable.of_norm_bounded_eventually_nat
      (Real.summable_one_div_nat_pow.mpr (show 1 < (2 : ℕ) by decide))
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
  have hn1 : (1 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le (by decide : 1 < 2) hn
  have hlog := Real.log_pos hn1
  have hnonneg : 0 ≤ mangoldtLogSquareTerm n :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (mul_nonneg (sq_nonneg _) hlog.le)
  rw [Real.norm_of_nonneg hnonneg, mangoldtLogSquareTerm, mul_comm ((n : ℝ) ^ 2), ← div_div]
  exact
    div_le_div_of_nonneg_right ((div_le_one hlog).mpr ArithmeticFunction.vonMangoldt_le_log)
      (sq_nonneg _)

/-- For every x and natural m, doubling the square comparison weight equals
the logarithmic square term minus 2 Lambda(m)/(x log x). Use log(m^2)=2 log m and totalized
inverse identities, so that zero denominators require no exceptional hypotheses. -/
private theorem two_mul_squareCorrectionTerm_eq (x : ℝ) (m : ℕ) :
    2 *
        (ArithmeticFunction.vonMangoldt m *
          (1 / ((m : ℝ) ^ 2 * Real.log ((m : ℝ) ^ 2)) - 1 / (x * Real.log x))) =
      mangoldtLogSquareTerm m - 2 * ArithmeticFunction.vonMangoldt m / (x * Real.log x) := by
  rw [mangoldtLogSquareTerm, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The sum of Lambda(n)/(n^2 log n) equals log(pi^2/6). Identify its complex
L-series with the logarithm of the zeta Euler product, take real parts of the exponential
identity, and use zeta(2)=pi^2/6. This fixes the constant in the reciprocal L-value bound. -/
theorem tsum_mangoldtLogSquareTerm_eq_log_pi_sq_div_six :
    ∑' n : ℕ, mangoldtLogSquareTerm n = Real.log (Real.pi ^ 2 / 6) := by
  change
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / ((n : ℝ) ^ 2 * Real.log n)) =
      Real.log (Real.pi ^ 2 / 6)
  have hzero : (fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℂ) / (Real.log n : ℂ)) 0 = 0 := by
    simp only [ArithmeticFunction.map_zero, Complex.ofReal_zero, zero_div]
  have heq :
    LSeries (fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℂ) / (Real.log n : ℂ)) 2 =
      (((∑' n : ℕ, ArithmeticFunction.vonMangoldt n / ((n : ℝ) ^ 2 * Real.log n)) : ℝ) : ℂ) := by
    rw [LSeries_def₀ hzero, Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) from rfl, Complex.cpow_natCast]
    rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast]
    ring
  have h := riemannZeta_eq_exp_LSeries (s := (2 : ℂ)) (by norm_num only [Complex.re_ofNat])
  rw [heq, riemannZeta_two] at h
  have hr := congrArg Complex.re h
  simp only [Complex.exp_ofReal_re, Complex.div_ofNat_re, ← Complex.ofReal_pow,
    Complex.ofReal_re] at hr
  rw [← hr, Real.log_exp]

/-- For any finite natural index set and real cutoff x, twice the square
comparison sum equals log(pi^2/6) minus its complementary logarithmic series tail and the
finite cutoff term. Summability separates the full zeta series; the term identity then
isolates the two losses that need a quantitative bound. -/
theorem two_mul_squareCorrection_sum_eq (x : ℝ) (s : Finset ℕ) :
    2 *
        ∑ m ∈ s,
          ArithmeticFunction.vonMangoldt m *
            (1 / ((m : ℝ) ^ 2 * Real.log ((m : ℝ) ^ 2)) - 1 / (x * Real.log x)) =
      Real.log (Real.pi ^ 2 / 6) - (∑' m : { m : ℕ // m ∉ s }, mangoldtLogSquareTerm m) -
        2 * (∑ m ∈ s, ArithmeticFunction.vonMangoldt m) / (x * Real.log x) := by
  have h := summable_mangoldtLogSquareTerm.sum_add_tsum_compl (s := s)
  rw [tsum_mangoldtLogSquareTerm_eq_log_pi_sq_div_six] at h
  change
    (∑ m ∈ s, mangoldtLogSquareTerm m) + (∑' m : { m : ℕ // m ∉ s }, mangoldtLogSquareTerm m) =
      Real.log (Real.pi ^ 2 / 6) at h
  rw [Finset.mul_sum]
  simp_rw [two_mul_squareCorrectionTerm_eq]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum]
  linarith only [h]

/-- For a real cutoff x, let the square cutoff contain positive m with
m^2 <= floor x. Add the logarithmic zeta series outside this cutoff to twice the finite
Mangoldt sum divided by x log x. This is the exact loss of the square correction from
log(pi^2/6); its explicit bound supplies the reciprocal estimate in Theorem 1.5. -/
noncomputable def squareMangoldtCorrectionLoss (x : ℝ) : ℝ :=
  let s := (Finset.Ioc 0 ⌊x⌋₊).filter (fun m ↦ m ^ 2 ≤ ⌊x⌋₊)
  (∑' m : { m : ℕ // m ∉ s }, mangoldtLogSquareTerm m) +
    2 * (∑ m ∈ s, ArithmeticFunction.vonMangoldt m) / (x * Real.log x)

/-- For every real x, twice the square correction equals log(pi^2/6) minus
the square Mangoldt correction loss. Specialize the finite-set series identity to the
square cutoff; this connects the Euler product constant to the lower L-value comparison. -/
theorem two_mul_squareMangoldtCorrection_eq (x : ℝ) :
    2 *
        ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊ with m ^ 2 ≤ ⌊x⌋₊,
          ArithmeticFunction.vonMangoldt m *
            (1 / ((m : ℝ) ^ 2 * Real.log ((m : ℝ) ^ 2)) - 1 / (x * Real.log x)) =
      Real.log (Real.pi ^ 2 / 6) - squareMangoldtCorrectionLoss x := by
  rw [two_mul_squareCorrection_sum_eq]
  dsimp only [squareMangoldtCorrectionLoss]
  ring

/-- At an index at least two, the logarithmic square term is nonnegative and at most
the reciprocal square. Divide the Mangoldt bound by the positive logarithm; this is the
pointwise majorant used for the odd part of the truncated series. -/
theorem mangoldtLogSquareTerm_bounds {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ mangoldtLogSquareTerm n ∧ mangoldtLogSquareTerm n ≤ 1 / (n : ℝ) ^ 2 := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le (by decide : 1 < 2) hn
  have hlog := Real.log_pos hn1
  constructor
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (mul_nonneg (sq_nonneg _) hlog.le)
  · rw [mangoldtLogSquareTerm, mul_comm ((n : ℝ) ^ 2), ← div_div]
    exact
      div_le_div_of_nonneg_right ((div_le_one hlog).mpr ArithmeticFunction.vonMangoldt_le_log)
        (sq_nonneg _)

/-- An even index with nonzero Mangoldt weight is a positive power of two. Write the
index as a prime power and use divisibility by two to identify its prime base. This
separates the even contribution from the odd reciprocal-square majorant. -/
theorem exists_two_pow_of_even_vonMangoldt_ne_zero {n : ℕ} (hn : Even n)
    (h : ArithmeticFunction.vonMangoldt n ≠ 0) : ∃ k : ℕ, 0 < k ∧ n = 2 ^ k := by
  obtain ⟨p, k, hp, hk, rfl⟩ := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h
  have hpN := Nat.prime_iff.mpr hp
  have hd : 2 ∣ p ^ k := even_iff_two_dvd.mp hn
  have heq : 2 = p :=
    (Nat.prime_dvd_prime_iff_eq Nat.prime_two hpN).mp (Nat.prime_two.dvd_of_dvd_pow hd)
  exact ⟨k, hk, by rw [← heq]⟩

/-- At a positive power of two the square term is exactly 1/(k 4^k). Cancel the
prime logarithm using the Mangoldt prime-power identity and log(2^k)=k log 2.
The resulting formula permits a geometric estimate of the even tail. -/
theorem mangoldtLogSquareTerm_two_pow (k : ℕ) (hk : 0 < k) :
    mangoldtLogSquareTerm (2 ^ k) = 1 / ((k : ℝ) * (2 : ℝ) ^ (2 * k)) := by
  rw [mangoldtLogSquareTerm, ArithmeticFunction.vonMangoldt_apply_pow (Nat.ne_of_gt hk),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, Nat.cast_pow, Nat.cast_ofNat,
    Real.log_pow, ← pow_mul, mul_comm k (2 : ℕ)]
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  have hl0 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num only))
  field_simp [hk0, hl0]

/-- For a real center greater than one, its reciprocal square is bounded by a
telescoping difference with endpoints one unit away. Clear the positive denominators.
This avoids doubling the leading constant when estimating the odd-index tail. -/
private theorem reciprocal_square_le_half_difference (a : ℝ) (ha : 1 < a) :
    1 / a ^ 2 ≤ 1 / (2 * (a - 1)) - 1 / (2 * (a + 1)) := by
  have hm : 0 < a - 1 := sub_pos.mpr ha
  have hp : 0 < a + 1 := lt_trans (by norm_num only : (0 : ℝ) < 2) (by linarith only [ha])
  have hz : a ≠ 0 := ne_of_gt (lt_trans (by norm_num only : (0 : ℝ) < 1) ha)
  field_simp [ne_of_gt hm, ne_of_gt hp, hz]
  nlinarith only [sq_nonneg a]

/-- For a real starting point a > 1, the reciprocal-square series along steps of
two is at most 1/(2(a-1)). Bound each term by a telescoping difference and discard
the nonnegative final endpoint in each finite sum, then pass to the infinite sum. -/
theorem tsum_reciprocal_square_step_two_le (a : ℝ) (ha : 1 < a) :
    (∑' k : ℕ, 1 / (a + 2 * k) ^ 2) ≤ 1 / (2 * (a - 1)) := by
  apply Real.tsum_le_of_sum_range_le (fun k ↦ div_nonneg (by norm_num only) (sq_nonneg _))
  intro n
  have h :=
    Finset.sum_le_sum
      (fun k (_ : k ∈ Finset.range n) ↦
        reciprocal_square_le_half_difference (a + 2 * k)
          (by nlinarith only [ha, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]))
  have heq :
    (∑ k ∈ Finset.range n, (1 / (2 * (a + 2 * k - 1)) - 1 / (2 * (a + 2 * k + 1)))) =
      1 / (2 * (a - 1)) - 1 / (2 * (a + 2 * n - 1)) := by
    convert Finset.sum_range_sub' (fun k : ℕ ↦ 1 / (2 * (a + 2 * k - 1))) n using 1
    · apply Finset.sum_congr rfl
      intro k _
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    · simp only [Nat.cast_zero, mul_zero, add_zero]
  rw [heq] at h
  exact
    h.trans
      (sub_le_self _
        (div_nonneg (by norm_num only) (by nlinarith only [ha, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])))

/-- The step-two reciprocal-square series is summable for a > 1. Its terms are
dominated by the summable reciprocal squares at k+1, since a+2k >= k+1. This
justifies comparison with the odd Mangoldt tail after reindexing. -/
theorem summable_reciprocal_square_step_two (a : ℝ) (ha : 1 < a) :
    Summable (fun k : ℕ ↦ 1 / (a + 2 * k) ^ 2) := by
  apply
    Summable.of_nonneg_of_le (fun k ↦ div_nonneg (by norm_num only) (sq_nonneg _)) (fun k ↦ ?_)
      ((Real.summable_one_div_nat_pow.mpr (by decide : 1 < (2 : ℕ))).comp_injective
        (show Function.Injective (fun k : ℕ ↦ k + 1) from fun _ _ h ↦ Nat.add_right_cancel h))
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  apply one_div_le_one_div_of_le
  · exact sq_pos_of_pos (by linarith only [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  · nlinarith only [ha, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- Above a natural cutoff N >= 2, the Mangoldt square terms at odd indices sum
to at most 1/(2(N-1)). Reindex an odd n by n/2-N/2, apply the reciprocal-square
majorant, and use the step-two telescoping bound. The floor in N/2 is retained
in the starting point, so the estimate applies to both parities of N. -/
theorem tsum_odd_mangoldtLogSquareTerm_tail_le (N : ℕ) (hN : 2 ≤ N) :
    (∑' n : { n : ℕ // N < n ∧ Odd n }, mangoldtLogSquareTerm n) ≤ 1 / (2 * ((N : ℝ) - 1)) := by
  let e : { n : ℕ // N < n ∧ Odd n } → ℕ := fun n ↦ n.val / 2 - N / 2
  have heq (n : { n : ℕ // N < n ∧ Odd n }) : n.val = 2 * (e n + N / 2) + 1 := by
    have hdiv := Nat.div_le_div_right (Nat.le_of_lt n.property.1) (c := 2)
    have hsub := Nat.sub_add_cancel hdiv
    have hmod := Nat.odd_iff.mp n.property.2
    have hd := Nat.div_add_mod n.val 2
    dsimp only [e]
    nlinarith only [hsub, hmod, hd]
  have hinj : Function.Injective e := by
    intro n m h
    apply Subtype.ext
    have hn := heq n
    have hm := heq m
    rw [h] at hn
    exact hn.trans hm.symm
  have ha : 1 < (2 * (N / 2) + 1 : ℕ) := by
    have hd : 1 ≤ N / 2 := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr hN
    nlinarith only [hd]
  have haR : 1 < (2 * ((N / 2 : ℕ) : ℝ) + 1) := by exact_mod_cast ha
  have h :=
    Summable.tsum_le_tsum_of_inj e hinj (fun k _ ↦ div_nonneg (by norm_num only) (sq_nonneg _))
      (fun n ↦ ?_) (summable_mangoldtLogSquareTerm.subtype _)
      (summable_reciprocal_square_step_two (2 * ((N / 2 : ℕ) : ℝ) + 1) haR)
  · apply h.trans
    apply (tsum_reciprocal_square_step_two_le (2 * ((N / 2 : ℕ) : ℝ) + 1) haR).trans
    apply one_div_le_one_div_of_le
    · have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
      linarith only [hNR]
    · have hd := Nat.div_add_mod N 2
      have hm := Nat.mod_lt N (by decide : 0 < 2)
      have hle : N ≤ 2 * (N / 2) + 1 := by nlinarith only [hd, hm]
      have hleR : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hle
      linarith only [hleR]
  · have hn : 2 ≤ n.val := hN.trans (Nat.le_of_lt n.property.1)
    apply (mangoldtLogSquareTerm_bounds hn).2.trans_eq
    rw [heq n]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    congr 2
    ring

/-- Beyond the exponent K, the Mangoldt square terms at powers of two sum to at
most 4/(3*4^(K+1)). Bound each term by its reciprocal square and sum the resulting
geometric series of ratio 1/4. This controls the even part of the square loss. -/
theorem tsum_mangoldtLogSquareTerm_two_pow_tail_le (K : ℕ) :
    (∑' k : ℕ, mangoldtLogSquareTerm (2 ^ (K + k + 1))) ≤ 4 / (3 * (2 : ℝ) ^ (2 * (K + 1))) := by
  have heq (k : ℕ) :
    1 / ((2 ^ (K + k + 1) : ℕ) : ℝ) ^ 2 = (1 / (2 : ℝ) ^ (2 * (K + 1))) * (1 / 4 : ℝ) ^ k := by
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [← pow_mul]
    have he : (K + k + 1) * 2 = 2 * (K + 1) + 2 * k := by ring
    have hp : (2 : ℝ) ^ (2 * k) = 4 ^ k := by
      rw [pow_mul]
      norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num only]
    rw [he, pow_add, hp]
    simp only [one_div, mul_inv_rev, inv_pow]
    ring
  have hg : Summable (fun k : ℕ ↦ (1 / (2 : ℝ) ^ (2 * (K + 1))) * (1 / 4 : ℝ) ^ k) :=
    (summable_geometric_of_abs_lt_one (by norm_num only : |(1 / 4 : ℝ)| < 1)).mul_left _
  have hf : Summable (fun k : ℕ ↦ mangoldtLogSquareTerm (2 ^ (K + k + 1))) :=
    summable_mangoldtLogSquareTerm.comp_injective
      (by
        intro a b h
        have he := Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) h
        have he' := Nat.add_right_cancel he
        exact Nat.add_left_cancel he')
  have h := hf.tsum_le_tsum (fun k ↦ ?_) hg
  · rw [tsum_mul_left, tsum_geometric_of_abs_lt_one (by norm_num only : |(1 / 4 : ℝ)| < 1)] at h
    convert h using 1
    ring
  · rw [← heq]
    apply (mangoldtLogSquareTerm_bounds ?_).2
    exact Nat.le_self_pow (Nat.ne_zero_of_lt (Nat.lt_add_one (K + k))) 2

/-- Above a positive natural cutoff N, the even Mangoldt square tail is at most
4/(3N^2). Nonzero terms occur only at powers of two; reindex them above log_2 N
and apply the geometric tail estimate. The first omitted power exceeds N, so
its reciprocal square is bounded by N^(-2). -/
theorem tsum_even_mangoldtLogSquareTerm_tail_le (N : ℕ) (hN : 0 < N) :
    (∑' n : { n : ℕ // N < n ∧ Even n }, mangoldtLogSquareTerm n) ≤ 4 / (3 * (N : ℝ) ^ 2) := by
  let K := Nat.log 2 N
  let g : ℕ → ℝ := fun k ↦ mangoldtLogSquareTerm (2 ^ (K + k + 1))
  have hpow (k : ℕ) : N < 2 ^ (K + k + 1) := by
    apply (Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) N).trans_le
    apply Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
    dsimp only [K]
    exact Nat.add_le_add_right (Nat.le_add_right _ _) 1
  let i : Function.support g → { n : ℕ // N < n ∧ Even n } := fun k ↦
    ⟨2 ^ (K + k.val + 1), hpow k.val,
      Even.pow_of_ne_zero (by decide : Even (2 : ℕ)) (Nat.ne_zero_of_lt (Nat.lt_add_one _))⟩
  have hi : Function.Injective i := by
    intro a b h
    apply Subtype.ext
    have hv := congrArg Subtype.val h
    have he := Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) hv
    exact Nat.add_left_cancel (Nat.add_right_cancel he)
  have hs :
    Function.support (fun n : { n : ℕ // N < n ∧ Even n } ↦ mangoldtLogSquareTerm n) ⊆
      Set.range i := by
    intro n hn
    change mangoldtLogSquareTerm n.val ≠ 0 at hn
    have hΛ : ArithmeticFunction.vonMangoldt n.val ≠ 0 := by
      intro hz
      apply hn
      rw [mangoldtLogSquareTerm, hz, zero_div]
    obtain ⟨j, hj, hnj⟩ := exists_two_pow_of_even_vonMangoldt_ne_zero n.property.2 hΛ
    have hKj : K < j := Nat.log_lt_of_lt_pow (Nat.ne_of_gt hN) (hnj ▸ n.property.1)
    let k := j - (K + 1)
    have hek : K + k + 1 = j := by
      have h := Nat.sub_add_cancel (Nat.succ_le_of_lt hKj)
      dsimp only [k]
      nlinarith only [h]
    have hg : g k ≠ 0 := by
      change mangoldtLogSquareTerm (2 ^ (K + k + 1)) ≠ 0
      rw [hek, ← hnj]
      exact hn
    refine ⟨⟨k, hg⟩, ?_⟩
    apply Subtype.ext
    change 2 ^ (K + k + 1) = n.val
    rw [hek, ← hnj]
  have heq := tsum_eq_tsum_of_ne_zero_bij i hi hs (fun _ ↦ rfl)
  change
    (∑' n : { n : ℕ // N < n ∧ Even n }, mangoldtLogSquareTerm n) =
      ∑' k : ℕ, mangoldtLogSquareTerm (2 ^ (K + k + 1)) at heq
  rw [heq]
  apply (tsum_mangoldtLogSquareTerm_two_pow_tail_le K).trans
  have hnR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpR : (N : ℝ) < (2 : ℝ) ^ (K + 1) := by exact_mod_cast hpow 0
  rw [mul_comm 2 (K + 1), pow_mul]
  apply div_le_div_of_nonneg_left (by norm_num only)
  · exact mul_pos (by norm_num only) (sq_pos_of_pos hnR)
  · nlinarith only [hpR, hnR, sq_nonneg ((2 : ℝ) ^ (K + 1) - (N : ℝ))]

/-- For N >= 2, the full logarithmic Mangoldt square tail is at most
1/(2(N-1))+4/(3N^2). Split the tail into odd and even indices using summable
indicator functions, then combine the step-two and prime-power estimates.
This gives the infinite-series part of the square correction loss. -/
theorem tsum_mangoldtLogSquareTerm_tail_le (N : ℕ) (hN : 2 ≤ N) :
    (∑' n : { n : ℕ // N < n }, mangoldtLogSquareTerm n) ≤
      1 / (2 * ((N : ℝ) - 1)) + 4 / (3 * (N : ℝ) ^ 2) := by
  have he := summable_mangoldtLogSquareTerm.indicator {n : ℕ | N < n ∧ Even n}
  have ho := summable_mangoldtLogSquareTerm.indicator {n : ℕ | N < n ∧ Odd n}
  have heq :
    (∑' n : { n : ℕ // N < n }, mangoldtLogSquareTerm n) =
      (∑' n : { n : ℕ // N < n ∧ Odd n }, mangoldtLogSquareTerm n) +
        (∑' n : { n : ℕ // N < n ∧ Even n }, mangoldtLogSquareTerm n) := by
    have hN' := tsum_subtype {n : ℕ | N < n} mangoldtLogSquareTerm
    have hO' := tsum_subtype {n : ℕ | N < n ∧ Odd n} mangoldtLogSquareTerm
    have hE' := tsum_subtype {n : ℕ | N < n ∧ Even n} mangoldtLogSquareTerm
    change
      (∑' n : { n : ℕ // N < n }, mangoldtLogSquareTerm n) =
        ∑' n : ℕ, {n : ℕ | N < n}.indicator mangoldtLogSquareTerm n at hN'
    change
      (∑' n : { n : ℕ // N < n ∧ Odd n }, mangoldtLogSquareTerm n) =
        ∑' n : ℕ, {n : ℕ | N < n ∧ Odd n}.indicator mangoldtLogSquareTerm n at hO'
    change
      (∑' n : { n : ℕ // N < n ∧ Even n }, mangoldtLogSquareTerm n) =
        ∑' n : ℕ, {n : ℕ | N < n ∧ Even n}.indicator mangoldtLogSquareTerm n at hE'
    rw [hN', hO', hE', ← ho.tsum_add he]
    apply tsum_congr
    intro n
    by_cases hn : N < n
    · rcases Nat.even_or_odd n with hEven | hOdd
      · have hNot : ¬Odd n := fun h ↦ by
          have hmod := Nat.odd_iff.mp h
          have hemod := (even_iff_two_dvd.mp hEven)
          have hz := Nat.mod_eq_zero_of_dvd hemod
          exact (by decide : (0 : ℕ) ≠ 1) (hz.symm.trans hmod)
        simp only [Set.indicator, Set.mem_ofPred_eq, hn, hEven, hNot, and_self, and_false, ite_true,
          ite_false, zero_add]
      · have hNot : ¬Even n := fun h ↦ by
          have hmod := Nat.odd_iff.mp hOdd
          have hz := Nat.mod_eq_zero_of_dvd (even_iff_two_dvd.mp h)
          exact (by decide : (0 : ℕ) ≠ 1) (hz.symm.trans hmod)
        simp only [Set.indicator, Set.mem_ofPred_eq, hn, hOdd, hNot, and_self, and_false, ite_true,
          ite_false, add_zero]
    · simp only [Set.indicator, Set.mem_ofPred_eq, hn, false_and, ite_false, add_zero]
  rw [heq]
  exact
    add_le_add (tsum_odd_mangoldtLogSquareTerm_tail_le N hN)
      (tsum_even_mangoldtLogSquareTerm_tail_le N (lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hN))

/-- For an even index with nonzero Mangoldt weight, its binary logarithm is its
positive prime-power exponent and its weight is log 2. Apply the support
classification and the exact logarithm of a power; these data reindex finite
even sums without counting indices whose Mangoldt weight vanishes. -/
private theorem even_vonMangoldt_support_data (n : ℕ) (hn : Even n)
    (h : ArithmeticFunction.vonMangoldt n ≠ 0) :
    n = 2 ^ (Nat.log 2 n) ∧ 0 < Nat.log 2 n ∧ ArithmeticFunction.vonMangoldt n = Real.log 2 := by
  obtain ⟨k, hk, rfl⟩ := exists_two_pow_of_even_vonMangoldt_ne_zero hn h
  rw [Nat.log_pow (by decide : 1 < (2 : ℕ)),
    ArithmeticFunction.vonMangoldt_apply_pow (Nat.ne_of_gt hk),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, Nat.cast_ofNat]
  exact ⟨rfl, hk, rfl⟩

/-- The even Mangoldt weights up to a positive N sum to at most log N. Reindex
nonzero weights by their binary prime-power exponents, each with weight log 2,
and use 2^(floor(log_2 N)) <= N. This bounds the finite even correction. -/
theorem sum_even_vonMangoldt_le_log (N : ℕ) (hN : 0 < N) :
    (∑ n ∈ Finset.Ioc 0 N with Even n, ArithmeticFunction.vonMangoldt n) ≤ Real.log N := by
  classical
  let s := (Finset.Ioc 0 N).filter Even
  let t := s.filter (fun n ↦ ArithmeticFunction.vonMangoldt n ≠ 0)
  have hm (n : ℕ) (hn : n ∈ t) :
    n = 2 ^ (Nat.log 2 n) ∧ 0 < Nat.log 2 n ∧ ArithmeticFunction.vonMangoldt n = Real.log 2 :=
    even_vonMangoldt_support_data n (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
      (Finset.mem_filter.mp hn).2
  have hinj : Set.InjOn (Nat.log 2) (t : Set ℕ) := by
    intro n hn m hm' he
    rw [(hm n hn).1, (hm m hm').1, he]
  have hsubset : t.image (Nat.log 2) ⊆ Finset.Ioc 0 (Nat.log 2 N) := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    apply Finset.mem_Ioc.mpr
    exact
      ⟨(hm n hn).2.1,
        Nat.log_mono_right
          (Finset.mem_Ioc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1).2⟩
  have h :=
    Finset.sum_le_sum_of_injOn (Nat.log 2) hinj hsubset (fun n hn ↦ (hm n hn).2.2.le)
      (fun _ _ _ ↦ Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 2))
  have heq :
    (∑ n ∈ t, ArithmeticFunction.vonMangoldt n) = ∑ n ∈ s, ArithmeticFunction.vonMangoldt n :=
    Finset.sum_filter_ne_zero s
  rw [heq, Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul] at h
  have hlog : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
    have hbase : 0 < (2 : ℝ) ^ (Nat.log 2 N) := pow_pos (by norm_num only) _
    have hpow : (2 : ℝ) ^ (Nat.log 2 N) ≤ N := by
      exact_mod_cast Nat.pow_log_le_self 2 (Nat.ne_of_gt hN)
    have h := Real.log_le_log hbase hpow
    rw [Real.log_pow] at h
    exact h
  exact h.trans hlog

/-- The odd Mangoldt weights up to a positive N sum to at most (N/2+1) log N.
Map odd indices injectively to their halves, bound their number by floor(N/2)+1,
and use Lambda(n) <= log n <= log N. This supplies the finite odd contribution
to the square correction loss. -/
theorem sum_odd_vonMangoldt_le_log (N : ℕ) (hN : 0 < N) :
    (∑ n ∈ Finset.Ioc 0 N with Odd n, ArithmeticFunction.vonMangoldt n) ≤
      ((N : ℝ) / 2 + 1) * Real.log N := by
  classical
  let s := (Finset.Ioc 0 N).filter Odd
  have hinj : Set.InjOn (fun n : ℕ ↦ n / 2) (s : Set ℕ) := by
    intro n hn m hm h
    have hnmod := Nat.odd_iff.mp (Finset.mem_filter.mp hn).2
    have hmmod := Nat.odd_iff.mp (Finset.mem_filter.mp hm).2
    have hn' := Nat.div_add_mod n 2
    have hm' := Nat.div_add_mod m 2
    nlinarith only [hnmod, hmmod, hn', hm', h]
  have hmap : Set.MapsTo (fun n : ℕ ↦ n / 2) (s : Set ℕ) (Finset.range (N / 2 + 1) : Set ℕ) := by
    intro n hn
    apply Finset.mem_range.mpr
    apply Nat.lt_add_one_of_le
    exact Nat.div_le_div_right (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2
  have hc := Finset.card_le_card_of_injOn (fun n : ℕ ↦ n / 2) hmap hinj
  rw [Finset.card_range] at hc
  have h :=
    Finset.sum_le_card_nsmul s ArithmeticFunction.vonMangoldt (Real.log N)
      (fun n hn ↦
        ArithmeticFunction.vonMangoldt_le_log.trans
          (Real.log_le_log (by exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1)
            (by exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2)))
  rw [nsmul_eq_mul] at h
  have hcR : (s.card : ℝ) ≤ (N : ℝ) / 2 + 1 := by
    have hc' : (s.card : ℝ) ≤ (N / 2 : ℕ) + 1 := by exact_mod_cast hc
    have hd := Nat.mul_div_le N 2
    have hdR : 2 * ((N / 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast hd
    linarith only [hc', hdR]
  have hlog := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN)
  exact h.trans (mul_le_mul_of_nonneg_right hcR hlog)

/-- For a positive N, the Mangoldt sum up to N is at most (N/2+2) log N.
Split indices into even and odd parts and combine their respective bounds.
The estimate is used with N=floor(sqrt x) in the finite square correction. -/
theorem sum_vonMangoldt_le_half_cutoff_log (N : ℕ) (hN : 0 < N) :
    (∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n) ≤ ((N : ℝ) / 2 + 2) * Real.log N := by
  have h :=
    Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 N) Even ArithmeticFunction.vonMangoldt
  simp only [Nat.not_even_iff_odd] at h
  have he := sum_even_vonMangoldt_le_log N hN
  have ho := sum_odd_vonMangoldt_le_log N hN
  nlinarith only [h, he, ho]

/-- For x >= 1, the positive square cutoff equals the interval up to floor(sqrt x).
Use the floor inequalities and m <= sqrt x iff m^2 <= x; sqrt x <= x makes the
extra upper cutoff redundant. This puts the finite and infinite loss terms
at the same natural endpoint. -/
theorem squareMangoldtCutoff_eq (x : ℝ) (hx : 1 ≤ x) :
    (Finset.Ioc 0 ⌊x⌋₊).filter (fun m ↦ m ^ 2 ≤ ⌊x⌋₊) = Finset.Ioc 0 ⌊Real.sqrt x⌋₊ := by
  have hx0 : 0 ≤ x := le_trans (by norm_num only) hx
  have hsx : Real.sqrt x ≤ x := by
    have hs := Real.sq_sqrt hx0
    have hsp := Real.sqrt_nonneg x
    nlinarith only [hs, hsp, hx]
  apply Finset.ext
  intro m
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · intro h
    refine ⟨h.1.1, (Nat.le_floor_iff (Real.sqrt_nonneg x)).mpr ?_⟩
    apply Real.le_sqrt_of_sq_le
    have hcast : (m : ℝ) ^ 2 ≤ ⌊x⌋₊ := by exact_mod_cast h.2
    exact hcast.trans (Nat.floor_le hx0)
  · intro h
    have hm : (m : ℝ) ≤ Real.sqrt x := (Nat.le_floor_iff (Real.sqrt_nonneg x)).mp h.2
    refine ⟨⟨h.1, (Nat.le_floor_iff hx0).mpr (hm.trans hsx)⟩, ?_⟩
    apply (Nat.le_floor_iff hx0).mpr
    simp only [Nat.cast_pow]
    exact (Real.le_sqrt (Nat.cast_nonneg m) hx0).mp hm

/-- The complementary series of the positive interval up to N equals the tail
above N. The only additional index is zero, whose Mangoldt term vanishes.
Rewrite both subtype series as indicator sums and compare their terms. -/
theorem tsum_compl_Ioc_mangoldtLogSquareTerm (N : ℕ) :
    (∑' n : { n : ℕ // n ∉ Finset.Ioc 0 N }, mangoldtLogSquareTerm n) =
      ∑' n : { n : ℕ // N < n }, mangoldtLogSquareTerm n := by
  have hc := tsum_subtype {n : ℕ | n ∉ Finset.Ioc 0 N} mangoldtLogSquareTerm
  have ht := tsum_subtype {n : ℕ | N < n} mangoldtLogSquareTerm
  change
    (∑' n : { n : ℕ // n ∉ Finset.Ioc 0 N }, mangoldtLogSquareTerm n) =
      ∑' n : ℕ, {n : ℕ | n ∉ Finset.Ioc 0 N}.indicator mangoldtLogSquareTerm n at hc
  change
    (∑' n : { n : ℕ // N < n }, mangoldtLogSquareTerm n) =
      ∑' n : ℕ, {n : ℕ | N < n}.indicator mangoldtLogSquareTerm n at ht
  rw [hc, ht]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [Set.indicator, mangoldtLogSquareTerm, ArithmeticFunction.map_zero, Nat.cast_zero,
      zero_div, ite_self]
  · have hn0 := Nat.pos_of_ne_zero hn
    have hiff : n ∉ Finset.Ioc 0 N ↔ N < n := by simp only [Finset.mem_Ioc, hn0, true_and, not_le]
    by_cases h : N < n
    · simp only [Set.indicator, Set.mem_ofPred_eq, hiff, h, ite_true]
    · simp only [Set.indicator, Set.mem_ofPred_eq, hiff, h, ite_false]

/-- If 10 <= n <= y <= n+1, the odd tail, even tail, and finite correction
majorants together are at most 3/(2y). Bound the three summands by constant
multiples of 1/y using positive denominators and n >= 10. This preserves the
square-loss constant needed by the reciprocal L-value estimate. -/
private theorem square_loss_majorant_le (n y : ℝ) (hn : 10 ≤ n) (hny : n ≤ y) (hyn : y ≤ n + 1) :
    1 / (2 * (n - 1)) + 4 / (3 * n ^ 2) + (y + 4) / (2 * y ^ 2) ≤ 3 / (2 * y) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 10) hn
  have hy0 : 0 < y := hn0.trans_le hny
  have hnm : 0 < n - 1 := by linarith only [hn]
  have ho : 1 / (2 * (n - 1)) ≤ 11 / (18 * y) := by
    apply
      (div_le_div_iff₀ (by linarith only [hnm] : 0 < 2 * (n - 1))
          (by linarith only [hy0] : 0 < 18 * y)).mpr
    nlinarith only [hn, hyn]
  have he : 4 / (3 * n ^ 2) ≤ 11 / (75 * y) := by
    apply
      (div_le_div_iff₀ (mul_pos (by norm_num only) (sq_pos_of_pos hn0))
          (by linarith only [hy0] : 0 < 75 * y)).mpr
    nlinarith only [hn, hyn, mul_nonneg hn0.le (sub_nonneg.mpr hn)]
  have hf : (y + 4) / (2 * y ^ 2) ≤ 7 / (10 * y) := by
    apply
      (div_le_div_iff₀ (mul_pos (by norm_num only) (sq_pos_of_pos hy0))
          (by linarith only [hy0] : 0 < 10 * y)).mpr
    nlinarith only [hn, hny, mul_nonneg hy0.le (sub_nonneg.mpr (hn.trans hny))]
  have hc : 11 / (18 * y) + 11 / (75 * y) + 7 / (10 * y) ≤ 3 / (2 * y) := by
    field_simp [ne_of_gt hy0]
    norm_num only
  linarith only [ho, he, hf, hc]

/-- For x >= 100, the finite part of the square correction loss is at most
(sqrt x+4)/(2x). Apply the parity-based Mangoldt sum bound at floor(sqrt x),
then use log(floor(sqrt x)) <= log x/2. The positive denominator x log x
allows comparison with the infinite-tail estimate. -/
theorem finite_squareMangoldtCorrectionLoss_le (x : ℝ) (hx : 100 ≤ x) :
    2 * (∑ n ∈ Finset.Ioc 0 ⌊Real.sqrt x⌋₊, ArithmeticFunction.vonMangoldt n) / (x * Real.log x) ≤
      (Real.sqrt x + 4) / (2 * x) := by
  let N := ⌊Real.sqrt x⌋₊
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 100) hx
  have hs10 : (10 : ℝ) ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by nlinarith only [hx])
  have hN10 : 10 ≤ N := (Nat.le_floor_iff (Real.sqrt_nonneg x)).mpr hs10
  have hN0 : 0 < N := lt_of_lt_of_le (by decide : 0 < (10 : ℕ)) hN10
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hNs : (N : ℝ) ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg x)
  have hl : 0 < Real.log x := Real.log_pos (by linarith only [hx])
  have hlog : Real.log (N : ℝ) ≤ Real.log x / 2 := by
    have h := Real.log_le_log hNR hNs
    rw [Real.log_sqrt hx0.le] at h
    exact h
  have hs := sum_vonMangoldt_le_half_cutoff_log N hN0
  have hNs' : (N : ℝ) / 2 + 2 ≤ Real.sqrt x / 2 + 2 := by linarith only [hNs]
  have hb :=
    hs.trans
      ((mul_le_mul_of_nonneg_left hlog (by linarith only [hNR] : 0 ≤ (N : ℝ) / 2 + 2)).trans
        (mul_le_mul_of_nonneg_right hNs' (div_nonneg hl.le (by norm_num only))))
  have h :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num only : (0 : ℝ) ≤ 2))
      (mul_nonneg hx0.le hl.le)
  convert h using 1
  field_simp [ne_of_gt hx0, ne_of_gt hl]
  ring

/-- For x >= 100, the square Mangoldt correction loss is at most 3/(2 sqrt x).
Identify the square cutoff with floor(sqrt x), combine the odd and power-of-two
tails with the finite correction, and apply the rational majorant at this
floor. This supplies the square-term error in the reciprocal L-value bound. -/
theorem squareMangoldtCorrectionLoss_le (x : ℝ) (hx : 100 ≤ x) :
    squareMangoldtCorrectionLoss x ≤ 3 / (2 * Real.sqrt x) := by
  have hx1 : 1 ≤ x := le_trans (by norm_num only) hx
  let N := ⌊Real.sqrt x⌋₊
  have hs10 : (10 : ℝ) ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by nlinarith only [hx])
  have hN10 : 10 ≤ N := (Nat.le_floor_iff (Real.sqrt_nonneg x)).mpr hs10
  have hN2 : 2 ≤ N := le_trans (by decide) hN10
  have hN10R : (10 : ℝ) ≤ N := by exact_mod_cast hN10
  have hNs : (N : ℝ) ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg x)
  have hsN : Real.sqrt x ≤ (N : ℝ) + 1 := (Nat.lt_floor_add_one (Real.sqrt x)).le
  rw [squareMangoldtCorrectionLoss, squareMangoldtCutoff_eq x hx1,
    tsum_compl_Ioc_mangoldtLogSquareTerm]
  have ht := tsum_mangoldtLogSquareTerm_tail_le N hN2
  have hf := finite_squareMangoldtCorrectionLoss_le x hx
  have h := add_le_add ht hf
  have hs := Real.sq_sqrt (le_trans (by norm_num only : (0 : ℝ) ≤ 100) hx)
  have hm := square_loss_majorant_le (N : ℝ) (Real.sqrt x) hN10R hNs hsN
  rw [hs] at hm
  exact h.trans hm

end PseudoPrime.AnalyticNumberTheory.Arithmetic
