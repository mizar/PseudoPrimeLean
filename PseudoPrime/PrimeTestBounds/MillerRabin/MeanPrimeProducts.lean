/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.PrimeProductSelectedCounting
public import PseudoPrime.NumberTheory.ProductFermatKernel
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ThetaPrimeCountBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsPrimeCount

/-! # Average-logarithm prime-product criterion

Transfer the selected prime-product count to a local Fermat kernel. The criterion keeps the
mean-logarithm and counting budgets explicit for subsequent analytic estimates.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Let `p ^ a` divide an odd `n > 1`, with `p` an odd prime and `a > 0`.
If the prime logarithms up to `B` meet the displayed average and counting inequalities, and
`0 ≤ τ ≤ log (p ^ a)`, a prime at most `B` rejects `n`. Selected products inject into
the local Fermat kernel, whose cardinality is the displayed gcd. This supplies the witness
interface for average-logarithm prime-product budgets. -/
theorem exists_prime_of_weight_budget {n p a : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (B k : ℕ) (τ δ : ℝ) (hk : 1 ≤ k) (hτ : 0 ≤ τ)
    (hsize : τ ≤ Real.log (p ^ a : ℕ))
    (havg :
      (Nat.choose (B.primesLE.card - 1) (k - 1) : ℝ) * (∑ r ∈ B.primesLE, Real.log r) ≤
        (τ - δ) * Nat.choose B.primesLE.card k)
    (hcount : τ * (p - 1).gcd (n - 1) < δ * Nat.choose B.primesLE.card k) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  let H := (powMonoidHom (n - 1) : (ZMod (p ^ a))ˣ →* (ZMod (p ^ a))ˣ).ker
  have hc : τ * Nat.card H < δ * Nat.choose B.primesLE.card k := by
    dsimp only [H]
    rw [NumberTheory.card_local_fermat_kernel_prime_pow hn hp hp2 ha hdiv]
    exact hcount
  obtain ⟨r, hr, hrout⟩ :=
    NumberTheory.exists_prime_outside_of_weight H B.primesLE k τ δ hk hτ hsize
      (fun r hr ↦ (Nat.mem_primesLE.mp hr).2) havg hc
  refine ⟨r, (Nat.mem_primesLE.mp hr).2, (Nat.mem_primesLE.mp hr).1, ?_⟩
  intro hpass
  exact hrout (PrimeTest.strongMR_local_divisorKernel hn ho hdiv hpass)

/-- Under the local prime-power hypotheses, a nonempty prime supply whose mean logarithm
meets the displayed bound yields a rejecting prime when the count exceeds the kernel budget.
The binomial identity converts the mean bound to the selected-product criterion. This is
the input form for explicit prime-count and Chebyshev estimates. -/
theorem exists_prime_of_mean_budget {n p a : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (B k : ℕ) (τ δ : ℝ) (hk : 1 ≤ k)
    (hs : 1 ≤ B.primesLE.card) (hτ : 0 ≤ τ) (hsize : τ ≤ Real.log (p ^ a : ℕ))
    (hmean : (k : ℝ) * (∑ r ∈ B.primesLE, Real.log r) ≤ (τ - δ) * B.primesLE.card)
    (hcount : τ * (p - 1).gcd (n - 1) < δ * Nat.choose B.primesLE.card k) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_of_weight_budget hn ho hp hp2 ha hdiv B k τ δ hk hτ hsize
      (Combinatorics.choose_weight_of_mean B.primesLE.card k _ τ δ hk hs hmean) hcount

/-- Let an odd `n > 1` factor as `m * q`, where `m > 1` and `q` is an odd prime.
If `0 ≤ τ ≤ log q`, the stated mean-logarithm and count bounds give an MR-rejecting
prime at most `B`. Bound the local kernel by `m - 1` and apply the mean criterion.
This is the large-cofactor interface for explicit average-logarithm budgets. -/
theorem large_cofactor_of_mean_budget {n m q : ℕ} (hn : 1 < n) (ho : Odd n) (hm : 1 < m)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = m * q) (B k : ℕ) (τ δ : ℝ) (hk : 1 ≤ k)
    (hs : 1 ≤ B.primesLE.card) (hτ : 0 ≤ τ) (hsize : τ ≤ Real.log q)
    (hmean : (k : ℝ) * (∑ r ∈ B.primesLE, Real.log r) ≤ (τ - δ) * B.primesLE.card)
    (hcount : τ * m < δ * Nat.choose B.primesLE.card k) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hd : q ^ 1 ∣ n := by
    rw [pow_one, hprod]
    exact dvd_mul_left q m
  have hgcd : (q - 1).gcd (n - 1) ≤ m - 1 := by
    rw [hprod, Nat.mul_comm m q]
    exact NumberTheory.gcd_predecessor_product_le_cofactor hq.pos hm
  have hgcd' : ((q - 1).gcd (n - 1) : ℝ) ≤ m := by exact_mod_cast hgcd.trans (Nat.sub_le m 1)
  have hc := (mul_le_mul_of_nonneg_left hgcd' hτ).trans_lt hcount
  exact
    exists_prime_of_mean_budget hn ho hq hq2 (by norm_num only) hd B k τ δ hk hs hτ
      (by simpa only [pow_one] using hsize) hmean hc

/-- For `n = m * q` with an odd prime `q`, a positive lower bound `M` for the number
of primes up to `B`, an upper bound `P` for their logarithm sum, and the displayed mean
and counting budgets yield an MR-rejecting prime at most `B`. Monotonicity transfers both
budgets from `M` to the full prime set. This accepts explicit Chebyshev estimates. -/
theorem large_cofactor_of_mean_supply {n m q : ℕ} (hn : 1 < n) (ho : Odd n) (hm : 1 < m)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = m * q) (B M k : ℕ) (τ δ P : ℝ) (hk : 1 ≤ k)
    (hM0 : 1 ≤ M) (hM : M ≤ B.primeCounting) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) (hmargin : 0 ≤ τ - δ)
    (hsize : τ ≤ Real.log q) (hθ : (∑ r ∈ B.primesLE, Real.log r) ≤ P)
    (hmean : (k : ℝ) * P ≤ (τ - δ) * M) (hcount : τ * m < δ * Nat.choose M k) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hMc : M ≤ B.primesLE.card := by
    rw [Nat.primesLE_card_eq_primeCounting]
    exact hM
  have hs : 1 ≤ B.primesLE.card := hM0.trans hMc
  have hm' : (M : ℝ) ≤ B.primesLE.card := Nat.cast_le.mpr hMc
  have hw := mul_le_mul_of_nonneg_left hθ (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hm'' := mul_le_mul_of_nonneg_left hm' hmargin
  have hc := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.choose_le_choose k hMc)) hδ
  exact
    large_cofactor_of_mean_budget hn ho hm hq hq2 hprod B k τ δ hk hs hτ hsize
      (hw.trans (hmean.trans hm'')) (hcount.trans_le hc)

/-- For `n = m * q` with an odd prime `q`, the displayed theta estimates on the terminal
sixteenth-scale interval and the mean and counting budgets give a rejecting prime up to `B`.
The Abel estimate supplies the prime count, while the theta upper bound controls the mean.
This is the analytic interface for the large-cofactor branch. -/
theorem large_cofactor_of_theta {n m q : ℕ} (hn : 1 < n) (ho : Odd n) (hm : 1 < m) (hq : q.Prime)
    (hq2 : q ≠ 2) (hprod : n = m * q) (B M k : ℕ) (τ δ P a η : ℝ) (hB : 32 ≤ B) (hk : 1 ≤ k)
    (hM0 : 1 ≤ M) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) (hmargin : 0 ≤ τ - δ) (hsize : τ ≤ Real.log q)
    (hθB : a * B ≤ Chebyshev.theta B)
    (hθ : ∀ t ∈ Set.Icc ((B : ℝ) / 16) B, η * t ≤ Chebyshev.theta t)
    (hupper : Chebyshev.theta B ≤ P)
    (hM : (M : ℝ) ≤ (B : ℝ) * (a / Real.log B + (15 * η / 16) / Real.log B ^ 2))
    (hmean : (k : ℝ) * P ≤ (τ - δ) * M) (hcount : τ * m < δ * Nat.choose M k) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hlower := AnalyticNumberTheory.Arithmetic.primeCount_ge_of_theta_sixteenth hB hθB hθ
  have hMc : M ≤ B.primeCounting := Nat.cast_le.mp (hM.trans hlower)
  have hlog : (∑ r ∈ B.primesLE, Real.log r) ≤ P := by
    rw [← Chebyshev.theta_eq_sum_primesLE_log]
    exact hupper
  exact
    large_cofactor_of_mean_supply hn ho hm hq hq2 hprod B M k τ δ P hk hM0 hMc hτ hδ hmargin hsize
      hlog hmean hcount

end PseudoPrime.PrimeTestBounds.MillerRabin
