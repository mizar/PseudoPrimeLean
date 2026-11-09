/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.AmbientFermatKernel
public import PseudoPrime.LLS.RelativeChebyshevLowerBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeProductMultisetBounds

/-! # Prime-count supply for prime-power witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH and `0 < h ≤ 1/2`, a lower bound on the relative Chebyshev
expression supplies at least `M` primes up to `B > 1`. Combine the relative
psi estimate with the unconditional psi-to-prime-count inequality and divide
by the positive logarithm. This supplies the analytic counting cells. -/
theorem primeCount_ge_of_relative_psi (hRH : RiemannHypothesis) {h : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1 / 2) {B M : ℕ} (hB : 1 < B)
    (hM : (M : ℝ) * Real.log B ≤ (1 - h) * B - (Real.sqrt B / 10 + 21 / 10) / h - 1839 / 1000) :
    M ≤ B.primeCounting := by
  have hl :=
    hM.trans
      ((LLS.psi_lower_relative_log_shift hRH hh hh1 (Nat.cast_nonneg B)).trans
        (Chebyshev.psi_le_primeCounting_mul_log B))
  have hp : 0 < Real.log (B : ℝ) := Real.log_pos (Nat.one_lt_cast.mpr hB)
  exact Nat.cast_le.mp ((mul_le_mul_iff_left₀ hp).mp hl)

/-- If at least `M` primes lie below `B`, the repeated-factor count can be
used with `M` instead of the exact prime count. Apply monotonicity of the
binomial coefficient and the local prime-power kernel criterion. -/
theorem exists_prime_primePow_multichoose_count {n p a : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (B M k : ℕ) (hB : 1 < B)
    (hprimecount : M ≤ B.primeCounting) (hsize : B ^ k < p ^ a)
    (hcount : p - 1 < Nat.choose (M + k) k) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_primePow_multichoose hn ho hp hp2 ha hdiv B.primesLE k B hB.le
      (fun r hr ↦ (Nat.mem_primesLE.mp hr).2) (fun r hr ↦ (Nat.mem_primesLE.mp hr).1) hsize
  rw [Nat.primesLE_card_eq_primeCounting]
  exact hcount.trans_le (Nat.choose_le_choose k (Nat.add_le_add_right hprimecount k))

/-- Under the same prime-count supply, the distinct-prime product count yields
a rejecting prime when `choose M k` exceeds `p - 1`. This is the counting
interface for analytic cells that do not need repeated factors. -/
theorem exists_prime_primePow_choose_count {n p a : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (B M k : ℕ) (hprimecount : M ≤ B.primeCounting)
    (hsize : B ^ k < p ^ a) (hcount : p - 1 < Nat.choose M k) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_witness_of_prime_pow_choose hn ho hp hp2 ha hdiv B.primesLE k B
      (fun r hr ↦ (Nat.mem_primesLE.mp hr).2) (fun r hr ↦ (Nat.mem_primesLE.mp hr).1) hsize
  rw [Nat.primesLE_card_eq_primeCounting]
  exact hcount.trans_le (Nat.choose_le_choose k hprimecount)

/-- A prime-count lower bound and a repeated-product count exceeding the exact
local gcd produce an MR rejecting prime. Monotonicity transfers the count from
`M` to all primes at most `B`; the gcd is retained for semiprime applications. -/
theorem exists_prime_multichoose_count_gcd {n p a : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (B M k : ℕ) (hB : 1 < B)
    (hprimecount : M ≤ B.primeCounting) (hsize : B ^ k < p ^ a)
    (hcount : (p - 1).gcd (n - 1) < Nat.choose (M + k) k) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_primePow_multichoose_gcd hn ho hp hp2 ha hdiv B.primesLE k B hB.le
      (fun r hr ↦ (Nat.mem_primesLE.mp hr).2) (fun r hr ↦ (Nat.mem_primesLE.mp hr).1) hsize
  rw [Nat.primesLE_card_eq_primeCounting]
  exact hcount.trans_le (Nat.choose_le_choose k (Nat.add_le_add_right hprimecount k))

/-- A prime-count lower bound and a distinct-product count exceeding the exact
local gcd produce an MR rejecting prime. Apply the existing local subgroup
criterion after identifying its cardinality and transferring the count. -/
theorem exists_prime_choose_count_gcd {n p a : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (B M k : ℕ) (hprimecount : M ≤ B.primeCounting)
    (hsize : B ^ k < p ^ a) (hcount : (p - 1).gcd (n - 1) < Nat.choose M k) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  apply
    exists_prime_witness_of_local_card_lt_choose
      (powMonoidHom (n - 1) : (ZMod (p ^ a))ˣ →* (ZMod (p ^ a))ˣ).ker B.primesLE k B
      (fun r hr ↦ (Nat.mem_primesLE.mp hr).2) (fun r hr ↦ (Nat.mem_primesLE.mp hr).1) hsize
  · rw [NumberTheory.card_local_fermat_kernel_prime_pow hn hp hp2 ha hdiv,
      Nat.primesLE_card_eq_primeCounting]
    exact hcount.trans_le (Nat.choose_le_choose k hprimecount)
  · exact fun r hr ↦ PrimeTest.strongMR_local_divisorKernel hn ho hdiv hr

end PseudoPrime.PrimeTestBounds.MillerRabin
