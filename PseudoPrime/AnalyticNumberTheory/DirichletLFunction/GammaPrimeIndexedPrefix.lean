/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaPrimePowerPrefix
public import PseudoPrime.Analysis.GammaActualPrimeCosts
public import Mathlib.Algebra.BigOperators.Intervals

/-! # Prime-indexed finite Euler prefixes -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Reindex positive exponents 1 through N as zero-based indices below N.
The exponent is k+1 after reindexing. This aligns the exact integer prefix
with the local-cost interfaces, which use positive powers in this form. -/
theorem gamma_positive_exponent_sum_eq_range (N : ℕ) (F : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 N, F k) = ∑ k ∈ Finset.range N, F (k + 1) := by
  rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.succ_eq_succ, Nat.succ_sub_one, Nat.add_comm]

/-- A row indexed by j is contained in the union of all selected rows.
Adding zero terms outside that row expresses its sum over the common
finite universe. This supports finite interchange without disjointness. -/
theorem gamma_prefix_row_eq_common_sum (J : Finset ℕ) (P : ℕ → Finset ℕ) (F : ℕ → ℕ → ℝ) {j : ℕ}
    (hj : j ∈ J) : (∑ p ∈ P j, F j p) = ∑ p ∈ J.biUnion P, if p ∈ P j then F j p else 0 := by
  have hsubset : P j ⊆ J.biUnion P := fun p hp ↦ Finset.mem_biUnion.mpr ⟨j, hj, hp⟩
  have hfilter : (J.biUnion P).filter (fun p ↦ p ∈ P j) = P j := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hsubset h, h⟩⟩
  rw [← Finset.sum_filter, hfilter]

/-- Exchange a finite exponent-first prefix for prime-first prefixes.
The outer prime set is the union of the row sets; the inner index set
retains exactly the rows containing the prime. Finite sum interchange
preserves every contribution even when row sets overlap. -/
theorem gamma_prefix_rows_eq_prime_sums (J : Finset ℕ) (P : ℕ → Finset ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ j ∈ J, ∑ p ∈ P j, F j p) = ∑ p ∈ J.biUnion P, ∑ j ∈ J.filter (fun j ↦ p ∈ P j), F j p := by
  rw [Finset.sum_congr rfl (fun j hj ↦ gamma_prefix_row_eq_common_sum J P F hj), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_filter]

/-- Number of positive exponents in the exact prefix at cutoff b.
The natural floor is the same bound used by the prime-power bijection.
Zero-based indices below it give exponents k+1 in local Euler sums. -/
noncomputable def gammaPrefixExponentCount (b : ℝ) : ℕ :=
  ⌊Real.log b / Real.log 2⌋₊

/-- Prime bases retained in row k of the exact prefix. The exponent is
k+1, and the prime bound is floor(b^(1/(k+1))). This row preserves the
cutoff from the original prime-power decomposition. -/
noncomputable def gammaPrefixRowPrimes (b : ℝ) (k : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 ⌊b ^ (1 / ((k + 1 : ℕ) : ℝ))⌋₊).filter Nat.Prime

/-- Common finite prime universe of all positive-power prefix rows.
It is their finite union, so it includes every contributing prime base
without a separate real-power monotonicity approximation. -/
noncomputable def gammaPrefixPrimeSet (b : ℝ) : Finset ℕ :=
  (Finset.range (gammaPrefixExponentCount b)).biUnion (gammaPrefixRowPrimes b)

/-- Zero-based positive-power indices selected for one prime p.
Membership means that the prime belongs to the exact row for k+1.
This finite set can be passed directly to the actual local-cost API. -/
noncomputable def gammaPrefixPowerIndices (b : ℝ) (p : ℕ) : Finset ℕ :=
  (Finset.range (gammaPrefixExponentCount b)).filter (fun k ↦ p ∈ gammaPrefixRowPrimes b k)

/-- The original integer character correction equals a sum of finite
positive-power prefixes indexed by prime. Apply the exact prime-power
decomposition, shift to k+1, and interchange finite rows. The resulting
index sets match the actual local Euler and ramp cost interfaces. -/
theorem gamma_character_prefix_eq_prime_indexed {q : ℕ} (χ : DirichletCharacter ℂ q) {b : ℝ}
    (hb : 0 ≤ b) :
    (∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, (1 - (χ n).re) * Analysis.gammaResolventMangoldtWeight n) =
      ∑ p ∈ gammaPrefixPrimeSet b,
        ∑ k ∈ gammaPrefixPowerIndices b p,
          (1 - (χ (p ^ (k + 1))).re) * Analysis.gammaResolventMangoldtWeight (p ^ (k + 1)) := by
  rw [gamma_character_prefix_eq_prime_power_sum χ hb, gamma_positive_exponent_sum_eq_range]
  exact
    gamma_prefix_rows_eq_prime_sums (Finset.range (gammaPrefixExponentCount b))
      (gammaPrefixRowPrimes b)
      (fun k p ↦ (1 - (χ (p ^ (k + 1))).re) * Analysis.gammaResolventMangoldtWeight (p ^ (k + 1)))

/-- A prime in a prefix row is at most b when b>=1. The positive exponent
has reciprocal at most one, so its real root is at most b. The floor
bound then gives the actual prime bound needed by no-witness transfer. -/
theorem gamma_prefix_row_prime_le {b : ℝ} (hb : 1 ≤ b) {k p : ℕ}
    (hp : p ∈ gammaPrefixRowPrimes b k) : (p : ℝ) ≤ b := by
  have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))
  have hdiv : (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ≤ 1 :=
    (div_le_iff₀ (zero_lt_one.trans_le hk1)).mpr (by simpa only [one_mul] using hk1)
  have hroot := Real.rpow_le_self_of_one_le hb hdiv
  have hfloor := Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hb) (1 / ((k + 1 : ℕ) : ℝ)))
  have hle : (p : ℝ) ≤ ⌊b ^ (1 / ((k + 1 : ℕ) : ℝ))⌋₊ := by
    exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
  exact hle.trans (hfloor.trans hroot)

/-- Every member of the common prefix prime set is prime and at most b.
Select a row containing it and apply the exact prime filter and root bound.
This supplies the arithmetic inputs to the ambient no-witness assumption. -/
theorem gamma_prefix_prime_data {b : ℝ} (hb : 1 ≤ b) {p : ℕ} (hp : p ∈ gammaPrefixPrimeSet b) :
    p.Prime ∧ (p : ℝ) ≤ b := by
  obtain ⟨k, hk, hpk⟩ := Finset.mem_biUnion.mp hp
  exact ⟨(Finset.mem_filter.mp hpk).2, gamma_prefix_row_prime_le hb hpk⟩

/-- A prefix prime outside the ambient modulus has character value one
under the prime no-witness assumption. The actual prefix prime bound and
prime coprimality transfer that assumption without requiring primitivity
or coprimality with the smaller character conductor. -/
theorem gamma_prefix_prime_value_one_of_not_dvd {q a : ℕ} (χ : DirichletCharacter ℂ q) {b : ℝ}
    (hb : 1 ≤ b) (hone : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p a → χ p = 1) {p : ℕ}
    (hp : p ∈ gammaPrefixPrimeSet b) (hpa : ¬p ∣ a) : χ p = 1 := by
  have hdata := gamma_prefix_prime_data hb hp
  exact hone p hdata.1 hdata.2 (hdata.1.coprime_iff_not_dvd.mpr hpa)

/-- Under the ambient prime no-witness assumption, every finite positive
power Euler prefix at a prime outside the ambient modulus is zero.
All powers of its local value one remain one. This removes only justified
zero terms from the prime-indexed integer prefix. -/
theorem gamma_prefix_euler_sum_eq_zero_of_not_dvd {q a : ℕ} (χ : DirichletCharacter ℂ q) {b : ℝ}
    (hb : 1 ≤ b) (hone : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p a → χ p = 1) {p : ℕ}
    (hp : p ∈ gammaPrefixPrimeSet b) (hpa : ¬p ∣ a) :
    (∑ k ∈ gammaPrefixPowerIndices b p,
        (1 - (χ (p ^ (k + 1))).re) * Analysis.gammaResolventMangoldtWeight (p ^ (k + 1))) =
      0 := by
  have hv := gamma_prefix_prime_value_one_of_not_dvd χ hb hone hp hpa
  simp only [map_pow, hv, one_pow, Complex.one_re, sub_self, zero_mul, Finset.sum_const_zero]

/-- A prime outside the common prefix universe has no retained power
indices. Any such index would place the prime in one of the union rows.
This justifies adding zero Euler prefixes at other ambient prime factors. -/
theorem gamma_prefix_power_indices_eq_empty {b : ℝ} {p : ℕ} (hp : p ∉ gammaPrefixPrimeSet b) :
    gammaPrefixPowerIndices b p = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro k hk
  exact hp (Finset.mem_biUnion.mpr ⟨k, (Finset.mem_filter.mp hk).1, (Finset.mem_filter.mp hk).2⟩)

/-- Under the ambient prime no-witness assumption, the original integer
character correction equals the sum of finite Euler prefixes over all
ambient prime factors. Outside primes have value one; unretained ambient
primes have empty index sets. This preserves minus-one values at primes
omitted by the smaller primitive conductor. -/
theorem gamma_character_prefix_eq_ambient_prime_sum {q a : ℕ} (χ : DirichletCharacter ℂ q)
    (ha : 0 < a) {b : ℝ} (hb : 1 ≤ b)
    (hone : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p a → χ p = 1) :
    (∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, (1 - (χ n).re) * Analysis.gammaResolventMangoldtWeight n) =
      ∑ p ∈ a.primeFactors,
        ∑ k ∈ gammaPrefixPowerIndices b p,
          (1 - (χ (p ^ (k + 1))).re) * Analysis.gammaResolventMangoldtWeight (p ^ (k + 1)) := by
  let F : ℕ → ℝ := fun p ↦
    ∑ k ∈ gammaPrefixPowerIndices b p,
      (1 - (χ (p ^ (k + 1))).re) * Analysis.gammaResolventMangoldtWeight (p ^ (k + 1))
  let S := (gammaPrefixPrimeSet b).filter (fun p : ℕ ↦ p ∣ a)
  have hsub : S ⊆ a.primeFactors := by
    intro p hp
    have hd := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(gamma_prefix_prime_data hb hd.1).1, hd.2, ha.ne'⟩
  have he0 : (∑ p ∈ S, F p) = ∑ p ∈ gammaPrefixPrimeSet b, F p :=
    Finset.sum_subset (Finset.filter_subset _ _)
      (fun p hp hnot ↦
        gamma_prefix_euler_sum_eq_zero_of_not_dvd χ hb hone hp
          (fun hd ↦ hnot (Finset.mem_filter.mpr ⟨hp, hd⟩)))
  have he1 : (∑ p ∈ S, F p) = ∑ p ∈ a.primeFactors, F p := by
    apply Finset.sum_subset hsub
    intro p hp hnot
    have hnotP : p ∉ gammaPrefixPrimeSet b := fun hP ↦
      hnot (Finset.mem_filter.mpr ⟨hP, Nat.dvd_of_mem_primeFactors hp⟩)
    dsimp only [F]
    rw [gamma_prefix_power_indices_eq_empty hnotP, Finset.sum_empty]
  rw [gamma_character_prefix_eq_prime_indexed χ (zero_le_one.trans hb)]
  exact he0.symm.trans he1

/-- The actual integer Euler correction and the full ambient local ramp
sum combine exactly into the existing actual local costs. Use the prime
no-witness transfer and sum the Euler and ramp terms over the same factors.
This connects the integer prefix to the shared conductor budget interface. -/
theorem gamma_character_prefix_add_ambient_ramp_eq_local_cost {q a : ℕ} (χ : DirichletCharacter ℂ q)
    (ha : 0 < a) {b : ℝ} (hb : 1 ≤ b)
    (hone : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p a → χ p = 1) (x : ℝ) :
    (∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, (1 - (χ n).re) * Analysis.gammaResolventMangoldtWeight n) +
        (∑ p ∈ a.primeFactors,
          Real.log p *
            ((∑' k : ℕ,
                Analysis.exponentialRampLocalCorrection (χ p) ((p : ℝ) ^ (k + 1) / x) (k + 1)) /
              Real.sqrt x)) =
      ∑ p ∈ a.primeFactors,
        Analysis.gammaActualPrimeLocalCost χ p (gammaPrefixPowerIndices b p) x := by
  rw [gamma_character_prefix_eq_ambient_prime_sum χ ha hb hone]
  simp only [Analysis.gammaActualPrimeLocalCost, Finset.sum_add_distrib]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
