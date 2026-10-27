/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaComparison
public import PseudoPrime.PrimeTest.MillerRabin.SignSubgroupIndex
public import PseudoPrime.PrimeTestBounds.MillerRabin.FromLLS
public import PseudoPrime.LLS.ConductorSumComparison
public import PseudoPrime.LLS.ExplicitKernelCoefficientBounds
public import PseudoPrime.LLS.SmallIndexGammaNumerics

/-! # Gamma coefficient bounds for strong Miller–Rabin witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At Gamma scale (33/50)/(11/6)*log(n)^2, an index-at-least-four subgroup
cannot satisfy the numerical comparison if its normalized remainder is at most
log(n)/4000. Bound the conductor sum by (index-1)*log(n), use the exponential
certificate 55/344, and apply the strict rational coefficient gap.
This is the analytic contradiction used to obtain MR witnesses. -/
private theorem gamma_inequality_contradiction_of_index_ge_four {n : ℕ} [NeZero n]
    (H : Subgroup (ZMod n)ˣ) (hi : 4 ≤ H.index) (hL : 0 < Real.log n) :
    let x := ((33 / 50 : ℝ) / (11 / 6)) * (Real.log n) ^ 2
    let R := (65 / 3 : ℝ) * x ^ (1 / 4 : ℝ) + 39 + (10002 * Real.log n + 10004) / Real.sqrt x
    R ≤ (1 / 2000 : ℝ) * Real.log n / 2 →
      ¬(((H.index : ℝ) * (1 - Real.exp (-(11 / 6 : ℝ))) - 1) * Real.sqrt x ≤
          (11783423 / 25000000 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
            13 * ((H.index : ℝ) + 1) * x ^ (1 / 4 : ℝ) +
            ((H.index - 1 : ℕ) : ℝ) * (39 + (10002 * Real.log n + 10004) / Real.sqrt x)) := by
  intro x R hR hcmp
  have hiR : (4 : ℝ) ≤ H.index := Nat.cast_le.mpr hi
  have hm : (0 : ℝ) < (H.index : ℝ) - 1 := by linarith only [hiR]
  have hcast : ((H.index - 1 : ℕ) : ℝ) = (H.index : ℝ) - 1 := by
    rw [Nat.cast_sub (le_trans (by decide : 1 ≤ 4) hi), Nat.cast_one]
  rw [hcast] at hcmp
  have hC := LLS.PaperStatements.subgroupConductorLogSum_le H
  have hCM := mul_le_mul_of_nonneg_left hC (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
  have he := LLS.PaperStatements.gamma_four_small_denominator_exp_bound
  have hep := mul_nonneg (le_of_lt hm) (sub_nonneg.mpr he)
  have hs := Real.sqrt_nonneg x
  have hx0 : 0 ≤ x := mul_nonneg (by norm_num only) (sq_nonneg _)
  have hr : 0 ≤ x ^ (1 / 4 : ℝ) := Real.rpow_nonneg hx0 _
  have hleft :
    ((H.index : ℝ) - 1) * (1 - (4 / 3 : ℝ) * (55 / 344)) * Real.sqrt x ≤
      ((H.index : ℝ) * (1 - Real.exp (-(11 / 6 : ℝ))) - 1) * Real.sqrt x := by
    have hz :=
      mul_nonneg hs
        (show 0 ≤ (H.index : ℝ) * ((55 / 344 : ℝ) - Real.exp (-(11 / 6 : ℝ))) by
          nlinarith only [hep, he])
    have hd :=
      mul_nonneg hs
        (show 0 ≤ ((4 / 3 : ℝ) * ((H.index : ℝ) - 1) - (H.index : ℝ)) * (55 / 344 : ℝ) by
          nlinarith only [hiR])
    nlinarith only [hz, hd]
  have hright :
    (11783423 / 25000000 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
        13 * ((H.index : ℝ) + 1) * x ^ (1 / 4 : ℝ) +
        ((H.index : ℝ) - 1) * (39 + (10002 * Real.log n + 10004) / Real.sqrt x) ≤
      ((H.index : ℝ) - 1) * ((11783423 / 25000000 : ℝ) * Real.log n + R) := by
    have hd :=
      mul_nonneg hr
        (show 0 ≤ (65 / 3 : ℝ) * ((H.index : ℝ) - 1) - 13 * ((H.index : ℝ) + 1) by
          linarith only [hiR])
    dsimp only [R]
    nlinarith only [hCM, hd]
  have hstrict := mul_lt_mul_of_pos_left (LLS.gamma_index_four_main_term_lt hL hR) hm
  rw [← mul_assoc] at hstrict
  exact (not_lt_of_ge (hleft.trans (hcmp.trans hright))) hstrict

/-- Under GRH for an odd n≥20000, a subgroup of index at least four containing
all strong passes gives a prime failing base below (33/50)*log(n)^2, provided
the fixed Gamma scale is at least one and the explicit normalized remainder is
at most log(n)/4000. Universal passage would give the impossible Gamma comparison.
The error condition is numerical and is discharged by the explicit cutoff below. -/
theorem exists_prime_witness_le_gamma_of_index_ge_four_and_error {n : ℕ} [NeZero n]
    (hnlarge : 20000 ≤ n) (hnOdd : Odd n) (H : Subgroup (ZMod n)ˣ) (hi : 4 ≤ H.index)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 0 < Real.log n)
    (hx : 1 ≤ ((33 / 50 : ℝ) / (11 / 6)) * (Real.log n) ^ 2)
    (hR :
      (65 / 3 : ℝ) * (((33 / 50 : ℝ) / (11 / 6)) * (Real.log n) ^ 2) ^ (1 / 4 : ℝ) + 39 +
          (10002 * Real.log n + 10004) / Real.sqrt (((33 / 50 : ℝ) / (11 / 6)) * (Real.log n) ^ 2) ≤
        (1 / 2000 : ℝ) * Real.log n / 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (33 / 50 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  classical
  by_contra hnone
  let x := ((33 / 50 : ℝ) / (11 / 6)) * (Real.log n) ^ 2
  have hcut : (11 / 6 : ℝ) * x = (33 / 50 : ℝ) * (Real.log n) ^ 2 := by
    dsimp only [x]
    ring
  have hpass :
    ∀ r : ℕ,
      r.Prime → (r : ℝ) ≤ (11 / 6 : ℝ) * x → PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
    intro r hr hbound
    rw [hcut] at hbound
    by_contra hfail
    exact hnone ⟨r, hr, hbound, hfail⟩
  have hcmp :=
    gamma_inequality_of_prime_passes_in_subgroup hnlarge hnOdd H hHpass hGRH hx
      (by norm_num only : (0 : ℝ) ≤ 11 / 6) hpass
  exact gamma_inequality_contradiction_of_index_ge_four H hi hL hR hcmp

/-- For L≥10^11, the scale x=(33/50)/(11/6)*L^2 is at least one and the
normalized Gamma remainder is at most L/4000. Its fourth root is at most sqrt(L),
and the constant plus inverse-square-root part is at most 20000.
The explicit square-root absorption lemma certifies a common cutoff for every index≥4. -/
private theorem gamma_index_four_error_budget {L : ℝ} (hL : 100000000000 ≤ L) :
    let x := ((33 / 50 : ℝ) / (11 / 6)) * L ^ 2
    1 ≤ x ∧
      (65 / 3 : ℝ) * x ^ (1 / 4 : ℝ) + 39 + (10002 * L + 10004) / Real.sqrt x ≤
        (1 / 2000 : ℝ) * L / 2 := by
  intro x
  have h16 : 16 ≤ L := le_trans (by norm_num only) hL
  have hpos : 0 < L := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 16) h16
  have hx0 : 0 ≤ x := mul_nonneg (by norm_num only) (sq_nonneg L)
  have hsqrt : Real.sqrt x = (3 / 5 : ℝ) * L := by
    apply (Real.sqrt_eq_iff_mul_self_eq hx0 (mul_nonneg (by norm_num only) hpos.le)).mpr
    dsimp only [x]
    ring
  have hfourth : x ^ (1 / 4 : ℝ) ≤ Real.sqrt L := by
    have he : x ^ (1 / 4 : ℝ) = Real.sqrt (Real.sqrt x) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0]
      congr 1
      norm_num only
    rw [he, hsqrt]
    apply Real.sqrt_le_sqrt
    linarith only [hpos.le]
  have hratio : (10002 * L + 10004) / Real.sqrt x ≤ 19961 := by
    rw [hsqrt]
    apply (div_le_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 3 / 5) hpos)).mpr
    linarith only [h16]
  have hA : 4 * (20000 : ℝ) / (1 / 2000 : ℝ) ≤ L :=
    (by norm_num only : 4 * (20000 : ℝ) / (1 / 2000 : ℝ) ≤ 100000000000).trans hL
  have hBC : (4 * ((0 : ℝ) + 65 / 3) / (1 / 2000 : ℝ)) ^ 2 ≤ L :=
    (by norm_num only : (4 * ((0 : ℝ) + 65 / 3) / (1 / 2000 : ℝ)) ^ 2 ≤ 100000000000).trans hL
  have habs :=
    Analysis.log_sqrt_error_le_half (by norm_num only : (0 : ℝ) ≤ 0)
      (by norm_num only : (0 : ℝ) < 1 / 2000) hpos hA hBC
  simp only [zero_mul, add_zero] at habs
  constructor
  · dsimp only [x]
    nlinarith only [h16]
  · have hf := mul_le_mul_of_nonneg_left hfourth (by norm_num only : (0 : ℝ) ≤ 65 / 3)
    linarith only [hf, hratio, habs]

/-- Under GRH, for an odd modulus n≥10^50000000000, any subgroup of index at
least four containing every strong pass yields a prime failing base at most
(33/50)*log(n)^2. The decimal lower bound gives log(n)≥10^11, so the explicit
Gamma error budget applies uniformly in the subgroup index. The supplied subgroup
remains an arithmetic input until all composite branches have been assembled. -/
theorem exists_prime_witness_le_gamma_of_index_ge_four {n : ℕ} [NeZero n] (hnOdd : Odd n)
    (H : Subgroup (ZMod n)ˣ) (hi : 4 ≤ H.index)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 10 ^ 50000000000 ≤ n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (33 / 50 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hL := Analysis.log_nat_ge_of_decimal hn
  norm_num only at hL
  have hpos : 0 < Real.log n := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 100000000000) hL
  have hlog := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr (NeZero.pos n) : (0 : ℝ) < n)
  have hnlarge : 20000 ≤ n := by
    apply Nat.cast_le (α := ℝ).mp
    norm_num only [Nat.cast_ofNat]
    linarith only [hL, hlog]
  have hb := gamma_index_four_error_budget hL
  exact
    exists_prime_witness_le_gamma_of_index_ge_four_and_error hnlarge hnOdd H hi hHpass hGRH hpos
      hb.1 hb.2

/-- A decimal exponent at least five gives a modulus cutoff at least 20000.
Compare powers before substituting a concrete large exponent, so the kernel
does not evaluate the enormous natural power. This enforces the analytic base cutoff. -/
private theorem decimal_cutoff_ge_twenty_thousand (d : ℕ) (hd : 5 ≤ d) : 20000 ≤ 10 ^ d := by
  exact (by decide : 20000 ≤ 10 ^ 5).trans (Nat.pow_le_pow_right (by decide : 0 < 10) hd)

/-- Under GRH, an odd prime-power composite p^a≥10^50000000000 has a prime
strong Miller–Rabin witness at most (33/50)*log(p^a)^2. Its Fermat subgroup has
index p^(a-1)≥4; the modulus cutoff excludes 9. Apply the uniform Gamma witness
theorem to its pass-containing subgroup. No unspecified threshold or analytic input remains. -/
theorem exists_prime_witness_le_gamma_of_prime_pow {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : 2 ≤ a) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hn : 10 ^ 50000000000 ≤ p ^ a) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (33 / 50 : ℝ) * (Real.log ((p ^ a : ℕ) : ℝ)) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass (p ^ a) (r : ZMod (p ^ a)) := by
  let : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  have hnlarge : 20000 ≤ p ^ a :=
    (decimal_cutoff_ge_twenty_thousand 50000000000 (by decide : 5 ≤ 50000000000)).trans hn
  have hn9 : p ^ a ≠ 9 := by
    intro h
    rw [h] at hnlarge
    exact (by decide : ¬20000 ≤ 9) hnlarge
  have hn1 : 1 < p ^ a := lt_of_lt_of_le (by decide : 1 < 20000) hnlarge
  exact
    exists_prime_witness_le_gamma_of_index_ge_four (hp.odd_of_ne_two hp2).pow
      (PrimeTest.fermatSubgroup (p ^ a))
      (PrimeTest.four_le_index_fermatSubgroup_prime_pow hp hp2 ha hn9)
      (fun _ hz ↦
        PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn1 (hp.odd_of_ne_two hp2).pow hz)
      hGRH hn

/-- Under GRH, a product p*q≥10^50000000000 of distinct odd primes p<q has
a prime strong Miller–Rabin witness at most (33/50)*log(p*q)^2. The minimum-two-adic
sign subgroup contains every pass and has index at least four, so the uniform
Gamma witness theorem applies. No unspecified threshold or analytic input remains. -/
theorem exists_prime_witness_le_gamma_of_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p < q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 10 ^ 50000000000 ≤ p * q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (33 / 50 : ℝ) * (Real.log ((p * q : ℕ) : ℝ)) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass (p * q) (r : ZMod (p * q)) := by
  let : NeZero (p * q) := ⟨mul_ne_zero hp.ne_zero hq.ne_zero⟩
  obtain ⟨H, hi, hHpass⟩ :=
    PrimeTest.exists_index_ge_four_subgroup_containing_passes_two_primes hp hq hp2 hq2 hpq
  exact
    exists_prime_witness_le_gamma_of_index_ge_four
      ((hp.odd_of_ne_two hp2).mul (hq.odd_of_ne_two hq2)) H hi hHpass hGRH hn

/-- Under GRH, every odd composite n≥10^50000000000 has a prime strong
Miller–Rabin witness at most (33/50)*log(n)^2. The explicit cutoff excludes 9,
and the minimum-two-adic sign subgroup has index at least four for every
remaining composite factorization. Apply the index-uniform Gamma error bound.
This is the complete coefficient-0.66 witness theorem, including prime base two. -/
theorem exists_prime_witness_le_gamma {n : ℕ} (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 10 ^ 50000000000 ≤ n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (33 / 50 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hnlarge : 20000 ≤ n :=
    (decimal_cutoff_ge_twenty_thousand 50000000000 (by decide : 5 ≤ 50000000000)).trans hn
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 20000) hnlarge
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  have hn9 : n ≠ 9 := by
    intro h
    rw [h] at hnlarge
    exact (by decide : ¬20000 ≤ 9) hnlarge
  obtain ⟨H, hi, hHpass⟩ :=
    PrimeTest.exists_index_ge_four_subgroup_containing_strongMillerRabinPass hn1 hnOdd hnComposite
      hn9
  exact exists_prime_witness_le_gamma_of_index_ge_four hnOdd H hi hHpass hGRH hn

/-- Under GRH for odd n≥10^50000000000, passing the strong test for every prime
base at most (33/50)*log(n)^2 is equivalent to primality. The composite direction
uses the coefficient-0.66 witness theorem, and the prime direction restricts
the existing log-squared criterion to the smaller cutoff.
This exposes the sharpened finite-base primality criterion at one explicit threshold. -/
theorem prime_iff_millerRabin_for_all_primes_le_gamma_log_sq {n : ℕ} (hnOdd : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 10 ^ 50000000000 ≤ n) :
    (∀ r : ℕ,
        r.Prime →
          (r : ℝ) ≤ (33 / 50 : ℝ) * (Real.log n) ^ 2 →
          PrimeTest.StrongMillerRabinPass n (r : ZMod n)) ↔
      n.Prime := by
  constructor
  · intro hpass
    by_contra hComposite
    obtain ⟨r, hr, hb, hfail⟩ := exists_prime_witness_le_gamma hnOdd hComposite hGRH hn
    exact hfail (hpass r hr hb)
  · intro hp r hr hb
    have hnlarge : 20000 ≤ n :=
      (decimal_cutoff_ge_twenty_thousand 50000000000 (by decide : 5 ≤ 50000000000)).trans hn
    have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 20000) hnlarge
    have hcap : (33 / 50 : ℝ) * (Real.log n) ^ 2 ≤ (Real.log n) ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) (by norm_num only)
    exact
      (prime_iff_millerRabin_for_all_primes_le_log_sq hGRH hn1 hnOdd).mpr hp r hr (hb.trans hcap)

end PseudoPrime.PrimeTestBounds.MillerRabin
