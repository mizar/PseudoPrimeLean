/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaSubgroupComparison
public import PseudoPrime.PrimeTest.MillerRabin.Composite
public import PseudoPrime.PrimeTest.MillerRabin.WitnessSubgroupCardinality
public import PseudoPrime.PrimeTest.MillerRabin.WitnessSubgroupTwoPrimes

/-! # Explicit Gamma comparison for universally passing prime bases

Small prime divisors cannot pass the strong test. A proper pass-containing
subgroup therefore satisfies the numerical Gamma inequality without finite level loss.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For odd n>1, if all prime bases up to real cutoff X pass the canonical
strong test, every prime divisor exceeds floor(X). A prime divisor would fail
the test by nonunitness. This removes finite principal-level loss in the analytic comparison. -/
private theorem prime_divisor_gt_cutoff_of_strong_pass {n : ℕ} (hn : 1 < n) (hnOdd : Odd n) {X : ℝ}
    (hpass : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    ∀ p : ℕ, p.Prime → p ∣ n → ⌊X⌋₊ < p := by
  intro p hp hdiv
  apply lt_of_not_ge
  intro hle
  have hX : (p : ℝ) ≤ X := (Nat.le_floor_iff' hp.ne_zero).mp hle
  exact PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn hnOdd hp hdiv (hpass p hp hX)

/-- For an odd modulus n≥20000 under GRH, a subgroup containing every strong pass
satisfies the explicit Gamma inequality if all prime bases below lambda*x pass.
Prime divisors cannot pass, so the finite principal-level correction vanishes.
Retaining the supplied subgroup permits an independently proved index bound to be used. -/
theorem gamma_inequality_of_prime_passes_in_subgroup {n : ℕ} [NeZero n] (hnlarge : 20000 ≤ n)
    (hnOdd : Odd n) (H : Subgroup (ZMod n)ˣ)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x lambda : ℝ} (hx : 1 ≤ x)
    (hl : 0 ≤ lambda)
    (hpass :
      ∀ p : ℕ, p.Prime → (p : ℝ) ≤ lambda * x → PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    ((H.index : ℝ) * (1 - Real.exp (-lambda)) - 1) * Real.sqrt x ≤
      (11783423 / 25000000 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
        13 * ((H.index : ℝ) + 1) * x ^ (1 / 4 : ℝ) +
        ((H.index - 1 : ℕ) : ℝ) * (39 + (10002 * Real.log n + 10004) / Real.sqrt x) := by
  have hn : 1 < n := by linarith only [hnlarge]
  apply
    LLS.PaperStatements.gamma_noSmallPrimes_explicit_inequality_of_no_small_divisor hnlarge H hGRH
      hx hl
  · exact prime_divisor_gt_cutoff_of_strong_pass hn hnOdd hpass
  · intro p hp _ hpX
    exact hHpass (p : ZMod n) (hpass p hp hpX)

/-- For an odd composite n≥20000 under GRH, if every prime base below
lambda*x passes, there is a proper subgroup satisfying the explicit Gamma
conductor inequality without a finite modulus-loss term, for x≥1 and lambda≥0.
Choose the proper subgroup containing all strong passes; prime-divisor exclusion
eliminates the level correction and pass containment supplies the no-small-prime condition.
This connects the numerical Gamma comparison to the Miller–Rabin contradiction. -/
theorem exists_proper_subgroup_gamma_inequality_of_prime_passes {n : ℕ} [NeZero n]
    (hnlarge : 20000 ≤ n) (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x lambda : ℝ} (hx : 1 ≤ x)
    (hl : 0 ≤ lambda)
    (hpass :
      ∀ p : ℕ, p.Prime → (p : ℝ) ≤ lambda * x → PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    ∃ H : Subgroup (ZMod n)ˣ,
      H ≠ ⊤ ∧
        ((H.index : ℝ) * (1 - Real.exp (-lambda)) - 1) * Real.sqrt x ≤
          (11783423 / 25000000 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
            13 * ((H.index : ℝ) + 1) * x ^ (1 / 4 : ℝ) +
            ((H.index - 1 : ℕ) : ℝ) * (39 + (10002 * Real.log n + 10004) / Real.sqrt x) := by
  have hn : 1 < n := by linarith only [hnlarge]
  obtain ⟨H, hH, hHpass⟩ :=
    PrimeTest.exists_proper_subgroup_containing_strongMillerRabinPass hn hnOdd hnComposite
  refine ⟨H, hH, ?_⟩
  apply
    LLS.PaperStatements.gamma_noSmallPrimes_explicit_inequality_of_no_small_divisor hnlarge H hGRH
      hx hl
  · exact prime_divisor_gt_cutoff_of_strong_pass hn hnOdd hpass
  · intro p hp _ hpX
    exact hHpass (p : ZMod n) (hpass p hp hpX)

/-- For an odd prime-power composite of size at least 20000 under GRH, universal
prime-base passage up to lambda*x forces the Gamma inequality for its Fermat subgroup,
whose index is at least four. The exact prime-power index excludes the exceptional
modulus 9, and Fermat containment supplies the analytic no-witness hypothesis.
This connects the prime-power branch to the uniform coefficient-0.66 comparison. -/
theorem fermatSubgroup_index_and_gamma_inequality_of_prime_pow_passes {p a : ℕ} [NeZero (p ^ a)]
    (hp : p.Prime) (hp2 : p ≠ 2) (ha : 2 ≤ a) (hnlarge : 20000 ≤ p ^ a)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x lambda : ℝ} (hx : 1 ≤ x)
    (hl : 0 ≤ lambda)
    (hpass :
      ∀ r : ℕ,
        r.Prime →
          (r : ℝ) ≤ lambda * x → PrimeTest.StrongMillerRabinPass (p ^ a) (r : ZMod (p ^ a))) :
    let H := PrimeTest.fermatSubgroup (p ^ a)
    4 ≤ H.index ∧
      ((H.index : ℝ) * (1 - Real.exp (-lambda)) - 1) * Real.sqrt x ≤
        (11783423 / 25000000 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
          13 * ((H.index : ℝ) + 1) * x ^ (1 / 4 : ℝ) +
          ((H.index - 1 : ℕ) : ℝ) *
            (39 + (10002 * Real.log ((p ^ a : ℕ) : ℝ) + 10004) / Real.sqrt x) := by
  have hn : 1 < p ^ a := by linarith only [hnlarge]
  have hn9 : p ^ a ≠ 9 := by
    intro h
    rw [h] at hnlarge
    exact (by decide : ¬20000 ≤ 9) hnlarge
  refine ⟨PrimeTest.four_le_index_fermatSubgroup_prime_pow hp hp2 ha hn9, ?_⟩
  exact
    gamma_inequality_of_prime_passes_in_subgroup hnlarge (hp.odd_of_ne_two hp2).pow
      (PrimeTest.fermatSubgroup (p ^ a))
      (fun _ hz ↦
        PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn (hp.odd_of_ne_two hp2).pow hz)
      hGRH hx hl hpass

/-- For a product of two distinct odd primes of size at least 20000 under GRH,
universal prime-base passage up to lambda*x yields an index-at-least-four subgroup
satisfying the Gamma inequality. Use the minimum-two-adic sign subgroup and its
pass containment, then apply the comparison for a specified subgroup.
This connects the squarefree two-prime branch to the uniform MR coefficient comparison. -/
theorem exists_index_ge_four_subgroup_gamma_inequality_of_two_prime_passes {p q : ℕ}
    [NeZero (p * q)] (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p < q)
    (hnlarge : 20000 ≤ p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x lambda : ℝ} (hx : 1 ≤ x) (hl : 0 ≤ lambda)
    (hpass :
      ∀ r : ℕ,
        r.Prime →
          (r : ℝ) ≤ lambda * x → PrimeTest.StrongMillerRabinPass (p * q) (r : ZMod (p * q))) :
    ∃ H : Subgroup (ZMod (p * q))ˣ,
      4 ≤ H.index ∧
        ((H.index : ℝ) * (1 - Real.exp (-lambda)) - 1) * Real.sqrt x ≤
          (11783423 / 25000000 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
            13 * ((H.index : ℝ) + 1) * x ^ (1 / 4 : ℝ) +
            ((H.index - 1 : ℕ) : ℝ) *
              (39 + (10002 * Real.log ((p * q : ℕ) : ℝ) + 10004) / Real.sqrt x) := by
  obtain ⟨H, hi, hHpass⟩ :=
    PrimeTest.exists_index_ge_four_subgroup_containing_passes_two_primes hp hq hp2 hq2 hpq
  exact
    ⟨H, hi,
      gamma_inequality_of_prime_passes_in_subgroup hnlarge
        ((hp.odd_of_ne_two hp2).mul (hq.odd_of_ne_two hq2)) H hHpass hGRH hx hl hpass⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
