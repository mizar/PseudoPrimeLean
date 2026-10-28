/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianNextTripleNumerics
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularThresholdBounds

/-! # Actual Gaussian triple comparison at coefficient 0.2827 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For index four with conductor-log sum at most twice log n, the actual
fixed-cutoff Gaussian comparison contradicts a secondary error at most log(n)/20000.
Use the certified unnormalized denominator and the three-character coefficient gap;
the conductor term is not divided by three. This supplies the branch witness proof. -/
private theorem gaussianNextTriple_contradiction {n : ℕ} [NeZero n] (H : Subgroup (ZMod n)ˣ)
    (hi : H.index = 4) (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n)
    (hL : 0 < Real.log n)
    (hE :
      70 * (((2827 / 10000 : ℝ) / (21 / 10)) * (Real.log n) ^ 2) ^ (1 / 4 : ℝ) +
          3 *
            LLS.PaperStatements.gaussianAmbientError n
              (((2827 / 10000 : ℝ) / (21 / 10)) * (Real.log n) ^ 2) ≤
        (1 / 10000 : ℝ) * Real.log n / 2)
    (hcmp :
      ((H.index : ℝ) *
              (∫ u in (0 : ℝ)..(21 / 10 : ℝ),
                (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
            Real.exp (1 / 16 : ℝ)) *
          Real.sqrt (((2827 / 10000 : ℝ) / (21 / 10)) * (Real.log n) ^ 2) ≤
        (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
          14 * ((H.index : ℝ) + 1) *
            (((2827 / 10000 : ℝ) / (21 / 10)) * (Real.log n) ^ 2) ^ (1 / 4 : ℝ) +
          ((H.index - 1 : ℕ) : ℝ) *
            LLS.PaperStatements.gaussianAmbientError n
              (((2827 / 10000 : ℝ) / (21 / 10)) * (Real.log n) ^ 2)) :
    False := by
  rw [hi] at hcmp
  norm_num only [Nat.cast_ofNat] at hcmp
  have hd := LLS.gaussian_kernel_triple_denominator_le_at_fixed_cutoff
  have hd' :
    (10971611 / 5000000 : ℝ) ≤
      4 *
          (∫ u in (0 : ℝ)..(21 / 10 : ℝ),
            (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
        (LLS.PaperStatements.gaussianGammaMellinKernel.function (1 / 2)).re := by
    exact hd
  have he :
    (LLS.PaperStatements.gaussianGammaMellinKernel.function (1 / 2)).re = Real.exp (1 / 16 : ℝ) :=
    Analysis.gaussianGammaFunction_endpoint
  rw [he] at hd'
  have hm :=
    mul_le_mul_of_nonneg_right hd'
      (Real.sqrt_nonneg (((2827 / 10000 : ℝ) / (21 / 10)) * (Real.log n) ^ 2))
  have hc := mul_le_mul_of_nonneg_left hC (by norm_num only : (0 : ℝ) ≤ 161 / 400)
  have hs :=
    Analysis.main_term_lt_of_sq_gap_and_error (D := (10971611 / 5000000 : ℝ)) (a :=
      (2827 / 21000 : ℝ)) (M := (161 / 200 : ℝ)) (δ := (1 / 10000 : ℝ)) (by norm_num only)
      (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by
        norm_num only at hE ⊢; exact hE)
  norm_num only at hm hs
  linarith only [hcmp, hm, hc, hs]

/-- Under GRH for odd n≥20000, an index-four subgroup containing all strong
passes and having conductor-log sum at most twice log n gives a prime failing
base at most (2827/10000)log(n)², provided the scale is at least four and its actual
secondary error is at most log(n)/20000. These remaining hypotheses are explicit;
arithmetic classification and a numerical starting value must discharge them
before this branch can be used in the final all-branches theorem. -/
theorem exists_prime_gaussianNextIndexFour {n : ℕ} [NeZero n] (hnlarge : 20000 ≤ n) (hnOdd : Odd n)
    (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n)
    (hx : 4 ≤ ((2827 / 10000 : ℝ) / (21 / 10)) * (Real.log n) ^ 2)
    (hE :
      70 * (((2827 / 10000 : ℝ) / (21 / 10)) * (Real.log n) ^ 2) ^ (1 / 4 : ℝ) +
          3 *
            LLS.PaperStatements.gaussianAmbientError n
              (((2827 / 10000 : ℝ) / (21 / 10)) * (Real.log n) ^ 2) ≤
        (1 / 10000 : ℝ) * Real.log n / 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (2827 / 10000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  classical
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 20000) hnlarge
  have hL : 0 < Real.log n := Real.log_pos (Nat.one_lt_cast.mpr hn1)
  by_contra hnone
  let x := ((2827 / 10000 : ℝ) / (21 / 10)) * (Real.log n) ^ 2
  have hcut : (21 / 10 : ℝ) * x = (2827 / 10000 : ℝ) * (Real.log n) ^ 2 := by
    dsimp only [x]
    ring
  have hpass :
    ∀ r : ℕ,
      r.Prime → (r : ℝ) ≤ (21 / 10 : ℝ) * x → PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
    intro r hr hb
    rw [hcut] at hb
    by_contra hfail
    exact hnone ⟨r, hr, hb, hfail⟩
  have hcmp :=
    gaussian_inequality_of_prime_passes_in_subgroup hnlarge hnOdd H hHpass hGRH hx
      (by norm_num only : (0 : ℝ) ≤ 21 / 10) hpass
  exact gaussianNextTriple_contradiction H hi hC hL hE hcmp

/-- At log n>=2 trillion the new triple numerical bounds close the actual Gaussian
index-four conductor-saving branch at coefficient 0.2827. -/
theorem exists_prime_gaussianNextConductor {n : ℕ} [NeZero n] (hnlarge : 20000 ≤ n) (ho : Odd n)
    (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n)
    (hL : (2000000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (2827 / 10000 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hsmall : (225000000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hx :=
    (by norm_num only : (4 : ℝ) ≤ 3 ^ 16).trans
      (Analysis.gaussianNextTripleScale_ge_three_pow_sixteen hsmall)
  have hE := Analysis.gaussianNextTriple_error_budget hL (le_refl (Real.log n))
  apply exists_prime_gaussianNextIndexFour hnlarge ho H hi hpass hGRH hC
  · dsimp only [Analysis.gaussianNextTripleScale] at hx
    norm_num only at hx ⊢
    exact hx
  · dsimp only [Analysis.gaussianNextTripleScale] at hE
    norm_num only at hE ⊢
    exact hE

/-- The uniform three-prime Korselt case satisfies the new coefficient from log n>=2 trillion.
Enumerate its three factors, derive the arithmetic conductor-saving subgroup, and use
its actual Gaussian comparison with the newly certified scale. -/
theorem exists_prime_gaussianNextTriple {n : ℕ} (ho : Odd n) (hsf : Squarefree n)
    (hc : n.primeFactors.card = 3) (hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1)
    (hU :
      ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (2000000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (2827 / 10000 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨ho.pos.ne'⟩
  obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ := Finset.card_eq_three.mp hc
  have hpMem : p ∈ n.primeFactors := hset ▸ Finset.mem_insert_self p _
  have hqMem : q ∈ n.primeFactors := hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self q _)
  have hrMem : r ∈ n.primeFactors :=
    hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self r))
  have hp := (Nat.mem_primeFactors.mp hpMem).1
  have hq := (Nat.mem_primeFactors.mp hqMem).1
  have hr := (Nat.mem_primeFactors.mp hrMem).1
  have hpn := (Nat.mem_primeFactors.mp hpMem).2.1
  have hqn := (Nat.mem_primeFactors.mp hqMem).2.1
  have hrn := (Nat.mem_primeFactors.mp hrMem).2.1
  have hprod := (Nat.prod_primeFactors_of_squarefree hsf).symm
  rw [hset] at hprod
  have hnprod : n = p * q * r := by
    simpa only [Finset.prod_insert, Finset.prod_singleton, Finset.mem_insert, Finset.mem_singleton,
      hpq, hpr, hqr, or_self, not_false_eq_true, mul_assoc] using hprod
  obtain ⟨H, hi, hpass, hC⟩ :=
    three_prime_korselt_conductor_subgroup_data hp hq hr
      (hp.odd_of_ne_two (ho.ne_two_of_dvd_nat hpn)) (hq.odd_of_ne_two (ho.ne_two_of_dvd_nat hqn))
      (hr.odd_of_ne_two (ho.ne_two_of_dvd_nat hrn)) hpq hpr hqr hnprod (hK p hp hpn) (hK q hq hqn)
      (hK r hr hrn) (hU p q hp hq hpn hqn) (hU p r hp hr hpn hrn)
  have hnlarge : 20000 ≤ n := by
    have hl := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr ho.pos)
    exact_mod_cast (show (20000 : ℝ) ≤ n by linarith only [hl, hL])
  exact exists_prime_gaussianNextConductor hnlarge ho H hi hpass hGRH hC.le hL

end PseudoPrime.PrimeTestBounds.MillerRabin
