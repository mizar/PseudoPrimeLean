/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularProfiles
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularRefinedBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianRelativeProfileBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularCoreBounds

/-! # Actual rejecting primes for rational triangular profiles -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For a certified profile, q²<=10¹² n and log n>=T imply that the local
subgroup cutoff is at most C(log n)². The logarithmic size inequality gives
log q<(log n+28)/2; the profile's local budget controls the additive constant. -/
theorem triangularProfile_local (f : TriangularProfile) {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
    (hsize : q ^ 2 ≤ 10 ^ 12 * n) (hL : f.T ≤ Real.log n) :
    max (3000 : ℝ) (Real.log q ^ 2) ≤ f.C * Real.log n ^ 2 := by
  exact triangularCore_local (triangularProfileCore f) hn hq hsize hL

/-- The generic signed gap gives an actual rejecting prime in the large-index
branch. A factor prime is nonunit; a subgroup-external prime cannot pass MR. -/
theorem exists_prime_triangularProfileIndex (f : TriangularProfile) {n : ℕ} [NeZero n] (hn : 1 < n)
    (ho : Odd n) (hi : 1000000000000 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : f.T ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ f.C * Real.log n ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  exact exists_prime_triangularCoreIndex (triangularProfileCore f) hn ho hi hGRH hL

/-- Uniform squarefree Korselt triples satisfy each triangular profile cutoff.
The first seven profiles use the new common relative certificate, while the
last uses the sharper certificate at its actual scale and entrance. -/
theorem triangularProfile_triple (f : TriangularProfile) {n : ℕ} (hnOdd : Odd n)
    (hsf : Squarefree n) (hc : n.primeFactors.card = 3)
    (hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1)
    (hU :
      ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hnlarge : 20000 ≤ n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : f.T ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ f.C * Real.log n ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  rcases f.triple with hcommon | hsharp
  · have hentry : gaussianRelativeCommon.T ≤ Real.log n := f.entry.trans hL
    obtain ⟨p, hp, hb, hr⟩ :=
      gaussianProfile_witness_card gaussianRelativeCommon hnOdd hsf hc hK hU hnlarge hGRH hentry
    refine ⟨p, hp, hb.trans ?_, hr⟩
    exact mul_le_mul_of_nonneg_right hcommon (sq_nonneg (Real.log n))
  · have hentry : gaussianRelativeSharper.T ≤ Real.log n := hsharp.2.trans hL
    obtain ⟨p, hp, hb, hr⟩ :=
      gaussianProfile_witness_card gaussianRelativeSharper hnOdd hsf hc hK hU hnlarge hGRH hentry
    refine ⟨p, hp, hb.trans ?_, hr⟩
    exact mul_le_mul_of_nonneg_right hsharp.1 (sq_nonneg (Real.log n))

/-- Under GRH, every odd composite n>1 above a certified profile entrance has
an actual rejecting prime at most C(log n)². The index-10¹² classification is
exhaustive: transfer the local cutoff, use the actual relative triple bound,
or apply the signed large-index gap. No factorization hypotheses remain. -/
theorem exists_prime_triangularProfile (f : TriangularProfile) {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : f.T ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ f.C * Real.log n ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply exists_prime_triangularCore (triangularProfileCore f) hn ho hc hGRH hL
  intro hsf hcard hK hU
  have h36 : 10 ^ 36 ≤ n :=
    decimal_le_of_log_upper (Nat.zero_lt_of_lt hn)
      (by
        norm_num only [Nat.cast_ofNat]
        linarith only [hL, f.entry])
  have hnlarge : 20000 ≤ n := (by norm_num only : 20000 ≤ 10 ^ 36).trans h36
  exact triangularProfile_triple f ho hsf hcard hK hU hnlarge hGRH hL

/-- The least rejecting prime satisfies the same profile bound. Extract the
least element from the actual all-odd-composite prime-witness theorem. -/
theorem exists_least_triangularProfile (f : TriangularProfile) {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : f.T ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ f.C * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact
    exists_least_prime_reject_of_exists_prime_reject
      (exists_prime_triangularProfile f hn ho hc hGRH hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
