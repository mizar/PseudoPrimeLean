/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.TriangularProfiles
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularRefinedBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianRelativeProfileBounds

/-! # Actual rejecting primes for rational triangular profiles -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For a certified profile, q²<=10¹² n and log n>=T imply that the local
subgroup cutoff is at most C(log n)². The logarithmic size inequality gives
log q<(log n+28)/2; the profile's local budget controls the additive constant. -/
theorem triangularProfile_local (f : Analysis.TriangularProfile) {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
    (hsize : q ^ 2 ≤ 10 ^ 12 * n) (hL : f.T ≤ Real.log n) :
    max (3000 : ℝ) (Real.log q ^ 2) ≤ f.C * Real.log n ^ 2 := by
  have hR : (q : ℝ) ^ 2 ≤ (10 : ℝ) ^ 12 * n := by exact_mod_cast hsize
  have hl := Real.log_le_log (pow_pos (Nat.cast_pos.mpr hq) 2) hR
  rw [Real.log_pow, Real.log_mul (pow_ne_zero _ (by norm_num only)) (Nat.cast_pos.mpr hn).ne',
    Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hLp : 0 < Real.log n := by linarith only [hL, f.entry]
  have ha : 0 < f.a := by linarith only [f.root]
  have hmul := mul_le_mul_of_nonneg_left hL (by linarith only [f.root] : (0 : ℝ) ≤ f.a - 1 / 2)
  have hcap : Real.log q ≤ f.a * Real.log n := by
    nlinarith only [hl, Analysis.log_ten_lt_seven_thirds, f.localBudget, hmul]
  have hp : 0 ≤ f.a * Real.log n := mul_nonneg ha.le hLp.le
  have hs := (sq_le_sq₀ (Real.log_natCast_nonneg q) hp).mpr hcap
  have hsq := mul_le_mul_of_nonneg_right f.square (sq_nonneg (Real.log n))
  have hbase : (1 / 4 : ℝ) ≤ f.C := by nlinarith only [f.root, f.square]
  have hc := mul_le_mul_of_nonneg_right hbase (sq_nonneg (Real.log n))
  apply max_le
  · nlinarith only [hc, hL, f.entry]
  · nlinarith only [hs, hsq]

/-- The generic signed gap gives an actual rejecting prime in the large-index
branch. A factor prime is nonunit; a subgroup-external prime cannot pass MR. -/
theorem exists_prime_triangularProfileIndex (f : Analysis.TriangularProfile) {n : ℕ} [NeZero n]
    (hn : 1 < n) (ho : Odd n) (hi : 1000000000000 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : f.T ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ f.C * Real.log n ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hiR : (1000000000000 : ℝ) ≤ ((PrimeTest.fermatSubgroup n).index : ℝ) := by exact_mod_cast hi
  obtain ⟨p, hp, hb, hout⟩ :=
    LLS.PaperStatements.exists_prime_factor_or_outside_of_triangular18_signed_gap
      (PrimeTest.fermatSubgroup n) hGRH (Analysis.triangularProfile_roots f hL).1
      (Analysis.triangularProfile_gap f hL hiR)
  refine ⟨p, hp, hb, ?_⟩
  intro hpass
  rcases hout with hd | hout
  · have hcop :=
      (ZMod.isUnit_iff_coprime p n).mp (PrimeTest.strongMillerRabinPass_isUnit hn ho hpass)
    exact (hp.coprime_iff_not_dvd.mp hcop) hd
  · exact hout (PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn ho hpass)

/-- Uniform squarefree Korselt triples satisfy each triangular profile cutoff.
The first seven profiles use the new common relative certificate, while the
last uses the sharper certificate at its actual scale and entrance. -/
theorem triangularProfile_triple (f : Analysis.TriangularProfile) {n : ℕ} (hnOdd : Odd n)
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
  · have hentry : Analysis.gaussianRelativeCommon.T ≤ Real.log n := f.entry.trans hL
    obtain ⟨p, hp, hb, hr⟩ :=
      gaussianProfile_witness_card Analysis.gaussianRelativeCommon hnOdd hsf hc hK hU hnlarge hGRH
        hentry
    refine ⟨p, hp, hb.trans ?_, hr⟩
    exact mul_le_mul_of_nonneg_right hcommon (sq_nonneg (Real.log n))
  · have hentry : Analysis.gaussianRelativeSharper.T ≤ Real.log n := hsharp.2.trans hL
    obtain ⟨p, hp, hb, hr⟩ :=
      gaussianProfile_witness_card Analysis.gaussianRelativeSharper hnOdd hsf hc hK hU hnlarge hGRH
        hentry
    refine ⟨p, hp, hb.trans ?_, hr⟩
    exact mul_le_mul_of_nonneg_right hsharp.1 (sq_nonneg (Real.log n))

/-- Under GRH, every odd composite n>1 above a certified profile entrance has
an actual rejecting prime at most C(log n)². The index-10¹² classification is
exhaustive: transfer the local cutoff, use the actual relative triple bound,
or apply the signed large-index gap. No factorization hypotheses remain. -/
theorem exists_prime_triangularProfile (f : Analysis.TriangularProfile) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : f.T ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ f.C * Real.log n ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  by_cases hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 12
  · have h36 : 10 ^ 36 ≤ n :=
      decimal_le_of_log_upper (Nat.zero_lt_of_lt hn)
        (by
          norm_num only [Nat.cast_ofNat]; linarith only [hL, f.entry])
    have hJ : (10 ^ 12 : ℕ) ^ 3 ≤ n := by simpa only [← pow_mul, Nat.reduceMul] using h36
    rcases
      finite_index_local_subgroup_or_uniform_korselt_triple hn ho hc (PrimeTest.fermatSubgroup n)
        le_rfl (by norm_num only : 1 ≤ 10 ^ 12) hJ hi with
      hl | ht
    · obtain ⟨q, hq, hqn, hsize, K, hK, hpass⟩ := hl
      have hqp : 0 < q := (by norm_num only : 0 < 2).trans_le hq
      let : NeZero q := ⟨hqp.ne'⟩
      obtain ⟨p, hp, hb, hr⟩ :=
        exists_prime_witness_le_local_subgroup_envelope hn ho hq hqn K hK hpass hGRH
      exact ⟨p, hp, hb.trans (triangularProfile_local f (Nat.zero_lt_of_lt hn) hqp hsize hL), hr⟩
    · have hnlarge : 20000 ≤ n := (by norm_num only : 20000 ≤ 10 ^ 36).trans h36
      exact triangularProfile_triple f ho ht.1 ht.2.1 ht.2.2.1 ht.2.2.2 hnlarge hGRH hL
  · exact
      exists_prime_triangularProfileIndex f hn ho (by exact_mod_cast (lt_of_not_ge hi).le) hGRH hL

/-- The least rejecting prime satisfies the same profile bound. Extract the
least element from the actual all-odd-composite prime-witness theorem. -/
theorem exists_least_triangularProfile (f : Analysis.TriangularProfile) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
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
