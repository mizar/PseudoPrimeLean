/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.JointSurplusEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.JointSurplusThresholds
public import PseudoPrime.PrimeTestBounds.MillerRabin.FiniteIndexClassification
public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEvenAnchors
public import PseudoPrime.PrimeTestBounds.MillerRabin.MRLocalCutoffNumerics
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSurplusIndex
public import PseudoPrime.PrimeTestBounds.MillerRabin.TotalFactorWitnessBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.MixedTwoAdicLogBounds

/-! # Existing high-scale witness for the 0.30 target -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The exceptional squarefree Korselt triple with uniform predecessor valuations.
This predicate packages the arithmetic alternative in the finite-index classification
for use in the nonexceptional witness branch. -/
def UniformKorseltTriple (n : ℕ) : Prop :=
  Squarefree n ∧
    n.primeFactors.card = 3 ∧
    (∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1) ∧
    (∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))

/-- Under GRH, an odd composite with at least four prime factors counted
with multiplicity has a rejecting prime within the 0.30 cutoff. The existing
total-factor estimate has coefficient at most one quarter. -/
theorem exists_prime_reject_03_four_factors {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hk : 4 ≤ ArithmeticFunction.cardFactors n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hf⟩ := exists_prime_witness_le_cardFactors_log_sq hn ho hc hGRH
  have hkR : (4 : ℝ) ≤ ArithmeticFunction.cardFactors n := by exact_mod_cast hk
  have hden : (16 : ℝ) ≤ (ArithmeticFunction.cardFactors n : ℝ) ^ 2 := by nlinarith only [hkR]
  have hcoef : (4 : ℝ) / (ArithmeticFunction.cardFactors n : ℝ) ^ 2 ≤ 3 / 10 := by
    apply (div_le_iff₀ (by linarith only [hden])).2
    nlinarith only [hden]
  exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩

/-- Under GRH, an odd input with at least three distinct prime factors has a
0.30 rejecting prime if a prime factor violates Korselt divisibility or two
predecessor valuations differ. The marked-factor coefficient is at most one quarter. -/
theorem exists_prime_reject_03_local_factor {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : 3 ≤ n.primeFactors.card)
    (hlocal :
      (∃ r ∈ n.primeFactors, ∃ s ∈ n.primeFactors, padicValNat 2 (s - 1) < padicValNat 2 (r - 1)) ∨
        ∃ r ∈ n.primeFactors, ¬r - 1 ∣ n - 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hf, hb, _⟩ := exists_leastWitness_le_local_factor_coefficient hn ho hc hlocal hGRH
  have hcR : (3 : ℝ) ≤ n.primeFactors.card := by exact_mod_cast hc
  have hden : (16 : ℝ) ≤ ((n.primeFactors.card : ℝ) + 1) ^ 2 := by nlinarith only [hcR]
  have hcoef : (4 : ℝ) / ((n.primeFactors.card : ℝ) + 1) ^ 2 ≤ 3 / 10 := by
    apply (div_le_iff₀ (by linarith only [hden])).2
    nlinarith only [hden]
  exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩

/-- Under GRH, a squarefree odd input with exactly three distinct prime
factors has a 0.30 rejecting prime unless it is a uniform Korselt triple.
Negating the exceptional conditions supplies a marked local factor. -/
theorem exists_prime_reject_03_nonuniform_three {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hsf : Squarefree n) (hc : n.primeFactors.card = 3) (hu : ¬UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  classical
  have hlocal :
    (∃ r ∈ n.primeFactors, ∃ s ∈ n.primeFactors, padicValNat 2 (s - 1) < padicValNat 2 (r - 1)) ∨
      ∃ r ∈ n.primeFactors, ¬r - 1 ∣ n - 1 := by
    by_contra h
    have hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1 := by
      intro p hp hd
      by_contra hbad
      exact h (Or.inr ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hd, Nat.ne_zero_of_lt hn⟩, hbad⟩)
    have hV :
      ∀ p q : ℕ,
        p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1) := by
      intro p q hp hq hpd hqd
      have hpm := Nat.mem_primeFactors.mpr ⟨hp, hpd, Nat.ne_zero_of_lt hn⟩
      have hqm := Nat.mem_primeFactors.mpr ⟨hq, hqd, Nat.ne_zero_of_lt hn⟩
      apply le_antisymm
      · exact Nat.le_of_not_gt (fun hv ↦ h (Or.inl ⟨p, hpm, q, hqm, hv⟩))
      · exact Nat.le_of_not_gt (fun hv ↦ h (Or.inl ⟨q, hqm, p, hpm, hv⟩))
    exact hu ⟨hsf, hc, hK, hV⟩
  exact exists_prime_reject_03_local_factor hn ho (hc.ge) hlocal hGRH

/-- Under GRH, a proper local subgroup at a divisor whose square is at most
`10^9 * n` yields a 0.30 rejecting prime from logarithmic scale 100. The
certified radius-48 correction absorbs the local modulus bound. -/
theorem exists_prime_reject_03_local100 {n q : ℕ} [NeZero q] (hn : 1 < n) (ho : Odd n) (hq : 0 < q)
    (hqn : q ∣ n) (hsize : q ^ 2 ≤ 10 ^ 9 * n) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (100 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hm : ((48 : ℚ), (579107 / 100000 : ℚ), 6) ∈ localEvenAnchors := by decide +kernel
  have hs := local_log_le_of_square_le (Nat.zero_lt_of_lt hn) hq hsize
  obtain ⟨p, hp, hb, hf⟩ := exists_prime_reject_of_local_anchor hn ho hqn H hH hpass hGRH hm hs
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hb
  have h10 := log_ten_lt_seven_thirds
  have hmax :
    max (48 : ℝ) ((Real.log n + 9 * Real.log 10) / 2 - 579107 / 100000) ≤
      (5477 / 10000 : ℝ) * Real.log n := by
    apply max_le
    · linarith only [hL]
    · linarith only [hL, h10]
  have hnonneg : 0 ≤ max (48 : ℝ) ((Real.log n + 9 * Real.log 10) / 2 - 579107 / 100000) :=
    le_trans (by norm_num only) (le_max_left _ _)
  have hsquare := mul_self_le_mul_self hnonneg hmax
  have hLsq := sq_nonneg (Real.log n)
  have hfinal :
    (max (48 : ℝ) ((Real.log n + 9 * Real.log 10) / 2 - 579107 / 100000)) ^ 2 ≤
      (3 / 10 : ℝ) * (Real.log n) ^ 2 := by
    nlinarith only [hsquare, hLsq]
  exact ⟨p, hp, hb.trans hfinal, hf⟩

/-- Under GRH, a nonexceptional odd composite at logarithmic scale at least 240
has a 0.30 witness when a subgroup of its Fermat subgroup has index at most
`10^9`. The arithmetic classification rules out its remaining alternative. -/
theorem exists_prime_reject_03_low_index {n : ℕ} [NeZero n] (ho : Odd n) (hc : ¬n.Prime)
    (H : Subgroup (ZMod n)ˣ) (hH : H ≤ PrimeTest.fermatSubgroup n) (hi : H.index ≤ 10 ^ 9)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (240 : ℝ) ≤ Real.log n)
    (hU : ¬UniformKorseltTriple n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
  (witness_or_uniformKorselt_log240_GRH ho hc H hH hi hGRH hL).resolve_right hU

/-- At logarithmic scale 100, the input exceeds the cube of the finite-index
threshold. The elementary bound on `log 10` supplies the comparison. -/
theorem ten_pow_27_le_of_log100 {n : ℕ} [NeZero n] (hL : (100 : ℝ) ≤ Real.log n) : 10 ^ 27 ≤ n := by
  by_contra hnot
  have hsmall : n < 10 ^ 27 := Nat.lt_of_not_ge hnot
  have hcast : (n : ℝ) < (10 : ℝ) ^ 27 := by exact_mod_cast hsmall
  have hlogsmall := Real.log_lt_log (Nat.cast_pos.mpr (NeZero.pos n)) hcast
  have hlog27 : Real.log ((10 : ℝ) ^ 27) < 100 := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [log_ten_lt_seven_thirds]
  exact (not_lt_of_ge hL) (hlogsmall.trans hlog27)

/-- Under GRH, the finite-index classification and the radius-48 local
correction give a 0.30 witness for every nonexceptional odd composite from
logarithmic scale 100 when the subgroup index is at most `10^9`. -/
theorem exists_prime_reject_03_low_index100 {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (H : Subgroup (ZMod n)ˣ) (hH : H ≤ PrimeTest.fermatSubgroup n)
    (hi : H.index ≤ 10 ^ 9) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (100 : ℝ) ≤ Real.log n) (hU : ¬UniformKorseltTriple n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hJ : (1 : ℕ) ≤ 10 ^ 9 := by norm_num only
  have hJ3 : (10 ^ 9 : ℕ) ^ 3 ≤ n := by
    norm_num only [show (10 ^ 9 : ℕ) ^ 3 = 10 ^ 27 by norm_num only]
    exact ten_pow_27_le_of_log100 hL
  rcases localSubgroup_or_uniformKorseltTriple hn ho hc H hH hJ hJ3 hi with hlocal | htriple
  · obtain ⟨q, hq, hqn, hsize, K, hproper, hpass⟩ := hlocal
    let : NeZero q := ⟨Nat.ne_zero_of_lt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    exact
      exists_prime_reject_03_local100 hn ho (lt_of_lt_of_le (by decide : 0 < 2) hq) hqn hsize K
        hproper hpass hGRH hL
  · exact False.elim (hU htriple)

/-- A positive triangular joint gap at a cutoff inside the kernel support
gives a rejecting prime for an odd input under GRH. A prime dividing the input
and a prime outside its Fermat subgroup both reject the original input. -/
theorem exists_prime_reject_triangular {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n)
    (hi : 1000000000 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 16 ≤ x)
    (hu : x ≤ Real.exp 36)
    (hgap :
      300000000 * (Real.sqrt x + Real.sqrt x⁻¹) +
          1300000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
          602600000 +
          (((PrimeTest.fermatSubgroup n).index : ℝ) - 1) * ((72 - Real.log x) * Real.log n) <
        ((PrimeTest.fermatSubgroup n).index : ℝ) *
          ((220 - 4 * Real.log x) * Real.sqrt x -
            (1064 / 5 - (19 / 5 : ℝ) * Real.log x) * x ^ (1 / 4 : ℝ) -
            855)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let H := PrimeTest.fermatSubgroup n
  have hiR : (1000000000 : ℝ) ≤ (H.index : ℝ) := by exact_mod_cast hi
  obtain ⟨p, hp, hb, hout⟩ :=
    LLS.PaperStatements.exists_prime_joint_interior H hGRH hx hu (by linarith only [hiR]) hgap
  refine ⟨p, hp, hb, ?_⟩
  intro hpass
  rcases hout with hd | hout
  · have hcop :=
      (ZMod.isUnit_iff_coprime p n).mp (PrimeTest.strongMillerRabinPass_isUnit hn ho hpass)
    exact (hp.coprime_iff_not_dvd.mp hcop) hd
  · exact hout (PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn ho hpass)

/-- The rational bounds for logarithm, roots, and index imply the strict
triangular joint gap on the scale beginning at 100. This algebraic certificate
is independent of the construction of those bounds. -/
theorem triangular_gap_03_scalar (L z r y ri yi I : ℝ) (hL : 100 ≤ L) (hz1 : 8 ≤ z) (hz2 : z ≤ 17)
    (hr1 : (5477 / 10000 : ℝ) * L ≤ r) (hr2 : r ≤ (548 / 1000 : ℝ) * L) (hy : y ≤ (3 / 40 : ℝ) * L)
    (hy0 : 0 ≤ y) (hri : ri ≤ 1) (hyi : yi ≤ 1) (hI : 1000000000 ≤ I) :
    300000000 * (r + ri) + 1300000 * (y + yi) + 602600000 + (I - 1) * ((72 - z) * L) <
      I * ((220 - 4 * z) * r - (1064 / 5 - (19 / 5 : ℝ) * z) * y - 855) := by
  have hA : 0 ≤ (17 - z) * r := mul_nonneg (by linarith only [hz2]) (by linarith only [hL, hr1])
  have hB : 0 ≤ (z - 8) * y := mul_nonneg (by linarith only [hz1]) hy0
  have hC : 0 ≤ (z - 8) * L := mul_nonneg (by linarith only [hz1]) (by linarith only [hL])
  have hD : 0 ≤ (I - 1) * ((z - 8) * L) := mul_nonneg (by linarith only [hI]) hC
  have hE : 0 ≤ I * ((17 - z) * r) := mul_nonneg (by linarith only [hI]) hA
  have hF : 0 ≤ I * ((z - 8) * y) := mul_nonneg (by linarith only [hI]) hB
  have hG : 0 ≤ I * (r - (5477 / 10000 : ℝ) * L) :=
    mul_nonneg (by linarith only [hI]) (by linarith only [hr1])
  have hH : 0 ≤ I * ((3 / 40 : ℝ) * L - y) :=
    mul_nonneg (by linarith only [hI]) (by linarith only [hy])
  have hK : 0 ≤ (I - 1000000000) * (L - 100) :=
    mul_nonneg (by linarith only [hI]) (by linarith only [hL])
  nlinarith only [hD, hE, hF, hG, hH, hK, hI, hL, hr2, hy, hri, hyi]

/-- The 0.30 quadratic cutoff is at least 16 at scale 100. Its square root
lies between two rational multiples of the scale and its fourth root is at
most `3L/40`; square comparison supplies the numerical gap bounds. -/
theorem triangular_03_roots {L : ℝ} (hL : 100 ≤ L) :
    let x := (3 / 10 : ℝ) * L ^ 2
    16 ≤ x ∧
      (5477 / 10000 : ℝ) * L ≤ Real.sqrt x ∧
      Real.sqrt x ≤ (548 / 1000 : ℝ) * L ∧ x ^ (1 / 4 : ℝ) ≤ (3 / 40 : ℝ) * L := by
  let x := (3 / 10 : ℝ) * L ^ 2
  have hLp : 0 < L := by linarith only [hL]
  have hx : 16 ≤ x := by
    dsimp only [x]; nlinarith only [hL]
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hcl : (5477 / 10000 : ℝ) ^ 2 ≤ 3 / 10 := by norm_num only
  have hcu : (3 / 10 : ℝ) ≤ (548 / 1000 : ℝ) ^ 2 := by norm_num only
  have hcl' := mul_le_mul_of_nonneg_right hcl (sq_nonneg L)
  have hcu' := mul_le_mul_of_nonneg_right hcu (sq_nonneg L)
  have hl : (5477 / 10000 : ℝ) * L ≤ Real.sqrt x := by
    apply (Real.le_sqrt (by linarith only [hL]) hx0).2
    dsimp only [x]
    nlinarith only [hcl']
  have hu : Real.sqrt x ≤ (548 / 1000 : ℝ) * L := by
    apply (Real.sqrt_le_iff).2
    constructor
    · linarith only [hL]
    · dsimp only [x]
      nlinarith only [hcu']
  have ht : (x ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt x := by
    have he := Real.rpow_mul hx0 (1 / 4) 2
    norm_num only [Real.rpow_two] at he
    rw [Real.sqrt_eq_rpow]
    exact he.symm
  have hpow := mul_le_mul_of_nonneg_right hL hLp.le
  have hquarter : x ^ (1 / 4 : ℝ) ≤ (3 / 40 : ℝ) * L := by
    have hp := Real.rpow_nonneg hx0 (1 / 4)
    nlinarith only [ht, hu, hpow, hp, hLp]
  exact ⟨hx, hl, hu, hquarter⟩

/-- Between scales 100 and 6500, the logarithm of the quadratic cutoff lies
between 8 and 17, and the cutoff lies inside the triangular support. Exact
rational logarithm certificates and monotonicity give both endpoints. -/
theorem triangular_03_logs {L : ℝ} (hL : 100 ≤ L) (hU : L ≤ 6500) :
    let x := (3 / 10 : ℝ) * L ^ 2
    8 ≤ Real.log x ∧ Real.log x ≤ 17 ∧ x ≤ Real.exp 36 := by
  let x := (3 / 10 : ℝ) * L ^ 2
  have hlo : (3000 : ℝ) ≤ x := by
    dsimp only [x]; nlinarith only [hL]
  have hhi : x ≤ (12675000 : ℝ) := by
    dsimp only [x]; nlinarith only [hL, hU]
  have hc1 : Analysis.rationalLogIntervalCheck 3000 12 16 8 9 = true := by decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 12675000 24 16 16 17 = true := by decide +kernel
  have hl := (Analysis.rationalLogIntervalCheck_sound hc1).1
  have hu := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_ofNat] at hl hu
  have hxpos : 0 < x := by linarith only [hlo]
  have hlx : 8 ≤ Real.log x := hl.trans (Real.log_le_log (by norm_num only) hlo)
  have hux : Real.log x ≤ 17 := (Real.log_le_log hxpos hhi).trans hu
  have hex : x ≤ Real.exp 36 := (Real.log_le_iff_le_exp hxpos).mp (by linarith only [hux])
  exact ⟨hlx, hux, hex⟩

/-- Under GRH, an odd input whose Fermat index is at least `10^9` has a
0.30 rejecting prime throughout logarithmic scales 100 to 6500. The root and
logarithm bounds establish the strict triangular gap at the target cutoff. -/
theorem exists_prime_reject_03_high_index {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n)
    (hi : 1000000000 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (100 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 6500) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let L := Real.log n
  let x := (3 / 10 : ℝ) * L ^ 2
  have roots := triangular_03_roots hL
  have logs := triangular_03_logs hL hU
  change
    16 ≤ x ∧
      (5477 / 10000 : ℝ) * L ≤ Real.sqrt x ∧
      Real.sqrt x ≤ (548 / 1000 : ℝ) * L ∧ x ^ (1 / 4 : ℝ) ≤ (3 / 40 : ℝ) * L at roots
  change 8 ≤ Real.log x ∧ Real.log x ≤ 17 ∧ x ≤ Real.exp 36 at logs
  have hx1 : 1 ≤ x := by linarith only [roots.1]
  have hinv : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx1
  have hri : Real.sqrt x⁻¹ ≤ 1 := Real.sqrt_le_one.mpr hinv
  have hyi : (x⁻¹) ^ (1 / 4 : ℝ) ≤ 1 :=
    Real.rpow_le_one (inv_nonneg.mpr (by linarith only [hx1])) hinv (by norm_num only)
  have hiR : (1000000000 : ℝ) ≤ ((PrimeTest.fermatSubgroup n).index : ℝ) := by exact_mod_cast hi
  have hgap :=
    triangular_gap_03_scalar L (Real.log x) (Real.sqrt x) (x ^ (1 / 4 : ℝ)) (Real.sqrt x⁻¹)
      ((x⁻¹) ^ (1 / 4 : ℝ)) ((PrimeTest.fermatSubgroup n).index : ℝ) hL logs.1 logs.2.1 roots.2.1
      roots.2.2.1 roots.2.2.2 (Real.rpow_nonneg (by linarith only [hx1]) _) hri hyi hiR
  exact exists_prime_reject_triangular hn ho hi hGRH roots.1 logs.2.2 hgap

/-- Under GRH, every odd composite with logarithm at least 6500 has a rejecting
prime below the 0.30 target. The global least-prime bound and its numerical
threshold provide the high-scale branch for the finite-scale construction. -/
theorem exists_prime_reject_03_log6500 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (6500 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
  ⟨compositeLeastPrime n, (compositeLeastPrime_spec hGRH hn ho hc).1,
    (jointSurplus_least_bound hn ho hc hGRH).trans (jointSurplus_lt_03 hL).le,
    (compositeLeastPrime_spec hGRH hn ho hc).2.1⟩

/-- Under GRH, every nonexceptional odd composite at logarithmic scale at
least 100 has a rejecting prime within the 0.30 cutoff. Split at Fermat index
`10^9` on the bounded scale and use the global estimate above scale 6500. -/
theorem exists_prime_reject_03_nonuniform100 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (100 : ℝ) ≤ Real.log n)
    (hU : ¬UniformKorseltTriple n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  by_cases hlarge : (6500 : ℝ) ≤ Real.log n
  · exact exists_prime_reject_03_log6500 hn ho hc hGRH hlarge
  · by_cases hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 9
    · exact
        exists_prime_reject_03_low_index100 hn ho hc (PrimeTest.fermatSubgroup n) le_rfl hi hGRH hL
          hU
    · exact
        exists_prime_reject_03_high_index hn ho (Nat.le_of_lt (Nat.lt_of_not_ge hi)) hGRH hL
          (le_of_not_ge hlarge)

end PseudoPrime.PrimeTestBounds.MillerRabin
