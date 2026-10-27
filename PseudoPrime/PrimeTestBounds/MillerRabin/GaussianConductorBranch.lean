/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianWitnessBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianVariableWitnessBounds
public import PseudoPrime.Analysis.GaussianTripleNumerics
public import PseudoPrime.LLS.ThreeConductorSum
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaIndex100GaussianClosure

/-! # Gaussian index-four branch with a two-log conductor cost

Connect the actual subgroup comparison to coefficient 282924/1000000 while retaining
the arithmetic conductor-saving and explicit secondary-error hypotheses.
This is a branch interface, not the completed all-branches MR theorem.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For index four with conductor-log sum at most twice log n, the actual
fixed-cutoff Gaussian comparison contradicts a secondary error at most log(n)/5000.
Use the certified unnormalized denominator and the three-character coefficient gap;
the conductor term is not divided by three. This supplies the branch witness proof. -/
private theorem gaussian_triple_comparison_contradiction {n : ℕ} [NeZero n] (H : Subgroup (ZMod n)ˣ)
    (hi : H.index = 4) (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n)
    (hL : 0 < Real.log n)
    (hE :
      70 * (((282924 / 1000000 : ℝ) / (21 / 10)) * (Real.log n) ^ 2) ^ (1 / 4 : ℝ) +
          3 *
            LLS.PaperStatements.gaussianAmbientError n
              (((282924 / 1000000 : ℝ) / (21 / 10)) * (Real.log n) ^ 2) ≤
        (1 / 2500 : ℝ) * Real.log n / 2)
    (hcmp :
      ((H.index : ℝ) *
              (∫ u in (0 : ℝ)..(21 / 10 : ℝ),
                (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
            Real.exp (1 / 16 : ℝ)) *
          Real.sqrt (((282924 / 1000000 : ℝ) / (21 / 10)) * (Real.log n) ^ 2) ≤
        (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
          14 * ((H.index : ℝ) + 1) *
            (((282924 / 1000000 : ℝ) / (21 / 10)) * (Real.log n) ^ 2) ^ (1 / 4 : ℝ) +
          ((H.index - 1 : ℕ) : ℝ) *
            LLS.PaperStatements.gaussianAmbientError n
              (((282924 / 1000000 : ℝ) / (21 / 10)) * (Real.log n) ^ 2)) :
    False := by
  rw [hi] at hcmp
  norm_num only [Nat.cast_ofNat] at hcmp
  have hd := LLS.gaussian_kernel_triple_denominator_le_at_fixed_cutoff
  have hd' :
    (21943 / 10000 : ℝ) ≤
      4 *
          (∫ u in (0 : ℝ)..(21 / 10 : ℝ),
            (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
        (LLS.PaperStatements.gaussianGammaMellinKernel.function (1 / 2)).re := by
    exact (by norm_num only : (21943 / 10000 : ℝ) ≤ 10971611 / 5000000).trans hd
  have he :
    (LLS.PaperStatements.gaussianGammaMellinKernel.function (1 / 2)).re = Real.exp (1 / 16 : ℝ) :=
    Analysis.gaussianGammaFunction_endpoint
  rw [he] at hd'
  have hm :=
    mul_le_mul_of_nonneg_right hd'
      (Real.sqrt_nonneg (((282924 / 1000000 : ℝ) / (21 / 10)) * (Real.log n) ^ 2))
  have hc := mul_le_mul_of_nonneg_left hC (by norm_num only : (0 : ℝ) ≤ 161 / 400)
  have hs := LLS.gaussian_three_character_main_term_lt_0282924 hL hE
  rw [show ((282924 / 1000000 : ℝ) / (21 / 10)) = 23577 / 175000 by norm_num only] at hm hs
  linarith only [hcmp, hm, hc, hs]

/-- Under GRH for odd n≥20000, an index-four subgroup containing all strong
passes and having conductor-log sum at most twice log n gives a prime failing
base at most (282924/1000000)log(n)², provided the scale is at least four and its actual
secondary error is at most log(n)/5000. These remaining hypotheses are explicit;
arithmetic classification and a numerical starting value must discharge them
before this branch can be used in the final all-branches theorem. -/
theorem exists_prime_witness_le_gaussian_of_index_four_conductor_saving {n : ℕ} [NeZero n]
    (hnlarge : 20000 ≤ n) (hnOdd : Odd n) (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n)
    (hx : 4 ≤ ((282924 / 1000000 : ℝ) / (21 / 10)) * (Real.log n) ^ 2)
    (hE :
      70 * (((282924 / 1000000 : ℝ) / (21 / 10)) * (Real.log n) ^ 2) ^ (1 / 4 : ℝ) +
          3 *
            LLS.PaperStatements.gaussianAmbientError n
              (((282924 / 1000000 : ℝ) / (21 / 10)) * (Real.log n) ^ 2) ≤
        (1 / 2500 : ℝ) * Real.log n / 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (282924 / 1000000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  classical
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 20000) hnlarge
  have hL : 0 < Real.log n := Real.log_pos (Nat.one_lt_cast.mpr hn1)
  by_contra hnone
  let x := ((282924 / 1000000 : ℝ) / (21 / 10)) * (Real.log n) ^ 2
  have hcut : (21 / 10 : ℝ) * x = (282924 / 1000000 : ℝ) * (Real.log n) ^ 2 := by
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
  exact gaussian_triple_comparison_contradiction H hi hC hL hE hcmp

/-- Under GRH, an odd n≥10^434782608696 and a supplied index-four subgroup
containing all strong passes with conductor-log sum at most twice log n give
a prime failing base at most (282924/1000000)log(n)². The decimal cutoff certifies
scale and error conditions internally. Only the arithmetic subgroup and conductor
conditions remain for the classification stage of the all-branches theorem. -/
theorem exists_prime_witness_le_gaussian_0283_of_conductor_saving {n : ℕ} [NeZero n] (hnOdd : Odd n)
    (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n)
    (hn : 10 ^ 434782608696 ≤ n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (282924 / 1000000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hlog := Analysis.gaussianMR_log_of_decimal hn
  have hL : (1000000000000 : ℝ) ≤ Real.log n := by
    norm_num only [Nat.cast_ofNat] at hlog
    linarith only [hlog]
  have hu := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr (NeZero.pos n) : (0 : ℝ) < n)
  have hnlarge : 20000 ≤ n := by
    apply Nat.cast_le (α := ℝ).mp
    norm_num only [Nat.cast_ofNat]
    linarith only [hL, hu]
  have hsmall : (225000000 : ℝ) ≤ Real.log n :=
    (by norm_num only : (225000000 : ℝ) ≤ 1000000000000).trans hL
  have hx :=
    (by norm_num only : (4 : ℝ) ≤ 3 ^ 16).trans
      (Analysis.gaussianTripleScale_ge_three_pow_sixteen hsmall)
  have hE := Analysis.gaussianTriple_error_budget hL (le_refl (Real.log n))
  apply
    exists_prime_witness_le_gaussian_of_index_four_conductor_saving hnlarge hnOdd H hi hHpass hGRH
      hC
  · dsimp only [Analysis.gaussianTripleScale] at hx
    norm_num only at hx ⊢
    exact hx
  · dsimp only [Analysis.gaussianTripleScale] at hE
    norm_num only at hE ⊢
    exact hE

open Classical in
/-- Under GRH and the explicit Gaussian starting value, an exact three-character
classification of the nonprincipal annihilator with pairwise product conductors
gives coefficient 282924/1000000 for a prime failing MR base. Derive index four and the
two-log conductor sum from the classification rather than assuming these costs.
This is the integration endpoint for the remaining common-sign subgroup arithmetic. -/
theorem exists_prime_witness_le_gaussian_0283_of_three_conductors {n p q r : ℕ} [NeZero n]
    (hnOdd : Odd n) (H : Subgroup (ZMod n)ˣ)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (a b c : NumberTheory.subgroupAnnihilator H) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hs : Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H) = {a, b, c})
    (ha : a.val.conductor = p * q) (hb : b.val.conductor = p * r) (hc : c.val.conductor = q * r)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hn : n = p * q * r) (hN : 10 ^ 434782608696 ≤ n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ (282924 / 1000000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  have hi := LLS.PaperStatements.index_four_of_three_nonprincipal_annihilator H a b c hab hac hbc hs
  have hC :=
    LLS.PaperStatements.subgroupConductorLogSum_eq_twice_log_of_three_conductors H a b c hab hac hbc
      hs ha hb hc hp hq hr hn
  exact exists_prime_witness_le_gaussian_0283_of_conductor_saving hnOdd H hi hHpass hGRH hC.le hN

open Classical in
/-- Under GRH for three distinct positive prime factors, an exact classification
of the nonprincipal annihilator and its pairwise product conductors gives the
Gaussian coefficient 282924/1000000 witness at the explicit starting value. Derive
character distinctness from prime distinctness and use the classified branch.
The character enumeration and pass containment remain arithmetic inputs. -/
theorem exists_prime_witness_le_gaussian_0283_of_three_prime_conductors {n p q r : ℕ} [NeZero n]
    (hnOdd : Odd n) (H : Subgroup (ZMod n)ˣ)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (a b c : NumberTheory.subgroupAnnihilator H)
    (hs : Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H) = {a, b, c})
    (ha : a.val.conductor = p * q) (hb : b.val.conductor = p * r) (hc : c.val.conductor = q * r)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hn : n = p * q * r) (hN : 10 ^ 434782608696 ≤ n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ (282924 / 1000000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  obtain ⟨hab, hac, hbc⟩ :=
    LLS.PaperStatements.three_characters_ne_of_pairwise_product_conductors H a b c ha hb hc hp.pos
      hq.pos hr.pos hpq hpr hqr
  exact
    exists_prime_witness_le_gaussian_0283_of_three_conductors hnOdd H hHpass hGRH a b c hab hac hbc
      hs ha hb hc hp.pos hq.pos hr.pos hn hN

/-- At the explicit Gaussian threshold, three annihilator members with the
pairwise product conductors of distinct prime factors suffice for coefficient
282924/1000000 when the containing subgroup has index four. Nonprincipality, character
distinctness and complete enumeration follow from conductors and cardinality.
Only subgroup membership, index and pass containment remain arithmetic inputs. -/
theorem exists_prime_witness_le_gaussian_0283_of_three_annihilator_members {n p q r : ℕ} [NeZero n]
    (hnOdd : Odd n) (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (a b c : NumberTheory.subgroupAnnihilator H) (ha : a.val.conductor = p * q)
    (hb : b.val.conductor = p * r) (hc : c.val.conductor = q * r) (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hn : n = p * q * r)
    (hN : 10 ^ 434782608696 ≤ n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ (282924 / 1000000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  classical
  have hnon : ∀ d : NumberTheory.subgroupAnnihilator H, 1 < d.val.conductor → d ≠ 1 := by
    intro d hd he
    rw [he, Subgroup.coe_one, DirichletCharacter.conductor_one] at hd
    exact (lt_irrefl 1) hd
  have ha1 : a ≠ 1 := hnon a (ha ▸ hp.one_lt.trans_le (Nat.le_mul_of_pos_right p hq.pos))
  have hb1 : b ≠ 1 := hnon b (hb ▸ hp.one_lt.trans_le (Nat.le_mul_of_pos_right p hr.pos))
  have hc1 : c ≠ 1 := hnon c (hc ▸ hq.one_lt.trans_le (Nat.le_mul_of_pos_right q hr.pos))
  obtain ⟨hab, hac, hbc⟩ :=
    LLS.PaperStatements.three_characters_ne_of_pairwise_product_conductors H a b c ha hb hc hp.pos
      hq.pos hr.pos hpq hpr hqr
  have hs :=
    LLS.PaperStatements.nonprincipal_annihilator_eq_three_of_index_four H hi a b c ha1 hb1 hc1 hab
      hac hbc
  exact
    exists_prime_witness_le_gaussian_0283_of_three_prime_conductors hnOdd H hHpass hGRH a b c hs ha
      hb hc hp hq hr hpq hpr hqr hn hN

open Classical in
/-- Under GRH at scale `600`, three annihilator members with pairwise product
conductors give a witness below the classified Gaussian star bound. The
conductors determine index four and conductor cost `2 log n`. -/
theorem exists_prime_witness_le_gaussian_star_of_three_annihilator_members {n p q r : ℕ} [NeZero n]
    (hnlarge : 20000 ≤ n) (hnOdd : Odd n) (H : Subgroup (ZMod n)ˣ)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 600 ≤ Real.log n)
    (a b c : NumberTheory.subgroupAnnihilator H) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hs : Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H) = {a, b, c})
    (ha : a.val.conductor = p * q) (hb : b.val.conductor = p * r) (hc : c.val.conductor = q * r)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hn : n = p * q * r) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianMRStarBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  classical
  have hi := LLS.PaperStatements.index_four_of_three_nonprincipal_annihilator H a b c hab hac hbc hs
  have hC :=
    LLS.PaperStatements.subgroupConductorLogSum_eq_twice_log_of_three_conductors H a b c hab hac hbc
      hs ha hb hc hp hq hr hn
  exact exists_prime_witness_le_gaussian_star_of_index_four hnOdd hnlarge H hi hHpass hGRH hC.le hL

open Classical in
/-- Three pairwise prime-product annihilator conductors give the conductor
cost required to apply the Gamma index-100 witness bound from `L ≥ 330`. -/
theorem exists_prime_witness_le_gammaIndex100_of_three_annihilator_members {n p q r : ℕ} [NeZero n]
    (hnlarge : 20000 ≤ n) (hnOdd : Odd n) (H : Subgroup (ZMod n)ˣ)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 330 ≤ Real.log n)
    (a b c : NumberTheory.subgroupAnnihilator H) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hs : Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H) = {a, b, c})
    (ha : a.val.conductor = p * q) (hb : b.val.conductor = p * r) (hc : c.val.conductor = q * r)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hn : n = p * q * r) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ gammaIndex100Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  have hi := LLS.PaperStatements.index_four_of_three_nonprincipal_annihilator H a b c hab hac hbc hs
  have hC :=
    LLS.PaperStatements.subgroupConductorLogSum_eq_twice_log_of_three_conductors H a b c hab hac hbc
      hs ha hb hc hp hq hr hn
  exact
    exists_prime_witness_le_gammaIndex100_of_index_four_conductor hnlarge hnOdd H hi hHpass hGRH
      hC.le hL

open Classical in
/-- Pairwise product conductors identify the three nonprincipal annihilators
and supply the exact conductor sum for the Gamma index-100 cutoff. -/
theorem exists_prime_witness_le_gammaIndex100_of_three_annihilator_prime_members {n p q r : ℕ}
    [NeZero n] (hnlarge : 20000 ≤ n) (hnOdd : Odd n) (H : Subgroup (ZMod n)ˣ)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 330 ≤ Real.log n)
    (hi : H.index = 4) (a b c : NumberTheory.subgroupAnnihilator H) (ha : a.val.conductor = p * q)
    (hb : b.val.conductor = p * r) (hc : c.val.conductor = q * r) (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hn : n = p * q * r) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ gammaIndex100Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  have hnon : ∀ d : NumberTheory.subgroupAnnihilator H, 1 < d.val.conductor → d ≠ 1 := by
    intro d hd he
    rw [he, Subgroup.coe_one, DirichletCharacter.conductor_one] at hd
    exact (lt_irrefl 1) hd
  have ha1 : a ≠ 1 := hnon a (ha ▸ hp.one_lt.trans_le (Nat.le_mul_of_pos_right p hq.pos))
  have hb1 : b ≠ 1 := hnon b (hb ▸ hp.one_lt.trans_le (Nat.le_mul_of_pos_right p hr.pos))
  have hc1 : c ≠ 1 := hnon c (hc ▸ hq.one_lt.trans_le (Nat.le_mul_of_pos_right q hr.pos))
  obtain ⟨hab, hac, hbc⟩ :=
    LLS.PaperStatements.three_characters_ne_of_pairwise_product_conductors H a b c ha hb hc hp.pos
      hq.pos hr.pos hpq hpr hqr
  have hs :=
    LLS.PaperStatements.nonprincipal_annihilator_eq_three_of_index_four H hi a b c ha1 hb1 hc1 hab
      hac hbc
  exact
    exists_prime_witness_le_gammaIndex100_of_three_annihilator_members hnlarge hnOdd H hHpass hGRH
      hL a b c hab hac hbc hs ha hb hc hp.pos hq.pos hr.pos hn

open Classical in
/-- Pairwise product conductors give the conductor cost needed by the 6/5
Gaussian bound at scale 500. -/
theorem exists_prime_witness_le_gaussian6fifths_of_three_annihilator_members {n p q r : ℕ}
    [NeZero n] (hnlarge : 20000 ≤ n) (hnOdd : Odd n) (H : Subgroup (ZMod n)ˣ)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 500 ≤ Real.log n)
    (a b c : NumberTheory.subgroupAnnihilator H) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hs : Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H) = {a, b, c})
    (ha : a.val.conductor = p * q) (hb : b.val.conductor = p * r) (hc : c.val.conductor = q * r)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hn : n = p * q * r) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianMR6FifthsBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  classical
  have hi := LLS.PaperStatements.index_four_of_three_nonprincipal_annihilator H a b c hab hac hbc hs
  have hC :=
    LLS.PaperStatements.subgroupConductorLogSum_eq_twice_log_of_three_conductors H a b c hab hac hbc
      hs ha hb hc hp hq hr hn
  exact
    exists_prime_witness_le_gaussian6fifths_of_index_four hnOdd hnlarge H hi hHpass hGRH hC.le hL

open Classical in
/-- At index four, the pairwise prime-product conductors identify the three
nonprincipal annihilators and supply their exact conductor sum. -/
theorem exists_prime_witness_le_gaussian6fifths_of_three_annihilator_prime_members {n p q r : ℕ}
    [NeZero n] (hnlarge : 20000 ≤ n) (hnOdd : Odd n) (H : Subgroup (ZMod n)ˣ)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 500 ≤ Real.log n)
    (hi : H.index = 4) (a b c : NumberTheory.subgroupAnnihilator H) (ha : a.val.conductor = p * q)
    (hb : b.val.conductor = p * r) (hc : c.val.conductor = q * r) (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hn : n = p * q * r) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianMR6FifthsBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  have hnon : ∀ d : NumberTheory.subgroupAnnihilator H, 1 < d.val.conductor → d ≠ 1 := by
    intro d hd he
    rw [he, Subgroup.coe_one, DirichletCharacter.conductor_one] at hd
    exact (lt_irrefl 1) hd
  have ha1 : a ≠ 1 := hnon a (ha ▸ hp.one_lt.trans_le (Nat.le_mul_of_pos_right p hq.pos))
  have hb1 : b ≠ 1 := hnon b (hb ▸ hp.one_lt.trans_le (Nat.le_mul_of_pos_right p hr.pos))
  have hc1 : c ≠ 1 := hnon c (hc ▸ hq.one_lt.trans_le (Nat.le_mul_of_pos_right q hr.pos))
  obtain ⟨hab, hac, hbc⟩ :=
    LLS.PaperStatements.three_characters_ne_of_pairwise_product_conductors H a b c ha hb hc hp.pos
      hq.pos hr.pos hpq hpr hqr
  have hs :=
    LLS.PaperStatements.nonprincipal_annihilator_eq_three_of_index_four H hi a b c ha1 hb1 hc1 hab
      hac hbc
  exact
    exists_prime_witness_le_gaussian6fifths_of_three_annihilator_members hnlarge hnOdd H hHpass hGRH
      hL a b c hab hac hbc hs ha hb hc hp.pos hq.pos hr.pos hn

open Classical in
/-- For distinct prime factors, pairwise product conductors determine the
three nonprincipal annihilator characters needed by the Gaussian star branch. -/
theorem exists_prime_witness_le_gaussian_star_of_three_annihilator_prime_members {n p q r : ℕ}
    [NeZero n] (hnlarge : 20000 ≤ n) (hnOdd : Odd n) (H : Subgroup (ZMod n)ˣ)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 600 ≤ Real.log n)
    (hi : H.index = 4) (a b c : NumberTheory.subgroupAnnihilator H) (ha : a.val.conductor = p * q)
    (hb : b.val.conductor = p * r) (hc : c.val.conductor = q * r) (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hn : n = p * q * r) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianMRStarBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  have hnon : ∀ d : NumberTheory.subgroupAnnihilator H, 1 < d.val.conductor → d ≠ 1 := by
    intro d hd he
    rw [he, Subgroup.coe_one, DirichletCharacter.conductor_one] at hd
    exact (lt_irrefl 1) hd
  have ha1 : a ≠ 1 := hnon a (ha ▸ hp.one_lt.trans_le (Nat.le_mul_of_pos_right p hq.pos))
  have hb1 : b ≠ 1 := hnon b (hb ▸ hp.one_lt.trans_le (Nat.le_mul_of_pos_right p hr.pos))
  have hc1 : c ≠ 1 := hnon c (hc ▸ hq.one_lt.trans_le (Nat.le_mul_of_pos_right q hr.pos))
  obtain ⟨hab, hac, hbc⟩ :=
    LLS.PaperStatements.three_characters_ne_of_pairwise_product_conductors H a b c ha hb hc hp.pos
      hq.pos hr.pos hpq hpr hqr
  have hs :=
    LLS.PaperStatements.nonprincipal_annihilator_eq_three_of_index_four H hi a b c ha1 hb1 hc1 hab
      hac hbc
  exact
    exists_prime_witness_le_gaussian_star_of_three_annihilator_members hnlarge hnOdd H hHpass hGRH
      hL a b c hab hac hbc hs ha hb hc hp.pos hq.pos hr.pos hn

end PseudoPrime.PrimeTestBounds.MillerRabin
