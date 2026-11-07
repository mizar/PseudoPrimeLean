/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianThreePrefix50000
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleGap

/-! Gaussian comparison for the three actual pair characters. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, universal prime passage through a cutoff at least 50000 bounds the
Gaussian principal deficit for a squarefree uniform Korselt triple. The three
primitive even pair characters supply the joint Euler gain and conductor sum. -/
theorem gaussian_pair_gap_of_all_pass {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r) (hpq : 20000 ≤ p * q) (hpr : 20000 ≤ p * r)
    (hqr : 20000 ≤ q * r) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hn : 1 < n) (ho : Odd n) (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n)
    (hrn : r ∣ n) (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {X x : ℝ} (hx : 1 ≤ x) (s : Finset ℕ)
    (hs : ∀ k ∈ s, (k : ℝ) ≤ X) (hX : 50000 ≤ X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    4 *
          (∑ k ∈ s,
            (LLS.PaperStatements.gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x
                k).re) -
        (∑' k : ℕ,
            LLS.PaperStatements.gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x
              k).re <
      (20115621 / 25000000 : ℝ) * Real.log n + 683 / 50 - 108 / 25 - 4 * (1129059 / 200000 : ℝ) +
        (1536 / 27 : ℝ) / x +
        (2129 / 2000 : ℝ) * (((7 / 3 : ℝ) * Real.log n + 12) / Real.sqrt x) +
        (1419 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) := by
  let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
  let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
  let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
  have ha : a ≠ 1 :=
    pair_character_ne_one hsq hpqn (hp.mul hq) ((by decide : 1 < 20000).trans_le hpq)
  have hb : b ≠ 1 :=
    pair_character_ne_one hsq hprn (hp.mul hr) ((by decide : 1 < 20000).trans_le hpr)
  have hc : c ≠ 1 :=
    pair_character_ne_one hsq hqrn (hq.mul hr) ((by decide : 1 < 20000).trans_le hqr)
  have ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re := by
    intro k
    simpa only [Int.cast_natCast] using
      pair_character_sum_ge_neg_one (k : ℤ) p q r (hp.mul hq) (hp.mul hr) (hq.mul hr)
  have hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1 := by
    intro l hl hlX
    exact pair_character_nat_eq_one hn ho hp hq hpn hqn hpqn hpK hqK hvq l (hpass l hl hlX)
  have hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1 := by
    intro l hl hlX
    exact pair_character_nat_eq_one hn ho hp hr hpn hrn hprn hpK hrK hvr l (hpass l hl hlX)
  have hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1 := by
    intro l hl hlX
    exact
      pair_character_nat_eq_one hn ho hq hr hqn hrn hqrn hqK hrK (hvr.trans hvq.symm) l
        (hpass l hl hlX)
  have h :=
    gaussian_principal_prefix_50000 hGRH a b c hpq hpr hqr
      (pair_character_primitive hsq hpqn (hp.mul hq))
      (pair_character_primitive hsq hprn (hp.mul hr))
      (pair_character_primitive hsq hqrn (hq.mul hr)) ha hb hc (inv_ne_one.mpr ha)
      (inv_ne_one.mpr hb) (inv_ne_one.mpr hc)
      (pair_character_even_of_korselt hn ho hp hq hpK hqK hvq)
      (pair_character_even_of_korselt hn ho hp hr hpK hrK hvr)
      (pair_character_even_of_korselt hn ho hq hr hqK hrK (hvr.trans hvq.symm)) hX ht hA hB hC hx s
      hs
  rw [pair_level_log_sum hnprod] at h
  convert h using 1
  ring

/-- Prime passage through a cutoff at least 50000 implies the Gaussian pair gap.
The cutoff forces every prime factor above 142, so each pair level is large enough
for the primitive-character remainder estimates. -/
theorem gaussian_pair_gap_of_cutoff_pass {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {X x : ℝ} (hx : 1 ≤ x) (s : Finset ℕ)
    (hs : ∀ k ∈ s, (k : ℝ) ≤ X) (hX : 50000 ≤ X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    4 *
          (∑ k ∈ s,
            (LLS.PaperStatements.gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x
                k).re) -
        (∑' k : ℕ,
            LLS.PaperStatements.gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x
              k).re <
      (20115621 / 25000000 : ℝ) * Real.log n + 683 / 50 - 108 / 25 - 4 * (1129059 / 200000 : ℝ) +
        (1536 / 27 : ℝ) / x +
        (2129 / 2000 : ℝ) * (((7 / 3 : ℝ) * Real.log n + 12) / Real.sqrt x) +
        (1419 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) := by
  have hX' : (142 : ℝ) ≤ X := (by norm_num only : (142 : ℝ) ≤ 50000).trans hX
  have hpq :=
    pair_level_large_of_all_pass hn ho (Fact.out : p.Prime) (Fact.out : q.Prime) hpn hqn hX' hpass
  have hpr :=
    pair_level_large_of_all_pass hn ho (Fact.out : p.Prime) (Fact.out : r.Prime) hpn hrn hX' hpass
  have hqr :=
    pair_level_large_of_all_pass hn ho (Fact.out : q.Prime) (Fact.out : r.Prime) hqn hrn hX' hpass
  exact
    gaussian_pair_gap_of_all_pass hsq hnprod hpq hpr hqr hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn
      hqrn hpK hqK hrK hvq hvr hx s hs hX hpass

/-- If a numerical lower bound reverses the Gaussian pair gap, a prime at most
`X` rejects Miller--Rabin for the uniform Korselt triple. The proof applies the
actual-character comparison under the contrary assumption that every such prime passes. -/
theorem exists_prime_reject_of_gaussian_gap {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q]
    [NeZero r] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)]
    [Fact (2 < r)] (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {X x : ℝ} (hx : 1 ≤ x) (s : Finset ℕ)
    (hs : ∀ k ∈ s, (k : ℝ) ≤ X) (hX : 50000 ≤ X)
    (hgap :
      4 *
            (∑ k ∈ s,
              (LLS.PaperStatements.gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x
                  k).re) -
          (∑' k : ℕ,
              LLS.PaperStatements.gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x
                k).re ≥
        (20115621 / 25000000 : ℝ) * Real.log n + 683 / 50 - 108 / 25 - 4 * (1129059 / 200000 : ℝ) +
          (1536 / 27 : ℝ) / x +
          (2129 / 2000 : ℝ) * (((7 / 3 : ℝ) * Real.log n + 12) / Real.sqrt x) +
          (1419 / 10 : ℝ) * x ^ (-9 / 16 : ℝ)) :
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  classical
  by_contra h
  have hall (l : ℕ) (hl : l.Prime) (hlX : (l : ℝ) ≤ X) :
    PrimeTest.StrongMillerRabinPass n (l : ZMod n) :=
    Classical.byContradiction (fun hf ↦ h ⟨l, hl, hlX, hf⟩)
  exact
    (not_lt_of_ge hgap)
      (gaussian_pair_gap_of_cutoff_pass hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn
        hpK hqK hrK hvq hvr hx s hs hX hall)

end PseudoPrime.PrimeTestBounds.MillerRabin
