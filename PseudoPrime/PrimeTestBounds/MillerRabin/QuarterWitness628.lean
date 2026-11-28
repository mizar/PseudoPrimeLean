/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMass626
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterComparison632
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseClosed107
public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformWideWindow

/-! # Quarter-square witness for logarithms from 626 to 628 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The three pair characters rule out universal passage up to the quarter-log-square
cutoff for a squarefree Korselt product with equal two-adic valuations. -/
theorem pair_impossible_628 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r] [Fact p.Prime]
    [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)] (hsq : Squarefree n)
    (hnprod : n = p * q * r) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hn : 1 < n) (ho : Odd n) (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n)
    (hrn : r ∣ n) (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hl : 626 ≤ Real.log n)
    (hh : Real.log n ≤ 628) (hP : (Real.log n / 2) ^ 4 < p) (hQ : (Real.log n / 2) ^ 4 < q)
    (hT : (Real.log n / 2) ^ 4 < r)
    (hpass :
      ∀ l : ℕ,
        l.Prime → (l : ℝ) ≤ (Real.log n / 2) ^ 2 → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    False := by
  let X := (Real.log n / 2) ^ 2
  let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
  let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
  let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
  have hpq : 2 ≤ p * q :=
    (Fact.out : p.Prime).two_le.trans (Nat.le_mul_of_pos_right p (Fact.out : q.Prime).pos)
  have hpr : 2 ≤ p * r :=
    (Fact.out : p.Prime).two_le.trans (Nat.le_mul_of_pos_right p (Fact.out : r.Prime).pos)
  have hqr : 2 ≤ q * r :=
    (Fact.out : q.Prime).two_le.trans (Nat.le_mul_of_pos_right q (Fact.out : r.Prime).pos)
  have ha : a ≠ 1 := pair_character_ne_one hsq hpqn (hp.mul hq) ((by decide : 1 < 2).trans_le hpq)
  have hb : b ≠ 1 := pair_character_ne_one hsq hprn (hp.mul hr) ((by decide : 1 < 2).trans_le hpr)
  have hc : c ≠ 1 := pair_character_ne_one hsq hqrn (hq.mul hr) ((by decide : 1 < 2).trans_le hqr)
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
  let R := Real.log n / 2
  have hR : 313 ≤ R := by
    dsimp only [R]; linarith only [hl]
  have hU : R ≤ 314 := by
    dsimp only [R]; linarith only [hh]
  have hL : Real.log n = 2 * R := by
    dsimp only [R]; ring
  have hlev : Real.log (p * q : ℕ) + Real.log (p * r : ℕ) + Real.log (q * r : ℕ) ≤ 4 * R := by
    rw [pair_level_log_sum hnprod, hL]
    linarith only
  have ea := pair_character_even_of_korselt hn ho hp hq hpK hqK hvq
  have eb := pair_character_even_of_korselt hn ho hp hr hpK hrK hvr
  have ec := pair_character_even_of_korselt hn ho hq hr hqK hrK (hvr.trans hvq.symm)
  have hZ :=
    signed_zero_upper_628 hGRH a b c hpq hpr hqr (pair_character_primitive hsq hpqn (hp.mul hq))
      (pair_character_primitive hsq hprn (hp.mul hr))
      (pair_character_primitive hsq hqrn (hq.mul hr)) ha hb hc ea eb ec ⟨hR, hU⟩ hlev ht hA hB hC
  have hM :=
    common_triple_mass_upper_to632 hn ho hsq hnprod hp hq hr hpK hqK hrK hvq hvr hGRH
      (show 300 ≤ R by linarith only [hR]) (show R ≤ 316 by linarith only [hU]) hL hP hQ hT hpass
  have hphase :=
    closed_passing_phase_107 hsq hn ho hp hq hr hpqn hprn hqrn hpK hqK hrK hvq hvr hGRH
      (show 300 ≤ R by linarith only [hR]) hL hnprod hpass
  dsimp only [twoShiftZeroPhase] at hphase
  apply
    zero_bounds_contradict_628 (M := quarterMass570 a + quarterMass570 b + quarterMass570 c)
      ⟨hR, hU⟩ _ _ hZ
  · linarith only [hM]
  · linarith only [hphase]

/-- Under GRH every odd uniform Korselt triple with logarithm between 626 and 628
has a prime strong Miller-Rabin witness at most the square of half its logarithm. -/
theorem uniform_witness_628 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hl : 626 ≤ Real.log n)
    (hh : Real.log n ≤ 628) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (Real.log n / 2) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  classical
  by_contra h
  have hall :
    ∀ l : ℕ,
      l.Prime →
        (l : ℝ) ≤ (Real.log n / 2) ^ 2 → PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
    intro l hl' hlX
    exact Classical.byContradiction (fun hf ↦ h ⟨l, hl', hlX, hf⟩)
  obtain ⟨p, q, r, hp, hq, hr, hpq, hqr, hnprod⟩ := uniformKorselt_ordered_factors hu
  have hpD : p ∣ n := ⟨q * r, hnprod.trans (Nat.mul_assoc _ _ _)⟩
  have hqD : q ∣ n := ⟨p * r, hnprod.trans (by ac_rfl)⟩
  have hrD : r ∣ n := ⟨p * q, hnprod.trans (by ac_rfl)⟩
  have hpO := Odd.of_dvd_nat ho hpD
  have hqO := Odd.of_dvd_nat ho hqD
  have hrO := Odd.of_dvd_nat ho hrD
  have hp2 : p ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hpO)
  have hq2 : q ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hqO)
  have hr2 : r ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hrO)
  let : NeZero n := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hn)⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  let : NeZero r := ⟨hr.ne_zero⟩
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact r.Prime := ⟨hr⟩
  let : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
  let : Fact (2 < q) := ⟨lt_of_le_of_ne hq.two_le (Ne.symm hq2)⟩
  let : Fact (2 < r) := ⟨lt_of_le_of_ne hr.two_le (Ne.symm hr2)⟩
  have hpqD : p * q ∣ n := ⟨r, hnprod⟩
  have hprD : p * r ∣ n := ⟨q, hnprod.trans (by ac_rfl)⟩
  have hqrD : q * r ∣ n := ⟨p, hnprod.trans (by ac_rfl)⟩
  have hLarge := uniform_wideWindow_lt_prime hnprod hp hq hr hpq hqr hu (by linarith only [hl])
  have hQ := hLarge.trans (Nat.cast_lt.mpr hpq)
  have hT := hQ.trans (Nat.cast_lt.mpr hqr)
  exact
    pair_impossible_628 hu.1 hnprod hGRH hn ho hpO hqO hrO hpD hqD hrD hpqD hprD hqrD
      (hu.2.2.1 p hp hpD) (hu.2.2.1 q hq hqD) (hu.2.2.1 r hr hrD) (hu.2.2.2 q p hq hp hqD hpD)
      (hu.2.2.2 r p hr hp hrD hpD) hl hh hLarge hQ hT hall

end PseudoPrime.PrimeTestBounds.MillerRabin
