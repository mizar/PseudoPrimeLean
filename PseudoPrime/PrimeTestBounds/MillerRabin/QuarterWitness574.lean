/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWitness570
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterContour574

/-! # Quarter-log-square witnesses on the section 62 interval -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The three-character contour upper bound contradicts the one-tenth psi
lower estimate and the recovered prime powers throughout section 62. -/
theorem triple_impossible_574 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hS : 2 ≤ s)
    (pa : a.IsPrimitive) (pb : b.IsPrimitive) (pc : c.IsPrimitive) (na : a ≠ 1) (nb : b ≠ 1)
    (nc : c ≠ 1) (ia : a⁻¹ ≠ 1) (ib : b⁻¹ ≠ 1) (ic : c⁻¹ ≠ 1) {r : ℝ} (hl : 285 ≤ r) (hu : r ≤ 287)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1)
    (hlog : Real.log p + Real.log q + Real.log s ≤ 4 * r) (ea : a.Even) (eb : b.Even)
    (ec : c.Even) : False := by
  have hr : 0 < r := by linarith only [hl]
  have hx := sq_pos_of_pos hr
  have hm := principal_lower_tenth_574 hl hu hG.riemann
  have hw := power_gain_574 a b c hl hu ht hA hB hC
  have hi :=
    triple_explicit_upper_574 hG a b c hP hQ hS pa pb pc na nb nc ia ib ic hl hu ht hA hB hC hlog ea
      eb ec
  have hc := conductor_radius_upper_570 (by linarith only [hl] : 278 ≤ r)
  rw [quarterKernel570, LLS.PaperStatements.rationalPole_transform _ _ _ _ (one_div_pos.mpr hx),
    Complex.ofReal_re, one_div] at hc
  have hx1 := one_le_pow₀ (show 1 ≤ r by linarith only [hl]) (n := 2)
  have ht' :=
    (Analysis.rationalLogIntervalCheck_sound (N := 278) (j := 8) (n := 16) (lo := 56 / 10) (hi := 6)
        (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at ht'
  have hlogr := ht'.trans (Real.log_le_log (by norm_num only) (by linarith only [hl] : 278 ≤ r))
  have hy : 13 ≤ Real.log (r ^ 2) + 14 / 5 := by
    rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [hlogr]
  have hn := central_gamma_nonpos_570 a ea hx hy
  dsimp only at hm hw hi
  rw [reflected_arch_eq_central_570 _ ia hx1, right_gamma_eq_central_570 _ hx,
    central_gamma_pair_eq_570 a ea hx] at hi
  rw [Complex.re_tsum (quarterKernel570.summable_summand (1 : DirichletCharacter ℂ 1) hx)] at hw
  linarith only [hm, hw, hi, hc, hn, hu]

/-- The three pair characters rule out universal passage up to the quarter-log-square
cutoff for a squarefree Korselt product with equal two-adic valuations. -/
theorem pair_impossible_574 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r] [Fact p.Prime]
    [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)] (hsq : Squarefree n)
    (hnprod : n = p * q * r) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hn : 1 < n) (ho : Odd n) (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n)
    (hrn : r ∣ n) (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hl : 570 ≤ Real.log n)
    (hh : Real.log n ≤ 574)
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
  apply
    triple_impossible_574 hGRH a b c hpq hpr hqr (pair_character_primitive hsq hpqn (hp.mul hq))
      (pair_character_primitive hsq hprn (hp.mul hr))
      (pair_character_primitive hsq hqrn (hq.mul hr)) ha hb hc (inv_ne_one.mpr ha)
      (inv_ne_one.mpr hb) (inv_ne_one.mpr hc) (r := Real.log n / 2) (by linarith only [hl])
      (by linarith only [hh]) ht hA hB hC _ (pair_character_even_of_korselt hn ho hp hq hpK hqK hvq)
      (pair_character_even_of_korselt hn ho hp hr hpK hrK hvr)
      (pair_character_even_of_korselt hn ho hq hr hqK hrK (hvr.trans hvq.symm))
  rw [pair_level_log_sum hnprod]
  linarith only

/-- Under GRH every odd uniform Korselt triple with logarithm between 570 and 574
has a prime strong Miller-Rabin witness at most the square of half its logarithm. -/
theorem uniform_witness_574 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hl : 570 ≤ Real.log n)
    (hh : Real.log n ≤ 574) :
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
  obtain ⟨p, q, r, hp, hq, hr, _, _, hnprod⟩ := uniformKorselt_ordered_factors hu
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
  exact
    pair_impossible_574 hu.1 hnprod hGRH hn ho hpO hqO hrO hpD hqD hrD hpqD hprD hqrD
      (hu.2.2.1 p hp hpD) (hu.2.2.1 q hq hqD) (hu.2.2.1 r hr hrD) (hu.2.2.2 q p hq hp hqD hpD)
      (hu.2.2.2 r p hr hp hrD hpD) hl hh hall

end PseudoPrime.PrimeTestBounds.MillerRabin
