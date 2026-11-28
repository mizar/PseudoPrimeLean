/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPowers644
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWideMass644
public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformWideWindow

/-! # Section 122 quarter-square witness comparison -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At section 122 radii, the pair characters and the stated power gain
rule out universal passage up to the squared half-logarithm. -/
private theorem pair_impossible_gain_644 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hl : 632 ≤ Real.log n)
    (hh : Real.log n ≤ 644) (hP : (Real.log n / 2) ^ 4 < p) (hQ : (Real.log n / 2) ^ 4 < q)
    (hT : (Real.log n / 2) ^ 4 < r)
    (hgain :
      320 < Real.log n / 2 →
        (if Real.log n / 2 ≤ 1287 / 4 then 0.14274902
          else if Real.log n / 2 ≤ 1609 / 5 then 0.14524702 else 0.14326402) ≤
          fixedPowerGain644 (Real.log n / 2))
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
  have hR : R ∈ Set.Icc 316 322 := by
    dsimp only [R]
    exact ⟨by linarith only [hl], by linarith only [hh]⟩
  have hL : Real.log n = 2 * R := by
    dsimp only [R]; ring
  have hlev : Real.log (p * q : ℕ) + Real.log (p * r : ℕ) + Real.log (q * r : ℕ) = 4 * R := by
    rw [pair_level_log_sum hnprod, hL]
    ring
  have ea := pair_character_even_of_korselt hn ho hp hq hpK hqK hvq
  have eb := pair_character_even_of_korselt hn ho hp hr hpK hrK hvr
  have ec := pair_character_even_of_korselt hn ho hq hr hqK hrK (hvr.trans hvq.symm)
  have hM :=
    triangle_pair_mass_upper_644 hn ho hsq hnprod hp hq hr hpK hqK hrK hvq hvr hGRH hR hL hP hQ hT
      (fun l hl hcut ↦
        hpass l hl
          (by
            have he := (Nat.le_floor_iff (Real.exp_pos _).le).mp hcut
            have hx : Real.exp (5 / 2 : ℝ) ≤ R ^ 2 := by
              have hx' := quarter_shift_scale_ge_one_644 hR.1 (h := 0) (by norm_num only)
              rw [add_zero, Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _),
                one_mul] at hx'
              exact (Real.exp_le_exp.mpr (by norm_num only)).trans hx'
            exact he.trans hx))
      hA hB hC
  have htrace (l : ℕ) : (a l).re + (b l).re + (c l).re ∈ Set.Icc (-1) 3 :=
    ⟨ht l, by
      linarith only [(Complex.re_le_norm _).trans (a.norm_le_one l),
        (Complex.re_le_norm _).trans (b.norm_le_one l),
        (Complex.re_le_norm _).trans (c.norm_le_one l)]⟩
  have hprefix (l : ℕ) (hl : l ∈ Finset.Ioc 0 99000) (hΛ : ArithmeticFunction.vonMangoldt l ≠ 0) :
    (a l).re + (b l).re + (c l).re = 3 := by
    have hsmall : (l : ℝ) ≤ X :=
      (show (l : ℝ) ≤ 99000 by exact_mod_cast (Finset.mem_Ioc.mp hl).2).trans
        ((by norm_num only : (99000 : ℝ) ≤ 316 ^ 2).trans
          (pow_le_pow_left₀ (by norm_num only) hR.1 2))
    have hbase {d : ℕ} (χ : DirichletCharacter ℂ d)
      (hχ : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → χ l = 1) : χ l = 1 :=
      AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) χ
        (fun l hl h _ ↦ hχ l hl h) hsmall (Nat.coprime_one_right l) hΛ
    rw [hbase a hA, hbase b hB, hbase c hC, Complex.one_re]
    norm_num only
  exact
    quarter_contradiction_of_gain_644
      ⟨pair_character_primitive hsq hpqn _, ha,
        (NumberTheory.complexJacobiNumeratorCharacter_isQuadratic _ _).inv, ea⟩
      ⟨pair_character_primitive hsq hprn _, hb,
        (NumberTheory.complexJacobiNumeratorCharacter_isQuadratic _ _).inv, eb⟩
      ⟨pair_character_primitive hsq hqrn _, hc,
        (NumberTheory.complexJacobiNumeratorCharacter_isQuadratic _ _).inv, ec⟩
      hpq hpr hqr hGRH hR hlev hA hB hC htrace hprefix hM hgain

/-- Under GRH, an odd uniform Korselt triple in [632,644] has a prime
witness within the squared half-logarithm whenever the remaining power gain
condition holds at its radius. -/
private theorem uniform_witness_of_gain_644 {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hl : 632 ≤ Real.log n) (hh : Real.log n ≤ 644)
    (hgain :
      320 < Real.log n / 2 →
        (if Real.log n / 2 ≤ 1287 / 4 then 0.14274902
          else if Real.log n / 2 ≤ 1609 / 5 then 0.14524702 else 0.14326402) ≤
          fixedPowerGain644 (Real.log n / 2)) :
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
    pair_impossible_gain_644 hu.1 hnprod hGRH hn ho hpO hqO hrO hpD hqD hrD hpqD hprD hqrD
      (hu.2.2.1 p hp hpD) (hu.2.2.1 q hq hqD) (hu.2.2.1 r hr hrD) (hu.2.2.2 q p hq hp hqD hpD)
      (hu.2.2.2 r p hr hp hrD hpD) hl hh hLarge hQ hT hgain hall

/-- Under GRH, an odd uniform Korselt triple with logarithm in [632,644]
has a prime strong Miller–Rabin witness within the squared half-logarithm. -/
theorem uniform_witness_644 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hl : 632 ≤ Real.log n)
    (hh : Real.log n ≤ 644) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (Real.log n / 2) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply uniform_witness_of_gain_644 hn ho hu hGRH hl hh
  intro h
  by_cases h₁ : Real.log n / 2 ≤ 1287 / 4
  · rw [ite_eq_left h₁]
    exact fixed_power_gain_320_644 ⟨h.le, by linarith only [hh]⟩
  rw [ite_eq_right h₁]
  by_cases h₂ : Real.log n / 2 ≤ 1609 / 5
  · rw [ite_eq_left h₂]
    exact fixed_power_gain_32175_644 ⟨(lt_of_not_ge h₁).le, by linarith only [hh]⟩
  rw [ite_eq_right h₂]
  exact fixed_power_gain_3218_644 ⟨(lt_of_not_ge h₂).le, by linarith only [hh]⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
