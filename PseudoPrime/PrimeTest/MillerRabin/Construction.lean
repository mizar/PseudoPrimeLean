/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.Data.Nat.GCD.BigOperators

/-! # Fixed-base strong pseudoprimes and construction bridges -/

@[expose] public section

namespace PseudoPrime.PrimeTest

/-- A finite list of bases all passes the proof-side strong Miller–Rabin condition for `n`.
Repeated entries have no effect; lists provide an executable representation of a fixed base set. -/
def PassesStrongBases (n : ℕ) (bases : List ℕ) : Prop :=
  ∀ a ∈ bases, IsStrongMillerRabinProbablePrime n a

/-- A strong pseudoprime to every base in `bases` is a composite number passing each base.
The condition `1 < n` excludes the nonprime values `0` and `1`. -/
def IsStrongPseudoprimeTo (n : ℕ) (bases : List ℕ) : Prop :=
  1 < n ∧ ¬Nat.Prime n ∧ PassesStrongBases n bases

/-- Execute the strong Miller–Rabin test at every base in a finite list. -/
def passesStrongBases (n : ℕ) (bases : List ℕ) : Bool :=
  bases.all (fun a ↦ strongMillerRabinWithBase n a)

/-- The executable multi-base test agrees with the proof-side universal condition. -/
theorem passesStrongBases_eq_true_iff (n : ℕ) (bases : List ℕ) :
    passesStrongBases n bases = true ↔ PassesStrongBases n bases := by
  rw [passesStrongBases, List.all_eq_true]
  constructor
  · intro h a ha
    exact strongMillerRabinWithBase_eq_true_iff.mp (h a ha)
  · intro h a ha
    exact strongMillerRabinWithBase_eq_true_iff.mpr (h a ha)

/-- A composite number accepted by the executable multi-base test meets the fixed-base
strong-pseudoprime specification. -/
theorem isStrongPseudoprimeTo_iff (n : ℕ) (bases : List ℕ) :
    IsStrongPseudoprimeTo n bases ↔ 1 < n ∧ ¬Nat.Prime n ∧ passesStrongBases n bases = true := by
  rw [IsStrongPseudoprimeTo, passesStrongBases_eq_true_iff]

/-- The exponent at the last minus-one stage is half of `n - 1`. -/
private theorem half_exp_eq {n s d : ℕ} (hs : 0 < s) (hdecomp : n - 1 = 2 ^ s * d) :
    (n - 1) / 2 = 2 ^ (s - 1) * d := by
  have hsucc : s - 1 + 1 = s := Nat.sub_add_cancel hs
  have hpow : 2 ^ s = 2 ^ (s - 1) * 2 := by conv_lhs => rw [← hsucc, pow_succ]
  calc
    (n - 1) / 2 = (2 ^ s * d) / 2 := by rw [hdecomp]
    _ = ((2 ^ (s - 1) * d) * 2) / 2 := by
      rw [hpow]
      ring_nf
    _ = 2 ^ (s - 1) * d := Nat.mul_div_cancel _ (by decide)

/-- For odd `n > 1`, a base with `a^((n - 1) / 2) = -1` passes the executable
strong Miller–Rabin test. The canonical two-adic exponent is positive, so this is the
last permitted minus-one stage. Local Legendre and CRT constructions use this result. -/
theorem strongMillerRabinWithBase_of_half_pow_neg_one {n a : ℕ} (hn : 1 < n) (hnOdd : Odd n)
    (hpow : (a : ZMod n) ^ ((n - 1) / 2) = -1) : strongMillerRabinWithBase n a = true := by
  obtain ⟨hs, _, hdecomp⟩ := odd_sub_canonical_decomp hn hnOdd
  apply (strongMillerRabinWithBase_eq_true_iff_pass).2
  right
  refine ⟨padicValNat 2 (n - 1) - 1, Nat.sub_lt hs (by decide), ?_⟩
  rwa [← half_exp_eq hs hdecomp]

/-- For odd composite `n > 1`, a half-exponent minus-one congruence at every listed
base proves `IsStrongPseudoprimeTo n bases`. Apply the single-base result to each list
member; the Arnault sufficient conditions use this common final step. -/
theorem isStrongPseudoprimeTo_of_half_pow_neg_one {n : ℕ} {bases : List ℕ} (hn : 1 < n)
    (hnOdd : Odd n) (hcomp : ¬Nat.Prime n) (hpow : ∀ a ∈ bases, (a : ZMod n) ^ ((n - 1) / 2) = -1) :
    IsStrongPseudoprimeTo n bases := by
  rw [IsStrongPseudoprimeTo]
  refine ⟨hn, hcomp, ?_⟩
  intro a ha
  exact
    strongMillerRabinWithBase_eq_true_iff.mp
      (strongMillerRabinWithBase_of_half_pow_neg_one hn hnOdd (hpow a ha))

/-- A power is one modulo a coprime product exactly when it is one modulo both factors. -/
theorem pow_mod_mul_eq_one_iff {p q : ℕ} (hc : p.Coprime q) (a d : ℕ) :
    ((a : ZMod (p * q)) ^ d = 1) ↔ (a : ZMod p) ^ d = 1 ∧ (a : ZMod q) ^ d = 1 := by
  constructor
  · intro h
    constructor
    · have hp := congrArg (fun x : ZMod (p * q) => ((ZMod.chineseRemainder hc) x).1) h
      simpa only [map_pow, map_natCast, Prod.pow_fst, Prod.fst_natCast, map_one, Prod.fst_one] using
        hp
    · have hq := congrArg (fun x : ZMod (p * q) => ((ZMod.chineseRemainder hc) x).2) h
      simpa only [map_pow, map_natCast, Prod.pow_snd, Prod.snd_natCast, map_one, Prod.snd_one] using
        hq
  · intro h
    apply (ZMod.chineseRemainder hc).injective
    apply Prod.ext
    · simpa only [map_pow, map_natCast, Prod.pow_fst, Prod.fst_natCast, map_one, Prod.fst_one] using
        h.1
    · simpa only [map_pow, map_natCast, Prod.pow_snd, Prod.snd_natCast, map_one, Prod.snd_one] using
        h.2

/-- A power is minus one modulo a coprime product exactly when it is minus one modulo both
factors. This is the CRT step in the local strong-pseudoprime criteria. -/
theorem pow_mod_mul_eq_neg_one_iff {p q : ℕ} (hc : p.Coprime q) (a d : ℕ) :
    ((a : ZMod (p * q)) ^ d = -1) ↔ (a : ZMod p) ^ d = -1 ∧ (a : ZMod q) ^ d = -1 := by
  constructor
  · intro h
    constructor
    · have hp := congrArg (fun x : ZMod (p * q) => ((ZMod.chineseRemainder hc) x).1) h
      simpa only [map_pow, map_natCast, Prod.pow_fst, Prod.fst_natCast, RingEquiv.map_neg_one,
        Prod.fst_neg, Prod.fst_one] using hp
    · have hq := congrArg (fun x : ZMod (p * q) => ((ZMod.chineseRemainder hc) x).2) h
      simpa only [map_pow, map_natCast, Prod.pow_snd, Prod.snd_natCast, RingEquiv.map_neg_one,
        Prod.snd_neg, Prod.snd_one] using hq
  · intro h
    apply (ZMod.chineseRemainder hc).injective
    apply Prod.ext
    · simpa only [map_pow, map_natCast, Prod.pow_fst, Prod.fst_natCast, RingEquiv.map_neg_one,
        Prod.fst_neg, Prod.fst_one] using h.1
    · simpa only [map_pow, map_natCast, Prod.pow_snd, Prod.snd_natCast, RingEquiv.map_neg_one,
        Prod.snd_neg, Prod.snd_one] using h.2

/-- For a coprime two-factor modulus, strong Miller–Rabin acceptance is equivalent to the
two local factors accepting at the same stage. This is the finite CRT core of the semiprime
signature criterion. -/
private theorem strongMillerRabinPass_mul_iff {p q s d a : ℕ} (hc : p.Coprime q) :
    ((a : ZMod (p * q)) ^ d = 1 ∨ ∃ j : ℕ, j < s ∧ (a : ZMod (p * q)) ^ (2 ^ j * d) = -1) ↔
      ((a : ZMod p) ^ d = 1 ∧ (a : ZMod q) ^ d = 1) ∨
        ∃ j : ℕ, j < s ∧ (a : ZMod p) ^ (2 ^ j * d) = -1 ∧ (a : ZMod q) ^ (2 ^ j * d) = -1 := by
  constructor
  · intro h
    rcases h with h | ⟨j, hj, h⟩
    · exact Or.inl ((pow_mod_mul_eq_one_iff hc a d).mp h)
    · exact Or.inr ⟨j, hj, (pow_mod_mul_eq_neg_one_iff hc a _).mp h⟩
  · intro h
    rcases h with h | ⟨j, hj, h⟩
    · exact Or.inl ((pow_mod_mul_eq_one_iff hc a d).mpr h)
    · exact Or.inr ⟨j, hj, (pow_mod_mul_eq_neg_one_iff hc a _).mpr h⟩

/-- The executable strong test on a semiprime is exactly the synchronized two-factor power
test. Both local minus-one powers must occur at the same repeated-square stage. -/
private theorem strongMillerRabinWithBase_mul_eq_true_iff_decomp {p q s d a : ℕ} (hc : p.Coprime q)
    (hn : 1 < p * q) (hdecomp : p * q - 1 = 2 ^ s * d) (hdOdd : Odd d) :
    strongMillerRabinWithBase (p * q) a = true ↔
      ((a : ZMod p) ^ d = 1 ∧ (a : ZMod q) ^ d = 1) ∨
        ∃ j : ℕ, j < s ∧ (a : ZMod p) ^ (2 ^ j * d) = -1 ∧ (a : ZMod q) ^ (2 ^ j * d) = -1 := by
  have hdvd : ¬2 ∣ d := by
    intro hdiv
    exact (Nat.not_even_iff_odd.mpr hdOdd) (even_iff_two_dvd.mpr hdiv)
  have hmax := Nat.maxPowDvdDiv_of_pow_mul_eq (Nat.sub_ne_zero_of_lt hn) hdecomp.symm hdvd
  have hs : padicValNat 2 (p * q - 1) = s := by
    calc
      padicValNat 2 (p * q - 1) = (Nat.maxPowDvdDiv 2 (p * q - 1)).1 :=
        (Nat.fst_maxPowDvdDiv 2 (p * q - 1)).symm
      _ = s := congrArg Prod.fst hmax
  have hd : Nat.divMaxPow (p * q - 1) 2 = d := by
    calc
      Nat.divMaxPow (p * q - 1) 2 = (Nat.maxPowDvdDiv 2 (p * q - 1)).2 :=
        (Nat.snd_maxPowDvdDiv 2 (p * q - 1)).symm
      _ = d := congrArg Prod.snd hmax
  rw [← hs, ← hd]
  exact (strongMillerRabinWithBase_eq_true_iff_pass).trans (strongMillerRabinPass_mul_iff hc)

/-- Under the local Fermat equation and an odd decomposition exponent, the zero component
of the two-adic order signature is exactly the initial `1` stage of the strong test. -/
private theorem pow_oddPart_eq_one_iff_orderOf_twoAdic_eq_zero {n s d : ℕ} {x : ZMod n}
    (hdOdd : Odd d) (hFermat : x ^ (2 ^ s * d) = 1) :
    x ^ d = 1 ↔ padicValNat 2 (orderOf x) = 0 := by
  constructor
  · intro h
    have hdiv : orderOf x ∣ d := orderOf_dvd_of_pow_eq_one h
    have hnot : ¬2 ∣ orderOf x := by
      intro htwo
      exact (Nat.not_even_iff_odd.mpr hdOdd) (even_iff_two_dvd.mpr (dvd_trans htwo hdiv))
    exact padicValNat.eq_zero_of_not_dvd hnot
  · intro hval
    have hdiv : orderOf x ∣ 2 ^ s * d := orderOf_dvd_of_pow_eq_one hFermat
    have hne : orderOf x ≠ 0 := by
      intro hzero
      rw [hzero] at hdiv
      have hprod0 := Nat.eq_zero_of_zero_dvd hdiv
      rcases mul_eq_zero.mp hprod0 with htwo | hd0
      · exact (pow_ne_zero s (by decide : (2 : ℕ) ≠ 0)) htwo
      · have hdmod := Nat.odd_iff.mp hdOdd
        exact Nat.zero_ne_one (by simpa only [hd0, Nat.zero_mod] using hdmod)
    have hnot : ¬2 ∣ orderOf x := by
      rcases padicValNat.eq_zero_iff.mp hval with htwo | hzero | hnot
      · exact False.elim ((by decide : (2 : ℕ) ≠ 1) htwo)
      · exact False.elim (hne hzero)
      · exact hnot
    have hcop : (orderOf x).Coprime (2 ^ s) :=
      (Nat.coprime_two_right.mpr
            (Nat.not_even_iff_odd.mp ((even_iff_two_dvd).not.mpr hnot))).pow_right
        s
    exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left hdiv)

/-- The odd part of a finite order divides the odd part of a Fermat exponent. -/
private theorem order_dvd_twoAdic_pow_mul {n s d : ℕ} {x : ZMod n} (hdOdd : Odd d)
    (hFermat : x ^ (2 ^ s * d) = 1) : orderOf x ∣ 2 ^ padicValNat 2 (orderOf x) * d := by
  let o := orderOf x
  let t := padicValNat 2 o
  let u := Nat.divMaxPow o 2
  change o ∣ 2 ^ t * d
  have hdiv : o ∣ 2 ^ s * d := orderOf_dvd_of_pow_eq_one hFermat
  have hone : o ≠ 0 := by
    intro hz
    have hzero : 2 ^ s * d = 0 := Nat.eq_zero_of_zero_dvd (hz ▸ hdiv)
    rcases mul_eq_zero.mp hzero with htwo | hd0
    · exact (pow_ne_zero s (by decide : (2 : ℕ) ≠ 0)) htwo
    · have hdmod := Nat.odd_iff.mp hdOdd
      exact Nat.zero_ne_one (by simpa only [hd0, Nat.zero_mod] using hdmod)
  have hfactor : u * 2 ^ t = o := Nat.divMaxPow_mul_pow_padicValNat 2 o
  have huodd : Odd u :=
    Nat.not_even_iff_odd.mp ((even_iff_two_dvd).not.mpr (Nat.not_dvd_divMaxPow (by decide) hone))
  have huD : u ∣ 2 ^ s * d := by
    have huO : u ∣ o := by
      rw [← hfactor]
      exact dvd_mul_right u _
    exact dvd_trans huO hdiv
  have hc : u.Coprime (2 ^ s) := (Nat.coprime_two_right.mpr huodd).pow_right s
  have hud : u ∣ d := hc.dvd_of_dvd_mul_left huD
  rcases hud with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  conv_rhs => rw [← hfactor]
  rw [hk]
  ring_nf

/-- A positive two-adic order signature has minus one at its last nontrivial stage. -/
private theorem local_minus_one_of_positive_signature {p s d : ℕ} [Fact (Nat.Prime p)] {x : ZMod p}
    (hdOdd : Odd d) (hFermat : x ^ (2 ^ s * d) = 1) (ht : 0 < padicValNat 2 (orderOf x)) :
    x ^ (2 ^ (padicValNat 2 (orderOf x) - 1) * d) = -1 := by
  let t := padicValNat 2 (orderOf x)
  change x ^ (2 ^ (t - 1) * d) = -1
  have hdiv : orderOf x ∣ 2 ^ t * d := order_dvd_twoAdic_pow_mul hdOdd hFermat
  have hpow : x ^ (2 ^ t * d) = 1 := orderOf_dvd_iff_pow_eq_one.mp hdiv
  have hsucc : t - 1 + 1 = t := Nat.sub_add_cancel ht
  have hexp : (2 ^ (t - 1) * d) * 2 = 2 ^ t * d := by
    conv_rhs => rw [← hsucc, pow_succ]
    ring_nf
  have hsq : (x ^ (2 ^ (t - 1) * d)) ^ 2 = 1 := by
    rw [← pow_mul, hexp]
    exact hpow
  have hne : x ^ (2 ^ (t - 1) * d) ≠ 1 := by
    intro hz
    have hlocal : orderOf x ∣ 2 ^ (t - 1) * d := orderOf_dvd_of_pow_eq_one hz
    have hpowdiv : 2 ^ t ∣ 2 ^ (t - 1) * d := dvd_trans pow_padicValNat_dvd hlocal
    have htwo : 2 ∣ d := by
      rw [show 2 ^ t = 2 ^ (t - 1) * 2 by conv_lhs => rw [← hsucc, pow_succ]] at hpowdiv
      exact Nat.dvd_of_mul_dvd_mul_left (pow_pos (by decide) _) hpowdiv
    exact (Nat.not_even_iff_odd.mpr hdOdd) (even_iff_two_dvd.mpr htwo)
  rcases sq_eq_one_iff.mp hsq with hone | hminus
  · exact False.elim (hne hone)
  · exact hminus

/-- The two-adic valuation of a local multiplicative order cannot exceed the strong-test
decomposition exponent when the Fermat congruence holds. -/
private theorem local_signature_le {n s d : ℕ} {x : ZMod n} (hdOdd : Odd d)
    (hFermat : x ^ (2 ^ s * d) = 1) : padicValNat 2 (orderOf x) ≤ s := by
  have hdiv : orderOf x ∣ 2 ^ s * d := orderOf_dvd_of_pow_eq_one hFermat
  have hdne : d ≠ 0 := by
    have ho := Nat.odd_iff.mp hdOdd
    intro hd0
    exact Nat.zero_ne_one (by simpa only [hd0, Nat.zero_mod] using ho)
  have hmulne : 2 ^ s * d ≠ 0 := mul_ne_zero (pow_ne_zero _ (by decide)) hdne
  have hv : padicValNat 2 (orderOf x) ≤ padicValNat 2 (2 ^ s * d) :=
    (padicValNat_dvd_iff_le hmulne).mp (dvd_trans pow_padicValNat_dvd hdiv)
  have hoddval : padicValNat 2 d = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    exact (even_iff_two_dvd).not.mp (Nat.not_even_iff_odd.mpr hdOdd)
  rw [padicValNat.mul (p := 2) (pow_ne_zero _ (by decide)) hdne, padicValNat.prime_pow, hoddval,
    Nat.add_zero] at hv
  exact hv

/-- A minus-one stage has exactly the indicated two-adic order signature. -/
private theorem local_minus_one_iff_signature {p s j d : ℕ} [Fact (Nat.Prime p)] {x : ZMod p}
    (hpOdd : Odd p) (hdOdd : Odd d) (hFermat : x ^ (2 ^ s * d) = 1) :
    x ^ (2 ^ j * d) = -1 ↔ padicValNat 2 (orderOf x) = j + 1 := by
  constructor
  · intro hminus
    have hpgt : 2 < p := by
      have hpge := (Fact.out : Nat.Prime p).two_le
      have hpmod := Nat.odd_iff.mp hpOdd
      exact
        Nat.lt_of_le_of_ne hpge
          (by
            intro h; subst p; exact (by decide : ¬Odd 2) hpOdd)
    have hne : (-1 : ZMod p) ≠ 1 := @ZMod.neg_one_ne_one p ⟨hpgt⟩
    have hexp : (2 ^ j * d) * 2 = 2 ^ (j + 1) * d := by
      rw [pow_succ]
      ring_nf
    have hnext : x ^ (2 ^ (j + 1) * d) = 1 := by
      rw [← hexp, pow_mul, hminus]
      ring
    have hle : padicValNat 2 (orderOf x) ≤ j + 1 := local_signature_le hdOdd hnext
    have hjlt : j < padicValNat 2 (orderOf x) := by
      by_contra hnot
      have htj : padicValNat 2 (orderOf x) ≤ j := Nat.le_of_not_gt hnot
      have hdiv : orderOf x ∣ 2 ^ j * d := by
        have hbase := order_dvd_twoAdic_pow_mul hdOdd hnext
        obtain ⟨k, hk⟩ := Nat.pow_dvd_pow 2 htj
        apply dvd_trans hbase
        exact
          ⟨k, by
            rw [hk]; ring⟩
      have hone : x ^ (2 ^ j * d) = 1 := orderOf_dvd_iff_pow_eq_one.mp hdiv
      exact hne (hminus ▸ hone)
    exact Nat.le_antisymm hle (Nat.succ_le_of_lt hjlt)
  · intro ht
    have hpos : 0 < padicValNat 2 (orderOf x) := by
      rw [ht]
      exact Nat.zero_lt_succ j
    have hminus := local_minus_one_of_positive_signature hdOdd hFermat hpos
    rw [ht] at hminus
    simpa only [Nat.add_sub_cancel_right] using hminus

/-- Under the two local Fermat congruences, a semiprime passes a base exactly when its
prime factors have the same two-adic multiplicative-order signature. -/
private theorem strongMillerRabinWithBase_mul_iff_order_signature_decomp {p q s d a : ℕ}
    [Fact (Nat.Prime p)] [Fact (Nat.Prime q)] (hpOdd : Odd p) (hqOdd : Odd q) (hc : p.Coprime q)
    (hn : 1 < p * q) (hdecomp : p * q - 1 = 2 ^ s * d) (hdOdd : Odd d)
    (hfp : (a : ZMod p) ^ (2 ^ s * d) = 1) (hfq : (a : ZMod q) ^ (2 ^ s * d) = 1) :
    strongMillerRabinWithBase (p * q) a = true ↔
      padicValNat 2 (orderOf (a : ZMod p)) = padicValNat 2 (orderOf (a : ZMod q)) := by
  rw [strongMillerRabinWithBase_mul_eq_true_iff_decomp hc hn hdecomp hdOdd]
  constructor
  · intro h
    rcases h with hzero | ⟨j, _, hp, hq⟩
    · rw [(pow_oddPart_eq_one_iff_orderOf_twoAdic_eq_zero hdOdd hfp).mp hzero.1,
        (pow_oddPart_eq_one_iff_orderOf_twoAdic_eq_zero hdOdd hfq).mp hzero.2]
    · rw [(local_minus_one_iff_signature hpOdd hdOdd hfp).mp hp,
        (local_minus_one_iff_signature hqOdd hdOdd hfq).mp hq]
  · intro ht
    by_cases hz : padicValNat 2 (orderOf (a : ZMod p)) = 0
    · left
      constructor
      · exact (pow_oddPart_eq_one_iff_orderOf_twoAdic_eq_zero hdOdd hfp).mpr hz
      · exact (pow_oddPart_eq_one_iff_orderOf_twoAdic_eq_zero hdOdd hfq).mpr (ht ▸ hz)
    · right
      let t := padicValNat 2 (orderOf (a : ZMod p))
      have hpos : 0 < t := Nat.pos_of_ne_zero hz
      have hle : t ≤ s := local_signature_le hdOdd hfp
      refine ⟨t - 1, (Nat.sub_lt hpos (by decide : 0 < 1)).trans_le hle, ?_, ?_⟩
      · exact local_minus_one_of_positive_signature hdOdd hfp hpos
      · have hqpos : 0 < padicValNat 2 (orderOf (a : ZMod q)) := by
          rw [← ht]
          exact hpos
        have hminus := local_minus_one_of_positive_signature hdOdd hfq hqpos
        rw [← ht] at hminus
        exact hminus

/-- Complete semiprime criterion: both Fermat equations and matching two-adic order signatures. -/
private theorem strongMillerRabinWithBase_mul_iff_fermat_and_order_signature_decomp {p q s d a : ℕ}
    [Fact (Nat.Prime p)] [Fact (Nat.Prime q)] (hpOdd : Odd p) (hqOdd : Odd q) (hc : p.Coprime q)
    (hn : 1 < p * q) (hdecomp : p * q - 1 = 2 ^ s * d) (hdOdd : Odd d) :
    strongMillerRabinWithBase (p * q) a = true ↔
      (a : ZMod p) ^ (2 ^ s * d) = 1 ∧
        (a : ZMod q) ^ (2 ^ s * d) = 1 ∧
        padicValNat 2 (orderOf (a : ZMod p)) = padicValNat 2 (orderOf (a : ZMod q)) := by
  constructor
  · intro hpass
    have hglobal : (a : ZMod (p * q)) ^ (2 ^ s * d) = 1 := by
      rw [← hdecomp]
      exact
        strongMillerRabinPass_pow hn (hpOdd.mul hqOdd)
          ((strongMillerRabinWithBase_eq_true_iff_pass).mp hpass)
    have hlocal := (pow_mod_mul_eq_one_iff hc a _).mp hglobal
    exact
      ⟨hlocal.1, hlocal.2,
        (strongMillerRabinWithBase_mul_iff_order_signature_decomp hpOdd hqOdd hc hn hdecomp hdOdd
              hlocal.1 hlocal.2).mp
          hpass⟩
  · rintro ⟨hfp, hfq, ht⟩
    exact
      (strongMillerRabinWithBase_mul_iff_order_signature_decomp hpOdd hqOdd hc hn hdecomp hdOdd hfp
            hfq).mpr
        ht

/-- If a prime-factor predecessor divides `n - 1` with the same two-adic valuation, the
Korselt quotient is odd. -/
theorem odd_korselt_quotient_of_equal_twoAdic {n p : ℕ} (hn : 1 < n) (hdiv : p - 1 ∣ n - 1)
    (hval : padicValNat 2 (p - 1) = padicValNat 2 (n - 1)) : Odd ((n - 1) / (p - 1)) := by
  have hrne : (n - 1) / (p - 1) ≠ 0 := by
    intro hzero
    have hprod := Nat.mul_div_cancel' hdiv
    rw [hzero, mul_zero] at hprod
    exact (Nat.sub_ne_zero_of_lt hn) hprod.symm
  have hv : padicValNat 2 ((n - 1) / (p - 1)) = 0 := by
    rw [padicValNat.div_of_dvd hdiv, ← hval, Nat.sub_self]
  rcases padicValNat.eq_zero_iff.mp hv with htwo | hzero | hnot
  · exact False.elim ((by decide : (2 : ℕ) ≠ 1) htwo)
  · exact False.elim (hrne hzero)
  · exact Nat.not_even_iff_odd.mp ((even_iff_two_dvd).not.mpr hnot)

/-- Euler's criterion transports a Legendre value of minus one across an odd Korselt
quotient to the half-exponent congruence modulo that prime factor. -/
theorem half_pow_neg_one_mod_prime_of_legendre {p n a : ℕ} [Fact (Nat.Prime p)] (hpOdd : Odd p)
    (hdiv : p - 1 ∣ n - 1) (hratioOdd : Odd ((n - 1) / (p - 1)))
    (hleg : legendreSym p (a : ℤ) = -1) : (a : ZMod p) ^ ((n - 1) / 2) = -1 := by
  have hp2 : p / 2 * 2 = p - 1 := by
    obtain ⟨k, hk⟩ := hpOdd
    rw [hk, Nat.mul_add_div (by decide : 0 < 2)]
    simp only [Nat.div_eq_of_lt (by decide : 1 < 2), Nat.add_zero]
    rw [Nat.add_sub_cancel_right]
    exact Nat.mul_comm k 2
  have hnfac : n - 1 = (p - 1) * ((n - 1) / (p - 1)) := (Nat.mul_div_cancel' hdiv).symm
  have hhalf : (n - 1) / 2 = (p / 2) * ((n - 1) / (p - 1)) := by
    calc
      (n - 1) / 2 = ((p - 1) * ((n - 1) / (p - 1))) / 2 := congrArg (fun x : ℕ ↦ x / 2) hnfac
      _ = (((p / 2) * ((n - 1) / (p - 1))) * 2) / 2 := by
        rw [← hp2]; ring_nf
      _ = (p / 2) * ((n - 1) / (p - 1)) := Nat.mul_div_cancel _ (by decide)
  have hEuler := legendreSym.eq_pow p (a : ℤ)
  rw [hleg] at hEuler
  have hpow : (a : ZMod p) ^ (p / 2) = -1 := by
    simpa only [Int.cast_neg, Int.cast_one, Int.cast_natCast] using hEuler.symm
  rw [hhalf, pow_mul, hpow]
  exact Odd.neg_one_pow hratioOdd

/-- Three odd prime factors satisfying Korselt, equal two-adic valuations,
and Legendre minus-one conditions pass every listed base. -/
private theorem arnault_three_factor_strongPseudoprime_core {p q r : ℕ} [Fact (Nat.Prime p)]
    [Fact (Nat.Prime q)] [Fact (Nat.Prime r)] {bases : List ℕ} (hpq : p.Coprime q)
    (hpqr : (p * q).Coprime r) (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r)
    (hnOdd : Odd (p * q * r)) (hpdiv : p - 1 ∣ (p * q * r) - 1) (hqdiv : q - 1 ∣ (p * q * r) - 1)
    (hrdiv : r - 1 ∣ (p * q * r) - 1)
    (hpval : padicValNat 2 (p - 1) = padicValNat 2 ((p * q * r) - 1))
    (hqval : padicValNat 2 (q - 1) = padicValNat 2 ((p * q * r) - 1))
    (hrval : padicValNat 2 (r - 1) = padicValNat 2 ((p * q * r) - 1))
    (hleg :
      ∀ a ∈ bases,
        legendreSym p (a : ℤ) = -1 ∧ legendreSym q (a : ℤ) = -1 ∧ legendreSym r (a : ℤ) = -1) :
    IsStrongPseudoprimeTo (p * q * r) bases := by
  have hpge : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hqge : 2 ≤ q := (Fact.out : Nat.Prime q).two_le
  have hrge : 2 ≤ r := (Fact.out : Nat.Prime r).two_le
  have hpqge : 2 ≤ p * q :=
    hpge.trans (Nat.le_mul_of_pos_right p (lt_of_lt_of_le (by decide : 0 < 2) hqge))
  have hn : 1 < p * q * r :=
    lt_of_lt_of_le (by decide : 1 < 2)
      (hpqge.trans (Nat.le_mul_of_pos_right (p * q) (lt_of_lt_of_le (by decide : 0 < 2) hrge)))
  have hpqne : p * q ≠ 1 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) hpqge)
  have hrne : r ≠ 1 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) hrge)
  have hcomp : ¬Nat.Prime (p * q * r) := Nat.not_prime_mul hpqne hrne
  apply isStrongPseudoprimeTo_of_half_pow_neg_one hn hnOdd hcomp
  intro a ha
  obtain ⟨hlp, hlq, hlr⟩ := hleg a ha
  have hpRatio := odd_korselt_quotient_of_equal_twoAdic hn hpdiv hpval
  have hqRatio := odd_korselt_quotient_of_equal_twoAdic hn hqdiv hqval
  have hrRatio := odd_korselt_quotient_of_equal_twoAdic hn hrdiv hrval
  have hpowp := half_pow_neg_one_mod_prime_of_legendre hpOdd hpdiv hpRatio hlp
  have hpowq := half_pow_neg_one_mod_prime_of_legendre hqOdd hqdiv hqRatio hlq
  have hpowr := half_pow_neg_one_mod_prime_of_legendre hrOdd hrdiv hrRatio hlr
  apply (pow_mod_mul_eq_neg_one_iff hpqr a _).2
  exact ⟨(pow_mod_mul_eq_neg_one_iff hpq a _).2 ⟨hpowp, hpowq⟩, hpowr⟩

/-- CRT lifts a common minus-one power from pairwise coprime factors to their product. -/
theorem pow_mod_list_prod_eq_neg_one (factors : List ℕ) (a e : ℕ) :
    List.Pairwise Nat.Coprime factors →
      (∀ p ∈ factors, (a : ZMod p) ^ e = -1) → (a : ZMod factors.prod) ^ e = -1 := by
  induction factors with
  | nil =>
    intro _ _
    change (a : ZMod 1) ^ e = -1
    exact Subsingleton.elim _ _
  | cons p rest ih =>
    intro hpair hlocal
    obtain ⟨hcop, hrestpair⟩ := List.pairwise_cons.mp hpair
    have hc : p.Coprime rest.prod := Nat.coprime_list_prod_right_iff.mpr hcop
    have hp : (a : ZMod p) ^ e = -1 := hlocal p (List.mem_cons_self)
    have hr : (a : ZMod rest.prod) ^ e = -1 :=
      ih hrestpair (fun q hq ↦ hlocal q (List.mem_cons_of_mem p hq))
    rw [List.prod_cons]
    exact (pow_mod_mul_eq_neg_one_iff hc a e).mpr ⟨hp, hr⟩

/-- A pairwise-coprime list of odd primes with Korselt divisibility, equal two-adic
valuations, and quadratic nonresidue bases passes every listed strong test. The nonresidue
condition is equivalent to the local Legendre symbol being minus one. -/
private theorem arnault_factors_strongPseudoprime_core (factors bases : List ℕ)
    (hpair : List.Pairwise Nat.Coprime factors) (hprimes : ∀ p ∈ factors, Nat.Prime p)
    (hodd : ∀ p ∈ factors, Odd p) (hn : 1 < factors.prod) (hnOdd : Odd factors.prod)
    (hcomp : ¬Nat.Prime factors.prod) (hdiv : ∀ p ∈ factors, p - 1 ∣ factors.prod - 1)
    (hval : ∀ p ∈ factors, padicValNat 2 (p - 1) = padicValNat 2 (factors.prod - 1))
    (hleg : ∀ p ∈ factors, ∀ a ∈ bases, ¬IsSquare (a : ZMod p)) :
    IsStrongPseudoprimeTo factors.prod bases := by
  apply isStrongPseudoprimeTo_of_half_pow_neg_one hn hnOdd hcomp
  intro a ha
  apply pow_mod_list_prod_eq_neg_one factors a _ hpair
  intro p hp
  have : Fact (Nat.Prime p) := ⟨hprimes p hp⟩
  have hlegp : legendreSym p (a : ℤ) = -1 := (legendreSym.eq_neg_one_iff' p).mpr (hleg p hp a ha)
  have hratio := odd_korselt_quotient_of_equal_twoAdic hn (hdiv p hp) (hval p hp)
  exact half_pow_neg_one_mod_prime_of_legendre (hodd p hp) (hdiv p hp) hratio hlegp

/-- CRT characterizes a one-power on a pairwise coprime factor list. -/
theorem pow_mod_list_prod_eq_one_iff (factors : List ℕ) (a e : ℕ)
    (hpair : List.Pairwise Nat.Coprime factors) :
    (a : ZMod factors.prod) ^ e = 1 ↔ ∀ p ∈ factors, (a : ZMod p) ^ e = 1 := by
  induction factors with
  | nil =>
    constructor
    · intro _ p hp
      exact False.elim (List.not_mem_nil hp)
    · intro _
      change (a : ZMod 1) ^ e = 1
      exact Subsingleton.elim _ _
  | cons p rest ih =>
    obtain ⟨hcop, hrestpair⟩ := List.pairwise_cons.mp hpair
    have hc : p.Coprime rest.prod := Nat.coprime_list_prod_right_iff.mpr hcop
    rw [List.prod_cons, pow_mod_mul_eq_one_iff hc, ih hrestpair]
    constructor
    · rintro ⟨hp, hr⟩ q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hp
      · exact hr q hq
    · intro h
      exact ⟨h p List.mem_cons_self, fun q hq ↦ h q (List.mem_cons_of_mem p hq)⟩

/-- CRT also characterizes the common minus-one stage on a factor list. -/
theorem pow_mod_list_prod_eq_neg_one_iff (factors : List ℕ) (a e : ℕ)
    (hpair : List.Pairwise Nat.Coprime factors) :
    (a : ZMod factors.prod) ^ e = -1 ↔ ∀ p ∈ factors, (a : ZMod p) ^ e = -1 := by
  induction factors with
  | nil =>
    constructor
    · intro _ p hp
      exact False.elim (List.not_mem_nil hp)
    · intro _
      change (a : ZMod 1) ^ e = -1
      exact Subsingleton.elim _ _
  | cons p rest ih =>
    obtain ⟨hcop, hrestpair⟩ := List.pairwise_cons.mp hpair
    have hc : p.Coprime rest.prod := Nat.coprime_list_prod_right_iff.mpr hcop
    rw [List.prod_cons, pow_mod_mul_eq_neg_one_iff hc, ih hrestpair]
    constructor
    · rintro ⟨hp, hr⟩ q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hp
      · exact hr q hq
    · intro h
      exact ⟨h p List.mem_cons_self, fun q hq ↦ h q (List.mem_cons_of_mem p hq)⟩

/-- For an odd squarefree product, a base passes exactly when every prime factor satisfies
Fermat and all factors share one two-adic multiplicative-order signature. -/
private theorem strongMillerRabinWithBase_factors_iff_fermat_and_order_signature_decomp
    (factors : List ℕ) {s d a : ℕ} (hpair : List.Pairwise Nat.Coprime factors)
    (hprimes : ∀ p ∈ factors, Nat.Prime p) (hodd : ∀ p ∈ factors, Odd p) (hn : 1 < factors.prod)
    (hnOdd : Odd factors.prod) (hdecomp : factors.prod - 1 = 2 ^ s * d) (hdOdd : Odd d) :
    strongMillerRabinWithBase factors.prod a = true ↔
      (∀ p ∈ factors, (a : ZMod p) ^ (2 ^ s * d) = 1) ∧
        ∃ t : ℕ, t ≤ s ∧ ∀ p ∈ factors, padicValNat 2 (orderOf (a : ZMod p)) = t := by
  have hdvd : ¬2 ∣ d := by
    intro hdiv
    exact (Nat.not_even_iff_odd.mpr hdOdd) (even_iff_two_dvd.mpr hdiv)
  have hmax := Nat.maxPowDvdDiv_of_pow_mul_eq (Nat.sub_ne_zero_of_lt hn) hdecomp.symm hdvd
  have hs : padicValNat 2 (factors.prod - 1) = s := by
    calc
      padicValNat 2 (factors.prod - 1) = (Nat.maxPowDvdDiv 2 (factors.prod - 1)).1 :=
        (Nat.fst_maxPowDvdDiv 2 (factors.prod - 1)).symm
      _ = s := congrArg Prod.fst hmax
  have hd : Nat.divMaxPow (factors.prod - 1) 2 = d := by
    calc
      Nat.divMaxPow (factors.prod - 1) 2 = (Nat.maxPowDvdDiv 2 (factors.prod - 1)).2 :=
        (Nat.snd_maxPowDvdDiv 2 (factors.prod - 1)).symm
      _ = d := congrArg Prod.snd hmax
  constructor
  · intro hpass
    have hpass' :
      (a : ZMod factors.prod) ^ d = 1 ∨
        ∃ j : ℕ, j < s ∧ (a : ZMod factors.prod) ^ (2 ^ j * d) = -1 := by
      simpa only [StrongMillerRabinPass, hs, hd] using
        ((strongMillerRabinWithBase_eq_true_iff_pass).mp hpass)
    have hglobal : (a : ZMod factors.prod) ^ (2 ^ s * d) = 1 := by
      rw [← hdecomp]
      exact
        strongMillerRabinPass_pow hn hnOdd ((strongMillerRabinWithBase_eq_true_iff_pass).mp hpass)
    have hlocal := (pow_mod_list_prod_eq_one_iff factors a _ hpair).mp hglobal
    refine ⟨hlocal, ?_⟩
    rcases hpass' with hzero | ⟨j, hj, hminus⟩
    · refine ⟨0, Nat.zero_le _, ?_⟩
      have hzeroLocal := (pow_mod_list_prod_eq_one_iff factors a d hpair).mp hzero
      intro p hp
      exact
        (pow_oddPart_eq_one_iff_orderOf_twoAdic_eq_zero hdOdd (hlocal p hp)).mp (hzeroLocal p hp)
    · refine ⟨j + 1, hj, ?_⟩
      have hminusLocal := (pow_mod_list_prod_eq_neg_one_iff factors a (2 ^ j * d) hpair).mp hminus
      intro p hp
      have : Fact (Nat.Prime p) := ⟨hprimes p hp⟩
      exact (local_minus_one_iff_signature (hodd p hp) hdOdd (hlocal p hp)).mp (hminusLocal p hp)
  · rintro ⟨hlocal, t, hts, hsig⟩
    apply (strongMillerRabinWithBase_eq_true_iff_pass).2
    change
      (a : ZMod factors.prod) ^ Nat.divMaxPow (factors.prod - 1) 2 = 1 ∨
        ∃ j : ℕ,
          j < padicValNat 2 (factors.prod - 1) ∧
            (a : ZMod factors.prod) ^ (2 ^ j * Nat.divMaxPow (factors.prod - 1) 2) = -1
    rw [hs, hd]
    by_cases hz : t = 0
    · left
      apply (pow_mod_list_prod_eq_one_iff factors a d hpair).mpr
      intro p hp
      exact
        (pow_oddPart_eq_one_iff_orderOf_twoAdic_eq_zero hdOdd (hlocal p hp)).mpr
          ((hsig p hp).trans hz)
    · right
      have htpos : 0 < t := Nat.pos_of_ne_zero hz
      refine ⟨t - 1, (Nat.sub_lt htpos (by decide : 0 < 1)).trans_le hts, ?_⟩
      apply (pow_mod_list_prod_eq_neg_one_iff factors a _ hpair).mpr
      intro p hp
      have : Fact (Nat.Prime p) := ⟨hprimes p hp⟩
      have hpos : 0 < padicValNat 2 (orderOf (a : ZMod p)) := by
        rw [hsig p hp]
        exact htpos
      have hminus := local_minus_one_of_positive_signature hdOdd (hlocal p hp) hpos
      rw [hsig p hp] at hminus
      exact hminus

/-- A semiprime passes a base exactly when both local Fermat equations hold and the
two local multiplicative orders have the same two-adic valuation. -/
theorem strongMillerRabinWithBase_mul_iff_fermat_and_order_signature {p q a : ℕ}
    [Fact (Nat.Prime p)] [Fact (Nat.Prime q)] (hpOdd : Odd p) (hqOdd : Odd q) (hc : p.Coprime q)
    (hn : 1 < p * q) (hnOdd : Odd (p * q)) :
    strongMillerRabinWithBase (p * q) a = true ↔
      (a : ZMod p) ^ (p * q - 1) = 1 ∧
        (a : ZMod q) ^ (p * q - 1) = 1 ∧
        padicValNat 2 (orderOf (a : ZMod p)) = padicValNat 2 (orderOf (a : ZMod q)) := by
  obtain ⟨hs, hd, hdecomp⟩ := odd_sub_canonical_decomp hn hnOdd
  simpa only [← hdecomp] using
    (strongMillerRabinWithBase_mul_iff_fermat_and_order_signature_decomp hpOdd hqOdd hc hn hdecomp
      hd (a := a))

/-- A squarefree odd product passes a base exactly when all local Fermat equations hold
and the two-adic valuations of the local multiplicative orders agree. -/
theorem strongMillerRabinWithBase_factors_iff_fermat_and_order_signature (factors : List ℕ) {a : ℕ}
    (hpair : List.Pairwise Nat.Coprime factors) (hprimes : ∀ p ∈ factors, Nat.Prime p)
    (hodd : ∀ p ∈ factors, Odd p) (hn : 1 < factors.prod) (hnOdd : Odd factors.prod) :
    strongMillerRabinWithBase factors.prod a = true ↔
      (∀ p ∈ factors, (a : ZMod p) ^ (factors.prod - 1) = 1) ∧
        ∃ t : ℕ,
          t ≤ padicValNat 2 (factors.prod - 1) ∧
            ∀ p ∈ factors, padicValNat 2 (orderOf (a : ZMod p)) = t := by
  obtain ⟨hs, hd, hdecomp⟩ := odd_sub_canonical_decomp hn hnOdd
  simpa only [← hdecomp] using
    (strongMillerRabinWithBase_factors_iff_fermat_and_order_signature_decomp factors hpair hprimes
      hodd hn hnOdd hdecomp hd (a := a))

/-- Three prime factors meeting the Legendre, Korselt, and valuation conditions give a
strong pseudoprime to every listed base. -/
theorem arnault_three_factor_strongPseudoprime {p q r : ℕ} [Fact (Nat.Prime p)] [Fact (Nat.Prime q)]
    [Fact (Nat.Prime r)] {bases : List ℕ} (hpq : p.Coprime q) (hpqr : (p * q).Coprime r)
    (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r) (hnOdd : Odd (p * q * r))
    (hpdiv : p - 1 ∣ (p * q * r) - 1) (hqdiv : q - 1 ∣ (p * q * r) - 1)
    (hrdiv : r - 1 ∣ (p * q * r) - 1)
    (hpval : padicValNat 2 (p - 1) = padicValNat 2 ((p * q * r) - 1))
    (hqval : padicValNat 2 (q - 1) = padicValNat 2 ((p * q * r) - 1))
    (hrval : padicValNat 2 (r - 1) = padicValNat 2 ((p * q * r) - 1))
    (hleg :
      ∀ a ∈ bases,
        legendreSym p (a : ℤ) = -1 ∧ legendreSym q (a : ℤ) = -1 ∧ legendreSym r (a : ℤ) = -1) :
    IsStrongPseudoprimeTo (p * q * r) bases := by
  have hpge : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hqge : 2 ≤ q := (Fact.out : Nat.Prime q).two_le
  have hrge : 2 ≤ r := (Fact.out : Nat.Prime r).two_le
  have hn : 1 < p * q * r := by
    have hprod : 2 ≤ p * q :=
      hpge.trans (Nat.le_mul_of_pos_right p (lt_of_lt_of_le (by decide : 0 < 2) hqge))
    exact
      lt_of_lt_of_le (by decide : 1 < 2)
        (hprod.trans (Nat.le_mul_of_pos_right (p * q) (lt_of_lt_of_le (by decide : 0 < 2) hrge)))
  exact
    arnault_three_factor_strongPseudoprime_core hpq hpqr hpOdd hqOdd hrOdd hnOdd hpdiv hqdiv hrdiv
      hpval hqval hrval hleg

/--
For a pairwise coprime list of odd primes with composite product greater than one,
Korselt divisibility, equal two-adic valuations, and nonresidue status of every supplied base
at every factor, the product is a strong pseudoprime to all listed bases. The proof invokes
the core Euler-criterion and CRT construction; compositeness is an explicit premise.
-/
theorem arnault_factors_strongPseudoprime (factors bases : List ℕ)
    (hpair : List.Pairwise Nat.Coprime factors) (hprimes : ∀ p ∈ factors, Nat.Prime p)
    (hodd : ∀ p ∈ factors, Odd p) (hn : 1 < factors.prod) (hnOdd : Odd factors.prod)
    (hcomp : ¬Nat.Prime factors.prod) (hdiv : ∀ p ∈ factors, p - 1 ∣ factors.prod - 1)
    (hval : ∀ p ∈ factors, padicValNat 2 (p - 1) = padicValNat 2 (factors.prod - 1))
    (hleg : ∀ p ∈ factors, ∀ a ∈ bases, ¬IsSquare (a : ZMod p)) :
    IsStrongPseudoprimeTo factors.prod bases := by
  exact
    arnault_factors_strongPseudoprime_core factors bases hpair hprimes hodd hn hnOdd hcomp hdiv hval
      hleg

/--
For coprime factors whose product is odd and greater than one, global strong-test
acceptance is equivalent to both factors having initial power one or both having minus one
at the same canonical stage. Factor primality is unnecessary here. The proof obtains the
global decomposition and applies the two-factor CRT power identities.
-/
theorem strongMillerRabinWithBase_mul_eq_true_iff {p q a : ℕ} (hc : p.Coprime q) (hn : 1 < p * q)
    (hnOdd : Odd (p * q)) :
    strongMillerRabinWithBase (p * q) a = true ↔
      (let s := padicValNat 2 (p * q - 1)
       let d := Nat.divMaxPow (p * q - 1) 2
       ((a : ZMod p) ^ d = 1 ∧ (a : ZMod q) ^ d = 1) ∨
        ∃ j : ℕ, j < s ∧ (a : ZMod p) ^ (2 ^ j * d) = -1 ∧ (a : ZMod q) ^ (2 ^ j * d) = -1) := by
  obtain ⟨hs, hd, hdecomp⟩ := odd_sub_canonical_decomp hn hnOdd
  exact strongMillerRabinWithBase_mul_eq_true_iff_decomp hc hn hdecomp hd

/-- Under both local Fermat equations, matching order signatures characterize the
strong test at the canonical decomposition. -/
theorem strongMillerRabinWithBase_mul_iff_order_signature {p q a : ℕ} [Fact (Nat.Prime p)]
    [Fact (Nat.Prime q)] (hpOdd : Odd p) (hqOdd : Odd q) (hc : p.Coprime q) (hn : 1 < p * q)
    (hnOdd : Odd (p * q)) (hfp : (a : ZMod p) ^ (p * q - 1) = 1)
    (hfq : (a : ZMod q) ^ (p * q - 1) = 1) :
    strongMillerRabinWithBase (p * q) a = true ↔
      padicValNat 2 (orderOf (a : ZMod p)) = padicValNat 2 (orderOf (a : ZMod q)) := by
  obtain ⟨hs, hd, hdecomp⟩ := odd_sub_canonical_decomp hn hnOdd
  rw [hdecomp] at hfp hfq
  exact
    strongMillerRabinWithBase_mul_iff_order_signature_decomp hpOdd hqOdd hc hn hdecomp hd hfp hfq

end PseudoPrime.PrimeTest
