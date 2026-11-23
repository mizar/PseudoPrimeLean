/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
public import PseudoPrime.Analysis.LogTaylorBounds
import all PseudoPrime.Data.Popcount
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Ring
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.EnvelopeTransfer

/-! # Kernel-checked prime counts by sieving a closed integer interval -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- Set bits at successive multiples of p by doubling the length of a progression. -/
private def positions (p n : ℕ) : ℕ :=
  Nat.rec 1 (fun i v => v.lor (v.shiftLeft (p.shiftLeft i))) n

private theorem positions_bit (p n k : ℕ) (hk : k < 2 ^ n) :
    (positions p n).testBit (p * k) = true := by
  induction n generalizing k with
  | zero =>
    have h : k = 0 := Nat.le_zero.mp (Nat.lt_succ_iff.mp hk)
    subst k
    simp only [Nat.mul_zero, positions]
    change (1 : ℕ).testBit 0 = true
    decide +kernel
  | succ n
    ih =>
    change ((positions p n) ||| ((positions p n) <<< (p <<< n))).testBit (p * k) = true
    rw [Nat.testBit_or, Bool.or_eq_true]
    by_cases h : k < 2 ^ n
    · exact Or.inl (ih k h)
    · right
      have hle := Nat.le_of_not_lt h
      have hsmall : k - 2 ^ n < 2 ^ n := by
        rw [pow_succ, Nat.mul_two] at hk
        exact (Nat.sub_lt_iff_lt_add hle).2 hk
      have hpos := Nat.mul_le_mul_left p hle
      rw [Nat.testBit_shiftLeft, Nat.shiftLeft_eq]
      simpa only [decide_eq_true hpos, Bool.true_and, ← Nat.mul_sub] using ih (k - 2 ^ n) hsmall

/-- Mark the positions i for which v + i is a multiple of p, starting at its first residue. -/
private def residueMask (width p v : ℕ) : ℕ :=
  let j := (p.sub v).mod p
  (Nat.ble j (width.sub 1)).rec 0
    ((positions p (((width.sub 1).sub j).div p).log2.succ).shiftLeft j)

/-- The first marked index is congruent to every index divisible after translation by v. -/
private theorem first_congr {p v i : ℕ} (hv : v < p) (hz : p ∣ v + i) :
    Nat.ModEq p ((p - v) % p) i := by
  let j := (p - v) % p
  have hj : p ∣ v + j := by
    apply Nat.dvd_of_mod_eq_zero
    change (v + ((p - v) % p)) % p = 0
    rw [Nat.add_mod_mod, Nat.add_sub_of_le hv.le, Nat.mod_self]
  exact
    Nat.ModEq.add_left_cancel' v
      ((Nat.modEq_zero_iff_dvd.mpr hj).trans (Nat.modEq_zero_iff_dvd.mpr hz).symm)

private theorem marked_residue {width p i v : ℕ} (hp : 0 < p) (hv : v < p) (hi : i < width)
    (hz : p ∣ v + i) : (residueMask width p v).testBit i = true := by
  let j := (p - v) % p
  have eqv := first_congr hv hz
  have hij : j ≤ i :=
    ((Nat.mod_eq_of_lt (Nat.mod_lt (p - v) hp)).symm.trans eqv).le.trans (Nat.mod_le i p)
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hij).mp eqv
  have hi' : i ≤ width - 1 := Nat.le_pred_of_lt hi
  have hle : k ≤ (width - 1 - j) / p := by
    apply (Nat.le_div_iff_mul_le hp).2
    rw [Nat.mul_comm, ← hk]
    exact Nat.sub_le_sub_right hi' j
  have hjw := Nat.ble_eq_true_of_le (hij.trans hi')
  change
    (Bool.rec (motive := fun _ => ℕ) 0 ((positions p (((width - 1 - j) / p).log2 + 1)).shiftLeft j)
            (Nat.ble j (width - 1))).testBit
        i =
      true
  rw [hjw]
  change ((positions p _) <<< j).testBit i = true
  rw [Nat.testBit_shiftLeft]
  simp only [decide_eq_true hij, Bool.true_and, hk]
  exact positions_bit p _ k (hle.trans_lt Nat.lt_log2_self)

/-- Mark multiples of p among the entries a + 1 + 2i of the sampled interval. -/
private def multipleMask (a width p : ℕ) : ℕ :=
  (Nat.beq p 2).rec (residueMask width p ((a.succ.mul (p.succ.div 2)).mod p))
    ((Nat.beq (a % 2) 0).rec (positions 1 (width.log2 + 1)) 0)

private theorem marks_divisor {a width p i : ℕ} (hp : p.Prime) (hi : i < width)
    (hd : p ∣ a + 1 + 2 * i) : (multipleMask a width p).testBit i = true := by
  rcases hp.eq_two_or_odd with htwo | hodd
  · subst p
    by_cases ha : a % 2 = 0
    · have hz := Nat.mod_eq_zero_of_dvd hd
      rw [Nat.add_mul_mod_self_left, Nat.add_mod, ha] at hz
      exact False.elim (Nat.one_ne_zero hz)
    · have he := Bool.eq_false_iff.mpr (ha ∘ Nat.eq_of_beq_eq_true)
      rw [multipleMask, Nat.beq_refl, he]
      simpa only [one_mul] using positions_bit 1 _ i (hi.trans (Nat.lt_log2_self))
  have hne : p ≠ 2 := by
    intro he
    subst p
    exact Nat.zero_ne_one hodd
  let k := (p + 1) / 2
  have hk : k * 2 = p + 1 := by
    apply Nat.div_mul_cancel
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.add_mod, hodd]
  have hb := dvd_mul_of_dvd_left hd k
  have he : (a + 1 + 2 * i) * k = (a + 1) * k + i + p * i := by
    calc
      _ = (a + 1) * k + (k * 2) * i := by ring
      _ = _ := by
        rw [hk]; ring
  rw [he] at hb
  have hr := (Nat.dvd_add_iff_left (Nat.dvd_mul_right p i)).2 hb
  rw [multipleMask, Bool.eq_false_iff.mpr (hne ∘ Nat.eq_of_beq_eq_true)]
  apply marked_residue hp.pos (Nat.mod_lt _ hp.pos) hi
  exact
    Nat.dvd_of_mod_eq_zero
      (by
        rw [Nat.mod_add_mod]
        exact Nat.mod_eq_zero_of_dvd hr)

private inductive Factors where
  | part (ps : List ℕ)
  | oddBlock (last : ℕ) (ps : List ℕ)
  | upperBlock (first last : ℕ) (offsets : List ℕ)
  | join (l r : Factors)

private def smallBase : ℕ :=
  let n : ℕ := 0x67bfd0
  let n := (n <<< 240) + 0x2bef01d7a4a7d3018fde15ef65434c5d2ecdecd32bdab805c5270799e540
  let n := (n <<< 240) + 0xc47d1b625175a57f3c30c90e4ef05875cab5f03c844a8a59e7e290a90a92
  let n := (n <<< 240) + 0xb39d2dfacd20556db05bb29ca1b5225b9bff9ef2ec239d08e783d4661600
  n

private theorem small_cover (m : ℕ) (hm : 2 ≤ m) (hu : m ≤ 512) : m ∣ smallBase := by
  have h : divisorBase 9 1 = smallBase := by decide +kernel
  rw [← h]
  exact dvd_divisorBase 9 1 m ((by decide : 1 ≤ 2).trans hm) (Nat.lt_succ_of_le hu)

private abbrev supported (q : ℕ) : Prop :=
  2 ≤ q ∧ (if q ≤ 512 then q.minFac = q else q < 513 * 513 ∧ q.gcd smallBase = 1)

private theorem supported_prime {q : ℕ} (h : supported q) : q.Prime := by
  obtain ⟨h2, ht⟩ := h
  by_cases hs : q ≤ 512
  · exact Nat.prime_def_minFac.mpr ⟨h2, (by simpa only [ite_eq_left hs] using ht)⟩
  rw [ite_eq_right hs] at ht
  refine Nat.prime_def_le_sqrt.mpr ⟨h2, ?_⟩
  intro m hm hroot hd
  have hu : q.sqrt ≤ 512 := Nat.le_of_lt_succ (Nat.sqrt_lt.mpr ht.1)
  have hg := Nat.dvd_gcd hd (small_cover m hm (hroot.trans hu))
  rw [ht.2] at hg
  exact (Nat.ne_of_gt hm) (Nat.eq_one_of_dvd_one hg)

private def primeWeight : List ℕ → ℕ
  | [] => 1
  | q :: qs => (if supported q then q else 1) * primeWeight qs

private def Factors.weight : Factors → ℕ
  | .part ps | .oddBlock _ ps => primeWeight ps
  | .upperBlock first _ offsets => primeWeight (offsets.map (first + ·))
  | .join l r => l.weight * r.weight

/-- Sieve only by trial divisors whose square does not exceed the right endpoint. -/
private def boundMask (a w p : ℕ) : ℕ :=
  (Nat.ble (p * p) (a + 2 * w)).rec 0 (multipleMask a w p)

private def unionMarks (a w : ℕ) : List ℕ → ℕ
  | [] => 0
  | p :: ps => boundMask a w p ||| unionMarks a w ps

/-- For an even start, the inverse of two modulo an odd prime is its upper half. -/
private def oddMark (half w p : ℕ) : ℕ :=
  let r := (half.add (p.succ.div 2)).mod p
  let j := (Nat.beq r 0).rec (p.sub r) 0
  let u := w.pred
  (Nat.ble j u).rec 0 ((positions p ((u.sub j).div p).log2.succ).shiftLeft j)

/-- The branch at residue zero replaces a second remainder by a subtraction. -/
private theorem oddMark_eq (half w p : ℕ) (hp : 0 < p) :
    oddMark half w p = residueMask w p ((half + (p + 1) / 2) % p) := by
  let r := (half + (p + 1) / 2) % p
  have first : (Nat.beq r 0).rec (p.sub r) 0 = (p - r) % p := by
    by_cases hr : r = 0
    · rw [hr, Nat.beq_refl, Nat.sub_zero, Nat.mod_self]
    · rw [Bool.eq_false_iff.mpr (hr ∘ Nat.eq_of_beq_eq_true)]
      exact (Nat.mod_eq_of_lt (Nat.sub_lt hp (Nat.pos_of_ne_zero hr))).symm
  exact
    congrArg
      (fun j : ℕ =>
        (Nat.ble j (w - 1)).rec (motive := fun _ => ℕ) 0
          ((positions p (((w - 1 - j) / p).log2 + 1)).shiftLeft j))
      first

/-- Fold the masks of eligible odd divisors into one exclusion mask. -/
private def oddMarks (half w : ℕ) : List ℕ → ℕ
  | [] => 0
  | p :: ps => oddMark half w p ||| oddMarks half w ps

/-- Check parity and the largest divisor once for an entire generated block. -/
private def blockMarks (a w last : ℕ) (ps : List ℕ) : ℕ :=
  if a % 2 = 0 ∧ last * last ≤ a + 2 * w then oddMarks (a / 2) w ps else unionMarks a w ps

/-- First odd-position index hit by this divisor in an even-start window. -/
private def firstIndex (half p : ℕ) : ℕ :=
  let r := (half.add (p.succ.div 2)).mod p
  (Nat.beq r 0).rec (p.sub r) 0

/-- Place a single bit when its index is inside the window. -/
private def bitAt (w j : ℕ) : ℕ :=
  (Nat.blt j w).rec 0 (Nat.shiftLeft 1 j)

/-- A window no wider than the prime contains at most one mark in its residue class. -/
private def singleMark (half w p : ℕ) : ℕ :=
  bitAt w (firstIndex half p)

/-- Set both possible in-range hits for each divisor in an active two-hit block. -/
private def pairMarks (half w first : ℕ) : List ℕ → ℕ
  | [] => 0
  | delta :: rest =>
    let p := first + delta
    let j := firstIndex half p
    bitAt w j ||| bitAt w (j + p) ||| pairMarks half w first rest

/-- Set the single possible bit for each eligible prime in a narrow window. -/
private def singleMarks (half w first : ℕ) : List ℕ → ℕ
  | [] => 0
  | delta :: rest => singleMark half w (first + delta) ||| singleMarks half w first rest

/-- Offset encoding certifies the minimum trial divisor and lets a whole block skip the sieve. -/
private def upperMarks (a w first last : ℕ) (offsets : List ℕ) : ℕ :=
  if a + 2 * w < first * first then 0
  else
    if a % 2 = 0 ∧ w ≤ first ∧ last * last ≤ a + 2 * w then singleMarks (a / 2) w first offsets
    else
      if w = 65536 ∧ a % 2 = 0 ∧ w ≤ first + first ∧ last * last ≤ a + 2 * w then
        pairMarks (a / 2) w first offsets
      else blockMarks a w last (offsets.map (first + ·))

private def Factors.excluded (a w : ℕ) : Factors → ℕ
  | .part ps => unionMarks a w ps
  | .oddBlock last ps => blockMarks a w last ps
  | .upperBlock first last offsets => upperMarks a w first last offsets
  | .join l r => l.excluded a w ||| r.excluded a w

private theorem marked_in_list {a w i p : ℕ} (hsq : p * p ≤ a + 2 * w) (hi : i < w) (hp : p.Prime)
    (hd : p ∣ a + 1 + 2 * i) (ps : List ℕ) (hm : p ∈ ps) :
    (unionMarks a w ps).testBit i = true := by
  induction ps with
  | nil => exact False.elim (List.not_mem_nil hm)
  | cons q qs ih =>
    rw [unionMarks, Nat.testBit_lor, Bool.or_eq_true]
    rcases List.mem_cons.mp hm with h | h
    · subst q
      exact
        Or.inl (by simpa only [boundMask, Nat.ble_eq_true_of_le hsq] using marks_divisor hp hi hd)
    · exact Or.inr (ih h)

/-- For an even entrance, translate a divisor of the sampled integer to its index residue. -/
private theorem index_dvd {a p i : ℕ} (ha : a % 2 = 0) (hp : p.Prime) (hd : p ∣ a + 1 + 2 * i) :
    p ∣ a / 2 + (p + 1) / 2 + i := by
  have half : 2 * (a / 2) = a := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero ha)
  rcases hp.eq_two_or_odd with h | h
  · subst p
    have bad := Nat.mod_eq_zero_of_dvd hd
    rw [Nat.add_mul_mod_self_left, Nat.add_mod, ha] at bad
    exact False.elim (Nat.one_ne_zero bad)
  have twice : (p + 1) / 2 * 2 = p + 1 := by
    apply Nat.div_mul_cancel
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.add_mod, h]
  have eqn : 2 * (a / 2 + (p + 1) / 2 + i) = (a + 1 + 2 * i) + p := by
    rw [Nat.mul_add, Nat.mul_add, half, Nat.mul_comm 2 ((p + 1) / 2), twice]
    ac_rfl
  have hd' : p ∣ 2 * (a / 2 + (p + 1) / 2 + i) := eqn ▸ Nat.dvd_add hd (Nat.dvd_refl p)
  have hn : ¬p ∣ 2 := by
    intro hh
    have he := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hh
    subst p
    exact Nat.zero_ne_one h
  exact (hp.dvd_mul.mp hd').resolve_left hn

/-- Divisibility of the sampled integer implies a mark at its index for an even start. -/
private theorem odd_marked {a w p i : ℕ} (ha : a % 2 = 0) (hp : p.Prime) (hi : i < w)
    (hd : p ∣ a + 1 + 2 * i) : (oddMark (a / 2) w p).testBit i = true := by
  rw [oddMark_eq _ _ _ hp.pos]
  apply marked_residue hp.pos (Nat.mod_lt _ hp.pos) hi
  apply Nat.dvd_of_mod_eq_zero
  rw [Nat.mod_add_mod]
  exact Nat.mod_eq_zero_of_dvd (index_dvd ha hp hd)

/-- A divisor in an eligible block excludes its composite multiple. -/
private theorem odd_list_marked {a w p i : ℕ} (ha : a % 2 = 0) (hp : p.Prime) (hi : i < w)
    (hd : p ∣ a + 1 + 2 * i) (ps : List ℕ) (hm : p ∈ ps) :
    (oddMarks (a / 2) w ps).testBit i = true := by
  induction ps with
  | nil => exact False.elim (List.not_mem_nil hm)
  | cons q qs ih =>
    rw [oddMarks, Nat.testBit_lor, Bool.or_eq_true]
    exact
      (List.mem_cons.mp hm).elim (fun h => Or.inl (h ▸ odd_marked ha hp hi hd))
        (fun h => Or.inr (ih h))

/-- For a divisible entry, its position reduced modulo the divisor is the first hit. -/
private theorem firstIndex_eq {a p i : ℕ} (ha : a % 2 = 0) (hp : p.Prime) (hd : p ∣ a + 1 + 2 * i) :
    firstIndex (a / 2) p = i % p := by
  let r := (a / 2 + (p + 1) / 2) % p
  have hz : p ∣ r + i :=
    Nat.dvd_of_mod_eq_zero
      (by
        dsimp only [r]
        rw [Nat.mod_add_mod]
        exact Nat.mod_eq_zero_of_dvd (index_dvd ha hp hd))
  have he := first_congr (Nat.mod_lt _ hp.pos) hz
  have heq := (Nat.mod_eq_of_lt (Nat.mod_lt (p - r) hp.pos)).symm.trans he
  rw [← heq]
  change (Nat.beq r 0).rec (p.sub r) 0 = (p - r) % p
  by_cases hr : r = 0
  · rw [hr, Nat.beq_refl, Nat.sub_zero, Nat.mod_self]
  · rw [Bool.eq_false_iff.mpr (hr ∘ Nat.eq_of_beq_eq_true)]
    exact (Nat.mod_eq_of_lt (Nat.sub_lt hp.pos (Nat.pos_of_ne_zero hr))).symm

/-- The guarded bit is set at every in-range requested index. -/
private theorem bitAt_self {w i : ℕ} (hi : i < w) : (bitAt w i).testBit i = true := by
  rw [bitAt, Nat.blt_eq.mpr hi]
  change ((1 : ℕ) <<< i).testBit i = true
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow_self]

/-- In a narrow window the certified index is exactly the first mark. -/
private theorem single_marked {a w p i : ℕ} (ha : a % 2 = 0) (hp : p.Prime) (hw : w ≤ p)
    (hi : i < w) (hd : p ∣ a + 1 + 2 * i) : (singleMark (a / 2) w p).testBit i = true := by
  rw [singleMark, firstIndex_eq ha hp hd, Nat.mod_eq_of_lt (hi.trans_le hw)]
  exact bitAt_self hi

/-- Below twice the period, a divisible position is the first or the second hit. -/
private theorem pair_hit {a w p i : ℕ} (ha : a % 2 = 0) (hp : p.Prime) (hw : w ≤ p + p) (hi : i < w)
    (hd : p ∣ a + 1 + 2 * i) :
    ((bitAt w (firstIndex (a / 2) p)) ||| bitAt w (firstIndex (a / 2) p + p)).testBit i = true := by
  rw [Nat.testBit_lor, Bool.or_eq_true, firstIndex_eq ha hp hd]
  by_cases h : i < p
  · rw [Nat.mod_eq_of_lt h]
    exact Or.inl (bitAt_self hi)
  · have hle := Nat.le_of_not_gt h
    have hlt := (Nat.sub_lt_iff_lt_add hle).2 (hi.trans_le hw)
    rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt hlt, Nat.sub_add_cancel hle]
    exact Or.inr (bitAt_self hi)

/-- Every represented divisor marks its in-range multiples in a two-hit block. -/
private theorem pair_list_marked {a w first p i : ℕ} (ha : a % 2 = 0) (hp : p.Prime)
    (hw : w ≤ first + first) (hi : i < w) (hd : p ∣ a + 1 + 2 * i) (ds : List ℕ)
    (hm : p ∈ ds.map (first + ·)) : (pairMarks (a / 2) w first ds).testBit i = true := by
  induction ds with
  | nil => exact False.elim (List.not_mem_nil hm)
  | cons delta rest ih =>
    rw [pairMarks, Nat.testBit_lor, Bool.or_eq_true]
    rcases List.mem_cons.mp hm with he | ht
    · subst p
      have hmin := Nat.le_add_right first delta
      exact Or.inl (pair_hit ha hp (hw.trans (Nat.add_le_add hmin hmin)) hi hd)
    · exact Or.inr (ih ht)

/-- Every represented divisor in a singleton block marks its multiple. -/
private theorem single_list_marked {a w first p i : ℕ} (ha : a % 2 = 0) (hp : p.Prime)
    (hw : w ≤ first) (hi : i < w) (hd : p ∣ a + 1 + 2 * i) (ds : List ℕ)
    (hm : p ∈ ds.map (first + ·)) : (singleMarks (a / 2) w first ds).testBit i = true := by
  induction ds with
  | nil => exact False.elim (List.not_mem_nil hm)
  | cons delta rest ih =>
    rw [singleMarks, Nat.testBit_lor, Bool.or_eq_true]
    rcases List.mem_cons.mp hm with he | ht
    · subst p
      exact Or.inl (single_marked ha hp (hw.trans (Nat.le_add_right first delta)) hi hd)
    · exact Or.inr (ih ht)

private theorem prime_in_weight {p : ℕ} (hp : p.Prime) (qs : List ℕ) (h : p ∣ primeWeight qs) :
    p ∈ qs := by
  induction qs with
  | nil => exact False.elim (hp.not_dvd_one h)
  | cons q qs ih =>
    rcases hp.dvd_mul.mp h with hq | ht
    · by_cases hprime : supported q
      · rw [ite_eq_left hprime] at hq
        exact
          List.mem_cons.mpr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (supported_prime hprime)).1 hq))
      · rw [ite_eq_right hprime] at hq
        exact False.elim (hp.not_dvd_one hq)
    · exact List.mem_cons.mpr (Or.inr (ih ht))

private theorem marked_by_factor {a w i p : ℕ} (hsq : p * p ≤ a + 2 * w) (hi : i < w) (hp : p.Prime)
    (hd : p ∣ a + 1 + 2 * i) (f : Factors) (hf : p ∣ f.weight) :
    (f.excluded a w).testBit i = true := by
  induction f with
  | part ps => exact marked_in_list hsq hi hp hd ps (prime_in_weight hp ps hf)
  | oddBlock last ps =>
    have hm := prime_in_weight hp ps hf
    by_cases h : a % 2 = 0 ∧ last * last ≤ a + 2 * w
    · simpa only [Factors.excluded, blockMarks, ite_eq_left h] using
        odd_list_marked h.1 hp hi hd ps hm
    · simpa only [Factors.excluded, blockMarks, ite_eq_right h] using
        marked_in_list hsq hi hp hd ps hm
  | upperBlock first last
    ds =>
    have hm := prime_in_weight hp (ds.map (first + ·)) hf
    obtain ⟨delta, _, he⟩ := List.mem_map.mp hm
    have hmin : first ≤ p := he ▸ Nat.le_add_right first delta
    have active := (Nat.mul_le_mul hmin hmin).trans hsq
    rw [Factors.excluded, upperMarks, ite_eq_right (Nat.not_lt_of_ge active)]
    by_cases h : a % 2 = 0 ∧ w ≤ first ∧ last * last ≤ a + 2 * w
    · rw [ite_eq_left h]
      exact single_list_marked h.1 hp h.2.1 hi hd ds hm
    · rw [ite_eq_right h]
      by_cases pair : w = 65536 ∧ a % 2 = 0 ∧ w ≤ first + first ∧ last * last ≤ a + 2 * w
      · rw [ite_eq_left pair]
        exact pair_list_marked pair.2.1 hp pair.2.2.1 hi hd ds hm
      rw [ite_eq_right pair]
      by_cases hall : a % 2 = 0 ∧ last * last ≤ a + 2 * w
      · simpa only [blockMarks, ite_eq_left hall] using odd_list_marked hall.1 hp hi hd _ hm
      · simpa only [blockMarks, ite_eq_right hall] using marked_in_list hsq hi hp hd _ hm
  | join l r ihl ihr =>
    rw [Factors.excluded, Nat.testBit_lor, Bool.or_eq_true]
    exact (hp.dvd_mul.mp hf).imp ihl ihr

private def liveBits (f : Factors) (a w : ℕ) : ℕ :=
  let top := (1 <<< w) - 1
  top ^^^ (top &&& f.excluded a w)

private theorem live_is_prime {a w B i : ℕ} (f : Factors)
    (hbase : ∀ p, p.Prime → p ≤ B → p ∣ f.weight) (ha : 1 ≤ a) (hb : a + 2 * w < (B + 1) * (B + 1))
    (hi : i < w) (hlive : (liveBits f a w).testBit i = true) : (a + 1 + 2 * i).Prime := by
  let n := a + 1 + 2 * i
  have h2 : 2 ≤ n := (Nat.add_le_add_right ha 1).trans (Nat.le_add_right _ _)
  refine Nat.prime_def_le_sqrt.mpr ⟨h2, ?_⟩
  intro m hm hs hd
  have hp := Nat.minFac_prime (Nat.ne_of_gt hm)
  have hnb : n ≤ a + 2 * w := by
    have hstep := Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hi)
    rw [Nat.mul_succ] at hstep
    change a + 1 + 2 * i ≤ a + 2 * w
    rw [Nat.add_right_comm a 1 (2 * i), Nat.add_assoc]
    exact Nat.add_le_add_left ((Nat.le_succ (2 * i + 1)).trans hstep) a
  have hu : n.sqrt ≤ B := Nat.le_of_lt_succ (Nat.sqrt_lt.mpr (hnb.trans_lt hb))
  have hms : m.minFac ≤ n.sqrt := (Nat.minFac_le (Nat.zero_lt_of_lt hm)).trans hs
  have hsq := (Nat.mul_le_mul hms hms).trans ((Nat.sqrt_le n).trans hnb)
  have hm :=
    marked_by_factor hsq hi hp ((Nat.minFac_dvd m).trans hd) f
      (hbase _ hp ((Nat.minFac_le (Nat.zero_lt_of_lt hm)).trans (hs.trans hu)))
  simp only [liveBits, Nat.testBit_xor, Nat.testBit_and, hm, Bool.and_true,
    bne_self_eq_false] at hlive
  exact Bool.noConfusion hlive

private def nibbleCount (z : ℕ) : ℕ :=
  (Nat.shiftRight 0x4332322132212110 (4 * (z % 16))) % 16

private theorem nibble_checked (z : Fin 16) : nibbleCount z.val = Data.bitCountPrefix 4 z.val := by
  exact
    (show ∀ n : Fin 16, nibbleCount n.val = Data.bitCountPrefix 4 n.val from by decide +kernel) z

/-- Four bits per table entry store the population count of each byte. -/
private def byteCount (z : ℕ) : ℕ :=
  let t := 0x8776766576656554766565546554544376656554655454436554544354434332
  let t := (t <<< 256) + 0x7665655465545443655454435443433265545443544343325443433243323221
  let t := (t <<< 256) + 0x7665655465545443655454435443433265545443544343325443433243323221
  let t := (t <<< 256) + 0x6554544354434332544343324332322154434332433232214332322132212110
  Nat.land (Nat.shiftRight t (Nat.shiftLeft (Nat.land z 255) 2)) 15

private theorem byte_checked (z : Fin 256) : byteCount z.val = Data.bitCountPrefix 8 z.val := by
  exact (show ∀ n : Fin 256, byteCount n.val = Data.bitCountPrefix 8 n.val from by decide +kernel) z

/-- Split a packed mask into equal halves until each leaf has the given bit width. -/
private def countTree (width : ℕ) (leaf : ℕ → ℕ) (d : ℕ) : ℕ → ℕ :=
  Nat.rec leaf
    (fun i rec z =>
      let n := Nat.shiftLeft width i
      Nat.add (rec (Nat.land z ((1 <<< n) - 1))) (rec (Nat.shiftRight z n)))
    d

/-- Count one 64-bit leaf with the certified parallel population count. -/
private def wordCount (z : ℕ) : ℕ :=
  Data.popcount64 (BitVec.ofNat 64 z)

/-- Count full words in wide windows and retain byte and nibble leaves for short windows. -/
private def countMask : ℕ → ℕ → ℕ
  | 0 => nibbleCount
  | 1 => byteCount
  | 2 => countTree 8 byteCount 1
  | 3 => countTree 8 byteCount 2
  | d + 4 => countTree 64 wordCount d

private theorem prime_step {a lo : ℕ} (hp : (a + 1).Prime) (hlo : 0 < lo) (ha : lo ≤ a + 1) :
    Real.log lo ≤ Chebyshev.theta (a + 1 : ℕ) - Chebyshev.theta a := by
  have he := PseudoPrime.AnalyticNumberTheory.Arithmetic.theta_prefix_add_interval (Nat.le_succ a)
  simp only [Nat.Ioc_succ_singleton, Finset.filter_singleton, hp, ite_true,
    Finset.sum_singleton] at he
  rw [← he, add_sub_cancel_left]
  exact Real.log_le_log (Nat.cast_pos.mpr hlo) (Nat.cast_le.mpr ha)

private theorem scan_gain (a lo z n : ℕ) (hlo : 1 ≤ lo) (ha : lo ≤ a)
    (ok : ∀ i < n, z.testBit i = true → (a + 1 + 2 * i).Prime) :
    (Data.bitCountPrefix n z : ℝ) * Real.log lo ≤
      Chebyshev.theta (a + 2 * n : ℕ) - Chebyshev.theta a := by
  induction n with
  | zero =>
    simp only [Data.bitCountPrefix, Nat.cast_zero, zero_mul, Nat.mul_zero, Nat.add_zero, sub_self,
      le_refl]
  | succ n ih =>
    have h := ih (fun i hi => ok i (hi.trans (Nat.lt_succ_self n)))
    rw [Nat.mul_succ, ← Nat.add_assoc]
    have he : a + 1 + 2 * n = a + 2 * n + 1 := by rw [Nat.add_right_comm]
    have he2 := Chebyshev.theta_mono (Nat.cast_le.mpr (Nat.le_succ (a + 2 * n + 1)))
    by_cases hb : z.testBit n = true
    · have hp := he ▸ ok n (Nat.lt_succ_self n) hb
      have hg := prime_step hp hlo (ha.trans (Nat.le_add_right a (2 * n)) |>.trans (Nat.le_succ _))
      rw [Data.bitCountPrefix, ite_eq_left hb, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      linarith only [hg, h, he2]
    · have hh := Chebyshev.theta_mono (Nat.cast_le.mpr (Nat.le_add_right (a + 2 * n) 2))
      rw [Data.bitCountPrefix, ite_eq_right hb, Nat.add_zero]
      linarith only [h, hh]

/-- Each set bit in a checked byte contributes a certified prime to the theta increment. -/
private theorem byte_leaf_gain (a lo z : ℕ) (hlo : 1 ≤ lo) (ha : lo ≤ a)
    (ok : ∀ i < 8, z.testBit i = true → (a + 1 + 2 * i).Prime) :
    (byteCount z : ℝ) * Real.log lo ≤ Chebyshev.theta (a + 2 * 8 : ℕ) - Chebyshev.theta a := by
  let v : Fin 256 := ⟨z % 256, Nat.mod_lt _ (by decide)⟩
  have he : byteCount z = Data.bitCountPrefix 8 v.val := by
    rw [← byte_checked]
    have hmask (n : ℕ) : Nat.land n 255 = n % 256 := Nat.and_two_pow_sub_one_eq_mod n 8
    simp only [byteCount, v, hmask, Nat.mod_mod]
  rw [he]
  apply scan_gain a lo v.val 8 hlo ha
  intro i hi hb
  change (z % 2 ^ 8).testBit i = true at hb
  simp only [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and] at hb
  exact ok i hi hb

/-- The 64-bit SWAR equality transfers the prefix bound to an entire word. -/
private theorem word_leaf_gain (a lo z : ℕ) (hlo : 1 ≤ lo) (ha : lo ≤ a)
    (ok : ∀ i < 64, z.testBit i = true → (a + 1 + 2 * i).Prime) :
    (wordCount z : ℝ) * Real.log lo ≤ Chebyshev.theta (a + 2 * 64 : ℕ) - Chebyshev.theta a := by
  rw [wordCount, Data.popcount64_eq_prefix]
  apply scan_gain a lo _ 64 hlo ha
  intro i hi hb
  change (z % 2 ^ 64).testBit i = true at hb
  apply ok i hi
  simpa only [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and] using hb

/-- Join the theta increments from the two disjoint halves of each counting node. -/
private theorem tree_gain (width : ℕ) (leaf : ℕ → ℕ)
    (gain :
      ∀ a lo z : ℕ,
        1 ≤ lo →
          lo ≤ a →
          (∀ i < width, z.testBit i = true → (a + 1 + 2 * i).Prime) →
          (leaf z : ℝ) * Real.log lo ≤ Chebyshev.theta (a + 2 * width : ℕ) - Chebyshev.theta a)
    (a lo z d : ℕ) (hlo : 1 ≤ lo) (ha : lo ≤ a)
    (ok : ∀ i < width * 2 ^ d, z.testBit i = true → (a + 1 + 2 * i).Prime) :
    (countTree width leaf d z : ℝ) * Real.log lo ≤
      Chebyshev.theta (a + 2 * (width * 2 ^ d) : ℕ) - Chebyshev.theta a := by
  induction d generalizing a z with
  | zero =>
    change (leaf z : ℝ) * _ ≤ _
    simp only [pow_zero, Nat.mul_one] at ok ⊢
    exact gain a lo z hlo ha ok
  | succ d ih =>
    let s := width * 2 ^ d
    have he : width * 2 ^ (d + 1) = s + s := by rw [pow_succ, Nat.mul_two, Nat.mul_add]
    have hs : width <<< d = s := Nat.shiftLeft_eq _ _
    have hl :=
      ih a (z % (1 <<< s)) ha
        (by
          intro i hi hb
          rw [Nat.one_shiftLeft, Nat.testBit_mod_two_pow] at hb
          change i < s at hi
          simp only [decide_eq_true hi, Bool.true_and] at hb
          exact ok i (he ▸ hi.trans_le (Nat.le_add_right s s)) hb)
    have hr :=
      ih (a + 2 * s) (z >>> s) (ha.trans (Nat.le_add_right _ _))
        (by
          intro i hi hb
          rw [Nat.testBit_shiftRight] at hb
          have hp := ok (s + i) (he ▸ Nat.add_lt_add_left hi s) hb
          simpa only [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm 1 (2 * s)] using hp)
    change
      ((countTree width leaf d (z &&& ((1 <<< (width <<< d)) - 1)) +
                countTree width leaf d (z >>> (width <<< d)) :
              ℕ) :
            ℝ) *
          _ ≤
        _
    rw [hs, Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.cast_add, add_mul, he,
      Nat.mul_add, ← Nat.add_assoc]
    rw [Nat.one_shiftLeft] at hl
    linarith only [hl, hr]

/-- Convert the count at any supported depth into a lower bound for the theta increment. -/
private theorem rank_gain (a lo z d : ℕ) (hlo : 1 ≤ lo) (ha : lo ≤ a)
    (ok : ∀ i < 4 * 2 ^ d, z.testBit i = true → (a + 1 + 2 * i).Prime) :
    (countMask d z : ℝ) * Real.log lo ≤
      Chebyshev.theta (a + 2 * (4 * 2 ^ d) : ℕ) - Chebyshev.theta a := by
  match d with
  | 0 =>
    let v : Fin 16 := ⟨z % 16, Nat.mod_lt _ (by decide)⟩
    have he : nibbleCount z = Data.bitCountPrefix 4 v.val := by
      rw [← nibble_checked]
      simp only [nibbleCount, v, Nat.mod_mod]
    rw [countMask, he]
    apply scan_gain a lo v.val 4 hlo ha
    intro i hi hb
    change (z % 2 ^ 4).testBit i = true at hb
    simp only [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and] at hb
    exact ok i hi hb
  | 1 => exact byte_leaf_gain a lo z hlo ha ok
  | 2 => exact tree_gain 8 byteCount byte_leaf_gain a lo z 1 hlo ha ok
  | 3 => exact tree_gain 8 byteCount byte_leaf_gain a lo z 2 hlo ha ok
  |
  d + 4 =>
    have width : 4 * 2 ^ (d + 4) = 64 * 2 ^ d := by
      rw [pow_add, Nat.mul_comm (2 ^ d) (2 ^ 4), ← Nat.mul_assoc]
      rfl
    rw [width] at ok ⊢
    exact tree_gain 64 wordCount word_leaf_gain a lo z d hlo ha ok

private def factors2 : Factors :=
  .part
    [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
      101, 103, 107, 109, 113, 127, 131]

private def factors137 : Factors :=
  .part
    [137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
      239, 241, 251]

private def factors257 : Factors :=
  .oddBlock 443
    [257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367,
      373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443]

private def factors449 : Factors :=
  .oddBlock 647
    [449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571,
      577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647]

private def factors653 : Factors :=
  .oddBlock 863
    [653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773,
      787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863]

private def factors877 : Factors :=
  .oddBlock 1091
    [877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009,
      1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091]

private def factors1093 : Factors :=
  .oddBlock 1307
    [1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213,
      1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303,
      1307]

private def factors1319 : Factors :=
  .oddBlock 1559
    [1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451,
      1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553,
      1559]

private def factors1567 : Factors :=
  .oddBlock 1789
    [1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667,
      1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787,
      1789]

private def factors1801 : Factors :=
  .oddBlock 2053
    [1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931,
      1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039,
      2053]

private def factors2063 : Factors :=
  .oddBlock 2297
    [2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161,
      2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293,
      2297]

private def factors2309 : Factors :=
  .oddBlock 2551
    [2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411,
      2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549,
      2551]

private def factors2557 : Factors :=
  .oddBlock 2791
    [2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687,
      2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789,
      2791]

private def factors2797 : Factors :=
  .oddBlock 3061
    [2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917,
      2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049,
      3061]

private def factors3067 : Factors :=
  .oddBlock 3331
    [3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209,
      3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329,
      3331]

private def factors3343 : Factors :=
  .oddBlock 3583
    [3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467,
      3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581,
      3583]

private def factors3593 : Factors :=
  .oddBlock 3851
    [3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709,
      3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847,
      3851]

private def factors3853 : Factors :=
  .oddBlock 4093
    [3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989,
      4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093]

private def basis : Factors :=
  (.join
    (.join
      (.join (.join (.join factors2 factors137) (.join factors257 factors449))
        (.join (.join factors653 factors877) (.join factors1093 factors1319)))
      (.join (.join (.join factors1567 factors1801) (.join factors2063 factors2309))
        (.join (.join factors2557 factors2797) (.join factors3067 factors3343))))
    (.join factors3593 factors3853))

private theorem coversPacked {p : ℕ} (hp : p.Prime) (hb : p ≤ 4096) : p ∣ basis.weight := by
  have h : divisorBase 12 1 ∣ basis.weight ^ 12 := by decide +kernel
  exact hp.dvd_of_dvd_pow ((dvd_divisorBase 12 1 p hp.one_lt.le (Nat.lt_succ_of_le hb)).trans h)

/-- Count certified primes among alternating integers in a window of width eight times
a power of two.
Every counted position is certified prime below the square of the next divisor. -/
def packedCount4096 (a d : ℕ) : ℕ :=
  countMask d (liveBits basis a (4 * 2 ^ d))

/-- Apply a verified prime count to the lower theta bound across this closed real interval. -/
theorem packedTile4096 (a b d k r j : ℕ) (e f q u : ℚ) (ha : 1000000 ≤ a)
    (hb : b < (4096 + 1) * (4096 + 1)) (he : a + 8 * 2 ^ d = b) (hc : packedCount4096 a d = k)
    (hs : r ^ 2 ≤ a) (hl : PseudoPrime.Analysis.rationalLogIntervalCheck a j 20 q u = true)
    (hf : f ≤ e + k * q) (hw : (b : ℚ) ≤ e + 5 * r) : ThetaLowerSegment a b e f := by
  have ha1 : 1 ≤ a := (by decide : 1 ≤ 1000000).trans ha
  have hwid : 2 * (4 * 2 ^ d) = 8 * 2 ^ d := (Nat.mul_assoc 2 4 (2 ^ d)).symm
  have hend : a + 2 * (4 * 2 ^ d) = b := hwid ▸ he
  have hg :=
    rank_gain a a (liveBits basis a (4 * 2 ^ d)) d ha1 le_rfl
      (fun _ hi => live_is_prime basis (fun _ => coversPacked) ha1 (hend ▸ hb) hi)
  change (packedCount4096 a d : ℝ) * Real.log a ≤ _ at hg
  rw [hend, hc] at hg
  have hq : (q : ℝ) ≤ Real.log a := by
    simpa only [Rat.cast_natCast] using (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1
  intro hentry
  have hk := mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg (α := ℝ) k)
  have hf' := (Rat.cast_le (K := ℝ)).2 hf
  have hw' := (Rat.cast_le (K := ℝ)).2 hw
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] at hf' hw'
  refine ⟨by linarith only [hf', hk, hg, hentry], fun x hax hxb => ?_⟩
  have hx : 1000000 ≤ x := (show (1000000 : ℝ) ≤ a by exact_mod_cast ha).trans hax
  have hr := Real.le_sqrt_of_sq_le ((show (r : ℝ) ^ 2 ≤ a by exact_mod_cast hs).trans hax)
  have ht : (5 : ℝ) ≤ Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) :=
    Joint.coefficient_from_ticks (n := 1000000) (m := 13000) (by decide) hx (by decide +kernel)
      (by norm_num only) (by norm_num only) (by norm_num only)
  apply le_trans _ ht
  apply (div_le_iff₀ (Real.sqrt_pos.2 (lt_of_lt_of_le (by norm_num only) hx))).2
  linarith only [hw', hr, hxb, hentry, Chebyshev.theta_mono hax]

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
