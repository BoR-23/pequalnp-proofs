import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Push

namespace PEqualNP.Outside.L_meta_4889_aux

def inc (p l : Fin 13) : Prop := (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)

abbrev incDecidable : DecidableRel inc := fun p l =>
  inferInstanceAs (Decidable ((p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)))

theorem symmInc {p l : Fin 13} (h : inc p l) : inc l p := by
  simpa [inc, Nat.add_comm] using h

def hit (z : Fin 26 → Bool) : Prop :=
  ∃ p l : Fin 13, inc p l ∧ z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true

def sample (P L : Finset (Fin 13)) (i : Fin 26) : Bool :=
  if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ P) else decide (Fin.ofNat 13 i.val ∈ L)

def avoiding (P : Finset (Fin 13)) : Finset (Fin 13) := by
  letI : DecidableRel inc := incDecidable
  exact {l : Fin 13 | ∀ p ∈ P, ¬inc p l}

theorem pointVal (P L : Finset (Fin 13)) (p : Fin 13) :
    sample P L (Fin.castAdd 13 p) = decide (p ∈ P) := by
  simp [sample, p.isLt]

theorem lineVal (P L : Finset (Fin 13)) (l : Fin 13) :
    sample P L (Fin.natAdd 13 l) = decide (l ∈ L) := by
  have e : Fin.ofNat 13 (13 + l.val) = l := by
    apply Fin.ext
    change (13 + l.val) % 13 = l.val
    rw [Nat.add_mod]
    simp [Nat.mod_eq_of_lt l.isLt]
  have hn : ¬ 13 + l.val < 13 := by omega
  simp only [sample, Fin.val_natAdd, if_neg hn, e]

theorem minimalSample (p l : Fin 13) (edge : inc p l) :
    Minimal hit (sample {p} {l}) := by
  refine ⟨⟨p, l, edge, by rw [pointVal]; simp, by rw [lineVal]; simp⟩, ?_⟩
  intro y hy below
  obtain ⟨a, b, _, ha, hb⟩ := hy
  have pa : a = p := by
    have h := below (Fin.castAdd 13 a)
    rw [ha, pointVal] at h
    exact Finset.mem_singleton.mp (of_decide_eq_true (Bool.eq_true_of_true_le h))
  have pl : b = l := by
    have h := below (Fin.natAdd 13 b)
    rw [hb, lineVal] at h
    exact Finset.mem_singleton.mp (of_decide_eq_true (Bool.eq_true_of_true_le h))
  subst a
  subst b
  intro i
  refine Fin.addCases (m := 13) (n := 13) (fun r => ?_) (fun s => ?_) i
  · rw [pointVal]
    by_cases e : r = p
    · subst r
      simp [ha]
    · simp [e]
  · rw [lineVal]
    by_cases e : s = l
    · subst s
      rw [hb]
      simp
    · simp [e]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem findLine (S : Finset (Fin 13)) (small : S.card ≤ 3) (p : Fin 13) (hp : p ∉ S) :
    ∃ l ∈ avoiding S, inc p l := by
  letI : DecidableRel inc := incDecidable
  let ns (q : Fin 13) : Finset (Fin 13) := Finset.univ.filter (inc q)
  have deg : ∀ q : Fin 13, (ns q).card = 4 := by decide
  have common : ∀ q r : Fin 13, q ≠ r → ((ns q) ∩ (ns r)).card ≤ 1 := by decide
  classical
  let covered := S.biUnion (fun q => ns p ∩ ns q)
  have bound : covered.card ≤ S.card := by
    calc
      covered.card ≤ ∑ q ∈ S, (ns p ∩ ns q).card := Finset.card_biUnion_le
      _ ≤ ∑ q ∈ S, 1 := Finset.sum_le_sum (fun q hq => common p q (fun e => hp (e ▸ hq)))
      _ = S.card := by simp
  have extra : ∃ l ∈ ns p, l ∉ covered := by
    by_contra h
    push Not at h
    have le := (Finset.card_le_card h).trans bound
    rw [deg] at le
    omega
  obtain ⟨l, hl, fresh⟩ := extra
  have edge : inc p l := (Finset.mem_filter.mp hl).2
  refine ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, edge⟩
  intro q hq hEdge
  exact fresh (Finset.mem_biUnion.mpr ⟨q, hq, Finset.mem_inter.mpr
    ⟨hl, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hEdge⟩⟩⟩)

theorem blockedLine (S : Finset (Fin 13)) (l : Fin 13) (hl : l ∉ avoiding S) :
    ∃ p ∈ S, inc p l := by
  letI : DecidableRel inc := incDecidable
  by_contra h
  push Not at h
  exact hl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

theorem maximalSample (P L : Finset (Fin 13))
    (safe : ∀ p ∈ P, ∀ l ∈ L, ¬inc p l)
    (newPoint : ∀ p ∉ P, ∃ l ∈ L, inc p l)
    (newLine : ∀ l ∉ L, ∃ p ∈ P, inc p l) :
    Maximal (fun z => ¬hit z) (sample P L) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨p, l, edge, hp, hl⟩
    rw [pointVal, decide_eq_true_eq] at hp
    rw [lineVal, decide_eq_true_eq] at hl
    exact safe p hp l hl edge
  · intro y noEdge above i
    refine Fin.addCases (m := 13) (n := 13) (fun p => ?_) (fun l => ?_) i
    · rw [pointVal]
      by_cases hp : p ∈ P
      · simp [hp]
      · cases hpy : y (Fin.castAdd 13 p) with
        | false => simp [hp]
        | true =>
          obtain ⟨l, hl, edge⟩ := newPoint p hp
          have yl : y (Fin.natAdd 13 l) = true := by
            have h := above (Fin.natAdd 13 l)
            rw [lineVal, decide_eq_true hl] at h
            exact Bool.eq_true_of_true_le h
          exact (noEdge ⟨p, l, edge, hpy, yl⟩).elim
    · rw [lineVal]
      by_cases hl : l ∈ L
      · simp [hl]
      · cases hly : y (Fin.natAdd 13 l) with
        | false => simp [hl]
        | true =>
          obtain ⟨p, hp, edge⟩ := newLine l hl
          have yp : y (Fin.castAdd 13 p) = true := by
            have h := above (Fin.castAdd 13 p)
            rw [pointVal, decide_eq_true hp] at h
            exact Bool.eq_true_of_true_le h
          exact (noEdge ⟨p, l, edge, yp, hly⟩).elim

theorem maxBoth (S : Finset (Fin 13)) (small : S.card ≤ 3) :
    Maximal (fun z => ¬hit z) (sample S (avoiding S)) ∧
      Maximal (fun z => ¬hit z) (sample (avoiding S) S) := by
  letI : DecidableRel inc := incDecidable
  have safe (p l : Fin 13) (hp : p ∈ S) (hl : l ∈ avoiding S) : ¬inc p l :=
    (Finset.mem_filter.mp hl).2 p hp
  refine ⟨maximalSample _ _ (fun p hp l hl => safe p l hp hl) (findLine S small) (blockedLine S), ?_⟩
  apply maximalSample
  · intro p hp l hl edge
    exact safe l p hl hp (symmInc edge)
  · intro p hp
    obtain ⟨l, hl, edge⟩ := blockedLine S p hp
    exact ⟨l, hl, symmInc edge⟩
  · intro l hl
    obtain ⟨p, hp, edge⟩ := findLine S small l hl
    exact ⟨p, hp, symmInc edge⟩

end PEqualNP.Outside.L_meta_4889_aux

theorem PEqualNP.Outside.L_meta_4889 : let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4); have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x4 : Finset (Fin (13 : ℕ))) => {x5 : Fin (13 : ℕ) | ∀ x6 ∈ x4, ¬x1 x6 x5}; (∀ (x5 x6 : Fin (13 : ℕ)), x1 x5 x6 → Minimal x2 (x3 {x5} {x6})) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), x5.card ≤ (3 : ℕ) → Maximal (fun (x7 : Fin (26 : ℕ) → Bool) => ¬x2 x7) (x3 x5 (x4 x5)) ∧ Maximal (fun (x7 : Fin (26 : ℕ) → Bool) => ¬x2 x7) (x3 (x4 x5) x5) := by
  exact ⟨PEqualNP.Outside.L_meta_4889_aux.minimalSample, PEqualNP.Outside.L_meta_4889_aux.maxBoth⟩
