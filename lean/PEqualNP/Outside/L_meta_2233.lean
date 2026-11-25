import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover (gateAt gateOpDecEq)

namespace PEqualNP.Outside.L_meta_2233

local instance : DecidableEq GateOp := gateOpDecEq

theorem gateAtEq (C : Circuit) {j : ℕ} (h : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt,List.getD_eq_getElem?_getD,h]

inductive WireOrChain (n : ℕ) (gs : List Gate) (source : ℕ) : ℕ → Prop
  | source : WireOrChain n gs source source
  | gate {j w : ℕ} (bound : j < gs.length) (hor : gs[j].op = .or)
      (reader : w ∈ gs[j].inputs) (earlier : w < n + j) (path : WireOrChain n gs source w) :
      WireOrChain n gs source (n + j)

theorem evalLength (n : ℕ) (gs : List Gate) (before : List (List ℕ)) :
    (gs.foldl (orStep n) before).length = before.length + gs.length := by
  induction gs generalizing before with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

theorem preserve (n : ℕ) (gs : List Gate) (before : List (List ℕ)) {i : ℕ}
    (hi : i < before.length) :
    (gs.foldl (orStep n) before).getD i [] = before.getD i [] := by
  induction gs generalizing before with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [orStep]; omega)]
    unfold orStep
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem reachAt (n : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (orStep n) []).getD j [] =
      j :: (if gs[j].op = .or then
        (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
          (fun w => ((gs.take j).foldl (orStep n) []).getD (w - n) [])
        else []) := by
  have hp : j < ((gs.take (j + 1)).foldl (orStep n) []).length := by
    rw [evalLength, List.length_take, Nat.min_eq_left (Nat.succ_le_iff.mpr hj)]
    simp
  conv_lhs => rw [← List.take_append_drop (j + 1) gs, List.foldl_append, preserve n _ _ hp]
  rw [List.take_succ_eq_append_getElem hj, List.foldl_append, List.foldl_cons, List.foldl_nil]
  let pre := (gs.take j).foldl (orStep n) []
  have len : pre.length = j := by
    simp [pre, evalLength, Nat.min_eq_left hj.le]
  have extract (x : List ℕ) : (pre ++ [x]).getD j [] = x := by
    rw [← len]
    simp [List.getD_eq_getElem?_getD]
  change (pre ++ [pre.length :: (if gs[j].op = .or then
    (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap
      (fun w => pre.getD (w - n) []) else [])]).getD j [] = _
  rw [extract]
  simp only [len, pre]


theorem reachesSelf {n : ℕ} (C : Circuit) {k : ℕ} (hk : k < C.gates.length) :
    OrReaches n C (n + k) k := by
  refine ⟨by omega, ?_⟩
  have sub : n + k - n = k := by omega
  rw [sub]
  change k ∈ (C.gates.foldl (orStep n) []).getD k []
  rw [reachAt _ _ _ hk]
  exact List.mem_cons_self

theorem reachViaOr {n : ℕ} (C : Circuit) {k j i : ℕ} (hj : j < C.gates.length)
    (orOp : C.gates[j].op = .or) (reader : i ∈ C.gates[j].inputs) (earlier : i < n + j)
    (prev : OrReaches n C i k) : OrReaches n C (n + j) k := by
  have sub : n + j - n = j := by omega
  refine ⟨by omega, ?_⟩
  rw [sub]
  change k ∈ (C.gates.foldl (orStep n) []).getD j []
  rw [reachAt _ _ _ hj, ite_eq_left orOp]
  refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨i, ?_, ?_⟩)
  · exact List.mem_filter.mpr ⟨reader, decide_eq_true ⟨prev.1, earlier⟩⟩
  · have earlierIdx : i - n < ((C.gates.take j).foldl (orStep n) []).length := by
      rw [evalLength, List.length_take, Nat.min_eq_left hj.le]
      have := prev.1
      simp
      omega
    have orig : k ∈ (C.gates.foldl (orStep n) []).getD (i - n) [] := prev.2
    have same : (C.gates.foldl (orStep n) []).getD (i - n) [] =
        ((C.gates.take j).foldl (orStep n) []).getD (i - n) [] := by
      conv_lhs => rw [← List.take_append_drop j C.gates, List.foldl_append,
        preserve n _ _ earlierIdx]
    exact same ▸ orig

theorem reachFromPath {n : ℕ} (C : Circuit) {k : ℕ} (hk : k < C.gates.length)
    {w : ℕ} (path : WireOrChain n C.gates (n + k) w) :
    OrReaches n C w k := by
  induction path with
  | source => exact reachesSelf C hk
  | gate jLength orOp reader earlier _ ih => exact reachViaOr C jLength orOp reader earlier ih

theorem pathFromReach {n : ℕ} (C : Circuit) (k : ℕ) :
    ∀ w, OrReaches n C w k → WireOrChain n C.gates (n + k) w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro reaches
    let j := w - n
    have wEq : w = n + j := by have := reaches.1; dsimp [j]; omega
    have member : k ∈ (C.gates.foldl (orStep n) []).getD j [] := reaches.2
    have hj : j < C.gates.length := by
      by_contra tooHigh
      have large : (C.gates.foldl (orStep n) []).length ≤ j := by
        rw [evalLength]
        simp
        omega
      rw [List.getD_eq_default _ _ large] at member
      simp at member
    rw [reachAt _ _ _ hj] at member
    rcases List.mem_cons.mp member with equal | child
    · rw [equal] at *
      rw [wEq]
      exact .source
    · by_cases orOp : C.gates[j].op = .or
      · rw [ite_eq_left orOp] at child
        obtain ⟨i, valid, has⟩ := List.mem_flatMap.mp child
        obtain ⟨reader, sel⟩ := List.mem_filter.mp valid
        have ⟨above, earlier⟩ := of_decide_eq_true sel
        have earlierIdx : i - n < ((C.gates.take j).foldl (orStep n) []).length := by
          rw [evalLength, List.length_take, Nat.min_eq_left hj.le]
          simp
          omega
        have same : (C.gates.foldl (orStep n) []).getD (i - n) [] =
            ((C.gates.take j).foldl (orStep n) []).getD (i - n) [] := by
          conv_lhs => rw [← List.take_append_drop j C.gates, List.foldl_append,
            preserve n _ _ earlierIdx]
        have prev := ih i (by omega) ⟨above, same ▸ has⟩
        rw [wEq]
        exact .gate hj orOp reader earlier prev
      · simp [orOp] at child

theorem firstRead {n a b : ℕ} (C : Circuit)
    (path : WireOrChain n C.gates a b) :
    a = b ∨ ∃ (j : ℕ) (hj : j < C.gates.length), C.gates[j].op = .or ∧
      a ∈ C.gates[j].inputs ∧ WireOrChain n C.gates (n + j) b := by
  induction path with
  | source => exact Or.inl rfl
  | gate jBound op reader earlier _ ih =>
    apply Or.inr
    rcases ih with same | ⟨k, h, o, aIn, tail⟩
    · exact ⟨_, jBound, op, same ▸ reader, .source⟩
    · exact ⟨k, h, o, aIn, .gate jBound op reader earlier tail⟩

end PEqualNP.Outside.L_meta_2233

open PEqualNP.Outside.L_meta_2233 in
theorem PEqualNP.Outside.L_meta_2233 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1 := by
  classical
  intro n C F legal terminal
  let Q := (Finset.range C.gates.length).filter fun i =>
    (gateAt C i).op = .or ∧ OrReaches n C C.output i
  have qMem (i : ℕ) : i ∈ Q ↔ i < C.gates.length ∧
      (gateAt C i).op = .or ∧ OrReaches n C C.output i := by
    simp [Q,Finset.mem_filter]
  have unionsDisjoint : Disjoint F Q := by
    apply Finset.disjoint_left.mpr
    intro j f q
    have andOp := (terminal j f).2.1
    have orOp := ((qMem j).mp q).2.1
    rw [andOp] at orOp
    cases orOp
  let inputs (i : ℕ) := ((gateAt C i).inputs.map (· - n)).toFinset
  have cover : F ∪ Q ⊆ {C.output-n} ∪ Q.biUnion inputs := by
    intro j both
    have jLt : j < C.gates.length := (Finset.mem_union.mp both).elim
      (fun h => (terminal j h).1) (fun h => ((qMem j).mp h).1)
    have reach : OrReaches n C C.output j := (Finset.mem_union.mp both).elim
      (fun h => (terminal j h).2.2) (fun h => ((qMem j).mp h).2.2)
    rcases firstRead C (pathFromReach C j C.output reach) with root | ⟨i,hi,op,reader,path⟩
    · have eq : j=C.output-n := by omega
      exact Finset.mem_union_left _ (Finset.mem_singleton.mpr eq)
    · have iIn : i ∈ Q :=
        (qMem i).mpr ⟨hi, gateAtEq C hi ▸ op, reachFromPath C hi path⟩
      have member : j ∈ inputs i := by
        change j ∈ ((gateAt C i).inputs.map (· - n)).toFinset
        apply List.mem_toFinset.mpr
        exact List.mem_map.mpr ⟨n+j, gateAtEq C hi ▸ reader, by omega⟩
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,iIn,member⟩)
  have count (i : ℕ) (iIn : i ∈ Q) : (inputs i).card ≤ 2 := by
    have hi := ((qMem i).mp iIn).1
    have len := legal.2.2 _ (List.getElem_mem hi)
    have bound := List.toFinset_card_le ((gateAt C i).inputs.map (· - n))
    simpa only [inputs,List.length_map,gateAtEq C hi,len] using bound
  have sum : (Q.biUnion inputs).card ≤ 2*Q.card := by
    calc
      (Q.biUnion inputs).card ≤ ∑ i ∈ Q, (inputs i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ Q, 2 := Finset.sum_le_sum count
      _ = 2*Q.card := by simp [Nat.mul_comm]
  have size : F.card + Q.card ≤ 1 + 2*Q.card := by
    rw [← Finset.card_union_of_disjoint unionsDisjoint]
    exact (Finset.card_le_card cover).trans
      ((Finset.card_union_le _ _).trans (by simp only [Finset.card_singleton]; omega))
  have setEq : {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = .or ∧
      OrReaches n C C.output i} = (Q : Set ℕ) := by
    ext i
    exact (qMem i).symm
  rw [setEq,Set.ncard_coe_finset]
  omega
