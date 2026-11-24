import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5080_791
    (findEqualWires :
      let I : Finset (Fin 13) := {0, 1, 3, 9}
      let pair (p l : Fin 13) : List Bool :=
        List.ofFn (fun i : Fin 13 => decide (i = p)) ++ List.ofFn (fun i : Fin 13 => decide (i = l))
      let quad (S : Finset (Fin 13)) : List Bool :=
        List.ofFn (fun i : Fin 13 => decide (i ∈ S)) ++
          List.ofFn (fun l : Fin 13 => decide (∀ p ∈ S, p - l ∉ I))
      let row (b : Bool) (x : List Bool) : Prop :=
        if b then ∃ p l, p - l ∈ I ∧ x = pair p l
        else ∃ S : Finset (Fin 13), S.card = 4 ∧
          (∀ l : Fin 13, (S.filter fun p => p - l ∈ I).card ≤ 2) ∧ x = quad S
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C →
        (∀ b x, row b x → C.eval x = b) → C.size < 64 →
        (∀ g ∈ C.gates, ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b) →
        2 ≤ PEqualNP.TopForm.andPairs 26 C →
        (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
          PEqualNP.CircuitLowerBounds.GateOp.and → 2 ≤ (PEqualNP.TopForm.readers 26 C j).card) →
        ∃ j < C.gates.length, ∃ w < 26 + j,
          ∀ b x, row b x → (C.wires x).getD (26 + j) false = (C.wires x).getD w false)
    (transferRows :
      let I : Finset (Fin 13) := {0, 1, 3, 9}
      let pair (p l : Fin 13) : List Bool :=
        List.ofFn (fun i : Fin 13 => decide (i = p)) ++ List.ofFn (fun i : Fin 13 => decide (i = l))
      let quad (S : Finset (Fin 13)) : List Bool :=
        List.ofFn (fun i : Fin 13 => decide (i ∈ S)) ++
          List.ofFn (fun l : Fin 13 => decide (∀ p ∈ S, p - l ∉ I))
      let row (b : Bool) (x : List Bool) : Prop :=
        if b then ∃ p l, p - l ∈ I ∧ x = pair p l
        else ∃ S : Finset (Fin 13), S.card = 4 ∧
          (∀ l : Fin 13, (S.filter fun p => p - l ∈ I).card ≤ 2) ∧ x = quad S
          ∀ (C D : PEqualNP.CircuitLowerBounds.Circuit) (j w : ℕ),
        (∀ b x, row b x → C.eval x = b) →
        (∀ b x, row b x → (C.wires x).getD (26 + j) false = (C.wires x).getD w false) →
        (∀ x : List Bool, x.length = 26 →
          (C.wires x).getD (26 + j) false = (C.wires x).getD w false → D.eval x = C.eval x) →
        ∀ b x, row b x → D.eval x = b) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → x4.size < (64 : ℕ) → x3 x4 → (∀ x10 ∈ x4.gates, x10.inputs.length = (2 : ℕ) ∧ x10.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x10.inputs.getD (1 : ℕ) (0 : ℕ)) → (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x4 → (∀ x12 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → (2 : ℕ) ≤ (PEqualNP.TopForm.readers (26 : ℕ) x4 x12).card) → ∃ x13 < x4.gates.length, ∃ x14 < (26 : ℕ) + x13, ∀ (x15 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x16 : List Bool), x16.length = (26 : ℕ) → (x4.wires x16).getD ((26 : ℕ) + x13) Bool.false = (x4.wires x16).getD x14 Bool.false → x15.eval x16 = x4.eval x16) → x2 x15 := by
  intro I right nested C mono back correct small _ binary pairs reread
  let pair (p l : Fin 13) : List Bool :=
    List.ofFn (fun i : Fin 13 => decide (i = p)) ++ List.ofFn (fun i : Fin 13 => decide (i = l))
  let quad (S : Finset (Fin 13)) : List Bool :=
    List.ofFn (fun i : Fin 13 => decide (i ∈ S)) ++
      List.ofFn (fun l : Fin 13 => decide (∀ p ∈ S, p - l ∉ I))
  let row (b : Bool) (x : List Bool) : Prop :=
    if b then ∃ p l, p - l ∈ I ∧ x = pair p l
    else ∃ S : Finset (Fin 13), S.card = 4 ∧
      (∀ l : Fin 13, (S.filter fun p => p - l ∈ I).card ≤ 2) ∧ x = quad S
  have asRows : ∀ b x, row b x → C.eval x = b := by
    intro b x hx
    cases b
    · obtain ⟨S, hs, noThree, rfl⟩ := hx
      exact correct.2 S hs noThree
    · obtain ⟨p, l, edge, rfl⟩ := hx
      exact correct.1 p l edge
  have strict (g : PEqualNP.CircuitLowerBounds.Gate) (hg : g ∈ C.gates) :
      ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b := by
    obtain ⟨len, different⟩ := binary g hg
    obtain ⟨a, b, ab⟩ := List.length_eq_two.mp len
    exact ⟨a, b, ab, by simpa only [ab, List.getD_cons_zero, List.getD_cons_succ] using different⟩
  obtain ⟨j, hj, w, hw, heq⟩ := findEqualWires C mono back asRows small strict pairs reread
  refine ⟨j, hj, w, hw, ?_⟩
  intro D preserved
  have checks : ∀ b x, row b x → D.eval x = b :=
    transferRows C D j w asRows heq preserved
  constructor
  · intro p l edge
    exact checks true (pair p l) ⟨p, l, edge, rfl⟩
  · intro S hS hquad
    exact checks false (quad S) ⟨S, hS, hquad, rfl⟩
