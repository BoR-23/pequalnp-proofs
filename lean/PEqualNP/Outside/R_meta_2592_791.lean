import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

theorem PEqualNP.Outside.R_meta_2592_791
    (normalize : ∀ C : Circuit, FanInTwo C → (∃ g ∈ C.gates, g.op = .not) →
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧ ReadsBack 10 D ∧
        (∀ g ∈ D.gates, g.inputs.Nodup ∧ (g.op = .not → g.inputs.length ≤ 1)) ∧
        (∃ g ∈ D.gates, g.op = .not) ∧ circuitFun 10 D = circuitFun 10 C)
    (earlierOnly : ∀ D : Circuit, FanInTwo D → D.size ≤ 19 → ReadsBack 10 D →
      (∀ g ∈ D.gates, g.inputs.Nodup ∧ (g.op = .not → g.inputs.length ≤ 1)) →
      (∃ g ∈ D.gates, g.op = .not) →
      ¬ ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) =
        ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (ℕ × ℕ)).any
          (fun e => x (Fin.ofNat 10 e.1) && x (Fin.ofNat 10 e.2))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (19 : ℕ) → (∃ x4 ∈ x1.gates, x4.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ¬∀ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5) = (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  intro C fan upper hasNot correct
  have result := normalize C fan hasNot
  obtain ⟨D, legal, size, earlier, nodup, notOp, sound⟩ := result
  apply earlierOnly D legal (size.symm ▸ upper) earlier nodup notOp
  intro x
  have exactValue := congrFun sound x
  change D.eval (List.ofFn x) = C.eval (List.ofFn x) at exactValue
  rw [exactValue, correct x]
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
  rfl
