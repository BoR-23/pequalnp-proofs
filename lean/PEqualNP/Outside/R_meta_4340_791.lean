import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4340_791
  (erase : let raw (C : PEqualNP.CircuitLowerBounds.Circuit) :=
      ∀ g ∈ C.gates, (∀ i ∈ g.inputs, i < 9) →
        g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and ∧
        g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not
    let red (p : Fin 9 × Fin 9) (g : PEqualNP.CircuitLowerBounds.Gate) :=
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      (∀ i ∈ g.inputs, i = p.1.val ∨ i = p.2.val ∨ i = 9) ∧
      (9 ∈ g.inputs ∨ p.1.val ∈ g.inputs ∧ p.2.val ∈ g.inputs)
    let input (p : Fin 9 × Fin 9) (x : Fin 9 → Bool) :=
      List.ofFn x ++ [x p.1 || x p.2]
    let gate := PEqualNP.MetaComplexity.NestedCover.gateAt
    ∀ (p : Fin 9 × Fin 9) (C : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ),
      PEqualNP.MetaComplexity.FanInTwo C → raw C → j < C.gates.length → red p (gate C j) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧
        raw D ∧ D.size < C.size ∧ ∀ x, D.eval (input p x) = C.eval (input p x))
  (normalized : let raw (C : PEqualNP.CircuitLowerBounds.Circuit) :=
      ∀ g ∈ C.gates, (∀ i ∈ g.inputs, i < 9) →
        g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and ∧
        g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not
    let red (p : Fin 9 × Fin 9) (g : PEqualNP.CircuitLowerBounds.Gate) :=
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      (∀ i ∈ g.inputs, i = p.1.val ∨ i = p.2.val ∨ i = 9) ∧
      (9 ∈ g.inputs ∨ p.1.val ∈ g.inputs ∧ p.2.val ∈ g.inputs)
    let input (p : Fin 9 × Fin 9) (x : Fin 9 → Bool) :=
      List.ofFn x ++ [x p.1 || x p.2]
    let gate := PEqualNP.MetaComplexity.NestedCover.gateAt
    let hit (x : Fin 9 → Bool) :=
      ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    ∀ p ∈ ([(0, 1), (0, 2), (0, 3), (0, 4), (0, 6), (4, 6)] : List (Fin 9 × Fin 9)),
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
        C.size ≤ 14 → raw C → (∀ j < C.gates.length, ¬red p (gate C j)) →
        ∃ x, C.eval (input p x) ≠ hit x) :
  ∀ x1 ∈ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (14 : ℕ) → (∀ x6 ∈ x3.gates, (∀ x8 ∈ x6.inputs, x8 < (9 : ℕ)) → x6.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and ∧ x6.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ (x7 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x7 ++ [x7 x1.1 || x7 x1.2]) ≠ (fun (x8 : Fin (9 : ℕ) → Bool) => x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) x7 := by
  classical
  intro p hp C fan limited rawH
  let raw (C : PEqualNP.CircuitLowerBounds.Circuit) :=
    ∀ g ∈ C.gates, (∀ i ∈ g.inputs, i < 9) →
      g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and ∧
      g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not
  let red (p : Fin 9 × Fin 9) (g : PEqualNP.CircuitLowerBounds.Gate) :=
    g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
    (∀ i ∈ g.inputs, i = p.1.val ∨ i = p.2.val ∨ i = 9) ∧
    (9 ∈ g.inputs ∨ p.1.val ∈ g.inputs ∧ p.2.val ∈ g.inputs)
  let input (p : Fin 9 × Fin 9) (x : Fin 9 → Bool) :=
    List.ofFn x ++ [x p.1 || x p.2]
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt
  let F (x : Fin 9 → Bool) :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
  change ∃ x, C.eval (input p x) ≠ F x
  have descend : ∀ s (D : PEqualNP.CircuitLowerBounds.Circuit), D.size = s →
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 14 → raw D →
      ∃ x, D.eval (input p x) ≠ F x := by
    intro s
    induction s using Nat.strong_induction_on with
    | ind s ih =>
      intro D eq hfan budget hraw
      by_cases has : ∃ j < D.gates.length, red p (gate D j)
      · obtain ⟨j, hj, hr⟩ := has
        obtain ⟨E, efan, eraw, smaller, agrees⟩ := erase p D j hfan hraw hj hr
        have ds : E.size < s := eq ▸ smaller
        obtain ⟨x, hx⟩ := ih E.size ds E rfl efan (by omega) eraw
        rw [agrees x] at hx
        exact ⟨x, hx⟩
      · have hnorm : ∀ j < D.gates.length, ¬red p (gate D j) := fun j hj hr => has ⟨j, hj, hr⟩
        obtain ⟨x, hx⟩ := normalized p hp D hfan budget hraw hnorm
        refine ⟨x, ?_⟩
        simp only [F, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] at hx ⊢
        exact hx
  exact descend C.size C rfl fan limited rawH
