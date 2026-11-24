import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4332_791
    (normalize :
      let E : Finset (Sym2 (Fin 9)) := {s(0,1), s(1,2), s(2,3), s(3,4), s(4,0), s(0,5), s(1,6), s(2,7),
         s(3,8), s(5,7), s(6,8), s(8,5)}
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (i : ℕ) (b : Bool),
        PEqualNP.MetaComplexity.FanInTwo C →
        (∀ z : Fin 10 → Bool, z 9 = false →
          (if b = true then !(C.wires (List.ofFn z)).getD i false
           else (C.wires (List.ofFn z)).getD i false) =
          (z 0 && z 1 || z 1 && z 2 || z 2 && z 3 || z 3 && z 4 || z 4 && z 0 ||
           z 0 && z 5 || z 1 && z 6 || z 2 && z 7 || z 3 && z 8 ||
           z 5 && z 7 || z 6 && z 8 || z 8 && z 5)) →
        ∃ (S : List (Finset (Fin 9))) (T : List (Fin 9 × Finset (Fin 9))),
        (∀ (P : List (Finset (Fin 9))) (U : Finset (Fin 9)) (Q : List (Finset (Fin 9))),
          S = P ++ U :: Q → ∃ A B : Finset (Fin 9),
            U = A ∪ B ∧ (A.card ≤ 1 ∨ A ∈ Q) ∧ (B.card ≤ 1 ∨ B ∈ Q)) ∧
        (∀ t ∈ T, (t.2.card ≤ 1 ∨ t.2 ∈ S) ∧ ∀ b ∈ t.2, s(t.1,b) ∈ E) ∧
        (∀ a b : Fin 9, s(a,b) ∈ E → ∃ t ∈ T,
          (t.1 = a ∧ b ∈ t.2) ∨ (t.1 = b ∧ a ∈ t.2)) ∧
        S.length + 2 * T.length ≤ C.size + 1)
    (count :
      let E : Finset (Sym2 (Fin 9)) := {s(0,1), s(1,2), s(2,3), s(3,4), s(4,0), s(0,5), s(1,6), s(2,7),
         s(3,8), s(5,7), s(6,8), s(8,5)}
      ∀ (S : List (Finset (Fin 9))) (T : List (Fin 9 × Finset (Fin 9))),
        (∀ (P : List (Finset (Fin 9))) (U : Finset (Fin 9)) (Q : List (Finset (Fin 9))),
          S = P ++ U :: Q → ∃ A B : Finset (Fin 9),
            U = A ∪ B ∧ (A.card ≤ 1 ∨ A ∈ Q) ∧ (B.card ≤ 1 ∨ B ∈ Q)) →
        (∀ t ∈ T, (t.2.card ≤ 1 ∨ t.2 ∈ S) ∧ ∀ b ∈ t.2, s(t.1,b) ∈ E) →
        (∀ a b : Fin 9, s(a,b) ∈ E → ∃ t ∈ T,
          (t.1 = a ∧ b ∈ t.2) ∨ (t.1 = b ∧ a ∈ t.2)) →
        17 ≤ S.length + 2 * T.length) :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Bool),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (15 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → Bool := fun (x7 : Fin (10 : ℕ) → Bool) => (x2.wires (List.ofFn x7)).getD x3 Bool.false;       ∃ (x8 : Fin (10 : ℕ) → Bool), x8 (9 : Fin (10 : ℕ)) = Bool.false ∧ (if x4 = Bool.true then !x7 x8 else x7 x8) ≠ x1 x8 := by
  intro f C i b fan size
  dsimp only
  by_contra notWitness
  push Not at notWitness
  obtain ⟨S, T, gates, stars, edges, budget⟩ := normalize C i b fan (by
    intro z hz
    simpa [f, hz] using notWitness z hz)
  have lower := count S T gates stars edges
  omega
