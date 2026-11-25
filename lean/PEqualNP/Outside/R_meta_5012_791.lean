import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.BlindGate

theorem PEqualNP.Outside.R_meta_5012_791
    (distinct : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsLeastAO G C → ∀ j < C.gates.length, ∀ a < n + j,
        ∃ x : Fin n → Bool, wireValue C n x (n + j) ≠ wireValue C n x a)
    (remaining : (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool),
  (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsLeastAO G C →
  (PEqualNP.TopForm.junk G C).card ≠ 1) →
∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool),
  (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsLeastAO G C →
  (∀ j ∈ PEqualNP.TopForm.junk G C, ∀ a < n + j, ∃ x : Fin n → Bool,
    PEqualNP.BlindGate.wireValue C n x (n + j) ≠ PEqualNP.BlindGate.wireValue C n x a) →
  (PEqualNP.TopForm.junk G C).card ≠ 2) :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool),
  (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsLeastAO G C →
  (PEqualNP.TopForm.junk G C).card ≠ 1) →
∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool),
  (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsLeastAO G C →
  (PEqualNP.TopForm.junk G C).card ≠ 2 := by
  intro rung n G inst C s bip free least
  apply remaining rung n G C s bip free least
  intro j jIn a before
  exact distinct n G C least j (Finset.mem_range.mp (Finset.mem_filter.mp jIn).1) a before
