import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_1251 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6) || (x 6 && x 7)) x := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 14]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩
  ], 17⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, C]
  · decide
  · decide
