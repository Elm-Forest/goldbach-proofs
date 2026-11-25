import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_1272 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7)) x := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 15]⟩
  ], 18⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
