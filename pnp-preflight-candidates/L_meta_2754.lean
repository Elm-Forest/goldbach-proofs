import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_meta_2754 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.not → x1.gates[(2 : ℕ)]? = Option.none → (16 : ℕ) ≤ x1.size := by
  intro C _ hfirst hfun hnot hnone
  exfalso
  rcases C with ⟨gs, o⟩
  cases gs with
  | nil => simp at hnot
  | cons g gs =>
    cases gs with
    | nil => simp at hnot
    | cons h gs =>
      cases gs with
      | cons k rest => simp at hnone
      | nil =>
        let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨[g, h], o⟩
        have hop : h.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
          simpa using hnot
        have hW (x : Fin 9 → Bool) :
            D.wires (List.ofFn x) =
              (List.ofFn x ++ [x 0 || x 4]) ++
                [PEqualNP.CircuitLowerBounds.GateOp.not.eval
                  (h.inputs.map fun i => (List.ofFn x ++ [x 0 || x 4]).getD i false)] := by
          have hg := hfirst x
          change g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) =
            (x 0 || x 4) at hg
          change (List.ofFn x ++ [g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)]) ++
              [h.op.eval (h.inputs.map fun i => (List.ofFn x ++
                [g.op.eval (g.inputs.map fun j => (List.ofFn x).getD j false)]).getD i false)] = _
          rw [hg, hop]
        by_cases ho : o < 9
        · let x : Fin 9 → Bool := fun i => decide (i.val = o)
          have he := congrFun hfun x
          change (D.wires (List.ofFn x)).getD o false = _ at he
          have hval : (D.wires (List.ofFn x)).getD o false = true := by
            rw [hW, List.getD_eq_getElem?_getD,
              List.getElem?_append_left (by simp; omega),
              List.getElem?_append_left (by simpa using ho)]
            simp [ho, x]
            interval_cases o <;> decide
          have hrow : (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 ||
              x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 ||
              x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
              x 6 && x 8 || x 8 && x 5) = false := by
            dsimp [x]
            interval_cases o <;> decide
          rw [hval, hrow] at he
          contradiction
        · by_cases ho9 : o = 9
          · let x : Fin 9 → Bool := fun i => decide (i = 0)
            have he := congrFun hfun x
            change (D.wires (List.ofFn x)).getD o false = false at he
            rw [ho9, hW] at he
            exact Bool.noConfusion he
          · by_cases ho10 : o = 10
            · let x : Fin 9 → Bool := fun _ => false
              have hz (i : ℕ) : (List.ofFn x ++ [false]).getD i false = false := by
                by_cases hi : i < 10
                · interval_cases i <;> rfl
                · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
                  rfl
              have he := congrFun hfun x
              change (D.wires (List.ofFn x)).getD o false = false at he
              rw [ho10, hW] at he
              change PEqualNP.CircuitLowerBounds.GateOp.not.eval
                (h.inputs.map fun i => (List.ofFn x ++ [false]).getD i false) = false at he
              cases hh : h.inputs with
              | nil => simp [hh, PEqualNP.CircuitLowerBounds.GateOp.eval] at he
              | cons i is =>
                simp only [hh] at he
                change (!((List.ofFn x ++ [false]).getD i false)) = false at he
                rw [hz i] at he
                contradiction
            · let x : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1)
              have he := congrFun hfun x
              change (D.wires (List.ofFn x)).getD o false = true at he
              rw [hW, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at he
              contradiction
