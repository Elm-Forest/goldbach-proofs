import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.R_meta_2346_1
    (transfer :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : Fin 14),
        a ≠ b → PEqualNP.TopForm.IsAO2 14 C →
        ∀ v : ℕ → Bool,
          let W := C.wires (List.ofFn fun i : Fin 14 => decide (i = a))
          (∀ i < 14, v i = decide (i = b.val)) →
          (∀ j < C.size,
            let g := PEqualNP.MetaComplexity.NestedCover.gateAt C j
            let u := PEqualNP.TopForm.opnd C j 0
            let w := PEqualNP.TopForm.opnd C j 1
            (g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
              v (14 + j) = ((W.getD u false && v w) || (v u && W.getD w false))) ∧
            (g.op = PEqualNP.CircuitLowerBounds.GateOp.or →
              v (14 + j) = (v u || v w))) →
          v C.output = false →
          PEqualNP.ReadK.lineSingle C 14 (fun i => decide (i = b.val))
            a.val b.val = false)
    (finite :
      let bad : List ℕ :=
        [127, 244, 361, 480, 595, 720, 833, 1063, 1188, 1313, 1539,
         2126, 2244, 2376, 2626, 3008, 3078, 4125, 4244, 4361, 4625,
         5125, 5889, 6156, 7300, 8250, 8368, 8488, 8722, 9250, 9632,
         10250, 11778, 12312, 12944, 14600, 16256]
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        C.size ≤ 27 → PEqualNP.TopForm.IsAO2 14 C →
        (∀ j < C.size, PEqualNP.TopForm.opnd C j 0 ≠ PEqualNP.TopForm.opnd C j 1) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C 0).op =
          PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ p l : Fin 7, p = l ∨ p = l + 1 ∨ p = l + 3 →
          C.eval (List.ofFn fun i : Fin 14 =>
            decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)) = true) →
        (∀ m ∈ bad, C.eval (List.ofFn fun i : Fin 14 => m.testBit i.val) = false) →
        PEqualNP.ReadK.lineSingle C 14 (fun i => decide (i = 7)) 0 7 = false →
        PEqualNP.ReadK.lineSingle C 14 (fun i => decide (i = 0)) 7 0 = false →
        False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      x1.size ≤ (27 : ℕ) →
      PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →
      (∀ x4 < x1.size,
        PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠
          PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →
      (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op =
        PEqualNP.CircuitLowerBounds.GateOp.and →
      (∀ (x6 : Fin (14 : ℕ) → Bool),
        x1.eval (List.ofFn x6) = Bool.true ↔
          ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)),
            (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨
              x7 = x8 + (3 : Fin (7 : ℕ))) ∧
            x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧
            x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →
      (∀ (x7 : Bool), ∃ (x8 : ℕ → Bool),
        have x9 : List Bool :=
          x1.wires (List.ofFn fun (x9 : Fin (14 : ℕ)) =>
            Decidable.decide
              (x9 = if x7 = Bool.true then (0 : Fin (14 : ℕ)) else (7 : Fin (14 : ℕ))))
        (∀ x10 < (14 : ℕ),
          x8 x10 = Decidable.decide (x10 = if x7 = Bool.true then (7 : ℕ) else (0 : ℕ))) ∧
        (∀ x10 < x1.size,
          have x12 : PEqualNP.CircuitLowerBounds.Gate :=
            PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10
          have x13 : ℕ := PEqualNP.TopForm.opnd x1 x10 (0 : Fin (2 : ℕ))
          have x14 : ℕ := PEqualNP.TopForm.opnd x1 x10 (1 : Fin (2 : ℕ))
          (x12.op = PEqualNP.CircuitLowerBounds.GateOp.and →
            x8 ((14 : ℕ) + x10) =
              (x9.getD x13 Bool.false && x8 x14 || x8 x13 && x9.getD x14 Bool.false)) ∧
          (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or →
            x8 ((14 : ℕ) + x10) = (x8 x13 || x8 x14))) ∧
        x8 x1.output = Bool.false) →
      False := by
  intro C hsize hao hdist hfirst hcorrect hread
  let bad : List ℕ :=
    [127, 244, 361, 480, 595, 720, 833, 1063, 1188, 1313, 1539,
     2126, 2244, 2376, 2626, 3008, 3078, 4125, 4244, 4361, 4625,
     5125, 5889, 6156, 7300, 8250, 8368, 8488, 8722, 9250, 9632,
     10250, 11778, 12312, 12944, 14600, 16256]
  have htable : bad.all (fun m => decide (¬ ∃ p l : Fin 7,
      (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
      m.testBit (Fin.castAdd 7 p).val = true ∧
      m.testBit (Fin.natAdd 7 l).val = true)) = true := by
    decide +kernel
  refine finite C hsize hao hdist hfirst ?_ ?_ ?_ ?_
  · intro p l hi
    apply (hcorrect _).mpr
    exact ⟨p, l, hi, by simp, by simp⟩
  · change ∀ m ∈ bad, C.eval (List.ofFn fun i : Fin 14 => m.testBit i.val) = false
    intro m hm
    have hno := of_decide_eq_true (List.all_eq_true.mp htable m hm)
    cases he : C.eval (List.ofFn fun i : Fin 14 => m.testBit i.val) with
    | false => rfl
    | true => exact False.elim (hno ((hcorrect _).mp he))
  · obtain ⟨v, hv⟩ := hread true
    exact transfer C 0 7 (by decide) hao v hv.1 hv.2.1 hv.2.2
  · obtain ⟨v, hv⟩ := hread false
    exact transfer C 7 0 (by decide) hao v hv.1 hv.2.1 hv.2.2
