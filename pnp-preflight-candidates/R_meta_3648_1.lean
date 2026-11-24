import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3648_1
    (sim :
      ∀ (n : ℕ) (C : PEqualNP.MetaComplexity.BinaryCircuit)
        (s : List (BitVec n)), 0 ∈ s →
        (∀ g ∈ C.gates, ∃ a b : Bool,
          g.op = fun u v => (u == a) && (v == b)) →
        let step := fun (w : List (BitVec n))
            (t : Bool × Bool × BitVec n × BitVec n) =>
          let (a, b, u, v) := t
          let z := (if a then u else ~~~u) &&& (if b then v else ~~~v)
          if u ∈ w ∧ v ∈ w ∧ z ∉ w then z :: w else w
        ∃ ts : List (Bool × Bool × BitVec n × BitVec n),
          ts.length ≤ C.size ∧
          ∃ z ∈ ts.foldl step s, ∀ r : Fin n,
            z.getLsbD r.val = C.eval (s.map fun u => u.getLsbD r.val))
    (search :
      let raw := fun (i : ℕ) =>
        BitVec.ofNat 512 (((2^512-1)/(2^(2^i)+1)) * 2^(2^i))
      let seed := List.ofFn (fun i : Fin 9 => raw i.val) ++
        [raw 0 ||| raw 4, 0]
      let target := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).foldl
        (fun w e => w ||| (raw (e / 10) &&& raw (e % 10))) 0
      let step := fun (w : List (BitVec 512))
          (t : Bool × Bool × BitVec 512 × BitVec 512) =>
        let (a, b, u, v) := t
        let z := (if a then u else ~~~u) &&& (if b then v else ~~~v)
        if u ∈ w ∧ v ∈ w ∧ z ∉ w then z :: w else w
      ∀ ts : List (Bool × Bool × BitVec 512 × BitVec 512),
        ts.length ≤ 13 → target ∉ ts.foldl step seed) :
    ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit), x1.size = (13 : ℕ) →
      x1.output < (24 : ℕ) →
      (∀ (x4 : ℕ) (x5 : PEqualNP.MetaComplexity.BinaryGate),
        x1.gates[x4]? = Option.some x5 →
        x5.left < (11 : ℕ) + x4 ∧ x5.right < (11 : ℕ) + x4 ∧
        ∃ (x7 : Bool) (x8 : Bool),
          x5.op = fun (x9 x10 : Bool) => x9 == x7 && x10 == x8) →
      ∃ (x5 : Fin (9 : ℕ) → Bool),
        (x1.eval (List.ofFn x5 ++
          [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), Bool.false]) != Bool.false) ≠
        (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) ||
         x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) ||
         x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) ||
         x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) ||
         x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) ||
         x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) ||
         x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) ||
         x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) ||
         x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) ||
         x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) ||
         x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) ||
         x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) := by
  intro C hsize _ hgate
  classical
  by_contra h
  let raw := fun (i : ℕ) =>
    BitVec.ofNat 512 (((2^512-1)/(2^(2^i)+1)) * 2^(2^i))
  let seed := List.ofFn (fun i : Fin 9 => raw i.val) ++
    [raw 0 ||| raw 4, 0]
  let target := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).foldl
    (fun w e => w ||| (raw (e / 10) &&& raw (e % 10))) 0
  have hzero : (0 : BitVec 512) ∈ seed := by simp [seed]
  have hops : ∀ g ∈ C.gates, ∃ a b : Bool,
      g.op = fun u v => (u == a) && (v == b) := by
    intro g hg
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hg
    exact (hgate i g hi).2.2
  obtain ⟨ts, hlen, z, hz, hbit⟩ := sim 512 C seed hzero hops
  have hout : z = target := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Fin 512 := ⟨j, hj⟩
    let x : Fin 9 → Bool := fun i => (raw i.val).getLsbD r.val
    change z.getLsbD r.val = target.getLsbD r.val
    have hseed : seed.map (fun u => u.getLsbD r.val) =
        List.ofFn x ++ [x 0 || x 4, false] := by
      simp only [seed, List.map_append, List.map_ofFn, List.map_cons,
        List.map_nil, Function.comp_def, BitVec.getLsbD_or, BitVec.getLsbD_zero]
      rfl
    have hrow :
        (C.eval (List.ofFn x ++ [x 0 || x 4, false]) != false) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
         x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
         x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
      by_contra hn
      exact h ⟨x, hn⟩
    have hbool (b : Bool) : (b != false) = b := by cases b <;> rfl
    rw [hbool] at hrow
    rw [hbit r, hseed, hrow]
    simp only [target, List.foldl_cons, List.foldl_nil, BitVec.getLsbD_or,
      BitVec.getLsbD_and, BitVec.getLsbD_zero, Bool.false_or, Bool.or_assoc]
    rfl
  have hcap : ts.length ≤ 13 := hsize ▸ hlen
  exact (search ts hcap) (hout ▸ hz)
