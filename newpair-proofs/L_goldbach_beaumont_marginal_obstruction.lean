import Mathlib

/-! A finite cyclic additive group has two bijections from its
underlying standard indexing set with no common value at a point:
a rotation by 1 of the standard equivalence. -/

theorem PEqualNP.Outside.L_goldbach_beaumont_marginal_obstruction :
    ∀ m : ℕ, 2 ≤ m →
      ∃ a b : Fin m → ZMod m,
        Function.Bijective a ∧ Function.Bijective b ∧ ∀ t, a t ≠ b t := by
  intro m hm
  letI : NeZero m := ⟨by omega⟩
  let f : Fin m → ZMod m := (ZMod.finEquiv m)
  have hf : Function.Bijective f := (ZMod.finEquiv m).bijective
  have hone : (1 : ZMod m) ≠ 0 := by
    intro h
    have hm1 : m ≠ 1 := by omega
    have hv := congrArg ZMod.val h
    simp [ZMod.val_one'' hm1] at hv
  refine ⟨f, (fun t => f t + 1), hf, ?_, ?_⟩
  · constructor
    · intro x y hxy
      apply hf.1
      exact add_right_cancel hxy
    · intro z
      obtain ⟨t, ht⟩ := hf.2 (z - 1)
      refine ⟨t, ?_⟩
      change f t + 1 = z
      rw [ht]
      simp
  · intro t h
    have heq : f t + 1 = f t + (0 : ZMod m) := by
      simpa only [add_zero] using h.symm
    exact hone (add_left_cancel heq)
