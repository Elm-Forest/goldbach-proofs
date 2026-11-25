import Mathlib

theorem PEqualNP.Outside.L_lib_121 :
    ∀ (f : List Bool → Bool) (b : ℕ) (x : List Bool),
      b ≤ x.length → f x = true →
      ∃ s : List Bool,
        (List.replicate b [false, true]).sections.find?
            (fun s => f (x.take (x.length - b) ++ s)) = some s ∧
        s.length = b ∧
        f (x.take (x.length - b) ++ s) = true := by
  intro f b x hb hx
  have allSections : ∀ ys : List Bool,
      List.Forall₂ (fun a choices => a ∈ choices)
        ys (List.replicate ys.length [false, true]) := by
    intro ys
    induction ys with
    | nil =>
        exact List.Forall₂.nil
    | cons a ys ih =>
        rw [List.length_cons, List.replicate_succ]
        apply List.Forall₂.cons
        · cases a <;> simp
        · exact ih

  let suffix := x.drop (x.length - b)
  let p : List Bool → Bool := fun s => f (x.take (x.length - b) ++ s)
  let candidates := (List.replicate b [false, true]).sections
  have hlen : suffix.length = b := by
    dsimp only [suffix]
    rw [List.length_drop]
    omega
  have hmem : suffix ∈ candidates := by
    change suffix ∈ (List.replicate b [false, true]).sections
    apply List.mem_sections.mpr
    simpa only [hlen] using allSections suffix
  have hp : p suffix = true := by
    change f (x.take (x.length - b) ++ x.drop (x.length - b)) = true
    rw [List.take_append_drop]
    exact hx

  change ∃ s : List Bool, candidates.find? p = some s ∧
    s.length = b ∧ p s = true
  cases hfind : candidates.find? p with
  | none =>
      exact ((List.find?_eq_none.mp hfind) suffix hmem hp).elim
  | some s =>
      have hs : s ∈ candidates := List.mem_of_find?_eq_some hfind
      have hslen : s.length = b := by
        change s ∈ (List.replicate b [false, true]).sections at hs
        simpa only [List.length_replicate] using List.mem_sections_length hs
      exact ⟨s, rfl, hslen, List.find?_some hfind⟩
