import Mathlib

open scoped BigOperators

private theorem reflection_grid_balance :
    ∀ (n m : ℕ) (b : ℕ → Fin m → ℝ), ∃ s : ℕ → ℝ,
      (∀ k, s k = 1 ∨ s k = -1) ∧
      (∑ j, (∑ k ∈ Finset.range n, s k * b k j)^2) ≤
      ∑ j, ∑ k ∈ Finset.range n, (b k j)^2 := by
  intro n m b
  induction n with
  | zero =>
    refine ⟨fun _ => 1, fun _ => Or.inl rfl, ?_⟩
    simp
  | succ n ih =>
    obtain ⟨s, hs, hb⟩ := ih
    let A : Fin m → ℝ := fun j => ∑ k ∈ Finset.range n, s k * b k j
    let E : ℝ → ℝ := fun z => ∑ j, (A j + z * b n j)^2
    have hpair : E 1 + E (-1) =
        2 * ((∑ j, (A j)^2) + ∑ j, (b n j)^2) := by
      unfold E
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    let z : ℝ := if E 1 ≤ E (-1) then 1 else -1
    have hz : z = 1 ∨ z = -1 := by
      unfold z
      split_ifs <;> simp
    have he : E z ≤ (∑ j, (A j)^2) + ∑ j, (b n j)^2 := by
      unfold z
      split_ifs with h
      · linarith
      · have h' := le_of_lt (lt_of_not_ge h)
        linarith
    refine ⟨fun k => if k = n then z else s k, ?_, ?_⟩
    · intro k
      change (if k = n then z else s k) = 1 ∨ (if k = n then z else s k) = -1
      by_cases hk : k = n
      · simpa [hk] using hz
      · simpa [hk] using hs k
    · have hinner (j : Fin m) :
          (∑ k ∈ Finset.range (n+1), (if k = n then z else s k) * b k j) =
          A j + z * b n j := by
        rw [Finset.sum_range_succ]
        have hsum : (∑ k ∈ Finset.range n, (if k = n then z else s k) * b k j) =
            A j := by
          unfold A
          apply Finset.sum_congr rfl
          intro k hk
          simp [Nat.ne_of_lt (Finset.mem_range.mp hk)]
        rw [hsum]
        simp
      calc
        _ = E z := by
          unfold E
          simp only [hinner]
        _ ≤ (∑ j, (A j)^2) + ∑ j, (b n j)^2 := he
        _ ≤ ∑ j, ∑ k ∈ Finset.range (n+1), (b k j)^2 := by
          simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
          exact add_le_add hb (le_refl (∑ j, (b n j)^2))


private theorem reflection_sum_split (n : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range (2*n+1), f k) =
      (∑ k ∈ Finset.range n, (f k + f (2*n-k))) + f n := by
  have hr : (∑ k ∈ Finset.range n, f (n+1+k)) =
      ∑ k ∈ Finset.range n, f (2*n-k) := by
    refine Finset.sum_bij (fun k _ => n-1-k) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_range] at hk ⊢
      omega
    · intro k hk l hl he
      simp only [Finset.mem_range] at hk hl
      omega
    · intro k hk
      have h := Finset.mem_range.mp hk
      refine ⟨n-1-k, Finset.mem_range.mpr (by omega), ?_⟩
      omega
    · intro k hk
      have h := Finset.mem_range.mp hk
      congr 1
      omega
  rw [show 2*n+1 = (n+1)+n by omega, Finset.sum_range_add,
    Finset.sum_range_succ, hr, Finset.sum_add_distrib]
  ring

theorem PEqualNP.Outside.L_goldbach_reflection_grid_thinning :
    ∀ (n m : ℕ) (w : ℕ → ℝ) (a : ℕ → Fin m → ℝ),
      (∀ k, 0 ≤ w k) → ∃ v : ℕ → ℝ,
      (∀ k, 0 ≤ v k ∧ v k ≤ 2*w k) ∧
      (∀ k ≤ 2*n, v k * v (2*n-k) = 0) ∧
      v n = 0 ∧
      (∑ j, ((∑ k ∈ Finset.range (2*n+1), (v k-w k)*a k j) + w n*a n j)^2) ≤
        ∑ j, ∑ k ∈ Finset.range n, (w k*a k j-w (2*n-k)*a (2*n-k) j)^2 := by
  intro n m w a hw
  let b : ℕ → Fin m → ℝ := fun k j => w k*a k j-w (2*n-k)*a (2*n-k) j
  obtain ⟨s, hs, hb⟩ := reflection_grid_balance n m b
  let v : ℕ → ℝ := fun k =>
    if k<n then (1+s k)*w k
    else if k=n then 0 else (1-s (2*n-k))*w k
  have hv (k : ℕ) : 0 ≤ v k ∧ v k ≤ 2*w k := by
    have h := hw k
    by_cases hk : k<n
    · rcases hs k with h1 | h1 <;> simp [v, hk, h1] <;>
        (first | nlinarith | constructor <;> nlinarith)
    · by_cases he : k=n
      · simp [v, he, hw n]
      · rcases hs (2*n-k) with h1 | h1 <;> simp [v, hk, he, h1] <;>
          (first | nlinarith | constructor <;> nlinarith)
  have hc : v n = 0 := by simp [v]
  have hz (k : ℕ) (hk : k ≤ 2*n) : v k * v (2*n-k) = 0 := by
    by_cases hl : k<n
    · have hr : ¬ 2*n-k<n := by omega
      have he : 2*n-k ≠ n := by omega
      have hi : 2*n-(2*n-k)=k := by omega
      rcases hs k with h1 | h1 <;> simp [v, hl, hr, he, hi, h1] <;> ring
    · by_cases he : k=n
      · simp [he, hc]
      · have hr : 2*n-k<n := by omega
        rcases hs (2*n-k) with h1 | h1 <;> simp [v, hl, he, hr, h1] <;> ring
  have hpair (k : ℕ) (hk : k ∈ Finset.range n) (j : Fin m) :
      (v k-w k)*a k j+(v (2*n-k)-w (2*n-k))*a (2*n-k) j =
        s k*b k j := by
    have hl := Finset.mem_range.mp hk
    have hr : ¬ 2*n-k<n := by omega
    have he : 2*n-k ≠ n := by omega
    have hi : 2*n-(2*n-k)=k := by omega
    simp [v, b, hl, hr, he, hi] <;> ring
  have hgrid (j : Fin m) :
      (∑ k ∈ Finset.range (2*n+1), (v k-w k)*a k j) + w n*a n j =
      ∑ k ∈ Finset.range n, s k*b k j := by
    rw [reflection_sum_split n (fun k => (v k-w k)*a k j), hc]
    have hp : (∑ k ∈ Finset.range n,
          ((v k-w k)*a k j+(v (2*n-k)-w (2*n-k))*a (2*n-k) j)) =
        ∑ k ∈ Finset.range n, s k*b k j :=
      Finset.sum_congr rfl (fun k hk => hpair k hk j)
    rw [hp]
    ring
  refine ⟨v, hv, hz, hc, ?_⟩
  simp only [hgrid]
  exact hb
