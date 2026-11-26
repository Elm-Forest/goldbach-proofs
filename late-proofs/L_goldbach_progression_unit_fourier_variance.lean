import Mathlib

/- Parseval lemmas adapted from gggreatboy, PR 232, commit e1935db9ce088807f49ad762bc62b8396c4ecd1c (Apache-2.0). -/

open Complex Finset
open scoped ComplexConjugate BigOperators

/-- The character `x ↦ exp (2π i x)`. -/
private noncomputable def gE (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- The Fourier kernel `exp (2π i j k / M)`. -/
private noncomputable def gC (M j k : ℕ) : ℂ := gE ((j : ℝ) * (k : ℝ) / (M : ℝ))

/-- The discrete Fourier transform of `f` at frequency `j`. -/
private noncomputable def gF (M : ℕ) (f : ℕ → ℂ) (j : ℕ) : ℂ := ∑ k ∈ range M, f k * gC M j k

private lemma gE_add (x y : ℝ) : gE (x + y) = gE x * gE y := by
  unfold gE
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma gE_zero : gE 0 = 1 := by
  unfold gE
  simp

private lemma gE_neg (x : ℝ) : conj (gE x) = gE (-x) := by
  unfold gE
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private lemma gE_nat (n : ℕ) : gE (n : ℝ) = 1 := by
  unfold gE
  rw [Complex.exp_eq_one_iff]
  exact ⟨(n : ℤ), by push_cast; ring⟩

private lemma gE_nat_mul (x : ℝ) (j : ℕ) : gE ((j : ℝ) * x) = gE x ^ j := by
  unfold gE
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private lemma gE_pow (M : ℕ) (hM : 0 < M) (n : ℕ) : gE ((n : ℝ) / (M : ℝ)) ^ M = 1 := by
  rw [← gE_nat_mul]
  have hM' : (M : ℝ) ≠ 0 := by positivity
  have h : (M : ℝ) * ((n : ℝ) / (M : ℝ)) = (n : ℝ) := by field_simp
  rw [h, gE_nat]

private lemma gE_ne_one (M : ℕ) (hM : 0 < M) {n : ℕ} (hn0 : 0 < n) (hnM : n < M) :
    gE ((n : ℝ) / (M : ℝ)) ≠ 1 := by
  intro h
  have hre : Real.cos (2 * Real.pi * ((n : ℝ) / (M : ℝ))) = 1 := by
    have h' := congrArg Complex.re h
    simp only [gE] at h'
    rwa [Complex.exp_ofReal_mul_I_re] at h'
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hnlt : (n : ℝ) < (M : ℝ) := by exact_mod_cast hnM
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have h1 : -(2 * Real.pi) < 2 * Real.pi * ((n : ℝ) / (M : ℝ)) := by
    have hdiv : (-1 : ℝ) < (n : ℝ) / (M : ℝ) := by
      rw [lt_div_iff₀ hMpos]
      linarith
    nlinarith [Real.pi_pos]
  have h2 : 2 * Real.pi * ((n : ℝ) / (M : ℝ)) < 2 * Real.pi := by
    have hdiv : (n : ℝ) / (M : ℝ) < 1 := by
      rw [div_lt_one hMpos]
      linarith
    nlinarith [Real.pi_pos]
  have hz : 2 * Real.pi * ((n : ℝ) / (M : ℝ)) = 0 :=
    (Real.cos_eq_one_iff_of_lt_of_lt h1 h2).mp hre
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hdiv0 : (n : ℝ) / (M : ℝ) = 0 := (mul_eq_zero.mp hz).resolve_left hpi
  have hn0' : (n : ℝ) = 0 := by
    rw [div_eq_zero_iff] at hdiv0
    rcases hdiv0 with h' | h'
    · exact h'
    · exact absurd h' hMpos.ne'
  exact hnpos.ne' hn0'

/-- For `0 < n < M` the sum of `exp (2π i j n / M)` over `j < M` vanishes. -/
private lemma sum_gE_zero (M : ℕ) (hM : 0 < M) {n : ℕ} (hn0 : 0 < n) (hnM : n < M) :
    (∑ j ∈ range M, gE ((j : ℝ) * ((n : ℝ) / (M : ℝ)))) = 0 := by
  have hterm : ∀ j : ℕ, gE ((j : ℝ) * ((n : ℝ) / (M : ℝ)))
      = gE ((n : ℝ) / (M : ℝ)) ^ j := fun j => gE_nat_mul _ j
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  have hpow : gE ((n : ℝ) / (M : ℝ)) ^ M = 1 := gE_pow M hM n
  have hne : gE ((n : ℝ) / (M : ℝ)) - 1 ≠ 0 :=
    sub_ne_zero.mpr (gE_ne_one M hM hn0 hnM)
  have h := mul_geom_sum (gE ((n : ℝ) / (M : ℝ))) M
  rw [hpow, sub_self] at h
  exact (mul_eq_zero.mp h).resolve_left hne

/-- Orthogonality of the kernel when `l < k`. -/
private lemma inner_sq_pos (M : ℕ) (hM : 0 < M) {k l : ℕ} (hlk : l < k) (hk : k < M) :
    (∑ j ∈ range M, gC M j k * conj (gC M j l)) = 0 := by
  have hn0 : 0 < k - l := Nat.sub_pos_of_lt hlk
  have hnM : k - l < M := by omega
  have hterm : ∀ j : ℕ, gC M j k * conj (gC M j l)
      = gE ((j : ℝ) * (((k - l : ℕ) : ℝ) / (M : ℝ))) := by
    intro j
    have hxj : conj (gC M j l) = gE (-((j : ℝ) * (l : ℝ) / (M : ℝ))) := by
      simp only [gC]
      exact gE_neg _
    rw [hxj, gC, ← gE_add]
    congr 1
    have hM' : (M : ℝ) ≠ 0 := by positivity
    have hkl : ((k - l : ℕ) : ℝ) = (k : ℝ) - (l : ℝ) := by
      rw [Nat.cast_sub hlk.le]
    rw [hkl]
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  exact sum_gE_zero M hM hn0 hnM

/-- Orthogonality of the kernel: the inner product of two columns is `M` on the diagonal. -/
private lemma inner_sq (M : ℕ) (hM : 0 < M) (k l : ℕ) (hk : k < M) (hl : l < M) :
    (∑ j ∈ range M, gC M j k * conj (gC M j l)) = if k = l then (M : ℂ) else 0 := by
  by_cases hkl : k = l
  · subst hkl
    rw [if_pos rfl]
    have hterm : ∀ j : ℕ, gC M j k * conj (gC M j k) = 1 := by
      intro j
      have hx : conj (gC M j k) = gE (-((j : ℝ) * (k : ℝ) / (M : ℝ))) := by
        simp only [gC]
        exact gE_neg _
      rw [hx, gC, ← gE_add]
      have hzero : (j : ℝ) * (k : ℝ) / (M : ℝ) + -((j : ℝ) * (k : ℝ) / (M : ℝ)) = 0 := by
        ring
      rw [hzero, gE_zero]
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
    simp
  · rw [if_neg hkl]
    rcases lt_or_gt_of_ne hkl with hlt | hgt
    · have hpos := inner_sq_pos M hM (k := l) (l := k) hlt hl
      calc (∑ j ∈ range M, gC M j k * conj (gC M j l))
          = ∑ j ∈ range M, conj (gC M j l * conj (gC M j k)) := by
            apply Finset.sum_congr rfl
            intro j _
            simp [mul_comm]
        _ = conj (∑ j ∈ range M, gC M j l * conj (gC M j k)) := by
            rw [map_sum]
        _ = 0 := by rw [hpos]; simp
    · exact inner_sq_pos M hM hgt hk

/-- Complex form of Parseval's identity for the discrete frequency kernel. -/
private lemma parseval_complex (M : ℕ) (hM : 0 < M) (f : ℕ → ℂ) :
    (∑ j ∈ range M, gF M f j * conj (gF M f j))
      = (M : ℂ) * ∑ k ∈ range M, f k * conj (f k) := by
  have hstep : ∀ j : ℕ, gF M f j * conj (gF M f j)
      = ∑ k ∈ range M, ∑ l ∈ range M,
          (f k * conj (f l)) * (gC M j k * conj (gC M j l)) := by
    intro j
    simp only [gF]
    rw [map_sum]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    rw [map_mul]
    ring
  calc (∑ j ∈ range M, gF M f j * conj (gF M f j))
      = ∑ j ∈ range M, ∑ k ∈ range M, ∑ l ∈ range M,
          (f k * conj (f l)) * (gC M j k * conj (gC M j l)) :=
        Finset.sum_congr rfl (fun j _ => hstep j)
    _ = ∑ k ∈ range M, ∑ l ∈ range M, ∑ j ∈ range M,
          (f k * conj (f l)) * (gC M j k * conj (gC M j l)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_comm]
    _ = ∑ k ∈ range M, ∑ l ∈ range M,
          (f k * conj (f l)) * (if k = l then (M : ℂ) else 0) := by
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro l hl
        rw [← Finset.mul_sum]
        rw [inner_sq M hM k l (mem_range.mp hk) (mem_range.mp hl)]
    _ = (M : ℂ) * ∑ k ∈ range M, f k * conj (f k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.sum_eq_single k]
        · rw [if_pos rfl, mul_comm]
        · intro l _ hlk
          rw [if_neg (Ne.symm hlk), mul_zero]
        · intro hknot
          exact absurd hk hknot

private lemma parseval_real (M : ℕ) (f : ℕ → ℂ) :
    (∑ j ∈ range M, ‖gF M f j‖ ^ 2) = (M : ℝ) * ∑ k ∈ range M, ‖f k‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos M with hM0 | hM
  · subst hM0
    simp
  apply Complex.ofReal_inj.mp
  push_cast
  have h1 : ∀ j, ((‖gF M f j‖ : ℂ) ^ 2) = gF M f j * conj (gF M f j) := by
    intro j
    rw [← Complex.mul_conj']
  have h2 : ∀ k, ((‖f k‖ : ℂ) ^ 2) = f k * conj (f k) := by
    intro k
    rw [← Complex.mul_conj']
  simp_rw [h1]
  rw [parseval_complex M hM f]
  congr 1
  simp_rw [h2]

theorem PEqualNP.Outside.L_goldbach_progression_unit_fourier_variance :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let Λ := ArithmeticFunction.vonMangoldt; ∀ (q n : ℕ), 0 < q → let D := fun r : ℕ => if Nat.Coprime r q then (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q=r), Λ k) - (n:ℝ)/Nat.totient q else 0; (∑ a ∈ Finset.range q, ‖∑ r ∈ Finset.range q, (D r:ℂ)*E ((a:ℝ)*r/q)‖^2) = (q:ℝ)*(∑ r ∈ Finset.range q, (D r)^2) := by
  dsimp only
  intro q n hq
  let D : ℕ → ℝ := fun r => if Nat.Coprime r q then (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q=r), ArithmeticFunction.vonMangoldt k) - (n:ℝ)/Nat.totient q else 0
  change (∑ a ∈ Finset.range q, ‖∑ r ∈ Finset.range q, (D r:ℂ)*gC q a r‖^2) = (q:ℝ)*(∑ r ∈ Finset.range q, (D r)^2)
  simpa only [gF, Complex.norm_real, Real.norm_eq_abs, sq_abs] using parseval_real q (fun r => (D r:ℂ))
