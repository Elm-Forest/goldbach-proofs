import Mathlib

-- child 1 zh: 中带（(log₂(n+2))² < q ≤ ⌊n^(1/5)⌋₊，窄窗半径 Q·n^(1/6)/(qn)）上的素数平方积分实部满足无条件单侧下界 ≥ -εn。
-- child 1 en: Middle-band narrow-arc floor: on (log₂(n+2))² < q ≤ ⌊n^(1/5)⌋₊ with narrow radius Q·n^(1/6)/(qn), the real part of the prime square integral is ≥ -εn for all sufficiently large even n.
-- child 2 zh: 高模数窄带（⌊n^(1/5)⌋₊ < q ≤ ⌊n^(1/3)⌋₊，窄窗半径 Q·n^(1/6)/(qn)）上的素数平方积分实部满足无条件单侧下界 ≥ -εn。
-- child 2 en: High-band narrow-arc floor: on ⌊n^(1/5)⌋₊ < q ≤ ⌊n^(1/3)⌋₊ with narrow radius Q·n^(1/6)/(qn), the real part of the prime square integral is ≥ -εn for all sufficiently large even n.

theorem Conjectures.Cuts.Cut474f9fc41d46524c836a3de4
    (hMidBand :
      let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0
      let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
      let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) =>
        Finset.sum (Finset.range (n + 1)) (fun k => (u k : ℂ) * E ((k : ℝ) * t))
      let Q := fun n : ℕ => (Nat.log 2 (n + 2)) ^ 2
      let A := fun n : ℕ => ⌊(n : ℝ) ^ (1 / 5 : ℝ)⌋₊
      let f := fun (n : ℕ) (t : ℝ) => (S n w t) ^ 2 * E (-(n : ℝ) * t)
      let midBand := fun n : ℕ =>
        {t : ℝ | ∃ q a : ℕ, Q n < q ∧ 1 ≤ q ∧ q ≤ A n ∧ a ≤ q ∧ Nat.Coprime a q ∧
          |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ) / ((q : ℝ) * (n : ℝ))}
      ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
        -(e * (n : ℝ)) ≤
          (intervalIntegral (fun t => (midBand n).indicator (f n) t)
            (0 : ℝ) 1 MeasureTheory.volume).re)
    (hHighBand :
      let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0
      let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
      let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) =>
        Finset.sum (Finset.range (n + 1)) (fun k => (u k : ℂ) * E ((k : ℝ) * t))
      let Q := fun n : ℕ => (Nat.log 2 (n + 2)) ^ 2
      let A := fun n : ℕ => ⌊(n : ℝ) ^ (1 / 5 : ℝ)⌋₊
      let Q₁ := fun n : ℕ => ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
      let f := fun (n : ℕ) (t : ℝ) => (S n w t) ^ 2 * E (-(n : ℝ) * t)
      let highBand := fun n : ℕ =>
        {t : ℝ | ∃ q a : ℕ, A n < q ∧ 1 ≤ q ∧ q ≤ Q₁ n ∧ a ≤ q ∧ Nat.Coprime a q ∧
          |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ) / ((q : ℝ) * (n : ℝ))}
      ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
        -(e * (n : ℝ)) ≤
          (intervalIntegral (fun t => (highBand n).indicator (f n) t)
            (0 : ℝ) 1 MeasureTheory.volume).re) :
    (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowPart := fun n : ℕ => lowWideArcs n \ arcs n; let remainder := fun n : ℕ => (wideArcs n \ arcs n) \ lowPart n; let inner := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n : ℝ) * (n : ℝ)^(1/6 : ℝ) / ((q:ℝ)*(n:ℝ))}; let J := fun (n : ℕ) (A : Set ℝ) => (intervalIntegral (fun t => A.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; let floor := fun (A : ℕ → Set ℝ) => ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n:ℝ)) ≤ J n (A n); floor (fun n => remainder n ∩ inner n)) :=
  open Finset Filter MeasureTheory in
  open scoped Interval Topology Classical in by
  dsimp only
  let arcSet (B : ℕ) (r n : ℝ) : Set ℝ :=
    {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ B ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ r / ((q : ℝ) * n)}

  let bandSet (Q B : ℕ) (u n : ℝ) : Set ℝ :=
    {t : ℝ | ∃ q a : ℕ, Q < q ∧ 1 ≤ q ∧ q ≤ B ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ u / ((q : ℝ) * n)}

  have arcSet_mono {B C : ℕ} {r s n : ℝ}
      (hB : B ≤ C) (hr : r ≤ s) (hn : 0 ≤ n) :
      arcSet B r n ⊆ arcSet C s n := by
    intro t ⟨q, a, hq, hqb, ha, hcop, hclose⟩
    exact ⟨q, a, hq, hqb.trans hB, ha, hcop,
      hclose.trans (div_le_div_of_nonneg_right hr (mul_nonneg (Nat.cast_nonneg q) hn))⟩

  have inner_remainder_eq (Q B : ℕ) (r R u n : ℝ)
      (hr : r ≤ R) (hu : u ≤ R) (hn : 0 ≤ n) :
      (((arcSet B R n \ arcSet Q r n) \
        (arcSet Q R n \ arcSet Q r n)) ∩ arcSet B u n) =
        arcSet B u n \ arcSet Q R n := by
    have hA := arcSet_mono (B := Q) (C := Q) (r := r) (s := R) le_rfl hr hn
    have hI := arcSet_mono (B := B) (C := B) (r := u) (s := R) le_rfl hu hn
    ext t
    constructor
    · rintro ⟨⟨⟨_, ha⟩, hl⟩, hi⟩
      exact ⟨hi, fun h => hl ⟨h, ha⟩⟩
    · rintro ⟨hi, hl⟩
      have ha : t ∉ arcSet Q r n := fun h => hl (hA h)
      exact ⟨⟨⟨hI hi, ha⟩, fun h => hl h.1⟩, hi⟩

  have overlap_center_eq {q r a b : ℕ} {u v n t : ℝ}
      (hq : 0 < q) (hr : 0 < r) (hn : 0 < n)
      (hc : a.Coprime q) (hd : b.Coprime r)
      (hsmall : u * (r : ℝ) + v * (q : ℝ) < n)
      (ha : |t - (a : ℝ) / q| ≤ u / ((q : ℝ) * n))
      (hb : |t - (b : ℝ) / r| ≤ v / ((r : ℝ) * n)) :
      q = r ∧ a = b := by
    have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
    have hrr : 0 < (r : ℝ) := by exact_mod_cast hr
    have hprod : 0 < (q : ℝ) * r := mul_pos hqr hrr
    have hrad : u / ((q : ℝ) * n) + v / ((r : ℝ) * n) < 1 / ((q : ℝ) * r) := by
      calc
        u / ((q : ℝ) * n) + v / ((r : ℝ) * n)
            = (u * (r : ℝ) + v * (q : ℝ)) / ((q : ℝ) * r * n) := by field_simp
        _ < n / ((q : ℝ) * r * n) := (div_lt_div_iff_of_pos_right (by positivity)).2 hsmall
        _ = 1 / ((q : ℝ) * r) := by field_simp
    have he : a * r = b * q := by
      by_contra hne
      have hsep : 1 / ((q : ℝ) * r) ≤ |(a : ℝ) / q - b / r| := by
        rw [show (a : ℝ) / q - b / r = (a * r - b * q) / (q * r) by field_simp,
          abs_div, abs_of_pos hprod]
        apply (div_le_div_iff_of_pos_right hprod).2
        rcases lt_or_gt_of_ne hne with hab | hba
        · have hgap : (a : ℝ) * r + 1 ≤ b * q := by exact_mod_cast Nat.succ_le_of_lt hab
          linarith [neg_le_abs ((a : ℝ) * r - b * q)]
        · have hgap : (b : ℝ) * q + 1 ≤ a * r := by exact_mod_cast Nat.succ_le_of_lt hba
          linarith [le_abs_self ((a : ℝ) * r - b * q)]
      have ht := abs_sub_le ((a : ℝ) / q) t ((b : ℝ) / r)
      rw [abs_sub_comm ((a : ℝ) / q) t] at ht
      linarith
    have hdiv1 : q ∣ r := hc.symm.dvd_of_dvd_mul_left (he ▸ dvd_mul_left q b)
    have hdiv2 : r ∣ q := hd.symm.dvd_of_dvd_mul_left (he.symm ▸ dvd_mul_left r a)
    obtain rfl := Nat.dvd_antisymm hdiv1 hdiv2
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_right hq he⟩

  have masked_band_eq (Q B : ℕ) (u R n : ℝ)
      (hu : 0 ≤ u) (huR : u ≤ R) (hn : 0 < n)
      (hsmall : u * (Q : ℝ) + R * (B : ℝ) < n) :
      arcSet B u n \ arcSet Q R n = bandSet Q B u n := by
    ext t
    constructor
    · rintro ⟨⟨q, a, hq, hqB, ha, hcop, hclose⟩, hl⟩
      have hQlt : Q < q := by
        by_contra! hle
        exact hl ⟨q, a, hq, hle, ha, hcop,
          hclose.trans (div_le_div_of_nonneg_right huR (mul_nonneg (Nat.cast_nonneg q) hn.le))⟩
      exact ⟨q, a, hQlt, hq, hqB, ha, hcop, hclose⟩
    · rintro ⟨q, a, hqQ, hq, hqB, ha, hcop, hclose⟩
      refine ⟨⟨q, a, hq, hqB, ha, hcop, hclose⟩, ?_⟩
      rintro ⟨r, b, hr, hrQ, hb, hd, hnear⟩
      have hsmall' : u * (r : ℝ) + R * (q : ℝ) < n :=
        (add_le_add
          (mul_le_mul_of_nonneg_left (by exact_mod_cast hrQ) hu)
          (mul_le_mul_of_nonneg_left (by exact_mod_cast hqB) (hu.trans huR))).trans_lt hsmall
      have he := overlap_center_eq (by omega : 0 < q) (by omega : 0 < r)
        hn hcop hd hsmall' hclose hnear
      omega

  have bandSet_union (Q A B : ℕ) (u n : ℝ) (hQA : Q ≤ A) (hAB : A ≤ B) :
      bandSet Q B u n = bandSet Q A u n ∪ bandSet A B u n := by
    ext t
    constructor
    · rintro ⟨q, a, hqQ, hq1, hqB, ha, hcop, hclose⟩
      by_cases hqA : q ≤ A
      · exact Or.inl ⟨q, a, hqQ, hq1, hqA, ha, hcop, hclose⟩
      · exact Or.inr ⟨q, a, by omega, hq1, hqB, ha, hcop, hclose⟩
    · intro h
      cases h with
      | inl h =>
        rcases h with ⟨q, a, hqQ, hq1, hqA, ha, hcop, hclose⟩
        exact ⟨q, a, hqQ, hq1, hqA.trans hAB, ha, hcop, hclose⟩
      | inr h =>
        rcases h with ⟨q, a, hqA, hq1, hqB, ha, hcop, hclose⟩
        exact ⟨q, a, lt_of_le_of_lt hQA hqA, hq1, hqB, ha, hcop, hclose⟩

  have bandSet_disjoint (Q A B : ℕ) (u n : ℝ)
      (hu : 0 ≤ u) (hn : 0 < n) (hsep : 2 * u * (B : ℝ) < n) (hAB : A ≤ B) :
      Disjoint (bandSet Q A u n) (bandSet A B u n) := by
    rw [Set.disjoint_left]
    rintro t ⟨q, a, _, hq1, hqA, _, hc, ha⟩ ⟨r, b, hrA, hr1, hrB, _, hd, hb⟩
    have hsmall : u * (r : ℝ) + u * (q : ℝ) < n := by
      have h1 : u * (r : ℝ) ≤ u * (B : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hrB) hu
      have h2 : u * (q : ℝ) ≤ u * (B : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast (hqA.trans hAB)) hu
      linarith
    have he := overlap_center_eq (by omega : 0 < q) (by omega : 0 < r) hn hc hd hsmall ha hb
    omega

  have measurableSet_bandSet (Q B : ℕ) (u n : ℝ) :
      MeasurableSet (bandSet Q B u n) := by
    have hEq : bandSet Q B u n =
        ⋃ q ∈ (Finset.Ioc Q B).filter (fun q => 1 ≤ q),
          ⋃ a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q),
            {t : ℝ | |t - (a : ℝ) / (q : ℝ)| ≤ u / ((q : ℝ) * n)} := by
      ext t
      simp only [bandSet, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_filter,
        Finset.mem_Ioc, Finset.mem_range]
      constructor
      · rintro ⟨q, a, hqQ, hq1, hqB, ha, hcop, hclose⟩
        exact ⟨q, ⟨⟨hqQ, hqB⟩, hq1⟩, a, ⟨Nat.lt_succ_of_le ha, hcop⟩, hclose⟩
      · rintro ⟨q, ⟨⟨hqQ, hqB⟩, hq1⟩, a, ⟨ha, hcop⟩, hclose⟩
        exact ⟨q, a, hqQ, hq1, hqB, Nat.lt_succ_iff.mp ha, hcop, hclose⟩
    rw [hEq]
    refine Finset.measurableSet_biUnion _ (fun q _ => Finset.measurableSet_biUnion _ (fun a _ => ?_))
    exact (isClosed_le (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const).measurableSet

  have eventual_geometry :
      ∀ᶠ n : ℕ in atTop,
        1 ≤ n ∧
        1 ≤ (Nat.log 2 (n + 2)) ^ 2 ∧
        (Nat.log 2 (n + 2)) ^ 2 ≤ ⌊(n : ℝ) ^ (1 / 5 : ℝ)⌋₊ ∧
        ⌊(n : ℝ) ^ (1 / 5 : ℝ)⌋₊ ≤ ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ ∧
        ((Nat.log 2 (n + 2)) ^ 2 : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ) ≤
          ((256 * ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ * (Nat.log 2 (n + 2)) ^ 2 : ℕ) : ℝ) ∧
        2 * ((256 * ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ * (Nat.log 2 (n + 2)) ^ 2 : ℕ) : ℝ) *
          (⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ : ℝ) < (n : ℝ) := by
    have hlog_small : ∀ᶠ n : ℕ in atTop,
        ((Nat.log 2 (n + 2)) ^ 2 : ℝ) ≤ (n : ℝ) ^ (1 / 12 : ℝ) := by
      have hlim : Tendsto (fun x : ℝ => (Real.log x) ^ 2 / x ^ (1 / 12 : ℝ)) atTop (nhds (0 : ℝ)) := by
        have h1 := isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 24 by norm_num)
        have h2 := h1.tendsto_div_nhds_zero
        have h3 := h2.pow 2
        simp only [zero_pow (by norm_num : 2 ≠ 0)] at h3
        refine h3.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        rw [div_pow, ← Real.rpow_natCast (x ^ (1 / 24 : ℝ)) 2, ← Real.rpow_mul hx.le]
        norm_num
      have hcomp : Tendsto (fun n : ℕ => (Real.log ((n : ℝ) + 2)) ^ 2 / ((n : ℝ) + 2) ^ (1 / 12 : ℝ))
          atTop (nhds (0 : ℝ)) :=
        hlim.comp ((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
      have hlt := hcomp.eventually (gt_mem_nhds (show (0 : ℝ) < (Real.log 2) ^ 2 / 2 by positivity))
      filter_upwards [hlt, eventually_ge_atTop 4] with n hn h4
      have hnR : (0 : ℝ) < (n : ℝ) := by positivity
      have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hpow_le : ((n : ℝ) + 2) ^ (1 / 12 : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 12 : ℝ) := by
        have h2n : (n : ℝ) + 2 ≤ 2 * (n : ℝ) := by
          have : (4 : ℝ) ≤ n := by exact_mod_cast h4
          linarith
        calc ((n : ℝ) + 2) ^ (1 / 12 : ℝ)
            ≤ (2 * (n : ℝ)) ^ (1 / 12 : ℝ) :=
              Real.rpow_le_rpow hn2.le h2n (by norm_num)
          _ = (2 : ℝ) ^ (1 / 12 : ℝ) * (n : ℝ) ^ (1 / 12 : ℝ) :=
              Real.mul_rpow (by norm_num) hnR.le
          _ ≤ 2 * (n : ℝ) ^ (1 / 12 : ℝ) := by
              have h21 : (2 : ℝ) ^ (1 / 12 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              rw [Real.rpow_one] at h21
              exact mul_le_mul_of_nonneg_right h21 (Real.rpow_nonneg hnR.le _)
      have hlog2 : ((Nat.log 2 (n + 2)) : ℝ) * Real.log 2 ≤ Real.log ((n : ℝ) + 2) := by
        have hpow : (2 : ℝ) ^ (Nat.log 2 (n + 2)) ≤ (n : ℝ) + 2 := by
          exact_mod_cast Nat.pow_log_le_self 2 (by omega : n + 2 ≠ 0)
        have hle := Real.log_le_log (by positivity) hpow
        rwa [Real.log_pow] at hle
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hsq : ((Nat.log 2 (n + 2)) ^ 2 : ℝ) * (Real.log 2) ^ 2 ≤ (Real.log ((n : ℝ) + 2)) ^ 2 := by
        have h0 : 0 ≤ ((Nat.log 2 (n + 2)) : ℝ) * Real.log 2 := by positivity
        nlinarith [sq_nonneg ((Real.log ((n : ℝ) + 2)) - ((Nat.log 2 (n + 2)) : ℝ) * Real.log 2)]
      have hdiv : (Real.log ((n : ℝ) + 2)) ^ 2 <
          (Real.log 2) ^ 2 / 2 * ((n : ℝ) + 2) ^ (1 / 12 : ℝ) :=
        (div_lt_iff₀ (Real.rpow_pos_of_pos hn2 _)).mp hn
      have hfin : ((Nat.log 2 (n + 2)) ^ 2 : ℝ) * (Real.log 2) ^ 2 <
          (Real.log 2) ^ 2 * (n : ℝ) ^ (1 / 12 : ℝ) := by
        calc ((Nat.log 2 (n + 2)) ^ 2 : ℝ) * (Real.log 2) ^ 2
            ≤ (Real.log ((n : ℝ) + 2)) ^ 2 := hsq
          _ < (Real.log 2) ^ 2 / 2 * ((n : ℝ) + 2) ^ (1 / 12 : ℝ) := hdiv
          _ ≤ (Real.log 2) ^ 2 / 2 * (2 * (n : ℝ) ^ (1 / 12 : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hpow_le (by positivity)
          _ = (Real.log 2) ^ 2 * (n : ℝ) ^ (1 / 12 : ℝ) := by ring
      nlinarith [sq_pos_of_pos hlog2_pos]
    filter_upwards [hlog_small, eventually_ge_atTop (10 ^ 16 : ℕ)] with n hlog hbig
    have hn1 : 1 ≤ n := by omega
    have hnR : (0 : ℝ) < (n : ℝ) := by positivity
    have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hQ1 : 1 ≤ (Nat.log 2 (n + 2)) ^ 2 := by
      have : 1 ≤ Nat.log 2 (n + 2) := Nat.le_log_of_pow_le (by norm_num) (by omega)
      nlinarith
    have hn_fifth : (n : ℝ) ^ (1 / 12 : ℝ) + 1 ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by
      have h1 : (2 : ℝ) ≤ (n : ℝ) ^ (1 / 12 : ℝ) := by
        have h212 : (2 : ℝ) ^ (12 : ℕ) ≤ (n : ℝ) := by
          have : (4096 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 4096 ≤ n by omega)
          norm_num; linarith
        have := Real.rpow_le_rpow (by positivity) h212 (show (0 : ℝ) ≤ 1 / 12 by norm_num)
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at this
        norm_num at this
        exact this
      have h2 : (2 : ℝ) * (n : ℝ) ^ (1 / 12 : ℝ) ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by
        have h2g : (2 : ℝ) ≤ (n : ℝ) ^ (7 / 60 : ℝ) := by
          have h260 : (2 : ℝ) ^ (60 : ℕ) ≤ (n : ℝ) ^ (7 : ℕ) := by
            have h210 : (2 : ℝ) ^ (10 : ℕ) ≤ (10 ^ 4 : ℝ) := by norm_num
            have h260_le : (2 : ℝ) ^ (60 : ℕ) ≤ (10 ^ 4 : ℝ) ^ (6 : ℕ) := by
              rw [show (60 : ℕ) = 10 * 6 by norm_num, pow_mul]
              exact pow_le_pow_left₀ (by positivity) h210 6
            have h10 : (10 ^ 4 : ℝ) ^ (6 : ℕ) ≤ (n : ℝ) ^ (7 : ℕ) := by
              have hle1 : (10 ^ 4 : ℝ) ≤ (n : ℝ) := by
                have : (10 ^ 4 : ℕ) ≤ n := by omega
                exact_mod_cast this
              have h6 : (10 ^ 4 : ℝ) ^ (6 : ℕ) ≤ (n : ℝ) ^ (6 : ℕ) :=
                pow_le_pow_left₀ (by positivity) hle1 6
              have h67 : (n : ℝ) ^ (6 : ℕ) ≤ (n : ℝ) ^ (7 : ℕ) := by
                rw [pow_succ]
                exact le_mul_of_one_le_right (by positivity) hn1R
              exact h6.trans h67
            exact h260_le.trans h10
          have := Real.rpow_le_rpow (by positivity) h260 (show (0 : ℝ) ≤ 1 / 60 by norm_num)
          rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
            ← Real.rpow_mul hnR.le] at this
          norm_num at this
          exact this
        calc (2 : ℝ) * (n : ℝ) ^ (1 / 12 : ℝ)
            ≤ (n : ℝ) ^ (7 / 60 : ℝ) * (n : ℝ) ^ (1 / 12 : ℝ) :=
              mul_le_mul_of_nonneg_right h2g (Real.rpow_nonneg hnR.le _)
          _ = (n : ℝ) ^ (7 / 60 + 1 / 12 : ℝ) := (Real.rpow_add hnR _ _).symm
          _ = (n : ℝ) ^ (1 / 5 : ℝ) := by norm_num
      linarith
    have hQA : (Nat.log 2 (n + 2)) ^ 2 ≤ ⌊(n : ℝ) ^ (1 / 5 : ℝ)⌋₊ := by
      apply Nat.le_floor
      push_cast
      exact hlog.trans (by linarith)
    have hAB : ⌊(n : ℝ) ^ (1 / 5 : ℝ)⌋₊ ≤ ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ :=
      Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hn1R (by norm_num))
    have huH : ((Nat.log 2 (n + 2)) ^ 2 : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ) ≤
        ((256 * ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ * (Nat.log 2 (n + 2)) ^ 2 : ℕ) : ℝ) := by
      push_cast
      have hQ1_ge : (n : ℝ) ^ (1 / 6 : ℝ) ≤ 256 * (⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ : ℝ) := by
        have hfl : (n : ℝ) ^ (1 / 3 : ℝ) - 1 < (⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ : ℝ) :=
          Nat.sub_one_lt_floor _
        have h16 : (n : ℝ) ^ (1 / 6 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hn1R (by norm_num)
        have h3ge : (2 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
          have h23 : (2 : ℝ) ^ (3 : ℕ) ≤ (n : ℝ) := by
            have : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 8 ≤ n by omega)
            norm_num; linarith
          have := Real.rpow_le_rpow (by positivity) h23 (show (0 : ℝ) ≤ 1 / 3 by norm_num)
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at this
          norm_num at this
          exact this
        linarith
      have hQnn : (0 : ℝ) ≤ ((Nat.log 2 (n + 2)) ^ 2 : ℝ) := by positivity
      nlinarith
    have hbud : 2 * ((256 * ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ * (Nat.log 2 (n + 2)) ^ 2 : ℕ) : ℝ) *
        (⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ : ℝ) < (n : ℝ) := by
      push_cast
      have hfl : (⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
        Nat.floor_le (Real.rpow_nonneg hnR.le _)
      have h512 : (512 : ℝ) < (n : ℝ) ^ (1 / 4 : ℝ) := by
        have h512_4 : (512 : ℝ) ^ (4 : ℕ) < (n : ℝ) := by
          have : (10 ^ 16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hbig
          have hnum : (512 : ℝ) ^ (4 : ℕ) < (10 ^ 16 : ℝ) := by norm_num
          exact lt_of_lt_of_le hnum this
        have := Real.rpow_lt_rpow (by positivity) h512_4 (show (0 : ℝ) < 1 / 4 by norm_num)
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at this
        norm_num at this
        exact this
      calc 2 * (256 * (⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ : ℝ) * ((Nat.log 2 (n + 2)) ^ 2 : ℝ)) *
            (⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ : ℝ)
          = 512 * ((⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ : ℝ) * (⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ : ℝ)) *
            ((Nat.log 2 (n + 2)) ^ 2 : ℝ) := by ring
        _ ≤ 512 * ((n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ)) * (n : ℝ) ^ (1 / 12 : ℝ) := by
            gcongr
        _ < (n : ℝ) ^ (1 / 4 : ℝ) * ((n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ)) *
            (n : ℝ) ^ (1 / 12 : ℝ) := by
            gcongr
        _ = (n : ℝ) ^ (1 / 4 + 1 / 3 + 1 / 3 + 1 / 12 : ℝ) := by
            rw [Real.rpow_add hnR, Real.rpow_add hnR, Real.rpow_add hnR]; ring
        _ = (n : ℝ) := by norm_num
    exact ⟨hn1, hQ1, hQA, hAB, huH, hbud⟩

  intro e he
  have he2 : 0 < e / 2 := by positivity
  obtain ⟨N1, hN1⟩ := hMidBand (e / 2) he2
  obtain ⟨N2, hN2⟩ := hHighBand (e / 2) he2
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp eventual_geometry
  refine ⟨max N0 (max N1 N2), ?_⟩
  intro n hn hnEven
  have h0 := hN0 n ((le_max_left N0 (max N1 N2)).trans hn)
  have h1 := hN1 n ((le_max_left N1 N2).trans ((le_max_right N0 (max N1 N2)).trans hn)) hnEven
  have h2 := hN2 n ((le_max_right N1 N2).trans ((le_max_right N0 (max N1 N2)).trans hn)) hnEven
  obtain ⟨hn1, hQ1, hQA, hAB, huH, hbud⟩ := h0
  let Q := (Nat.log 2 (n + 2)) ^ 2
  let A := ⌊(n : ℝ) ^ (1 / 5 : ℝ)⌋₊
  let B := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
  let H : ℝ := ((256 * B * Q : ℕ) : ℝ)
  let u : ℝ := (Q : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hu0 : 0 ≤ u := by positivity
  have hQu : (Q : ℝ) ≤ u :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) (Real.one_le_rpow hn1R (by norm_num))
  have hQB : Q ≤ B := hQA.trans hAB
  have huH' : u ≤ H := by
    dsimp only [u, H, Q, B]
    rw [Nat.cast_pow]
    exact huH
  have hbud' : 2 * H * (B : ℝ) < (n : ℝ) := hbud
  have hsep : 2 * u * (B : ℝ) < (n : ℝ) := by
    apply lt_of_le_of_lt _ hbud'
    gcongr
  have hmask : u * (Q : ℝ) + H * (B : ℝ) < (n : ℝ) := by
    apply lt_of_le_of_lt _ hbud'
    have hprod : u * (Q : ℝ) ≤ H * (B : ℝ) :=
      mul_le_mul huH' (by exact_mod_cast hQB) (Nat.cast_nonneg _) (hu0.trans huH')
    linarith
  have hSetEq :
      (((arcSet B H n \ arcSet Q (Q : ℝ) n) \
        (arcSet Q H n \ arcSet Q (Q : ℝ) n)) ∩ arcSet B u n) =
        bandSet Q A u n ∪ bandSet A B u n := by
    rw [inner_remainder_eq Q B (Q : ℝ) H u (n : ℝ) (hQu.trans huH') huH' hnR.le,
      masked_band_eq Q B u H (n : ℝ) hu0 huH' hnR hmask,
      bandSet_union Q A B u (n : ℝ) hQA hAB]
  have hDisj := bandSet_disjoint Q A B u (n : ℝ) hu0 hnR hsep hAB
  let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0
  let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
  let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) =>
    Finset.sum (Finset.range (n + 1)) (fun k => (u k : ℂ) * E ((k : ℝ) * t))
  let f := fun (n : ℕ) (t : ℝ) => (S n w t) ^ 2 * E (-(n : ℝ) * t)
  have hfCont : Continuous (f n) := by
    unfold f S E
    refine Continuous.mul (Continuous.pow ?_ 2) ?_
    · refine Finset.induction_on (Finset.range (n + 1)) ?_ ?_
      · simpa using continuous_const
      · intro k s hk ih
        have hterm : Continuous (fun t : ℝ => (w k : ℂ) *
            Complex.exp (((2 * Real.pi * ((k : ℝ) * t) : ℝ) : ℂ) * Complex.I)) :=
          Continuous.mul continuous_const <| Complex.continuous_exp.comp <|
            (Complex.continuous_ofReal.comp ((continuous_const.mul continuous_id).comp
              (continuous_const.mul continuous_id))).mul continuous_const
        exact (hterm.add ih).congr (fun t => (Finset.sum_insert hk).symm)
    · exact Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp ((continuous_const.mul continuous_id).comp
          (continuous_const.mul continuous_id))).mul continuous_const)
  have hInt0 : IntervalIntegrable (f n) MeasureTheory.volume (0 : ℝ) 1 :=
    hfCont.intervalIntegrable (0 : ℝ) 1
  have hInt1 : IntervalIntegrable (fun t => (bandSet Q A u n).indicator (f n) t)
      MeasureTheory.volume (0 : ℝ) 1 :=
    ⟨hInt0.1.indicator (measurableSet_bandSet Q A u (n : ℝ)),
     hInt0.2.indicator (measurableSet_bandSet Q A u (n : ℝ))⟩
  have hInt2 : IntervalIntegrable (fun t => (bandSet A B u n).indicator (f n) t)
      MeasureTheory.volume (0 : ℝ) 1 :=
    ⟨hInt0.1.indicator (measurableSet_bandSet A B u (n : ℝ)),
     hInt0.2.indicator (measurableSet_bandSet A B u (n : ℝ))⟩
  have hSplit :
      intervalIntegral (fun t => (bandSet Q A u n ∪ bandSet A B u n).indicator (f n) t)
        (0 : ℝ) 1 MeasureTheory.volume =
      intervalIntegral (fun t => (bandSet Q A u n).indicator (f n) t)
        (0 : ℝ) 1 MeasureTheory.volume +
      intervalIntegral (fun t => (bandSet A B u n).indicator (f n) t)
        (0 : ℝ) 1 MeasureTheory.volume := by
    have hfun : (fun t => (bandSet Q A u n ∪ bandSet A B u n).indicator (f n) t) =
        fun t => (bandSet Q A u n).indicator (f n) t + (bandSet A B u n).indicator (f n) t := by
      ext t
      exact congrFun (Set.indicator_union_of_disjoint hDisj (f n)) t
    rw [hfun, intervalIntegral.integral_add hInt1 hInt2]
  change -(e * (n : ℝ)) ≤
    (intervalIntegral (fun t =>
      ((((arcSet B H n \ arcSet Q (Q : ℝ) n) \
        (arcSet Q H n \ arcSet Q (Q : ℝ) n)) ∩ arcSet B u n)).indicator (f n) t)
      (0 : ℝ) 1 MeasureTheory.volume).re
  rw [hSetEq, hSplit, Complex.add_re]
  dsimp only at h1 h2
  have h1' : -(e / 2 * (n : ℝ)) ≤
      (intervalIntegral (fun t => (bandSet Q A u n).indicator (f n) t)
        (0 : ℝ) 1 MeasureTheory.volume).re := h1
  have h2' : -(e / 2 * (n : ℝ)) ≤
      (intervalIntegral (fun t => (bandSet A B u n).indicator (f n) t)
        (0 : ℝ) 1 MeasureTheory.volume).re := h2
  linarith
