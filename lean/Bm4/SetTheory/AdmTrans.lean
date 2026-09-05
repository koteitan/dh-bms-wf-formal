/-
  Part III (§16): admissibility transfers downward along full elementarity, so the pair
  `L Λ ≺ L Θ` produced by Lemma 16.2 consists of two admissible ordinals.
-/
import Bm4.SetTheory.Skolem

universe u

namespace BM4.ST

open Fm

/-! ### The collection formula -/

/-- Satisfaction of the collection formula `∃ nb, (∀ i ∈ na, ∃ j ∈ nb, φ)` over a transitive
domain `W`, with the fresh variable `na` assigned the set `a` and `nb = na + 1`. -/
theorem sat_collFm {W : ZFSet.{u}} (hW : W.IsTransitive) (φ : Fm) (i j na : ℕ)
    (hi : i < na) (hj : j < na) (hfvna : ∀ k ∈ fv φ, k < na)
    (v : ℕ → ZFSet.{u}) {a : ZFSet.{u}} (ha : a ∈ W) :
    SatIn W (Function.update v na a) (Fm.ex (na + 1) (Fm.ball i na (Fm.bex j (na + 1) φ))) ↔
      ∃ b ∈ W, ∀ x ∈ a, ∃ y ∈ b, SatIn W (Function.update (Function.update v i x) j y) φ := by
  have hna_eq : ∀ b : ZFSet.{u},
      (Function.update (Function.update v na a) (na + 1) b) na = a := by
    intro b
    rw [Function.update_of_ne (by omega : na ≠ na + 1), Function.update_self]
  have hnb_eq : ∀ b x : ZFSet.{u},
      (Function.update (Function.update (Function.update v na a) (na + 1) b) i x) (na + 1)
        = b := by
    intro b x
    rw [Function.update_of_ne (by omega : na + 1 ≠ i), Function.update_self]
  have hcongr : ∀ b x y : ZFSet.{u},
      (SatIn W (Function.update (Function.update (Function.update
          (Function.update v na a) (na + 1) b) i x) j y) φ ↔
        SatIn W (Function.update (Function.update v i x) j y) φ) := by
    intro b x y
    apply sat_congr
    intro k hk
    have hklt := hfvna k hk
    have hkna : k ≠ na := by omega
    have hknb : k ≠ na + 1 := by omega
    by_cases hkj : k = j
    · subst hkj; simp
    · rw [Function.update_of_ne hkj, Function.update_of_ne hkj]
      by_cases hki : k = i
      · subst hki; simp
      · rw [Function.update_of_ne hki, Function.update_of_ne hki,
          Function.update_of_ne hknb, Function.update_of_ne hkna]
  simp only [SatIn]
  rw [sat_ex]
  constructor
  · rintro ⟨b, hbW, hb⟩
    refine ⟨b, hbW, ?_⟩
    rw [sat_ball_of_ne (show i ≠ na by omega)] at hb
    intro x hx
    have h2 := hb x (hW.subset_of_mem ha hx) (by rw [hna_eq b]; exact hx)
    rw [sat_bex_of_ne (show j ≠ na + 1 by omega)] at h2
    obtain ⟨y, _, hyb, hsy⟩ := h2
    rw [hnb_eq b x] at hyb
    exact ⟨y, hyb, (hcongr b x y).mp hsy⟩
  · rintro ⟨b, hbW, hb⟩
    refine ⟨b, hbW, ?_⟩
    rw [sat_ball_of_ne (show i ≠ na by omega)]
    intro x _ hxa
    rw [hna_eq b] at hxa
    rw [sat_bex_of_ne (show j ≠ na + 1 by omega)]
    obtain ⟨y, hyb, hsy⟩ := hb x hxa
    exact ⟨y, hW.subset_of_mem hbW hyb, by rw [hnb_eq b x]; exact hyb, (hcongr b x y).mpr hsy⟩

/-! ### Downward transfer of admissibility -/

/-- If `L Λ ≺ L θ` with `θ` admissible, `ω < Λ` and `Λ` a limit, then `Λ` is admissible. -/
theorem isAdmissible_of_elemFull {Λ θ : Ordinal.{u}} (hω : Ordinal.omega0 < Λ)
    (hlim : Order.IsSuccLimit Λ) (hel : ElemFull (L Λ) (L θ)) (hθ : IsAdmissible θ) :
    IsAdmissible Λ := by
  refine ⟨hω, hlim, ?_⟩
  intro s P hP i j hij v hv a ha hcol
  obtain ⟨φ, -, hfvs, hsatφ⟩ := id hP
  have hΛT : (L Λ).IsTransitive := L_transitive Λ
  have hθT : (L θ).IsTransitive := L_transitive θ
  have hΛpos : (0 : Ordinal.{u}) < Λ := Ordinal.omega0_pos.trans hω
  have hDΛ : GoodDom (· ∈ L Λ) := goodDom_mem hΛT (L_nonempty hΛpos)
  have hDθ : GoodDom (· ∈ L θ) := hθ.goodDom
  have hsub : L Λ ⊆ L θ := hel.1
  -- updating `v` at `i` and `j` keeps the values inside the domain
  have hvalW : ∀ W : ZFSet.{u}, ValD (· ∈ W) ((s.erase i).erase j) v →
      ∀ x y : ZFSet.{u}, x ∈ W → y ∈ W →
        ValD (· ∈ W) s (Function.update (Function.update v i x) j y) := by
    intro W hvW x y hx hy k hk
    by_cases hkj : k = j
    · subst hkj; simpa
    · rw [Function.update_of_ne hkj]
      by_cases hki : k = i
      · subst hki; simpa
      · rw [Function.update_of_ne hki]
        exact hvW k (Finset.mem_erase.mpr ⟨hkj, Finset.mem_erase.mpr ⟨hki, hk⟩⟩)
  have hvθ : ValD (· ∈ L θ) ((s.erase i).erase j) v := fun k hk => hsub (hv k hk)
  have haθ : a ∈ L θ := hsub ha
  -- Step 1: `P` is absolute between `L Λ` and `L θ`
  have habs : ∀ w : ℕ → ZFSet.{u}, ValD (· ∈ L Λ) s w → (P (· ∈ L Λ) w ↔ P (· ∈ L θ) w) := by
    intro w hw
    exact (hP.absolute hDΛ hw).trans (hP.absolute hDθ (fun k hk => hsub (hw k hk))).symm
  -- Step 2: collect inside `L θ`
  have hcolθ : ∀ x ∈ a, ∃ y ∈ L θ,
      P (· ∈ L θ) (Function.update (Function.update v i x) j y) := by
    intro x hx
    obtain ⟨y, hy, hPy⟩ := hcol x hx
    exact ⟨y, hsub hy, (habs _ (hvalW (L Λ) hv x y (hΛT.subset_of_mem ha hx) hy)).mp hPy⟩
  obtain ⟨b₀, hb₀, hb₀spec⟩ := hθ.collection s P hP i j hij v hvθ a haθ hcolθ
  -- Step 3: fresh variables for the collection formula
  obtain ⟨na, hina, hjna, hfvna⟩ :
      ∃ na : ℕ, i < na ∧ j < na ∧ ∀ k ∈ fv φ, k < na :=
    ⟨max (bound φ) (max i j) + 1, by omega, by omega,
      fun k hk => by have := fv_lt_bound hk; omega⟩
  -- the collection formula holds in `L θ`
  have hsatθ : SatIn (L θ) (Function.update v na a)
      (Fm.ex (na + 1) (Fm.ball i na (Fm.bex j (na + 1) φ))) := by
    rw [sat_collFm hθT φ i j na hina hjna hfvna v haθ]
    refine ⟨b₀, hb₀, ?_⟩
    intro x hx
    obtain ⟨y, hyb, hPy⟩ := hb₀spec x hx
    exact ⟨y, hyb, (hsatφ (· ∈ L θ) _ hDθ (hvalW (L θ) hvθ x y (hθT.subset_of_mem haθ hx)
      (hθT.subset_of_mem hb₀ hyb))).mpr hPy⟩
  -- Step 4: reflect it down to `L Λ`
  have hfvsub : fv (Fm.ex (na + 1) (Fm.ball i na (Fm.bex j (na + 1) φ))) ⊆
      insert na (((fv φ).erase i).erase j) := by
    intro k hk
    simp only [fv_ex, fv_ball, fv_bex, Finset.mem_erase, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton] at hk ⊢
    tauto
  have hvalΨ : ∀ k ∈ fv (Fm.ex (na + 1) (Fm.ball i na (Fm.bex j (na + 1) φ))),
      Function.update v na a k ∈ L Λ := by
    intro k hk
    have hk2 := hfvsub hk
    rw [Finset.mem_insert] at hk2
    rcases hk2 with rfl | hk2
    · simpa using ha
    · rw [Finset.mem_erase, Finset.mem_erase] at hk2
      obtain ⟨hkj, hki, hkfv⟩ := hk2
      rw [Function.update_of_ne (by have := hfvna k hkfv; omega : k ≠ na)]
      exact hv k (Finset.mem_erase.mpr ⟨hkj, Finset.mem_erase.mpr ⟨hki, hfvs hkfv⟩⟩)
  have hsatΛ : SatIn (L Λ) (Function.update v na a)
      (Fm.ex (na + 1) (Fm.ball i na (Fm.bex j (na + 1) φ))) :=
    (hel.2 _ (Function.update v na a) hvalΨ).mpr hsatθ
  rw [sat_collFm hΛT φ i j na hina hjna hfvna v ha] at hsatΛ
  obtain ⟨b, hbΛ, hbspec⟩ := hsatΛ
  refine ⟨b, hbΛ, ?_⟩
  intro x hx
  obtain ⟨y, hyb, hsy⟩ := hbspec x hx
  exact ⟨y, hyb, (hsatφ (· ∈ L Λ) _ hDΛ (hvalW (L Λ) hv x y (hΛT.subset_of_mem ha hx)
    (hΛT.subset_of_mem hbΛ hyb))).mp hsy⟩

/-! ### Lemma 16.2 with both ordinals admissible -/

/-- Lemma 16.2, recording that the `Λ` produced is a limit ordinal. -/
theorem exists_elemFull_pair' :
    ∃ Λ : Ordinal.{u}, Ordinal.omega0 < Λ ∧ Order.IsSuccLimit Λ ∧ Λ < omega1.{u} ∧
      ElemFull (L Λ) (L omega1.{u}) := by
  refine ⟨Lam (Ordinal.omega0 + 1), ?_, Lam_isSuccLimit _, Lam_lt_omega1 ?_, elemFull_L_Lam ?_⟩
  · exact lt_of_lt_of_le (Order.lt_add_one_iff.mpr le_rfl) (chain_le_Lam _ 0)
  · exact omega1_isSuccLimit.add_one_lt omega0_lt_omega1
  · exact omega1_isSuccLimit.add_one_lt omega0_lt_omega1

/-- Lemma 16.2 with both ordinals admissible. -/
theorem exists_admissible_elemFull_pair :
    ∃ Λ Θ : Ordinal.{u}, IsAdmissible Λ ∧ IsAdmissible Θ ∧ Λ < Θ ∧ ElemFull (L Λ) (L Θ) := by
  obtain ⟨Λ, hω, hlim, hlt, hel⟩ := exists_elemFull_pair'.{u}
  exact ⟨Λ, omega1.{u}, isAdmissible_of_elemFull hω hlim hel isAdmissible_omega1',
    isAdmissible_omega1', hlt, hel⟩

end BM4.ST
