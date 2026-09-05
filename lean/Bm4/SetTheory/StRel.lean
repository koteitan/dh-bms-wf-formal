/-
  Part III, §15: correctness of the internal stability predicates.

  Lemma 15.3 (`stK_iff`): for good `ξ < θ`, the predicate `St_k(ξ)` evaluated in `L θ` says
  exactly `L ξ ≺*_{k+2} L θ`.
  Lemma 15.5 (`relK_iff`): for good `ξ < η < θ`, the predicate `Rel_k(ξ, η)` evaluated in `L θ`
  says exactly `L ξ ≺*_{k+2} L η`.
-/
import Bm4.SetTheory.Good
import Bm4.SetTheory.BFConv

universe u

namespace BM4.ST

open Fm

/-! ### List helpers -/

theorem dedup_ne_nil {α : Type*} [DecidableEq α] {l : List α} (h : l ≠ []) : l.dedup ≠ [] := by
  rcases l with _ | ⟨a, t⟩
  · exact absurd rfl h
  · intro he
    have hm : a ∈ (a :: t).dedup := by rw [List.mem_dedup]; simp
    rw [he] at hm
    simp at hm

theorem map_ne_nil {α β : Type*} (f : α → β) {l : List α} (h : l ≠ []) : l.map f ≠ [] := by
  rcases l with _ | ⟨a, t⟩
  · exact absurd rfl h
  · simp

/-! ### Inversion for the alternating hierarchy -/

theorem isSigma_zero_inv : ∀ {φ : Fm}, IsSigma 0 φ → IsDelta0 φ
  | _, .zero h => h

theorem isPi_zero_inv : ∀ {φ : Fm}, IsPi 0 φ → IsDelta0 φ
  | _, .zero h => h

theorem isSigma_succ_inv : ∀ {q : ℕ} {φ : Fm}, IsSigma (q + 1) φ →
    ∃ (l : List ℕ) (ψ : Fm), l ≠ [] ∧ l.Nodup ∧ IsPi q ψ ∧ φ = Fm.exs l ψ
  | _, _, .succ l hl hnd hp => ⟨l, _, hl, hnd, hp, rfl⟩

theorem isPi_succ_inv : ∀ {q : ℕ} {φ : Fm}, IsPi (q + 1) φ →
    ∃ (l : List ℕ) (ψ : Fm), l ≠ [] ∧ l.Nodup ∧ IsSigma q ψ ∧ φ = Fm.alls l ψ
  | _, _, .succ l hl hnd hp => ⟨l, _, hl, hnd, hp, rfl⟩

/-! ### Removing repetitions inside a quantifier block

A repeated variable inside one block is vacuous (the innermost binding wins), so a block may be
replaced by its duplicate-free version. -/

theorem sat_exs_dedup {D : ZFSet.{u} → Prop} (hD : ∃ z, D z) (χ : Fm) (l : List ℕ) :
    ∀ v : ℕ → ZFSet.{u}, Sat D v (Fm.exs l.dedup χ) ↔ Sat D v (Fm.exs l χ) := by
  induction l with
  | nil => intro v; rfl
  | cons i l ih =>
    intro v
    by_cases hi : i ∈ l
    · have hnot : i ∉ fv (Fm.exs l χ) := by
        rw [Fm.fv_exs]
        simp only [Finset.mem_sdiff, List.mem_toFinset, not_and, not_not]
        intro _; exact hi
      rw [List.dedup_cons_of_mem hi, ih v, Fm.exs_cons]
      exact (sat_ex_of_notMem (v := v) hnot hD).symm
    · rw [List.dedup_cons_of_notMem hi, Fm.exs_cons, Fm.exs_cons]
      simp only [sat_ex]
      exact exists_congr fun z => and_congr_right fun _ => ih _

theorem sat_alls_dedup {D : ZFSet.{u} → Prop} (hD : ∃ z, D z) (χ : Fm) (l : List ℕ) :
    ∀ v : ℕ → ZFSet.{u}, Sat D v (Fm.alls l.dedup χ) ↔ Sat D v (Fm.alls l χ) := by
  induction l with
  | nil => intro v; rfl
  | cons i l ih =>
    intro v
    by_cases hi : i ∈ l
    · have hnot : i ∉ fv (Fm.alls l χ) := by
        rw [Fm.fv_alls]
        simp only [Finset.mem_sdiff, List.mem_toFinset, not_and, not_not]
        intro _; exact hi
      rw [List.dedup_cons_of_mem hi, ih v, Fm.alls_cons]
      exact (sat_all_of_notMem (v := v) hnot hD).symm
    · rw [List.dedup_cons_of_notMem hi, Fm.alls_cons, Fm.alls_cons]
      simp only [sat_all]
      exact forall_congr' fun z => imp_congr_right fun _ => ih _

/-! ### Normalisation

Every Σ̂q / Π̂q formula is equivalent (over a nonempty domain) to a block formula whose block
variables are pairwise distinct and arbitrarily large.  This is what makes `GoodAsn` available
for the correctness theorem 13.6. -/

theorem exists_norm : ∀ j : ℕ,
    (∀ (K : ℕ) (φ : Fm), IsSigma j φ → ∃ b : BF, BF.Sig j b ∧ b.blockVars.Nodup ∧
        (∀ i ∈ b.blockVars, K ≤ i) ∧
        ∀ (D : ZFSet.{u} → Prop), (∃ z, D z) → ∀ v : ℕ → ZFSet.{u},
          (Sat D v b.toFm ↔ Sat D v φ)) ∧
    (∀ (K : ℕ) (φ : Fm), IsPi j φ → ∃ b : BF, BF.Pi j b ∧ b.blockVars.Nodup ∧
        (∀ i ∈ b.blockVars, K ≤ i) ∧
        ∀ (D : ZFSet.{u} → Prop), (∃ z, D z) → ∀ v : ℕ → ZFSet.{u},
          (Sat D v b.toFm ↔ Sat D v φ)) := by
  intro j
  induction j with
  | zero =>
    refine ⟨fun K φ hφ => ⟨BF.delta true φ, .zero (isSigma_zero_inv hφ), ?_, ?_,
        fun _ _ _ => Iff.rfl⟩, fun K φ hφ => ⟨BF.delta true φ, .zero (isPi_zero_inv hφ), ?_, ?_,
        fun _ _ _ => Iff.rfl⟩⟩ <;> simp [BF.blockVars]
  | succ q ih =>
    constructor
    · intro K φ hφ
      obtain ⟨l, ψ, hl, -, hp, rfl⟩ := isSigma_succ_inv hφ
      obtain ⟨Kx, hKx⟩ : ∃ n : ℕ, n = Fm.bound (Fm.exs l ψ) + K + 1 := ⟨_, rfl⟩
      have hKb : ∀ i ∈ fv (Fm.exs l ψ), i < Kx := by
        intro i hi
        have := Fm.fv_lt_bound hi
        omega
      obtain ⟨g, hg⟩ : ∃ f : ℕ → ℕ, f = Fm.avoidMap (Fm.exs l ψ) Kx := ⟨_, rfl⟩
      have hginj : Function.Injective g := by
        rw [hg]; exact Fm.avoidMap_injective _ hKb
      have hlg : ∀ i ∈ l.map g, Kx ≤ i := by
        intro i hi
        obtain ⟨j0, hj0, rfl⟩ := List.mem_map.mp hi
        have hjn : j0 ∉ fv (Fm.exs l ψ) := by
          rw [Fm.fv_exs]
          simp only [Finset.mem_sdiff, List.mem_toFinset, not_and, not_not]
          intro _; exact hj0
        rw [hg]
        simp only [Fm.avoidMap, if_neg hjn]
        omega
      obtain ⟨l', hl'⟩ : ∃ m : List ℕ, m = (l.map g).dedup := ⟨_, rfl⟩
      have hl'nd : l'.Nodup := by rw [hl']; exact List.nodup_dedup _
      have hl'ne : l' ≠ [] := by rw [hl']; exact dedup_ne_nil (map_ne_nil g hl)
      have hl'ge : ∀ i ∈ l', Kx ≤ i := by
        intro i hi
        rw [hl', List.mem_dedup] at hi
        exact hlg i hi
      obtain ⟨K2, hK2⟩ : ∃ n : ℕ, n = l'.sum + Kx + 1 := ⟨_, rfl⟩
      have hl'lt : ∀ i ∈ l', i < K2 := by
        intro i hi
        have := List.le_sum_of_mem hi
        omega
      obtain ⟨b, hbPi, hbnd, hbK, hbsat⟩ := ih.2 K2 (Fm.rename g ψ) (IsPi.rename hginj hp)
      refine ⟨BF.exs l' b, BF.Sig.succ hl'ne hbPi, ?_, ?_, ?_⟩
      · simp only [BF.blockVars]
        refine List.nodup_append.mpr ⟨hl'nd, hbnd, ?_⟩
        intro i hi i2 hi2
        have h1 := hl'lt i hi
        have h2 := hbK i2 hi2
        omega
      · intro i hi
        simp only [BF.blockVars, List.mem_append] at hi
        rcases hi with hi | hi
        · have := hl'ge i hi; omega
        · have := hbK i hi; omega
      · intro D hD v
        have e1 : Sat D v (BF.exs l' b).toFm ↔ Sat D v (Fm.exs l' (Fm.rename g ψ)) := by
          rw [toFm_exs]
          exact Fm.sat_exs_congr (fun w => hbsat D hD w) l' v
        have e2 : Sat D v (Fm.exs l' (Fm.rename g ψ)) ↔
            Sat D v (Fm.exs (l.map g) (Fm.rename g ψ)) := by
          rw [hl']; exact sat_exs_dedup hD _ _ v
        have e3 : Sat D v (Fm.exs (l.map g) (Fm.rename g ψ)) ↔ Sat D v (Fm.exs l ψ) := by
          rw [← Fm.rename_exs g l ψ, hg]
          exact Fm.sat_rename_avoidMap (Fm.exs l ψ) hKb D v
        exact e1.trans (e2.trans e3)
    · intro K φ hφ
      obtain ⟨l, ψ, hl, -, hp, rfl⟩ := isPi_succ_inv hφ
      obtain ⟨Kx, hKx⟩ : ∃ n : ℕ, n = Fm.bound (Fm.alls l ψ) + K + 1 := ⟨_, rfl⟩
      have hKb : ∀ i ∈ fv (Fm.alls l ψ), i < Kx := by
        intro i hi
        have := Fm.fv_lt_bound hi
        omega
      obtain ⟨g, hg⟩ : ∃ f : ℕ → ℕ, f = Fm.avoidMap (Fm.alls l ψ) Kx := ⟨_, rfl⟩
      have hginj : Function.Injective g := by
        rw [hg]; exact Fm.avoidMap_injective _ hKb
      have hlg : ∀ i ∈ l.map g, Kx ≤ i := by
        intro i hi
        obtain ⟨j0, hj0, rfl⟩ := List.mem_map.mp hi
        have hjn : j0 ∉ fv (Fm.alls l ψ) := by
          rw [Fm.fv_alls]
          simp only [Finset.mem_sdiff, List.mem_toFinset, not_and, not_not]
          intro _; exact hj0
        rw [hg]
        simp only [Fm.avoidMap, if_neg hjn]
        omega
      obtain ⟨l', hl'⟩ : ∃ m : List ℕ, m = (l.map g).dedup := ⟨_, rfl⟩
      have hl'nd : l'.Nodup := by rw [hl']; exact List.nodup_dedup _
      have hl'ne : l' ≠ [] := by rw [hl']; exact dedup_ne_nil (map_ne_nil g hl)
      have hl'ge : ∀ i ∈ l', Kx ≤ i := by
        intro i hi
        rw [hl', List.mem_dedup] at hi
        exact hlg i hi
      obtain ⟨K2, hK2⟩ : ∃ n : ℕ, n = l'.sum + Kx + 1 := ⟨_, rfl⟩
      have hl'lt : ∀ i ∈ l', i < K2 := by
        intro i hi
        have := List.le_sum_of_mem hi
        omega
      obtain ⟨b, hbSig, hbnd, hbK, hbsat⟩ := ih.1 K2 (Fm.rename g ψ) (IsSigma.rename hginj hp)
      refine ⟨BF.alls l' b, BF.Pi.succ hl'ne hbSig, ?_, ?_, ?_⟩
      · simp only [BF.blockVars]
        refine List.nodup_append.mpr ⟨hl'nd, hbnd, ?_⟩
        intro i hi i2 hi2
        have h1 := hl'lt i hi
        have h2 := hbK i2 hi2
        omega
      · intro i hi
        simp only [BF.blockVars, List.mem_append] at hi
        rcases hi with hi | hi
        · have := hl'ge i hi; omega
        · have := hbK i hi; omega
      · intro D hD v
        have e1 : Sat D v (BF.alls l' b).toFm ↔ Sat D v (Fm.alls l' (Fm.rename g ψ)) := by
          rw [toFm_alls]
          exact Fm.sat_alls_congr (fun w => hbsat D hD w) l' v
        have e2 : Sat D v (Fm.alls l' (Fm.rename g ψ)) ↔
            Sat D v (Fm.alls (l.map g) (Fm.rename g ψ)) := by
          rw [hl']; exact sat_alls_dedup hD _ _ v
        have e3 : Sat D v (Fm.alls (l.map g) (Fm.rename g ψ)) ↔ Sat D v (Fm.alls l ψ) := by
          rw [← Fm.rename_alls g l ψ, hg]
          exact Fm.sat_rename_avoidMap (Fm.alls l ψ) hKb D v
        exact e1.trans (e2.trans e3)

/-! ### Auxiliary Δ₀ predicate -/

/-- `M` is nonempty. -/
theorem delta0_nonemptyMem (M : ℕ) : Delta0Def.{u} {M} (fun _ v => ∃ x, x ∈ v M) := by
  have h1 := Delta0Def.top.{u}.bex (M + 1) M (by omega)
  refine (h1.congr ?_).of_eq ?_
  · intro D v _ _
    exact ⟨fun ⟨x, hx, _⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨x, hx, trivial⟩⟩
  · ext k
    simp

/-! ### Elementary facts -/

theorem isSeqA_of_subset {A B a : ZFSet.{u}} (h : IsSeqA ωZ A a) (hAB : A ⊆ B) :
    IsSeqA ωZ B a := ⟨h.1, h.2.1, fun i x hix => hAB (h.2.2 i x hix)⟩

end BM4.ST
