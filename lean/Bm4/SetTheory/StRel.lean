/-
  Part III, §15: correctness of the internal stability predicates.

  Lemma 15.3 (`stK_iff`): for good `ξ < θ`, the predicate `St_k(ξ)` evaluated in `L θ` says
  exactly `L ξ ≺*_{k+2} L θ`.
  Lemma 15.5 (`relK_iff`): for good `ξ < η < θ`, the predicate `Rel_k(ξ, η)` evaluated in `L θ`
  says exactly `L ξ ≺*_{k+2} L η`.
-/
import Bm4.SetTheory.Good
import Bm4.SetTheory.TV
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

/-! ### Elementary facts -/

theorem isSeqA_of_subset {A B a : ZFSet.{u}} (h : IsSeqA ωZ A a) (hAB : A ⊆ B) :
    IsSeqA ωZ B a := ⟨h.1, h.2.1, fun i x hix => hAB (h.2.2 i x hix)⟩

theorem tvBody_of_tvConj {D : ZFSet.{u} → Prop} {h w M : ZFSet.{u}} :
    ∀ (q j : ℕ), 1 ≤ j → j ≤ q → TVConj D h w q M → TVBody D h w j M := by
  intro q
  induction q with
  | zero => intro j h1 h2 _; omega
  | succ q ih =>
    intro j h1 h2 hc
    rcases Nat.lt_or_ge j (q + 1) with hlt | hge
    · exact ih j h1 (by omega) hc.1
    · have hj : j = q + 1 := by omega
      subst hj
      exact hc.2

/-! ### The truth predicate transfers between `L ξ` and `L θ`

This uses only the Lévy complexity of `TrSigS` (Lemma 13.5) and `≺*`, not the correctness of the
truth predicate; in particular no hypothesis on the code or on the assignment is needed. -/

theorem trSigS_transfer {ξ θ : Ordinal.{u}} (hθ : GoodOrd θ) (hξ : GoodOrd ξ) (hlt : ξ < θ)
    {k : ℕ} (hel : ElemHat (k + 2) (L ξ) (L θ)) {j : ℕ} (hj : j ≤ k + 2)
    {e a : ZFSet.{u}} (he : e ∈ L ξ) (ha : a ∈ L ξ) :
    TrSigS (· ∈ L θ) (L Ordinal.omega0) ωZ j e a ↔
      TrSigS (· ∈ L ξ) (L Ordinal.omega0) ωZ j e a := by
  classical
  obtain ⟨φ, hφ, hfvφ, hsat⟩ := (trComplexity.{u} j 0 1 2 3 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)).1
  set vv : ℕ → ZFSet.{u} := fun i =>
    if i = 0 then L Ordinal.omega0.{u} else if i = 1 then ωZ.{u} else if i = 2 then e else a
    with hvv
  have hv0 : vv 0 = L Ordinal.omega0.{u} := by simp [hvv]
  have hv1 : vv 1 = ωZ.{u} := by simp [hvv]
  have hv2 : vv 2 = e := by simp [hvv]
  have hv3 : vv 3 = a := by simp [hvv]
  have hvalξ : ValD (· ∈ L ξ) ({0, 1, 2, 3} : Finset ℕ) vv := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · rw [hv0]; exact hξ.Lomega_mem
    · rw [hv1]; exact hξ.omegaZ_mem
    · rw [hv2]; exact he
    · rw [hv3]; exact ha
  have hsub : L ξ ⊆ L θ := L_mono hlt.le
  have hvalθ : ValD (· ∈ L θ) ({0, 1, 2, 3} : Finset ℕ) vv := fun i hi => hsub (hvalξ i hi)
  have hgξ : GoodDom (· ∈ L ξ) := goodDom_mem hξ.transitive ⟨ωZ, hξ.omegaZ_mem⟩
  have hgθ : GoodDom (· ∈ L θ) := goodDom_mem hθ.transitive ⟨ωZ, hθ.omegaZ_mem⟩
  have h1 := hsat (· ∈ L ξ) vv hgξ hvalξ
  have h2 := hsat (· ∈ L θ) vv hgθ hvalθ
  simp only [hv0, hv1, hv2, hv3] at h1 h2
  have hE : SatIn (L ξ) vv φ ↔ SatIn (L θ) vv φ := by
    refine hel.sigma (j := max j 1) (by omega) hφ ?_
    intro x hx
    exact hvalξ x (hfvφ hx)
  rw [← h1, ← h2]
  exact hE.symm

/-! ### The bridge: `TV_{k+2}(L ξ)` computed in `L θ` is `L ξ ≺*_{k+2} L θ` -/

theorem tvq_iff_elemHat {ξ θ : Ordinal.{u}} (hθ : GoodOrd θ) (hξ : GoodOrd ξ) (hlt : ξ < θ)
    (k : ℕ) :
    TVq (· ∈ L θ) (L Ordinal.omega0) ωZ (k + 2) (L ξ) ↔ ElemHat (k + 2) (L ξ) (L θ) := by
  constructor
  · -- `TV` gives elementarity: normalise, then use the correctness of the truth predicate.
    rintro ⟨-, -, -, -, hconj⟩
    refine elemHat_of_downward hξ.transitive hθ.transitive (L_mono hlt.le) ?_
    intro j hj1 hj2 φ hφ v hv hsatθ
    obtain ⟨b, hbSig, hbnd, -, hbsat⟩ := (exists_norm.{u} j).1 0 φ hφ
    have hemp : (∅ : ZFSet.{u}) ∈ L ξ := hξ.wClosed.empty_mem
    obtain ⟨a0, ha0, -, ha0val⟩ := exists_seq_of_val (fv φ) v hv
    obtain ⟨a, ha, -, haval, hadom⟩ := exists_padSeq ha0 hemp (b.blockVars.sum + 1)
    have haξ : a ∈ L ξ := isSeqA_mem_of_wClosed hξ.wClosed ha
    have hsub : L ξ ⊆ L θ := L_mono hlt.le
    have hLω : L Ordinal.omega0.{u} ⊆ L ξ := L_mono hξ.omega_lt.le
    have hcodeξ : BF.code.{u} b ∈ L ξ := hLω (BF.code_mem_Lω b)
    have hdom : ∀ i ∈ b.blockVars, ∃ y, ZFSet.pair (natZ.{u} i) y ∈ a := by
      intro i hi
      have := List.le_sum_of_mem hi
      exact hadom i (by omega)
    have hGξ : GoodAsn (L ξ) b a := ⟨ha, haξ, hdom, hbnd, hcodeξ, hξ.wClosed⟩
    have hGθ : GoodAsn (L θ) b a :=
      ⟨isSeqA_of_subset ha hsub, hsub haξ, hdom, hbnd, hsub hcodeξ, hθ.wClosed⟩
    have hagree : ∀ x ∈ fv φ, v x = SeqVal a x := by
      intro x hx
      rw [haval, ha0val x hx]
    have hsat1 : Sat (· ∈ L θ) (SeqVal a) φ := (sat_congr hagree).mp hsatθ
    have hsat2 : Sat (· ∈ L θ) (SeqVal a) b.toFm :=
      (hbsat _ ⟨ωZ, hθ.omegaZ_mem⟩ (SeqVal a)).mpr hsat1
    have htrθ : TrSigS (· ∈ L θ) (L Ordinal.omega0) ωZ j (BF.code.{u} b) a :=
      (trSigS_correct hθ.transitive hθ.base j b hbSig a hGθ).mpr hsat2
    have htrξ : TrSigS (· ∈ L ξ) (L Ordinal.omega0) ωZ j (BF.code.{u} b) a :=
      tvBody_of_tvConj (k + 2) j hj1 hj2 hconj (BF.code.{u} b) hcodeξ a haξ
        ((isSigCodeW_iff j _).mpr ⟨b, hbSig, rfl⟩) ha htrθ
    have hsat3 : Sat (· ∈ L ξ) (SeqVal a) b.toFm :=
      (trSigS_correct hξ.transitive hξ.base j b hbSig a hGξ).mp htrξ
    have hsat4 : Sat (· ∈ L ξ) (SeqVal a) φ :=
      (hbsat _ ⟨ωZ, hξ.omegaZ_mem⟩ (SeqVal a)).mp hsat3
    exact (sat_congr hagree).mpr hsat4
  · -- elementarity gives `TV`: the truth predicate is Σ̂j, hence absolute between `L ξ` and `L θ`.
    intro hel
    refine ⟨hξ.transitive, ⟨ωZ, hξ.omegaZ_mem⟩, hξ.Lomega_mem, hξ.omegaZ_mem, ?_⟩
    have key : ∀ q, q ≤ k + 2 → TVConj (· ∈ L θ) (L Ordinal.omega0) ωZ q (L ξ) := by
      intro q
      induction q with
      | zero => intro _; trivial
      | succ q ih =>
        intro hq
        refine ⟨ih (by omega), ?_⟩
        intro e he a ha _ _ htr
        exact (trSigS_transfer hθ hξ hlt hel (by omega) he ha).mp htr
    exact key (k + 2) le_rfl

/-! ### Lemma 15.3 and Lemma 15.5 -/

/-- **Lemma 15.3**: for good `ξ < θ`, the internal predicate `St_k(ξ)` evaluated in `L θ`
expresses `L ξ ≺*_{k+2} L θ`. -/
theorem stK_iff {ξ θ : Ordinal.{u}} (hθ : GoodOrd θ) (hξ : GoodOrd ξ) (hlt : ξ < θ) (k : ℕ) :
    StK (· ∈ L θ) (L Ordinal.omega0) ωZ k ξ.toZFSet ↔ ElemHat (k + 2) (L ξ) (L θ) := by
  constructor
  · intro hst
    obtain ⟨c, hc, hcode⟩ := hθ.lcode_L hlt
    exact (tvq_iff_elemHat hθ hξ hlt k).mp (hst (L ξ) (hθ.L_mem hlt) c hc hcode)
  · intro hel M hM c hc hcode
    have hM' : M = L ξ := lcode_sound hcode
    subst hM'
    exact (tvq_iff_elemHat hθ hξ hlt k).mpr hel

/-- **Lemma 15.5**: for good `ξ < η < θ`, the internal predicate `Rel_k(ξ, η)` evaluated in `L θ`
expresses `L ξ ≺*_{k+2} L η`. -/
theorem relK_iff {ξ η θ : Ordinal.{u}} (hθ : GoodOrd θ) (hη : GoodOrd η) (hξ : GoodOrd ξ)
    (hξη : ξ < η) (hηθ : η < θ) (k : ℕ) :
    RelK (· ∈ L θ) (L Ordinal.omega0) ωZ k ξ.toZFSet η.toZFSet ↔ ElemHat (k + 2) (L ξ) (L η) := by
  constructor
  · rintro ⟨M, -, -, c, -, hcode, hst⟩
    have hM' : M = L η := lcode_sound hcode
    subst hM'
    exact (stK_iff hη hξ hξη k).mp hst
  · intro hel
    obtain ⟨c, hc, hcode⟩ := hθ.lcode_L hηθ
    exact ⟨L η, hθ.L_mem hηθ,
      ⟨hη.transitive, ⟨ωZ, hη.omegaZ_mem⟩, hη.Lomega_mem, hη.omegaZ_mem, hη.toZFSet_mem hξη⟩,
      c, hc, hcode, (stK_iff hη hξ hξη k).mpr hel⟩

end BM4.ST
