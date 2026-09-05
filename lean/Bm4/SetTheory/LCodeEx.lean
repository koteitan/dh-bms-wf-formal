/-
  Part III, §10: Lemma 10.5(2) — a code for the constructible hierarchy up to `ξ` exists inside
  an admissible `L θ` — and the consequence that every admissible ordinal is *good*.
-/
import Bm4.SetTheory.Good
import Bm4.SetTheory.BaseOK
import Bm4.SetTheory.Recursion

universe u

namespace BM4.ST

open Fm

/-! ### The function computed by the recursion -/

/-- The truth part of the stage `ζ`. -/
noncomputable def LTr (ζ : Ordinal.{u}) : ZFSet.{u} := TruthSet (L ζ)

theorem LTr_eq (ζ : Ordinal.{u}) : LTr ζ = TruthSet (L ζ) := rfl

/-- The value of the recursion at stage `ζ`: the pair `⟨L ζ, LTr ζ⟩` of the stage and its
truth part. -/
noncomputable def LFn (ζ : Ordinal.{u}) : ZFSet.{u} := ZFSet.pair (L ζ) (LTr ζ)

/-! ### Reading the stage off the graph -/

/-- The graph `g` assigns to `ξ` a pair whose first component is `A`. -/
def CFst (g ξ A : ZFSet.{u}) : Prop := ∃ z, ZFSet.pair ξ (ZFSet.pair A z) ∈ g

theorem bexFst_iff (c ξ : ZFSet.{u}) (P : ZFSet.{u} → Prop) :
    (∃ A, CFst c ξ A ∧ P A) ↔
      ∃ p ∈ c, ∃ q ∈ p, ∃ y ∈ q, ∃ q' ∈ y, ∃ A ∈ q', CFst c ξ A ∧ P A := by
  constructor
  · rintro ⟨A, ⟨z, hz⟩, hP⟩
    exact ⟨_, hz, _, upair_mem_pair _ _, _, mem_upair_right _ _, _, upair_mem_pair _ _,
      A, mem_upair_left _ _, ⟨z, hz⟩, hP⟩
  · rintro ⟨p, -, q, -, y, -, q', -, A, -, hA, hP⟩
    exact ⟨A, hA, hP⟩

theorem delta0_cfst (c ξ A : ℕ) :
    Delta0Def {c, ξ, A} (fun _ v => CFst (v c) (v ξ) (v A)) := by
  set n := c + ξ + A + 1 with hn
  -- p := n, q := n+1, y := n+2, q' := n+3, z := n+4
  have h0 := (delta0_isKPair n ξ (n + 2) (by omega) (by omega)).and
    (delta0_isKPair (n + 2) A (n + 4) (by omega) (by omega))
  have h1 := h0.bex (n + 4) (n + 3) (by omega)
  have h2 := h1.bex (n + 3) (n + 2) (by omega)
  have h3 := h2.bex (n + 2) (n + 1) (by omega)
  have h4 := h3.bex (n + 1) n (by omega)
  have h5 := h4.bex n c (by omega)
  refine (h5.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · rintro ⟨p, hp, q, -, y, -, q', -, z, -, rfl, rfl⟩
      exact ⟨z, hp⟩
    · rintro ⟨z, hz⟩
      exact ⟨_, hz, _, upair_mem_pair _ _, _, mem_upair_right _ _, _, upair_mem_pair _ _,
        z, mem_upair_right _ _, rfl, rfl⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-! ### The step relation -/

/-- The clause determining the stage `A` at `ζ` from the graph `g` of the values below `ζ`. -/
def AStep (h w ζ g A U₂ T₂ : ZFSet.{u}) : Prop :=
  (∃ η ∈ ζ, ζ = insert η η ∧
      ∃ A₀, CFst g η A₀ ∧ SatCode h w A₀ U₂ T₂ ∧ IsDefPow h w U₂ A₀ T₂ A) ∨
    ((∀ η ∈ ζ, ζ ≠ insert η η) ∧
      ((∀ x ∈ A, ∃ η ∈ ζ, ∃ A₀, CFst g η A₀ ∧ x ∈ A₀) ∧
        (∀ η ∈ ζ, ∃ A₀, CFst g η A₀ ∧ A₀ ⊆ A)))

/-- The step relation of the recursion: the value `y` at `ζ` is the pair `⟨A, T⟩` with `A`
determined by `AStep` and `T` the truth part of a satisfaction code for `A`. -/
def LStep (h w ζ g y U₁ U₂ T₂ : ZFSet.{u}) : Prop :=
  ∃ A T, y = ZFSet.pair A T ∧ SatCode h w A U₁ T ∧ AStep h w ζ g A U₂ T₂

theorem aStep_iff_bounded (h w ζ g A U₂ T₂ : ZFSet.{u}) :
    AStep h w ζ g A U₂ T₂ ↔
      ((∃ η ∈ ζ, ζ = insert η η ∧
          ∃ p ∈ g, ∃ q ∈ p, ∃ y ∈ q, ∃ q' ∈ y, ∃ A₀ ∈ q',
            CFst g η A₀ ∧ SatCode h w A₀ U₂ T₂ ∧ IsDefPow h w U₂ A₀ T₂ A) ∨
        ((∀ η ∈ ζ, ζ ≠ insert η η) ∧
          ((∀ x ∈ A, ∃ η ∈ ζ, ∃ p ∈ g, ∃ q ∈ p, ∃ y ∈ q, ∃ q' ∈ y, ∃ A₀ ∈ q',
              CFst g η A₀ ∧ x ∈ A₀) ∧
            (∀ η ∈ ζ, ∃ p ∈ g, ∃ q ∈ p, ∃ y ∈ q, ∃ q' ∈ y, ∃ A₀ ∈ q',
              CFst g η A₀ ∧ A₀ ⊆ A)))) := by
  unfold AStep
  refine or_congr (exists_congr fun η => and_congr_right fun _ => and_congr_right fun _ =>
    bexFst_iff g η _) ?_
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · exact forall_congr' fun x => imp_congr_right fun _ => exists_congr fun η =>
      and_congr_right fun _ => bexFst_iff g η _
  · exact forall_congr' fun η => imp_congr_right fun _ => bexFst_iff g η _

theorem lStep_iff_bounded (h w ζ g y U₁ U₂ T₂ : ZFSet.{u}) :
    LStep h w ζ g y U₁ U₂ T₂ ↔
      ∃ q ∈ y, ∃ A ∈ q, ∃ q' ∈ y, ∃ T ∈ q',
        y = ZFSet.pair A T ∧ (SatCode h w A U₁ T ∧ AStep h w ζ g A U₂ T₂) := by
  constructor
  · rintro ⟨A, T, rfl, hbody⟩
    exact ⟨{A}, singleton_mem_pair _ _, A, ZFSet.mem_singleton.mpr rfl,
      {A, T}, upair_mem_pair _ _, T, mem_upair_right _ _, rfl, hbody⟩
  · rintro ⟨q, -, A, -, q', -, T, -, rfl, hbody⟩
    exact ⟨A, T, rfl, hbody⟩

/-! ### Δ₀-definability of the step relation

Variables: `0 = ζ`, `1 = g`, `2 = y`, `3 = h`, `4 = w`, and the witness block
`5 = U₁`, `6 = U₂`, `7 = T₂`. -/

theorem delta0_aStep :
    Delta0Def.{u} {0, 1, 3, 4, 6, 7, 10}
      (fun _ v => AStep (v 3) (v 4) (v 0) (v 1) (v 10) (v 6) (v 7)) := by
  -- η := 12, p := 13, q := 14, y := 15, q' := 16, A₀ := 17, x := 18
  have e2 := (delta0_cfst 1 12 17).and
    ((delta0_satCode 3 4 17 6 7 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)).and
      (delta0_isDefPow 3 4 6 17 7 10 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)))
  have e3 := e2.bex 17 16 (by omega)
  have e4 := e3.bex 16 15 (by omega)
  have e5 := e4.bex 15 14 (by omega)
  have e6 := e5.bex 14 13 (by omega)
  have e7 := e6.bex 13 1 (by omega)
  have e9 := (delta0_isSucc 0 12 (by omega)).and e7
  have e10 := e9.bex 12 0 (by omega)
  have l1 := ((delta0_isSucc 0 12 (by omega)).not).ball 12 0 (by omega)
  have m1 := (delta0_cfst 1 12 17).and (Delta0Def.mem 18 17)
  have m2 := m1.bex 17 16 (by omega)
  have m3 := m2.bex 16 15 (by omega)
  have m4 := m3.bex 15 14 (by omega)
  have m5 := m4.bex 14 13 (by omega)
  have m6 := m5.bex 13 1 (by omega)
  have m7 := m6.bex 12 0 (by omega)
  have l2 := m7.ball 18 10 (by omega)
  have n1 := (delta0_cfst 1 12 17).and (delta0_subset 17 10 (by omega))
  have n2 := n1.bex 17 16 (by omega)
  have n3 := n2.bex 16 15 (by omega)
  have n4 := n3.bex 15 14 (by omega)
  have n5 := n4.bex 14 13 (by omega)
  have n6 := n5.bex 13 1 (by omega)
  have l3 := n6.ball 12 0 (by omega)
  have lim := l1.and (l2.and l3)
  refine ((e10.or lim).congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    exact (aStep_iff_bounded (v 3) (v 4) (v 0) (v 1) (v 10) (v 6) (v 7)).symm
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase] at hk ⊢
    omega

theorem delta0_lStep :
    Delta0Def.{u} {0, 1, 2, 3, 4, 5, 6, 7}
      (fun _ v => LStep (v 3) (v 4) (v 0) (v 1) (v 2) (v 5) (v 6) (v 7)) := by
  -- A := 10, T := 11, q := 19, q' := 20
  have b2 := (delta0_satCode 3 4 10 5 11 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)).and delta0_aStep
  have core := (delta0_isKPair 2 10 11 (by omega) (by omega)).and b2
  have c1 := core.bex 11 20 (by omega)
  have c2 := c1.bex 20 2 (by omega)
  have c3 := c2.bex 10 19 (by omega)
  have c4 := c3.bex 19 2 (by omega)
  refine (c4.congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    exact (lStep_iff_bounded (v 3) (v 4) (v 0) (v 1) (v 2) (v 5) (v 6) (v 7)).symm
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase] at hk ⊢
    omega

/-! ### Satisfaction codes for the truth set inside `L θ` -/

/-- Lemma 10.5(1) with the truth part pinned down to `TruthSet A`. -/
theorem satCode_truthSet_in_L {θ : Ordinal.{u}} (hθ : IsAdmissible θ) {A : ZFSet.{u}}
    (hA : A ∈ L θ) :
    ∃ U ∈ L θ, SatCode (L Ordinal.omega0) ωZ A U (TruthSet A) := by
  have hlim := hθ.isSuccLimit
  have hT : TruthSet A ∈ L θ := truthSet_mem_L hθ hA
  have hω : ωZ.{u} ∈ L θ := hθ.omega_mem
  -- Lemma 10.4(3) applied to `{A, ω, T}`, as in the paper's proof of Lemma 10.5(1)
  have hXL : (insert A (insert ωZ.{u} (insert (TruthSet A) (∅ : ZFSet.{u})))) ∈ L θ :=
    insert_mem_L_of_limit hlim hA
      (insert_mem_L_of_limit hlim hω
        (insert_mem_L_of_limit hlim hT (empty_mem_L_of_limit hlim)))
  obtain ⟨U, hUL, hXU, hUtrans, hUpucl⟩ := exists_puCl_superset hθ hXL
  exact ⟨U, hUL, satCode_truthSet hUtrans (hXU (by simp)) (hXU (by simp)) (hXU (by simp)) hUpucl⟩

theorem LTr_mem_L {θ : Ordinal.{u}} (hθ : IsAdmissible θ) {ζ : Ordinal.{u}} (hζ : ζ < θ) :
    LTr ζ ∈ L θ := truthSet_mem_L hθ (L_mem_L hζ)

theorem LFn_mem_L {θ : Ordinal.{u}} (hθ : IsAdmissible θ) {ζ : Ordinal.{u}} (hζ : ζ < θ) :
    LFn ζ ∈ L θ :=
  kpair_mem_L_of_limit hθ.isSuccLimit (L_mem_L hζ) (LTr_mem_L hθ hζ)

/-- A satisfaction code for `L ζ` (`ζ < θ`) with truth part `LTr ζ`, inside `L θ`. -/
theorem satCode_LTr {θ : Ordinal.{u}} (hθ : IsAdmissible θ) {ζ : Ordinal.{u}} (hζ : ζ < θ) :
    ∃ U ∈ L θ, SatCode (L Ordinal.omega0) ωZ (L ζ) U (LTr ζ) :=
  satCode_truthSet_in_L hθ (L_mem_L hζ)

/-- Any satisfaction code for `L ζ` has truth part `LTr ζ`. -/
theorem satCode_LTr_unique {θ : Ordinal.{u}} (hθ : IsAdmissible θ) {ζ : Ordinal.{u}} (hζ : ζ < θ)
    {U T : ZFSet.{u}} (hc : SatCode (L Ordinal.omega0) ωZ (L ζ) U T) : T = LTr ζ := by
  obtain ⟨U', -, hc'⟩ := satCode_LTr hθ hζ
  exact satCode_unique hc hc'

/-! ### Values of the graph -/

theorem cfst_graphBelow_LFn {ζ a : Ordinal.{u}} {A₀ : ZFSet.{u}}
    (h : CFst (graphBelow LFn ζ) a.toZFSet A₀) : a < ζ ∧ A₀ = L a := by
  obtain ⟨z, hz⟩ := h
  rw [pair_mem_graphBelow_iff] at hz
  exact ⟨hz.1, (ZFSet.pair_injective hz.2).1⟩

theorem cfst_graphBelow_LFn_of_lt {ζ a : Ordinal.{u}} (h : a < ζ) :
    CFst (graphBelow LFn ζ) a.toZFSet (L a) :=
  ⟨LTr a, pair_mem_graphBelow_iff.mpr ⟨h, rfl⟩⟩

/-! ### The step relation holds, and pins the value down -/

theorem lStep_holds {θ : Ordinal.{u}} (hθ : IsAdmissible θ) {ζ : Ordinal.{u}}
    (hζ : ζ < θ) : ∃ U₁ ∈ L θ, ∃ U₂ ∈ L θ, ∃ T₂ ∈ L θ,
      LStep (L Ordinal.omega0) ωZ ζ.toZFSet (graphBelow LFn ζ) (LFn ζ) U₁ U₂ T₂ := by
  have hlim := hθ.isSuccLimit
  have hE : (∅ : ZFSet.{u}) ∈ L θ := empty_mem_L_of_limit hlim
  obtain ⟨U₁, hU₁, hc₁⟩ := satCode_LTr hθ hζ
  rcases Ordinal.zero_or_succ_or_isSuccLimit ζ with rfl | ⟨η, hη⟩ | hlimζ
  · -- `ζ = 0`
    refine ⟨U₁, hU₁, ∅, hE, ∅, hE, L (0 : Ordinal.{u}), LTr (0 : Ordinal.{u}), rfl, hc₁,
      Or.inr ⟨?_, ?_, ?_⟩⟩
    · intro η hη
      rw [Ordinal.toZFSet_zero] at hη
      exact absurd hη (ZFSet.notMem_empty _)
    · intro x hx
      rw [L_zero] at hx
      exact absurd hx (ZFSet.notMem_empty _)
    · intro η hη
      rw [Ordinal.toZFSet_zero] at hη
      exact absurd hη (ZFSet.notMem_empty _)
  · -- `ζ = η + 1`
    subst hη
    have hηlt : η < Order.succ η := Order.lt_succ_of_not_isMax (not_isMax η)
    have hηθ : η < θ := hηlt.trans hζ
    have hsucc : (Order.succ η).toZFSet = insert η.toZFSet η.toZFSet := by
      rw [Order.succ_eq_add_one, Ordinal.toZFSet_add_one]
    have hmemη : η.toZFSet ∈ (Order.succ η).toZFSet :=
      Ordinal.toZFSet_mem_toZFSet_iff.mpr hηlt
    obtain ⟨U₂, hU₂, hc₂⟩ := satCode_LTr hθ hηθ
    refine ⟨U₁, hU₁, U₂, hU₂, LTr η, LTr_mem_L hθ hηθ, L (Order.succ η), LTr (Order.succ η),
      rfl, hc₁, ?_⟩
    refine Or.inl ⟨η.toZFSet, hmemη, hsucc, L η, cfst_graphBelow_LFn_of_lt hηlt, hc₂, ?_⟩
    rw [isDefPow_iff hc₂, Order.succ_eq_add_one, L_succ]
  · -- `ζ` limit
    refine ⟨U₁, hU₁, ∅, hE, ∅, hE, L ζ, LTr ζ, rfl, hc₁, Or.inr ⟨?_, ?_, ?_⟩⟩
    · intro x hx heq
      obtain ⟨a, ha, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
      rw [← Ordinal.toZFSet_add_one] at heq
      have he := Ordinal.toZFSet_injective heq
      exact absurd (hlimζ.add_one_lt ha) (by rw [he]; exact lt_irrefl _)
    · intro x hx
      obtain ⟨a, ha, hxa⟩ := (mem_L_limit hlimζ).mp hx
      exact ⟨a.toZFSet, Ordinal.toZFSet_mem_toZFSet_iff.mpr ha, L a,
        cfst_graphBelow_LFn_of_lt ha, hxa⟩
    · intro η hη
      obtain ⟨a, ha, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hη
      exact ⟨L a, cfst_graphBelow_LFn_of_lt ha, L_mono ha.le⟩

theorem lStep_unique {θ : Ordinal.{u}} (hθ : IsAdmissible θ) {ζ : Ordinal.{u}}
    (hζ : ζ < θ) {y U₁ U₂ T₂ : ZFSet.{u}}
    (h : LStep (L Ordinal.omega0) ωZ ζ.toZFSet (graphBelow LFn ζ) y U₁ U₂ T₂) :
    y = LFn ζ := by
  obtain ⟨A, T, rfl, hc, hA⟩ := h
  have hAL : A = L ζ := by
    rcases Ordinal.zero_or_succ_or_isSuccLimit ζ with rfl | ⟨η, hη⟩ | hlimζ
    · rcases hA with ⟨η', hη'mem, -, -⟩ | ⟨-, hsub1, -⟩
      · rw [Ordinal.toZFSet_zero] at hη'mem
        exact absurd hη'mem (ZFSet.notMem_empty _)
      · rw [L_zero]
        ext x
        simp only [ZFSet.notMem_empty, iff_false]
        intro hx
        obtain ⟨η', hη'mem, -, -, -⟩ := hsub1 x hx
        rw [Ordinal.toZFSet_zero] at hη'mem
        exact absurd hη'mem (ZFSet.notMem_empty _)
    · subst hη
      have hηlt : η < Order.succ η := Order.lt_succ_of_not_isMax (not_isMax η)
      have hsucc : (Order.succ η).toZFSet = insert η.toZFSet η.toZFSet := by
        rw [Order.succ_eq_add_one, Ordinal.toZFSet_add_one]
      rcases hA with ⟨η', hη'mem, hη'eq, A₀, hcf, hsc, hdc⟩ | ⟨hno, -, -⟩
      · obtain ⟨a, ha, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hη'mem
        have haη : a = η := by
          have hee : (Order.succ a).toZFSet = (Order.succ η).toZFSet := by
            rw [Order.succ_eq_add_one, Ordinal.toZFSet_add_one, ← hη'eq]
          exact Order.succ_injective (Ordinal.toZFSet_injective hee)
        subst haη
        obtain ⟨-, rfl⟩ := cfst_graphBelow_LFn hcf
        rw [isDefPow_iff hsc] at hdc
        rw [hdc, Order.succ_eq_add_one, L_succ]
      · exact absurd hsucc (hno η.toZFSet (Ordinal.toZFSet_mem_toZFSet_iff.mpr hηlt))
    · rcases hA with ⟨η', hη'mem, hη'eq, -⟩ | ⟨-, hsub1, hsub2⟩
      · obtain ⟨a, ha, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hη'mem
        rw [← Ordinal.toZFSet_add_one] at hη'eq
        have he := Ordinal.toZFSet_injective hη'eq
        exact absurd (hlimζ.add_one_lt ha) (by rw [he]; exact lt_irrefl _)
      · ext x
        constructor
        · intro hx
          obtain ⟨η', hη'mem, A₀, hcf, hxA⟩ := hsub1 x hx
          obtain ⟨a, ha, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hη'mem
          obtain ⟨-, rfl⟩ := cfst_graphBelow_LFn hcf
          exact (mem_L_limit hlimζ).mpr ⟨a, ha, hxA⟩
        · intro hx
          obtain ⟨a, ha, hxa⟩ := (mem_L_limit hlimζ).mp hx
          obtain ⟨A₀, hcf, hsub⟩ := hsub2 a.toZFSet (Ordinal.toZFSet_mem_toZFSet_iff.mpr ha)
          obtain ⟨-, rfl⟩ := cfst_graphBelow_LFn hcf
          exact hsub hxa
  subst hAL
  rw [satCode_LTr_unique hθ hζ hc]
  rfl

/-! ### The graph of the recursion lies in `L θ` -/

/-- The parameter valuation of the step relation. -/
noncomputable def stepVal (k : ℕ) : ZFSet.{u} :=
  if k = 3 then L Ordinal.omega0 else if k = 4 then ωZ else ∅

theorem graphBelow_LFn_mem_L {θ : Ordinal.{u}} (hθ : IsAdmissible θ) :
    ∀ ζ < θ, graphBelow LFn ζ ∈ L θ := by
  have hlim := hθ.isSuccLimit
  refine sigma1_recursion hθ delta0_lStep [5, 6, 7] (by decide) (by decide) (by decide)
    (v := stepVal) ?_ LFn ?_ ?_
  · intro k hk hkl hk3
    have hk5 : k ≠ 5 := fun h => hkl (by simp [h])
    have hk6 : k ≠ 6 := fun h => hkl (by simp [h])
    have hk7 : k ≠ 7 := fun h => hkl (by simp [h])
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    have hk' : k = 3 ∨ k = 4 := by omega
    rcases hk' with rfl | rfl
    · simpa [stepVal] using L_mem_L hθ.omega_lt
    · simpa [stepVal] using hθ.omega_mem
  · intro ζ hζ _
    refine ⟨LFn_mem_L hθ hζ, ?_⟩
    obtain ⟨U₁, hU₁, U₂, hU₂, T₂, hT₂, hs⟩ := lStep_holds hθ hζ
    refine ⟨U₁, hU₁, U₂, hU₂, T₂, hT₂, ?_⟩
    simpa [upd3, stepVal, Function.update_apply] using hs
  · intro ζ hζ _ y _ hy
    obtain ⟨a, -, b, -, c, -, hs⟩ := hy
    refine lStep_unique hθ hζ (U₁ := a) (U₂ := b) (T₂ := c) ?_
    simpa [upd3, stepVal, Function.update_apply] using hs

/-! ### Δ₀ separations that carry the parts of the code into `L θ` -/

/-- A graph whose pairs all lie in `L δ` and which a Δ₀ condition picks out of `L δ` lies in
`L θ`. -/
theorem graphBelow_mem_L_of_sep {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ) {s : Finset ℕ}
    {P : Pred.{u}} (hP : Delta0Def s P) (i : ℕ) {v : ℕ → ZFSet.{u}}
    (hv : ValD (· ∈ L θ) (s.erase i) v) {δ : Ordinal.{u}} (hδ : δ < θ)
    {F : Ordinal.{u} → ZFSet.{u}} {ζ : Ordinal.{u}}
    (hmem : ∀ a < ζ, ZFSet.pair a.toZFSet (F a) ∈ L δ)
    (hchar : ∀ p : ZFSet.{u}, P (fun _ => True) (Function.update v i p) ↔
      ∃ a < ζ, p = ZFSet.pair a.toZFSet (F a)) :
    graphBelow F ζ ∈ L θ := by
  have heq : graphBelow F ζ =
      ZFSet.sep (fun x => P (fun _ => True) (Function.update v i x)) (L δ) := by
    ext p
    rw [ZFSet.mem_sep, hchar p, mem_graphBelow]
    exact ⟨fun ⟨a, ha, he⟩ => ⟨he ▸ hmem a ha, a, ha, he⟩, fun hp => hp.2⟩
  rw [heq]
  exact sep_mem_L_of_limit hθ hP i hv (L_mem_L hδ)

/-- `p` is the stage part `⟨ζ, A⟩` of an entry `⟨ζ, ⟨A, T⟩⟩` of `g`. -/
def FstPart (g p : ZFSet.{u}) : Prop :=
  ∃ ζ A T, ZFSet.pair ζ (ZFSet.pair A T) ∈ g ∧ p = ZFSet.pair ζ A

theorem fstPart_iff_bounded (g p : ZFSet.{u}) :
    FstPart g p ↔
      ∃ q₀ ∈ p, ∃ ζ ∈ q₀, ∃ q₁ ∈ p, ∃ A ∈ q₁, p = ZFSet.pair ζ A ∧
        ∃ e ∈ g, ∃ q ∈ e, ∃ z ∈ q, ∃ r ∈ z, ∃ T ∈ r,
          z = ZFSet.pair A T ∧ e = ZFSet.pair ζ z := by
  constructor
  · rintro ⟨ζ, A, T, hg, rfl⟩
    exact ⟨_, singleton_mem_pair _ _, ζ, ZFSet.mem_singleton.mpr rfl, _, upair_mem_pair _ _,
      A, mem_upair_right _ _, rfl, _, hg, _, upair_mem_pair _ _, _, mem_upair_right _ _,
      _, upair_mem_pair _ _, T, mem_upair_right _ _, rfl, rfl⟩
  · rintro ⟨q₀, -, ζ, -, q₁, -, A, -, rfl, e, he, q, -, z, -, r, -, T, -, rfl, rfl⟩
    exact ⟨ζ, A, T, he, rfl⟩

theorem delta0_fstPart (g p : ℕ) (hgp : g ≠ p) :
    Delta0Def {g, p} (fun _ v => FstPart (v g) (v p)) := by
  set m := g + p + 1 with hm
  -- q₀ := m, ζ := m+1, q₁ := m+2, A := m+3, e := m+4, q := m+5, z := m+6, r := m+7, T := m+8
  have inner := (delta0_isKPair (m + 6) (m + 3) (m + 8) (by omega) (by omega)).and
    (delta0_isKPair (m + 4) (m + 1) (m + 6) (by omega) (by omega))
  have i1 := inner.bex (m + 8) (m + 7) (by omega)
  have i2 := i1.bex (m + 7) (m + 6) (by omega)
  have i3 := i2.bex (m + 6) (m + 5) (by omega)
  have i4 := i3.bex (m + 5) (m + 4) (by omega)
  have i5 := i4.bex (m + 4) g (by omega)
  have c0 := (delta0_isKPair p (m + 1) (m + 3) (by omega) (by omega)).and i5
  have c1 := c0.bex (m + 3) (m + 2) (by omega)
  have c2 := c1.bex (m + 2) p (by omega)
  have c3 := c2.bex (m + 1) m (by omega)
  have c4 := c3.bex m p (by omega)
  refine (c4.congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    exact (fstPart_iff_bounded (v g) (v p)).symm
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase] at hk ⊢
    omega

/-- `p` is a truth-part entry `⟨ζ, T⟩` for a stage `ζ ∈ d` of the stage function `H`. -/
def SatPart (h w U H d p : ZFSet.{u}) : Prop :=
  ∃ ζ ∈ d, ∃ A, ZFSet.pair ζ A ∈ H ∧ ∃ T, p = ZFSet.pair ζ T ∧ SatCode h w A U T

theorem satPart_iff_bounded (h w U H d p : ZFSet.{u}) :
    SatPart h w U H d p ↔
      ∃ ζ ∈ d, ∃ pH ∈ H, ∃ qH ∈ pH, ∃ A ∈ qH, ∃ q ∈ p, ∃ T ∈ q,
        pH = ZFSet.pair ζ A ∧ p = ZFSet.pair ζ T ∧ SatCode h w A U T := by
  refine exists_congr fun ζ => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨A, hA, T, rfl, hsc⟩
    exact ⟨_, hA, _, upair_mem_pair _ _, A, mem_upair_right _ _,
      _, upair_mem_pair _ _, T, mem_upair_right _ _, rfl, rfl, hsc⟩
  · rintro ⟨pH, hpH, qH, -, A, -, q, -, T, -, rfl, rfl, hsc⟩
    exact ⟨A, hpH, T, rfl, hsc⟩

set_option linter.unusedVariables false in
theorem delta0_satPart (h w U H d p : ℕ) (hhw : h ≠ w) (hhU : h ≠ U) (hhH : h ≠ H)
    (hhd : h ≠ d) (hhp : h ≠ p) (hwU : w ≠ U) (hwH : w ≠ H) (hwd : w ≠ d) (hwp : w ≠ p)
    (hUH : U ≠ H) (hUd : U ≠ d) (hUp : U ≠ p) (hHd : H ≠ d) (hHp : H ≠ p) (hdp : d ≠ p) :
    Delta0Def {h, w, U, H, d, p} (fun _ v => SatPart (v h) (v w) (v U) (v H) (v d) (v p)) := by
  set m := h + w + U + H + d + p + 1 with hm
  -- ζ := m, pH := m+1, qH := m+2, A := m+3, q := m+4, T := m+5
  have core := (delta0_isKPair (m + 1) m (m + 3) (by omega) (by omega)).and
    ((delta0_isKPair p m (m + 5) (by omega) (by omega)).and
      (delta0_satCode h w (m + 3) U (m + 5) hhw (by omega) hhU (by omega) (by omega) hwU
        (by omega) (by omega) (by omega) (by omega)))
  have c1 := core.bex (m + 5) (m + 4) (by omega)
  have c2 := c1.bex (m + 4) p (by omega)
  have c3 := c2.bex (m + 3) (m + 2) (by omega)
  have c4 := c3.bex (m + 2) (m + 1) (by omega)
  have c5 := c4.bex (m + 1) H (by omega)
  have c6 := c5.bex m d (by omega)
  refine (c6.congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    exact (satPart_iff_bounded (v h) (v w) (v U) (v H) (v d) (v p)).symm
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase] at hk ⊢
    omega

/-- `p` is an enumeration entry `⟨ζ, D(ζ)⟩` for a stage `ζ ∈ d`. -/
def DefPart (h w U H S d p : ZFSet.{u}) : Prop :=
  ∃ ζ ∈ d, ∃ A, ZFSet.pair ζ A ∈ H ∧ ∃ T, ZFSet.pair ζ T ∈ S ∧
    ∃ Dz, p = ZFSet.pair ζ Dz ∧ IsDefEnum h w U A T Dz

theorem defPart_iff_bounded (h w U H S d p : ZFSet.{u}) :
    DefPart h w U H S d p ↔
      ∃ ζ ∈ d, ∃ pH ∈ H, ∃ qH ∈ pH, ∃ A ∈ qH, ∃ pS ∈ S, ∃ qS ∈ pS, ∃ T ∈ qS,
        ∃ q ∈ p, ∃ Dz ∈ q, pH = ZFSet.pair ζ A ∧ pS = ZFSet.pair ζ T ∧
          p = ZFSet.pair ζ Dz ∧ IsDefEnum h w U A T Dz := by
  refine exists_congr fun ζ => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨A, hA, T, hT, Dz, rfl, hde⟩
    exact ⟨_, hA, _, upair_mem_pair _ _, A, mem_upair_right _ _,
      _, hT, _, upair_mem_pair _ _, T, mem_upair_right _ _,
      _, upair_mem_pair _ _, Dz, mem_upair_right _ _, rfl, rfl, rfl, hde⟩
  · rintro ⟨pH, hpH, qH, -, A, -, pS, hpS, qS, -, T, -, q, -, Dz, -, rfl, rfl, rfl, hde⟩
    exact ⟨A, hpH, T, hpS, Dz, rfl, hde⟩

set_option linter.unusedVariables false in
theorem delta0_defPart (h w U H S d p : ℕ) (hhw : h ≠ w) (hhU : h ≠ U) (hhH : h ≠ H)
    (hhS : h ≠ S) (hhd : h ≠ d) (hhp : h ≠ p) (hwU : w ≠ U) (hwH : w ≠ H) (hwS : w ≠ S)
    (hwd : w ≠ d) (hwp : w ≠ p) (hUH : U ≠ H) (hUS : U ≠ S) (hUd : U ≠ d) (hUp : U ≠ p)
    (hHS : H ≠ S) (hHd : H ≠ d) (hHp : H ≠ p) (hSd : S ≠ d) (hSp : S ≠ p) (hdp : d ≠ p) :
    Delta0Def {h, w, U, H, S, d, p}
      (fun _ v => DefPart (v h) (v w) (v U) (v H) (v S) (v d) (v p)) := by
  set m := h + w + U + H + S + d + p + 1 with hm
  -- ζ := m, pH := m+1, qH := m+2, A := m+3, pS := m+4, qS := m+5, T := m+6,
  -- q := m+7, Dz := m+8
  have core := (delta0_isKPair (m + 1) m (m + 3) (by omega) (by omega)).and
    ((delta0_isKPair (m + 4) m (m + 6) (by omega) (by omega)).and
      ((delta0_isKPair p m (m + 8) (by omega) (by omega)).and
        (delta0_isDefEnum h w U (m + 3) (m + 6) (m + 8) hhw hhU (by omega) (by omega)
          (by omega) hwU (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega))))
  have c1 := core.bex (m + 8) (m + 7) (by omega)
  have c2 := c1.bex (m + 7) p (by omega)
  have c3 := c2.bex (m + 6) (m + 5) (by omega)
  have c4 := c3.bex (m + 5) (m + 4) (by omega)
  have c5 := c4.bex (m + 4) S (by omega)
  have c6 := c5.bex (m + 3) (m + 2) (by omega)
  have c7 := c6.bex (m + 2) (m + 1) (by omega)
  have c8 := c7.bex (m + 1) H (by omega)
  have c9 := c8.bex m d (by omega)
  refine (c9.congr ?_).mono ?_
  · intro Dd v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    exact (defPart_iff_bounded (v h) (v w) (v U) (v H) (v S) (v d) (v p)).symm
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase] at hk ⊢
    omega

/-! ### Lemma 10.5(2) -/

theorem kpair_mem_of_trans {X a b : ZFSet.{u}} (hX : X.IsTransitive)
    (h : ZFSet.pair a b ∈ X) : a ∈ X ∧ b ∈ X := by
  have h1 : ({a, b} : ZFSet.{u}) ∈ X := hX.subset_of_mem h (upair_mem_pair a b)
  exact ⟨hX.subset_of_mem h1 (mem_upair_left a b), hX.subset_of_mem h1 (mem_upair_right a b)⟩

theorem ordinal_zero_le (a : Ordinal.{u}) : (0 : Ordinal.{u}) ≤ a := by
  rw [← Ordinal.bot_eq_zero]; exact bot_le

theorem ordinal_lt_add_one (a : Ordinal.{u}) : a < a + 1 := Order.lt_add_one_iff.mpr le_rfl

theorem puCl_L {δ : Ordinal.{u}} (hδ : Order.IsSuccLimit δ) : PUCl (L δ) :=
  fun _ hx _ hy => ⟨pair_mem_L_of_limit hδ hx hy, sUnion_mem_L_of_limit hδ hx⟩

/-- The limit clause (9.3) holds for the stage function `graphBelow L (ξ + 1)`. -/
theorem limClause_graphBelow_L {ξ : Ordinal.{u}} :
    ∀ a : Ordinal.{u}, a ≤ ξ → LimClause (graphBelow L (ξ + 1)) a.toZFSet := by
  intro a haξ hne hclosed Hl hHl
  have ha0 : a ≠ 0 := fun h => hne (by rw [h, Ordinal.toZFSet_zero])
  have halim : Order.IsSuccLimit a := by
    rw [Ordinal.isSuccLimit_iff]
    refine ⟨ha0, ?_⟩
    rw [Order.isSuccPrelimit_iff_succ_lt]
    intro b hb
    have hmem := hclosed b.toZFSet (Ordinal.toZFSet_mem_toZFSet_iff.mpr hb)
    rw [← Ordinal.toZFSet_add_one] at hmem
    rw [Order.succ_eq_add_one]
    exact Ordinal.toZFSet_mem_toZFSet_iff.mp hmem
  obtain ⟨-, rfl⟩ := pair_mem_graphBelow_iff.mp hHl
  constructor
  · intro x hx
    obtain ⟨b, hb, hxb⟩ := (mem_L_limit halim).mp hx
    exact ⟨b.toZFSet, Ordinal.toZFSet_mem_toZFSet_iff.mpr hb, L b,
      pair_mem_graphBelow_iff.mpr
        ⟨(hb.trans_le haξ).trans (ordinal_lt_add_one ξ), rfl⟩, hxb⟩
  · intro ζ hζ Hz hHz
    obtain ⟨b, hb, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hζ
    obtain ⟨-, rfl⟩ := pair_mem_graphBelow_iff.mp hHz
    exact L_mono hb.le


/-- **Lemma 10.5(2)**: a code for the constructible hierarchy up to `ξ` lies inside `L θ`. -/
theorem lcode_exists_in_L {θ : Ordinal.{u}} (hθ : IsAdmissible θ) {ξ : Ordinal.{u}} (hξ : ξ < θ) :
    ∃ M ∈ L θ, ∃ c ∈ L θ, LCode (L Ordinal.omega0) ωZ ξ.toZFSet M c := by
  have hlim := hθ.isSuccLimit
  have hξ1 : ξ + 1 < θ := hlim.add_one_lt hξ
  -- the graph of the recursion bounds every stage and every truth part at once
  have hg : graphBelow LFn (ξ + 1) ∈ L θ := graphBelow_LFn_mem_L hθ _ hξ1
  obtain ⟨γ₀, hγ₀, hg'⟩ := (mem_L_limit hlim).mp hg
  obtain ⟨δ, hδlim, hδge, hδlt⟩ := exists_limit_between hθ
    (show max γ₀ (max (ξ + 1) (Ordinal.omega0.{u} + 1)) < θ from
      max_lt hγ₀ (max_lt hξ1 (hlim.add_one_lt hθ.omega_lt)))
  have hgδ : graphBelow LFn (ξ + 1) ∈ L δ := L_mono ((le_max_left _ _).trans hδge) hg'
  have hξδ : ξ < δ := lt_of_lt_of_le (ordinal_lt_add_one ξ)
    (((le_max_left _ _).trans (le_max_right _ _)).trans hδge)
  have hωδ : Ordinal.omega0.{u} < δ := lt_of_lt_of_le (ordinal_lt_add_one _)
    (((le_max_right _ _).trans (le_max_right _ _)).trans hδge)
  have hωZδ : ωZ.{u} ∈ L δ := (toZFSet_mem_L_iff δ Ordinal.omega0).mpr hωδ
  have hstage : ∀ a : Ordinal.{u}, a < ξ + 1 →
      a.toZFSet ∈ L δ ∧ L a ∈ L δ ∧ LTr a ∈ L δ := by
    intro a ha
    have hmem : ZFSet.pair a.toZFSet (LFn a) ∈ graphBelow LFn (ξ + 1) :=
      mem_graphBelow.mpr ⟨a, ha, rfl⟩
    obtain ⟨h1, h2⟩ := kpair_mem_of_trans (L_transitive δ)
      ((L_transitive δ).subset_of_mem hgδ hmem)
    rw [LFn] at h2
    obtain ⟨h3, h4⟩ := kpair_mem_of_trans (L_transitive δ) h2
    exact ⟨h1, h3, h4⟩
  have hsat : ∀ a : Ordinal.{u}, a < ξ + 1 →
      SatCode (L Ordinal.omega0) ωZ (L a) (L δ) (LTr a) := fun a ha =>
    satCode_truthSet (L_transitive δ) (hstage a ha).2.1 (hstage a ha).2.2 hωZδ (puCl_L hδlim)
  -- the stage function `H`
  have hHmem : ∀ a : Ordinal.{u}, a < ξ + 1 → ZFSet.pair a.toZFSet (L a) ∈ L δ := fun a ha =>
    kpair_mem_L_of_limit hδlim (hstage a ha).1 (hstage a ha).2.1
  have hHL : graphBelow L (ξ + 1) ∈ L θ := by
    refine graphBelow_mem_L_of_sep hlim (delta0_fstPart 0 1 (by omega)) 1
      (v := fun _ => graphBelow LFn (ξ + 1)) (fun i _ => hg) hδlt hHmem ?_
    intro p
    show FstPart (graphBelow LFn (ξ + 1)) p ↔ _
    constructor
    · rintro ⟨ζ, A, T, hmem, rfl⟩
      obtain ⟨a, ha, he⟩ := mem_graphBelow.mp hmem
      obtain ⟨rfl, hAT⟩ := ZFSet.pair_injective he
      rw [LFn] at hAT
      obtain ⟨rfl, -⟩ := ZFSet.pair_injective hAT
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.toZFSet, L a, LTr a, mem_graphBelow.mpr ⟨a, ha, rfl⟩, rfl⟩
  -- the truth-part function `S`
  have hSmem : ∀ a : Ordinal.{u}, a < ξ → ZFSet.pair a.toZFSet (LTr a) ∈ L δ := fun a ha =>
    kpair_mem_L_of_limit hδlim (hstage a (ha.trans (ordinal_lt_add_one ξ))).1
      (hstage a (ha.trans (ordinal_lt_add_one ξ))).2.2
  have hSL : graphBelow LTr ξ ∈ L θ := by
    refine graphBelow_mem_L_of_sep hlim
      (delta0_satPart 0 1 2 3 4 5 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)) 5
      (v := fun k => if k = 0 then L Ordinal.omega0 else if k = 1 then ωZ
        else if k = 2 then L δ else if k = 3 then graphBelow L (ξ + 1) else ξ.toZFSet)
      ?_ hδlt hSmem ?_
    · intro i hi
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hi
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl
      · simpa using L_mem_L hθ.omega_lt
      · simpa using hθ.omega_mem
      · simpa using L_mem_L hδlt
      · simpa using hHL
      · simpa using (toZFSet_mem_L_iff θ ξ).mpr hξ
    · intro p
      show SatPart (L Ordinal.omega0) ωZ (L δ) (graphBelow L (ξ + 1)) ξ.toZFSet p ↔ _
      constructor
      · rintro ⟨ζ, hζ, A, hA, T, rfl, hsc⟩
        obtain ⟨a, ha, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hζ
        obtain ⟨-, rfl⟩ := pair_mem_graphBelow_iff.mp hA
        exact ⟨a, ha, by rw [satCode_unique hsc (hsat a (ha.trans (ordinal_lt_add_one ξ)))]⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a.toZFSet, Ordinal.toZFSet_mem_toZFSet_iff.mpr ha, L a,
          pair_mem_graphBelow_iff.mpr ⟨ha.trans (ordinal_lt_add_one ξ), rfl⟩,
          LTr a, rfl, hsat a (ha.trans (ordinal_lt_add_one ξ))⟩
  -- the enumeration function `D`
  have hDsub : ∀ a : Ordinal.{u}, a < ξ → defEnum (L a) (LTr a) ⊆ L δ := by
    intro a ha p hp
    have ha1 : a < ξ + 1 := ha.trans (ordinal_lt_add_one ξ)
    obtain ⟨e, he, a', hinp, rfl⟩ := mem_defEnum.mp hp
    have heδ : e ∈ L δ := L_mono hωδ.le he
    have ha'δ : a' ∈ L δ := seq_mem_of_puCl (L_transitive δ) (hstage a ha1).2.1 hωZδ
      (puCl_L hδlim) hinp.2.1
    have hbits := (isDefEnum_defEnum (hsat a ha1)).2.2 e a' _
      (mem_defEnum.mpr ⟨e, he, a', hinp, rfl⟩)
    have hbδ : defBit (L a) (LTr a) e a' ∈ L δ := by
      have hmemDef := definableOver_of_defInp (hsat a ha1) hinp hbits.1 hbits.2
      rw [← L_succ] at hmemDef
      exact L_mono (hδlim.add_one_lt (ha.trans hξδ)).le hmemDef
    exact kpair_mem_L_of_limit hδlim (kpair_mem_L_of_limit hδlim heδ ha'δ) hbδ
  obtain ⟨δ₂, hδ₂lim, hδ₂ge, hδ₂lt⟩ := exists_limit_between hθ
    (show δ + 1 < θ from hlim.add_one_lt hδlt)
  have hδδ₂ : δ < δ₂ := lt_of_lt_of_le (ordinal_lt_add_one δ) hδ₂ge
  have hDmem : ∀ a : Ordinal.{u}, a < ξ →
      ZFSet.pair a.toZFSet (defEnum (L a) (LTr a)) ∈ L δ₂ := by
    intro a ha
    have ha1 : a < ξ + 1 := ha.trans (ordinal_lt_add_one ξ)
    have heq : defEnum (L a) (LTr a) =
        ZFSet.sep (fun x => IsDefEntry (L Ordinal.omega0) ωZ (L δ) (L a) (LTr a) x) (L δ) := by
      ext p
      rw [ZFSet.mem_sep]
      exact ⟨fun hp => ⟨hDsub a ha hp, (mem_defEnum_iff_isDefEntry (hsat a ha1)).mp hp⟩,
        fun hp => (mem_defEnum_iff_isDefEntry (hsat a ha1)).mpr hp.2⟩
    have hDL : defEnum (L a) (LTr a) ∈ L δ₂ := by
      rw [heq]
      refine sep_mem_L_of_limit hδ₂lim
        (delta0_isDefEntry 0 1 2 3 4 5 (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)) 5
        (v := fun k => if k = 0 then L Ordinal.omega0 else if k = 1 then ωZ
          else if k = 2 then L δ else if k = 3 then L a else LTr a) ?_ (L_mem_L hδδ₂)
      intro i hi
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hi
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl
      · simpa using L_mem_L (hωδ.trans hδδ₂)
      · simpa using L_mono hδδ₂.le hωZδ
      · simpa using L_mem_L hδδ₂
      · simpa using L_mono hδδ₂.le (hstage a ha1).2.1
      · simpa using L_mono hδδ₂.le (hstage a ha1).2.2
    exact kpair_mem_L_of_limit hδ₂lim (L_mono hδδ₂.le (hstage a ha1).1) hDL
  have hDL : graphBelow (fun a => defEnum (L a) (LTr a)) ξ ∈ L θ := by
    refine graphBelow_mem_L_of_sep hlim
      (delta0_defPart 0 1 2 3 4 5 6 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)) 6
      (v := fun k => if k = 0 then L Ordinal.omega0 else if k = 1 then ωZ
        else if k = 2 then L δ else if k = 3 then graphBelow L (ξ + 1)
        else if k = 4 then graphBelow LTr ξ else ξ.toZFSet)
      ?_ hδ₂lt hDmem ?_
    · intro i hi
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hi
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl
      · simpa using L_mem_L hθ.omega_lt
      · simpa using hθ.omega_mem
      · simpa using L_mem_L hδlt
      · simpa using hHL
      · simpa using hSL
      · simpa using (toZFSet_mem_L_iff θ ξ).mpr hξ
    · intro p
      show DefPart (L Ordinal.omega0) ωZ (L δ) (graphBelow L (ξ + 1)) (graphBelow LTr ξ)
        ξ.toZFSet p ↔ _
      constructor
      · rintro ⟨ζ, hζ, A, hA, T, hT, Dz, rfl, hde⟩
        obtain ⟨a, ha, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hζ
        obtain ⟨-, rfl⟩ := pair_mem_graphBelow_iff.mp hA
        obtain ⟨-, rfl⟩ := pair_mem_graphBelow_iff.mp hT
        exact ⟨a, ha, by
          rw [isDefEnum_eq_defEnum (hsat a (ha.trans (ordinal_lt_add_one ξ))) hde]⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a.toZFSet, Ordinal.toZFSet_mem_toZFSet_iff.mpr ha, L a,
          pair_mem_graphBelow_iff.mpr ⟨ha.trans (ordinal_lt_add_one ξ), rfl⟩,
          LTr a, pair_mem_graphBelow_iff.mpr ⟨ha, rfl⟩, _, rfl,
          isDefEnum_defEnum (hsat a (ha.trans (ordinal_lt_add_one ξ)))⟩
  -- Lemma 10.4(3) applied to `{H, S, D, L δ}`, as in the paper's proof of Lemma 10.5(2):
  -- one transitive, pair- and union-closed auxiliary set containing all the data
  have hXL : (insert (graphBelow L (ξ + 1)) (insert (graphBelow LTr ξ)
      (insert (graphBelow (fun a => defEnum (L a) (LTr a)) ξ)
        (insert (L δ) (∅ : ZFSet.{u}))))) ∈ L θ :=
    insert_mem_L_of_limit hlim hHL
      (insert_mem_L_of_limit hlim hSL
        (insert_mem_L_of_limit hlim hDL
          (insert_mem_L_of_limit hlim (L_mem_L hδlt) (empty_mem_L_of_limit hlim))))
  obtain ⟨U, hUL, hXU, hUtrans, hUpucl⟩ := exists_puCl_superset hθ hXL
  have hHρ : graphBelow L (ξ + 1) ∈ U := hXU (by simp)
  have hSρ : graphBelow LTr ξ ∈ U := hXU (by simp)
  have hDρ : graphBelow (fun a => defEnum (L a) (LTr a)) ξ ∈ U := hXU (by simp)
  have hsub : ∀ z ∈ L δ, z ∈ U := fun z hz => hUtrans.subset_of_mem (hXU (by simp)) hz
  have hsatρ : ∀ a : Ordinal.{u}, a < ξ + 1 →
      SatCode (L Ordinal.omega0) ωZ (L a) U (LTr a) := fun a ha =>
    satCode_truthSet hUtrans (hsub _ (hstage a ha).2.1) (hsub _ (hstage a ha).2.2)
      (hsub _ hωZδ) hUpucl
  refine ⟨L ξ, L_mem_L hξ, fourTuple U (graphBelow L (ξ + 1)) (graphBelow LTr ξ)
      (graphBelow (fun a => defEnum (L a) (LTr a)) ξ), ?_,
    U, graphBelow L (ξ + 1), graphBelow LTr ξ, graphBelow (fun a => defEnum (L a) (LTr a)) ξ,
    fourCode_fourTuple _ _ _ _,
    ⟨ZFSet.isOrdinal_toZFSet ξ, hUtrans, ?_, ?_, hHρ, hSρ, hDρ, ?_, hUpucl⟩,
    ⟨graphBelow_isFunc _ _, ?_, graphBelow_isFunc _ _, graphBelow_isDom _ _,
      graphBelow_isFunc _ _, graphBelow_isDom _ _, ?_⟩, ?_, ?_, ?_,
    ⟨?_, limClause_graphBelow_L ξ le_rfl⟩, ?_⟩
  · refine ofList_mem_L_of_limit hlim _ ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact kpair_mem_L_of_limit hlim (natZ_mem_L hθ.omega_lt 0) hUL
    · exact kpair_mem_L_of_limit hlim (natZ_mem_L hθ.omega_lt 1) hHL
    · exact kpair_mem_L_of_limit hlim (natZ_mem_L hθ.omega_lt 2) hSL
    · exact kpair_mem_L_of_limit hlim (natZ_mem_L hθ.omega_lt 3) hDL
  · exact hsub _ ((toZFSet_mem_L_iff δ ξ).mpr hξδ)
  · exact hsub _ (L_mem_L hξδ)
  · exact hsub _ hωZδ
  · rw [← Ordinal.toZFSet_add_one]; exact graphBelow_isDom _ _
  · have h0 : ZFSet.pair (0 : Ordinal.{u}).toZFSet (L (0 : Ordinal.{u})) ∈
        graphBelow L (ξ + 1) :=
      pair_mem_graphBelow_iff.mpr ⟨lt_of_le_of_lt (ordinal_zero_le ξ) (ordinal_lt_add_one ξ), rfl⟩
    rwa [Ordinal.toZFSet_zero, L_zero, ← natZ_zero] at h0
  · intro s hs Hx hHx Sx hSx
    obtain ⟨a, ha, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hs
    obtain ⟨-, rfl⟩ := pair_mem_graphBelow_iff.mp hHx
    obtain ⟨-, rfl⟩ := pair_mem_graphBelow_iff.mp hSx
    exact hsatρ a (ha.trans (ordinal_lt_add_one ξ))
  · intro s hs Hx hHx Sx hSx Dx hDx
    obtain ⟨a, ha, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hs
    obtain ⟨-, rfl⟩ := pair_mem_graphBelow_iff.mp hHx
    obtain ⟨-, rfl⟩ := pair_mem_graphBelow_iff.mp hSx
    obtain ⟨-, rfl⟩ := pair_mem_graphBelow_iff.mp hDx
    exact isDefEnum_defEnum (hsatρ a (ha.trans (ordinal_lt_add_one ξ)))
  · intro s hs Dx hDx Hx' hHx'
    obtain ⟨a, ha, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hs
    obtain ⟨-, rfl⟩ := pair_mem_graphBelow_iff.mp hDx
    rw [← Ordinal.toZFSet_add_one] at hHx'
    obtain ⟨-, rfl⟩ := pair_mem_graphBelow_iff.mp hHx'
    intro y
    rw [L_succ, ← mem_ran_defEnum_iff (hsatρ a (ha.trans (ordinal_lt_add_one ξ)))
      (isDefEnum_defEnum (hsatρ a (ha.trans (ordinal_lt_add_one ξ))))]
  · intro s hs
    obtain ⟨a, ha, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hs
    exact limClause_graphBelow_L a ha.le
  · exact pair_mem_graphBelow_iff.mpr ⟨ordinal_lt_add_one ξ, rfl⟩

/-- Every admissible ordinal is *good*. -/
theorem goodOrd_of_isAdmissible {θ : Ordinal.{u}} (hθ : IsAdmissible θ) : GoodOrd θ :=
  ⟨hθ, baseCorrect_L hθ, fun _ hξ => lcode_exists_in_L hθ hξ⟩

end BM4.ST
