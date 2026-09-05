/-
  Part III (§16, second half): a countable `Λ` with `L Λ ≺ L ω₁` (Lemma 16.2).
-/
import Bm4.SetTheory.Omega1
import Bm4.SetTheory.Elem

universe u

namespace BM4.ST

open Fm Classical

/-- `ω₁` as an ordinal. -/
noncomputable def omega1 : Ordinal.{u} := (Cardinal.aleph 1).ord

theorem omega0_lt_omega1 : Ordinal.omega0.{u} < omega1.{u} := by
  unfold omega1
  rw [Cardinal.ord_aleph]
  exact Ordinal.omega0_lt_omega_one

theorem isAdmissible_omega1' : IsAdmissible omega1.{u} := isAdmissible_omega1

theorem omega1_isSuccLimit : Order.IsSuccLimit omega1.{u} := isAdmissible_omega1'.isSuccLimit

/-- Two valuations agreeing on `fv φ` after an update at `i` give the same truth value. -/
theorem satIn_update_congr {M : ZFSet.{u}} {φ : Fm} {i : ℕ} {v v' : ℕ → ZFSet.{u}}
    (h : ∀ k ∈ (fv φ).erase i, v k = v' k) (x : ZFSet.{u}) :
    SatIn M (Function.update v i x) φ ↔ SatIn M (Function.update v' i x) φ := by
  apply sat_congr
  intro k hk
  by_cases hki : k = i
  · subst hki; simp
  · rw [Function.update_of_ne hki, Function.update_of_ne hki]
    exact h k (Finset.mem_erase.mpr ⟨hki, hk⟩)

/-- A stage of `L` containing a given element of `L ω₁`. -/
noncomputable def stageOf {x : ZFSet.{u}} (hx : x ∈ L omega1.{u}) : Ordinal.{u} :=
  Classical.choose ((mem_L_limit omega1_isSuccLimit).mp hx)

theorem stageOf_lt {x : ZFSet.{u}} (hx : x ∈ L omega1.{u}) : stageOf hx < omega1.{u} :=
  (Classical.choose_spec ((mem_L_limit omega1_isSuccLimit).mp hx)).1

theorem mem_L_stageOf {x : ZFSet.{u}} (hx : x ∈ L omega1.{u}) : x ∈ L (stageOf hx) :=
  (Classical.choose_spec ((mem_L_limit omega1_isSuccLimit).mp hx)).2

/-- The index type of existential statements with parameters read off a countable enumeration:
a formula, the quantified variable, and a list assigning to variable `k` the index `l[k]`. -/
abbrev Idx : Type := Fm × ℕ × List ℕ

/-- The valuation determined by an enumeration `e` and an index list. -/
noncomputable def valOfIdx (e : ℕ → ZFSet.{u}) (l : List ℕ) : ℕ → ZFSet.{u} :=
  fun k => e (l.getD k 0)

theorem valOfIdx_range_map (e : ℕ → ZFSet.{u}) (n : ℕ → ℕ) {N k : ℕ} (hk : k < N) :
    valOfIdx e ((List.range N).map n) k = e (n k) := by
  unfold valOfIdx
  congr 1
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

/-- Witness stage for one index, relative to an enumeration `e`. -/
noncomputable def witStage (e : ℕ → ZFSet.{u}) (p : Idx) : Ordinal.{u} :=
  if h : ∃ x, ∃ hx : x ∈ L omega1.{u},
      SatIn (L omega1) (Function.update (valOfIdx e p.2.2) p.2.1 x) p.1 then
    stageOf (Classical.choose_spec h).1
  else 0

theorem witStage_lt (e : ℕ → ZFSet.{u}) (p : Idx) : witStage e p < omega1.{u} := by
  unfold witStage
  split_ifs with h
  · exact stageOf_lt _
  · exact Ordinal.omega0_pos.trans omega0_lt_omega1

theorem witStage_spec (e : ℕ → ZFSet.{u}) (p : Idx)
    (h : ∃ x, ∃ hx : x ∈ L omega1.{u},
      SatIn (L omega1) (Function.update (valOfIdx e p.2.2) p.2.1 x) p.1) :
    ∃ x ∈ L (witStage e p), SatIn (L omega1) (Function.update (valOfIdx e p.2.2) p.2.1 x) p.1 := by
  unfold witStage
  rw [dif_pos h]
  refine ⟨Classical.choose h, mem_L_stageOf (Classical.choose_spec h).1, ?_⟩
  exact (Classical.choose_spec h).2

/-! ### Enumerations of the countable stages -/

theorem exists_enum {γ : Ordinal.{u}} (hγ : γ < omega1.{u}) :
    ∃ f : ℕ → ZFSet.{u}, ∀ x ∈ L γ, ∃ n, f n = x := by
  rcases Set.eq_empty_or_nonempty (L γ).toSet with hemp | hne
  · refine ⟨fun _ => ∅, fun x hx => ?_⟩
    exact absurd (show x ∈ (L γ).toSet from hx) (by rw [hemp]; exact fun h => h)
  · obtain ⟨f, hf⟩ := (L_countable hγ).exists_eq_range hne
    refine ⟨f, fun x hx => ?_⟩
    have : x ∈ Set.range f := by rw [← hf]; exact hx
    exact this

/-- A fixed enumeration of `L γ`. -/
noncomputable def enumL (γ : Ordinal.{u}) : ℕ → ZFSet.{u} :=
  if h : ∃ f : ℕ → ZFSet.{u}, ∀ x ∈ L γ, ∃ n, f n = x then Classical.choose h else fun _ => ∅

theorem enumL_spec {γ : Ordinal.{u}} (hγ : γ < omega1.{u}) {x : ZFSet.{u}} (hx : x ∈ L γ) :
    ∃ n, enumL γ n = x := by
  unfold enumL
  rw [dif_pos (exists_enum hγ)]
  exact Classical.choose_spec (exists_enum hγ) x hx

/-! ### The successor stage -/

/-- A stage above `γ` containing witnesses for all existential statements with parameters
in `L γ` that hold in `L ω₁`. -/
noncomputable def nextStage (γ : Ordinal.{u}) : Ordinal.{u} :=
  max (γ + 1) (⨆ p : ULift.{u} Idx, witStage (enumL γ) p.down)

theorem lt_nextStage (γ : Ordinal.{u}) : γ < nextStage γ :=
  lt_of_lt_of_le (Order.lt_add_one_iff.mpr le_rfl) (le_max_left _ _)

theorem nextStage_lt {γ : Ordinal.{u}} (hγ : γ < omega1.{u}) : nextStage γ < omega1.{u} := by
  have hcof : (Cardinal.aleph 1) = (omega1.{u}).cof := by
    show (Cardinal.aleph 1) = ((Cardinal.aleph 1).ord).cof
    rw [Cardinal.isRegular_aleph_one.cof_ord]
  have hsup : (⨆ p : ULift.{u} Idx, witStage (enumL γ) p.down) < omega1.{u} := by
    apply Ordinal.iSup_lt_of_lt_cof
    · rw [← hcof]
      calc Cardinal.mk (ULift.{u} Idx) ≤ Cardinal.aleph0 :=
            Cardinal.mk_le_aleph0_iff.mpr inferInstance
        _ < Cardinal.aleph 1 := Cardinal.aleph0_lt_aleph_one
    · intro p
      exact witStage_lt _ _
  exact max_lt (omega1_isSuccLimit.add_one_lt hγ) hsup

theorem le_nextStage_witStage (γ : Ordinal.{u}) (p : Idx) :
    witStage (enumL γ) p ≤ nextStage γ :=
  le_trans (Ordinal.le_iSup (fun q : ULift.{u} Idx => witStage (enumL γ) q.down) (ULift.up p))
    (le_max_right _ _)

/-- **Witness property** of `nextStage`. -/
theorem witness_in_nextStage {γ : Ordinal.{u}} (hγ : γ < omega1.{u}) (φ : Fm) (i : ℕ)
    (v : ℕ → ZFSet.{u}) (hv : ∀ k ∈ (fv φ).erase i, v k ∈ L γ)
    (hex : ∃ x ∈ L omega1.{u}, SatIn (L omega1) (Function.update v i x) φ) :
    ∃ y ∈ L (nextStage γ), SatIn (L omega1) (Function.update v i y) φ := by
  classical
  -- an index list representing `v` on the relevant variables
  set N : ℕ := (insert i (fv φ)).sup id + 1 with hN
  have hlt : ∀ k ∈ (fv φ).erase i, k < N := by
    intro k hk
    have : k ≤ (insert i (fv φ)).sup id :=
      Finset.le_sup (f := id) (Finset.mem_insert_of_mem (Finset.mem_of_mem_erase hk))
    omega
  have hn : ∀ k, ∃ m, k ∈ (fv φ).erase i → enumL γ m = v k := by
    intro k
    by_cases hk : k ∈ (fv φ).erase i
    · obtain ⟨m, hm⟩ := enumL_spec hγ (hv k hk)
      exact ⟨m, fun _ => hm⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose n hnspec using hn
  set l : List ℕ := (List.range N).map n with hl
  have hagree : ∀ k ∈ (fv φ).erase i, valOfIdx (enumL γ) l k = v k := by
    intro k hk
    rw [hl, valOfIdx_range_map (enumL γ) n (hlt k hk)]
    exact hnspec k hk
  -- the existential statement holds of the index valuation
  obtain ⟨x, hx, hsat⟩ := hex
  have hsat' : SatIn (L omega1) (Function.update (valOfIdx (enumL γ) l) i x) φ :=
    (satIn_update_congr (fun k hk => (hagree k hk).symm) x).mp hsat
  have hh : ∃ y, ∃ hy : y ∈ L omega1.{u},
      SatIn (L omega1) (Function.update (valOfIdx (enumL γ) ((φ, i, l) : Idx).2.2)
        ((φ, i, l) : Idx).2.1 y) ((φ, i, l) : Idx).1 := ⟨x, hx, hsat'⟩
  obtain ⟨y, hy, hysat⟩ := witStage_spec (enumL γ) (φ, i, l) hh
  refine ⟨y, L_mono (le_nextStage_witStage γ (φ, i, l)) hy, ?_⟩
  exact (satIn_update_congr (fun k hk => hagree k hk) y).mp hysat

/-! ### The chain and its limit -/

/-- The chain of stages starting from `γ₀`. -/
noncomputable def chain (γ₀ : Ordinal.{u}) : ℕ → Ordinal.{u}
  | 0 => γ₀
  | s + 1 => nextStage (chain γ₀ s)

theorem chain_lt_omega1 {γ₀ : Ordinal.{u}} (h : γ₀ < omega1.{u}) :
    ∀ s, chain γ₀ s < omega1.{u}
  | 0 => h
  | s + 1 => nextStage_lt (chain_lt_omega1 h s)

theorem chain_lt_succ (γ₀ : Ordinal.{u}) (s : ℕ) : chain γ₀ s < chain γ₀ (s + 1) :=
  lt_nextStage _

theorem chain_mono (γ₀ : Ordinal.{u}) : Monotone (chain γ₀) := by
  intro s t hst
  induction hst with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (chain_lt_succ γ₀ _).le

/-- The limit of the chain. -/
noncomputable def Lam (γ₀ : Ordinal.{u}) : Ordinal.{u} := ⨆ s : ULift.{u} ℕ, chain γ₀ s.down

theorem chain_le_Lam (γ₀ : Ordinal.{u}) (s : ℕ) : chain γ₀ s ≤ Lam γ₀ :=
  Ordinal.le_iSup (fun t : ULift.{u} ℕ => chain γ₀ t.down) (ULift.up s)

theorem chain_lt_Lam (γ₀ : Ordinal.{u}) (s : ℕ) : chain γ₀ s < Lam γ₀ :=
  lt_of_lt_of_le (chain_lt_succ γ₀ s) (chain_le_Lam γ₀ (s + 1))

theorem lt_Lam_iff {γ₀ o : Ordinal.{u}} : o < Lam γ₀ ↔ ∃ s, o < chain γ₀ s := by
  unfold Lam
  rw [Ordinal.lt_iSup_iff]
  exact ⟨fun ⟨s, hs⟩ => ⟨s.down, hs⟩, fun ⟨s, hs⟩ => ⟨ULift.up s, hs⟩⟩

theorem Lam_lt_omega1 {γ₀ : Ordinal.{u}} (h : γ₀ < omega1.{u}) : Lam γ₀ < omega1.{u} := by
  have hcof : (Cardinal.aleph 1) = (omega1.{u}).cof := by
    show (Cardinal.aleph 1) = ((Cardinal.aleph 1).ord).cof
    rw [Cardinal.isRegular_aleph_one.cof_ord]
  apply Ordinal.iSup_lt_of_lt_cof
  · rw [← hcof]
    calc Cardinal.mk (ULift.{u} ℕ) ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0_iff.mpr inferInstance
      _ < Cardinal.aleph 1 := Cardinal.aleph0_lt_aleph_one
  · intro s
    exact chain_lt_omega1 h s.down

theorem Lam_isSuccLimit (γ₀ : Ordinal.{u}) : Order.IsSuccLimit (Lam γ₀) := by
  rw [Order.isSuccLimit_iff]
  constructor
  · exact fun h => absurd (h ▸ chain_lt_Lam γ₀ 0) (by simp)
  · intro δ hδ
    -- `hδ : Order.CovBy δ (Lam γ₀)`; derive a contradiction
    have hδlt : δ < Lam γ₀ := hδ.lt
    obtain ⟨s, hs⟩ := lt_Lam_iff.mp hδlt
    exact absurd (chain_lt_Lam γ₀ s) (not_lt.mpr (hδ.ge_of_gt hs))

theorem mem_L_Lam_iff {γ₀ : Ordinal.{u}} {x : ZFSet.{u}} :
    x ∈ L (Lam γ₀) ↔ ∃ s, x ∈ L (chain γ₀ s) := by
  rw [mem_L_limit (Lam_isSuccLimit γ₀)]
  constructor
  · rintro ⟨o, ho, hx⟩
    obtain ⟨s, hs⟩ := lt_Lam_iff.mp ho
    exact ⟨s, L_mono hs.le hx⟩
  · rintro ⟨s, hx⟩
    exact ⟨chain γ₀ s, chain_lt_Lam γ₀ s, hx⟩

/-! ### Lemma 16.2: `L Λ ≺ L ω₁` -/

theorem elemFull_L_Lam {γ₀ : Ordinal.{u}} (h : γ₀ < omega1.{u}) :
    ElemFull (L (Lam γ₀)) (L omega1.{u}) := by
  classical
  refine elemFull_of_witness (L_mono (Lam_lt_omega1 h).le) ?_
  intro φ i v hv hex
  -- all relevant parameters appear at some stage of the chain
  have hstage : ∀ k, ∃ s, k ∈ (fv φ).erase i → v k ∈ L (chain γ₀ s) := by
    intro k
    by_cases hk : k ∈ (fv φ).erase i
    · obtain ⟨s, hs⟩ := mem_L_Lam_iff.mp (hv k hk)
      exact ⟨s, fun _ => hs⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose sf hsf using hstage
  set S : ℕ := ((fv φ).erase i).sup sf with hS
  have hvS : ∀ k ∈ (fv φ).erase i, v k ∈ L (chain γ₀ S) := by
    intro k hk
    exact L_mono (chain_mono γ₀ (Finset.le_sup (f := sf) hk)) (hsf k hk)
  obtain ⟨y, hy, hysat⟩ :=
    witness_in_nextStage (chain_lt_omega1 h S) φ i v hvS hex
  exact ⟨y, mem_L_Lam_iff.mpr ⟨S + 1, hy⟩, hysat⟩

/-- **Lemma 16.2**: there are `Λ < Θ = ω₁` with `ω < Λ` and `L Λ ≺ L Θ`. -/
theorem exists_elemFull_pair :
    ∃ Λ : Ordinal.{u}, Ordinal.omega0 < Λ ∧ Λ < omega1.{u} ∧ ElemFull (L Λ) (L omega1.{u}) := by
  refine ⟨Lam (Ordinal.omega0 + 1), ?_, Lam_lt_omega1 ?_, elemFull_L_Lam ?_⟩
  · exact lt_of_lt_of_le (Order.lt_add_one_iff.mpr le_rfl) (chain_le_Lam _ 0)
  · exact omega1_isSuccLimit.add_one_lt omega0_lt_omega1
  · exact omega1_isSuccLimit.add_one_lt omega0_lt_omega1

end BM4.ST
