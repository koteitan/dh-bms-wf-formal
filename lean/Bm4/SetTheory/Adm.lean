/-
  Part III, B3: admissible ordinals (semantic definition) and basic closure properties of `L θ`.
-/
import Bm4.SetTheory.L
import Bm4.SetTheory.Defin

universe u

namespace BM4.ST

open Fm

/-- The ordinal `ω` as a ZFC set. -/
noncomputable def ωZ : ZFSet.{u} := Ordinal.omega0.toZFSet

/-- Δ₀-Collection in a transitive set `W`: for every Δ₀ predicate `P` (in variables `i`, `j`
and parameters in `W`) and `a ∈ W`, if every `x ∈ a` has a `y ∈ W` with `P x y`, then there is
`b ∈ W` collecting such `y`'s. -/
def Delta0Collection (W : ZFSet.{u}) : Prop :=
  ∀ (s : Finset ℕ) (P : Pred.{u}), Delta0Def s P → ∀ (i j : ℕ), i ≠ j →
    ∀ (v : ℕ → ZFSet.{u}), ValD (· ∈ W) ((s.erase i).erase j) v → ∀ a ∈ W,
      (∀ x ∈ a, ∃ y ∈ W, P (· ∈ W) (Function.update (Function.update v i x) j y)) →
      ∃ b ∈ W, ∀ x ∈ a, ∃ y ∈ b, P (· ∈ W) (Function.update (Function.update v i x) j y)

/-- Admissible ordinals: `θ > ω`, a limit, and `L θ` satisfies Δ₀-Collection.

The paper defines "`θ` is admissible" as `L θ ⊨ KP`, where KP consists of Extensionality, Empty
Set, Pairing, Union, Infinity, Δ₀-Separation, Δ₀-Collection and Set Induction.  The triple used
here is equivalent to that: the seven axioms other than Δ₀-Collection hold in `L θ` for every
limit `θ > ω`, and conversely `ω < θ` and the limit property follow from the truth of the KP
axioms in `L θ`.  The equivalence is not available at this point in the development — the KP
axioms are formulas of `Bm4/SetTheory/KPAx.lean`, which is downstream of this file — and is
proved there: `KPSat.satIn_kpAx` (this triple implies every KP axiom is true in `L θ`),
`KPSat.isAdmissible_of_kpTrue`, and `AdmKP.omega_lt_of_kpTrue` / `AdmKP.isSuccLimit_of_kpTrue`
(the converse). -/
def IsAdmissible (θ : Ordinal.{u}) : Prop :=
  Ordinal.omega0 < θ ∧ Order.IsSuccLimit θ ∧ Delta0Collection (L θ)

theorem IsAdmissible.omega_lt {θ : Ordinal.{u}} (h : IsAdmissible θ) : Ordinal.omega0 < θ := h.1
theorem IsAdmissible.isSuccLimit {θ : Ordinal.{u}} (h : IsAdmissible θ) : Order.IsSuccLimit θ := h.2.1
theorem IsAdmissible.collection {θ : Ordinal.{u}} (h : IsAdmissible θ) : Delta0Collection (L θ) :=
  h.2.2

theorem IsAdmissible.pos {θ : Ordinal.{u}} (h : IsAdmissible θ) : 0 < θ :=
  Ordinal.omega0_pos.trans h.omega_lt

theorem IsAdmissible.omega_mem {θ : Ordinal.{u}} (h : IsAdmissible θ) : ωZ ∈ L θ :=
  (toZFSet_mem_L_iff θ _).mpr h.omega_lt

theorem IsAdmissible.goodDom {θ : Ordinal.{u}} (h : IsAdmissible θ) : GoodDom (· ∈ L θ) :=
  goodDom_mem (L_transitive θ) (L_nonempty h.pos)

/-! ### Closure of `L θ` for limit `θ` -/

/-- Pairs `{a, b}` of elements of `L o` lie in `L (o+1)`. -/
theorem pair_mem_L_succ {o : Ordinal.{u}} {a b : ZFSet.{u}} (ha : a ∈ L o) (hb : b ∈ L o) :
    ({a, b} : ZFSet.{u}) ∈ L (o + 1) := by
  rw [L_succ, mem_Def]
  refine ⟨?_, Fm.or (Fm.eq 0 1) (Fm.eq 0 2), 0, fun n => if n = 1 then a else b, ?_, ?_⟩
  · intro x hx
    rw [ZFSet.mem_insert_iff, ZFSet.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  · intro j hj
    simp only [fv_or, fv, Finset.mem_erase, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton] at hj
    rcases hj with ⟨h0, (rfl | rfl) | (rfl | rfl)⟩
    · exact absurd rfl h0
    · simpa
    · exact absurd rfl h0
    · simp [hb]
  · intro x
    simp only [SatIn, sat_or, sat_eq, Function.update_self,
      Function.update_of_ne (show (1 : ℕ) ≠ 0 by decide),
      Function.update_of_ne (show (2 : ℕ) ≠ 0 by decide)]
    simp only [if_true, if_false, show (2 : ℕ) = 1 ↔ False by decide]
    rw [ZFSet.mem_insert_iff, ZFSet.mem_singleton]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨ha, Or.inl rfl⟩
      · exact ⟨hb, Or.inr rfl⟩
    · rintro ⟨_, rfl | rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl

theorem pair_mem_L_of_limit {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ) {a b : ZFSet.{u}}
    (ha : a ∈ L θ) (hb : b ∈ L θ) : ({a, b} : ZFSet.{u}) ∈ L θ := by
  rw [mem_L_limit hθ] at ha hb
  obtain ⟨o₁, ho₁, ha⟩ := ha
  obtain ⟨o₂, ho₂, hb⟩ := hb
  have ha' : a ∈ L (max o₁ o₂) := L_mono (le_max_left _ _) ha
  have hb' : b ∈ L (max o₁ o₂) := L_mono (le_max_right _ _) hb
  exact L_mono (hθ.add_one_lt (max_lt ho₁ ho₂)).le (pair_mem_L_succ ha' hb')

theorem singleton_mem_L_of_limit {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ) {a : ZFSet.{u}}
    (ha : a ∈ L θ) : ({a} : ZFSet.{u}) ∈ L θ := by
  have := pair_mem_L_of_limit hθ ha ha
  rwa [ZFSet.pair_eq_singleton] at this

/-- Kuratowski pairs. -/
theorem kpair_mem_L_of_limit {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ) {a b : ZFSet.{u}}
    (ha : a ∈ L θ) (hb : b ∈ L θ) : ZFSet.pair a b ∈ L θ :=
  pair_mem_L_of_limit hθ (singleton_mem_L_of_limit hθ ha) (pair_mem_L_of_limit hθ ha hb)

/-- Unions `⋃ a` of elements of `L o` (transitive) lie in `L (o+1)`. -/
theorem sUnion_mem_L_succ {o : Ordinal.{u}} {a : ZFSet.{u}} (ha : a ∈ L o) :
    ZFSet.sUnion a ∈ L (o + 1) := by
  rw [L_succ, mem_Def]
  have hT := L_transitive o
  refine ⟨?_, Fm.bex 2 1 (Fm.mem 0 2), 0, fun _ => a, ?_, ?_⟩
  · intro x hx
    rw [ZFSet.mem_sUnion] at hx
    obtain ⟨y, hy, hx⟩ := hx
    exact hT.subset_of_mem (hT.subset_of_mem ha hy) hx
  · intro j _
    exact ha
  · intro x
    rw [ZFSet.mem_sUnion]
    simp only [SatIn]
    rw [sat_bex_of_ne (by decide)]
    simp only [sat_mem, Function.update_self, Function.update_of_ne (show (1 : ℕ) ≠ 0 by decide),
      Function.update_of_ne (show (0 : ℕ) ≠ 2 by decide),
      Function.update_of_ne (show (2 : ℕ) ≠ 0 by decide)]
    constructor
    · rintro ⟨y, hy, hx⟩
      exact ⟨hT.subset_of_mem (hT.subset_of_mem ha hy) hx, y, hT.subset_of_mem ha hy, hy, hx⟩
    · rintro ⟨_, y, _, hy, hx⟩
      exact ⟨y, hy, hx⟩

theorem sUnion_mem_L_of_limit {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ) {a : ZFSet.{u}}
    (ha : a ∈ L θ) : ZFSet.sUnion a ∈ L θ := by
  rw [mem_L_limit hθ] at ha
  obtain ⟨o, ho, ha⟩ := ha
  exact L_mono (hθ.add_one_lt ho).le (sUnion_mem_L_succ ha)

/-- Δ₀-Separation in `L θ` for a limit `θ`: `{x ∈ a | P x}` for Δ₀ `P` with parameters in `L θ`. -/
theorem sep_mem_L_of_limit {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ) {s : Finset ℕ}
    {P : Pred.{u}} (hP : Delta0Def s P) (i : ℕ) {v : ℕ → ZFSet.{u}}
    (hv : ValD (· ∈ L θ) (s.erase i) v) {a : ZFSet.{u}} (ha : a ∈ L θ) :
    ZFSet.sep (fun x => P (fun _ => True) (Function.update v i x)) a ∈ L θ := by
  -- all parameters and `a` lie in some `L o`, `o < θ`
  obtain ⟨φ, hφ, hfv, hsat⟩ := hP
  have hfin : ∃ o < θ, a ∈ L o ∧ ∀ j ∈ s.erase i, v j ∈ L o := by
    have hall : ∀ j ∈ s.erase i, ∃ o < θ, v j ∈ L o :=
      fun j hj => (mem_L_limit hθ).mp (hv j hj)
    choose f hf using hall
    obtain ⟨oa, hoa, ha'⟩ := (mem_L_limit hθ).mp ha
    let osup : Ordinal.{u} := (s.erase i).attach.sup (fun j => f j.1 j.2)
    have hsup_lt : osup < θ := by
      rw [Finset.sup_lt_iff hθ.bot_lt]
      intro j _
      exact (hf j.1 j.2).1
    refine ⟨max oa osup, max_lt hoa hsup_lt, L_mono (le_max_left _ _) ha', ?_⟩
    intro j hj
    have hle : f j hj ≤ osup :=
      Finset.le_sup (f := fun j : {x // x ∈ s.erase i} => f j.1 j.2) (Finset.mem_attach _ ⟨j, hj⟩)
    exact L_mono (hle.trans (le_max_right _ _)) (hf j hj).2
  obtain ⟨o, ho, ha', hv'⟩ := hfin
  have hsucc : o + 1 < θ := hθ.add_one_lt ho
  refine L_mono hsucc.le ?_
  rw [L_succ, mem_Def]
  have hT := L_transitive o
  refine ⟨?_, Fm.and (Fm.mem i (i + 1 + s.sup id)) φ, i, ?_, ?_, ?_⟩
  · intro x hx
    rw [ZFSet.mem_sep] at hx
    exact hT.subset_of_mem ha' hx.1
  · -- valuation: the parameters, and `a` at a fresh variable `m`
    exact Function.update v (i + 1 + s.sup id) a
  · intro j hj
    simp only [fv_and, fv, Finset.mem_erase, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton] at hj
    rcases hj with ⟨hji, (rfl | rfl) | hj⟩
    · exact absurd rfl hji
    · simpa
    · have hjm : j ≠ i + 1 + s.sup id := by
        intro h
        have := Finset.le_sup (f := id) (hfv hj)
        simp only [id] at this
        omega
      rw [Function.update_of_ne hjm]
      exact hv' j (Finset.mem_erase.mpr ⟨hji, hfv hj⟩)
  · intro x
    rw [ZFSet.mem_sep]
    have hm : i ≠ i + 1 + s.sup id := by omega
    have hmnot : i + 1 + s.sup id ∉ s := fun h => by
      have := Finset.le_sup (f := id) h
      simp only [id] at this
      omega
    have hval : ∀ x ∈ L o,
        ValD (· ∈ L o) s (Function.update (Function.update v (i + 1 + s.sup id) a) i x) := by
      intro x hx j hj
      by_cases hji : j = i
      · subst hji; simpa
      · rw [Function.update_of_ne hji]
        have hjm : j ≠ i + 1 + s.sup id := fun h => hmnot (by rw [← h]; exact hj)
        rw [Function.update_of_ne hjm]
        exact hv' j (Finset.mem_erase.mpr ⟨hji, hj⟩)
    have hD : GoodDom (· ∈ L o) := goodDom_mem hT ⟨a, ha'⟩
    have key : ∀ x ∈ L o,
        (SatIn (L o) (Function.update (Function.update v (i + 1 + s.sup id) a) i x) φ ↔
          P (fun _ => True) (Function.update v i x)) := by
      intro x hx
      simp only [SatIn]
      have hP : Delta0Def s P := ⟨φ, hφ, hfv, hsat⟩
      rw [hsat _ _ hD (hval x hx), hP.absolute hD (hval x hx)]
      apply Delta0Def.congr_val ⟨φ, hφ, hfv, hsat⟩ goodDom_univ (fun _ _ => trivial)
        (fun _ _ => trivial)
      intro j hj
      by_cases hji : j = i
      · subst hji; simp
      · rw [Function.update_of_ne hji, Function.update_of_ne hji]
        exact Function.update_of_ne (fun h => hmnot (by rw [← h]; exact hj)) _ _
    simp only [SatIn, sat_and, sat_mem, Function.update_self]
    rw [Function.update_of_ne hm.symm, Function.update_self]
    constructor
    · rintro ⟨hxa, hPx⟩
      exact ⟨hT.subset_of_mem ha' hxa, hxa, (key x (hT.subset_of_mem ha' hxa)).mpr hPx⟩
    · rintro ⟨hx, hxa, hsatx⟩
      exact ⟨hxa, (key x hx).mp hsatx⟩

end BM4.ST
