/-
  Part III (§16, first half): every `L γ` with `γ < ω₁` is countable (Lemma 16.1), and `ω₁` is
  admissible (Lemma 16.2, first half).
-/
import Bm4.SetTheory.Adm

universe u

namespace BM4.ST

open Fm

deriving instance Countable for Fm

/-- A valuation read off a finite list of (variable, value) pairs. -/
noncomputable def valOfList (l : List (ℕ × ZFSet.{u})) (k : ℕ) : ZFSet.{u} :=
  if h : ∃ p ∈ l, p.1 = k then (Classical.choose h).2 else ∅

/-- The definable subset of `M` given by `(φ, i, l)`. -/
noncomputable def defOf (M : ZFSet.{u}) (φ : Fm) (i : ℕ) (l : List (ℕ × ZFSet.{u})) : ZFSet.{u} :=
  ZFSet.sep (fun x => SatIn M (Function.update (valOfList l) i x) φ) M

theorem Def_subset_range (M : ZFSet.{u}) :
    (Def M).toSet ⊆ Set.range (fun p : Fm × ℕ × List (ℕ × (M : Set ZFSet.{u})) =>
      defOf M p.1 p.2.1 (p.2.2.map (fun q => (q.1, (q.2 : ZFSet.{u}))))) := by
  intro X hX
  change X ∈ Def M at hX
  obtain ⟨_, φ, i, v, hv, hX⟩ := mem_Def.mp hX
  let l : List (ℕ × (M : Set ZFSet.{u})) :=
    ((fv φ).erase i).toList.attach.map (fun k => (k.1, ⟨v k.1, hv k.1 (Finset.mem_toList.mp k.2)⟩))
  refine ⟨(φ, i, l), ?_⟩
  simp only
  set l' := l.map (fun q => (q.1, (q.2 : ZFSet.{u}))) with hl'
  have hmem : ∀ p ∈ l', p.1 ∈ (fv φ).erase i ∧ p.2 = v p.1 := by
    intro p hp
    rw [hl', List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    simp only [l, List.mem_map, List.mem_attach, true_and] at hq
    obtain ⟨k, rfl⟩ := hq
    exact ⟨Finset.mem_toList.mp k.2, rfl⟩
  have hkey : ∀ k ∈ (fv φ).erase i, valOfList l' k = v k := by
    intro k hk
    have hex : ∃ p ∈ l', p.1 = k := by
      refine ⟨(k, v k), ?_, rfl⟩
      rw [hl', List.mem_map]
      refine ⟨(k, ⟨v k, hv k hk⟩), ?_, rfl⟩
      simp only [l, List.mem_map, List.mem_attach, true_and]
      exact ⟨⟨k, Finset.mem_toList.mpr hk⟩, rfl⟩
    unfold valOfList
    rw [dif_pos hex]
    obtain ⟨hp, hpk⟩ := Classical.choose_spec hex
    rw [(hmem _ hp).2, hpk]
  symm
  ext x
  unfold defOf
  rw [ZFSet.mem_sep, hX x]
  apply and_congr_right; intro _
  apply sat_congr
  intro y hy
  by_cases hyi : y = i
  · subst hyi; simp
  · rw [Function.update_of_ne hyi, Function.update_of_ne hyi]
    exact (hkey y (Finset.mem_erase.mpr ⟨hyi, hy⟩)).symm

/-- The definable power set of a countable set is countable. -/
theorem Def_countable {M : ZFSet.{u}} (hM : M.toSet.Countable) : (Def M).toSet.Countable := by
  haveI : Countable (M : Set ZFSet.{u}) := hM.to_subtype
  exact (Set.countable_range _).mono (Def_subset_range M)

/-- Lemma 16.1: every `L γ` with `γ < ω₁` is countable. -/
theorem L_countable {γ : Ordinal.{u}} (h : γ < (Cardinal.aleph 1).ord) : (L γ).toSet.Countable := by
  induction γ using Ordinal.limitRecOn with
  | zero =>
    rw [L_zero]
    exact Set.countable_empty.mono (fun z hz => by
      change z ∈ (∅ : ZFSet.{u}) at hz
      exact (ZFSet.notMem_empty z hz).elim)
  | add_one o ih =>
    rw [L_succ]
    exact Def_countable (ih ((Order.lt_add_one_iff.mpr le_rfl).trans h))
  | limit o hlim ih =>
    have hcard : o.card ≤ Cardinal.aleph0 := by
      have := Cardinal.lt_ord.mp h
      exact Cardinal.lt_aleph_one_iff.mp this
    haveI : Countable (Set.Iio o) := by
      rw [← Cardinal.mk_le_aleph0_iff, Cardinal.mk_Iio_ordinal, Cardinal.lift_le_aleph0]
      exact hcard
    have heq : (L o).toSet = ⋃ x : Set.Iio o, (L x.1).toSet := by
      ext z
      rw [Set.mem_iUnion]
      change z ∈ L o ↔ ∃ x : Set.Iio o, z ∈ L x.1
      rw [mem_L_limit hlim]
      constructor
      · rintro ⟨o', ho', hz⟩; exact ⟨⟨o', ho'⟩, hz⟩
      · rintro ⟨⟨o', ho'⟩, hz⟩; exact ⟨o', ho', hz⟩
    rw [heq]
    exact Set.countable_iUnion (fun x => ih x.1 x.2 (x.2.trans h))

/-- Elements of `L γ` with `γ < ω₁` are countable sets. -/
theorem countable_of_mem_L {γ : Ordinal.{u}} (h : γ < (Cardinal.aleph 1).ord) {x : ZFSet.{u}}
    (hx : x ∈ L γ) : x.toSet.Countable :=
  (L_countable h).mono (fun z hz => (L_transitive γ).subset_of_mem hx hz)

/-- Lemma 16.2 (first half): `ω₁` is admissible. -/
theorem isAdmissible_omega1 : IsAdmissible ((Cardinal.aleph 1).ord : Ordinal.{u}) := by
  refine ⟨?_, Cardinal.isSuccLimit_ord Cardinal.aleph0_lt_aleph_one.le, ?_⟩
  · rw [Cardinal.ord_aleph]; exact Ordinal.omega0_lt_omega_one
  · intro s P hP i j hij v hv a ha H
    set θ : Ordinal.{u} := (Cardinal.aleph 1).ord with hθ
    have hlim : Order.IsSuccLimit θ := Cardinal.isSuccLimit_ord Cardinal.aleph0_lt_aleph_one.le
    -- `a` is countable
    obtain ⟨γa, hγa, haγ⟩ := (mem_L_limit hlim).mp ha
    have hcount : a.toSet.Countable := countable_of_mem_L hγa haγ
    haveI : Countable (a : Set ZFSet.{u}) := hcount.to_subtype
    -- choose witnesses and their stages
    have H' : ∀ x : (a : Set ZFSet.{u}), ∃ y, y ∈ L θ ∧
        P (· ∈ L θ) (Function.update (Function.update v i x.1) j y) := fun x => by
      obtain ⟨y, hy, hP⟩ := H x.1 x.2
      exact ⟨y, hy, hP⟩
    choose y hyL hyP using H'
    have H'' : ∀ x : (a : Set ZFSet.{u}), ∃ o, o < θ ∧ y x ∈ L o := fun x =>
      (mem_L_limit hlim).mp (hyL x)
    choose o ho hyo using H''
    -- shrink the index type to universe `u`
    let ι := Shrink.{u} (a : Set ZFSet.{u})
    let e : (a : Set ZFSet.{u}) ≃ ι := equivShrink _
    haveI : Countable ι := Countable.of_equiv _ e
    let f : ι → Ordinal.{u} := fun k => o (e.symm k)
    have hι : Cardinal.mk ι < Cardinal.aleph 1 :=
      Cardinal.lt_aleph_one_iff.mpr (Cardinal.mk_le_aleph0_iff.mpr inferInstance)
    have hsup : Ordinal.lsub f < θ :=
      Cardinal.lsub_lt_ord_of_isRegular Cardinal.isRegular_aleph_one hι (fun k => ho _)
    refine ⟨L (Ordinal.lsub f), L_mem_L hsup, ?_⟩
    intro x hx
    refine ⟨y ⟨x, hx⟩, ?_, hyP ⟨x, hx⟩⟩
    have hlt : o ⟨x, hx⟩ < Ordinal.lsub f := by
      have := Ordinal.lt_lsub f (e ⟨x, hx⟩)
      simpa [f] using this
    exact L_mono hlt.le (hyo ⟨x, hx⟩)

end BM4.ST
