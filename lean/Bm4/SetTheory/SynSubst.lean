/-
  Part III, §12: the graph of substitution is Δ₀ (Lemma 12.2 (1)).

  `Bm4/SetTheory/Subst.lean` defines the operation `φ ↦ φ[x := y]` on the inductive type `Fm`.
  What Lemma 12.2 actually asserts is the statement one level down, about *codes*: the relation

      G(x, y, e, d)  ⟺  `e` codes a formula `φ` and `d` codes `φ[x := y]`

  is Δ₀.  This file proves that, as an instance of the paper's general schema (8.3), which is
  already available as `GraphW` / `delta0_graphW` in `Bm4/SetTheory/CodeFV.lean`: one only has to
  supply the three local rules (atomic, `imp`, `all`) and check that they are Δ₀.

  One design point.  The `all` rule of `TraceW` receives the bound variable `i` and the *value*
  computed at the child, but not the child's code; and substitution needs the child's code, since
  `∀x φ` returns `∀x φ` unchanged.  So the value computed at a node is taken to be the **pair**
  `⟨input code, output code⟩`; the `imp` and `all` rules then recover the children's codes from
  their values.  `SubstW` reads the output off the second component, and `substW_iff` is the
  correctness statement.
-/
import Bm4.SetTheory.CodeFV
import Bm4.SetTheory.Subst

universe u

namespace BM4.ST

open Fm

/-! ### The local rules -/

/-- `i'` is the result of substituting `y` for `x` in the variable index `i`. -/
def SbIdx (x y i i' : ZFSet.{u}) : Prop := (i = x ∧ i' = y) ∨ (i ≠ x ∧ i' = i)

/-- Local rule at an atomic node: the value is `⟨e, e'⟩` with `e'` the atom with both variable
slots substituted.  The parameter is `p = ⟨x, y⟩`. -/
def SbAtomR (w p e v : ZFSet.{u}) : Prop :=
  (e = ZFSet.pair (natZ 0) (natZ 0) ∧ v = ZFSet.pair e e) ∨
  ∃ x ∈ w, ∃ y ∈ w, ∃ i ∈ w, ∃ j ∈ w, ∃ i' ∈ w, ∃ j' ∈ w, ∃ r ∈ v, ∃ b ∈ r,
    p = ZFSet.pair x y ∧ SbIdx x y i i' ∧ SbIdx x y j j' ∧ v = ZFSet.pair e b ∧
      ((e = ZFSet.pair (natZ 1) (ZFSet.pair i j) ∧
          b = ZFSet.pair (natZ 1) (ZFSet.pair i' j')) ∨
       (e = ZFSet.pair (natZ 2) (ZFSet.pair i j) ∧
          b = ZFSet.pair (natZ 2) (ZFSet.pair i' j')))

/-- Local rule at an `imp` node: both components are formed componentwise. -/
def SbImpR (_w _p v₁ v₂ v : ZFSet.{u}) : Prop :=
  ∃ q₁ ∈ v₁, ∃ e₁ ∈ q₁, ∃ d₁ ∈ q₁, ∃ q₂ ∈ v₂, ∃ e₂ ∈ q₂, ∃ d₂ ∈ q₂,
    ∃ r ∈ v, ∃ a ∈ r, ∃ b ∈ r,
      v₁ = ZFSet.pair e₁ d₁ ∧ v₂ = ZFSet.pair e₂ d₂ ∧ v = ZFSet.pair a b ∧
      a = ZFSet.pair (natZ 3) (ZFSet.pair e₁ e₂) ∧ b = ZFSet.pair (natZ 3) (ZFSet.pair d₁ d₂)

/-- Local rule at an `all` node: the substitution is blocked when the bound variable is `x`, and
then the output is the input code itself. -/
def SbAllR (w p i v₁ v : ZFSet.{u}) : Prop :=
  ∃ x ∈ w, ∃ y ∈ w, ∃ q₁ ∈ v₁, ∃ e₁ ∈ q₁, ∃ d₁ ∈ q₁, ∃ r ∈ v, ∃ a ∈ r, ∃ b ∈ r,
    p = ZFSet.pair x y ∧ v₁ = ZFSet.pair e₁ d₁ ∧ v = ZFSet.pair a b ∧
    a = ZFSet.pair (natZ 4) (ZFSet.pair i e₁) ∧
    ((i = x ∧ b = a) ∨ (i ≠ x ∧ b = ZFSet.pair (natZ 4) (ZFSet.pair i d₁)))

/-! ### The three rules are Δ₀ -/

theorem delta0_sbIdx (a b c d : ℕ) :
    Delta0Def.{u} {a, b, c, d} (fun _ v => SbIdx (v a) (v b) (v c) (v d)) :=
  ((((Delta0Def.eq.{u} c a).and (Delta0Def.eq.{u} d b)).or
      ((Delta0Def.eq.{u} c a).not.and (Delta0Def.eq.{u} d c))).congr
    (fun _ _ _ _ => Iff.rfl)).mono
    (by intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at hk ⊢
        tauto)

theorem delta0_sbAtomR (a b c d : ℕ) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Delta0Def.{u} {a, b, c, d} (fun _ v => SbAtomR (v a) (v b) (v c) (v d)) := by
  set m := a + b + c + d + 1 with hm
  -- x := m, y := m+1, i := m+2, j := m+3, i' := m+4, j' := m+5, r := m+6, b := m+7
  have h0 := (delta0_isKPair b m (m + 1) (by omega) (by omega)).and
    ((delta0_sbIdx m (m + 1) (m + 2) (m + 4)).and
      ((delta0_sbIdx m (m + 1) (m + 3) (m + 5)).and
        ((delta0_isKPair d c (m + 7) (by omega) (by omega)).and
          (((delta0_tagPair 1 c (m + 2) (m + 3) (by omega) (by omega)).and
              (delta0_tagPair 1 (m + 7) (m + 4) (m + 5) (by omega) (by omega))).or
           ((delta0_tagPair 2 c (m + 2) (m + 3) (by omega) (by omega)).and
              (delta0_tagPair 2 (m + 7) (m + 4) (m + 5) (by omega) (by omega)))))))
  have h1 := h0.bex (m + 7) (m + 6) (by omega)
  have h2 := h1.bex (m + 6) d (by omega)
  have h3 := h2.bex (m + 5) a (by omega)
  have h4 := h3.bex (m + 4) a (by omega)
  have h5 := h4.bex (m + 3) a (by omega)
  have h6 := h5.bex (m + 2) a (by omega)
  have h7 := h6.bex (m + 1) a (by omega)
  have h8 := h7.bex m a (by omega)
  have h := ((delta0_tagPair0 c).and (delta0_isKPair d c c (by omega) (by omega))).or h8
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    rfl
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

theorem delta0_sbImpR (a b c d e : ℕ) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    Delta0Def.{u} {a, b, c, d, e} (fun _ v => SbImpR (v a) (v b) (v c) (v d) (v e)) := by
  set m := a + b + c + d + e + 1 with hm
  -- q₁ := m, e₁ := m+1, d₁ := m+2, q₂ := m+3, e₂ := m+4, d₂ := m+5,
  -- r := m+6, A := m+7, B := m+8
  have h0 := (delta0_isKPair c (m + 1) (m + 2) (by omega) (by omega)).and
    ((delta0_isKPair d (m + 4) (m + 5) (by omega) (by omega)).and
      ((delta0_isKPair e (m + 7) (m + 8) (by omega) (by omega)).and
        ((delta0_tagPair 3 (m + 7) (m + 1) (m + 4) (by omega) (by omega)).and
          (delta0_tagPair 3 (m + 8) (m + 2) (m + 5) (by omega) (by omega)))))
  have h1 := h0.bex (m + 8) (m + 6) (by omega)
  have h2 := h1.bex (m + 7) (m + 6) (by omega)
  have h3 := h2.bex (m + 6) e (by omega)
  have h4 := h3.bex (m + 5) (m + 3) (by omega)
  have h5 := h4.bex (m + 4) (m + 3) (by omega)
  have h6 := h5.bex (m + 3) d (by omega)
  have h7 := h6.bex (m + 2) m (by omega)
  have h8 := h7.bex (m + 1) m (by omega)
  have h := h8.bex m c (by omega)
  refine (h.congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    rfl
  · intro k hk; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union] at hk ⊢; omega

theorem delta0_sbAllR (a b c d e : ℕ) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    Delta0Def.{u} {a, b, c, d, e} (fun _ v => SbAllR (v a) (v b) (v c) (v d) (v e)) := by
  set m := a + b + c + d + e + 1 with hm
  -- x := m, y := m+1, q₁ := m+2, e₁ := m+3, d₁ := m+4, r := m+5, A := m+6, B := m+7
  have h0 := (delta0_isKPair b m (m + 1) (by omega) (by omega)).and
    ((delta0_isKPair d (m + 3) (m + 4) (by omega) (by omega)).and
      ((delta0_isKPair e (m + 6) (m + 7) (by omega) (by omega)).and
        ((delta0_tagPair 4 (m + 6) c (m + 3) (by omega) (by omega)).and
          (((Delta0Def.eq.{u} c m).and (Delta0Def.eq.{u} (m + 7) (m + 6))).or
            ((Delta0Def.eq.{u} c m).not.and
              (delta0_tagPair 4 (m + 7) c (m + 4) (by omega) (by omega)))))))
  have h1 := h0.bex (m + 7) (m + 5) (by omega)
  have h2 := h1.bex (m + 6) (m + 5) (by omega)
  have h3 := h2.bex (m + 5) e (by omega)
  have h4 := h3.bex (m + 4) (m + 2) (by omega)
  have h5 := h4.bex (m + 3) (m + 2) (by omega)
  have h6 := h5.bex (m + 2) d (by omega)
  have h7 := h6.bex (m + 1) a (by omega)
  have h := h7.bex m a (by omega)
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    rfl
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega


/-- (8.3) for substitution: the graph built from the three local rules is Δ₀. -/
theorem delta0_graphW_sb (h w p e d : ℕ)
    (hhw : h ≠ w) (hhp : h ≠ p) (hhe : h ≠ e) (hhd : h ≠ d)
    (hwp : w ≠ p) (hwe : w ≠ e) (hwd : w ≠ d) (hpe : p ≠ e) (hpd : p ≠ d) (hed : e ≠ d) :
    Delta0Def.{u} {h, w, p, e, d}
      (fun _ v => GraphW (v h) (v w) SbAtomR SbImpR SbAllR (v p) (v e) (v d)) :=
  delta0_graphW h w p e d
    (fun a b c d hab hac had hbc hbd hcd => delta0_sbAtomR a b c d hab hac had hbc hbd hcd)
    (fun a b c d e _ h2 h3 h4 _ _ _ h8 h9 h10 => delta0_sbImpR a b c d e h2 h3 h4 h8 h9 h10)
    (fun a b c d e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
      delta0_sbAllR a b c d e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    hhw hhp hhe hhd hwp hwe hwd hpe hpd hed

/-! ### The graph of substitution -/

/-- The graph of substitution: `d` is the code of the result of substituting in the formula coded
by `e`, the parameter being `p = ⟨x, y⟩`.  The trace values are pairs `⟨input, output⟩`, so the
output is read off the second component; both the position `k` and that pair are quantified in
bounded form, which is what keeps the predicate Δ₀. -/
def SubstW (h w p e d : ZFSet.{u}) : Prop :=
  ∃ s ∈ h, ∃ t ∈ h, DerSeqW w s ∧ TraceW w SbAtomR SbImpR SbAllR p s t ∧
    ∃ P ∈ s, ∃ Q ∈ P, ∃ k ∈ Q, P = ZFSet.pair k e ∧
      ∃ P' ∈ t, ∃ Q' ∈ P', ∃ z ∈ Q', P' = ZFSet.pair k z ∧ z = ZFSet.pair e d

theorem substW_iff_graphW (h w p e d : ZFSet.{u}) :
    SubstW h w p e d ↔ GraphW h w SbAtomR SbImpR SbAllR p e (ZFSet.pair e d) := by
  constructor
  · rintro ⟨s, hs, t, ht, hd, htr, P, hP, Q, -, k, -, rfl, P', hP', Q', -, z, -, rfl, rfl⟩
    exact ⟨s, hs, t, ht, hd, htr, k, hP, hP'⟩
  · rintro ⟨s, hs, t, ht, hd, htr, k, hke, hkd⟩
    exact ⟨s, hs, t, ht, hd, htr, _, hke, _, upair_mem_pair _ _, k, mem_upair_left _ _, rfl,
      _, hkd, _, upair_mem_pair _ _, _, mem_upair_right _ _, rfl, rfl⟩

/-- Lemma 12.2 (1) for substitution: the graph is Δ₀. -/
theorem delta0_substW (h w p e d : ℕ)
    (hhw : h ≠ w) (hhp : h ≠ p) (hhe : h ≠ e) (hhd : h ≠ d)
    (hwp : w ≠ p) (hwe : w ≠ e) (hwd : w ≠ d) (hpe : p ≠ e) (hpd : p ≠ d) (hed : e ≠ d) :
    Delta0Def.{u} {h, w, p, e, d} (fun _ v => SubstW (v h) (v w) (v p) (v e) (v d)) := by
  set m := h + w + p + e + d + 1 with hm
  -- s := m, t := m+1, P := m+2, Q := m+3, k := m+4, P' := m+5, Q' := m+6, z := m+7
  have i0 := (delta0_isKPair (m + 5) (m + 4) (m + 7) (by omega) (by omega)).and
    (delta0_isKPair (m + 7) e d (by omega) (by omega))
  have i1 := i0.bex (m + 7) (m + 6) (by omega)
  have i2 := i1.bex (m + 6) (m + 5) (by omega)
  have i3 := i2.bex (m + 5) (m + 1) (by omega)
  have b0 := (delta0_isKPair (m + 2) (m + 4) e (by omega) (by omega)).and i3
  have b1 := b0.bex (m + 4) (m + 3) (by omega)
  have b2 := b1.bex (m + 3) (m + 2) (by omega)
  have b3 := b2.bex (m + 2) m (by omega)
  have dd := (delta0_derSeqW w m (by omega)).and
    ((delta0_traceW (A := SbAtomR) (I := SbImpR) (U := SbAllR) w p m (m + 1)
      (fun a b c d hab hac had hbc hbd hcd => delta0_sbAtomR a b c d hab hac had hbc hbd hcd)
      (fun a b c d e _ h2 h3 h4 _ _ _ h8 h9 h10 => delta0_sbImpR a b c d e h2 h3 h4 h8 h9 h10)
      (fun a b c d e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
        delta0_sbAllR a b c d e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).and b3)
  have hh1 := dd.bex (m + 1) h (by omega)
  have hh := hh1.bex m h (by omega)
  refine (hh.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    rfl
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-! ### Correctness: the shape of atomic codes -/

theorem isAtomicCodeW_shape {e : ZFSet.{u}} (h : IsAtomicCodeW ωZ e) :
    e = (Fm.falsum).code ∨ (∃ i j : ℕ, e = (Fm.eq i j).code) ∨
      (∃ i j : ℕ, e = (Fm.mem i j).code) := by
  rcases h with rfl | ⟨i, hi, j, hj, H⟩
  · exact Or.inl rfl
  · obtain ⟨i', rfl⟩ := mem_ωZ_iff.mp hi
    obtain ⟨j', rfl⟩ := mem_ωZ_iff.mp hj
    rcases H with rfl | rfl
    · exact Or.inr (Or.inl ⟨i', j', rfl⟩)
    · exact Or.inr (Or.inr ⟨i', j', rfl⟩)

theorem sbIdx_natZ (x y i : ℕ) : SbIdx (natZ.{u} x) (natZ y) (natZ i) (natZ (Fm.sb x y i)) := by
  unfold Fm.sb SbIdx
  split_ifs with hi
  · exact Or.inl ⟨by rw [hi], rfl⟩
  · exact Or.inr ⟨fun hh => hi (natZ_injective hh), rfl⟩

/-! ### The local rules do hold at the codes -/

theorem sbAtomR_of_atomic (x y : ℕ) {φ : Fm} (h : IsAtomicCodeW ωZ.{u} φ.code) :
    SbAtomR ωZ.{u} (ZFSet.pair (natZ x) (natZ y)) φ.code
      (ZFSet.pair φ.code (Fm.subst x y φ).code) := by
  have key : ∀ (ψ : Fm) (i j : ℕ), (ψ = Fm.eq i j ∨ ψ = Fm.mem i j) →
      SbAtomR ωZ.{u} (ZFSet.pair (natZ x) (natZ y)) ψ.code
        (ZFSet.pair ψ.code (Fm.subst x y ψ).code) := by
    intro ψ i j hψ
    refine Or.inr ⟨natZ x, natZ_mem_ωZ x, natZ y, natZ_mem_ωZ y, natZ i, natZ_mem_ωZ i,
      natZ j, natZ_mem_ωZ j, natZ (Fm.sb x y i), natZ_mem_ωZ _, natZ (Fm.sb x y j),
      natZ_mem_ωZ _, _, upair_mem_pair _ _, _, mem_upair_right _ _, rfl,
      sbIdx_natZ x y i, sbIdx_natZ x y j, rfl, ?_⟩
    rcases hψ with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  rcases isAtomicCodeW_shape h with hc | ⟨i, j, hc⟩ | ⟨i, j, hc⟩ <;>
    obtain rfl := Fm.code_injective hc
  · exact Or.inl ⟨rfl, rfl⟩
  · exact key _ i j (Or.inl rfl)
  · exact key _ i j (Or.inr rfl)

theorem sbImpR_intro (x y : ℕ) (φ ψ : Fm) :
    SbImpR ωZ.{u} (ZFSet.pair (natZ x) (natZ y))
      (ZFSet.pair φ.code (Fm.subst x y φ).code)
      (ZFSet.pair ψ.code (Fm.subst x y ψ).code)
      (ZFSet.pair (Fm.imp φ ψ).code (Fm.subst x y (Fm.imp φ ψ)).code) :=
  ⟨_, upair_mem_pair _ _, _, mem_upair_left _ _, _, mem_upair_right _ _,
   _, upair_mem_pair _ _, _, mem_upair_left _ _, _, mem_upair_right _ _,
   _, upair_mem_pair _ _, _, mem_upair_left _ _, _, mem_upair_right _ _,
   rfl, rfl, rfl, rfl, rfl⟩

theorem sbAllR_intro (x y i : ℕ) (φ : Fm) :
    SbAllR ωZ.{u} (ZFSet.pair (natZ x) (natZ y)) (natZ i)
      (ZFSet.pair φ.code (Fm.subst x y φ).code)
      (ZFSet.pair (Fm.all i φ).code (Fm.subst x y (Fm.all i φ)).code) := by
  refine ⟨natZ x, natZ_mem_ωZ x, natZ y, natZ_mem_ωZ y, _, upair_mem_pair _ _,
    _, mem_upair_left _ _, _, mem_upair_right _ _, _, upair_mem_pair _ _,
    _, mem_upair_left _ _, _, mem_upair_right _ _, rfl, rfl, rfl, rfl, ?_⟩
  by_cases hix : i = x
  · subst hix
    exact Or.inl ⟨rfl, by rw [Fm.subst_all_of_eq]⟩
  · refine Or.inr ⟨fun hh => hix (natZ_injective hh), ?_⟩
    rw [Fm.subst_all_of_ne hix]
    rfl

/-! ### Soundness -/

theorem sbCodeShape_imp {ψ : Fm} {a b : ZFSet.{u}}
    (h : ψ.code = ZFSet.pair (natZ 3) (ZFSet.pair a b)) :
    ∃ ψ₁ ψ₂ : Fm, ψ = Fm.imp ψ₁ ψ₂ ∧ a = ψ₁.code ∧ b = ψ₂.code := nfCodeShape_imp h

theorem traceW_sb_entry {x y : ℕ} {s t : ZFSet.{u}}
    (ht : TraceW ωZ SbAtomR SbImpR SbAllR (ZFSet.pair (natZ x) (natZ y)) s t) :
    ∀ n e v, ZFSet.pair (natZ n) e ∈ s → ZFSet.pair (natZ n) v ∈ t →
      ∃ φ : Fm, e = φ.code ∧ v = ZFSet.pair φ.code (Fm.subst x y φ).code := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro e v he hv
  obtain ⟨v', hv', H⟩ := ht.2 _ _ he
  obtain rfl : v' = v := ht.1.2 _ _ _ hv' hv
  rcases H with hA | ⟨k₁, hk₁, k₂, hk₂, e₁, e₂, v₁, v₂, h₁, h₂, g₁, g₂, rfl, HI⟩ |
    ⟨k₁, hk₁, e₁, v₁, i, hi, h₁, g₁, rfl, HU⟩
  · -- atomic
    rcases hA with ⟨hb, rfl⟩ | ⟨x', -, y', -, i, hi, j, hj, i', -, j', -, r, -, b, -,
        hp, hi', hj', rfl, Hshape⟩
    · exact ⟨Fm.falsum, hb, by rw [hb]; rfl⟩
    · rw [ZFSet.pair_inj] at hp
      obtain ⟨rfl, rfl⟩ := hp
      obtain ⟨i₀, rfl⟩ := mem_ωZ_iff.mp hi
      obtain ⟨j₀, rfl⟩ := mem_ωZ_iff.mp hj
      have hii : i' = natZ (Fm.sb x y i₀) := by
        rcases hi' with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
        · rw [Fm.sb, if_pos (natZ_injective h1)]
        · rw [Fm.sb, if_neg (fun hh => h1 (by rw [hh]))]
      have hjj : j' = natZ (Fm.sb x y j₀) := by
        rcases hj' with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
        · rw [Fm.sb, if_pos (natZ_injective h1)]
        · rw [Fm.sb, if_neg (fun hh => h1 (by rw [hh]))]
      subst hii; subst hjj
      rcases Hshape with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨Fm.eq i₀ j₀, rfl, rfl⟩
      · exact ⟨Fm.mem i₀ j₀, rfl, rfl⟩
  · -- imp
    obtain ⟨n₁, hn₁, rfl⟩ := mem_natZ_iff.mp hk₁
    obtain ⟨n₂, hn₂, rfl⟩ := mem_natZ_iff.mp hk₂
    obtain ⟨φ₁, rfl, rfl⟩ := ih n₁ hn₁ e₁ v₁ h₁ g₁
    obtain ⟨φ₂, rfl, rfl⟩ := ih n₂ hn₂ e₂ v₂ h₂ g₂
    obtain ⟨q₁, -, a₁, -, b₁, -, q₂, -, a₂, -, b₂, -, r, -, A, -, B, -,
      hv₁, hv₂, rfl, hA', hB'⟩ := HI
    rw [ZFSet.pair_inj] at hv₁ hv₂
    obtain ⟨rfl, rfl⟩ := hv₁
    obtain ⟨rfl, rfl⟩ := hv₂
    exact ⟨Fm.imp φ₁ φ₂, rfl, by rw [hA', hB']; rfl⟩
  · -- all
    obtain ⟨n₁, hn₁, rfl⟩ := mem_natZ_iff.mp hk₁
    obtain ⟨φ₁, rfl, rfl⟩ := ih n₁ hn₁ e₁ v₁ h₁ g₁
    obtain ⟨i₀, rfl⟩ := mem_ωZ_iff.mp hi
    obtain ⟨x', -, y', -, q₁, -, a₁, -, b₁, -, r, -, A, -, B, -,
      hp, hv₁, rfl, hA', hB'⟩ := HU
    rw [ZFSet.pair_inj] at hp hv₁
    obtain ⟨rfl, rfl⟩ := hp
    obtain ⟨rfl, rfl⟩ := hv₁
    refine ⟨Fm.all i₀ φ₁, rfl, ?_⟩
    rcases hB' with ⟨hix, rfl⟩ | ⟨hix, rfl⟩
    · obtain rfl := natZ_injective hix
      rw [hA', Fm.subst_all_of_eq]; rfl
    · rw [hA', Fm.subst_all_of_ne (fun hh => hix (by rw [hh]))]; rfl

/-! ### Completeness -/

open Classical in
/-- The value the rules attach to a code: the pair of the code and the code of its substitution
instance. -/
noncomputable def sbValZ (x y : ℕ) (e : ZFSet.{u}) : ZFSet.{u} :=
  if h : ∃ φ : Fm, e = φ.code then ZFSet.pair e (Fm.subst x y h.choose).code
  else ZFSet.pair e e

theorem sbValZ_code (x y : ℕ) (φ : Fm) :
    sbValZ.{u} x y φ.code = ZFSet.pair φ.code (Fm.subst x y φ).code := by
  have h : ∃ ψ : Fm, (φ.code : ZFSet.{u}) = ψ.code := ⟨φ, rfl⟩
  rw [sbValZ, dif_pos h]
  have : h.choose = φ := (Fm.code_injective h.choose_spec).symm
  rw [this]

theorem sbValZ_mem_Lω (x y : ℕ) {e : ZFSet.{u}} (he : ∃ φ : Fm, e = φ.code) :
    sbValZ.{u} x y e ∈ L Ordinal.omega0 := by
  obtain ⟨φ, rfl⟩ := he
  rw [sbValZ_code]
  exact kpair_mem_Lω φ.code_mem_Lω (Fm.subst x y φ).code_mem_Lω

theorem traceW_sb_seqOf_der (x y : ℕ) (φ : Fm) :
    TraceW ωZ.{u} SbAtomR SbImpR SbAllR (ZFSet.pair (natZ x) (natZ y))
      (seqOfAux 0 (Fm.der.{u} φ)) (seqOfAux 0 ((Fm.der.{u} φ).map (sbValZ x y))) := by
  refine ⟨isFunc_seqOfAux _, ?_⟩
  intro k e hke
  obtain ⟨n, z, hz, hp⟩ := mem_seqOfAux.mp hke
  rw [ZFSet.pair_inj] at hp
  obtain ⟨hk, he⟩ := hp
  subst hk
  subst he
  have key : ∀ (m : ℕ) (y' : ZFSet.{u}), (Fm.der.{u} φ)[m]? = some y' →
      ZFSet.pair (natZ m) (sbValZ x y y') ∈ seqOfAux 0 ((Fm.der.{u} φ).map (sbValZ x y)) := by
    intro m y' hy'
    exact mem_seqOfAux.mpr ⟨m, sbValZ x y y', by simp [hy'], by simp⟩
  have keys : ∀ (m : ℕ) (y' : ZFSet.{u}), (Fm.der.{u} φ)[m]? = some y' →
      ZFSet.pair (natZ m) y' ∈ seqOfAux 0 (Fm.der.{u} φ) := by
    intro m y' hy'
    exact mem_seqOfAux.mpr ⟨m, y', hy', by simp⟩
  refine ⟨sbValZ x y e, by simpa using key n e hz, ?_⟩
  have hzmem : e ∈ Fm.der.{u} φ := by
    obtain ⟨hn, hh⟩ := List.getElem?_eq_some_iff.mp hz
    exact hh ▸ List.getElem_mem hn
  obtain ⟨ψ₀, rfl⟩ := Fm.mem_der.{u} φ e hzmem
  obtain ⟨y', hy', H⟩ := Fm.der_good.{u} φ n ψ₀.code hz
  rw [hz] at hy'
  obtain rfl := Option.some.inj hy'
  rcases H with H | ⟨n₁, hn₁, n₂, hn₂, y₁, y₂, hy₁, hy₂, H⟩ | ⟨n₁, hn₁, y₁, i, hy₁, H⟩
  · rw [sbValZ_code]
    exact Or.inl (sbAtomR_of_atomic x y H)
  · obtain ⟨ψ₁, ψ₂, rfl, rfl, rfl⟩ := sbCodeShape_imp H
    refine Or.inr (Or.inl ⟨natZ n₁, by simpa [natZ_mem_natZ_iff] using hn₁, natZ n₂,
      by simpa [natZ_mem_natZ_iff] using hn₂, ψ₁.code, ψ₂.code, sbValZ x y ψ₁.code,
      sbValZ x y ψ₂.code, keys _ _ hy₁, keys _ _ hy₂, key _ _ hy₁, key _ _ hy₂, rfl, ?_⟩)
    rw [sbValZ_code, sbValZ_code, sbValZ_code]
    exact sbImpR_intro x y ψ₁ ψ₂
  · obtain ⟨ψ₁, rfl, rfl⟩ := nfCodeShape_all H
    refine Or.inr (Or.inr ⟨natZ n₁, by simpa [natZ_mem_natZ_iff] using hn₁, ψ₁.code,
      sbValZ x y ψ₁.code, natZ i, natZ_mem_ωZ i, keys _ _ hy₁, key _ _ hy₁, rfl, ?_⟩)
    rw [sbValZ_code, sbValZ_code]
    exact sbAllR_intro x y i ψ₁

/-! ### Lemma 12.2 (1) for substitution -/

/-- Correctness of the instance: `SubstW` holds exactly of the code of a formula and the code of
its substitution instance.  Combined with `delta0_substW`, this is Lemma 12.2 (1) for
substitution: the graph of `φ ↦ φ[x := y]` on codes is Δ₀. -/
theorem substW_iff (x y : ℕ) (e d : ZFSet.{u}) :
    SubstW (L Ordinal.omega0) ωZ (ZFSet.pair (natZ x) (natZ y)) e d ↔
      ∃ φ : Fm, e = φ.code ∧ d = (Fm.subst x y φ).code := by
  rw [substW_iff_graphW]
  constructor
  · rintro ⟨s, -, t, -, hs, ht, k, hke, hkd⟩
    obtain ⟨dm, hdm, hdom⟩ := hs.2.1
    have hkd' : k ∈ dm := (hdom k).mpr ⟨e, hke⟩
    obtain ⟨M, rfl⟩ := mem_ωZ_iff.mp hdm
    obtain ⟨q, -, rfl⟩ := mem_natZ_iff.mp hkd'
    obtain ⟨φ, rfl, hval⟩ := traceW_sb_entry ht q e _ hke hkd
    rw [ZFSet.pair_inj] at hval
    exact ⟨φ, rfl, hval.2⟩
  · rintro ⟨φ, rfl, rfl⟩
    refine ⟨seqOfAux 0 (Fm.der.{u} φ), ?_,
      seqOfAux 0 ((Fm.der.{u} φ).map (sbValZ x y)), ?_,
      derSeqW_seqOf_der φ, traceW_sb_seqOf_der x y φ,
      natZ ((Fm.der.{u} φ).length - 1), ?_, ?_⟩
    · apply seqOfAux_mem_Lω
      intro w hw
      obtain ⟨ψ, rfl⟩ := Fm.mem_der.{u} φ w hw
      exact ψ.code_mem_Lω
    · apply seqOfAux_mem_Lω
      intro w hw
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw
      exact sbValZ_mem_Lω x y (Fm.mem_der.{u} φ z hz)
    · exact mem_seqOfAux.mpr ⟨(Fm.der.{u} φ).length - 1, φ.code, Fm.der_last.{u} φ, by simp⟩
    · refine mem_seqOfAux.mpr ⟨(Fm.der.{u} φ).length - 1,
        ZFSet.pair φ.code (Fm.subst x y φ).code, ?_, by simp⟩
      rw [List.getElem?_map, Fm.der_last.{u} φ]
      exact congrArg some (sbValZ_code x y φ)

end BM4.ST
