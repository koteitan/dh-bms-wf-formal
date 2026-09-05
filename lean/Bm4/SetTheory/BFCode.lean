/-
  Part III: codes of block formulas, Δ₀ recognizers for codes of Δ₀ formulas and of Δ₀ block
  formulas, and the Δ₀ projections (block variable sequence, body).  The recognizers for the
  codes of Σ̂q / Π̂q block formulas live in `Bm4.SetTheory.BFCodeD`, where — as Definition 12.1
  requires — every quantifier block is asked to consist of pairwise distinct variables.
-/
import Bm4.SetTheory.Code
import Bm4.SetTheory.BF

universe u

namespace BM4.ST

open Fm

/-! ### Finite sequences of naturals -/

/-- A finite sequence (function with domain `natZ l.length`) built from a list of naturals:
pairs `⟨natZ k, natZ (l.get k)⟩`. -/
def seqOfNats (l : List ℕ) : ZFSet.{u} := seqOfAux 0 (l.map natZ.{u})

theorem getElem?_map_natZ {l : List ℕ} {n i : ℕ} :
    (l.map natZ.{u})[n]? = some (natZ.{u} i) ↔ l[n]? = some i := by
  rw [List.getElem?_map]
  cases h : l[n]? with
  | none => simp
  | some j => simp [natZ_injective.eq_iff]

theorem mem_seqOfNats {l : List ℕ} {n i : ℕ} :
    ZFSet.pair (natZ.{u} n) (natZ.{u} i) ∈ seqOfNats.{u} l ↔ l[n]? = some i := by
  rw [seqOfNats, mem_seqOfAux]
  constructor
  · rintro ⟨m, x, hx, hp⟩
    rw [ZFSet.pair_inj] at hp
    obtain ⟨h1, rfl⟩ := hp
    have hnm : n = m := by have := natZ_injective h1; omega
    subst hnm
    exact getElem?_map_natZ.mp hx
  · intro h
    exact ⟨n, natZ i, getElem?_map_natZ.mpr h, by simp⟩

theorem seqOfNats_mem_Lω (l : List ℕ) : seqOfNats.{u} l ∈ L Ordinal.omega0 := by
  apply seqOfAux_mem_Lω
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact natZ_mem_Lω i

theorem seqOfNats_injective : Function.Injective seqOfNats.{u} := by
  intro l l' h
  apply List.ext_getElem?
  intro n
  cases hl : l[n]? with
  | none =>
    cases hl' : l'[n]? with
    | none => rfl
    | some j =>
      have hm : ZFSet.pair (natZ.{u} n) (natZ.{u} j) ∈ seqOfNats.{u} l' := mem_seqOfNats.mpr hl'
      rw [← h, mem_seqOfNats, hl] at hm
      exact absurd hm (by simp)
  | some i =>
    have hm : ZFSet.pair (natZ.{u} n) (natZ.{u} i) ∈ seqOfNats.{u} l := mem_seqOfNats.mpr hl
    rw [h, mem_seqOfNats] at hm
    exact hm.symm

/-! ### Codes of block formulas -/

/-- Codes of block formulas: `delta sg φ ↦ ⟨natZ 0, ⟨natZ (if sg then 1 else 0), φ.code⟩⟩`,
`exs l ψ ↦ ⟨natZ 1, ⟨seqOfNats l, ψ.code⟩⟩`, `alls l ψ ↦ ⟨natZ 2, ⟨seqOfNats l, ψ.code⟩⟩`. -/
def BF.code : BF → ZFSet.{u}
  | .delta sg φ => ZFSet.pair (natZ 0) (ZFSet.pair (natZ (if sg then 1 else 0)) φ.code)
  | .exs l ψ => ZFSet.pair (natZ 1) (ZFSet.pair (seqOfNats l) (BF.code ψ))
  | .alls l ψ => ZFSet.pair (natZ 2) (ZFSet.pair (seqOfNats l) (BF.code ψ))

theorem BF.code_injective : Function.Injective BF.code.{u} := by
  intro a
  induction a with
  | delta sg φ =>
    intro b h
    cases b with
    | delta sg' φ' =>
      simp only [BF.code, ZFSet.pair_inj] at h
      obtain ⟨-, h1, h2⟩ := h
      have hs := natZ_injective h1
      have hsg : sg = sg' := by cases sg <;> cases sg' <;> revert hs <;> decide
      rw [hsg, Fm.code_injective h2]
    | exs l ψ => simp only [BF.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
    | alls l ψ => simp only [BF.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | exs l ψ ih =>
    intro b h
    cases b with
    | delta sg' φ' => simp only [BF.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
    | exs l' ψ' =>
      simp only [BF.code, ZFSet.pair_inj] at h
      obtain ⟨-, h1, h2⟩ := h
      rw [seqOfNats_injective h1, ih h2]
    | alls l' ψ' => simp only [BF.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | alls l ψ ih =>
    intro b h
    cases b with
    | delta sg' φ' => simp only [BF.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
    | exs l' ψ' => simp only [BF.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
    | alls l' ψ' =>
      simp only [BF.code, ZFSet.pair_inj] at h
      obtain ⟨-, h1, h2⟩ := h
      rw [seqOfNats_injective h1, ih h2]

theorem BF.code_mem_Lω (b : BF) : b.code ∈ L Ordinal.omega0.{u} := by
  induction b with
  | delta sg φ =>
    exact kpair_mem_Lω (natZ_mem_Lω 0) (kpair_mem_Lω (natZ_mem_Lω _) φ.code_mem_Lω)
  | exs l ψ ih => exact kpair_mem_Lω (natZ_mem_Lω 1) (kpair_mem_Lω (seqOfNats_mem_Lω l) ih)
  | alls l ψ ih => exact kpair_mem_Lω (natZ_mem_Lω 2) (kpair_mem_Lω (seqOfNats_mem_Lω l) ih)

/-! ### Codes of Δ₀ formulas -/

/-- Derivation sequences with the Δ₀ discipline: each entry is an atomic code, an `imp` of two
earlier entries, or a bounded quantifier `all i (imp (mem i j) φ')` with `i ≠ j` and `φ'` earlier;
the code shape of the last case is
`pair (natZ 4) (pair i (pair (natZ 3) (pair (pair (natZ 2) (pair i j)) e')))`. -/
def Delta0DerSeqW (w s : ZFSet.{u}) : Prop :=
  IsFunc s ∧ (∃ d ∈ w, IsDom s d) ∧
  ∀ k e, ZFSet.pair k e ∈ s →
    IsAtomicCodeW w e ∨
    (∃ k₁ ∈ k, ∃ k₂ ∈ k, ∃ e₁ e₂, ZFSet.pair k₁ e₁ ∈ s ∧ ZFSet.pair k₂ e₂ ∈ s ∧
      e = ZFSet.pair (natZ 3) (ZFSet.pair e₁ e₂)) ∨
    (∃ k₁ ∈ k, ∃ e₁, ∃ i ∈ w, ∃ j ∈ w, i ≠ j ∧ ZFSet.pair k₁ e₁ ∈ s ∧
      e = ZFSet.pair (natZ 4) (ZFSet.pair i (ZFSet.pair (natZ 3)
        (ZFSet.pair (ZFSet.pair (natZ 2) (ZFSet.pair i j)) e₁))))

/-- `e` is the code of a Δ₀ formula: it occurs in a Δ₀-disciplined derivation sequence in `h`. -/
def IsDelta0CodeW (h w e : ZFSet.{u}) : Prop :=
  ∃ s ∈ h, Delta0DerSeqW w s ∧ ∃ k, ZFSet.pair k e ∈ s

theorem delta0_delta0DerSeqW (w s : ℕ) (hws : w ≠ s) :
    Delta0Def {w, s} (fun _ v => Delta0DerSeqW (v w) (v s)) := by
  set m := w + s + 1 with hm
  have h1 := delta0_isFunc s
  have h2 := (delta0_isDom s m (by omega)).bex m w (by omega)
  -- imp case: k₁ := m+6, k₂ := m+7, p₁ := m+8, q₁ := m+9, e₁ := m+10,
  --           p₂ := m+11, q₂ := m+12, e₂ := m+13
  have i0 := (delta0_isKPair (m + 8) (m + 6) (m + 10) (by omega) (by omega)).and
    ((delta0_isKPair (m + 11) (m + 7) (m + 13) (by omega) (by omega)).and
      (delta0_tagPair 3 (m + 5) (m + 10) (m + 13) (by omega) (by omega)))
  have i1 := i0.bex (m + 13) (m + 12) (by omega)
  have i2 := i1.bex (m + 12) (m + 11) (by omega)
  have i3 := i2.bex (m + 11) s (by omega)
  have i4 := i3.bex (m + 10) (m + 9) (by omega)
  have i5 := i4.bex (m + 9) (m + 8) (by omega)
  have i6 := i5.bex (m + 8) s (by omega)
  have i7 := i6.bex (m + 7) (m + 3) (by omega)
  have iC := i7.bex (m + 6) (m + 3) (by omega)
  -- ball case: k₁ := m+20, p₁ := m+21, q₁ := m+22, e₁ := m+23, i := m+24, j := m+25,
  --   qa := m+26, X := m+27, r := m+28, B := m+29, qb := m+30, Y := m+31, r2 := m+32, C := m+33
  have a0 := (delta0_isKPair (m + 21) (m + 20) (m + 23) (by omega) (by omega)).and
    (((Delta0Def.eq (m + 24) (m + 25)).not).and
      ((delta0_tagPair 2 (m + 33) (m + 24) (m + 25) (by omega) (by omega)).and
        ((delta0_tagPair 3 (m + 29) (m + 33) (m + 23) (by omega) (by omega)).and
          (delta0_tagPair 4 (m + 5) (m + 24) (m + 29) (by omega) (by omega)))))
  have a1 := a0.bex (m + 33) (m + 32) (by omega)
  have a2 := a1.bex (m + 32) (m + 31) (by omega)
  have a3 := a2.bex (m + 31) (m + 30) (by omega)
  have a4 := a3.bex (m + 30) (m + 29) (by omega)
  have a5 := a4.bex (m + 29) (m + 28) (by omega)
  have a6 := a5.bex (m + 28) (m + 27) (by omega)
  have a7 := a6.bex (m + 27) (m + 26) (by omega)
  have a8 := a7.bex (m + 26) (m + 5) (by omega)
  have a9 := a8.bex (m + 25) w (by omega)
  have a10 := a9.bex (m + 24) w (by omega)
  have a11 := a10.bex (m + 23) (m + 22) (by omega)
  have a12 := a11.bex (m + 22) (m + 21) (by omega)
  have a13 := a12.bex (m + 21) s (by omega)
  have aC := a13.bex (m + 20) (m + 3) (by omega)
  have c0 := (delta0_isKPair (m + 1) (m + 3) (m + 5) (by omega) (by omega)).imp
    ((delta0_isAtomicCodeW w (m + 5) (by omega)).or (iC.or aC))
  have c1 := c0.ball (m + 5) (m + 4) (by omega)
  have c2 := c1.ball (m + 4) (m + 1) (by omega)
  have c3 := c2.ball (m + 3) (m + 2) (by omega)
  have c4 := c3.ball (m + 2) (m + 1) (by omega)
  have h3 := c4.ball (m + 1) s (by omega)
  refine ((h1.and (h2.and h3)).congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    unfold Delta0DerSeqW
    refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
    rw [forall_pair_mem_iff_bounded]
    apply forall_congr'; intro p; apply imp_congr_right; intro _
    apply forall_congr'; intro q; apply imp_congr_right; intro _
    apply forall_congr'; intro k; apply imp_congr_right; intro _
    apply forall_congr'; intro q'; apply imp_congr_right; intro _
    apply forall_congr'; intro e; apply imp_congr_right; intro _
    apply imp_congr_right; intro _
    apply or_congr Iff.rfl
    apply or_congr
    · apply exists_congr; intro k₁; apply and_congr_right; intro _
      apply exists_congr; intro k₂; apply and_congr_right; intro _
      constructor
      · rintro ⟨p₁, hp₁, q₁, _, e₁, _, p₂, hp₂, q₂, _, e₂, _, rfl, rfl, H⟩
        exact ⟨e₁, e₂, hp₁, hp₂, H⟩
      · rintro ⟨e₁, e₂, h₁, h₂, H⟩
        exact ⟨_, h₁, _, upair_mem_pair _ _, e₁, mem_upair_right _ _, _, h₂, _, upair_mem_pair _ _,
          e₂, mem_upair_right _ _, rfl, rfl, H⟩
    · apply exists_congr; intro k₁; apply and_congr_right; intro _
      constructor
      · rintro ⟨p₁, hp₁, q₁, _, e₁, _, i, hi, j, hj, qa, _, X, _, r, _, B, _,
          qb, _, Y, _, r₂, _, C, _, rfl, hij, rfl, rfl, H⟩
        exact ⟨e₁, i, hi, j, hj, hij, hp₁, H⟩
      · rintro ⟨e₁, i, hi, j, hj, hij, h₁, H⟩
        exact ⟨_, h₁, _, upair_mem_pair _ _, e₁, mem_upair_right _ _, i, hi, j, hj,
          _, by rw [H]; exact upair_mem_pair _ _, _, mem_upair_right _ _,
          _, upair_mem_pair _ _, _, mem_upair_right _ _,
          _, upair_mem_pair _ _, _, mem_upair_right _ _,
          _, upair_mem_pair _ _, _, mem_upair_left _ _, rfl, hij, rfl, rfl, H⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

theorem delta0_isDelta0CodeW (h w e : ℕ) (hhw : h ≠ w) (hhe : h ≠ e) (hwe : w ≠ e) :
    Delta0Def {h, w, e} (fun _ v => IsDelta0CodeW (v h) (v w) (v e)) := by
  set m := h + w + e + 1 with hm
  have k0 := delta0_isKPair (m + 1) (m + 3) e (by omega) (by omega)
  have k1 := k0.bex (m + 3) (m + 2) (by omega)
  have k2 := k1.bex (m + 2) (m + 1) (by omega)
  have k3 := k2.bex (m + 1) m (by omega)
  have d := (delta0_delta0DerSeqW w m (by omega)).and k3
  have hh := d.bex m h (by omega)
  refine (hh.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    unfold IsDelta0CodeW
    apply exists_congr; intro s; apply and_congr_right; intro _
    apply and_congr_right; intro _
    constructor
    · rintro ⟨p, hp, q, _, k, _, rfl⟩; exact ⟨k, hp⟩
    · rintro ⟨k, hk⟩
      exact ⟨_, hk, _, singleton_mem_pair _ _, k, ZFSet.mem_singleton.mpr rfl, rfl⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-! ### Correctness of the Δ₀-code recognizer -/

theorem code_ball (i j : ℕ) (φ : Fm) : Fm.code.{u} (Fm.ball i j φ) =
    ZFSet.pair (natZ 4) (ZFSet.pair (natZ i) (ZFSet.pair (natZ 3)
      (ZFSet.pair (ZFSet.pair (natZ 2) (ZFSet.pair (natZ i) (natZ j))) (Fm.code.{u} φ)))) := rfl

/-- Position `n` of `l` is atomic, an `imp` of earlier positions, or a bounded quantifier over an
earlier position. -/
def GoodD (l : List ZFSet.{u}) (n : ℕ) : Prop :=
  ∃ x, l[n]? = some x ∧
    (IsAtomicCodeW ωZ x ∨
    (∃ n₁ < n, ∃ n₂ < n, ∃ x₁ x₂, l[n₁]? = some x₁ ∧ l[n₂]? = some x₂ ∧
      x = ZFSet.pair (natZ 3) (ZFSet.pair x₁ x₂)) ∨
    (∃ n₁ < n, ∃ x₁, ∃ i j : ℕ, i ≠ j ∧ l[n₁]? = some x₁ ∧
      x = ZFSet.pair (natZ 4) (ZFSet.pair (natZ i) (ZFSet.pair (natZ 3)
        (ZFSet.pair (ZFSet.pair (natZ 2) (ZFSet.pair (natZ i) (natZ j))) x₁)))))

theorem goodD_append_left {l₁ : List ZFSet.{u}} (l₂ : List ZFSet.{u}) {n : ℕ} (h : GoodD l₁ n) :
    GoodD (l₁ ++ l₂) n := by
  obtain ⟨x, hx, H⟩ := h
  have hn : n < l₁.length := (List.getElem?_eq_some_iff.mp hx).1
  refine ⟨x, by rw [List.getElem?_append_left hn]; exact hx, ?_⟩
  rcases H with H | ⟨n₁, h₁, n₂, h₂, x₁, x₂, hx₁, hx₂, H⟩ | ⟨n₁, h₁, x₁, i, j, hij, hx₁, H⟩
  · exact Or.inl H
  · exact Or.inr (Or.inl ⟨n₁, h₁, n₂, h₂, x₁, x₂,
      by rw [List.getElem?_append_left (by omega)]; exact hx₁,
      by rw [List.getElem?_append_left (by omega)]; exact hx₂, H⟩)
  · exact Or.inr (Or.inr ⟨n₁, h₁, x₁, i, j, hij,
      by rw [List.getElem?_append_left (by omega)]; exact hx₁, H⟩)

theorem goodD_append_right (l₁ : List ZFSet.{u}) {l₂ : List ZFSet.{u}} {n : ℕ} (h : GoodD l₂ n) :
    GoodD (l₁ ++ l₂) (l₁.length + n) := by
  obtain ⟨x, hx, H⟩ := h
  have key : ∀ m x', l₂[m]? = some x' → (l₁ ++ l₂)[l₁.length + m]? = some x' := by
    intro m x' hm
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    exact hm
  refine ⟨x, key n x hx, ?_⟩
  rcases H with H | ⟨n₁, h₁, n₂, h₂, x₁, x₂, hx₁, hx₂, H⟩ | ⟨n₁, h₁, x₁, i, j, hij, hx₁, H⟩
  · exact Or.inl H
  · exact Or.inr (Or.inl ⟨l₁.length + n₁, by omega, l₁.length + n₂, by omega, x₁, x₂,
      key _ _ hx₁, key _ _ hx₂, H⟩)
  · exact Or.inr (Or.inr ⟨l₁.length + n₁, by omega, x₁, i, j, hij, key _ _ hx₁, H⟩)

/-- Every Δ₀ formula has a Δ₀-disciplined derivation list ending with its code. -/
theorem exists_delta0Der {φ : Fm} (h : IsDelta0 φ) :
    ∃ l : List ZFSet.{u}, (∀ x ∈ l, x ∈ L Ordinal.omega0) ∧ 0 < l.length ∧
      l[l.length - 1]? = some (Fm.code.{u} φ) ∧ ∀ n, n < l.length → GoodD l n := by
  induction h with
  | falsum =>
    refine ⟨[Fm.code.{u} .falsum], ?_, by simp, by simp, ?_⟩
    · intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact Fm.code_mem_Lω _
    · intro n hn
      have hn1 : n < 1 := by simpa using hn
      have : n = 0 := by omega
      subst this
      exact ⟨_, rfl, Or.inl isAtomicCodeW_code_atomic.{u}.1⟩
  | eq i j =>
    refine ⟨[Fm.code.{u} (.eq i j)], ?_, by simp, by simp, ?_⟩
    · intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact Fm.code_mem_Lω _
    · intro n hn
      have hn1 : n < 1 := by simpa using hn
      have : n = 0 := by omega
      subst this
      exact ⟨_, rfl, Or.inl (isAtomicCodeW_code_atomic.{u}.2.1 i j)⟩
  | mem i j =>
    refine ⟨[Fm.code.{u} (.mem i j)], ?_, by simp, by simp, ?_⟩
    · intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact Fm.code_mem_Lω _
    · intro n hn
      have hn1 : n < 1 := by simpa using hn
      have : n = 0 := by omega
      subst this
      exact ⟨_, rfl, Or.inl (isAtomicCodeW_code_atomic.{u}.2.2 i j)⟩
  | @imp φ ψ hφ hψ ih₁ ih₂ =>
    obtain ⟨l₁, hm₁, hp₁, hl₁, hg₁⟩ := ih₁
    obtain ⟨l₂, hm₂, hp₂, hl₂, hg₂⟩ := ih₂
    refine ⟨l₁ ++ (l₂ ++ [Fm.code.{u} (.imp φ ψ)]), ?_, ?_, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | hx | rfl
      · exact hm₁ x hx
      · exact hm₂ x hx
      · exact Fm.code_mem_Lω _
    · simp only [List.length_append, List.length_singleton]; omega
    · simp only [List.length_append, List.length_singleton]
      rw [List.getElem?_append_right (by omega)]
      have he : l₁.length + (l₂.length + 1) - 1 - l₁.length = l₂.length := by omega
      rw [he, List.getElem?_concat_length]
    · intro n hn
      simp only [List.length_append, List.length_singleton] at hn
      rcases lt_or_ge n l₁.length with h1 | h1
      · exact goodD_append_left _ (hg₁ n h1)
      rcases lt_or_ge n (l₁.length + l₂.length) with h2 | h2
      · have hgg := goodD_append_right l₁
          (goodD_append_left [Fm.code.{u} (.imp φ ψ)] (hg₂ (n - l₁.length) (by omega)))
        rwa [Nat.add_sub_cancel' h1] at hgg
      · have hn0 : n = l₁.length + l₂.length := by omega
        subst hn0
        refine ⟨Fm.code.{u} (.imp φ ψ), ?_, Or.inr (Or.inl ⟨l₁.length - 1, by omega,
          l₁.length + (l₂.length - 1), by omega, Fm.code.{u} φ, Fm.code.{u} ψ, ?_, ?_, rfl⟩)⟩
        · rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
            List.getElem?_concat_length]
        · rw [List.getElem?_append_left (by omega)]; exact hl₁
        · rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
            List.getElem?_append_left (by omega)]
          exact hl₂
  | @ball i j hij φ hφ ih =>
    obtain ⟨l₁, hm₁, hp₁, hl₁, hg₁⟩ := ih
    refine ⟨l₁ ++ [Fm.code.{u} (Fm.ball i j φ)], ?_, ?_, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hm₁ x hx
      · exact Fm.code_mem_Lω _
    · simp only [List.length_append, List.length_singleton]; omega
    · simp only [List.length_append, List.length_singleton]
      have he : l₁.length + 1 - 1 = l₁.length := by omega
      rw [he, List.getElem?_concat_length]
    · intro n hn
      simp only [List.length_append, List.length_singleton] at hn
      rcases lt_or_ge n l₁.length with h1 | h1
      · exact goodD_append_left _ (hg₁ n h1)
      · have hn0 : n = l₁.length := by omega
        subst hn0
        refine ⟨Fm.code.{u} (Fm.ball i j φ), List.getElem?_concat_length,
          Or.inr (Or.inr ⟨l₁.length - 1, by omega, Fm.code.{u} φ, i, j, hij, ?_, code_ball i j φ⟩)⟩
        rw [List.getElem?_append_left (by omega)]
        exact hl₁

/-- The sequence built from a Δ₀-disciplined list is a Δ₀ derivation sequence. -/
theorem delta0DerSeqW_seqOfAux {l : List ZFSet.{u}} (hg : ∀ n, n < l.length → GoodD l n) :
    Delta0DerSeqW ωZ (seqOfAux 0 l) := by
  refine ⟨⟨?_, ?_⟩, ⟨natZ l.length, natZ_mem_ωZ _, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨n, x, _, rfl⟩ := mem_seqOfAux.mp hp
    exact ⟨_, _, rfl⟩
  · intro a b b' hab hab'
    obtain ⟨n, x, hx, hp⟩ := mem_seqOfAux.mp hab
    obtain ⟨n', x', hx', hp'⟩ := mem_seqOfAux.mp hab'
    rw [ZFSet.pair_inj] at hp hp'
    obtain ⟨rfl, rfl⟩ := hp
    obtain ⟨ha, rfl⟩ := hp'
    have hnn : n = n' := by simpa using natZ_injective ha
    subst hnn
    rw [hx] at hx'
    exact Option.some.inj hx'
  · intro a
    rw [mem_natZ_iff]
    constructor
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨x, hx⟩ : ∃ x, l[m]? = some x := ⟨l[m], List.getElem?_eq_some_iff.mpr ⟨hm, rfl⟩⟩
      exact ⟨x, mem_seqOfAux.mpr ⟨m, x, hx, by simp⟩⟩
    · rintro ⟨b, hb⟩
      obtain ⟨n, x, hx, hp⟩ := mem_seqOfAux.mp hb
      rw [ZFSet.pair_inj] at hp
      exact ⟨n, (List.getElem?_eq_some_iff.mp hx).1, by simpa using hp.1⟩
  · intro k e hke
    obtain ⟨n, x, hx, hp⟩ := mem_seqOfAux.mp hke
    rw [ZFSet.pair_inj] at hp
    obtain ⟨hk, he⟩ := hp
    subst hk
    subst he
    obtain ⟨y, hy, H⟩ := hg n (List.getElem?_eq_some_iff.mp hx).1
    rw [hx] at hy
    obtain rfl := Option.some.inj hy
    rcases H with H | ⟨n₁, h₁, n₂, h₂, x₁, x₂, hx₁, hx₂, H⟩ | ⟨n₁, h₁, x₁, i, j, hij, hx₁, H⟩
    · exact Or.inl H
    · exact Or.inr (Or.inl ⟨natZ n₁, by simpa [natZ_mem_natZ_iff] using h₁, natZ n₂,
        by simpa [natZ_mem_natZ_iff] using h₂, x₁, x₂,
        mem_seqOfAux.mpr ⟨n₁, x₁, hx₁, by simp⟩, mem_seqOfAux.mpr ⟨n₂, x₂, hx₂, by simp⟩, H⟩)
    · exact Or.inr (Or.inr ⟨natZ n₁, by simpa [natZ_mem_natZ_iff] using h₁, x₁, natZ i,
        natZ_mem_ωZ i, natZ j, natZ_mem_ωZ j, fun hE => hij (natZ_injective hE),
        mem_seqOfAux.mpr ⟨n₁, x₁, hx₁, by simp⟩, H⟩)

/-- Every entry of a Δ₀ derivation sequence (over `ωZ`) is the code of a Δ₀ formula. -/
theorem delta0DerSeqW_entry_isDelta0Code {s : ZFSet.{u}} (hs : Delta0DerSeqW ωZ s) :
    ∀ n e, ZFSet.pair (natZ n) e ∈ s → ∃ φ : Fm, IsDelta0 φ ∧ e = Fm.code.{u} φ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro e he
  rcases hs.2.2 _ _ he with H | ⟨k₁, hk₁, k₂, hk₂, e₁, e₂, h₁, h₂, rfl⟩ |
    ⟨k₁, hk₁, e₁, i, hi, j, hj, hij, h₁, rfl⟩
  · rcases H with rfl | ⟨i, hi, j, hj, H⟩
    · exact ⟨.falsum, IsDelta0.falsum, rfl⟩
    · obtain ⟨i', rfl⟩ := mem_ωZ_iff.mp hi
      obtain ⟨j', rfl⟩ := mem_ωZ_iff.mp hj
      rcases H with rfl | rfl
      · exact ⟨.eq i' j', IsDelta0.eq _ _, rfl⟩
      · exact ⟨.mem i' j', IsDelta0.mem _ _, rfl⟩
  · obtain ⟨n₁, hn₁, rfl⟩ := mem_natZ_iff.mp hk₁
    obtain ⟨n₂, hn₂, rfl⟩ := mem_natZ_iff.mp hk₂
    obtain ⟨φ₁, hφ₁, rfl⟩ := ih n₁ hn₁ e₁ h₁
    obtain ⟨φ₂, hφ₂, rfl⟩ := ih n₂ hn₂ e₂ h₂
    exact ⟨.imp φ₁ φ₂, hφ₁.imp hφ₂, rfl⟩
  · obtain ⟨n₁, hn₁, rfl⟩ := mem_natZ_iff.mp hk₁
    obtain ⟨φ₁, hφ₁, rfl⟩ := ih n₁ hn₁ e₁ h₁
    obtain ⟨i', rfl⟩ := mem_ωZ_iff.mp hi
    obtain ⟨j', rfl⟩ := mem_ωZ_iff.mp hj
    exact ⟨Fm.ball i' j' φ₁, IsDelta0.ball (fun hE => hij (by rw [hE])) hφ₁,
      (code_ball i' j' φ₁).symm⟩

/-- Correctness: the codes of Δ₀ formulas are exactly the elements with a Δ₀-disciplined
derivation sequence in `L ω`. -/
theorem isDelta0CodeW_iff (e : ZFSet.{u}) :
    IsDelta0CodeW (L Ordinal.omega0) ωZ e ↔ ∃ φ : Fm, IsDelta0 φ ∧ e = Fm.code.{u} φ := by
  constructor
  · rintro ⟨s, _, hs, k, hk⟩
    obtain ⟨d, hd, hdom⟩ := hs.2.1
    have hkd : k ∈ d := (hdom k).mpr ⟨e, hk⟩
    obtain ⟨N, rfl⟩ := mem_ωZ_iff.mp hd
    obtain ⟨n, _, rfl⟩ := mem_natZ_iff.mp hkd
    exact delta0DerSeqW_entry_isDelta0Code hs n e hk
  · rintro ⟨φ, hφ, rfl⟩
    obtain ⟨l, hmem, hpos, hlast, hg⟩ := exists_delta0Der.{u} hφ
    exact ⟨seqOfAux 0 l, seqOfAux_mem_Lω 0 l hmem, delta0DerSeqW_seqOfAux hg,
      natZ (l.length - 1), mem_seqOfAux.mpr ⟨l.length - 1, Fm.code.{u} φ, hlast, by simp⟩⟩

/-! ### Membership in `seqOfNats` -/

theorem getElem?_map_natZ' {l : List ℕ} {n : ℕ} {x : ZFSet.{u}}
    (h : (l.map natZ.{u})[n]? = some x) : ∃ i, l[n]? = some i ∧ x = natZ.{u} i := by
  rw [List.getElem?_map] at h
  cases hl : l[n]? with
  | none => rw [hl] at h; exact absurd h (by simp)
  | some i => rw [hl] at h; exact ⟨i, rfl, by simpa using h.symm⟩

theorem mem_seqOfNats_iff {l : List ℕ} {p : ZFSet.{u}} :
    p ∈ seqOfNats.{u} l ↔ ∃ n i, l[n]? = some i ∧ p = ZFSet.pair (natZ n) (natZ i) := by
  rw [seqOfNats, mem_seqOfAux]
  constructor
  · rintro ⟨n, x, hx, rfl⟩
    obtain ⟨i, hi, rfl⟩ := getElem?_map_natZ' hx
    exact ⟨n, i, hi, by simp⟩
  · rintro ⟨n, i, hl, rfl⟩
    exact ⟨n, natZ i, getElem?_map_natZ.mpr hl, by simp⟩

theorem getElem?_map_range {α : Type*} (f : ℕ → α) {N mm : ℕ} (h : mm < N) :
    ((List.range N).map f)[mm]? = some (f mm) := by
  rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa using h)]
  simp

/-! ### Recognizer for codes of Δ₀ block formulas -/

/-- `e` codes a signed Δ₀ block formula `delta sg φ`. -/
def IsDeltaBFCodeW (h w e : ZFSet.{u}) : Prop :=
  ∃ sg d, e = ZFSet.pair (natZ 0) (ZFSet.pair sg d) ∧ (sg = natZ 0 ∨ sg = natZ 1) ∧
    IsDelta0CodeW h w d

/-- Δ₀-definability of `∃ a d, e = ⟨natZ t, ⟨a, d⟩⟩ ∧ Q w a ∧ P h w d`. -/
theorem delta0_pairShape (t : ℕ) (h w e : ℕ) (hhw : h ≠ w) (hhe : h ≠ e) (hwe : w ≠ e)
    {Q : ZFSet.{u} → ZFSet.{u} → Prop} {P : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop}
    (hQ : ∀ a : ℕ, h ≠ a → w ≠ a → e ≠ a → Delta0Def.{u} {w, a} (fun _ v => Q (v w) (v a)))
    (hP : ∀ d : ℕ, h ≠ d → w ≠ d → e ≠ d →
      Delta0Def.{u} {h, w, d} (fun _ v => P (v h) (v w) (v d))) :
    Delta0Def.{u} {h, w, e} (fun _ v =>
      ∃ a d, v e = ZFSet.pair (natZ t) (ZFSet.pair a d) ∧ Q (v w) a ∧ P (v h) (v w) d) := by
  set m := h + w + e + 1 with hm
  have b0 := (delta0_tagPair t e (m + 4) (m + 6) (by omega) (by omega)).and
    ((hQ (m + 4) (by omega) (by omega) (by omega)).and
      (hP (m + 6) (by omega) (by omega) (by omega)))
  have b1 := b0.bex (m + 6) (m + 5) (by omega)
  have b2 := b1.bex (m + 5) (m + 2) (by omega)
  have b3 := b2.bex (m + 4) (m + 3) (by omega)
  have b4 := b3.bex (m + 3) (m + 2) (by omega)
  have b5 := b4.bex (m + 2) (m + 1) (by omega)
  have b6 := b5.bex (m + 1) e (by omega)
  refine (b6.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · rintro ⟨qa, _, X, _, r, _, a, _, r', _, d, _, H, hq, hp⟩
      exact ⟨a, d, H, hq, hp⟩
    · rintro ⟨a, d, H, hq, hp⟩
      exact ⟨_, by rw [H]; exact upair_mem_pair _ _, _, mem_upair_right _ _,
        _, upair_mem_pair _ _, a, mem_upair_left _ _,
        _, upair_mem_pair _ _, d, mem_upair_right _ _, H, hq, hp⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

theorem delta0_isDeltaBFCodeW (h w e : ℕ) (hhw : h ≠ w) (hhe : h ≠ e) (hwe : w ≠ e) :
    Delta0Def.{u} {h, w, e} (fun _ v => IsDeltaBFCodeW (v h) (v w) (v e)) := by
  refine (delta0_pairShape (Q := fun _ x => x = natZ 0 ∨ x = natZ 1)
    (P := fun H W d => IsDelta0CodeW H W d) 0 h w e hhw hhe hwe ?_
    (fun d hhd hwd _ => delta0_isDelta0CodeW h w d hhw hhd hwd)).congr (fun _ _ _ _ => ?_)
  · intro a _ _ _
    refine ((delta0_isNatZ 0 a).or (delta0_isNatZ 1 a)).mono ?_
    intro k hk
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert] at hk ⊢
    tauto
  · rfl

/-! ### Correctness of the Δ₀ block-code recognizer -/

theorem isDeltaBFCodeW_iff (e : ZFSet.{u}) :
    IsDeltaBFCodeW (L Ordinal.omega0) ωZ e ↔
      ∃ (sg : Bool) (φ : Fm), IsDelta0 φ ∧ e = BF.code.{u} (BF.delta sg φ) := by
  constructor
  · rintro ⟨sgv, d, H, hs, hd⟩
    obtain ⟨φ, hφ, rfl⟩ := (isDelta0CodeW_iff d).mp hd
    rcases hs with rfl | rfl
    · exact ⟨false, φ, hφ, by rw [H]; rfl⟩
    · exact ⟨true, φ, hφ, by rw [H]; rfl⟩
  · rintro ⟨sg, φ, hφ, rfl⟩
    refine ⟨natZ (if sg then 1 else 0), Fm.code.{u} φ, rfl, ?_,
      (isDelta0CodeW_iff _).mpr ⟨φ, hφ, rfl⟩⟩
    cases sg <;> simp

/-! ### Projections of a block code -/

/-- Projections of a block code `⟨t, ⟨ν, d⟩⟩` whose tag `t` is `natZ 1` (`∃`) or `natZ 2` (`∀`):
`ν` is `Vars(e)` and `d` is `Body(e)` in the sense of Definition 12.1, which speaks of an
alternating block formula.  A `Δ₀` block code `⟨natZ 0, ⟨sg, d⟩⟩` carries no block of
variables and is excluded by the tag test. -/
def IsVarsBody (e ν d : ZFSet.{u}) : Prop :=
  e = ZFSet.pair (natZ 1) (ZFSet.pair ν d) ∨ e = ZFSet.pair (natZ 2) (ZFSet.pair ν d)

theorem delta0_isVarsBody (e ν d : ℕ) (hev : e ≠ ν) (hed : e ≠ d) (hvd : ν ≠ d) :
    Delta0Def.{u} {e, ν, d} (fun _ v => IsVarsBody (v e) (v ν) (v d)) :=
  ((delta0_tagPair 1 e ν d hev hed).or (delta0_tagPair 2 e ν d hev hed)).of_eq
    (Finset.union_self _)

theorem isVarsBody_code_exs (l : List ℕ) (ψ : BF) :
    IsVarsBody (BF.code.{u} (BF.exs l ψ)) (seqOfNats.{u} l) (BF.code.{u} ψ) := Or.inl rfl

theorem isVarsBody_code_alls (l : List ℕ) (ψ : BF) :
    IsVarsBody (BF.code.{u} (BF.alls l ψ)) (seqOfNats.{u} l) (BF.code.{u} ψ) := Or.inr rfl

theorem isVarsBody_unique {e ν d ν' d' : ZFSet.{u}} (h : IsVarsBody e ν d)
    (h' : IsVarsBody e ν' d') : ν = ν' ∧ d = d' := by
  rcases h with H | H <;> rcases h' with H' | H' <;>
    (rw [H, ZFSet.pair_inj, ZFSet.pair_inj] at H'; exact ⟨H'.2.1, H'.2.2⟩)

end BM4.ST
