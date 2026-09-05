/-
  Part III, §8: codes of formulas as hereditarily finite sets, derivation sequences,
  Δ₀-definability of "being a code", and correctness.
-/
import Bm4.SetTheory.HF

universe u

namespace BM4.ST

open Fm

/-- Codes of formulas as hereditarily finite sets. -/
def Fm.code : Fm → ZFSet.{u}
  | .falsum => ZFSet.pair (natZ 0) (natZ 0)
  | .eq i j => ZFSet.pair (natZ 1) (ZFSet.pair (natZ i) (natZ j))
  | .mem i j => ZFSet.pair (natZ 2) (ZFSet.pair (natZ i) (natZ j))
  | .imp φ ψ => ZFSet.pair (natZ 3) (ZFSet.pair φ.code ψ.code)
  | .all i φ => ZFSet.pair (natZ 4) (ZFSet.pair (natZ i) φ.code)

theorem natZ_ne {m n : ℕ} (h : m ≠ n) : natZ.{u} m ≠ natZ n := fun e => h (natZ_injective e)

theorem Fm.code_injective : Function.Injective Fm.code.{u} := by
  intro φ
  induction φ with
  | falsum =>
    intro ψ h
    cases ψ <;> simp only [Fm.code, ZFSet.pair_inj] at h <;>
      first | rfl | exact absurd h.1 (natZ_ne (by decide))
  | eq i j =>
    intro ψ h
    cases ψ <;> simp only [Fm.code, ZFSet.pair_inj] at h <;>
      first
      | exact absurd h.1 (natZ_ne (by decide))
      | (obtain ⟨_, h1, h2⟩ := h; rw [natZ_injective h1, natZ_injective h2])
  | mem i j =>
    intro ψ h
    cases ψ <;> simp only [Fm.code, ZFSet.pair_inj] at h <;>
      first
      | exact absurd h.1 (natZ_ne (by decide))
      | (obtain ⟨_, h1, h2⟩ := h; rw [natZ_injective h1, natZ_injective h2])
  | imp φ₁ φ₂ ih₁ ih₂ =>
    intro ψ h
    cases ψ <;> simp only [Fm.code, ZFSet.pair_inj] at h <;>
      first
      | exact absurd h.1 (natZ_ne (by decide))
      | (obtain ⟨_, h1, h2⟩ := h; rw [ih₁ h1, ih₂ h2])
  | all i φ ih =>
    intro ψ h
    cases ψ <;> simp only [Fm.code, ZFSet.pair_inj] at h <;>
      first
      | exact absurd h.1 (natZ_ne (by decide))
      | (obtain ⟨_, h1, h2⟩ := h; rw [natZ_injective h1, ih h2])

theorem natZ_mem_Lω (n : ℕ) : natZ.{u} n ∈ L Ordinal.omega0 := by
  rw [natZ_eq_toZFSet, toZFSet_mem_L_iff]
  exact Ordinal.nat_lt_omega0 n

theorem kpair_mem_Lω {a b : ZFSet.{u}} (ha : a ∈ L Ordinal.omega0) (hb : b ∈ L Ordinal.omega0) :
    ZFSet.pair a b ∈ L Ordinal.omega0 :=
  kpair_mem_L_of_limit Ordinal.isSuccLimit_omega0 ha hb

theorem Fm.code_mem_Lω (φ : Fm) : φ.code ∈ L Ordinal.omega0.{u} := by
  induction φ with
  | falsum => exact kpair_mem_Lω (natZ_mem_Lω 0) (natZ_mem_Lω 0)
  | eq i j => exact kpair_mem_Lω (natZ_mem_Lω 1) (kpair_mem_Lω (natZ_mem_Lω i) (natZ_mem_Lω j))
  | mem i j => exact kpair_mem_Lω (natZ_mem_Lω 2) (kpair_mem_Lω (natZ_mem_Lω i) (natZ_mem_Lω j))
  | imp φ ψ ih₁ ih₂ => exact kpair_mem_Lω (natZ_mem_Lω 3) (kpair_mem_Lω ih₁ ih₂)
  | all i φ ih => exact kpair_mem_Lω (natZ_mem_Lω 4) (kpair_mem_Lω (natZ_mem_Lω i) ih)

/-- `x = natZ k` is Δ₀-definable (no parameters). -/
theorem delta0_isNatZ (k : ℕ) : ∀ x : ℕ, Delta0Def.{u} {x} (fun _ v => v x = natZ k) := by
  induction k with
  | zero =>
    intro x
    exact (delta0_isEmpty x).congr (fun _ _ _ _ => by simp [natZ])
  | succ k ih =>
    intro x
    have h := ((ih (x + 1)).and (delta0_isInsert x (x + 1) (x + 1) (by omega) (by omega))).bex
      (x + 1) x (by omega)
    refine (h.congr ?_).of_eq ?_
    · intro D v _ _
      simp (disch := omega) only [Function.update_self, Function.update_of_ne]
      constructor
      · rintro ⟨y, _, rfl, h⟩; exact h
      · intro H
        refine ⟨natZ k, ?_, rfl, H⟩
        rw [H, natZ]; exact ZFSet.mem_insert _ _
    · ext j; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
        Finset.mem_union]; omega

/-! ### Tagged pairs -/

/-- `e = pair (natZ n) (pair a b)` is Δ₀-definable. -/
theorem delta0_tagPair (n : ℕ) (e a b : ℕ) (hea : e ≠ a) (heb : e ≠ b) :
    Delta0Def {e, a, b} (fun _ v => v e = ZFSet.pair (natZ n) (ZFSet.pair (v a) (v b))) := by
  set m := e + a + b + 1 with hm
  -- `∃ q ∈ e, ∃ t ∈ q, ∃ q' ∈ e, ∃ r ∈ q', t = natZ n ∧ r = pair a b ∧ e = pair t r`
  have h0 := (delta0_isNatZ n (m + 1)).and
    ((delta0_isKPair (m + 3) a b (by omega) (by omega)).and
      (delta0_isKPair e (m + 1) (m + 3) (by omega) (by omega)))
  have h1 := h0.bex (m + 3) (m + 2) (by omega)
  have h2 := h1.bex (m + 2) e (by omega)
  have h3 := h2.bex (m + 1) m (by omega)
  have h := h3.bex m e (by omega)
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · rintro ⟨q, _, t, _, q', _, r, _, rfl, rfl, H⟩; exact H
    · intro H
      exact ⟨_, by rw [H]; exact singleton_mem_pair _ _, natZ n, ZFSet.mem_singleton.mpr rfl,
        _, by rw [H]; exact upair_mem_pair _ _, _, mem_upair_right _ _, rfl, rfl, H⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- `e = pair (natZ 0) (natZ 0)` (the code of `⊥`) is Δ₀-definable. -/
theorem delta0_tagPair0 (e : ℕ) :
    Delta0Def.{u} {e} (fun _ v => v e = ZFSet.pair (natZ 0) (natZ 0)) := by
  set m := e + 1 with hm
  have h0 := (delta0_isNatZ 0 (m + 1)).and (delta0_isKPair e (m + 1) (m + 1) (by omega) (by omega))
  have h1 := h0.bex (m + 1) m (by omega)
  have h := h1.bex m e (by omega)
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · rintro ⟨q, _, t, _, rfl, H⟩; exact H
    · intro H
      exact ⟨_, by rw [H]; exact singleton_mem_pair _ _, natZ 0, ZFSet.mem_singleton.mpr rfl, rfl, H⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-! ### Atomic codes, derivation sequences, codes -/

/-- `e` is an atomic code, with variable indices in the set `w` (intended `w = ωZ`). -/
def IsAtomicCodeW (w e : ZFSet.{u}) : Prop :=
  e = ZFSet.pair (natZ 0) (natZ 0) ∨
  ∃ i ∈ w, ∃ j ∈ w, e = ZFSet.pair (natZ 1) (ZFSet.pair i j) ∨ e = ZFSet.pair (natZ 2) (ZFSet.pair i j)

/-- Derivation sequences: `s` is a function whose domain is an element of `w` (a natural number),
each value being an atomic code or built from values at earlier positions by `imp` or `all`. -/
def DerSeqW (w s : ZFSet.{u}) : Prop :=
  IsFunc s ∧ (∃ d ∈ w, IsDom s d) ∧
  ∀ k e, ZFSet.pair k e ∈ s →
    IsAtomicCodeW w e ∨
    (∃ k₁ ∈ k, ∃ k₂ ∈ k, ∃ e₁ e₂, ZFSet.pair k₁ e₁ ∈ s ∧ ZFSet.pair k₂ e₂ ∈ s ∧
      e = ZFSet.pair (natZ 3) (ZFSet.pair e₁ e₂)) ∨
    (∃ k₁ ∈ k, ∃ e₁, ∃ i ∈ w, ZFSet.pair k₁ e₁ ∈ s ∧ e = ZFSet.pair (natZ 4) (ZFSet.pair i e₁))

/-- `e` is a code: it occurs in a derivation sequence lying in `h` (intended `h = L ω`). -/
def IsCodeW (h w e : ZFSet.{u}) : Prop := ∃ s ∈ h, DerSeqW w s ∧ ∃ k, ZFSet.pair k e ∈ s

theorem delta0_isAtomicCodeW (w e : ℕ) (hwe : w ≠ e) :
    Delta0Def {w, e} (fun _ v => IsAtomicCodeW (v w) (v e)) := by
  set m := w + e + 1 with hm
  have h0 := (delta0_tagPair 1 e m (m + 1) (by omega) (by omega)).or
    (delta0_tagPair 2 e m (m + 1) (by omega) (by omega))
  have h1 := h0.bex (m + 1) w (by omega)
  have h2 := h1.bex m w (by omega)
  have h := (delta0_tagPair0 e).or h2
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    rfl
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- Bounding the components of a pair in `s`. -/
theorem forall_pair_mem_iff_bounded (s : ZFSet.{u}) (P : ZFSet.{u} → ZFSet.{u} → Prop) :
    (∀ k e, ZFSet.pair k e ∈ s → P k e) ↔
      ∀ p ∈ s, ∀ q ∈ p, ∀ k ∈ q, ∀ q' ∈ p, ∀ e ∈ q', p = ZFSet.pair k e → P k e := by
  constructor
  · intro H p hp q _ k _ q' _ e _ hpke
    subst hpke; exact H k e hp
  · intro H k e hke
    exact H _ hke _ (singleton_mem_pair k e) k (ZFSet.mem_singleton.mpr rfl) _
      (upair_mem_pair k e) e (mem_upair_right k e) rfl

theorem exists_pair_mem_iff_bounded (s k : ZFSet.{u}) (P : ZFSet.{u} → Prop) :
    (∃ e, ZFSet.pair k e ∈ s ∧ P e) ↔
      ∃ p ∈ s, ∃ q ∈ p, ∃ e ∈ q, p = ZFSet.pair k e ∧ P e := by
  constructor
  · rintro ⟨e, hke, hP⟩
    exact ⟨_, hke, _, upair_mem_pair k e, e, mem_upair_right k e, rfl, hP⟩
  · rintro ⟨p, hp, q, _, e, _, rfl, hP⟩
    exact ⟨e, hp, hP⟩

theorem delta0_derSeqW (w s : ℕ) (hws : w ≠ s) :
    Delta0Def {w, s} (fun _ v => DerSeqW (v w) (v s)) := by
  set m := w + s + 1 with hm
  have h1 := delta0_isFunc s
  have h2 := (delta0_isDom s m (by omega)).bex m w (by omega)
  -- variables: p := m+1, q := m+2, k := m+3, q' := m+4, e := m+5
  -- imp case: k₁ := m+6, k₂ := m+7, p₁ := m+8, q₁ := m+9, e₁ := m+10, p₂ := m+11, q₂ := m+12, e₂ := m+13
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
  -- all case: k₁ := m+6, p₁ := m+8, q₁ := m+9, e₁ := m+10, i := m+14
  have a0 := (delta0_isKPair (m + 8) (m + 6) (m + 10) (by omega) (by omega)).and
    (delta0_tagPair 4 (m + 5) (m + 14) (m + 10) (by omega) (by omega))
  have a1 := a0.bex (m + 14) w (by omega)
  have a2 := a1.bex (m + 10) (m + 9) (by omega)
  have a3 := a2.bex (m + 9) (m + 8) (by omega)
  have a4 := a3.bex (m + 8) s (by omega)
  have aC := a4.bex (m + 6) (m + 3) (by omega)
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
    unfold DerSeqW
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
      · rintro ⟨p₁, hp₁, q₁, _, e₁, _, i, hi, rfl, H⟩
        exact ⟨e₁, i, hi, hp₁, H⟩
      · rintro ⟨e₁, i, hi, h₁, H⟩
        exact ⟨_, h₁, _, upair_mem_pair _ _, e₁, mem_upair_right _ _, i, hi, rfl, H⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

theorem delta0_isCodeW (h w e : ℕ) (hhw : h ≠ w) (hhe : h ≠ e) (hwe : w ≠ e) :
    Delta0Def {h, w, e} (fun _ v => IsCodeW (v h) (v w) (v e)) := by
  set m := h + w + e + 1 with hm
  -- s := m, p := m+1, q := m+2, k := m+3
  have k0 := delta0_isKPair (m + 1) (m + 3) e (by omega) (by omega)
  have k1 := k0.bex (m + 3) (m + 2) (by omega)
  have k2 := k1.bex (m + 2) (m + 1) (by omega)
  have k3 := k2.bex (m + 1) m (by omega)
  have d := (delta0_derSeqW w m (by omega)).and k3
  have hh := d.bex m h (by omega)
  refine (hh.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    unfold IsCodeW
    apply exists_congr; intro s; apply and_congr_right; intro _
    apply and_congr_right; intro _
    constructor
    · rintro ⟨p, hp, q, _, k, _, rfl⟩; exact ⟨k, hp⟩
    · rintro ⟨k, hk⟩
      exact ⟨_, hk, _, singleton_mem_pair _ _, k, ZFSet.mem_singleton.mpr rfl, rfl⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-! ### Correctness -/

theorem mem_natZ_iff {x : ZFSet.{u}} : ∀ {n : ℕ}, x ∈ natZ n ↔ ∃ m < n, x = natZ m
  | 0 => by simp [natZ]
  | n + 1 => by
    rw [natZ, ZFSet.mem_insert_iff, mem_natZ_iff]
    constructor
    · rintro (rfl | ⟨m, hm, rfl⟩)
      · exact ⟨n, by omega, rfl⟩
      · exact ⟨m, by omega, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
      · exact Or.inr ⟨m, hm, rfl⟩
      · exact Or.inl rfl

/-- The sequence coding a list from position `k` on. -/
def seqOfAux : ℕ → List ZFSet.{u} → ZFSet.{u}
  | _, [] => ∅
  | k, x :: l => insert (ZFSet.pair (natZ k) x) (seqOfAux (k + 1) l)

theorem mem_seqOfAux {p : ZFSet.{u}} : ∀ {k : ℕ} {l : List ZFSet.{u}},
    p ∈ seqOfAux k l ↔ ∃ n x, l[n]? = some x ∧ p = ZFSet.pair (natZ (k + n)) x
  | k, [] => by simp [seqOfAux]
  | k, a :: l => by
    rw [seqOfAux, ZFSet.mem_insert_iff, mem_seqOfAux]
    constructor
    · rintro (rfl | ⟨n, x, hx, rfl⟩)
      · exact ⟨0, a, rfl, by simp⟩
      · exact ⟨n + 1, x, by simpa using hx, by rw [Nat.add_assoc, Nat.add_comm 1 n]⟩
    · rintro ⟨n, x, hx, rfl⟩
      cases n with
      | zero =>
        left
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx; simp
      | succ n =>
        right
        exact ⟨n, x, by simpa using hx, by rw [Nat.add_assoc, Nat.add_comm 1 n]⟩

theorem seqOfAux_mem_Lω : ∀ (k : ℕ) (l : List ZFSet.{u}), (∀ x ∈ l, x ∈ L Ordinal.omega0) →
    seqOfAux k l ∈ L Ordinal.omega0
  | _, [], _ => empty_mem_L_of_limit Ordinal.isSuccLimit_omega0
  | k, a :: l, hl => by
    rw [seqOfAux]
    exact insert_mem_L_of_limit Ordinal.isSuccLimit_omega0
      (kpair_mem_Lω (natZ_mem_Lω k) (hl a (by simp)))
      (seqOfAux_mem_Lω (k + 1) l (fun x hx => hl x (by simp [hx])))

/-- The derivation list of a formula: all subformula codes, each after its own subformulas. -/
def Fm.der : Fm → List ZFSet.{u}
  | .falsum => [Fm.code .falsum]
  | .eq i j => [Fm.code (.eq i j)]
  | .mem i j => [Fm.code (.mem i j)]
  | .imp φ ψ => φ.der ++ (ψ.der ++ [Fm.code (.imp φ ψ)])
  | .all i φ => φ.der ++ [Fm.code (.all i φ)]

theorem Fm.der_length_pos (φ : Fm) : 0 < (Fm.der.{u} φ).length := by
  cases φ <;> simp [Fm.der]

theorem Fm.der_last (φ : Fm) : (Fm.der.{u} φ)[(Fm.der.{u} φ).length - 1]? = some φ.code := by
  cases φ with
  | falsum => rfl
  | eq i j => rfl
  | mem i j => rfl
  | imp φ ψ =>
    simp only [Fm.der, List.length_append, List.length_singleton]
    rw [List.getElem?_append_right (by omega)]
    have : (Fm.der.{u} φ).length + ((Fm.der.{u} ψ).length + 1) - 1 - (Fm.der.{u} φ).length =
        (Fm.der.{u} ψ).length := by omega
    rw [this, List.getElem?_concat_length]
  | all i φ =>
    simp only [Fm.der, List.length_append, List.length_singleton]
    have : (Fm.der.{u} φ).length + 1 - 1 = (Fm.der.{u} φ).length := by omega
    rw [this, List.getElem?_concat_length]

theorem Fm.mem_der (φ : Fm) : ∀ x ∈ Fm.der.{u} φ, ∃ ψ : Fm, x = ψ.code := by
  induction φ with
  | falsum => intro x hx; simp only [Fm.der, List.mem_singleton] at hx; exact ⟨_, hx⟩
  | eq i j => intro x hx; simp only [Fm.der, List.mem_singleton] at hx; exact ⟨_, hx⟩
  | mem i j => intro x hx; simp only [Fm.der, List.mem_singleton] at hx; exact ⟨_, hx⟩
  | imp φ ψ ih₁ ih₂ =>
    intro x hx
    simp only [Fm.der, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx | rfl
    · exact ih₁ x hx
    · exact ih₂ x hx
    · exact ⟨_, rfl⟩
  | all i φ ih =>
    intro x hx
    simp only [Fm.der, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact ih x hx
    · exact ⟨_, rfl⟩

/-- Position `n` of `l` is atomic or built from earlier positions. -/
def Good (l : List ZFSet.{u}) (n : ℕ) : Prop :=
  ∃ x, l[n]? = some x ∧
    (IsAtomicCodeW ωZ x ∨
    (∃ n₁ < n, ∃ n₂ < n, ∃ x₁ x₂, l[n₁]? = some x₁ ∧ l[n₂]? = some x₂ ∧
      x = ZFSet.pair (natZ 3) (ZFSet.pair x₁ x₂)) ∨
    (∃ n₁ < n, ∃ x₁, ∃ i : ℕ, l[n₁]? = some x₁ ∧ x = ZFSet.pair (natZ 4) (ZFSet.pair (natZ i) x₁)))

theorem good_append_left {l₁ : List ZFSet.{u}} (l₂ : List ZFSet.{u}) {n : ℕ} (h : Good l₁ n) :
    Good (l₁ ++ l₂) n := by
  obtain ⟨x, hx, H⟩ := h
  have hn : n < l₁.length := (List.getElem?_eq_some_iff.mp hx).1
  refine ⟨x, by rw [List.getElem?_append_left hn]; exact hx, ?_⟩
  rcases H with H | ⟨n₁, h₁, n₂, h₂, x₁, x₂, hx₁, hx₂, H⟩ | ⟨n₁, h₁, x₁, i, hx₁, H⟩
  · exact Or.inl H
  · exact Or.inr (Or.inl ⟨n₁, h₁, n₂, h₂, x₁, x₂, by rw [List.getElem?_append_left (by omega)]; exact hx₁,
      by rw [List.getElem?_append_left (by omega)]; exact hx₂, H⟩)
  · exact Or.inr (Or.inr ⟨n₁, h₁, x₁, i, by rw [List.getElem?_append_left (by omega)]; exact hx₁, H⟩)

theorem good_append_right (l₁ : List ZFSet.{u}) {l₂ : List ZFSet.{u}} {n : ℕ} (h : Good l₂ n) :
    Good (l₁ ++ l₂) (l₁.length + n) := by
  obtain ⟨x, hx, H⟩ := h
  have key : ∀ m x', l₂[m]? = some x' → (l₁ ++ l₂)[l₁.length + m]? = some x' := by
    intro m x' hm
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    exact hm
  refine ⟨x, key n x hx, ?_⟩
  rcases H with H | ⟨n₁, h₁, n₂, h₂, x₁, x₂, hx₁, hx₂, H⟩ | ⟨n₁, h₁, x₁, i, hx₁, H⟩
  · exact Or.inl H
  · exact Or.inr (Or.inl ⟨l₁.length + n₁, by omega, l₁.length + n₂, by omega, x₁, x₂,
      key _ _ hx₁, key _ _ hx₂, H⟩)
  · exact Or.inr (Or.inr ⟨l₁.length + n₁, by omega, x₁, i, key _ _ hx₁, H⟩)

theorem isAtomicCodeW_code_atomic :
    IsAtomicCodeW ωZ.{u} (Fm.code .falsum) ∧ (∀ i j, IsAtomicCodeW ωZ.{u} (Fm.code (.eq i j))) ∧
      (∀ i j, IsAtomicCodeW ωZ.{u} (Fm.code (.mem i j))) :=
  ⟨Or.inl rfl, fun i j => Or.inr ⟨_, natZ_mem_ωZ i, _, natZ_mem_ωZ j, Or.inl rfl⟩,
    fun i j => Or.inr ⟨_, natZ_mem_ωZ i, _, natZ_mem_ωZ j, Or.inr rfl⟩⟩

theorem Fm.der_good (φ : Fm) : ∀ n x, (Fm.der.{u} φ)[n]? = some x → Good (Fm.der.{u} φ) n := by
  induction φ with
  | falsum =>
    intro n x hx
    have hn : n = 0 := by
      have := (List.getElem?_eq_some_iff.mp hx).1; simp [Fm.der] at this; exact this
    subst hn
    exact ⟨_, rfl, Or.inl isAtomicCodeW_code_atomic.{u}.1⟩
  | eq i j =>
    intro n x hx
    have hn : n = 0 := by
      have := (List.getElem?_eq_some_iff.mp hx).1; simp [Fm.der] at this; exact this
    subst hn
    exact ⟨_, rfl, Or.inl (isAtomicCodeW_code_atomic.{u}.2.1 i j)⟩
  | mem i j =>
    intro n x hx
    have hn : n = 0 := by
      have := (List.getElem?_eq_some_iff.mp hx).1; simp [Fm.der] at this; exact this
    subst hn
    exact ⟨_, rfl, Or.inl (isAtomicCodeW_code_atomic.{u}.2.2 i j)⟩
  | imp φ ψ ih₁ ih₂ =>
    intro n x hx
    simp only [Fm.der] at hx ⊢
    have hlen : n < (Fm.der.{u} φ).length + ((Fm.der.{u} ψ).length + 1) := by
      have := (List.getElem?_eq_some_iff.mp hx).1; simpa using this
    rcases lt_or_ge n (Fm.der.{u} φ).length with h1 | h1
    · rw [List.getElem?_append_left h1] at hx
      exact good_append_left _ (ih₁ n x hx)
    rcases lt_or_ge n ((Fm.der.{u} φ).length + (Fm.der.{u} ψ).length) with h2 | h2
    · rw [List.getElem?_append_right h1, List.getElem?_append_left (by omega)] at hx
      have := good_append_right (Fm.der.{u} φ) (good_append_left [Fm.code.{u} (.imp φ ψ)] (ih₂ _ x hx))
      rwa [Nat.add_sub_cancel' h1] at this
    · have hn : n = (Fm.der.{u} φ).length + (Fm.der.{u} ψ).length := by omega
      subst hn
      have hφ := Fm.der_length_pos.{u} φ
      have hψ := Fm.der_length_pos.{u} ψ
      refine ⟨Fm.code.{u} (.imp φ ψ), ?_, Or.inr (Or.inl ⟨(Fm.der.{u} φ).length - 1, by omega,
        (Fm.der.{u} φ).length + ((Fm.der.{u} ψ).length - 1), by omega, φ.code, ψ.code, ?_, ?_, rfl⟩)⟩
      · rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, List.getElem?_concat_length]
      · rw [List.getElem?_append_left (by omega)]
        exact Fm.der_last.{u} φ
      · rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
          List.getElem?_append_left (by omega)]
        exact Fm.der_last.{u} ψ
  | all i φ ih =>
    intro n x hx
    simp only [Fm.der] at hx ⊢
    have hlen : n < (Fm.der.{u} φ).length + 1 := by
      have := (List.getElem?_eq_some_iff.mp hx).1; simpa using this
    rcases lt_or_ge n (Fm.der.{u} φ).length with h1 | h1
    · rw [List.getElem?_append_left h1] at hx
      exact good_append_left _ (ih n x hx)
    · have hn : n = (Fm.der.{u} φ).length := by omega
      subst hn
      have hφ := Fm.der_length_pos.{u} φ
      refine ⟨Fm.code.{u} (.all i φ), List.getElem?_concat_length, Or.inr (Or.inr ⟨(Fm.der.{u} φ).length - 1,
        by omega, φ.code, i, ?_, rfl⟩)⟩
      rw [List.getElem?_append_left (by omega)]
      exact Fm.der_last.{u} φ

/-- The derivation sequence of a formula is a derivation sequence. -/
theorem derSeqW_seqOf_der (φ : Fm) : DerSeqW ωZ (seqOfAux 0 (Fm.der.{u} φ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨natZ (Fm.der.{u} φ).length, natZ_mem_ωZ _, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨n, x, _, rfl⟩ := mem_seqOfAux.mp hp
    exact ⟨_, _, rfl⟩
  · intro a b b' hab hab'
    obtain ⟨n, x, hx, hp⟩ := mem_seqOfAux.mp hab
    obtain ⟨n', x', hx', hp'⟩ := mem_seqOfAux.mp hab'
    rw [ZFSet.pair_inj] at hp hp'
    obtain ⟨rfl, rfl⟩ := hp
    obtain ⟨ha, rfl⟩ := hp'
    have : n = n' := by simpa using natZ_injective ha
    subst this
    rw [hx] at hx'
    exact Option.some.inj hx' 
  · intro a
    rw [mem_natZ_iff]
    constructor
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨x, hx⟩ : ∃ x, (Fm.der.{u} φ)[m]? = some x :=
        ⟨(Fm.der.{u} φ)[m], List.getElem?_eq_some_iff.mpr ⟨hm, rfl⟩⟩
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
    obtain ⟨y, hy, H⟩ := Fm.der_good.{u} φ n e hx
    rw [hx] at hy
    obtain rfl := Option.some.inj hy
    rcases H with H | ⟨n₁, h₁, n₂, h₂, x₁, x₂, hx₁, hx₂, H⟩ | ⟨n₁, h₁, x₁, i, hx₁, H⟩
    · exact Or.inl H
    · exact Or.inr (Or.inl ⟨natZ n₁, by simpa [natZ_mem_natZ_iff] using h₁, natZ n₂,
        by simpa [natZ_mem_natZ_iff] using h₂, x₁, x₂,
        mem_seqOfAux.mpr ⟨n₁, x₁, hx₁, by simp⟩, mem_seqOfAux.mpr ⟨n₂, x₂, hx₂, by simp⟩, H⟩)
    · exact Or.inr (Or.inr ⟨natZ n₁, by simpa [natZ_mem_natZ_iff] using h₁, x₁, natZ i,
        natZ_mem_ωZ i, mem_seqOfAux.mpr ⟨n₁, x₁, hx₁, by simp⟩, H⟩)

/-- Every entry of a derivation sequence (over `ωZ`) is a code. -/
theorem derSeqW_entry_isCode {s : ZFSet.{u}} (hs : DerSeqW ωZ s) :
    ∀ n e, ZFSet.pair (natZ n) e ∈ s → ∃ φ : Fm, e = φ.code := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro e he
  rcases hs.2.2 _ _ he with H | ⟨k₁, hk₁, k₂, hk₂, e₁, e₂, h₁, h₂, rfl⟩ | ⟨k₁, hk₁, e₁, i, hi, h₁, rfl⟩
  · rcases H with rfl | ⟨i, hi, j, hj, H⟩
    · exact ⟨.falsum, rfl⟩
    · obtain ⟨i', rfl⟩ := mem_ωZ_iff.mp hi
      obtain ⟨j', rfl⟩ := mem_ωZ_iff.mp hj
      rcases H with rfl | rfl
      · exact ⟨.eq i' j', rfl⟩
      · exact ⟨.mem i' j', rfl⟩
  · obtain ⟨n₁, hn₁, rfl⟩ := mem_natZ_iff.mp hk₁
    obtain ⟨n₂, hn₂, rfl⟩ := mem_natZ_iff.mp hk₂
    obtain ⟨φ₁, rfl⟩ := ih n₁ hn₁ e₁ h₁
    obtain ⟨φ₂, rfl⟩ := ih n₂ hn₂ e₂ h₂
    exact ⟨.imp φ₁ φ₂, rfl⟩
  · obtain ⟨n₁, hn₁, rfl⟩ := mem_natZ_iff.mp hk₁
    obtain ⟨φ₁, rfl⟩ := ih n₁ hn₁ e₁ h₁
    obtain ⟨i', rfl⟩ := mem_ωZ_iff.mp hi
    exact ⟨.all i' φ₁, rfl⟩

/-- Correctness: the codes are exactly the elements with a derivation sequence in `L ω`. -/
theorem isCodeW_iff (e : ZFSet.{u}) : IsCodeW (L Ordinal.omega0) ωZ e ↔ ∃ φ : Fm, e = φ.code := by
  constructor
  · rintro ⟨s, _, hs, k, hk⟩
    obtain ⟨d, hd, hdom⟩ := hs.2.1
    have hkd : k ∈ d := (hdom k).mpr ⟨e, hk⟩
    obtain ⟨N, rfl⟩ := mem_ωZ_iff.mp hd
    obtain ⟨n, _, rfl⟩ := mem_natZ_iff.mp hkd
    exact derSeqW_entry_isCode hs n e hk
  · rintro ⟨φ, rfl⟩
    refine ⟨seqOfAux 0 (Fm.der.{u} φ), ?_, derSeqW_seqOf_der φ, natZ ((Fm.der.{u} φ).length - 1), ?_⟩
    · apply seqOfAux_mem_Lω
      intro x hx
      obtain ⟨ψ, rfl⟩ := Fm.mem_der.{u} φ x hx
      exact ψ.code_mem_Lω
    · exact mem_seqOfAux.mpr ⟨(Fm.der.{u} φ).length - 1, φ.code, Fm.der_last.{u} φ, by simp⟩

end BM4.ST
