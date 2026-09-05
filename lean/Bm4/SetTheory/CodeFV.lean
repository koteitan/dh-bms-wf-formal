/-
  Part III, §8 (continued): a Δ₀ predicate recognising the codes of formulas in which a given
  variable does not occur free.

  `NotFreeW h w x e` says: `e` is the code of a formula `φ` with `x ∉ fv φ`.  It is built exactly
  like `IsCodeW` of `Bm4/SetTheory/Code.lean` — a derivation sequence over the subformula codes —
  except that the formation rules are the ones for `fv`:

  * `⊥` is always "x not free";
  * `i = j` / `i ∈ j` only when `i ≠ x` and `j ≠ x`;
  * `φ → ψ` when both `φ` and `ψ` are;
  * `∀i φ` when `i ≠ x` and `φ` is;
  * `∀x φ` always — and there `φ` need only be *some* code, which is what the extra
    (bounded) `IsCodeW` disjunct expresses.

  No flag is carried on the sequence entries: every entry is already a "x not free" code, and the
  `∀x φ` step calls the ordinary code recognizer `IsCodeW` on the immediate subterm, which is
  bounded by `e` itself.

  The last two sections of this file give the paper's general schema (8.3) instead — the pair of a
  derivation sequence `s` and a computation sequence `τ` obeying local rules `Trace_F` supplied as
  parameters (`TraceW`, `GraphW`), its Δ₀-definability once for all operations (`delta0_traceW`,
  `delta0_graphW`) — and exhibit `NotFreeW` as one instance of it (`notFreeW_iff_graphW`).
-/
import Bm4.SetTheory.BFCode

universe u

namespace BM4.ST

/-! ### The predicate -/

/-- `e` is an atomic code with variable indices in `w`, none of them equal to `x`. -/
def NFAtomicW (w x e : ZFSet.{u}) : Prop :=
  e = ZFSet.pair (natZ 0) (natZ 0) ∨
  ∃ i ∈ w, ∃ j ∈ w, i ≠ x ∧ j ≠ x ∧
    (e = ZFSet.pair (natZ 1) (ZFSet.pair i j) ∨ e = ZFSet.pair (natZ 2) (ZFSet.pair i j))

/-- Derivation sequences for "the variable `x` is not free": `s` is a function whose domain is an
element of `w`, every value being an atomic code avoiding `x`, or built from earlier values by
`imp`, by `all i` with `i ≠ x`, or by `all x` applied to an arbitrary code (recognised by
`IsCodeW h w`). -/
def NFDerSeqW (h w x s : ZFSet.{u}) : Prop :=
  IsFunc s ∧ (∃ d ∈ w, IsDom s d) ∧
  ∀ k e, ZFSet.pair k e ∈ s →
    NFAtomicW w x e ∨
    (∃ k₁ ∈ k, ∃ k₂ ∈ k, ∃ e₁ e₂, ZFSet.pair k₁ e₁ ∈ s ∧ ZFSet.pair k₂ e₂ ∈ s ∧
      e = ZFSet.pair (natZ 3) (ZFSet.pair e₁ e₂)) ∨
    (∃ k₁ ∈ k, ∃ e₁, ∃ i ∈ w, i ≠ x ∧ ZFSet.pair k₁ e₁ ∈ s ∧
      e = ZFSet.pair (natZ 4) (ZFSet.pair i e₁)) ∨
    (∃ e₁, IsCodeW h w e₁ ∧ e = ZFSet.pair (natZ 4) (ZFSet.pair x e₁))

/-- `e` codes a formula in which the variable `x` does not occur free: it occurs in a
"not free" derivation sequence lying in `h` (intended `h = L ω`, `w = ωZ`). -/
def NotFreeW (h w x e : ZFSet.{u}) : Prop :=
  ∃ s ∈ h, NFDerSeqW h w x s ∧ ∃ k, ZFSet.pair k e ∈ s

/-! ### Δ₀-definability -/

theorem delta0_nfAtomicW (w x e : ℕ) (hwx : w ≠ x) (hwe : w ≠ e) (hxe : x ≠ e) :
    Delta0Def.{u} {w, x, e} (fun _ v => NFAtomicW (v w) (v x) (v e)) := by
  set m := w + x + e + 1 with hm
  have h0 := (Delta0Def.eq.{u} m x).not.and
    ((Delta0Def.eq.{u} (m + 1) x).not.and
      ((delta0_tagPair 1 e m (m + 1) (by omega) (by omega)).or
        (delta0_tagPair 2 e m (m + 1) (by omega) (by omega))))
  have h1 := h0.bex (m + 1) w (by omega)
  have h2 := h1.bex m w (by omega)
  have h := (delta0_tagPair0 e).or h2
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    rfl
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- The subterm of `pair (natZ 4) (pair x e₁)` in the `e₁` slot is bounded by the whole code. -/
theorem exists_allCode_iff_bounded (x e : ZFSet.{u}) (P : ZFSet.{u} → Prop) :
    (∃ e₁, P e₁ ∧ e = ZFSet.pair (natZ 4) (ZFSet.pair x e₁)) ↔
      ∃ q ∈ e, ∃ r ∈ q, ∃ t ∈ r, ∃ e₁ ∈ t,
        P e₁ ∧ e = ZFSet.pair (natZ 4) (ZFSet.pair x e₁) := by
  constructor
  · rintro ⟨e₁, hP, rfl⟩
    exact ⟨_, upair_mem_pair _ _, _, mem_upair_right _ _, _, upair_mem_pair _ _,
      e₁, mem_upair_right _ _, hP, rfl⟩
  · rintro ⟨q, -, r, -, t, -, e₁, -, hP, H⟩
    exact ⟨e₁, hP, H⟩

theorem delta0_nfDerSeqW (h w x s : ℕ) (hhw : h ≠ w) (hhx : h ≠ x) (hhs : h ≠ s)
    (hwx : w ≠ x) (hws : w ≠ s) (hxs : x ≠ s) :
    Delta0Def.{u} {h, w, x, s} (fun _ v => NFDerSeqW (v h) (v w) (v x) (v s)) := by
  set m := h + w + x + s + 1 with hm
  have h1 := delta0_isFunc s
  have h2 := (delta0_isDom s m (by omega)).bex m w (by omega)
  -- variables: p := m+1, q := m+2, k := m+3, q' := m+4, e := m+5
  -- imp: k₁ := m+6, k₂ := m+7, p₁ := m+8, q₁ := m+9, e₁ := m+10,
  --      p₂ := m+11, q₂ := m+12, e₂ := m+13
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
  -- all with `i ≠ x`: k₁ := m+6, p₁ := m+8, q₁ := m+9, e₁ := m+10, i := m+14
  have a0 := (Delta0Def.eq.{u} (m + 14) x).not.and
    ((delta0_isKPair (m + 8) (m + 6) (m + 10) (by omega) (by omega)).and
      (delta0_tagPair 4 (m + 5) (m + 14) (m + 10) (by omega) (by omega)))
  have a1 := a0.bex (m + 14) w (by omega)
  have a2 := a1.bex (m + 10) (m + 9) (by omega)
  have a3 := a2.bex (m + 9) (m + 8) (by omega)
  have a4 := a3.bex (m + 8) s (by omega)
  have aC := a4.bex (m + 6) (m + 3) (by omega)
  -- all with `i = x`: q := m+15, r := m+16, t := m+17, e₁ := m+18
  have b0 := (delta0_isCodeW h w (m + 18) (by omega) (by omega) (by omega)).and
    (delta0_tagPair 4 (m + 5) x (m + 18) (by omega) (by omega))
  have b1 := b0.bex (m + 18) (m + 17) (by omega)
  have b2 := b1.bex (m + 17) (m + 16) (by omega)
  have b3 := b2.bex (m + 16) (m + 15) (by omega)
  have bC := b3.bex (m + 15) (m + 5) (by omega)
  have c0 := (delta0_isKPair (m + 1) (m + 3) (m + 5) (by omega) (by omega)).imp
    ((delta0_nfAtomicW w x (m + 5) (by omega) (by omega) (by omega)).or (iC.or (aC.or bC)))
  have c1 := c0.ball (m + 5) (m + 4) (by omega)
  have c2 := c1.ball (m + 4) (m + 1) (by omega)
  have c3 := c2.ball (m + 3) (m + 2) (by omega)
  have c4 := c3.ball (m + 2) (m + 1) (by omega)
  have h3 := c4.ball (m + 1) s (by omega)
  refine ((h1.and (h2.and h3)).congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    unfold NFDerSeqW
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
      · rintro ⟨p₁, hp₁, q₁, -, e₁, -, p₂, hp₂, q₂, -, e₂, -, rfl, rfl, H⟩
        exact ⟨e₁, e₂, hp₁, hp₂, H⟩
      · rintro ⟨e₁, e₂, hh₁, hh₂, H⟩
        exact ⟨_, hh₁, _, upair_mem_pair _ _, e₁, mem_upair_right _ _, _, hh₂,
          _, upair_mem_pair _ _, e₂, mem_upair_right _ _, rfl, rfl, H⟩
    apply or_congr
    · apply exists_congr; intro k₁; apply and_congr_right; intro _
      constructor
      · rintro ⟨p₁, hp₁, q₁, -, e₁, -, i, hi, hne, rfl, H⟩
        exact ⟨e₁, i, hi, hne, hp₁, H⟩
      · rintro ⟨e₁, i, hi, hne, hh₁, H⟩
        exact ⟨_, hh₁, _, upair_mem_pair _ _, e₁, mem_upair_right _ _, i, hi, hne, rfl, H⟩
    · exact (exists_allCode_iff_bounded _ _ _).symm
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

theorem delta0_notFreeW (h w x e : ℕ) (hhw : h ≠ w) (hhx : h ≠ x) (hhe : h ≠ e)
    (hwx : w ≠ x) (hwe : w ≠ e) (hxe : x ≠ e) :
    Delta0Def.{u} {h, w, x, e} (fun _ v => NotFreeW (v h) (v w) (v x) (v e)) := by
  set m := h + w + x + e + 1 with hm
  have k0 := delta0_isKPair (m + 1) (m + 3) e (by omega) (by omega)
  have k1 := k0.bex (m + 3) (m + 2) (by omega)
  have k2 := k1.bex (m + 2) (m + 1) (by omega)
  have k3 := k2.bex (m + 1) m (by omega)
  have d := (delta0_nfDerSeqW h w x m (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)).and k3
  have hh := d.bex m h (by omega)
  refine (hh.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    unfold NotFreeW
    apply exists_congr; intro s; apply and_congr_right; intro _
    apply and_congr_right; intro _
    constructor
    · rintro ⟨p, hp, q, -, k, -, rfl⟩; exact ⟨k, hp⟩
    · rintro ⟨k, hk⟩
      exact ⟨_, hk, _, singleton_mem_pair _ _, k, ZFSet.mem_singleton.mpr rfl, rfl⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-! ### Soundness -/

theorem nfDerSeqW_entry {x : ℕ} {s : ZFSet.{u}}
    (hs : NFDerSeqW (L Ordinal.omega0) ωZ (natZ x) s) :
    ∀ n e, ZFSet.pair (natZ n) e ∈ s → ∃ φ : Fm, e = φ.code ∧ x ∉ Fm.fv φ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro e he
  rcases hs.2.2 _ _ he with H | ⟨k₁, hk₁, k₂, hk₂, e₁, e₂, h₁, h₂, rfl⟩ |
    ⟨k₁, hk₁, e₁, i, hi, hix, h₁, rfl⟩ | ⟨e₁, hcode, rfl⟩
  · rcases H with rfl | ⟨i, hi, j, hj, hix, hjx, H⟩
    · exact ⟨.falsum, rfl, by simp [Fm.fv]⟩
    · obtain ⟨i', rfl⟩ := mem_ωZ_iff.mp hi
      obtain ⟨j', rfl⟩ := mem_ωZ_iff.mp hj
      have hi' : x ≠ i' := fun hh => hix (by rw [hh])
      have hj' : x ≠ j' := fun hh => hjx (by rw [hh])
      rcases H with rfl | rfl
      · exact ⟨.eq i' j', rfl, by
          simp only [Fm.fv, Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hi', hj'⟩⟩
      · exact ⟨.mem i' j', rfl, by
          simp only [Fm.fv, Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hi', hj'⟩⟩
  · obtain ⟨n₁, hn₁, rfl⟩ := mem_natZ_iff.mp hk₁
    obtain ⟨n₂, hn₂, rfl⟩ := mem_natZ_iff.mp hk₂
    obtain ⟨φ₁, rfl, hf₁⟩ := ih n₁ hn₁ e₁ h₁
    obtain ⟨φ₂, rfl, hf₂⟩ := ih n₂ hn₂ e₂ h₂
    exact ⟨.imp φ₁ φ₂, rfl, by
      simp only [Fm.fv, Finset.mem_union, not_or]; exact ⟨hf₁, hf₂⟩⟩
  · obtain ⟨n₁, hn₁, rfl⟩ := mem_natZ_iff.mp hk₁
    obtain ⟨φ₁, rfl, hf₁⟩ := ih n₁ hn₁ e₁ h₁
    obtain ⟨i', rfl⟩ := mem_ωZ_iff.mp hi
    exact ⟨.all i' φ₁, rfl, by
      simp only [Fm.fv, Finset.mem_erase, not_and]; exact fun _ => hf₁⟩
  · obtain ⟨ψ, rfl⟩ := (isCodeW_iff e₁).mp hcode
    exact ⟨.all x ψ, rfl, by simp [Fm.fv]⟩

/-! ### Completeness: derivation lists that stop at `∀x` -/

/-- The derivation list of `φ` for the variable `x`: all subformula codes, each after its own
subformulas, but pruned at a quantifier `∀x` (whose body need not avoid `x`). -/
def Fm.derNF (x : ℕ) : Fm → List ZFSet.{u}
  | .falsum => [Fm.code .falsum]
  | .eq i j => [Fm.code (.eq i j)]
  | .mem i j => [Fm.code (.mem i j)]
  | .imp φ ψ => Fm.derNF x φ ++ (Fm.derNF x ψ ++ [Fm.code (.imp φ ψ)])
  | .all i φ => if i = x then [Fm.code (.all i φ)] else Fm.derNF x φ ++ [Fm.code (.all i φ)]

theorem Fm.derNF_length_pos (x : ℕ) (φ : Fm) : 0 < (Fm.derNF.{u} x φ).length := by
  cases φ with
  | falsum => simp only [Fm.derNF]; simp
  | eq i j => simp only [Fm.derNF]; simp
  | mem i j => simp only [Fm.derNF]; simp
  | imp φ ψ => simp only [Fm.derNF, List.length_append, List.length_singleton]; omega
  | all i φ =>
    by_cases hix : i = x
    · simp only [Fm.derNF, if_pos hix]; simp
    · simp only [Fm.derNF, if_neg hix, List.length_append, List.length_singleton]; omega

theorem Fm.derNF_last (x : ℕ) (φ : Fm) :
    (Fm.derNF.{u} x φ)[(Fm.derNF.{u} x φ).length - 1]? = some φ.code := by
  cases φ with
  | falsum => rfl
  | eq i j => rfl
  | mem i j => rfl
  | imp φ ψ =>
    simp only [Fm.derNF, List.length_append, List.length_singleton]
    rw [List.getElem?_append_right (by omega)]
    have : (Fm.derNF.{u} x φ).length + ((Fm.derNF.{u} x ψ).length + 1) - 1
        - (Fm.derNF.{u} x φ).length = (Fm.derNF.{u} x ψ).length := by omega
    rw [this, List.getElem?_concat_length]
  | all i φ =>
    by_cases hix : i = x
    · simp only [Fm.derNF, if_pos hix]; rfl
    · simp only [Fm.derNF, if_neg hix, List.length_append, List.length_singleton]
      have : (Fm.derNF.{u} x φ).length + 1 - 1 = (Fm.derNF.{u} x φ).length := by omega
      rw [this, List.getElem?_concat_length]

theorem Fm.mem_derNF (x : ℕ) : ∀ (φ : Fm), ∀ y ∈ Fm.derNF.{u} x φ, ∃ ψ : Fm, y = ψ.code := by
  intro φ
  induction φ with
  | falsum => intro y hy; simp only [Fm.derNF, List.mem_singleton] at hy; exact ⟨_, hy⟩
  | eq i j => intro y hy; simp only [Fm.derNF, List.mem_singleton] at hy; exact ⟨_, hy⟩
  | mem i j => intro y hy; simp only [Fm.derNF, List.mem_singleton] at hy; exact ⟨_, hy⟩
  | imp φ ψ ih₁ ih₂ =>
    intro y hy
    simp only [Fm.derNF, List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | hy | rfl
    · exact ih₁ y hy
    · exact ih₂ y hy
    · exact ⟨_, rfl⟩
  | all i φ ih =>
    intro y hy
    by_cases hix : i = x
    · simp only [Fm.derNF, if_pos hix, List.mem_singleton] at hy; exact ⟨_, hy⟩
    · simp only [Fm.derNF, if_neg hix, List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · exact ih y hy
      · exact ⟨_, rfl⟩

/-- Position `n` of `l` is a formation step for "`x` not free". -/
def GoodNF (x : ℕ) (l : List ZFSet.{u}) (n : ℕ) : Prop :=
  ∃ y, l[n]? = some y ∧
    (NFAtomicW ωZ (natZ x) y ∨
    (∃ n₁ < n, ∃ n₂ < n, ∃ y₁ y₂, l[n₁]? = some y₁ ∧ l[n₂]? = some y₂ ∧
      y = ZFSet.pair (natZ 3) (ZFSet.pair y₁ y₂)) ∨
    (∃ n₁ < n, ∃ y₁, ∃ i : ℕ, i ≠ x ∧ l[n₁]? = some y₁ ∧
      y = ZFSet.pair (natZ 4) (ZFSet.pair (natZ i) y₁)) ∨
    (∃ ψ : Fm, y = ZFSet.pair (natZ 4) (ZFSet.pair (natZ x) ψ.code)))

theorem goodNF_append_left {x : ℕ} {l₁ : List ZFSet.{u}} (l₂ : List ZFSet.{u}) {n : ℕ}
    (h : GoodNF x l₁ n) : GoodNF x (l₁ ++ l₂) n := by
  obtain ⟨y, hy, H⟩ := h
  have hn : n < l₁.length := (List.getElem?_eq_some_iff.mp hy).1
  refine ⟨y, by rw [List.getElem?_append_left hn]; exact hy, ?_⟩
  rcases H with H | ⟨n₁, h₁, n₂, h₂, y₁, y₂, hy₁, hy₂, H⟩ | ⟨n₁, h₁, y₁, i, hix, hy₁, H⟩ | H
  · exact Or.inl H
  · exact Or.inr (Or.inl ⟨n₁, h₁, n₂, h₂, y₁, y₂,
      by rw [List.getElem?_append_left (by omega)]; exact hy₁,
      by rw [List.getElem?_append_left (by omega)]; exact hy₂, H⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n₁, h₁, y₁, i, hix,
      by rw [List.getElem?_append_left (by omega)]; exact hy₁, H⟩))
  · exact Or.inr (Or.inr (Or.inr H))

theorem goodNF_append_right {x : ℕ} (l₁ : List ZFSet.{u}) {l₂ : List ZFSet.{u}} {n : ℕ}
    (h : GoodNF x l₂ n) : GoodNF x (l₁ ++ l₂) (l₁.length + n) := by
  obtain ⟨y, hy, H⟩ := h
  have key : ∀ p y', l₂[p]? = some y' → (l₁ ++ l₂)[l₁.length + p]? = some y' := by
    intro p y' hp
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    exact hp
  refine ⟨y, key n y hy, ?_⟩
  rcases H with H | ⟨n₁, h₁, n₂, h₂, y₁, y₂, hy₁, hy₂, H⟩ | ⟨n₁, h₁, y₁, i, hix, hy₁, H⟩ | H
  · exact Or.inl H
  · exact Or.inr (Or.inl ⟨l₁.length + n₁, by omega, l₁.length + n₂, by omega, y₁, y₂,
      key _ _ hy₁, key _ _ hy₂, H⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨l₁.length + n₁, by omega, y₁, i, hix, key _ _ hy₁, H⟩))
  · exact Or.inr (Or.inr (Or.inr H))

theorem Fm.derNF_good (x : ℕ) : ∀ (φ : Fm), x ∉ Fm.fv φ →
    ∀ n y, (Fm.derNF.{u} x φ)[n]? = some y → GoodNF x (Fm.derNF.{u} x φ) n := by
  intro φ
  induction φ with
  | falsum =>
    intro _ n y hy
    have hn : n = 0 := by
      have := (List.getElem?_eq_some_iff.mp hy).1
      simp only [Fm.derNF, List.length_singleton] at this; omega
    subst hn
    exact ⟨_, rfl, Or.inl (Or.inl rfl)⟩
  | eq i j =>
    intro hfv n y hy
    have hn : n = 0 := by
      have := (List.getElem?_eq_some_iff.mp hy).1
      simp only [Fm.derNF, List.length_singleton] at this; omega
    subst hn
    simp only [Fm.fv, Finset.mem_insert, Finset.mem_singleton, not_or] at hfv
    exact ⟨_, rfl, Or.inl (Or.inr ⟨natZ i, natZ_mem_ωZ i, natZ j, natZ_mem_ωZ j,
      fun hh => hfv.1 (natZ_injective hh).symm, fun hh => hfv.2 (natZ_injective hh).symm,
      Or.inl rfl⟩)⟩
  | mem i j =>
    intro hfv n y hy
    have hn : n = 0 := by
      have := (List.getElem?_eq_some_iff.mp hy).1
      simp only [Fm.derNF, List.length_singleton] at this; omega
    subst hn
    simp only [Fm.fv, Finset.mem_insert, Finset.mem_singleton, not_or] at hfv
    exact ⟨_, rfl, Or.inl (Or.inr ⟨natZ i, natZ_mem_ωZ i, natZ j, natZ_mem_ωZ j,
      fun hh => hfv.1 (natZ_injective hh).symm, fun hh => hfv.2 (natZ_injective hh).symm,
      Or.inr rfl⟩)⟩
  | imp φ ψ ih₁ ih₂ =>
    intro hfv n y hy
    simp only [Fm.fv, Finset.mem_union, not_or] at hfv
    simp only [Fm.derNF] at hy ⊢
    have hlen : n < (Fm.derNF.{u} x φ).length + ((Fm.derNF.{u} x ψ).length + 1) := by
      have := (List.getElem?_eq_some_iff.mp hy).1; simpa using this
    rcases lt_or_ge n (Fm.derNF.{u} x φ).length with h1 | h1
    · rw [List.getElem?_append_left h1] at hy
      exact goodNF_append_left _ (ih₁ hfv.1 n y hy)
    rcases lt_or_ge n ((Fm.derNF.{u} x φ).length + (Fm.derNF.{u} x ψ).length) with h2 | h2
    · rw [List.getElem?_append_right h1, List.getElem?_append_left (by omega)] at hy
      have := goodNF_append_right (Fm.derNF.{u} x φ)
        (goodNF_append_left [Fm.code.{u} (.imp φ ψ)] (ih₂ hfv.2 _ y hy))
      rwa [Nat.add_sub_cancel' h1] at this
    · have hn : n = (Fm.derNF.{u} x φ).length + (Fm.derNF.{u} x ψ).length := by omega
      subst hn
      have hφ := Fm.derNF_length_pos.{u} x φ
      have hψ := Fm.derNF_length_pos.{u} x ψ
      refine ⟨Fm.code.{u} (.imp φ ψ), ?_, Or.inr (Or.inl ⟨(Fm.derNF.{u} x φ).length - 1,
        by omega, (Fm.derNF.{u} x φ).length + ((Fm.derNF.{u} x ψ).length - 1), by omega,
        φ.code, ψ.code, ?_, ?_, rfl⟩)⟩
      · rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
          List.getElem?_concat_length]
      · rw [List.getElem?_append_left (by omega)]
        exact Fm.derNF_last.{u} x φ
      · rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
          List.getElem?_append_left (by omega)]
        exact Fm.derNF_last.{u} x ψ
  | all i φ ih =>
    intro hfv n y hy
    by_cases hix : i = x
    · simp only [Fm.derNF, if_pos hix] at hy ⊢
      have hn : n = 0 := by
        have := (List.getElem?_eq_some_iff.mp hy).1
        simp only [List.length_singleton] at this; omega
      subst hn
      exact ⟨_, rfl, Or.inr (Or.inr (Or.inr ⟨φ, by rw [hix]; rfl⟩))⟩
    · have hfvφ : x ∉ Fm.fv φ := by
        simp only [Fm.fv, Finset.mem_erase, not_and] at hfv
        exact hfv (fun hh => hix hh.symm)
      simp only [Fm.derNF, if_neg hix] at hy ⊢
      have hlen : n < (Fm.derNF.{u} x φ).length + 1 := by
        have := (List.getElem?_eq_some_iff.mp hy).1; simpa using this
      rcases lt_or_ge n (Fm.derNF.{u} x φ).length with h1 | h1
      · rw [List.getElem?_append_left h1] at hy
        exact goodNF_append_left _ (ih hfvφ n y hy)
      · have hn : n = (Fm.derNF.{u} x φ).length := by omega
        subst hn
        have hφ := Fm.derNF_length_pos.{u} x φ
        refine ⟨Fm.code.{u} (.all i φ), List.getElem?_concat_length,
          Or.inr (Or.inr (Or.inl ⟨(Fm.derNF.{u} x φ).length - 1, by omega, φ.code, i, hix,
            ?_, rfl⟩))⟩
        rw [List.getElem?_append_left (by omega)]
        exact Fm.derNF_last.{u} x φ

/-! ### The derivation sequence of a formula -/

theorem isFunc_seqOfAux (l : List ZFSet.{u}) : IsFunc (seqOfAux 0 l) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨n, y, -, rfl⟩ := mem_seqOfAux.mp hp
    exact ⟨_, _, rfl⟩
  · intro a b b' hab hab'
    obtain ⟨n, y, hy, hp⟩ := mem_seqOfAux.mp hab
    obtain ⟨n', y', hy', hp'⟩ := mem_seqOfAux.mp hab'
    rw [ZFSet.pair_inj] at hp hp'
    obtain ⟨rfl, rfl⟩ := hp
    obtain ⟨ha, rfl⟩ := hp'
    have : n = n' := by simpa using natZ_injective ha
    subst this
    rw [hy] at hy'
    exact Option.some.inj hy'

theorem nfDerSeqW_seqOf_derNF (x : ℕ) (φ : Fm) (hfv : x ∉ Fm.fv φ) :
    NFDerSeqW (L Ordinal.omega0) ωZ (natZ x) (seqOfAux 0 (Fm.derNF.{u} x φ)) := by
  refine ⟨isFunc_seqOfAux _,
    ⟨natZ (Fm.derNF.{u} x φ).length, natZ_mem_ωZ _, isDom_seqOfAux _⟩, ?_⟩
  intro k e hke
  obtain ⟨n, z, hz, hp⟩ := mem_seqOfAux.mp hke
  rw [ZFSet.pair_inj] at hp
  obtain ⟨hk, he⟩ := hp
  subst hk
  subst he
  obtain ⟨y, hy, H⟩ := Fm.derNF_good.{u} x φ hfv n e hz
  rw [hz] at hy
  obtain rfl := Option.some.inj hy
  rcases H with H | ⟨n₁, h₁, n₂, h₂, y₁, y₂, hy₁, hy₂, H⟩ | ⟨n₁, h₁, y₁, i, hix, hy₁, H⟩ |
    ⟨ψ, H⟩
  · exact Or.inl H
  · exact Or.inr (Or.inl ⟨natZ n₁, by simpa [natZ_mem_natZ_iff] using h₁, natZ n₂,
      by simpa [natZ_mem_natZ_iff] using h₂, y₁, y₂,
      mem_seqOfAux.mpr ⟨n₁, y₁, hy₁, by simp⟩, mem_seqOfAux.mpr ⟨n₂, y₂, hy₂, by simp⟩, H⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨natZ n₁, by simpa [natZ_mem_natZ_iff] using h₁, y₁,
      natZ i, natZ_mem_ωZ i, fun hh => hix (natZ_injective hh),
      mem_seqOfAux.mpr ⟨n₁, y₁, hy₁, by simp⟩, H⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ψ.code, (isCodeW_iff _).mpr ⟨ψ, rfl⟩, H⟩))

/-! ### Correctness -/

/-- Correctness: `NotFreeW` recognises exactly the codes of formulas in which the variable `k`
does not occur free. -/
theorem notFreeW_iff (k : ℕ) (e : ZFSet.{u}) :
    NotFreeW (L Ordinal.omega0) ωZ (natZ.{u} k) e ↔ ∃ φ : Fm, e = φ.code ∧ k ∉ Fm.fv φ := by
  constructor
  · rintro ⟨s, -, hs, c, hc⟩
    obtain ⟨d, hd, hdom⟩ := hs.2.1
    have hcd : c ∈ d := (hdom c).mpr ⟨e, hc⟩
    obtain ⟨M, rfl⟩ := mem_ωZ_iff.mp hd
    obtain ⟨p, -, rfl⟩ := mem_natZ_iff.mp hcd
    exact nfDerSeqW_entry hs p e hc
  · rintro ⟨φ, rfl, hfv⟩
    refine ⟨seqOfAux 0 (Fm.derNF.{u} k φ), ?_, nfDerSeqW_seqOf_derNF k φ hfv,
      natZ ((Fm.derNF.{u} k φ).length - 1), ?_⟩
    · apply seqOfAux_mem_Lω
      intro y hy
      obtain ⟨ψ, rfl⟩ := Fm.mem_derNF.{u} k φ y hy
      exact ψ.code_mem_Lω
    · exact mem_seqOfAux.mpr
        ⟨(Fm.derNF.{u} k φ).length - 1, φ.code, Fm.derNF_last.{u} k φ, by simp⟩

/-! ### The general graph schema (8.3)

The paper gives the graph of every syntactic operation `F` by the single schema

```
G_F(ē, d)  :⇔  ∃ s ∈ ω ∃ τ ∈ ω (DerSeq(ē, s) ∧ Trace_F(ē, d, s, τ))
```

where `s` is a derivation sequence of the input code and `τ` is a *computation sequence* running
alongside `s`: it attaches a value to every position of `s`, the value at a node being determined
by the node's tag, its immediate subcodes and the values already computed for its children.  That
local rule is the only part that depends on `F`, so it is taken here as a parameter: `A` is the
rule at atomic nodes, `I` at `imp` nodes and `U` at `all` nodes.  `p` is the parameter block of
`ē` besides the principal input.  `TraceW` and `GraphW` below are that schema, and
`delta0_traceW` / `delta0_graphW` are the paper's conclusion that the schema is Δ₀ as soon as the
local rules are — one proof for all operations, rather than one per predicate. -/

/-- `τ` is a computation sequence for the local rules `A`, `I`, `U` alongside the derivation
sequence `s`: a function attaching to each position of `s` a value licensed by the rule for that
node's tag from the values at its children. -/
def TraceW (w : ZFSet.{u})
    (A : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (I : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (U : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (p s t : ZFSet.{u}) : Prop :=
  IsFunc t ∧
  ∀ k e, ZFSet.pair k e ∈ s → ∃ v, ZFSet.pair k v ∈ t ∧
    (A w p e v ∨
     (∃ k₁ ∈ k, ∃ k₂ ∈ k, ∃ e₁ e₂ v₁ v₂, ZFSet.pair k₁ e₁ ∈ s ∧ ZFSet.pair k₂ e₂ ∈ s ∧
        ZFSet.pair k₁ v₁ ∈ t ∧ ZFSet.pair k₂ v₂ ∈ t ∧
        e = ZFSet.pair (natZ 3) (ZFSet.pair e₁ e₂) ∧ I w p v₁ v₂ v) ∨
     (∃ k₁ ∈ k, ∃ e₁ v₁, ∃ i ∈ w, ZFSet.pair k₁ e₁ ∈ s ∧ ZFSet.pair k₁ v₁ ∈ t ∧
        e = ZFSet.pair (natZ 4) (ZFSet.pair i e₁) ∧ U w p i v₁ v))

/-- The graph (8.3) of the operation whose local rules are `A`, `I`, `U`: the input `e` and the
output `d` sit at the same position of a derivation sequence `s` and of a computation sequence
`τ` for it, both lying in `h` (intended `h = L ω`, `w = ωZ`). -/
def GraphW (h w : ZFSet.{u})
    (A : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (I : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (U : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (p e d : ZFSet.{u}) : Prop :=
  ∃ s ∈ h, ∃ t ∈ h, DerSeqW w s ∧ TraceW w A I U p s t ∧
    ∃ k, ZFSet.pair k e ∈ s ∧ ZFSet.pair k d ∈ t

variable {A : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop}
  {I : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop}
  {U : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop}

/-- The schema is Δ₀ as soon as the three local rules are: this is (8.3)'s conclusion, proved once
for every syntactic operation instead of once per predicate. -/
theorem delta0_traceW (w p s t : ℕ)
    (hA : ∀ a b c d : ℕ, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      Delta0Def.{u} {a, b, c, d} (fun _ v => A (v a) (v b) (v c) (v d)))
    (hI : ∀ a b c d e : ℕ, a ≠ b → a ≠ c → a ≠ d → a ≠ e → b ≠ c → b ≠ d → b ≠ e →
        c ≠ d → c ≠ e → d ≠ e →
      Delta0Def.{u} {a, b, c, d, e} (fun _ v => I (v a) (v b) (v c) (v d) (v e)))
    (hU : ∀ a b c d e : ℕ, a ≠ b → a ≠ c → a ≠ d → a ≠ e → b ≠ c → b ≠ d → b ≠ e →
        c ≠ d → c ≠ e → d ≠ e →
      Delta0Def.{u} {a, b, c, d, e} (fun _ v => U (v a) (v b) (v c) (v d) (v e)))
    (hwp : w ≠ p) (hws : w ≠ s) (hwt : w ≠ t) (hps : p ≠ s) (hpt : p ≠ t) (hst : s ≠ t) :
    Delta0Def.{u} {w, p, s, t} (fun _ v => TraceW (v w) A I U (v p) (v s) (v t)) := by
  set m := w + p + s + t + 1 with hm
  -- P := m+1, Q := m+2, k := m+3, Q' := m+4, e := m+5; P₀ := m+6, Q₀ := m+7, v := m+8
  -- k₁ := m+9, k₂ := m+10; P₁ := m+11, Q₁ := m+12, e₁ := m+13; P₂ := m+14, Q₂ := m+15, e₂ := m+16
  -- R₁ := m+17, S₁ := m+18, v₁ := m+19; R₂ := m+20, S₂ := m+21, v₂ := m+22; i := m+23
  have i0 := (delta0_isKPair (m + 11) (m + 9) (m + 13) (by omega) (by omega)).and
    ((delta0_isKPair (m + 14) (m + 10) (m + 16) (by omega) (by omega)).and
      ((delta0_isKPair (m + 17) (m + 9) (m + 19) (by omega) (by omega)).and
        ((delta0_isKPair (m + 20) (m + 10) (m + 22) (by omega) (by omega)).and
          ((delta0_tagPair 3 (m + 5) (m + 13) (m + 16) (by omega) (by omega)).and
            (hI w p (m + 19) (m + 22) (m + 8) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))))))
  have i1 := i0.bex (m + 22) (m + 21) (by omega)
  have i2 := i1.bex (m + 21) (m + 20) (by omega)
  have i3 := i2.bex (m + 20) t (by omega)
  have i4 := i3.bex (m + 19) (m + 18) (by omega)
  have i5 := i4.bex (m + 18) (m + 17) (by omega)
  have i6 := i5.bex (m + 17) t (by omega)
  have i7 := i6.bex (m + 16) (m + 15) (by omega)
  have i8 := i7.bex (m + 15) (m + 14) (by omega)
  have i9 := i8.bex (m + 14) s (by omega)
  have i10 := i9.bex (m + 13) (m + 12) (by omega)
  have i11 := i10.bex (m + 12) (m + 11) (by omega)
  have i12 := i11.bex (m + 11) s (by omega)
  have i13 := i12.bex (m + 10) (m + 3) (by omega)
  have iC := i13.bex (m + 9) (m + 3) (by omega)
  have a0 := (delta0_isKPair (m + 11) (m + 9) (m + 13) (by omega) (by omega)).and
    ((delta0_isKPair (m + 17) (m + 9) (m + 19) (by omega) (by omega)).and
      ((delta0_tagPair 4 (m + 5) (m + 23) (m + 13) (by omega) (by omega)).and
        (hU w p (m + 23) (m + 19) (m + 8) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))))
  have a1 := a0.bex (m + 23) w (by omega)
  have a2 := a1.bex (m + 19) (m + 18) (by omega)
  have a3 := a2.bex (m + 18) (m + 17) (by omega)
  have a4 := a3.bex (m + 17) t (by omega)
  have a5 := a4.bex (m + 13) (m + 12) (by omega)
  have a6 := a5.bex (m + 12) (m + 11) (by omega)
  have a7 := a6.bex (m + 11) s (by omega)
  have aC := a7.bex (m + 9) (m + 3) (by omega)
  have b0 := (delta0_isKPair (m + 6) (m + 3) (m + 8) (by omega) (by omega)).and
    ((hA w p (m + 5) (m + 8) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)).or (iC.or aC))
  have b1 := b0.bex (m + 8) (m + 7) (by omega)
  have b2 := b1.bex (m + 7) (m + 6) (by omega)
  have b3 := b2.bex (m + 6) t (by omega)
  have c0 := (delta0_isKPair (m + 1) (m + 3) (m + 5) (by omega) (by omega)).imp b3
  have c1 := c0.ball (m + 5) (m + 4) (by omega)
  have c2 := c1.ball (m + 4) (m + 1) (by omega)
  have c3 := c2.ball (m + 3) (m + 2) (by omega)
  have c4 := c3.ball (m + 2) (m + 1) (by omega)
  have h2 := c4.ball (m + 1) s (by omega)
  refine (((delta0_isFunc t).and h2).congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    unfold TraceW
    refine and_congr Iff.rfl ?_
    rw [forall_pair_mem_iff_bounded]
    apply forall_congr'; intro P; apply imp_congr_right; intro _
    apply forall_congr'; intro Q; apply imp_congr_right; intro _
    apply forall_congr'; intro k; apply imp_congr_right; intro _
    apply forall_congr'; intro Q'; apply imp_congr_right; intro _
    apply forall_congr'; intro e; apply imp_congr_right; intro _
    apply imp_congr_right; intro _
    rw [exists_pair_mem_iff_bounded]
    apply exists_congr; intro P₀; apply and_congr_right; intro _
    apply exists_congr; intro Q₀; apply and_congr_right; intro _
    apply exists_congr; intro v₀; apply and_congr_right; intro _
    apply and_congr_right; intro _
    apply or_congr Iff.rfl
    apply or_congr
    · apply exists_congr; intro k₁; apply and_congr_right; intro _
      apply exists_congr; intro k₂; apply and_congr_right; intro _
      constructor
      · rintro ⟨P₁, hP₁, Q₁, -, e₁, -, P₂, hP₂, Q₂, -, e₂, -, R₁, hR₁, S₁, -, v₁, -,
          R₂, hR₂, S₂, -, v₂, -, rfl, rfl, rfl, rfl, H, HI⟩
        exact ⟨e₁, e₂, v₁, v₂, hP₁, hP₂, hR₁, hR₂, H, HI⟩
      · rintro ⟨e₁, e₂, v₁, v₂, h₁, h₂, g₁, g₂, H, HI⟩
        exact ⟨_, h₁, _, upair_mem_pair _ _, e₁, mem_upair_right _ _,
          _, h₂, _, upair_mem_pair _ _, e₂, mem_upair_right _ _,
          _, g₁, _, upair_mem_pair _ _, v₁, mem_upair_right _ _,
          _, g₂, _, upair_mem_pair _ _, v₂, mem_upair_right _ _, rfl, rfl, rfl, rfl, H, HI⟩
    · apply exists_congr; intro k₁; apply and_congr_right; intro _
      constructor
      · rintro ⟨P₁, hP₁, Q₁, -, e₁, -, R₁, hR₁, S₁, -, v₁, -, i, hi, rfl, rfl, H, HU⟩
        exact ⟨e₁, v₁, i, hi, hP₁, hR₁, H, HU⟩
      · rintro ⟨e₁, v₁, i, hi, h₁, g₁, H, HU⟩
        exact ⟨_, h₁, _, upair_mem_pair _ _, e₁, mem_upair_right _ _,
          _, g₁, _, upair_mem_pair _ _, v₁, mem_upair_right _ _, i, hi, rfl, rfl, H, HU⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- (8.3): the graph of a syntactic operation with Δ₀ local rules is Δ₀. -/
theorem delta0_graphW (h w p e d : ℕ)
    (hA : ∀ a b c d : ℕ, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      Delta0Def.{u} {a, b, c, d} (fun _ v => A (v a) (v b) (v c) (v d)))
    (hI : ∀ a b c d e : ℕ, a ≠ b → a ≠ c → a ≠ d → a ≠ e → b ≠ c → b ≠ d → b ≠ e →
        c ≠ d → c ≠ e → d ≠ e →
      Delta0Def.{u} {a, b, c, d, e} (fun _ v => I (v a) (v b) (v c) (v d) (v e)))
    (hU : ∀ a b c d e : ℕ, a ≠ b → a ≠ c → a ≠ d → a ≠ e → b ≠ c → b ≠ d → b ≠ e →
        c ≠ d → c ≠ e → d ≠ e →
      Delta0Def.{u} {a, b, c, d, e} (fun _ v => U (v a) (v b) (v c) (v d) (v e)))
    (hhw : h ≠ w) (hhp : h ≠ p) (hhe : h ≠ e) (hhd : h ≠ d)
    (hwp : w ≠ p) (hwe : w ≠ e) (hwd : w ≠ d) (hpe : p ≠ e) (hpd : p ≠ d) (hed : e ≠ d) :
    Delta0Def.{u} {h, w, p, e, d} (fun _ v => GraphW (v h) (v w) A I U (v p) (v e) (v d)) := by
  set m := h + w + p + e + d + 1 with hm
  -- s := m, t := m+1, P := m+2, Q := m+3, k := m+4, P' := m+5
  have k0 := (delta0_isKPair (m + 2) (m + 4) e (by omega) (by omega)).and
    ((delta0_isKPair (m + 5) (m + 4) d (by omega) (by omega)).bex (m + 5) (m + 1) (by omega))
  have k1 := k0.bex (m + 4) (m + 3) (by omega)
  have k2 := k1.bex (m + 3) (m + 2) (by omega)
  have k3 := k2.bex (m + 2) m (by omega)
  have dd := (delta0_derSeqW w m (by omega)).and
    ((delta0_traceW (A := A) (I := I) (U := U) w p m (m + 1) hA hI hU (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)).and k3)
  have hh1 := dd.bex (m + 1) h (by omega)
  have hh := hh1.bex m h (by omega)
  refine (hh.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    unfold GraphW
    apply exists_congr; intro s; apply and_congr_right; intro _
    apply exists_congr; intro t; apply and_congr_right; intro _
    apply and_congr_right; intro _
    apply and_congr_right; intro _
    constructor
    · rintro ⟨P, hP, Q, -, k, -, rfl, P', hP', rfl⟩
      exact ⟨k, hP, hP'⟩
    · rintro ⟨k, hk, hk'⟩
      exact ⟨_, hk, _, singleton_mem_pair _ _, k, ZFSet.mem_singleton.mpr rfl, rfl,
        _, hk', rfl⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-! ### `NotFreeW` as an instance of the schema

`NotFreeW` above is a hand-written derivation-sequence recognizer specialised to "`x` is not
free".  Here the same predicate is obtained from the general schema instead: three local rules
compute the truth value of "`x` does not occur free" at every node of the syntax tree,
`delta0_graphW` yields the Δ₀-definability of the resulting graph, and `notFreeW_iff_graphW`
identifies that graph with `NotFreeW`. -/

/-- Two-valued output: `natZ 1` for "yes", `natZ 0` for "no". -/
def Bl (P : Prop) (v : ZFSet.{u}) : Prop := (P ∧ v = natZ 1) ∨ (¬ P ∧ v = natZ 0)

/-- Local rule at an atomic node: the value records whether the atom avoids `x`. -/
def nfAtomR (w x e v : ZFSet.{u}) : Prop := IsAtomicCodeW w e ∧ Bl (NFAtomicW w x e) v

/-- Local rule at an `imp` node: the conjunction of the children's values. -/
def nfImpR (_w _x v₁ v₂ v : ZFSet.{u}) : Prop := Bl (v₁ = natZ 1 ∧ v₂ = natZ 1) v

/-- Local rule at an `all` node: true when the bound variable is `x`, else the child's value. -/
def nfAllR (_w x i v₁ v : ZFSet.{u}) : Prop := Bl (i = x ∨ v₁ = natZ 1) v

theorem delta0_bl {s : Finset ℕ} {P : Pred.{u}} (hP : Delta0Def.{u} s P) (d : ℕ) :
    Delta0Def.{u} (s ∪ {d}) (fun D v => Bl (P D v) (v d)) :=
  (((hP.and (delta0_isNatZ 1 d)).or (hP.not.and (delta0_isNatZ 0 d))).congr
    (fun _ _ _ _ => Iff.rfl)).of_eq (Finset.union_self _)

theorem delta0_nfAtomR (a b c d : ℕ) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Delta0Def.{u} {a, b, c, d} (fun _ v => nfAtomR (v a) (v b) (v c) (v d)) :=
  (((delta0_isAtomicCodeW a c hac).and
    (delta0_bl (delta0_nfAtomicW a b c hab hac hbc) d)).congr (fun _ _ _ _ => Iff.rfl)).mono
    (by intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at hk ⊢
        tauto)

theorem delta0_nfImpR (a b c d e : ℕ) :
    Delta0Def.{u} {a, b, c, d, e} (fun _ v => nfImpR (v a) (v b) (v c) (v d) (v e)) :=
  ((delta0_bl ((delta0_isNatZ 1 c).and (delta0_isNatZ 1 d)) e).congr
    (fun _ _ _ _ => Iff.rfl)).mono
    (by intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at hk ⊢
        tauto)

theorem delta0_nfAllR (a b c d e : ℕ) :
    Delta0Def.{u} {a, b, c, d, e} (fun _ v => nfAllR (v a) (v b) (v c) (v d) (v e)) :=
  ((delta0_bl ((Delta0Def.eq.{u} c b).or (delta0_isNatZ 1 d)) e).congr
    (fun _ _ _ _ => Iff.rfl)).mono
    (by intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at hk ⊢
        tauto)

/-- (8.3) for "the variable `x` does not occur free", read off the general schema. -/
theorem delta0_graphW_nf (h w p e d : ℕ)
    (hhw : h ≠ w) (hhp : h ≠ p) (hhe : h ≠ e) (hhd : h ≠ d)
    (hwp : w ≠ p) (hwe : w ≠ e) (hwd : w ≠ d) (hpe : p ≠ e) (hpd : p ≠ d) (hed : e ≠ d) :
    Delta0Def.{u} {h, w, p, e, d}
      (fun _ v => GraphW (v h) (v w) nfAtomR nfImpR nfAllR (v p) (v e) (v d)) :=
  delta0_graphW h w p e d
    (fun a b c d hab hac had hbc hbd hcd => delta0_nfAtomR a b c d hab hac had hbc hbd hcd)
    (fun a b c d e _ _ _ _ _ _ _ _ _ _ => delta0_nfImpR a b c d e)
    (fun a b c d e _ _ _ _ _ _ _ _ _ _ => delta0_nfAllR a b c d e)
    hhw hhp hhe hhd hwp hwe hwd hpe hpd hed

/-! ### Correctness of the instance -/

theorem fv_imp_not_mem_iff (x : ℕ) (φ ψ : Fm) :
    x ∉ Fm.fv (Fm.imp φ ψ) ↔ (x ∉ Fm.fv φ ∧ x ∉ Fm.fv ψ) := by
  simp only [Fm.fv, Finset.mem_union, not_or]

theorem fv_all_not_mem_iff (x i : ℕ) (φ : Fm) :
    x ∉ Fm.fv (Fm.all i φ) ↔ (i = x ∨ x ∉ Fm.fv φ) := by
  simp only [Fm.fv]
  constructor
  · intro h
    by_cases hx : i = x
    · exact Or.inl hx
    · exact Or.inr (fun hmem => h (Finset.mem_erase.mpr ⟨fun hh => hx hh.symm, hmem⟩))
  · rintro (rfl | h) hmem
    · exact (Finset.mem_erase.mp hmem).1 rfl
    · exact h (Finset.mem_erase.mp hmem).2

theorem nfAtomicW_eq_iff (x i j : ℕ) :
    NFAtomicW ωZ.{u} (natZ x) (Fm.code (Fm.eq i j)) ↔ x ∉ Fm.fv (Fm.eq i j) := by
  simp only [Fm.fv, Finset.mem_insert, Finset.mem_singleton, not_or]
  constructor
  · rintro (H | ⟨a, -, b, -, hax, hbx, H | H⟩)
    · rw [Fm.code, ZFSet.pair_inj] at H
      exact absurd H.1 (natZ_ne (by decide))
    · rw [Fm.code, ZFSet.pair_inj, ZFSet.pair_inj] at H
      obtain ⟨-, rfl, rfl⟩ := H
      exact ⟨fun hh => hax (by rw [hh]), fun hh => hbx (by rw [hh])⟩
    · rw [Fm.code, ZFSet.pair_inj] at H
      exact absurd H.1 (natZ_ne (by decide))
  · rintro ⟨hi, hj⟩
    exact Or.inr ⟨natZ i, natZ_mem_ωZ i, natZ j, natZ_mem_ωZ j,
      fun hh => hi (natZ_injective hh).symm, fun hh => hj (natZ_injective hh).symm, Or.inl rfl⟩

theorem nfAtomicW_mem_iff (x i j : ℕ) :
    NFAtomicW ωZ.{u} (natZ x) (Fm.code (Fm.mem i j)) ↔ x ∉ Fm.fv (Fm.mem i j) := by
  simp only [Fm.fv, Finset.mem_insert, Finset.mem_singleton, not_or]
  constructor
  · rintro (H | ⟨a, -, b, -, hax, hbx, H | H⟩)
    · rw [Fm.code, ZFSet.pair_inj] at H
      exact absurd H.1 (natZ_ne (by decide))
    · rw [Fm.code, ZFSet.pair_inj] at H
      exact absurd H.1 (natZ_ne (by decide))
    · rw [Fm.code, ZFSet.pair_inj, ZFSet.pair_inj] at H
      obtain ⟨-, rfl, rfl⟩ := H
      exact ⟨fun hh => hax (by rw [hh]), fun hh => hbx (by rw [hh])⟩
  · rintro ⟨hi, hj⟩
    exact Or.inr ⟨natZ i, natZ_mem_ωZ i, natZ j, natZ_mem_ωZ j,
      fun hh => hi (natZ_injective hh).symm, fun hh => hj (natZ_injective hh).symm, Or.inr rfl⟩

/-- On an atomic code, `NFAtomicW` decides "`x` does not occur free". -/
theorem isAtomicCodeW_nf (x : ℕ) {e : ZFSet.{u}} (h : IsAtomicCodeW ωZ e) :
    ∃ φ : Fm, e = φ.code ∧ (NFAtomicW ωZ (natZ x) e ↔ x ∉ Fm.fv φ) := by
  rcases h with rfl | ⟨i, hi, j, hj, H⟩
  · exact ⟨Fm.falsum, rfl, iff_of_true (Or.inl rfl) (by simp [Fm.fv])⟩
  · obtain ⟨i', rfl⟩ := mem_ωZ_iff.mp hi
    obtain ⟨j', rfl⟩ := mem_ωZ_iff.mp hj
    rcases H with rfl | rfl
    · exact ⟨Fm.eq i' j', rfl, nfAtomicW_eq_iff x i' j'⟩
    · exact ⟨Fm.mem i' j', rfl, nfAtomicW_mem_iff x i' j'⟩

theorem nfCodeShape_imp {ψ : Fm} {a b : ZFSet.{u}}
    (h : ψ.code = ZFSet.pair (natZ 3) (ZFSet.pair a b)) :
    ∃ ψ₁ ψ₂ : Fm, ψ = Fm.imp ψ₁ ψ₂ ∧ a = ψ₁.code ∧ b = ψ₂.code := by
  cases ψ with
  | falsum => rw [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | eq i j => rw [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | mem i j => rw [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | imp φ₁ φ₂ =>
    rw [Fm.code, ZFSet.pair_inj, ZFSet.pair_inj] at h
    exact ⟨φ₁, φ₂, rfl, h.2.1.symm, h.2.2.symm⟩
  | all i φ₁ => rw [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))

theorem nfCodeShape_all {ψ : Fm} {i : ℕ} {a : ZFSet.{u}}
    (h : ψ.code = ZFSet.pair (natZ 4) (ZFSet.pair (natZ i) a)) :
    ∃ ψ₁ : Fm, ψ = Fm.all i ψ₁ ∧ a = ψ₁.code := by
  cases ψ with
  | falsum => rw [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | eq i j => rw [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | mem i j => rw [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | imp φ₁ φ₂ => rw [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | all j φ₁ =>
    rw [Fm.code, ZFSet.pair_inj, ZFSet.pair_inj] at h
    obtain ⟨-, hij, hab⟩ := h
    obtain rfl := natZ_injective hij
    exact ⟨φ₁, rfl, hab.symm⟩

/-! ### Soundness of the instance -/

theorem traceW_nf_entry {x : ℕ} {s t : ZFSet.{u}}
    (ht : TraceW ωZ nfAtomR nfImpR nfAllR (natZ x) s t) :
    ∀ n e v, ZFSet.pair (natZ n) e ∈ s → ZFSet.pair (natZ n) v ∈ t →
      ∃ φ : Fm, e = φ.code ∧ (v = natZ 1 ↔ x ∉ Fm.fv φ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro e v he hv
  obtain ⟨v', hv', H⟩ := ht.2 _ _ he
  obtain rfl : v' = v := ht.1.2 _ _ _ hv' hv
  rcases H with ⟨hat, hbl⟩ | ⟨k₁, hk₁, k₂, hk₂, e₁, e₂, v₁, v₂, h₁, h₂, g₁, g₂, rfl, HI⟩ |
    ⟨k₁, hk₁, e₁, v₁, i, hi, h₁, g₁, rfl, HU⟩
  · obtain ⟨φ, rfl, hiff⟩ := isAtomicCodeW_nf x hat
    refine ⟨φ, rfl, ?_⟩
    rcases hbl with ⟨hp, rfl⟩ | ⟨hp, rfl⟩
    · exact iff_of_true rfl (hiff.mp hp)
    · exact iff_of_false (fun hh => absurd hh (natZ_ne (by decide)))
        (fun hfv => hp (hiff.mpr hfv))
  · obtain ⟨n₁, hn₁, rfl⟩ := mem_natZ_iff.mp hk₁
    obtain ⟨n₂, hn₂, rfl⟩ := mem_natZ_iff.mp hk₂
    obtain ⟨φ₁, rfl, hf₁⟩ := ih n₁ hn₁ e₁ v₁ h₁ g₁
    obtain ⟨φ₂, rfl, hf₂⟩ := ih n₂ hn₂ e₂ v₂ h₂ g₂
    refine ⟨Fm.imp φ₁ φ₂, rfl, ?_⟩
    rw [fv_imp_not_mem_iff]
    rcases HI with ⟨hp, rfl⟩ | ⟨hp, rfl⟩
    · exact iff_of_true rfl ⟨hf₁.mp hp.1, hf₂.mp hp.2⟩
    · exact iff_of_false (fun hh => absurd hh (natZ_ne (by decide)))
        (fun hfv => hp ⟨hf₁.mpr hfv.1, hf₂.mpr hfv.2⟩)
  · obtain ⟨n₁, hn₁, rfl⟩ := mem_natZ_iff.mp hk₁
    obtain ⟨φ₁, rfl, hf₁⟩ := ih n₁ hn₁ e₁ v₁ h₁ g₁
    obtain ⟨i', rfl⟩ := mem_ωZ_iff.mp hi
    refine ⟨Fm.all i' φ₁, rfl, ?_⟩
    rw [fv_all_not_mem_iff]
    rcases HU with ⟨hp, rfl⟩ | ⟨hp, rfl⟩
    · refine iff_of_true rfl ?_
      rcases hp with hp | hp
      · exact Or.inl (natZ_injective hp)
      · exact Or.inr (hf₁.mp hp)
    · refine iff_of_false (fun hh => absurd hh (natZ_ne (by decide))) (fun hfv => hp ?_)
      rcases hfv with rfl | hfv
      · exact Or.inl rfl
      · exact Or.inr (hf₁.mpr hfv)

/-! ### Completeness of the instance -/

open Classical in
/-- The value the rules attach to a code: `natZ 1` when it codes a formula avoiding `x`. -/
noncomputable def nfValZ (x : ℕ) (y : ZFSet.{u}) : ZFSet.{u} :=
  if ∃ φ : Fm, y = φ.code ∧ x ∉ Fm.fv φ then natZ 1 else natZ 0

theorem nfValZ_eq_zero_or_one (x : ℕ) (y : ZFSet.{u}) :
    nfValZ.{u} x y = natZ 1 ∨ nfValZ.{u} x y = natZ 0 := by
  unfold nfValZ; split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem nfValZ_code_eq_one_iff (x : ℕ) (φ : Fm) :
    nfValZ.{u} x φ.code = natZ 1 ↔ x ∉ Fm.fv φ := by
  unfold nfValZ; split_ifs with h
  · refine iff_of_true rfl ?_
    obtain ⟨ψ, hψ, hfv⟩ := h
    rwa [Fm.code_injective hψ]
  · exact iff_of_false (fun hh => absurd hh (natZ_ne (by decide))) (fun hfv => h ⟨φ, rfl, hfv⟩)

theorem nfValZ_mem_Lω (x : ℕ) (y : ZFSet.{u}) : nfValZ.{u} x y ∈ L Ordinal.omega0 := by
  rcases nfValZ_eq_zero_or_one x y with h | h <;> rw [h]
  · exact natZ_mem_Lω 1
  · exact natZ_mem_Lω 0

/-- The computation sequence of a formula for the rules of "`x` not free": the values run
alongside the ordinary derivation sequence `Fm.der φ` of `Code.lean`. -/
theorem traceW_nf_seqOf_der (x : ℕ) (φ : Fm) :
    TraceW ωZ.{u} nfAtomR nfImpR nfAllR (natZ x)
      (seqOfAux 0 (Fm.der.{u} φ)) (seqOfAux 0 ((Fm.der.{u} φ).map (nfValZ x))) := by
  refine ⟨isFunc_seqOfAux _, ?_⟩
  intro k e hke
  obtain ⟨n, z, hz, hp⟩ := mem_seqOfAux.mp hke
  rw [ZFSet.pair_inj] at hp
  obtain ⟨hk, he⟩ := hp
  subst hk
  subst he
  have key : ∀ (m : ℕ) (y : ZFSet.{u}), (Fm.der.{u} φ)[m]? = some y →
      ZFSet.pair (natZ m) (nfValZ x y) ∈ seqOfAux 0 ((Fm.der.{u} φ).map (nfValZ x)) := by
    intro m y hy
    exact mem_seqOfAux.mpr ⟨m, nfValZ x y, by simp [hy], by simp⟩
  have keys : ∀ (m : ℕ) (y : ZFSet.{u}), (Fm.der.{u} φ)[m]? = some y →
      ZFSet.pair (natZ m) y ∈ seqOfAux 0 (Fm.der.{u} φ) := by
    intro m y hy
    exact mem_seqOfAux.mpr ⟨m, y, hy, by simp⟩
  refine ⟨nfValZ x e, by simpa using key n e hz, ?_⟩
  have hzmem : e ∈ Fm.der.{u} φ := by
    obtain ⟨hn, hh⟩ := List.getElem?_eq_some_iff.mp hz
    exact hh ▸ List.getElem_mem hn
  obtain ⟨y, hy, H⟩ := Fm.der_good.{u} φ n e hz
  rw [hz] at hy
  obtain rfl := Option.some.inj hy
  rcases H with H | ⟨n₁, hn₁, n₂, hn₂, y₁, y₂, hy₁, hy₂, H⟩ | ⟨n₁, hn₁, y₁, i, hy₁, H⟩
  · refine Or.inl ⟨H, ?_⟩
    obtain ⟨φ₀, hz0, hiff⟩ := isAtomicCodeW_nf x H
    by_cases hp : NFAtomicW ωZ.{u} (natZ x) e
    · refine Or.inl ⟨hp, ?_⟩
      rw [hz0]
      exact (nfValZ_code_eq_one_iff x φ₀).mpr (hiff.mp hp)
    · refine Or.inr ⟨hp, ?_⟩
      rcases nfValZ_eq_zero_or_one x e with h1 | h0
      · exact absurd (hiff.mpr ((nfValZ_code_eq_one_iff x φ₀).mp (hz0 ▸ h1))) hp
      · exact h0
  · obtain ⟨ψ, rfl⟩ := Fm.mem_der.{u} φ e hzmem
    obtain ⟨ψ₁, ψ₂, rfl, rfl, rfl⟩ := nfCodeShape_imp H
    refine Or.inr (Or.inl ⟨natZ n₁, by simpa [natZ_mem_natZ_iff] using hn₁, natZ n₂,
      by simpa [natZ_mem_natZ_iff] using hn₂, ψ₁.code, ψ₂.code, nfValZ x ψ₁.code,
      nfValZ x ψ₂.code, keys _ _ hy₁, keys _ _ hy₂, key _ _ hy₁, key _ _ hy₂, rfl, ?_⟩)
    by_cases hc : nfValZ.{u} x ψ₁.code = natZ 1 ∧ nfValZ.{u} x ψ₂.code = natZ 1
    · refine Or.inl ⟨hc, (nfValZ_code_eq_one_iff x (Fm.imp ψ₁ ψ₂)).mpr ?_⟩
      rw [fv_imp_not_mem_iff]
      exact ⟨(nfValZ_code_eq_one_iff x ψ₁).mp hc.1, (nfValZ_code_eq_one_iff x ψ₂).mp hc.2⟩
    · refine Or.inr ⟨hc, ?_⟩
      rcases nfValZ_eq_zero_or_one x (Fm.imp ψ₁ ψ₂).code with h1 | h0
      · refine absurd ?_ hc
        have := (nfValZ_code_eq_one_iff x (Fm.imp ψ₁ ψ₂)).mp h1
        rw [fv_imp_not_mem_iff] at this
        exact ⟨(nfValZ_code_eq_one_iff x ψ₁).mpr this.1, (nfValZ_code_eq_one_iff x ψ₂).mpr this.2⟩
      · exact h0
  · obtain ⟨ψ, rfl⟩ := Fm.mem_der.{u} φ e hzmem
    obtain ⟨ψ₁, rfl, rfl⟩ := nfCodeShape_all H
    refine Or.inr (Or.inr ⟨natZ n₁, by simpa [natZ_mem_natZ_iff] using hn₁, ψ₁.code,
      nfValZ x ψ₁.code, natZ i, natZ_mem_ωZ i, keys _ _ hy₁, key _ _ hy₁, rfl, ?_⟩)
    by_cases hc : natZ.{u} i = natZ x ∨ nfValZ.{u} x ψ₁.code = natZ 1
    · refine Or.inl ⟨hc, (nfValZ_code_eq_one_iff x (Fm.all i ψ₁)).mpr ?_⟩
      rw [fv_all_not_mem_iff]
      rcases hc with hc | hc
      · exact Or.inl (natZ_injective hc)
      · exact Or.inr ((nfValZ_code_eq_one_iff x ψ₁).mp hc)
    · refine Or.inr ⟨hc, ?_⟩
      rcases nfValZ_eq_zero_or_one x (Fm.all i ψ₁).code with h1 | h0
      · refine absurd ?_ hc
        have := (nfValZ_code_eq_one_iff x (Fm.all i ψ₁)).mp h1
        rw [fv_all_not_mem_iff] at this
        rcases this with rfl | this
        · exact Or.inl rfl
        · exact Or.inr ((nfValZ_code_eq_one_iff x ψ₁).mpr this)
      · exact h0

/-- Correctness of the instance: the graph (8.3) built from the three local rules recognises
exactly the codes of formulas in which `x` does not occur free. -/
theorem graphW_nf_iff (x : ℕ) (e : ZFSet.{u}) :
    GraphW (L Ordinal.omega0) ωZ nfAtomR nfImpR nfAllR (natZ.{u} x) e (natZ 1) ↔
      ∃ φ : Fm, e = φ.code ∧ x ∉ Fm.fv φ := by
  constructor
  · rintro ⟨s, -, t, -, hs, ht, k, hke, hkd⟩
    obtain ⟨d, hd, hdom⟩ := hs.2.1
    have hkd' : k ∈ d := (hdom k).mpr ⟨e, hke⟩
    obtain ⟨M, rfl⟩ := mem_ωZ_iff.mp hd
    obtain ⟨p, -, rfl⟩ := mem_natZ_iff.mp hkd'
    obtain ⟨φ, rfl, hiff⟩ := traceW_nf_entry ht p e (natZ 1) hke hkd
    exact ⟨φ, rfl, hiff.mp rfl⟩
  · rintro ⟨φ, rfl, hfv⟩
    refine ⟨seqOfAux 0 (Fm.der.{u} φ), ?_, seqOfAux 0 ((Fm.der.{u} φ).map (nfValZ x)), ?_,
      derSeqW_seqOf_der φ, traceW_nf_seqOf_der x φ, natZ ((Fm.der.{u} φ).length - 1), ?_, ?_⟩
    · apply seqOfAux_mem_Lω
      intro y hy
      obtain ⟨ψ, rfl⟩ := Fm.mem_der.{u} φ y hy
      exact ψ.code_mem_Lω
    · apply seqOfAux_mem_Lω
      intro y hy
      obtain ⟨z, -, rfl⟩ := List.mem_map.mp hy
      exact nfValZ_mem_Lω x z
    · exact mem_seqOfAux.mpr ⟨(Fm.der.{u} φ).length - 1, φ.code, Fm.der_last.{u} φ, by simp⟩
    · refine mem_seqOfAux.mpr ⟨(Fm.der.{u} φ).length - 1, natZ 1, ?_, by simp⟩
      rw [List.getElem?_map, Fm.der_last.{u} φ]
      exact congrArg some ((nfValZ_code_eq_one_iff x φ).mpr hfv)

/-- U-19: the hand-written recognizer `NotFreeW` is the instance of the general schema (8.3) at
the local rules `nfAtomR`, `nfImpR`, `nfAllR`. -/
theorem notFreeW_iff_graphW (x : ℕ) (e : ZFSet.{u}) :
    NotFreeW (L Ordinal.omega0) ωZ (natZ.{u} x) e ↔
      GraphW (L Ordinal.omega0) ωZ nfAtomR nfImpR nfAllR (natZ.{u} x) e (natZ 1) :=
  (notFreeW_iff x e).trans (graphW_nf_iff x e).symm

end BM4.ST
