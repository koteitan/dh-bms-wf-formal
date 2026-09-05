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

theorem isDom_seqOfAux (l : List ZFSet.{u}) : IsDom (seqOfAux 0 l) (natZ l.length) := by
  intro a
  rw [mem_natZ_iff]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y, l[p]? = some y := ⟨l[p], List.getElem?_eq_some_iff.mpr ⟨hp, rfl⟩⟩
    exact ⟨y, mem_seqOfAux.mpr ⟨p, y, hy, by simp⟩⟩
  · rintro ⟨b, hb⟩
    obtain ⟨n, y, hy, hp⟩ := mem_seqOfAux.mp hb
    rw [ZFSet.pair_inj] at hp
    exact ⟨n, (List.getElem?_eq_some_iff.mp hy).1, by simpa using hp.1⟩

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

end BM4.ST
