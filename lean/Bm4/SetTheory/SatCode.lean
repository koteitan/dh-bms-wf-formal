/-
  Part III, §8.2: satisfaction codes (Definition 8.3, Lemma 8.2, Lemma 8.4) for named-variable
  formulas.  Assignments are finite sequences over `A` (functions with domain a natural number).
  Every clause of a satisfaction code is guarded by the appropriateness condition `Asn_A(e, a)`
  of (8.4): `a` is an `A`-valued finite sequence whose domain covers every free variable of the
  code `e`.  Accordingly the update `Update(a, i, x, b)` of §8.1 fills the newly created slots
  with `x`, so that an appropriate assignment for `∀v_i φ` updates to an appropriate assignment
  for `φ`.
-/
import Bm4.SetTheory.CodeFV

universe u

namespace BM4.ST

open Fm Classical

/-! ### Values, finite sequences, updates -/

/-- `x` is the value of the sequence `a` at index `i` (default `∅`). -/
def ValAt (a i x : ZFSet.{u}) : Prop :=
  ZFSet.pair i x ∈ a ∨ ((∀ y, ZFSet.pair i y ∉ a) ∧ x = ∅)

/-- `a` is a finite sequence over `A`: a function with domain an element of `w` (a natural
number when `w = ωZ`) and values in `A`. -/
def IsSeqA (w A a : ZFSet.{u}) : Prop :=
  IsFunc a ∧ (∃ d ∈ w, IsDom a d) ∧ ∀ i x, ZFSet.pair i x ∈ a → x ∈ A

/-- `i` lies in the domain of `a`. -/
def InDomZ (a i : ZFSet.{u}) : Prop := ∃ y, ZFSet.pair i y ∈ a

/-- `Asn_A(e, a)` of (8.4): `a` is an appropriate `A`-valued assignment for the code `e`, i.e.
a finite sequence over `A` whose domain covers every free variable of `e`. -/
def IsAsn (h w A e a : ZFSet.{u}) : Prop :=
  IsSeqA w A a ∧ ∀ i ∈ w, ¬ NotFreeW h w i e → InDomZ a i

/-- The bounded form of `InDomZ`. -/
theorem inDomZ_iff_bounded (a i : ZFSet.{u}) :
    InDomZ a i ↔ ∃ p ∈ a, ∃ q ∈ p, ∃ y ∈ q, p = ZFSet.pair i y := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨_, hy, _, upair_mem_pair i y, y, mem_upair_right i y, rfl⟩
  · rintro ⟨p, hp, q, -, y, -, rfl⟩
    exact ⟨y, hp⟩

/-- `NotFreeW` on the code of `φ` is `k ∉ fv φ`. -/
theorem notFreeW_code_iff (k : ℕ) (φ : Fm) :
    NotFreeW (L Ordinal.omega0) ωZ (natZ.{u} k) φ.code ↔ k ∉ Fm.fv φ := by
  rw [notFreeW_iff]
  constructor
  · rintro ⟨ψ, hψ, hk⟩
    rw [Fm.code_injective hψ]
    exact hk
  · exact fun h => ⟨φ, rfl, h⟩

/-- `IsAsn` on the code of `φ`: the domain of `a` covers `fv φ`. -/
theorem isAsn_code_iff {A a : ZFSet.{u}} {φ : Fm} :
    IsAsn (L Ordinal.omega0) ωZ A φ.code a ↔
      IsSeqA ωZ A a ∧ ∀ k ∈ Fm.fv φ, InDomZ a (natZ k) := by
  refine and_congr Iff.rfl ⟨fun H k hk => ?_, fun H i hi hnf => ?_⟩
  · exact H (natZ k) (natZ_mem_ωZ k) (by rw [notFreeW_code_iff]; exact fun h => h hk)
  · obtain ⟨k, rfl⟩ := mem_ωZ_iff.mp hi
    rw [notFreeW_code_iff] at hnf
    exact H k (not_not.mp hnf)

/-- The guard of the quantifier clause on the code of `φ`: the domain of `a` covers
`fv φ \ {i}`, which is `fv (∀v_i φ)`. -/
theorem allGuard_code_iff {a : ZFSet.{u}} {φ : Fm} {i : ℕ} :
    (∀ k ∈ ωZ.{u}, k ≠ natZ i → ¬ NotFreeW (L Ordinal.omega0) ωZ k φ.code → InDomZ a k) ↔
      ∀ k ∈ (Fm.fv φ).erase i, InDomZ a (natZ k) := by
  constructor
  · intro H k hk
    rw [Finset.mem_erase] at hk
    refine H (natZ k) (natZ_mem_ωZ k) (fun hc => hk.1 (natZ_injective hc)) ?_
    rw [notFreeW_code_iff]
    exact fun h => h hk.2
  · intro H j hj hji hnf
    obtain ⟨k, rfl⟩ := mem_ωZ_iff.mp hj
    rw [notFreeW_code_iff] at hnf
    exact H k (Finset.mem_erase.mpr ⟨fun hc => hji (by rw [hc]), not_not.mp hnf⟩)

/-- `b` is the sequence `a` updated at index `i` with value `x` (§8.1 `Update(a, i, x, b)`): the
pair `⟨i, x⟩`, the pairs of `a` not at `i`, and `⟨j, x⟩` for the new positions `j ∈ i` outside
the domain of `a` — the paper's convention that the newly created slots are filled with `x`. -/
def IsUpdSeq (a i x b : ZFSet.{u}) : Prop :=
  ∀ p, p ∈ b ↔ p = ZFSet.pair i x ∨ (p ∈ a ∧ ∀ y, p ≠ ZFSet.pair i y) ∨
    (∃ j ∈ i, (∀ y, ZFSet.pair j y ∉ a) ∧ p = ZFSet.pair j x)

/-- `b` is `a` padded with pairs `⟨k, ∅⟩`, i.e. with the default value of an index outside the
domain.  Padding does not change any value of the sequence. -/
def IsPadOf (a b : ZFSet.{u}) : Prop :=
  a ⊆ b ∧ ∀ p ∈ b, p ∈ a ∨ ∃ k, p = ZFSet.pair k ∅

/-- The value of a sequence at a natural-number index (default `∅`). -/
noncomputable def SeqVal (a : ZFSet.{u}) (i : ℕ) : ZFSet.{u} :=
  if h : ∃ x, ZFSet.pair (natZ i) x ∈ a then Classical.choose h else ∅

theorem isUpdSeq_unique {a i x b b' : ZFSet.{u}} (h : IsUpdSeq a i x b) (h' : IsUpdSeq a i x b') :
    b = b' := by
  ext p; rw [h p, h' p]

theorem seqVal_spec {a : ZFSet.{u}} (hf : IsFunc a) {i : ℕ} {x : ZFSet.{u}}
    (hx : ZFSet.pair (natZ i) x ∈ a) : SeqVal a i = x := by
  unfold SeqVal
  rw [dif_pos ⟨x, hx⟩]
  exact hf.2 _ _ _ (Classical.choose_spec (⟨x, hx⟩ : ∃ x, ZFSet.pair (natZ i) x ∈ a)) hx

theorem seqVal_of_notMem {a : ZFSet.{u}} {i : ℕ} (h : ∀ y, ZFSet.pair (natZ i) y ∉ a) :
    SeqVal a i = ∅ := by
  unfold SeqVal
  rw [dif_neg]
  rintro ⟨y, hy⟩
  exact h y hy

theorem valAt_iff {a : ZFSet.{u}} (hf : IsFunc a) {i : ℕ} {x : ZFSet.{u}} :
    ValAt a (natZ i) x ↔ x = SeqVal a i := by
  unfold ValAt
  constructor
  · rintro (h | ⟨h, rfl⟩)
    · exact (seqVal_spec hf h).symm
    · exact (seqVal_of_notMem h).symm
  · rintro rfl
    by_cases h : ∃ y, ZFSet.pair (natZ i) y ∈ a
    · obtain ⟨y, hy⟩ := h
      left; rw [seqVal_spec hf hy]; exact hy
    · right
      push Not at h
      exact ⟨h, seqVal_of_notMem h⟩

/-- Padding with `∅` does not change the values of a sequence. -/
theorem seqVal_of_isPadOf {a b : ZFSet.{u}} (hfa : IsFunc a) (hfb : IsFunc b)
    (h : IsPadOf a b) : SeqVal b = SeqVal a := by
  funext k
  by_cases hex : ∃ y, ZFSet.pair (natZ k) y ∈ a
  · obtain ⟨y, hy⟩ := hex
    rw [seqVal_spec hfa hy, seqVal_spec hfb (h.1 hy)]
  · push Not at hex
    rw [seqVal_of_notMem hex]
    by_cases hexb : ∃ z, ZFSet.pair (natZ k) z ∈ b
    · obtain ⟨z, hz⟩ := hexb
      rw [seqVal_spec hfb hz]
      rcases h.2 _ hz with h1 | ⟨k', h1⟩
      · exact absurd h1 (hex z)
      · rw [ZFSet.pair_inj] at h1
        exact h1.2
    · push Not at hexb
      exact seqVal_of_notMem hexb

theorem seqVal_mem_of_inDom {A a : ZFSet.{u}} (ha : IsSeqA ωZ A a) {i : ℕ}
    (h : InDomZ a (natZ i)) : SeqVal a i ∈ A := by
  obtain ⟨y, hy⟩ := h
  rw [seqVal_spec ha.1 hy]
  exact ha.2.2 _ _ hy

/-- If `∅ ∈ A`, every value of the sequence (including the default at an index outside the
domain) lies in `A`. -/
theorem seqVal_mem {A a : ZFSet.{u}} (ha : IsSeqA ωZ A a) (hemp : ∅ ∈ A) (i : ℕ) :
    SeqVal a i ∈ A := by
  by_cases h : ∃ y, ZFSet.pair (natZ i) y ∈ a
  · exact seqVal_mem_of_inDom ha h
  · push Not at h
    rw [seqVal_of_notMem h]
    exact hemp

theorem ωZ_transitive : ZFSet.IsTransitive ωZ.{u} := by
  intro x hx y hy
  obtain ⟨n, rfl⟩ := mem_ωZ_iff.mp hx
  obtain ⟨m, _, rfl⟩ := mem_natZ_iff.mp hy
  exact natZ_mem_ωZ m

/-- Elements of the domain of a sequence are naturals. -/
theorem isSeqA_index {w A a i x : ZFSet.{u}} (hw : w.IsTransitive) (ha : IsSeqA w A a)
    (h : ZFSet.pair i x ∈ a) : i ∈ w := by
  obtain ⟨d, hd, hdom⟩ := ha.2.1
  exact hw.subset_of_mem hd ((hdom i).mpr ⟨x, h⟩)

/-- Domain of a sequence over `ωZ` is some `natZ n`. -/
theorem isSeqA_dom {A a : ZFSet.{u}} (ha : IsSeqA ωZ A a) : ∃ n, IsDom a (natZ n) := by
  obtain ⟨d, hd, hdom⟩ := ha.2.1
  obtain ⟨n, rfl⟩ := mem_ωZ_iff.mp hd
  exact ⟨n, hdom⟩

/-- The update of a sequence, as a set. -/
noncomputable def updSeq (a i x : ZFSet.{u}) : ZFSet.{u} :=
  insert (ZFSet.pair i x)
    (ZFSet.sep (fun p => ∀ y, p ≠ ZFSet.pair i y) a ∪
      ZFSet.pairSep (fun j _ => ∀ y, ZFSet.pair j y ∉ a) i ({x} : ZFSet.{u}))

theorem isUpdSeq_updSeq (a i x : ZFSet.{u}) : IsUpdSeq a i x (updSeq a i x) := by
  intro p
  unfold updSeq
  rw [ZFSet.mem_insert_iff, ZFSet.mem_union, ZFSet.mem_sep, ZFSet.mem_pairSep]
  apply or_congr Iff.rfl
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨j, hj, z, hz, rfl, hy⟩
    rw [ZFSet.mem_singleton] at hz
    subst hz
    exact ⟨j, hj, hy, rfl⟩
  · rintro ⟨j, hj, hy, rfl⟩
    exact ⟨j, hj, x, ZFSet.mem_singleton.mpr rfl, rfl, hy⟩

theorem natZ_union (m n : ℕ) : natZ.{u} m ∪ natZ n = natZ (max m n) := by
  ext x
  rw [ZFSet.mem_union, mem_natZ_iff, mem_natZ_iff, mem_natZ_iff]
  constructor
  · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
    · exact ⟨k, by omega, rfl⟩
    · exact ⟨k, by omega, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    rcases lt_or_ge k m with h | h
    · exact Or.inl ⟨k, h, rfl⟩
    · exact Or.inr ⟨k, by omega, rfl⟩

/-- The update of a sequence exists as a finite sequence over `A`; its domain covers that of `a`
together with `i`, and there its values are those of `Function.update (SeqVal a) i x`. -/
theorem exists_updSeq {A a : ZFSet.{u}} (ha : IsSeqA ωZ A a) (i : ℕ) {x : ZFSet.{u}}
    (hx : x ∈ A) :
    ∃ b, IsUpdSeq a (natZ i) x b ∧ IsSeqA ωZ A b ∧
      (∀ k : ℕ, InDomZ a (natZ k) ∨ k = i → InDomZ b (natZ k)) ∧
      (∀ k : ℕ, InDomZ a (natZ k) ∨ k = i →
        SeqVal b k = Function.update (SeqVal a) i x k) := by
  obtain ⟨n, hdom⟩ := isSeqA_dom ha
  have hf := ha.1
  refine ⟨updSeq a (natZ i) x, isUpdSeq_updSeq _ _ _, ?_, ?_, ?_⟩
  · have hup := isUpdSeq_updSeq a (natZ i) x
    refine ⟨⟨?_, ?_⟩, ⟨natZ (max n (i + 1)), natZ_mem_ωZ _, ?_⟩, ?_⟩
    · intro p hp
      rcases (hup p).mp hp with rfl | ⟨hpa, _⟩ | ⟨j, _, _, rfl⟩
      · exact ⟨_, _, rfl⟩
      · exact hf.1 p hpa
      · exact ⟨_, _, rfl⟩
    · intro j y y' hy hy'
      rcases (hup _).mp hy with h1 | ⟨h1, h1'⟩ | ⟨j₁, hj₁, hj₁', h1⟩ <;>
        rcases (hup _).mp hy' with h2 | ⟨h2, h2'⟩ | ⟨j₂, hj₂, hj₂', h2⟩
      · rw [ZFSet.pair_inj] at h1 h2; rw [h1.2, h2.2]
      · rw [ZFSet.pair_inj] at h1; exact absurd rfl (h1.1 ▸ h2' y')
      · rw [ZFSet.pair_inj] at h1 h2; obtain ⟨rfl, rfl⟩ := h2
        exact absurd hj₂ (h1.1 ▸ fun h => (ZFSet.mem_irrefl _) h)
      · rw [ZFSet.pair_inj] at h2; exact absurd rfl (h2.1 ▸ h1' y)
      · exact hf.2 _ _ _ h1 h2
      · rw [ZFSet.pair_inj] at h2; obtain ⟨rfl, rfl⟩ := h2; exact absurd h1 (hj₂' y)
      · rw [ZFSet.pair_inj] at h1 h2; obtain ⟨rfl, rfl⟩ := h1
        exact absurd hj₁ (h2.1 ▸ fun h => (ZFSet.mem_irrefl _) h)
      · rw [ZFSet.pair_inj] at h1; obtain ⟨rfl, rfl⟩ := h1; exact absurd h2 (hj₁' y')
      · rw [ZFSet.pair_inj] at h1 h2; rw [h1.2, h2.2]
    · intro j
      rw [mem_natZ_iff]
      constructor
      · rintro ⟨m, hm, rfl⟩
        by_cases hmi : m = i
        · subst hmi; exact ⟨x, (hup _).mpr (Or.inl rfl)⟩
        · by_cases hmn : m < n
          · obtain ⟨y, hy⟩ := (hdom (natZ m)).mp (mem_natZ_iff.mpr ⟨m, hmn, rfl⟩)
            refine ⟨y, (hup _).mpr (Or.inr (Or.inl ⟨hy, fun y' h => ?_⟩))⟩
            rw [ZFSet.pair_inj] at h
            exact hmi (natZ_injective h.1)
          · refine ⟨x, (hup _).mpr (Or.inr (Or.inr ⟨natZ m, mem_natZ_iff.mpr ⟨m, by omega, rfl⟩,
              fun y hy => ?_, rfl⟩))⟩
            have := (hdom (natZ m)).mpr ⟨y, hy⟩
            rw [mem_natZ_iff] at this
            obtain ⟨k, hk, hkm⟩ := this
            exact hmn (by rw [natZ_injective hkm]; exact hk)
      · rintro ⟨y, hy⟩
        rcases (hup _).mp hy with h1 | ⟨h1, _⟩ | ⟨j₁, hj₁, _, h1⟩
        · rw [ZFSet.pair_inj] at h1; exact ⟨i, by omega, h1.1⟩
        · have := (hdom j).mpr ⟨y, h1⟩
          obtain ⟨m, hm, rfl⟩ := mem_natZ_iff.mp this
          exact ⟨m, by omega, rfl⟩
        · rw [ZFSet.pair_inj] at h1; obtain ⟨rfl, rfl⟩ := h1
          obtain ⟨m, hm, rfl⟩ := mem_natZ_iff.mp hj₁
          exact ⟨m, by omega, rfl⟩
    · intro j y hy
      rcases (hup _).mp hy with h1 | ⟨h1, _⟩ | ⟨j₁, _, _, h1⟩
      · rw [ZFSet.pair_inj] at h1; rw [h1.2]; exact hx
      · exact ha.2.2 _ _ h1
      · rw [ZFSet.pair_inj] at h1; rw [h1.2]; exact hx
  · -- domain
    have hup := isUpdSeq_updSeq a (natZ i) x
    rintro k (⟨y, hy⟩ | rfl)
    · by_cases hki : k = i
      · subst hki; exact ⟨x, (hup _).mpr (Or.inl rfl)⟩
      · refine ⟨y, (hup _).mpr (Or.inr (Or.inl ⟨hy, fun y' h => ?_⟩))⟩
        rw [ZFSet.pair_inj] at h
        exact hki (natZ_injective h.1)
    · exact ⟨x, (hup _).mpr (Or.inl rfl)⟩
  · -- values
    have hup := isUpdSeq_updSeq a (natZ i) x
    have hfb : IsFunc (updSeq a (natZ i) x) := by
      refine ⟨fun p hp => ?_, fun j y y' hy hy' => ?_⟩
      · rcases (hup p).mp hp with rfl | ⟨hpa, _⟩ | ⟨j, _, _, rfl⟩
        · exact ⟨_, _, rfl⟩
        · exact hf.1 p hpa
        · exact ⟨_, _, rfl⟩
      · rcases (hup _).mp hy with h1 | ⟨h1, h1'⟩ | ⟨j₁, hj₁, hj₁', h1⟩ <;>
          rcases (hup _).mp hy' with h2 | ⟨h2, h2'⟩ | ⟨j₂, hj₂, hj₂', h2⟩
        · rw [ZFSet.pair_inj] at h1 h2; rw [h1.2, h2.2]
        · rw [ZFSet.pair_inj] at h1; exact absurd rfl (h1.1 ▸ h2' y')
        · rw [ZFSet.pair_inj] at h1 h2; obtain ⟨rfl, rfl⟩ := h2
          exact absurd hj₂ (h1.1 ▸ fun h => (ZFSet.mem_irrefl _) h)
        · rw [ZFSet.pair_inj] at h2; exact absurd rfl (h2.1 ▸ h1' y)
        · exact hf.2 _ _ _ h1 h2
        · rw [ZFSet.pair_inj] at h2; obtain ⟨rfl, rfl⟩ := h2; exact absurd h1 (hj₂' y)
        · rw [ZFSet.pair_inj] at h1 h2; obtain ⟨rfl, rfl⟩ := h1
          exact absurd hj₁ (h2.1 ▸ fun h => (ZFSet.mem_irrefl _) h)
        · rw [ZFSet.pair_inj] at h1; obtain ⟨rfl, rfl⟩ := h1; exact absurd h2 (hj₁' y')
        · rw [ZFSet.pair_inj] at h1 h2; rw [h1.2, h2.2]
    rintro k (⟨y, hy⟩ | rfl)
    · by_cases hki : k = i
      · subst hki
        rw [Function.update_self]
        exact seqVal_spec hfb ((hup _).mpr (Or.inl rfl))
      · rw [Function.update_of_ne hki, seqVal_spec hf hy]
        apply seqVal_spec hfb
        refine (hup _).mpr (Or.inr (Or.inl ⟨hy, fun y' h => ?_⟩))
        rw [ZFSet.pair_inj] at h
        exact hki (natZ_injective h.1)
    · rw [Function.update_self]
      exact seqVal_spec hfb ((hup _).mpr (Or.inl rfl))

/-! ### Satisfaction codes (Definition 8.3) -/

/-- Definition 8.3, a satisfaction code for the structure `(A, ∈)`: `U` is a transitive auxiliary
set closed under pairs and unions containing `A`, `T`, `w`; `T` consists of pairs `⟨e, a⟩` of a
code `e ∈ h` and an *appropriate* `A`-valued assignment `a ∈ U` for `e`; and `T` satisfies the
Tarski clauses for all appropriate pairs.  The appropriateness condition is spelled out per
clause: for an atomic code it is that both variables lie in the domain of `a`, for `→` it is
appropriateness for both subcodes, and for `∀v_i` it is coverage of the free variables of the
matrix other than `i`. -/
structure SatCode (h w A U T : ZFSet.{u}) : Prop where
  trans : U.IsTransitive
  A_mem : A ∈ U
  T_mem : T ∈ U
  w_mem : w ∈ U
  pucl : ∀ x ∈ U, ∀ y ∈ U, ({x, y} : ZFSet.{u}) ∈ U ∧ ZFSet.sUnion x ∈ U
  proper : ∀ z ∈ T, ∃ e ∈ h, ∃ a ∈ U, z = ZFSet.pair e a ∧ IsCodeW h w e ∧ IsAsn h w A e a
  falsum : ∀ a ∈ U, IsSeqA w A a → ZFSet.pair (ZFSet.pair (natZ 0) (natZ 0)) a ∉ T
  eq : ∀ i ∈ w, ∀ j ∈ w, ∀ a ∈ U, IsSeqA w A a → InDomZ a i → InDomZ a j →
    (ZFSet.pair (ZFSet.pair (natZ 1) (ZFSet.pair i j)) a ∈ T ↔
      ∃ x ∈ A, ValAt a i x ∧ ∃ y ∈ A, ValAt a j y ∧ x = y)
  mem : ∀ i ∈ w, ∀ j ∈ w, ∀ a ∈ U, IsSeqA w A a → InDomZ a i → InDomZ a j →
    (ZFSet.pair (ZFSet.pair (natZ 2) (ZFSet.pair i j)) a ∈ T ↔
      ∃ x ∈ A, ValAt a i x ∧ ∃ y ∈ A, ValAt a j y ∧ x ∈ y)
  imp : ∀ e₁ ∈ h, ∀ e₂ ∈ h, IsCodeW h w e₁ → IsCodeW h w e₂ → ∀ a ∈ U,
    IsAsn h w A e₁ a → IsAsn h w A e₂ a →
    (ZFSet.pair (ZFSet.pair (natZ 3) (ZFSet.pair e₁ e₂)) a ∈ T ↔
      (ZFSet.pair e₁ a ∈ T → ZFSet.pair e₂ a ∈ T))
  all : ∀ i ∈ w, ∀ e ∈ h, IsCodeW h w e → ∀ a ∈ U, IsSeqA w A a →
    (∀ k ∈ w, k ≠ i → ¬ NotFreeW h w k e → InDomZ a k) →
    (ZFSet.pair (ZFSet.pair (natZ 4) (ZFSet.pair i e)) a ∈ T ↔
      ∀ x ∈ A, ∀ b ∈ U, IsUpdSeq a i x b → ZFSet.pair e b ∈ T)

/-! ### Lemma 8.2 -/

/-- Kuratowski pairs of elements of a pair/union-closed set lie in it. -/
theorem kpair_mem_of_pucl {U x y : ZFSet.{u}}
    (hcl : ∀ x ∈ U, ∀ y ∈ U, ({x, y} : ZFSet.{u}) ∈ U ∧ ZFSet.sUnion x ∈ U)
    (hx : x ∈ U) (hy : y ∈ U) : ZFSet.pair x y ∈ U := by
  have h1 : ({x} : ZFSet.{u}) ∈ U := by
    have := (hcl x hx x hx).1
    rwa [ZFSet.pair_eq_singleton] at this
  have h2 := (hcl x hx y hy).1
  exact (hcl _ h1 _ h2).1

theorem insert_mem_of_pucl {U x y : ZFSet.{u}}
    (hcl : ∀ x ∈ U, ∀ y ∈ U, ({x, y} : ZFSet.{u}) ∈ U ∧ ZFSet.sUnion x ∈ U)
    (hx : x ∈ U) (hy : y ∈ U) : insert x y ∈ U := by
  rw [insert_eq_sUnion]
  have h1 : ({x} : ZFSet.{u}) ∈ U := by
    have := (hcl x hx x hx).1
    rwa [ZFSet.pair_eq_singleton] at this
  exact (hcl _ (hcl _ h1 _ hy).1 _ (hcl _ h1 _ hy).1).2

/-- **Lemma 8.2**, first claim: *every* standard finite sequence code all of whose values lie in
`U` lies itself in `U`, for `U` transitive with `ωZ ∈ U` and closed under pairs and unions. -/
theorem seqU_mem_of_puCl {U a : ZFSet.{u}} (hU : U.IsTransitive) (hω : ωZ ∈ U)
    (hcl : ∀ x ∈ U, ∀ y ∈ U, ({x, y} : ZFSet.{u}) ∈ U ∧ ZFSet.sUnion x ∈ U)
    (ha : IsSeqA ωZ U a) : a ∈ U := by
  obtain ⟨n, hdom⟩ := isSeqA_dom ha
  -- the initial segments `a ∩ (natZ m × ⋯)`
  let seg : ℕ → ZFSet.{u} := fun m => ZFSet.sep (fun p => ∃ j ∈ natZ m, ∃ y, p = ZFSet.pair j y) a
  have hseg : ∀ m, seg m ∈ U := by
    intro m
    induction m with
    | zero =>
      have : seg 0 = ∅ := by
        ext p; simp only [seg, ZFSet.mem_sep, natZ, ZFSet.notMem_empty, false_and, exists_false,
          and_false]
      rw [this]
      -- `∅ ∈ A ∈ U`? not assumed; use `∅ ∈ ωZ ∈ U`
      exact hU.subset_of_mem hω (by simpa [natZ] using natZ_mem_ωZ.{u} 0)
    | succ m ih =>
      by_cases hm : ∃ y, ZFSet.pair (natZ m) y ∈ a
      · obtain ⟨y, hy⟩ := hm
        have : seg (m + 1) = insert (ZFSet.pair (natZ m) y) (seg m) := by
          ext p
          simp only [seg, ZFSet.mem_sep, ZFSet.mem_insert_iff]
          constructor
          · rintro ⟨hp, j, hj, z, rfl⟩
            obtain ⟨k, hk, rfl⟩ := mem_natZ_iff.mp hj
            rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
            · exact Or.inr ⟨hp, _, mem_natZ_iff.mpr ⟨k, hk, rfl⟩, z, rfl⟩
            · left; rw [ha.1.2 _ _ _ hp hy]
          · rintro (rfl | ⟨hp, j, hj, z, rfl⟩)
            · exact ⟨hy, _, mem_natZ_iff.mpr ⟨m, by omega, rfl⟩, y, rfl⟩
            · obtain ⟨k, hk, rfl⟩ := mem_natZ_iff.mp hj
              exact ⟨hp, _, mem_natZ_iff.mpr ⟨k, by omega, rfl⟩, z, rfl⟩
        rw [this]
        have hnU : natZ m ∈ U := hU.subset_of_mem hω (natZ_mem_ωZ m)
        have hyU : y ∈ U := ha.2.2 _ _ hy
        exact insert_mem_of_pucl hcl (kpair_mem_of_pucl hcl hnU hyU) ih
      · have : seg (m + 1) = seg m := by
          ext p
          simp only [seg, ZFSet.mem_sep]
          constructor
          · rintro ⟨hp, j, hj, z, rfl⟩
            obtain ⟨k, hk, rfl⟩ := mem_natZ_iff.mp hj
            rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
            · exact ⟨hp, _, mem_natZ_iff.mpr ⟨k, hk, rfl⟩, z, rfl⟩
            · exact absurd ⟨z, hp⟩ hm
          · rintro ⟨hp, j, hj, z, rfl⟩
            obtain ⟨k, hk, rfl⟩ := mem_natZ_iff.mp hj
            exact ⟨hp, _, mem_natZ_iff.mpr ⟨k, by omega, rfl⟩, z, rfl⟩
        rw [this]; exact ih
  have : a = seg n := by
    ext p
    simp only [seg, ZFSet.mem_sep]
    constructor
    · intro hp
      obtain ⟨j, y, rfl⟩ := ha.1.1 p hp
      exact ⟨hp, j, (hdom j).mpr ⟨y, hp⟩, y, rfl⟩
    · exact fun h => h.1
  rw [this]; exact hseg n

/-- A standard finite sequence over `A` is one over `U` when `A ∈ U` and `U` is transitive. -/
theorem isSeqA_of_mem {U A a : ZFSet.{u}} (hU : U.IsTransitive) (hAU : A ∈ U)
    (ha : IsSeqA ωZ A a) : IsSeqA ωZ.{u} U a :=
  ⟨ha.1, ha.2.1, fun i x hix => hU.subset_of_mem hAU (ha.2.2 i x hix)⟩

/-- **Lemma 8.2**, second claim: an `A`-valued finite assignment lies in `U` when `A ∈ U`. -/
theorem seq_mem_of_puCl {U A a : ZFSet.{u}} (hU : U.IsTransitive) (hAU : A ∈ U) (hω : ωZ ∈ U)
    (hcl : ∀ x ∈ U, ∀ y ∈ U, ({x, y} : ZFSet.{u}) ∈ U ∧ ZFSet.sUnion x ∈ U)
    (ha : IsSeqA ωZ A a) : a ∈ U :=
  seqU_mem_of_puCl hU hω hcl (isSeqA_of_mem hU hAU ha)

/-! #### Prefixing, appending and concatenation (Lemma 8.2, second claim) -/

/-- §8.1 `Concat(t, a, b)`: `b` is the concatenation of `t` (of length `m`) and `a`, so that
`b j = t j` for `j < m` and `b (m + j) = a j`. -/
def IsConcatSeq (t a b : ZFSet.{u}) : Prop :=
  ∃ m : ℕ, IsDom t (natZ m) ∧
    ∀ p, p ∈ b ↔ (p ∈ t ∨ ∃ (j : ℕ) (y : ZFSet.{u}),
      ZFSet.pair (natZ j) y ∈ a ∧ p = ZFSet.pair (natZ (m + j)) y)

/-- The one-element sequence `⟨0, x⟩`, used for `Cons` and `Append`. -/
noncomputable def singleSeq (x : ZFSet.{u}) : ZFSet.{u} := {ZFSet.pair (natZ 0) x}

theorem isSeqA_singleSeq {U x : ZFSet.{u}} (hx : x ∈ U) : IsSeqA ωZ.{u} U (singleSeq x) := by
  refine ⟨⟨fun p hp => ?_, fun i y y' hy hy' => ?_⟩, ⟨natZ 1, natZ_mem_ωZ 1, fun i => ?_⟩,
    fun i y hy => ?_⟩
  · rw [singleSeq, ZFSet.mem_singleton] at hp; exact ⟨_, _, hp⟩
  · rw [singleSeq, ZFSet.mem_singleton, ZFSet.pair_inj] at hy hy'
    rw [hy.2, hy'.2]
  · rw [singleSeq]
    constructor
    · intro hi
      obtain ⟨k, hk, rfl⟩ := mem_natZ_iff.mp hi
      rw [show k = 0 by omega]
      exact ⟨x, ZFSet.mem_singleton.mpr rfl⟩
    · rintro ⟨y, hy⟩
      rw [ZFSet.mem_singleton, ZFSet.pair_inj] at hy
      rw [hy.1]
      exact natZ_mem_natZ_iff.mpr (by omega)
  · rw [singleSeq, ZFSet.mem_singleton, ZFSet.pair_inj] at hy
    rw [hy.2]; exact hx

/-- The concatenation of two standard finite sequences over `U` is one. -/
theorem isSeqA_of_isConcatSeq {U t a b : ZFSet.{u}} (ht : IsSeqA ωZ U t) (ha : IsSeqA ωZ U a)
    (hb : IsConcatSeq t a b) : IsSeqA ωZ.{u} U b := by
  obtain ⟨m, hdomt, hmem⟩ := hb
  obtain ⟨n, hdoma⟩ := isSeqA_dom ha
  have hidx : ∀ (i y : ZFSet.{u}), ZFSet.pair i y ∈ t → ∃ k < m, i = natZ k := by
    intro i y hiy
    exact mem_natZ_iff.mp ((hdomt i).mpr ⟨y, hiy⟩)
  refine ⟨⟨fun p hp => ?_, fun i y y' hy hy' => ?_⟩,
    ⟨natZ (m + n), natZ_mem_ωZ _, fun i => ?_⟩, fun i y hy => ?_⟩
  · rcases (hmem p).mp hp with h | ⟨j, y, -, rfl⟩
    · exact ht.1.1 p h
    · exact ⟨_, _, rfl⟩
  · rcases (hmem _).mp hy with h1 | ⟨j, z, hja, e1⟩ <;>
      rcases (hmem _).mp hy' with h2 | ⟨j', z', hja', e2⟩
    · exact ht.1.2 _ _ _ h1 h2
    · obtain ⟨k, hk, hik⟩ := hidx _ _ h1
      obtain ⟨e2a, -⟩ := ZFSet.pair_injective e2
      exact absurd (natZ_injective (hik.symm.trans e2a)) (by omega)
    · obtain ⟨k, hk, hik⟩ := hidx _ _ h2
      obtain ⟨e1a, -⟩ := ZFSet.pair_injective e1
      exact absurd (natZ_injective (hik.symm.trans e1a)) (by omega)
    · obtain ⟨e1a, rfl⟩ := ZFSet.pair_injective e1
      obtain ⟨e2a, rfl⟩ := ZFSet.pair_injective e2
      have : j = j' := by
        have := natZ_injective (e1a.symm.trans e2a)
        omega
      subst this
      exact ha.1.2 _ _ _ hja hja'
  · constructor
    · intro hi
      obtain ⟨k, hk, rfl⟩ := mem_natZ_iff.mp hi
      rcases Nat.lt_or_ge k m with hkm | hkm
      · obtain ⟨y, hy⟩ := (hdomt (natZ k)).mp (natZ_mem_natZ_iff.mpr hkm)
        exact ⟨y, (hmem _).mpr (Or.inl hy)⟩
      · obtain ⟨y, hy⟩ := (hdoma (natZ (k - m))).mp (natZ_mem_natZ_iff.mpr (by omega))
        exact ⟨y, (hmem _).mpr (Or.inr ⟨k - m, y, hy, by rw [show m + (k - m) = k by omega]⟩)⟩
    · rintro ⟨y, hy⟩
      rcases (hmem _).mp hy with h | ⟨j, z, hja, e⟩
      · obtain ⟨k, hk, hik⟩ := hidx _ _ h
        rw [hik]; exact natZ_mem_natZ_iff.mpr (by omega)
      · obtain ⟨ea, -⟩ := ZFSet.pair_injective e
        obtain ⟨k, hk, hjk⟩ := mem_natZ_iff.mp ((hdoma (natZ j)).mpr ⟨z, hja⟩)
        have : j = k := natZ_injective hjk
        rw [ea]; exact natZ_mem_natZ_iff.mpr (by omega)
  · rcases (hmem _).mp hy with h | ⟨j, z, hja, e⟩
    · exact ht.2.2 _ _ h
    · obtain ⟨-, rfl⟩ := ZFSet.pair_injective e
      exact ha.2.2 _ _ hja

/-- **Lemma 8.2**: the concatenation of two standard finite sequences over `U` lies in `U`. -/
theorem concat_mem_of_puCl {U t a b : ZFSet.{u}} (hU : U.IsTransitive) (hω : ωZ ∈ U)
    (hcl : ∀ x ∈ U, ∀ y ∈ U, ({x, y} : ZFSet.{u}) ∈ U ∧ ZFSet.sUnion x ∈ U)
    (ht : IsSeqA ωZ U t) (ha : IsSeqA ωZ U a) (hb : IsConcatSeq t a b) : b ∈ U :=
  seqU_mem_of_puCl hU hω hcl (isSeqA_of_isConcatSeq ht ha hb)

/-- **Lemma 8.2**: prefixing a value (§8.1 `Cons(x, a, b)`) stays in `U`. -/
theorem cons_mem_of_puCl {U x a b : ZFSet.{u}} (hU : U.IsTransitive) (hω : ωZ ∈ U)
    (hcl : ∀ x ∈ U, ∀ y ∈ U, ({x, y} : ZFSet.{u}) ∈ U ∧ ZFSet.sUnion x ∈ U)
    (hx : x ∈ U) (ha : IsSeqA ωZ U a) (hb : IsConcatSeq (singleSeq x) a b) : b ∈ U :=
  concat_mem_of_puCl hU hω hcl (isSeqA_singleSeq hx) ha hb

/-- **Lemma 8.2**: appending a value (§8.1 `Append(a, x, b)`) stays in `U`. -/
theorem append_mem_of_puCl {U x a b : ZFSet.{u}} (hU : U.IsTransitive) (hω : ωZ ∈ U)
    (hcl : ∀ x ∈ U, ∀ y ∈ U, ({x, y} : ZFSet.{u}) ∈ U ∧ ZFSet.sUnion x ∈ U)
    (hx : x ∈ U) (ha : IsSeqA ωZ U a) (hb : IsConcatSeq a (singleSeq x) b) : b ∈ U :=
  concat_mem_of_puCl hU hω hcl ha (isSeqA_singleSeq hx) hb

/-- **Lemma 8.2**: the update of a standard finite sequence over `U` (§8.1 `Update(a, i, x, b)`)
stays in `U`. -/
theorem updSeq_mem_of_puCl {U a b x : ZFSet.{u}} (hU : U.IsTransitive) (hω : ωZ ∈ U)
    (hcl : ∀ x ∈ U, ∀ y ∈ U, ({x, y} : ZFSet.{u}) ∈ U ∧ ZFSet.sUnion x ∈ U)
    (ha : IsSeqA ωZ U a) (hx : x ∈ U) {i : ℕ} (hb : IsUpdSeq a (natZ i) x b) : b ∈ U := by
  obtain ⟨b', hb', hseq', -, -⟩ := exists_updSeq ha i hx
  rw [isUpdSeq_unique hb hb']
  exact seqU_mem_of_puCl hU hω hcl hseq'

/-! ### Lemma 8.4: correctness -/

theorem valAt_iff' {a : ZFSet.{u}} (hf : IsFunc a) (i : ℕ) (x : ZFSet.{u}) :
    ValAt a (natZ i) x ↔ x = SeqVal a i := valAt_iff hf

/-- Lemma 8.4 (8.6): correctness of any satisfaction code, on appropriate pairs. -/
theorem satCode_correct {A U T : ZFSet.{u}} (hc : SatCode (L Ordinal.omega0) ωZ A U T) (φ : Fm) :
    ∀ a, IsSeqA ωZ A a → (∀ k ∈ Fm.fv φ, InDomZ a (natZ k)) → a ∈ U →
      (ZFSet.pair φ.code a ∈ T ↔ SatIn A (SeqVal a) φ) := by
  induction φ with
  | falsum =>
    intro a ha _ haU
    simp only [Fm.code, SatIn, sat_falsum, iff_false]
    exact hc.falsum a haU ha
  | eq i j =>
    intro a ha hcov haU
    have hi : InDomZ a (natZ i) := hcov i (by simp [Fm.fv])
    have hj : InDomZ a (natZ j) := hcov j (by simp [Fm.fv])
    simp only [Fm.code, SatIn, sat_eq]
    rw [hc.eq _ (natZ_mem_ωZ i) _ (natZ_mem_ωZ j) a haU ha hi hj]
    constructor
    · rintro ⟨x, _, hx, y, _, hy, rfl⟩
      rw [valAt_iff ha.1] at hx hy
      rw [← hx, ← hy]
    · intro h
      exact ⟨_, seqVal_mem_of_inDom ha hi, (valAt_iff ha.1).mpr rfl,
        _, seqVal_mem_of_inDom ha hj, (valAt_iff ha.1).mpr rfl, h⟩
  | mem i j =>
    intro a ha hcov haU
    have hi : InDomZ a (natZ i) := hcov i (by simp [Fm.fv])
    have hj : InDomZ a (natZ j) := hcov j (by simp [Fm.fv])
    simp only [Fm.code, SatIn, sat_mem]
    rw [hc.mem _ (natZ_mem_ωZ i) _ (natZ_mem_ωZ j) a haU ha hi hj]
    constructor
    · rintro ⟨x, _, hx, y, _, hy, hxy⟩
      rw [valAt_iff ha.1] at hx hy
      rw [← hx, ← hy]; exact hxy
    · intro h
      exact ⟨_, seqVal_mem_of_inDom ha hi, (valAt_iff ha.1).mpr rfl,
        _, seqVal_mem_of_inDom ha hj, (valAt_iff ha.1).mpr rfl, h⟩
  | imp φ ψ ihφ ihψ =>
    intro a ha hcov haU
    have hcφ : ∀ k ∈ Fm.fv φ, InDomZ a (natZ k) := fun k hk =>
      hcov k (by simp only [Fm.fv, Finset.mem_union]; exact Or.inl hk)
    have hcψ : ∀ k ∈ Fm.fv ψ, InDomZ a (natZ k) := fun k hk =>
      hcov k (by simp only [Fm.fv, Finset.mem_union]; exact Or.inr hk)
    simp only [Fm.code, SatIn, sat_imp]
    rw [hc.imp _ (Fm.code_mem_Lω φ) _ (Fm.code_mem_Lω ψ) ((isCodeW_iff _).mpr ⟨φ, rfl⟩)
      ((isCodeW_iff _).mpr ⟨ψ, rfl⟩) a haU (isAsn_code_iff.mpr ⟨ha, hcφ⟩)
      (isAsn_code_iff.mpr ⟨ha, hcψ⟩)]
    rw [ihφ a ha hcφ haU, ihψ a ha hcψ haU]
  | all i φ ih =>
    intro a ha hcov haU
    simp only [Fm.fv] at hcov
    simp only [Fm.code, SatIn, sat_all]
    rw [hc.all _ (natZ_mem_ωZ i) _ (Fm.code_mem_Lω φ) ((isCodeW_iff _).mpr ⟨φ, rfl⟩) a haU ha
      (allGuard_code_iff.mpr hcov)]
    have key : ∀ x ∈ A, ∀ b, IsUpdSeq a (natZ i) x b →
        (ZFSet.pair φ.code b ∈ T ↔ SatIn A (Function.update (SeqVal a) i x) φ) ∧ b ∈ U := by
      intro x hx b hb
      obtain ⟨b', hb', hbseq, hbdom, hbval⟩ := exists_updSeq ha i hx
      have hbU : b' ∈ U := seq_mem_of_puCl hc.trans hc.A_mem hc.w_mem hc.pucl hbseq
      have hbcov : ∀ k ∈ Fm.fv φ, InDomZ b' (natZ k) := by
        intro k hk
        by_cases hki : k = i
        · exact hbdom k (Or.inr hki)
        · exact hbdom k (Or.inl (hcov k (Finset.mem_erase.mpr ⟨hki, hk⟩)))
      have hagree : ∀ k ∈ Fm.fv φ, SeqVal b' k = Function.update (SeqVal a) i x k := by
        intro k hk
        by_cases hki : k = i
        · exact hbval k (Or.inr hki)
        · exact hbval k (Or.inl (hcov k (Finset.mem_erase.mpr ⟨hki, hk⟩)))
      rw [isUpdSeq_unique hb hb']
      exact ⟨(ih b' hbseq hbcov hbU).trans (sat_congr hagree), hbU⟩
    constructor
    · intro H x hx
      obtain ⟨b, hb, -, -, -⟩ := exists_updSeq ha i hx
      obtain ⟨hiff, hbU⟩ := key x hx b hb
      exact hiff.mp (H x hx b hbU hb)
    · intro H x hx b hbU hb
      exact (key x hx b hb).1.mpr (H x hx)

/-- Uniqueness of the truth part. -/
theorem satCode_unique {A U U' T T' : ZFSet.{u}} (hc : SatCode (L Ordinal.omega0) ωZ A U T)
    (hc' : SatCode (L Ordinal.omega0) ωZ A U' T') : T = T' := by
  have key : ∀ {U U' T T' : ZFSet.{u}}, SatCode (L Ordinal.omega0) ωZ A U T →
      SatCode (L Ordinal.omega0) ωZ A U' T' → ∀ z ∈ T, z ∈ T' := by
    intro U U' T T' hc hc' z hz
    obtain ⟨e, _, a, haU, rfl, hcode, hasn⟩ := hc.proper z hz
    obtain ⟨φ, rfl⟩ := (isCodeW_iff e).mp hcode
    obtain ⟨ha, hcov⟩ := isAsn_code_iff.mp hasn
    have haU' : a ∈ U' := seq_mem_of_puCl hc'.trans hc'.A_mem hc'.w_mem hc'.pucl ha
    rw [satCode_correct hc' φ a ha hcov haU']
    exact (satCode_correct hc φ a ha hcov haU).mp hz
  ext z
  exact ⟨key hc hc' z, key hc' hc z⟩

/-! ### Δ0-definability -/

/-- The bounded form of `∀ y, pair i y ∉ a`. -/
theorem forall_pair_notMem_iff_bounded (a i : ZFSet.{u}) :
    (∀ y, ZFSet.pair i y ∉ a) ↔ ∀ p ∈ a, ∀ q ∈ p, ∀ y ∈ q, p ≠ ZFSet.pair i y := by
  constructor
  · intro H p hp q _ y _ hpy
    subst hpy; exact H y hp
  · intro H y hy
    exact H _ hy _ (upair_mem_pair i y) y (mem_upair_right i y) rfl

/-- `pair i x ∈ a ∨ ((∀ y, pair i y ∉ a) ∧ x = ∅)`. -/
theorem delta0_valAt (a i x : ℕ) (hai : a ≠ i) (hax : a ≠ x) (hix : i ≠ x) :
    Delta0Def {a, i, x} (fun _ v => ValAt (v a) (v i) (v x)) := by
  set m := a + i + x + 1 with hm
  have n1 := (delta0_isKPair m i (m + 2) (by omega) (by omega)).not
  have n2 := n1.ball (m + 2) (m + 1) (by omega)
  have n3 := n2.ball (m + 1) m (by omega)
  have hne := n3.ball m a (by omega)
  have h := (delta0_funVal a i x hai hax hix).or (hne.and (delta0_isEmpty x))
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    unfold ValAt
    rw [forall_pair_notMem_iff_bounded]
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- `InDomZ a i` is Δ0. -/
theorem delta0_inDomZ (a i : ℕ) (hai : a ≠ i) :
    Delta0Def {a, i} (fun _ v => InDomZ (v a) (v i)) := by
  set m := a + i + 1 with hm
  have h0 := delta0_isKPair m i (m + 2) (by omega) (by omega)
  have h1 := h0.bex (m + 2) (m + 1) (by omega)
  have h2 := h1.bex (m + 1) m (by omega)
  have hb := h2.bex m a (by omega)
  refine (hb.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    exact (inDomZ_iff_bounded (v a) (v i)).symm
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- `p = pair k ∅` in bounded form. -/
theorem delta0_eqPairEmpty (p j : ℕ) (hpj : p ≠ j) :
    Delta0Def {p, j} (fun _ v => v p = ZFSet.pair (v j) ∅) := by
  set m := p + j + 1 with hm
  have h0 := (delta0_isEmpty (m + 1)).and (delta0_isKPair p j (m + 1) (by omega) (by omega))
  have h1 := h0.bex (m + 1) m (by omega)
  have h := h1.bex m p (by omega)
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · rintro ⟨q, _, z, _, rfl, H⟩; exact H
    · intro H
      exact ⟨_, by rw [H]; exact upair_mem_pair _ _, ∅, mem_upair_right _ _, rfl, H⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- The bounded form of `∃ k, p = pair k ∅`. -/
theorem exists_pairEmpty_iff_bounded (p : ZFSet.{u}) :
    (∃ k, p = ZFSet.pair k ∅) ↔ ∃ q ∈ p, ∃ k ∈ q, p = ZFSet.pair k ∅ := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨{k}, singleton_mem_pair k ∅, k, ZFSet.mem_singleton.mpr rfl, rfl⟩
  · rintro ⟨q, -, k, -, h⟩
    exact ⟨k, h⟩

theorem delta0_isPadOf (a b : ℕ) (hab : a ≠ b) :
    Delta0Def {a, b} (fun _ v => IsPadOf (v a) (v b)) := by
  set m := a + b + 1 with hm
  have h1 := delta0_subset a b hab
  have i1 := (delta0_eqPairEmpty m (m + 2) (by omega)).bex (m + 2) (m + 1) (by omega)
  have i2 := i1.bex (m + 1) m (by omega)
  have h2 := ((Delta0Def.mem m a).or i2).ball m b (by omega)
  refine ((h1.and h2).congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    unfold IsPadOf
    refine and_congr Iff.rfl (forall_congr' fun p => imp_congr_right fun _ => ?_)
    exact or_congr Iff.rfl (exists_pairEmpty_iff_bounded p).symm
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

theorem delta0_isSeqA (w A a : ℕ) (hwA : w ≠ A) (hwa : w ≠ a) (hAa : A ≠ a) :
    Delta0Def {w, A, a} (fun _ v => IsSeqA (v w) (v A) (v a)) := by
  set m := w + A + a + 1 with hm
  have h1 := delta0_isFunc a
  have h2 := (delta0_isDom a m (by omega)).bex m w (by omega)
  -- `∀ p ∈ a, ∀ q ∈ p, ∀ i ∈ q, ∀ q' ∈ p, ∀ x ∈ q', p = pair i x → x ∈ A`
  have c0 := (delta0_isKPair (m + 1) (m + 3) (m + 5) (by omega) (by omega)).imp
    (Delta0Def.mem (m + 5) A)
  have c1 := c0.ball (m + 5) (m + 4) (by omega)
  have c2 := c1.ball (m + 4) (m + 1) (by omega)
  have c3 := c2.ball (m + 3) (m + 2) (by omega)
  have c4 := c3.ball (m + 2) (m + 1) (by omega)
  have h3 := c4.ball (m + 1) a (by omega)
  refine ((h1.and (h2.and h3)).congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    unfold IsSeqA
    refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
    rw [forall_pair_mem_iff_bounded]
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- Appropriateness `Asn_A(e, a)` is Δ0. -/
theorem delta0_isAsn (h w A e a : ℕ) (hhw : h ≠ w) (hhe : h ≠ e) (hwA : w ≠ A) (hwe : w ≠ e)
    (hwa : w ≠ a) (hAa : A ≠ a) :
    Delta0Def {h, w, A, e, a} (fun _ v => IsAsn (v h) (v w) (v A) (v e) (v a)) := by
  set m := h + w + A + e + a + 1 with hm
  have c1 := delta0_isSeqA w A a hwA hwa hAa
  have c2 := ((delta0_notFreeW h w m e (by omega) (by omega) hhe (by omega) hwe
    (by omega)).not.imp (delta0_inDomZ a m (by omega))).ball m w (by omega)
  refine ((c1.and c2).congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    exact Iff.rfl
  · intro k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- `pair j x ∈ b` in bounded form: `∃ p ∈ b, p = pair j x`. -/
theorem delta0_pairVarMem (b j x : ℕ) (hbj : b ≠ j) (hbx : b ≠ x) :
    Delta0Def {b, j, x} (fun _ v => ZFSet.pair (v j) (v x) ∈ v b) := by
  set m := b + j + x + 1 with hm
  have h := (delta0_isKPair m j x (by omega) (by omega)).bex m b (by omega)
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · rintro ⟨p, hp, rfl⟩; exact hp
    · intro H; exact ⟨_, H, rfl⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

theorem delta0_isUpdSeq (a i x b : ℕ) (hai : a ≠ i) (hax : a ≠ x) (hab : a ≠ b) (hix : i ≠ x)
    (hib : i ≠ b) (hxb : x ≠ b) :
    Delta0Def {a, i, x, b} (fun _ v => IsUpdSeq (v a) (v i) (v x) (v b)) := by
  set m := a + i + x + b + 1 with hm
  -- p := m, q := m+1, y := m+2, j := m+3
  have ne1 := (delta0_isKPair m i (m + 2) (by omega) (by omega)).not
  have ne2 := ne1.ball (m + 2) (m + 1) (by omega)
  have hneP := ne2.ball (m + 1) m (by omega)
  -- `∀ p' ∈ a, ∀ q ∈ p', ∀ y ∈ q, p' ≠ pair j y` (with `p' := m+4`, `q := m+5`, `y := m+6`)
  have nv1 := (delta0_isKPair (m + 4) (m + 3) (m + 6) (by omega) (by omega)).not
  have nv2 := nv1.ball (m + 6) (m + 5) (by omega)
  have nv3 := nv2.ball (m + 5) (m + 4) (by omega)
  have hnoval := nv3.ball (m + 4) a (by omega)
  have r1 := ((hnoval.and (delta0_isKPair m (m + 3) x (by omega) (by omega))).bex (m + 3) i
    (by omega))
  have rhs := (delta0_isKPair m i x (by omega) (by omega)).or
    (((Delta0Def.mem m a).and hneP).or r1)
  have h1 := rhs.ball m b (by omega)
  have h2 := delta0_funVal b i x (by omega) (by omega) hix
  have h3 := (hneP.imp (Delta0Def.mem m b)).ball m a (by omega)
  have h4 := (hnoval.imp (delta0_pairVarMem b (m + 3) x (by omega) (by omega))).ball (m + 3) i
    (by omega)
  refine (((h1.and h2).and (h3.and h4)).congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    unfold IsUpdSeq
    constructor
    · rintro ⟨⟨H1, H2⟩, H3, H4⟩ p
      constructor
      · intro hp
        rcases H1 p hp with h | ⟨hpa, hne⟩ | ⟨j, hj, hnv, hpj⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨hpa, (forall_ne_pair_iff_bounded p (v i)).mpr hne⟩)
        · exact Or.inr (Or.inr ⟨j, hj, (forall_pair_notMem_iff_bounded (v a) j).mpr hnv, hpj⟩)
      · rintro (rfl | ⟨hpa, hne⟩ | ⟨j, hj, hnv, rfl⟩)
        · exact H2
        · exact H3 p hpa ((forall_ne_pair_iff_bounded p (v i)).mp hne)
        · exact H4 j hj ((forall_pair_notMem_iff_bounded (v a) j).mp hnv)
    · intro H
      refine ⟨⟨fun p hp => ?_, ?_⟩, fun p hpa hne => ?_, fun j hj hnv => ?_⟩
      · rcases (H p).mp hp with h | ⟨hpa, hne⟩ | ⟨j, hj, hnv, hpj⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨hpa, (forall_ne_pair_iff_bounded p (v i)).mp hne⟩)
        · exact Or.inr (Or.inr ⟨j, hj, (forall_pair_notMem_iff_bounded (v a) j).mp hnv, hpj⟩)
      · exact (H _).mpr (Or.inl rfl)
      · exact (H p).mpr (Or.inr (Or.inl ⟨hpa, (forall_ne_pair_iff_bounded p (v i)).mpr hne⟩))
      · exact (H _).mpr (Or.inr (Or.inr ⟨j, hj, (forall_pair_notMem_iff_bounded (v a) j).mpr hnv,
          rfl⟩))
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- `pair (pair (natZ n) (pair i j)) a ∈ T` is Δ0. -/
theorem delta0_codeMem (n : ℕ) (T i j a : ℕ) (hTi : T ≠ i) (hTj : T ≠ j) (hTa : T ≠ a)
    (hia : i ≠ a) (hja : j ≠ a) :
    Delta0Def {T, i, j, a}
      (fun _ v => ZFSet.pair (ZFSet.pair (natZ n) (ZFSet.pair (v i) (v j))) (v a) ∈ v T) := by
  set m := T + i + j + a + 1 with hm
  have h0 := (delta0_tagPair n (m + 2) i j (by omega) (by omega)).and
    (delta0_isKPair m (m + 2) a (by omega) (by omega))
  have h1 := h0.bex (m + 2) (m + 1) (by omega)
  have h2 := h1.bex (m + 1) m (by omega)
  have h := h2.bex m T (by omega)
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · rintro ⟨p, hp, q, _, e, _, rfl, rfl⟩; exact hp
    · intro H
      exact ⟨_, H, _, singleton_mem_pair _ _, _, ZFSet.mem_singleton.mpr rfl, rfl, rfl⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- `pair (pair (natZ 0) (natZ 0)) a ∈ T` is Δ0. -/
theorem delta0_codeMem0 (T a : ℕ) (hTa : T ≠ a) :
    Delta0Def {T, a} (fun _ v => ZFSet.pair (ZFSet.pair (natZ 0) (natZ 0)) (v a) ∈ v T) := by
  set m := T + a + 1 with hm
  have h0 := (delta0_tagPair0 (m + 2)).and (delta0_isKPair m (m + 2) a (by omega) (by omega))
  have h1 := h0.bex (m + 2) (m + 1) (by omega)
  have h2 := h1.bex (m + 1) m (by omega)
  have h := h2.bex m T (by omega)
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · rintro ⟨p, hp, q, _, e, _, rfl, rfl⟩; exact hp
    · intro H
      exact ⟨_, H, _, singleton_mem_pair _ _, _, ZFSet.mem_singleton.mpr rfl, rfl, rfl⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

section SatCodeDelta0

variable (h w A U T : ℕ) (hhw : h ≠ w) (hhA : h ≠ A) (hhU : h ≠ U) (hhT : h ≠ T) (hwA : w ≠ A)
  (hwU : w ≠ U) (hwT : w ≠ T) (hAU : A ≠ U) (hAT : A ≠ T) (hUT : U ≠ T)

include hhw hhA hhU hhT hwA hwU hwT hAU hAT hUT

theorem delta0_sc_pucl : Delta0Def {h, w, A, U, T} (fun _ v =>
    ∀ x ∈ v U, ∀ y ∈ v U, ({x, y} : ZFSet.{u}) ∈ v U ∧ ZFSet.sUnion x ∈ v U) := by
  set m := h + w + A + U + T + 1 with hm
  have p1 := (delta0_isUPair (m + 2) m (m + 1) (by omega) (by omega)).bex (m + 2) U (by omega)
  have p2 := (delta0_isSUnion (m + 3) m (by omega)).bex (m + 3) U (by omega)
  have p3 := (p1.and p2).ball (m + 1) U (by omega)
  have p4 := p3.ball m U (by omega)
  refine (p4.congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    apply forall_congr'; intro x; apply imp_congr_right; intro _
    apply forall_congr'; intro y; apply imp_congr_right; intro _
    apply and_congr
    · exact ⟨fun ⟨_, hp, e⟩ => e ▸ hp, fun H => ⟨_, H, rfl⟩⟩
    · exact ⟨fun ⟨_, hp, e⟩ => e ▸ hp, fun H => ⟨_, H, rfl⟩⟩
  · intro k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

theorem delta0_sc_proper : Delta0Def {h, w, A, U, T} (fun _ v =>
    ∀ z ∈ v T, ∃ e ∈ v h, ∃ a ∈ v U, z = ZFSet.pair e a ∧ IsCodeW (v h) (v w) e ∧
      IsAsn (v h) (v w) (v A) e a) := by
  set m := h + w + A + U + T + 1 with hm
  have c0 := (delta0_isKPair m (m + 1) (m + 2) (by omega) (by omega)).and
    ((delta0_isCodeW h w (m + 1) hhw (by omega) (by omega)).and
      (delta0_isAsn h w A (m + 1) (m + 2) hhw (by omega) hwA (by omega) (by omega)
        (by omega)))
  have c1 := c0.bex (m + 2) U (by omega)
  have c2 := c1.bex (m + 1) h (by omega)
  have c3 := c2.ball m T (by omega)
  refine (c3.congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
  · intro k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

theorem delta0_sc_falsum : Delta0Def {h, w, A, U, T} (fun _ v =>
    ∀ a ∈ v U, IsSeqA (v w) (v A) a → ZFSet.pair (ZFSet.pair (natZ 0) (natZ 0)) a ∉ v T) := by
  set m := h + w + A + U + T + 1 with hm
  have c0 := (delta0_isSeqA w A m hwA (by omega) (by omega)).imp
    (delta0_codeMem0 T m (by omega)).not
  have c1 := c0.ball m U (by omega)
  refine (c1.congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
  · intro k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

theorem delta0_sc_eq : Delta0Def {h, w, A, U, T} (fun _ v =>
    ∀ i ∈ v w, ∀ j ∈ v w, ∀ a ∈ v U, IsSeqA (v w) (v A) a → InDomZ a i → InDomZ a j →
      (ZFSet.pair (ZFSet.pair (natZ 1) (ZFSet.pair i j)) a ∈ v T ↔
        ∃ x ∈ v A, ValAt a i x ∧ ∃ y ∈ v A, ValAt a j y ∧ x = y)) := by
  set m := h + w + A + U + T + 1 with hm
  -- i := m, j := m+1, a := m+2, x := m+3, y := m+4
  have r0 := (delta0_valAt (m + 2) (m + 1) (m + 4) (by omega) (by omega) (by omega)).and
    (Delta0Def.eq (m + 3) (m + 4))
  have r1 := r0.bex (m + 4) A (by omega)
  have r2 := (delta0_valAt (m + 2) m (m + 3) (by omega) (by omega) (by omega)).and r1
  have r3 := r2.bex (m + 3) A (by omega)
  have c0 := (delta0_isSeqA w A (m + 2) hwA (by omega) (by omega)).imp
    ((delta0_inDomZ (m + 2) m (by omega)).imp
      ((delta0_inDomZ (m + 2) (m + 1) (by omega)).imp
        ((delta0_codeMem 1 T m (m + 1) (m + 2) (by omega) (by omega) (by omega) (by omega)
          (by omega)).iff r3)))
  have c1 := c0.ball (m + 2) U (by omega)
  have c2 := c1.ball (m + 1) w (by omega)
  have c3 := c2.ball m w (by omega)
  refine (c3.congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
  · intro k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

theorem delta0_sc_mem : Delta0Def {h, w, A, U, T} (fun _ v =>
    ∀ i ∈ v w, ∀ j ∈ v w, ∀ a ∈ v U, IsSeqA (v w) (v A) a → InDomZ a i → InDomZ a j →
      (ZFSet.pair (ZFSet.pair (natZ 2) (ZFSet.pair i j)) a ∈ v T ↔
        ∃ x ∈ v A, ValAt a i x ∧ ∃ y ∈ v A, ValAt a j y ∧ x ∈ y)) := by
  set m := h + w + A + U + T + 1 with hm
  have r0 := (delta0_valAt (m + 2) (m + 1) (m + 4) (by omega) (by omega) (by omega)).and
    (Delta0Def.mem (m + 3) (m + 4))
  have r1 := r0.bex (m + 4) A (by omega)
  have r2 := (delta0_valAt (m + 2) m (m + 3) (by omega) (by omega) (by omega)).and r1
  have r3 := r2.bex (m + 3) A (by omega)
  have c0 := (delta0_isSeqA w A (m + 2) hwA (by omega) (by omega)).imp
    ((delta0_inDomZ (m + 2) m (by omega)).imp
      ((delta0_inDomZ (m + 2) (m + 1) (by omega)).imp
        ((delta0_codeMem 2 T m (m + 1) (m + 2) (by omega) (by omega) (by omega) (by omega)
          (by omega)).iff r3)))
  have c1 := c0.ball (m + 2) U (by omega)
  have c2 := c1.ball (m + 1) w (by omega)
  have c3 := c2.ball m w (by omega)
  refine (c3.congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
  · intro k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

theorem delta0_sc_imp : Delta0Def {h, w, A, U, T} (fun _ v =>
    ∀ e₁ ∈ v h, ∀ e₂ ∈ v h, IsCodeW (v h) (v w) e₁ → IsCodeW (v h) (v w) e₂ →
      ∀ a ∈ v U, IsAsn (v h) (v w) (v A) e₁ a → IsAsn (v h) (v w) (v A) e₂ a →
        (ZFSet.pair (ZFSet.pair (natZ 3) (ZFSet.pair e₁ e₂)) a ∈ v T ↔
          (ZFSet.pair e₁ a ∈ v T → ZFSet.pair e₂ a ∈ v T))) := by
  set m := h + w + A + U + T + 1 with hm
  -- e₁ := m, e₂ := m+1, a := m+2
  have r0 := (delta0_funVal T m (m + 2) (by omega) (by omega) (by omega)).imp
    (delta0_funVal T (m + 1) (m + 2) (by omega) (by omega) (by omega))
  have c0 := (delta0_isAsn h w A m (m + 2) hhw (by omega) hwA (by omega) (by omega)
      (by omega)).imp
    ((delta0_isAsn h w A (m + 1) (m + 2) hhw (by omega) hwA (by omega) (by omega)
      (by omega)).imp
      ((delta0_codeMem 3 T m (m + 1) (m + 2) (by omega) (by omega) (by omega) (by omega)
        (by omega)).iff r0))
  have c1 := c0.ball (m + 2) U (by omega)
  have c2 := (delta0_isCodeW h w m hhw (by omega) (by omega)).imp
    ((delta0_isCodeW h w (m + 1) hhw (by omega) (by omega)).imp c1)
  have c3 := c2.ball (m + 1) h (by omega)
  have c4 := c3.ball m h (by omega)
  refine (c4.congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
  · intro k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

theorem delta0_sc_all : Delta0Def {h, w, A, U, T} (fun _ v =>
    ∀ i ∈ v w, ∀ e ∈ v h, IsCodeW (v h) (v w) e → ∀ a ∈ v U, IsSeqA (v w) (v A) a →
      (∀ k ∈ v w, k ≠ i → ¬ NotFreeW (v h) (v w) k e → InDomZ a k) →
      (ZFSet.pair (ZFSet.pair (natZ 4) (ZFSet.pair i e)) a ∈ v T ↔
        ∀ x ∈ v A, ∀ b ∈ v U, IsUpdSeq a i x b → ZFSet.pair e b ∈ v T)) := by
  set m := h + w + A + U + T + 1 with hm
  -- i := m, e := m+1, a := m+2, x := m+3, b := m+4
  have r0 := (delta0_isUpdSeq (m + 2) m (m + 3) (m + 4) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)).imp
    (delta0_funVal T (m + 1) (m + 4) (by omega) (by omega) (by omega))
  have r1 := r0.ball (m + 4) U (by omega)
  have r2 := r1.ball (m + 3) A (by omega)
  have g0 := ((Delta0Def.eq (m + 5) m).not.imp
    ((delta0_notFreeW h w (m + 5) (m + 1) hhw (by omega) (by omega) (by omega) (by omega)
      (by omega)).not.imp (delta0_inDomZ (m + 2) (m + 5) (by omega)))).ball (m + 5) w (by omega)
  have c0 := (delta0_isSeqA w A (m + 2) hwA (by omega) (by omega)).imp
    (g0.imp
      ((delta0_codeMem 4 T m (m + 1) (m + 2) (by omega) (by omega) (by omega) (by omega)
        (by omega)).iff r2))
  have c1 := c0.ball (m + 2) U (by omega)
  have c2 := (delta0_isCodeW h w (m + 1) hhw (by omega) (by omega)).imp c1
  have c3 := c2.ball (m + 1) h (by omega)
  have c4 := c3.ball m w (by omega)
  refine (c4.congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
  · intro k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

theorem delta0_satCode :
    Delta0Def {h, w, A, U, T} (fun _ v => SatCode (v h) (v w) (v A) (v U) (v T)) := by
  set m := h + w + A + U + T + 1 with hm
  have f1 := (delta0_isTransitive U).mono
    (by intro k; simp only [Finset.mem_insert, Finset.mem_singleton]; omega :
      ({U} : Finset ℕ) ⊆ {h, w, A, U, T})
  have f2 := (Delta0Def.mem A U).mono
    (by intro k; simp only [Finset.mem_insert, Finset.mem_singleton]; omega :
      ({A, U} : Finset ℕ) ⊆ {h, w, A, U, T})
  have f3 := (Delta0Def.mem T U).mono
    (by intro k; simp only [Finset.mem_insert, Finset.mem_singleton]; omega :
      ({T, U} : Finset ℕ) ⊆ {h, w, A, U, T})
  have f4 := (Delta0Def.mem w U).mono
    (by intro k; simp only [Finset.mem_insert, Finset.mem_singleton]; omega :
      ({w, U} : Finset ℕ) ⊆ {h, w, A, U, T})
  have f6 := delta0_sc_pucl h w A U T hhw hhA hhU hhT hwA hwU hwT hAU hAT hUT
  have f7 := delta0_sc_proper h w A U T hhw hhA hhU hhT hwA hwU hwT hAU hAT hUT
  have f8 := delta0_sc_falsum h w A U T hhw hhA hhU hhT hwA hwU hwT hAU hAT hUT
  have f9 := delta0_sc_eq h w A U T hhw hhA hhU hhT hwA hwU hwT hAU hAT hUT
  have f10 := delta0_sc_mem h w A U T hhw hhA hhU hhT hwA hwU hwT hAU hAT hUT
  have f11 := delta0_sc_imp h w A U T hhw hhA hhU hhT hwA hwU hwT hAU hAT hUT
  have f12 := delta0_sc_all h w A U T hhw hhA hhU hhT hwA hwU hwT hAU hAT hUT
  have hall := f1.and (f2.and (f3.and (f4.and (f6.and (f7.and (f8.and (f9.and
    (f10.and (f11.and f12)))))))))
  refine (hall.congr ?_).mono ?_
  · intro D v _ _
    constructor
    · rintro ⟨h1, h2, h3, h4, h6, h7, h8, h9, h10, h11, h12⟩
      exact ⟨h1, h2, h3, h4, h6, h7, h8, h9, h10, h11, h12⟩
    · intro H
      exact ⟨H.trans, H.A_mem, H.T_mem, H.w_mem, H.pucl, H.proper, H.falsum,
        H.eq, H.mem, H.imp, H.all⟩
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase] at hk ⊢
    omega

end SatCodeDelta0

/-! ### Existence in the universe -/

/-- The set of all finite sequences over `A`. -/
noncomputable def Seqs (A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (IsSeqA ωZ A) (ZFSet.powerset (ZFSet.pairSep (fun _ _ => True) ωZ A))

theorem mem_Seqs {A a : ZFSet.{u}} : a ∈ Seqs A ↔ IsSeqA ωZ A a := by
  unfold Seqs
  rw [ZFSet.mem_sep, ZFSet.mem_powerset]
  constructor
  · exact fun h => h.2
  · intro ha
    refine ⟨fun p hp => ?_, ha⟩
    obtain ⟨j, y, rfl⟩ := ha.1.1 p hp
    rw [ZFSet.mem_pairSep]
    exact ⟨j, isSeqA_index ωZ_transitive ha hp, y, ha.2.2 _ _ hp, rfl, trivial⟩

/-- The truth set of `(A, ∈)`: the appropriate pairs that hold. -/
noncomputable def TruthSet (A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ (φ : Fm) (a : ZFSet.{u}), z = ZFSet.pair (Fm.code.{u} φ) a ∧
      IsSeqA ωZ A a ∧ (∀ k ∈ Fm.fv φ, InDomZ a (natZ k)) ∧ SatIn A (SeqVal a) φ)
    (ZFSet.pairSep (fun _ _ => True) (L Ordinal.omega0) (Seqs A))

theorem mem_TruthSet {A z : ZFSet.{u}} : z ∈ TruthSet A ↔
    ∃ (φ : Fm) (a : ZFSet.{u}), z = ZFSet.pair (Fm.code.{u} φ) a ∧ IsSeqA ωZ A a ∧
      (∀ k ∈ Fm.fv φ, InDomZ a (natZ k)) ∧ SatIn A (SeqVal a) φ := by
  unfold TruthSet
  rw [ZFSet.mem_sep]
  constructor
  · exact fun h => h.2
  · rintro ⟨φ, a, rfl, ha, hcov, hs⟩
    refine ⟨?_, φ, a, rfl, ha, hcov, hs⟩
    rw [ZFSet.mem_pairSep]
    exact ⟨_, Fm.code_mem_Lω φ, a, mem_Seqs.mpr ha, rfl, trivial⟩

theorem pair_code_mem_TruthSet {A a : ZFSet.{u}} {φ : Fm} :
    ZFSet.pair (Fm.code.{u} φ) a ∈ TruthSet A ↔ IsSeqA ωZ A a ∧
      (∀ k ∈ Fm.fv φ, InDomZ a (natZ k)) ∧ SatIn A (SeqVal a) φ := by
  rw [mem_TruthSet]
  constructor
  · rintro ⟨ψ, b, h, hb, hcov, hs⟩
    rw [ZFSet.pair_inj] at h
    obtain ⟨h1, rfl⟩ := h
    rw [Fm.code_injective h1]
    exact ⟨hb, hcov, hs⟩
  · rintro ⟨ha, hcov, hs⟩
    exact ⟨φ, a, rfl, ha, hcov, hs⟩

/-- The Tarski clauses of Definition 8.3 hold for `TruthSet A`, given a suitable `U`. -/
theorem satCode_truthSet_of {A U : ZFSet.{u}} (hUtrans : U.IsTransitive)
    (hAU : A ∈ U) (hTU : TruthSet A ∈ U) (hωU : ωZ ∈ U)
    (hpucl : ∀ x ∈ U, ∀ y ∈ U, ({x, y} : ZFSet.{u}) ∈ U ∧ ZFSet.sUnion x ∈ U) :
    SatCode (L Ordinal.omega0) ωZ A U (TruthSet A) := by
  have hseqU : ∀ a, IsSeqA ωZ A a → a ∈ U := fun a ha =>
    seq_mem_of_puCl hUtrans hAU hωU hpucl ha
  refine ⟨hUtrans, hAU, hTU, hωU, hpucl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨φ, a, rfl, ha, hcov, hs⟩ := mem_TruthSet.mp hz
    exact ⟨_, Fm.code_mem_Lω φ, a, hseqU a ha, rfl, (isCodeW_iff _).mpr ⟨φ, rfl⟩,
      isAsn_code_iff.mpr ⟨ha, hcov⟩⟩
  · intro a _ _ h
    exact ((pair_code_mem_TruthSet (φ := Fm.falsum)).mp h).2.2
  · intro i hi j hj a _ ha hdi hdj
    obtain ⟨i₀, rfl⟩ := mem_ωZ_iff.mp hi
    obtain ⟨j₀, rfl⟩ := mem_ωZ_iff.mp hj
    have hcov : ∀ k ∈ Fm.fv (Fm.eq i₀ j₀), InDomZ a (natZ k) := by
      intro k hk
      simp only [Fm.fv, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hdi
      · exact hdj
    rw [show ZFSet.pair (natZ 1) (ZFSet.pair (natZ i₀) (natZ j₀)) = Fm.code.{u} (Fm.eq i₀ j₀) from rfl,
      pair_code_mem_TruthSet]
    simp only [SatIn, sat_eq]
    constructor
    · rintro ⟨-, -, h⟩
      exact ⟨_, seqVal_mem_of_inDom ha hdi, (valAt_iff ha.1).mpr rfl,
        _, seqVal_mem_of_inDom ha hdj, (valAt_iff ha.1).mpr rfl, h⟩
    · rintro ⟨x, _, hx, y, _, hy, rfl⟩
      rw [valAt_iff ha.1] at hx hy
      exact ⟨ha, hcov, by rw [← hx, ← hy]⟩
  · intro i hi j hj a _ ha hdi hdj
    obtain ⟨i₀, rfl⟩ := mem_ωZ_iff.mp hi
    obtain ⟨j₀, rfl⟩ := mem_ωZ_iff.mp hj
    have hcov : ∀ k ∈ Fm.fv (Fm.mem i₀ j₀), InDomZ a (natZ k) := by
      intro k hk
      simp only [Fm.fv, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hdi
      · exact hdj
    rw [show ZFSet.pair (natZ 2) (ZFSet.pair (natZ i₀) (natZ j₀)) = Fm.code.{u} (Fm.mem i₀ j₀) from rfl,
      pair_code_mem_TruthSet]
    simp only [SatIn, sat_mem]
    constructor
    · rintro ⟨-, -, h⟩
      exact ⟨_, seqVal_mem_of_inDom ha hdi, (valAt_iff ha.1).mpr rfl,
        _, seqVal_mem_of_inDom ha hdj, (valAt_iff ha.1).mpr rfl, h⟩
    · rintro ⟨x, _, hx, y, _, hy, hxy⟩
      rw [valAt_iff ha.1] at hx hy
      exact ⟨ha, hcov, by rw [← hx, ← hy]; exact hxy⟩
  · intro e₁ _ e₂ _ h₁ h₂ a _ hA1 hA2
    obtain ⟨φ, rfl⟩ := (isCodeW_iff e₁).mp h₁
    obtain ⟨ψ, rfl⟩ := (isCodeW_iff e₂).mp h₂
    obtain ⟨ha, hcφ⟩ := isAsn_code_iff.mp hA1
    obtain ⟨-, hcψ⟩ := isAsn_code_iff.mp hA2
    have hcimp : ∀ k ∈ Fm.fv (Fm.imp φ ψ), InDomZ a (natZ k) := by
      intro k hk
      simp only [Fm.fv, Finset.mem_union] at hk
      rcases hk with hk | hk
      · exact hcφ k hk
      · exact hcψ k hk
    rw [show ZFSet.pair (natZ 3) (ZFSet.pair (Fm.code.{u} φ) (Fm.code.{u} ψ)) =
      Fm.code.{u} (Fm.imp φ ψ) from rfl, pair_code_mem_TruthSet, pair_code_mem_TruthSet,
      pair_code_mem_TruthSet]
    simp only [SatIn, sat_imp]
    constructor
    · rintro ⟨-, -, H⟩ ⟨-, -, hφ⟩
      exact ⟨ha, hcψ, H hφ⟩
    · intro H
      exact ⟨ha, hcimp, fun hφ => (H ⟨ha, hcφ, hφ⟩).2.2⟩
  · intro i hi e _ he a _ ha hg
    obtain ⟨i₀, rfl⟩ := mem_ωZ_iff.mp hi
    obtain ⟨φ, rfl⟩ := (isCodeW_iff e).mp he
    have hcov := allGuard_code_iff.mp hg
    have hall : ∀ x ∈ A, ∀ b, IsUpdSeq a (natZ i₀) x b → b ∈ U ∧ IsSeqA ωZ A b ∧
        ((∀ k ∈ Fm.fv φ, InDomZ b (natZ k)) ∧
          (SatIn A (SeqVal b) φ ↔ SatIn A (Function.update (SeqVal a) i₀ x) φ)) := by
      intro x hx b hb
      obtain ⟨b', hb', hbseq, hbdom, hbval⟩ := exists_updSeq ha i₀ hx
      have hbcov : ∀ k ∈ Fm.fv φ, InDomZ b' (natZ k) := by
        intro k hk
        by_cases hki : k = i₀
        · exact hbdom k (Or.inr hki)
        · exact hbdom k (Or.inl (hcov k (Finset.mem_erase.mpr ⟨hki, hk⟩)))
      have hagree : ∀ k ∈ Fm.fv φ, SeqVal b' k = Function.update (SeqVal a) i₀ x k := by
        intro k hk
        by_cases hki : k = i₀
        · exact hbval k (Or.inr hki)
        · exact hbval k (Or.inl (hcov k (Finset.mem_erase.mpr ⟨hki, hk⟩)))
      rw [isUpdSeq_unique hb hb']
      exact ⟨hseqU b' hbseq, hbseq, hbcov, sat_congr hagree⟩
    rw [show ZFSet.pair (natZ 4) (ZFSet.pair (natZ i₀) (Fm.code.{u} φ)) =
      Fm.code.{u} (Fm.all i₀ φ) from rfl, pair_code_mem_TruthSet]
    simp only [SatIn, sat_all]
    constructor
    · rintro ⟨-, -, H⟩ x hx b _ hb
      obtain ⟨-, hbseq, hbcov, hiff⟩ := hall x hx b hb
      exact pair_code_mem_TruthSet.mpr ⟨hbseq, hbcov, hiff.mpr (H x hx)⟩
    · intro H
      refine ⟨ha, by simpa only [Fm.fv] using hcov, fun x hx => ?_⟩
      obtain ⟨b', hb', -, -, -⟩ := exists_updSeq ha i₀ hx
      obtain ⟨hbU, -, -, hiff⟩ := hall x hx b' hb'
      exact hiff.mp (pair_code_mem_TruthSet.mp (H x hx b' hbU hb')).2.2

/-- Lemma 8.4, existence in the universe. -/
theorem satCode_exists (A : ZFSet.{u}) :
    ∃ U T, SatCode (L Ordinal.omega0) ωZ A U T := by
  set T := TruthSet A with hT
  set γ : Ordinal.{u} := max (ZFSet.rank A) (max (ZFSet.rank T)
    (max (ZFSet.rank ωZ) (ZFSet.rank (L Ordinal.omega0)))) + Ordinal.omega0 with hγ
  have hγlim : Order.IsSuccLimit γ := Ordinal.isSuccLimit_add _ Ordinal.isSuccLimit_omega0
  have hbase : max (ZFSet.rank A) (max (ZFSet.rank T)
      (max (ZFSet.rank ωZ) (ZFSet.rank (L Ordinal.omega0)))) < γ :=
    lt_add_of_pos_right _ Ordinal.omega0_pos
  set U := ZFSet.vonNeumann γ with hU
  have hmemU : ∀ x : ZFSet.{u}, x ∈ U ↔ ZFSet.rank x < γ := fun x => ZFSet.mem_vonNeumann
  have hUtrans : U.IsTransitive := ZFSet.isTransitive_vonNeumann γ
  have hAU : A ∈ U := (hmemU A).mpr (lt_of_le_of_lt (le_max_left _ _) hbase)
  have hTU : T ∈ U := (hmemU T).mpr
    (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hbase)
  have hωU : ωZ ∈ U := (hmemU ωZ).mpr
    (lt_of_le_of_lt (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) hbase)
  have hpucl : ∀ x ∈ U, ∀ y ∈ U, ({x, y} : ZFSet.{u}) ∈ U ∧ ZFSet.sUnion x ∈ U := by
    intro x hx y hy
    rw [hmemU] at hx hy
    constructor
    · rw [hmemU, ZFSet.rank_pair]
      exact max_lt (hγlim.succ_lt hx) (hγlim.succ_lt hy)
    · rw [hmemU]
      exact lt_of_le_of_lt (ZFSet.rank_sUnion_le x) hx
  exact ⟨U, T, satCode_truthSet_of hUtrans hAU hTU hωU hpucl⟩

end BM4.ST
