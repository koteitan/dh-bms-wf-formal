/-
  Part III, §9: the internal (Δ0) description of the constructible hierarchy.
  Definition 9.1 (`LCode`) and Lemma 9.2 (soundness of a code).
-/
import Bm4.SetTheory.SatCode

universe u

namespace BM4.ST

open Fm

/-! ### `L 1` and `∅ ∈ L ξ` -/

theorem L_one : L (1 : Ordinal.{u}) = ({∅} : ZFSet.{u}) := by
  have h : (1 : Ordinal.{u}) = 0 + 1 := by simp
  rw [h, L_succ, L_zero]
  ext X
  rw [mem_Def, ZFSet.mem_singleton]
  constructor
  · rintro ⟨hX, -⟩
    exact (ZFSet.eq_empty X).mpr fun x hx => ZFSet.notMem_empty x (hX hx)
  · rintro rfl
    refine ⟨subset_rfl, Fm.falsum, 0, fun _ => ∅, fun j hj => by simp [fv] at hj, ?_⟩
    intro x
    simp [SatIn]

theorem natZ_zero : natZ.{u} 0 = (∅ : ZFSet.{u}) := rfl

theorem natZ_one : natZ.{u} 1 = ({∅} : ZFSet.{u}) := rfl

theorem empty_mem_L {ξ : Ordinal.{u}} (h : 0 < ξ) : (∅ : ZFSet.{u}) ∈ L ξ := by
  have h1 : (1 : Ordinal.{u}) ≤ ξ := by
    rw [show (1 : Ordinal.{u}) = 0 + 1 by simp, ← Order.succ_eq_add_one]
    exact Order.succ_le_of_lt h
  refine L_mono h1 ?_
  rw [L_one]
  exact ZFSet.mem_singleton.mpr rfl

/-! ### Finite sequences from a valuation -/

/-- The finite sequence with domain `natZ N` and value `v k` at `k < N`. -/
noncomputable def seqOfVal (N : ℕ) (v : ℕ → ZFSet.{u}) : ZFSet.{u} :=
  ofList ((List.range N).map fun k => ZFSet.pair (natZ k) (v k))

theorem mem_seqOfVal {N : ℕ} {v : ℕ → ZFSet.{u}} {p : ZFSet.{u}} :
    p ∈ seqOfVal N v ↔ ∃ k < N, p = ZFSet.pair (natZ k) (v k) := by
  simp only [seqOfVal, mem_ofList, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩

theorem isSeqA_seqOfVal {A : ZFSet.{u}} {N : ℕ} {v : ℕ → ZFSet.{u}}
    (hv : ∀ k, k < N → v k ∈ A) : IsSeqA ωZ A (seqOfVal N v) := by
  refine ⟨⟨?_, ?_⟩, ⟨natZ N, natZ_mem_ωZ N, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨k, _, rfl⟩ := mem_seqOfVal.mp hp
    exact ⟨_, _, rfl⟩
  · intro x b b' hb hb'
    obtain ⟨k, _, e⟩ := mem_seqOfVal.mp hb
    obtain ⟨k', _, e'⟩ := mem_seqOfVal.mp hb'
    rw [ZFSet.pair_inj] at e e'
    have : k = k' := natZ_injective (e.1 ▸ e'.1 ▸ rfl)
    rw [e.2, e'.2, this]
  · intro x
    rw [mem_natZ_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨v k, mem_seqOfVal.mpr ⟨k, hk, rfl⟩⟩
    · rintro ⟨b, hb⟩
      obtain ⟨k, hk, e⟩ := mem_seqOfVal.mp hb
      rw [ZFSet.pair_inj] at e
      exact ⟨k, hk, e.1⟩
  · intro i x hx
    obtain ⟨k, hk, e⟩ := mem_seqOfVal.mp hx
    rw [ZFSet.pair_inj] at e
    rw [e.2]
    exact hv k hk

theorem seqVal_seqOfVal {A : ZFSet.{u}} {N : ℕ} {v : ℕ → ZFSet.{u}}
    (hv : ∀ k, k < N → v k ∈ A) {k : ℕ} (hk : k < N) : SeqVal (seqOfVal N v) k = v k :=
  seqVal_spec (isSeqA_seqOfVal hv).1 (mem_seqOfVal.mpr ⟨k, hk, rfl⟩)

/-- Any valuation with values in `A` on a finite set of indices is realised by a finite
sequence over `A` whose domain covers that set. -/
theorem exists_seq_of_val {A : ZFSet.{u}} (s : Finset ℕ) (v : ℕ → ZFSet.{u})
    (hv : ∀ j ∈ s, v j ∈ A) :
    ∃ a, IsSeqA ωZ A a ∧ (∀ k ∈ s, InDomZ a (natZ k)) ∧ ∀ k ∈ s, SeqVal a k = v k := by
  classical
  rcases Finset.eq_empty_or_nonempty s with rfl | ⟨j₀, hj₀⟩
  · refine ⟨seqOfVal 0 v, isSeqA_seqOfVal (A := A) (fun k hk => absurd hk (Nat.not_lt_zero k)),
      ?_, ?_⟩ <;> intro k hk <;> exact absurd hk (Finset.notMem_empty k)
  · set N := s.sup id + 1 with hN
    set v' : ℕ → ZFSet.{u} := fun k => if k ∈ s then v k else v j₀ with hv'
    have hlt : ∀ k ∈ s, k < N := fun k hk => Nat.lt_succ_of_le (Finset.le_sup (f := id) hk)
    have hmem : ∀ k, k < N → v' k ∈ A := by
      intro k _
      by_cases hks : k ∈ s
      · simp only [hv', if_pos hks]; exact hv k hks
      · simp only [hv', if_neg hks]; exact hv j₀ hj₀
    refine ⟨seqOfVal N v', isSeqA_seqOfVal hmem,
      fun k hk => ⟨v' k, mem_seqOfVal.mpr ⟨k, hlt k hk, rfl⟩⟩, fun k hk => ?_⟩
    · rw [seqVal_seqOfVal hmem (hlt k hk)]
      simp only [hv', if_pos hk]

/-! ### §8.1 `Cons(x, a, b)`: the concatenation assignment -/

/-- §8.1 `Cons(x, a, b)`: `b` is the sequence `a` with the value `x` prefixed, so that
`b(0) = x` and `b(j + 1) = a(j)`. -/
def IsConsSeq (x a b : ZFSet.{u}) : Prop :=
  ∀ p, p ∈ b ↔ p = ZFSet.pair (natZ 0) x ∨
    ∃ j y, ZFSet.pair j y ∈ a ∧ p = ZFSet.pair (insert j j) y

theorem isConsSeq_unique {x a b b' : ZFSet.{u}} (h : IsConsSeq x a b) (h' : IsConsSeq x a b') :
    b = b' := by
  ext p; rw [h p, h' p]

theorem natZ_succ (n : ℕ) : natZ.{u} (n + 1) = insert (natZ n) (natZ n) := rfl

/-- Existence of the concatenation assignment, with its values. -/
theorem exists_consSeq {A a : ZFSet.{u}} (ha : IsSeqA ωZ A a) {x : ZFSet.{u}} (hx : x ∈ A) :
    ∃ b, IsConsSeq x a b ∧ IsSeqA ωZ A b ∧ InDomZ b (natZ 0) ∧ SeqVal b 0 = x ∧
      ∀ m : ℕ, InDomZ a (natZ m) →
        InDomZ b (natZ (m + 1)) ∧ SeqVal b (m + 1) = SeqVal a m := by
  classical
  obtain ⟨n, hdom⟩ := isSeqA_dom ha
  set v : ℕ → ZFSet.{u} := fun k => if k = 0 then x else SeqVal a (k - 1) with hv
  have hdomlt : ∀ m : ℕ, InDomZ a (natZ m) ↔ m < n := by
    intro m
    constructor
    · intro hm
      obtain ⟨k, hk, e⟩ := mem_natZ_iff.mp ((hdom (natZ m)).mpr hm)
      exact (natZ_injective e) ▸ hk
    · intro hm
      exact (hdom (natZ m)).mp (mem_natZ_iff.mpr ⟨m, hm, rfl⟩)
  have hvA : ∀ k, k < n + 1 → v k ∈ A := by
    intro k hk
    by_cases hk0 : k = 0
    · simp only [hv, if_pos hk0]; exact hx
    · simp only [hv, if_neg hk0]
      exact seqVal_mem_of_inDom ha ((hdomlt (k - 1)).mpr (by omega))
  refine ⟨seqOfVal (n + 1) v, ?_, isSeqA_seqOfVal hvA, ?_, ?_, ?_⟩
  · intro p
    rw [mem_seqOfVal]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · left; simp only [hv, if_pos rfl]
      · right
        obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
        refine ⟨natZ m, SeqVal a m, ?_, ?_⟩
        · obtain ⟨y, hy⟩ := (hdomlt m).mpr (by omega)
          rwa [seqVal_spec ha.1 hy]
        · simp only [hv, if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel, natZ_succ]
    · rintro (rfl | ⟨j, y, hjy, rfl⟩)
      · exact ⟨0, by omega, by simp only [hv, if_pos rfl]⟩
      · obtain ⟨m, rfl⟩ := mem_ωZ_iff.mp (isSeqA_index ωZ_transitive ha hjy)
        have hm : m < n := (hdomlt m).mp ⟨y, hjy⟩
        refine ⟨m + 1, by omega, ?_⟩
        rw [natZ_succ]
        simp only [hv, if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel]
        rw [seqVal_spec ha.1 hjy]
  · exact ⟨v 0, mem_seqOfVal.mpr ⟨0, by omega, rfl⟩⟩
  · rw [seqVal_seqOfVal hvA (by omega : 0 < n + 1)]
    simp only [hv, if_pos rfl]
  · intro m hm
    have hmn : m < n := (hdomlt m).mp hm
    refine ⟨⟨v (m + 1), mem_seqOfVal.mpr ⟨m + 1, by omega, rfl⟩⟩, ?_⟩
    rw [seqVal_seqOfVal hvA (by omega : m + 1 < n + 1)]
    simp only [hv, if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel]

/-- The concatenation assignment lies in a pair/union-closed transitive `U` (Lemma 8.2). -/
theorem consSeq_mem_of_puCl {U A a b x : ZFSet.{u}} (hU : U.IsTransitive) (hAU : A ∈ U)
    (hω : ωZ ∈ U) (hcl : ∀ x ∈ U, ∀ y ∈ U, ({x, y} : ZFSet.{u}) ∈ U ∧ ZFSet.sUnion x ∈ U)
    (ha : IsSeqA ωZ A a) (hx : x ∈ A) (hb : IsConsSeq x a b) : b ∈ U := by
  obtain ⟨b', hb', hseq', -, -, -⟩ := exists_consSeq ha hx
  rw [isConsSeq_unique hb hb']
  exact seq_mem_of_puCl hU hAU hω hcl hseq'

/-! #### §9.1: `a_x` as a term versus the `U`-bounded quantifier

Formula (9.1) of §9.1 is written with `a_x` as a *term*, with no quantifier around it, and
the paper justifies its ∆₀-ness afterwards by remarking that `a_x` lies in `U` (Lemma 8.2).
The Lean statements of (9.1) instead put the frame `U` into the definition itself, as
`∃ ax ∈ U, Cons(x, a, ax) ∧ ⟨e, ax⟩ ∈ T`.  The lemmas below show that the two readings agree:
`a_x` is unique, it always lies in `U` under condition 1 of Definition 8.3, and therefore the
bounded existential, the unbounded existential and both universal readings are equivalent. -/

/-- §9.1 introduces `a_x` as a *term*.  It is well defined: for `x ∈ A` and an `A`-valued
finite parameter list `a` there is exactly one `b` with `Cons(x, a, b)`. -/
theorem existsUnique_consSeq {A a : ZFSet.{u}} (ha : IsSeqA ωZ A a) {x : ZFSet.{u}}
    (hx : x ∈ A) : ∃! b, IsConsSeq x a b := by
  obtain ⟨b, hb, -, -, -, -⟩ := exists_consSeq ha hx
  exact ⟨b, hb, fun _ hb' => isConsSeq_unique hb' hb⟩

/-- The frame `U` may be dropped from the existential over `a_x`: by Lemma 8.2 the term `a_x`
lies in `U` anyway.  This is the paper's own reading of (9.1). -/
theorem consSeq_bex_iff_ex {U A a x : ZFSet.{u}} {P : ZFSet.{u} → Prop} (hU : U.IsTransitive)
    (hAU : A ∈ U) (hω : ωZ ∈ U)
    (hcl : ∀ y ∈ U, ∀ z ∈ U, ({y, z} : ZFSet.{u}) ∈ U ∧ ZFSet.sUnion y ∈ U)
    (ha : IsSeqA ωZ A a) (hx : x ∈ A) :
    (∃ ax ∈ U, IsConsSeq x a ax ∧ P ax) ↔ ∃ ax, IsConsSeq x a ax ∧ P ax := by
  constructor
  · rintro ⟨ax, -, hax, hP⟩
    exact ⟨ax, hax, hP⟩
  · rintro ⟨ax, hax, hP⟩
    exact ⟨ax, consSeq_mem_of_puCl hU hAU hω hcl ha hx hax, hax, hP⟩

/-- The existential and the universal reading of the term `a_x` agree, since `a_x` exists and
is unique. -/
theorem consSeq_bex_iff_forall {U A a x : ZFSet.{u}} {P : ZFSet.{u} → Prop} (hU : U.IsTransitive)
    (hAU : A ∈ U) (hω : ωZ ∈ U)
    (hcl : ∀ y ∈ U, ∀ z ∈ U, ({y, z} : ZFSet.{u}) ∈ U ∧ ZFSet.sUnion y ∈ U)
    (ha : IsSeqA ωZ A a) (hx : x ∈ A) :
    (∃ ax ∈ U, IsConsSeq x a ax ∧ P ax) ↔ ∀ ax, IsConsSeq x a ax → P ax := by
  constructor
  · rintro ⟨ax, -, hax, hP⟩ ax' hax'
    exact isConsSeq_unique hax' hax ▸ hP
  · intro H
    obtain ⟨ax, hax, -, -, -, -⟩ := exists_consSeq ha hx
    exact ⟨ax, consSeq_mem_of_puCl hU hAU hω hcl ha hx hax, hax, H ax hax⟩

/-- The bounded existential and the bounded universal reading of the term `a_x` agree. -/
theorem consSeq_bex_iff_ball {U A a x : ZFSet.{u}} {P : ZFSet.{u} → Prop} (hU : U.IsTransitive)
    (hAU : A ∈ U) (hω : ωZ ∈ U)
    (hcl : ∀ y ∈ U, ∀ z ∈ U, ({y, z} : ZFSet.{u}) ∈ U ∧ ZFSet.sUnion y ∈ U)
    (ha : IsSeqA ωZ A a) (hx : x ∈ A) :
    (∃ ax ∈ U, IsConsSeq x a ax ∧ P ax) ↔ ∀ ax ∈ U, IsConsSeq x a ax → P ax := by
  constructor
  · intro H ax _ hax
    exact (consSeq_bex_iff_forall hU hAU hω hcl ha hx).mp H ax hax
  · intro H
    obtain ⟨ax, hax, -, -, -, -⟩ := exists_consSeq ha hx
    have haxU := consSeq_mem_of_puCl hU hAU hω hcl ha hx hax
    exact ⟨ax, haxU, hax, H ax haxU hax⟩

/-- The value clause of (9.1) as the Lean definitions state it, `x ∈ b ↔ ∃ ax ∈ U, …`, is
equivalent to the paper's own form `x ∈ b ⟺ ⟨e, a_x⟩ ∈ T` with `a_x` read as a term. -/
theorem defVal_iff_term {U A T e a b : ZFSet.{u}}
    (hsat : SatCode (L Ordinal.omega0) ωZ A U T) (ha : IsSeqA ωZ A a) :
    (∀ x ∈ A, (x ∈ b ↔ ∃ ax ∈ U, IsConsSeq x a ax ∧ ZFSet.pair e ax ∈ T)) ↔
      ∀ x ∈ A, ∀ ax, IsConsSeq x a ax → (x ∈ b ↔ ZFSet.pair e ax ∈ T) := by
  constructor
  · intro H x hx ax hax
    rw [H x hx]
    constructor
    · rintro ⟨ax', -, hax', hT⟩
      exact isConsSeq_unique hax' hax ▸ hT
    · intro hT
      exact ⟨ax, consSeq_mem_of_puCl hsat.trans hsat.A_mem hsat.w_mem hsat.pucl ha hx hax,
        hax, hT⟩
  · intro H x hx
    obtain ⟨ax, hax, -, -, -, -⟩ := exists_consSeq ha hx
    rw [H x hx ax hax]
    constructor
    · intro hT
      exact ⟨ax, consSeq_mem_of_puCl hsat.trans hsat.A_mem hsat.w_mem hsat.pucl ha hx hax,
        hax, hT⟩
    · rintro ⟨ax', -, hax', hT⟩
      exact isConsSeq_unique hax' hax ▸ hT

/-! #### `IsConsSeq` is Δ₀ -/

theorem isConsSeq_iff_bounded (x a b : ZFSet.{u}) :
    IsConsSeq x a b ↔
      ((∀ p ∈ b, (∃ q ∈ p, ∃ z ∈ q, z = natZ 0 ∧ p = ZFSet.pair z x) ∨
          (∃ q ∈ p, ∃ s ∈ q, ∃ j ∈ s, ∃ q' ∈ p, ∃ y ∈ q',
            s = insert j j ∧ p = ZFSet.pair s y ∧ ZFSet.pair j y ∈ a)) ∧
        (∃ p ∈ b, ∃ q ∈ p, ∃ z ∈ q, z = natZ 0 ∧ p = ZFSet.pair z x) ∧
        (∀ p ∈ a, ∀ q ∈ p, ∀ j ∈ q, ∀ q' ∈ p, ∀ y ∈ q', p = ZFSet.pair j y →
          ∃ p' ∈ b, ∃ r ∈ p', ∃ s ∈ r, s = insert j j ∧ p' = ZFSet.pair s y)) := by
  constructor
  · intro H
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      rcases (H p).mp hp with rfl | ⟨j, y, hjy, rfl⟩
      · exact Or.inl ⟨_, singleton_mem_pair _ _, _, ZFSet.mem_singleton.mpr rfl, rfl, rfl⟩
      · exact Or.inr ⟨_, singleton_mem_pair _ _, _, ZFSet.mem_singleton.mpr rfl,
          j, ZFSet.mem_insert_iff.mpr (Or.inl rfl), _, upair_mem_pair _ _,
          y, mem_upair_right _ _, rfl, rfl, hjy⟩
    · exact ⟨_, (H _).mpr (Or.inl rfl), _, singleton_mem_pair _ _, _,
        ZFSet.mem_singleton.mpr rfl, rfl, rfl⟩
    · intro p hp q _ j _ q' _ y _ hpe
      subst hpe
      have : ZFSet.pair (insert j j) y ∈ b := (H _).mpr (Or.inr ⟨j, y, hp, rfl⟩)
      exact ⟨_, this, _, singleton_mem_pair _ _, _, ZFSet.mem_singleton.mpr rfl, rfl, rfl⟩
  · rintro ⟨H1, H2, H3⟩ p
    constructor
    · intro hp
      rcases H1 p hp with ⟨q, -, z, -, rfl, rfl⟩ | ⟨q, -, s, -, j, -, q', -, y, -, rfl, rfl, hjy⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨j, y, hjy, rfl⟩
    · rintro (rfl | ⟨j, y, hjy, rfl⟩)
      · obtain ⟨p, hp, q, -, z, -, rfl, rfl⟩ := H2
        exact hp
      · obtain ⟨p', hp', r, -, s, -, rfl, rfl⟩ := H3 _ hjy _ (singleton_mem_pair j y) j
          (ZFSet.mem_singleton.mpr rfl) _ (upair_mem_pair j y) y (mem_upair_right j y) rfl
        exact hp'

theorem delta0_isConsSeq (x a b : ℕ) (hxa : x ≠ a) (hxb : x ≠ b) (hab : a ≠ b) :
    Delta0Def {x, a, b} (fun _ v => IsConsSeq (v x) (v a) (v b)) := by
  set m := x + a + b + 1 with hm
  -- p := m, q := m+1, z := m+2, s := m+3, j := m+4, q' := m+5, y := m+6, p' := m+7, r := m+8
  have z0 := (delta0_isNatZ 0 (m + 2)).and (delta0_isKPair m (m + 2) x (by omega) (by omega))
  have z1 := z0.bex (m + 2) (m + 1) (by omega)
  have z2 := z1.bex (m + 1) m (by omega)
  have s0 := ((delta0_isSucc (m + 3) (m + 4) (by omega)).and
    ((delta0_isKPair m (m + 3) (m + 6) (by omega) (by omega)).and
      (delta0_funVal a (m + 4) (m + 6) (by omega) (by omega) (by omega))))
  have s1 := s0.bex (m + 6) (m + 5) (by omega)
  have s2 := s1.bex (m + 5) m (by omega)
  have s3 := s2.bex (m + 4) (m + 3) (by omega)
  have s4 := s3.bex (m + 3) (m + 1) (by omega)
  have s5 := s4.bex (m + 1) m (by omega)
  have c1 := (z2.or s5).ball m b (by omega)
  have c2 := z2.bex m b (by omega)
  have t0 := (delta0_isSucc (m + 3) (m + 4) (by omega)).and
    (delta0_isKPair (m + 7) (m + 3) (m + 6) (by omega) (by omega))
  have t1 := t0.bex (m + 3) (m + 8) (by omega)
  have t2 := t1.bex (m + 8) (m + 7) (by omega)
  have t3 := t2.bex (m + 7) b (by omega)
  have t4 := ((delta0_isKPair m (m + 4) (m + 6) (by omega) (by omega)).imp t3)
  have t5 := t4.ball (m + 6) (m + 5) (by omega)
  have t6 := t5.ball (m + 5) m (by omega)
  have t7 := t6.ball (m + 4) (m + 1) (by omega)
  have t8 := t7.ball (m + 1) m (by omega)
  have c3 := t8.ball m a (by omega)
  refine ((c1.and (c2.and c3)).congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    exact (isConsSeq_iff_bounded (v x) (v a) (v b)).symm
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase] at hk ⊢
    omega
/-! ### §9.1: the input of a definable subset -/

/-- §9.1 `DefInp_X(e, a)`: `e` is a formula code whose free variables are the designated
variable `v0` and parameter variables, and `a` is a finite `X`-valued parameter list with
`a(j)` the value of the `j`-th parameter variable `v_{j+1}` — so whenever `v_{j+1}` is free in
`e`, the index `j` lies in the domain of `a`. -/
def DefInp (h w X e a : ZFSet.{u}) : Prop :=
  IsCodeW h w e ∧ IsSeqA w X a ∧
    ∀ j ∈ w, ∀ k ∈ w, k = insert j j → ¬ NotFreeW h w k e → InDomZ a j

set_option linter.unusedVariables false in
theorem delta0_defInp (h w X e a : ℕ) (hhw : h ≠ w) (hhX : h ≠ X) (hhe : h ≠ e) (hha : h ≠ a)
    (hwX : w ≠ X) (hwe : w ≠ e) (hwa : w ≠ a) (hXe : X ≠ e) (hXa : X ≠ a) (hea : e ≠ a) :
    Delta0Def {h, w, X, e, a} (fun _ v => DefInp (v h) (v w) (v X) (v e) (v a)) := by
  set m := h + w + X + e + a + 1 with hm
  -- j := m, k := m+1
  have g0 := (delta0_isSucc (m + 1) m (by omega)).imp
    ((delta0_notFreeW h w (m + 1) e hhw (by omega) hhe (by omega) hwe (by omega)).not.imp
      (delta0_inDomZ a m (by omega)))
  have g1 := g0.ball (m + 1) w (by omega)
  have g2 := g1.ball m w (by omega)
  have hall := (delta0_isCodeW h w e hhw hhe hwe).and
    ((delta0_isSeqA w X a hwX hwa hXa).and g2)
  refine (hall.congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    exact Iff.rfl
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase] at hk ⊢
    omega

/-- `DefInp` on the code of `φ`: the domain of `a` covers every `j` with `v_{j+1}` free
in `φ`. -/
theorem defInp_code_iff {X a : ZFSet.{u}} {φ : Fm} :
    DefInp (L Ordinal.omega0) ωZ X φ.code a ↔
      IsSeqA ωZ X a ∧ ∀ j : ℕ, (j + 1) ∈ Fm.fv φ → InDomZ a (natZ j) := by
  refine ⟨fun ⟨_, ha, hg⟩ => ⟨ha, fun j hj => ?_⟩,
    fun ⟨ha, hg⟩ => ⟨(isCodeW_iff _).mpr ⟨φ, rfl⟩, ha, fun j hj k hk hke hnf => ?_⟩⟩
  · refine hg (natZ j) (natZ_mem_ωZ j) (natZ (j + 1)) (natZ_mem_ωZ (j + 1)) (natZ_succ j) ?_
    rw [notFreeW_code_iff]
    exact fun hc => hc hj
  · obtain ⟨n, rfl⟩ := mem_ωZ_iff.mp hj
    subst hke
    rw [← natZ_succ n, notFreeW_code_iff] at hnf
    exact hg n (not_not.mp hnf)

/-! ### Definition 9.1, condition 4: the enumeration of the definable subsets -/

/-- Definition 9.1, condition 4: `Dx` is a function whose domain is *exactly*
`{⟨e, a⟩ : e ∈ h, a ∈ U, DefInp_{Hx}(e, a)}`, and whose value `b = Dx(e, a)` is a subset of
`Hx` with `x ∈ b ↔ ⟨e, a_x⟩ ∈ Sx` for every `x ∈ Hx` (9.1). -/
def IsDefEnum (h w U Hx Sx Dx : ZFSet.{u}) : Prop :=
  IsFunc Dx ∧
    (∀ k, (∃ b, ZFSet.pair k b ∈ Dx) ↔
      ∃ e ∈ h, ∃ a ∈ U, k = ZFSet.pair e a ∧ DefInp h w Hx e a) ∧
    ∀ e a b, ZFSet.pair (ZFSet.pair e a) b ∈ Dx →
      b ⊆ Hx ∧ ∀ x ∈ Hx, (x ∈ b ↔ ∃ ax ∈ U, IsConsSeq x a ax ∧ ZFSet.pair e ax ∈ Sx)

theorem isDefEnum_iff_bounded (h w U Hx Sx Dx : ZFSet.{u}) :
    IsDefEnum h w U Hx Sx Dx ↔
      (IsFunc Dx ∧
        (∀ p ∈ Dx, ∀ q ∈ p, ∀ k ∈ q, ∀ q' ∈ p, ∀ b ∈ q', p = ZFSet.pair k b →
          ∃ r ∈ k, ∃ e ∈ r, ∃ r' ∈ k, ∃ a ∈ r', k = ZFSet.pair e a ∧ e ∈ h ∧ a ∈ U ∧
            DefInp h w Hx e a ∧ b ⊆ Hx ∧
            ∀ x ∈ Hx, (x ∈ b ↔ ∃ ax ∈ U, IsConsSeq x a ax ∧ ZFSet.pair e ax ∈ Sx)) ∧
        (∀ e ∈ h, ∀ a ∈ U, DefInp h w Hx e a →
          ∃ p ∈ Dx, ∃ q ∈ p, ∃ k ∈ q, ∃ q' ∈ p, ∃ b ∈ q',
            k = ZFSet.pair e a ∧ p = ZFSet.pair k b)) := by
  constructor
  · rintro ⟨hf, hdom, hval⟩
    refine ⟨hf, ?_, ?_⟩
    · intro p hp q _ k _ q' _ b _ hpe
      subst hpe
      obtain ⟨e, he, a, ha, rfl, hinp⟩ := (hdom k).mp ⟨b, hp⟩
      obtain ⟨hsub, hx⟩ := hval e a b hp
      exact ⟨_, singleton_mem_pair e a, e, ZFSet.mem_singleton.mpr rfl, _, upair_mem_pair e a,
        a, mem_upair_right e a, rfl, he, ha, hinp, hsub, hx⟩
    · intro e he a ha hinp
      obtain ⟨b, hb⟩ := (hdom (ZFSet.pair e a)).mpr ⟨e, he, a, ha, rfl, hinp⟩
      exact ⟨_, hb, _, singleton_mem_pair _ _, _, ZFSet.mem_singleton.mpr rfl,
        _, upair_mem_pair _ _, b, mem_upair_right _ _, rfl, rfl⟩
  · rintro ⟨hf, hA, hB⟩
    have key : ∀ k b, ZFSet.pair k b ∈ Dx →
        ∃ e a, k = ZFSet.pair e a ∧ e ∈ h ∧ a ∈ U ∧ DefInp h w Hx e a ∧ b ⊆ Hx ∧
          ∀ x ∈ Hx, (x ∈ b ↔ ∃ ax ∈ U, IsConsSeq x a ax ∧ ZFSet.pair e ax ∈ Sx) := by
      intro k b hkb
      obtain ⟨r, -, e, -, r', -, a, -, hk, he, ha, hinp, hsub, hx⟩ :=
        hA _ hkb _ (singleton_mem_pair k b) k (ZFSet.mem_singleton.mpr rfl) _
          (upair_mem_pair k b) b (mem_upair_right k b) rfl
      exact ⟨e, a, hk, he, ha, hinp, hsub, hx⟩
    refine ⟨hf, fun k => ⟨?_, ?_⟩, ?_⟩
    · rintro ⟨b, hb⟩
      obtain ⟨e, a, rfl, he, ha, hinp, -, -⟩ := key k b hb
      exact ⟨e, he, a, ha, rfl, hinp⟩
    · rintro ⟨e, he, a, ha, rfl, hinp⟩
      obtain ⟨p, hp, q, -, k, -, q', -, b, -, rfl, rfl⟩ := hB e he a ha hinp
      exact ⟨b, hp⟩
    · intro e a b hb
      obtain ⟨e', a', hk, -, -, -, hsub, hx⟩ := key _ b hb
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective hk
      exact ⟨hsub, hx⟩

/-- Definition 9.1, condition 4, in the paper's own form (9.1): for every entry
`⟨⟨e, a⟩, b⟩` of `Dx` and every `x ∈ Hx`, `x ∈ b ⟺ ⟨e, a_x⟩ ∈ Sx`, with `a_x` the term of
§9.1 rather than a `U`-bounded existential. -/
theorem IsDefEnum.val_term {U A T Dx e a b : ZFSet.{u}}
    (hsat : SatCode (L Ordinal.omega0) ωZ A U T)
    (hD : IsDefEnum (L Ordinal.omega0) ωZ U A T Dx)
    (hb : ZFSet.pair (ZFSet.pair e a) b ∈ Dx) :
    b ⊆ A ∧ ∀ x ∈ A, ∀ ax, IsConsSeq x a ax → (x ∈ b ↔ ZFSet.pair e ax ∈ T) := by
  obtain ⟨e', -, a', -, hk, hinp⟩ := (hD.2.1 (ZFSet.pair e a)).mp ⟨b, hb⟩
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective hk
  obtain ⟨hbA, hval⟩ := hD.2.2 e a b hb
  exact ⟨hbA, (defVal_iff_term hsat hinp.2.1).mp hval⟩

set_option linter.unusedVariables false in
theorem delta0_isDefEnum (h w U Hx Sx Dx : ℕ) (hhw : h ≠ w) (hhU : h ≠ U) (hhH : h ≠ Hx)
    (hhS : h ≠ Sx) (hhD : h ≠ Dx) (hwU : w ≠ U) (hwH : w ≠ Hx) (hwS : w ≠ Sx) (hwD : w ≠ Dx)
    (hUH : U ≠ Hx) (hUS : U ≠ Sx) (hUD : U ≠ Dx) (hHS : Hx ≠ Sx) (hHD : Hx ≠ Dx)
    (hSD : Sx ≠ Dx) :
    Delta0Def {h, w, U, Hx, Sx, Dx}
      (fun _ v => IsDefEnum (v h) (v w) (v U) (v Hx) (v Sx) (v Dx)) := by
  set m := h + w + U + Hx + Sx + Dx + 1 with hm
  -- p := m, q := m+1, k := m+2, q' := m+3, b := m+4, r := m+5, e := m+6, r' := m+7,
  -- a := m+8, x := m+9, ax := m+10
  have val0 := (delta0_isConsSeq (m + 9) (m + 8) (m + 10) (by omega) (by omega) (by omega)).and
    (delta0_funVal Sx (m + 6) (m + 10) (by omega) (by omega) (by omega))
  have val1 := val0.bex (m + 10) U (by omega)
  have val2 := ((Delta0Def.mem (m + 9) (m + 4)).iff val1).ball (m + 9) Hx (by omega)
  have a0 := (delta0_isKPair (m + 2) (m + 6) (m + 8) (by omega) (by omega)).and
    ((Delta0Def.mem (m + 6) h).and ((Delta0Def.mem (m + 8) U).and
      ((delta0_defInp h w Hx (m + 6) (m + 8) hhw hhH (by omega) (by omega) hwH (by omega)
          (by omega) (by omega) (by omega) (by omega)).and
        ((delta0_subset (m + 4) Hx (by omega)).and val2))))
  have a1 := a0.bex (m + 8) (m + 7) (by omega)
  have a2 := a1.bex (m + 7) (m + 2) (by omega)
  have a3 := a2.bex (m + 6) (m + 5) (by omega)
  have a4 := a3.bex (m + 5) (m + 2) (by omega)
  have a5 := (delta0_isKPair m (m + 2) (m + 4) (by omega) (by omega)).imp a4
  have a6 := a5.ball (m + 4) (m + 3) (by omega)
  have a7 := a6.ball (m + 3) m (by omega)
  have a8 := a7.ball (m + 2) (m + 1) (by omega)
  have a9 := a8.ball (m + 1) m (by omega)
  have cA := a9.ball m Dx (by omega)
  have b0 := (delta0_isKPair (m + 2) (m + 6) (m + 8) (by omega) (by omega)).and
    (delta0_isKPair m (m + 2) (m + 4) (by omega) (by omega))
  have b1 := b0.bex (m + 4) (m + 3) (by omega)
  have b2 := b1.bex (m + 3) m (by omega)
  have b3 := b2.bex (m + 2) (m + 1) (by omega)
  have b4 := b3.bex (m + 1) m (by omega)
  have b5 := b4.bex m Dx (by omega)
  have b6 := (delta0_defInp h w Hx (m + 6) (m + 8) hhw hhH (by omega) (by omega) hwH (by omega)
      (by omega) (by omega) (by omega) (by omega)).imp b5
  have b7 := b6.ball (m + 8) U (by omega)
  have cB := b7.ball (m + 6) h (by omega)
  refine (((delta0_isFunc Dx).and (cA.and cB)).congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    exact (isDefEnum_iff_bounded (v h) (v w) (v U) (v Hx) (v Sx) (v Dx)).symm
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase] at hk ⊢
    omega

/-! ### The domain clause -/

theorem isDom_insert_iff_bounded (c η : ZFSet.{u}) :
    IsDom c (insert η η) ↔
      ((∀ a ∈ η, ∃ p ∈ c, ∃ q ∈ p, ∃ b ∈ q, p = ZFSet.pair a b) ∧
        (∃ p ∈ c, ∃ q ∈ p, ∃ b ∈ q, p = ZFSet.pair η b) ∧
        (∀ p ∈ c, ∀ q ∈ p, ∀ a ∈ q, ∀ q' ∈ p, ∀ b ∈ q', p = ZFSet.pair a b →
          (a ∈ η ∨ a = η))) := by
  unfold IsDom
  constructor
  · intro H
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨b, hb⟩ := (H a).mp (ZFSet.mem_insert_iff.mpr (Or.inr ha))
      exact ⟨_, hb, _, upair_mem_pair a b, b, mem_upair_right a b, rfl⟩
    · obtain ⟨b, hb⟩ := (H η).mp (ZFSet.mem_insert_iff.mpr (Or.inl rfl))
      exact ⟨_, hb, _, upair_mem_pair η b, b, mem_upair_right η b, rfl⟩
    · intro p hp q _ a _ q' _ b _ hab
      subst hab
      rcases ZFSet.mem_insert_iff.mp ((H a).mpr ⟨b, hp⟩) with h | h
      · exact Or.inr h
      · exact Or.inl h
  · rintro ⟨H1, H2, H3⟩ a
    rw [ZFSet.mem_insert_iff]
    constructor
    · rintro (rfl | ha)
      · obtain ⟨p, hp, q, -, b, -, rfl⟩ := H2
        exact ⟨b, hp⟩
      · obtain ⟨p, hp, q, -, b, -, rfl⟩ := H1 a ha
        exact ⟨b, hp⟩
    · rintro ⟨b, hb⟩
      have := H3 _ hb _ (singleton_mem_pair a b) a (ZFSet.mem_singleton.mpr rfl) _
        (upair_mem_pair a b) b (mem_upair_right a b) rfl
      tauto

theorem delta0_isDomInsert (c η : ℕ) :
    Delta0Def {c, η} (fun _ v => IsDom (v c) (insert (v η) (v η))) := by
  set n := c + η + 1 with hn
  have d0 := delta0_isKPair (n + 1) n (n + 3) (by omega) (by omega)
  have d1 := d0.bex (n + 3) (n + 2) (by omega)
  have d2 := d1.bex (n + 2) (n + 1) (by omega)
  have d3 := d2.bex (n + 1) c (by omega)
  have d4 := d3.ball n η (by omega)
  have e0 := delta0_isKPair (n + 1) η (n + 3) (by omega) (by omega)
  have e1 := e0.bex (n + 3) (n + 2) (by omega)
  have e2 := e1.bex (n + 2) (n + 1) (by omega)
  have e3 := e2.bex (n + 1) c (by omega)
  have f0 := (delta0_isKPair n (n + 2) (n + 4) (by omega) (by omega)).imp
    ((Delta0Def.mem (n + 2) η).or (Delta0Def.eq (n + 2) η))
  have f1 := f0.ball (n + 4) (n + 3) (by omega)
  have f2 := f1.ball (n + 3) n (by omega)
  have f3 := f2.ball (n + 2) (n + 1) (by omega)
  have f4 := f3.ball (n + 1) n (by omega)
  have f5 := f4.ball n c (by omega)
  refine ((d4.and (e3.and f5)).congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    exact (isDom_insert_iff_bounded (v c) (v η)).symm
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase] at hk ⊢
    omega

/-! ### §9.1: the code of a four-tuple -/

/-- §9.1: `FourCode(c, U, H, S, D)` — `c` is a function with `dom(c) = 4` and
`⟨0,U⟩, ⟨1,H⟩, ⟨2,S⟩, ⟨3,D⟩ ∈ c`. -/
def FourCode (c U H S D : ZFSet.{u}) : Prop :=
  IsFunc c ∧ IsDom c (natZ 4) ∧
    ZFSet.pair (natZ 0) U ∈ c ∧ ZFSet.pair (natZ 1) H ∈ c ∧
    ZFSet.pair (natZ 2) S ∈ c ∧ ZFSet.pair (natZ 3) D ∈ c

/-- `U, H, S, D` all lie in `⋃⋃c`, so the four leading quantifiers of Definition 9.1 are
bounded. -/
theorem bexFour_iff (c : ZFSet.{u}) (P : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop) :
    (∃ U H S D, FourCode c U H S D ∧ P U H S D) ↔
      ∃ p₀ ∈ c, ∃ q₀ ∈ p₀, ∃ U ∈ q₀, ∃ p₁ ∈ c, ∃ q₁ ∈ p₁, ∃ H ∈ q₁,
        ∃ p₂ ∈ c, ∃ q₂ ∈ p₂, ∃ S ∈ q₂, ∃ p₃ ∈ c, ∃ q₃ ∈ p₃, ∃ D ∈ q₃,
          FourCode c U H S D ∧ P U H S D := by
  constructor
  · rintro ⟨U, H, S, D, hfc, hP⟩
    exact ⟨_, hfc.2.2.1, _, upair_mem_pair _ _, U, mem_upair_right _ _,
      _, hfc.2.2.2.1, _, upair_mem_pair _ _, H, mem_upair_right _ _,
      _, hfc.2.2.2.2.1, _, upair_mem_pair _ _, S, mem_upair_right _ _,
      _, hfc.2.2.2.2.2, _, upair_mem_pair _ _, D, mem_upair_right _ _, hfc, hP⟩
  · rintro ⟨-, -, -, -, U, -, -, -, -, -, H, -, -, -, -, -, S, -, -, -, -, -, D, -, hfc, hP⟩
    exact ⟨U, H, S, D, hfc, hP⟩

theorem fourCode_iff_bounded (c U H S D : ZFSet.{u}) :
    FourCode c U H S D ↔
      ((IsFunc c ∧
        (∀ p ∈ c, ∀ q ∈ p, ∀ k ∈ q, ∀ q' ∈ p, ∀ z ∈ q', p = ZFSet.pair k z →
          (k = natZ 0 ∨ k = natZ 1 ∨ k = natZ 2 ∨ k = natZ 3))) ∧
        (((∃ p ∈ c, ∃ q ∈ p, ∃ k ∈ q, k = natZ 0 ∧ p = ZFSet.pair k U) ∧
          (∃ p ∈ c, ∃ q ∈ p, ∃ k ∈ q, k = natZ 1 ∧ p = ZFSet.pair k H)) ∧
        ((∃ p ∈ c, ∃ q ∈ p, ∃ k ∈ q, k = natZ 2 ∧ p = ZFSet.pair k S) ∧
          (∃ p ∈ c, ∃ q ∈ p, ∃ k ∈ q, k = natZ 3 ∧ p = ZFSet.pair k D)))) := by
  have hmem : ∀ (n : ℕ) (X : ZFSet.{u}), ZFSet.pair (natZ n) X ∈ c ↔
      ∃ p ∈ c, ∃ q ∈ p, ∃ k ∈ q, k = natZ n ∧ p = ZFSet.pair k X := by
    intro n X
    refine ⟨fun hp => ⟨_, hp, _, singleton_mem_pair _ _, _, ZFSet.mem_singleton.mpr rfl,
      rfl, rfl⟩, ?_⟩
    rintro ⟨p, hp, q, -, k, -, rfl, rfl⟩
    exact hp
  constructor
  · rintro ⟨hf, hd, h0, h1, h2, h3⟩
    refine ⟨⟨hf, ?_⟩, ⟨(hmem 0 U).mp h0, (hmem 1 H).mp h1⟩,
      (hmem 2 S).mp h2, (hmem 3 D).mp h3⟩
    intro p hp q _ k _ q' _ z _ hpe
    subst hpe
    obtain ⟨j, hj, rfl⟩ := mem_natZ_iff.mp ((hd k).mpr ⟨z, hp⟩)
    interval_cases j
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · rintro ⟨⟨hf, hb⟩, ⟨h0, h1⟩, h2, h3⟩
    have g0 := (hmem 0 U).mpr h0
    have g1 := (hmem 1 H).mpr h1
    have g2 := (hmem 2 S).mpr h2
    have g3 := (hmem 3 D).mpr h3
    refine ⟨hf, ?_, g0, g1, g2, g3⟩
    intro a
    constructor
    · intro ha
      obtain ⟨j, hj, rfl⟩ := mem_natZ_iff.mp ha
      interval_cases j
      · exact ⟨U, g0⟩
      · exact ⟨H, g1⟩
      · exact ⟨S, g2⟩
      · exact ⟨D, g3⟩
    · rintro ⟨b, hb'⟩
      rcases hb _ hb' _ (singleton_mem_pair a b) a (ZFSet.mem_singleton.mpr rfl) _
        (upair_mem_pair a b) b (mem_upair_right a b) rfl with rfl | rfl | rfl | rfl
      · exact mem_natZ_iff.mpr ⟨0, by omega, rfl⟩
      · exact mem_natZ_iff.mpr ⟨1, by omega, rfl⟩
      · exact mem_natZ_iff.mpr ⟨2, by omega, rfl⟩
      · exact mem_natZ_iff.mpr ⟨3, by omega, rfl⟩

theorem delta0_fourCode (c U H S D : ℕ) (hcU : c ≠ U) (hcH : c ≠ H) (hcS : c ≠ S) (hcD : c ≠ D) :
    Delta0Def.{u} {c, U, H, S, D} (fun _ v => FourCode (v c) (v U) (v H) (v S) (v D)) := by
  set m := c + U + H + S + D + 1 with hm
  -- p := m, q := m+1, k := m+2, q' := m+3, z := m+4
  have b0 := (delta0_isKPair m (m + 2) (m + 4) (by omega) (by omega)).imp
    ((delta0_isNatZ 0 (m + 2)).or ((delta0_isNatZ 1 (m + 2)).or
      ((delta0_isNatZ 2 (m + 2)).or (delta0_isNatZ 3 (m + 2)))))
  have b1 := b0.ball (m + 4) (m + 3) (by omega)
  have b2 := b1.ball (m + 3) m (by omega)
  have b3 := b2.ball (m + 2) (m + 1) (by omega)
  have b4 := b3.ball (m + 1) m (by omega)
  have b5 := b4.ball m c (by omega)
  have e0 := ((((delta0_isNatZ 0 (m + 2)).and
    (delta0_isKPair m (m + 2) U (by omega) (by omega))).bex (m + 2) (m + 1)
      (by omega)).bex (m + 1) m (by omega)).bex m c (by omega)
  have e1 := ((((delta0_isNatZ 1 (m + 2)).and
    (delta0_isKPair m (m + 2) H (by omega) (by omega))).bex (m + 2) (m + 1)
      (by omega)).bex (m + 1) m (by omega)).bex m c (by omega)
  have e2 := ((((delta0_isNatZ 2 (m + 2)).and
    (delta0_isKPair m (m + 2) S (by omega) (by omega))).bex (m + 2) (m + 1)
      (by omega)).bex (m + 1) m (by omega)).bex m c (by omega)
  have e3 := ((((delta0_isNatZ 3 (m + 2)).and
    (delta0_isKPair m (m + 2) D (by omega) (by omega))).bex (m + 2) (m + 1)
      (by omega)).bex (m + 1) m (by omega)).bex m c (by omega)
  refine ((((delta0_isFunc c).and b5).and ((e0.and e1).and (e2.and e3))).congr ?_).mono ?_
  · intro Dm v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    exact (fourCode_iff_bounded (v c) (v U) (v H) (v S) (v D)).symm
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase] at hk ⊢
    omega
/-! ### Definition 9.1: the clauses at one stage -/

theorem ball_val_iff (H ξ : ZFSet.{u}) (P : ZFSet.{u} → Prop) :
    (∀ Hx, ZFSet.pair ξ Hx ∈ H → P Hx) ↔
      ∀ p ∈ H, ∀ q ∈ p, ∀ Hx ∈ q, p = ZFSet.pair ξ Hx → P Hx := by
  constructor
  · intro h p hp q _ Hx _ hpe; subst hpe; exact h Hx hp
  · intro h Hx hHx
    exact h _ hHx _ (upair_mem_pair ξ Hx) Hx (mem_upair_right ξ Hx) rfl

theorem bex_val_iff (H ξ : ZFSet.{u}) (P : ZFSet.{u} → Prop) :
    (∃ Hx, ZFSet.pair ξ Hx ∈ H ∧ P Hx) ↔
      ∃ p ∈ H, ∃ q ∈ p, ∃ Hx ∈ q, p = ZFSet.pair ξ Hx ∧ P Hx := by
  constructor
  · rintro ⟨Hx, hHx, hP⟩
    exact ⟨_, hHx, _, upair_mem_pair ξ Hx, Hx, mem_upair_right ξ Hx, rfl, hP⟩
  · rintro ⟨p, hp, q, -, Hx, -, rfl, hP⟩
    exact ⟨Hx, hp, hP⟩

/-- Definition 9.1, condition 3 at the stage `ξ`: `SatCode(H(ξ), U, S(ξ))`. -/
def SatClause (h w U H S ξ : ZFSet.{u}) : Prop :=
  ∀ Hx, ZFSet.pair ξ Hx ∈ H → ∀ Sx, ZFSet.pair ξ Sx ∈ S → SatCode h w Hx U Sx

/-- Definition 9.1, condition 4 at the stage `ξ`. -/
def DefClause (h w U H S D ξ : ZFSet.{u}) : Prop :=
  ∀ Hx, ZFSet.pair ξ Hx ∈ H → ∀ Sx, ZFSet.pair ξ Sx ∈ S → ∀ Dx, ZFSet.pair ξ Dx ∈ D →
    IsDefEnum h w U Hx Sx Dx

/-- Definition 9.1, (9.2) at the stage `ξ`: `H(ξ + 1) = ran D(ξ)`. -/
def SuccClause (H D ξ : ZFSet.{u}) : Prop :=
  ∀ Dx, ZFSet.pair ξ Dx ∈ D → ∀ Hx', ZFSet.pair (insert ξ ξ) Hx' ∈ H → IsRan Dx Hx'

/-- Definition 9.1, (9.3) at a non-zero limit `lam`: `H(lam) = ⋃_{ζ < lam} H(ζ)`. -/
def LimClause (H lam : ZFSet.{u}) : Prop :=
  lam ≠ ∅ → (∀ ζ ∈ lam, insert ζ ζ ∈ lam) →
    ∀ Hl, ZFSet.pair lam Hl ∈ H →
      (∀ x ∈ Hl, ∃ ζ ∈ lam, ∃ Hz, ZFSet.pair ζ Hz ∈ H ∧ x ∈ Hz) ∧
      (∀ ζ ∈ lam, ∀ Hz, ZFSet.pair ζ Hz ∈ H → Hz ⊆ Hl)

theorem satClause_iff_bounded (h w U H S ξ : ZFSet.{u}) :
    SatClause h w U H S ξ ↔
      ∀ p ∈ H, ∀ q ∈ p, ∀ Hx ∈ q, ∀ p' ∈ S, ∀ q' ∈ p', ∀ Sx ∈ q',
        p = ZFSet.pair ξ Hx → p' = ZFSet.pair ξ Sx → SatCode h w Hx U Sx := by
  constructor
  · intro Hd p hp q _ Hx _ p' hp' q' _ Sx _ h1 h2
    subst h1; subst h2; exact Hd Hx hp Sx hp'
  · intro Hd Hx hHx Sx hSx
    exact Hd _ hHx _ (upair_mem_pair ξ Hx) Hx (mem_upair_right ξ Hx) _ hSx
      _ (upair_mem_pair ξ Sx) Sx (mem_upair_right ξ Sx) rfl rfl

theorem defClause_iff_bounded (h w U H S D ξ : ZFSet.{u}) :
    DefClause h w U H S D ξ ↔
      ∀ p ∈ H, ∀ q ∈ p, ∀ Hx ∈ q, ∀ p' ∈ S, ∀ q' ∈ p', ∀ Sx ∈ q',
        ∀ p'' ∈ D, ∀ q'' ∈ p'', ∀ Dx ∈ q'',
        p = ZFSet.pair ξ Hx → p' = ZFSet.pair ξ Sx → p'' = ZFSet.pair ξ Dx →
          IsDefEnum h w U Hx Sx Dx := by
  constructor
  · intro Hd p hp q _ Hx _ p' hp' q' _ Sx _ p'' hp'' q'' _ Dx _ h1 h2 h3
    subst h1; subst h2; subst h3; exact Hd Hx hp Sx hp' Dx hp''
  · intro Hd Hx hHx Sx hSx Dx hDx
    exact Hd _ hHx _ (upair_mem_pair ξ Hx) Hx (mem_upair_right ξ Hx) _ hSx
      _ (upair_mem_pair ξ Sx) Sx (mem_upair_right ξ Sx) _ hDx
      _ (upair_mem_pair ξ Dx) Dx (mem_upair_right ξ Dx) rfl rfl rfl

theorem succClause_iff_bounded (H D ξ : ZFSet.{u}) :
    SuccClause H D ξ ↔
      ∀ p ∈ D, ∀ q ∈ p, ∀ Dx ∈ q, ∀ p' ∈ H, ∀ r ∈ p', ∀ s ∈ r, ∀ q' ∈ p', ∀ Hx' ∈ q',
        p = ZFSet.pair ξ Dx → s = insert ξ ξ → p' = ZFSet.pair s Hx' → IsRan Dx Hx' := by
  constructor
  · intro Hd p hp q _ Dx _ p' hp' r _ s _ q' _ Hx' _ h1 h2 h3
    subst h1; subst h2; subst h3; exact Hd Dx hp Hx' hp'
  · intro Hd Dx hDx Hx' hHx'
    exact Hd _ hDx _ (upair_mem_pair ξ Dx) Dx (mem_upair_right ξ Dx) _ hHx'
      _ (singleton_mem_pair _ _) (insert ξ ξ) (ZFSet.mem_singleton.mpr rfl)
      _ (upair_mem_pair _ _) Hx' (mem_upair_right _ _) rfl rfl rfl

theorem limClause_iff_bounded (H lam : ZFSet.{u}) :
    LimClause H lam ↔
      (¬ (lam = natZ 0) → (∀ ζ ∈ lam, ∃ s ∈ lam, s = insert ζ ζ) →
        ∀ p ∈ H, ∀ q ∈ p, ∀ Hl ∈ q, p = ZFSet.pair lam Hl →
          ((∀ x ∈ Hl, ∃ ζ ∈ lam, ∃ p₂ ∈ H, ∃ q₂ ∈ p₂, ∃ Hz ∈ q₂,
              p₂ = ZFSet.pair ζ Hz ∧ x ∈ Hz) ∧
            (∀ ζ ∈ lam, ∀ p₃ ∈ H, ∀ q₃ ∈ p₃, ∀ Hz ∈ q₃, p₃ = ZFSet.pair ζ Hz →
              Hz ⊆ Hl))) := by
  unfold LimClause
  rw [natZ_zero]
  refine imp_congr Iff.rfl (imp_congr ?_ ?_)
  · constructor
    · intro Hd ζ hζ; exact ⟨_, Hd ζ hζ, rfl⟩
    · rintro Hd ζ hζ
      obtain ⟨s, hs, rfl⟩ := Hd ζ hζ
      exact hs
  · rw [ball_val_iff]
    refine forall_congr' fun p => imp_congr_right fun _ => forall_congr' fun q =>
      imp_congr_right fun _ => forall_congr' fun Hl => imp_congr_right fun _ =>
        imp_congr_right fun _ => and_congr ?_ ?_
    · exact forall_congr' fun x => imp_congr_right fun _ => exists_congr fun ζ =>
        and_congr_right fun _ => bex_val_iff H ζ _
    · exact forall_congr' fun ζ => imp_congr_right fun _ => ball_val_iff H ζ _

set_option linter.unusedVariables false in
theorem delta0_satClause (h w U H S ξ : ℕ) (hhw : h ≠ w) (hhU : h ≠ U) (hhH : h ≠ H)
    (hhS : h ≠ S) (hhξ : h ≠ ξ) (hwU : w ≠ U) (hwH : w ≠ H) (hwS : w ≠ S) (hwξ : w ≠ ξ)
    (hUH : U ≠ H) (hUS : U ≠ S) (hUξ : U ≠ ξ) (hHS : H ≠ S) (hHξ : H ≠ ξ) (hSξ : S ≠ ξ) :
    Delta0Def {h, w, U, H, S, ξ} (fun _ v => SatClause (v h) (v w) (v U) (v H) (v S) (v ξ)) := by
  set m := h + w + U + H + S + ξ + 1 with hm
  -- p := m, q := m+1, Hx := m+2, p' := m+3, q' := m+4, Sx := m+5
  have core := (delta0_isKPair m ξ (m + 2) (by omega) (by omega)).imp
    ((delta0_isKPair (m + 3) ξ (m + 5) (by omega) (by omega)).imp
      (delta0_satCode h w (m + 2) U (m + 5) hhw (by omega) hhU (by omega) (by omega)
        hwU (by omega) (by omega) (by omega) (by omega)))
  have c1 := core.ball (m + 5) (m + 4) (by omega)
  have c2 := c1.ball (m + 4) (m + 3) (by omega)
  have c3 := c2.ball (m + 3) S (by omega)
  have c4 := c3.ball (m + 2) (m + 1) (by omega)
  have c5 := c4.ball (m + 1) m (by omega)
  have c6 := c5.ball m H (by omega)
  refine (c6.congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    exact (satClause_iff_bounded (v h) (v w) (v U) (v H) (v S) (v ξ)).symm
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase] at hk ⊢
    omega

set_option linter.unusedVariables false in
theorem delta0_defClause (h w U H S D ξ : ℕ) (hhw : h ≠ w) (hhU : h ≠ U) (hhH : h ≠ H)
    (hhS : h ≠ S) (hhD : h ≠ D) (hhξ : h ≠ ξ) (hwU : w ≠ U) (hwH : w ≠ H) (hwS : w ≠ S)
    (hwD : w ≠ D) (hwξ : w ≠ ξ) (hUH : U ≠ H) (hUS : U ≠ S) (hUD : U ≠ D) (hUξ : U ≠ ξ)
    (hHS : H ≠ S) (hHD : H ≠ D) (hHξ : H ≠ ξ) (hSD : S ≠ D) (hSξ : S ≠ ξ) (hDξ : D ≠ ξ) :
    Delta0Def {h, w, U, H, S, D, ξ}
      (fun _ v => DefClause (v h) (v w) (v U) (v H) (v S) (v D) (v ξ)) := by
  set m := h + w + U + H + S + D + ξ + 1 with hm
  -- p := m, q := m+1, Hx := m+2, p' := m+3, q' := m+4, Sx := m+5,
  -- p'' := m+6, q'' := m+7, Dx := m+8
  have core := (delta0_isKPair m ξ (m + 2) (by omega) (by omega)).imp
    ((delta0_isKPair (m + 3) ξ (m + 5) (by omega) (by omega)).imp
      ((delta0_isKPair (m + 6) ξ (m + 8) (by omega) (by omega)).imp
        (delta0_isDefEnum h w U (m + 2) (m + 5) (m + 8) hhw hhU (by omega) (by omega)
          (by omega) hwU (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega))))
  have c1 := core.ball (m + 8) (m + 7) (by omega)
  have c2 := c1.ball (m + 7) (m + 6) (by omega)
  have c3 := c2.ball (m + 6) D (by omega)
  have c4 := c3.ball (m + 5) (m + 4) (by omega)
  have c5 := c4.ball (m + 4) (m + 3) (by omega)
  have c6 := c5.ball (m + 3) S (by omega)
  have c7 := c6.ball (m + 2) (m + 1) (by omega)
  have c8 := c7.ball (m + 1) m (by omega)
  have c9 := c8.ball m H (by omega)
  refine (c9.congr ?_).mono ?_
  · intro Dd v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    exact (defClause_iff_bounded (v h) (v w) (v U) (v H) (v S) (v D) (v ξ)).symm
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase] at hk ⊢
    omega

set_option linter.unusedVariables false in
theorem delta0_succClause (H D ξ : ℕ) (hHD : H ≠ D) (hHξ : H ≠ ξ) (hDξ : D ≠ ξ) :
    Delta0Def {H, D, ξ} (fun _ v => SuccClause (v H) (v D) (v ξ)) := by
  set m := H + D + ξ + 1 with hm
  -- p := m, q := m+1, Dx := m+2, p' := m+3, r := m+4, s := m+5, q' := m+6, Hx' := m+7
  have core := (delta0_isKPair m ξ (m + 2) (by omega) (by omega)).imp
    ((delta0_isSucc (m + 5) ξ (by omega)).imp
      ((delta0_isKPair (m + 3) (m + 5) (m + 7) (by omega) (by omega)).imp
        (delta0_isRan (m + 2) (m + 7) (by omega))))
  have c1 := core.ball (m + 7) (m + 6) (by omega)
  have c2 := c1.ball (m + 6) (m + 3) (by omega)
  have c3 := c2.ball (m + 5) (m + 4) (by omega)
  have c4 := c3.ball (m + 4) (m + 3) (by omega)
  have c5 := c4.ball (m + 3) H (by omega)
  have c6 := c5.ball (m + 2) (m + 1) (by omega)
  have c7 := c6.ball (m + 1) m (by omega)
  have c8 := c7.ball m D (by omega)
  refine (c8.congr ?_).mono ?_
  · intro Dd v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    exact (succClause_iff_bounded (v H) (v D) (v ξ)).symm
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase] at hk ⊢
    omega

theorem delta0_limClause (H lam : ℕ) (hHl : H ≠ lam) :
    Delta0Def {H, lam} (fun _ v => LimClause (v H) (v lam)) := by
  set m := H + lam + 1 with hm
  -- p := m, q := m+1, Hl := m+2, x := m+3, ζ := m+4, p₂ := m+5, q₂ := m+6, Hz := m+7, s := m+8
  have a0 := (delta0_isKPair (m + 5) (m + 4) (m + 7) (by omega) (by omega)).and
    (Delta0Def.mem (m + 3) (m + 7))
  have a1 := a0.bex (m + 7) (m + 6) (by omega)
  have a2 := a1.bex (m + 6) (m + 5) (by omega)
  have a3 := a2.bex (m + 5) H (by omega)
  have a4 := a3.bex (m + 4) lam (by omega)
  have a5 := a4.ball (m + 3) (m + 2) (by omega)
  have b0 := (delta0_isKPair (m + 5) (m + 4) (m + 7) (by omega) (by omega)).imp
    (delta0_subset (m + 7) (m + 2) (by omega))
  have b1 := b0.ball (m + 7) (m + 6) (by omega)
  have b2 := b1.ball (m + 6) (m + 5) (by omega)
  have b3 := b2.ball (m + 5) H (by omega)
  have b4 := b3.ball (m + 4) lam (by omega)
  have d0 := (delta0_isKPair m lam (m + 2) (by omega) (by omega)).imp (a5.and b4)
  have d1 := d0.ball (m + 2) (m + 1) (by omega)
  have d2 := d1.ball (m + 1) m (by omega)
  have d3 := d2.ball m H (by omega)
  have s0 := ((delta0_isSucc (m + 8) (m + 4) (by omega)).bex (m + 8) lam (by omega)).ball
    (m + 4) lam (by omega)
  have k0 := (delta0_isNatZ 0 lam).not.imp (s0.imp d3)
  refine (k0.congr ?_).mono ?_
  · intro Dd v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    exact (limClause_iff_bounded (v H) (v lam)).symm
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase] at hk ⊢
    omega

theorem delta0_zeroPairMem (H : ℕ) :
    Delta0Def.{u} {H} (fun _ v => ZFSet.pair (natZ 0) (natZ 0) ∈ v H) := by
  have h := (delta0_tagPair0 (H + 1)).bex (H + 1) H (by omega)
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    exact ⟨fun ⟨_, hp, e⟩ => e ▸ hp, fun hp => ⟨_, hp, rfl⟩⟩
  · ext k
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton, Finset.mem_union]
    omega

/-! ### Definition 9.1: codes for the constructible hierarchy -/

/-- **Definition 9.1**. `LCode(η, M, c)`: for some `U, H, S, D` bounded by `⋃⋃c` one has
`FourCode(c, U, H, S, D)` together with

1. `η` is an ordinal, `U` is transitive with `η, M, H, S, D, ω ∈ U`, and `PUCl(U)`;
2. `H` is a function with domain exactly `η + 1`, `S` and `D` are functions with domain
   exactly `η`, and `H(0) = ∅`;
3. `SatCode(H(ξ), U, S(ξ))` for every `ξ < η`;
4. `D(ξ)` enumerates the definable subsets of `H(ξ)` for every `ξ < η`;
5. `H(ξ + 1) = ran D(ξ)` (9.2), `H(λ) = ⋃_{ξ<λ} H(ξ)` for non-zero limit `λ ≤ η` (9.3),
   and `M = H(η)`. -/
def LCode (h w η M c : ZFSet.{u}) : Prop :=
  ∃ U H S D, FourCode c U H S D ∧
    (η.IsOrdinal ∧ U.IsTransitive ∧ η ∈ U ∧ M ∈ U ∧ H ∈ U ∧ S ∈ U ∧ D ∈ U ∧ w ∈ U ∧ PUCl U) ∧
    (IsFunc H ∧ IsDom H (insert η η) ∧ IsFunc S ∧ IsDom S η ∧ IsFunc D ∧ IsDom D η ∧
      ZFSet.pair (natZ 0) (natZ 0) ∈ H) ∧
    (∀ ξ ∈ η, SatClause h w U H S ξ) ∧
    (∀ ξ ∈ η, DefClause h w U H S D ξ) ∧
    (∀ ξ ∈ η, SuccClause H D ξ) ∧
    ((∀ lam ∈ η, LimClause H lam) ∧ LimClause H η) ∧
    ZFSet.pair η M ∈ H

set_option linter.unusedVariables false in
theorem delta0_lcode (h w η M c : ℕ) (hhw : h ≠ w) (hhη : h ≠ η) (hhM : h ≠ M) (hhc : h ≠ c)
    (hwη : w ≠ η) (hwM : w ≠ M) (hwc : w ≠ c) (hηM : η ≠ M) (hηc : η ≠ c) (hMc : M ≠ c) :
    Delta0Def {h, w, η, M, c} (fun _ v => LCode (v h) (v w) (v η) (v M) (v c)) := by
  set m := h + w + η + M + c + 1 with hm
  -- U := m, H := m+1, S := m+2, D := m+3
  -- p₀ := m+4, q₀ := m+5, p₁ := m+6, q₁ := m+7, p₂ := m+8, q₂ := m+9,
  -- p₃ := m+10, q₃ := m+11, ξ / lam := m+12
  have d1 := (delta0_isOrdinal η).and ((delta0_isTransitive m).and
    ((Delta0Def.mem η m).and ((Delta0Def.mem M m).and ((Delta0Def.mem (m + 1) m).and
      ((Delta0Def.mem (m + 2) m).and ((Delta0Def.mem (m + 3) m).and
        ((Delta0Def.mem w m).and (delta0_puCl m))))))))
  have d2 := (delta0_isFunc (m + 1)).and ((delta0_isDomInsert (m + 1) η).and
    ((delta0_isFunc (m + 2)).and ((delta0_isDom (m + 2) η (by omega)).and
      ((delta0_isFunc (m + 3)).and ((delta0_isDom (m + 3) η (by omega)).and
        (delta0_zeroPairMem (m + 1)))))))
  have d3 := (delta0_satClause h w m (m + 1) (m + 2) (m + 12) hhw (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)).ball (m + 12) η (by omega)
  have d4 := (delta0_defClause h w m (m + 1) (m + 2) (m + 3) (m + 12) hhw (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)).ball (m + 12) η (by omega)
  have d5 := (delta0_succClause (m + 1) (m + 3) (m + 12) (by omega) (by omega)
    (by omega)).ball (m + 12) η (by omega)
  have d6 := ((delta0_limClause (m + 1) (m + 12) (by omega)).ball (m + 12) η (by omega)).and
    (delta0_limClause (m + 1) η (by omega))
  have d7 := delta0_funVal (m + 1) η M (by omega) (by omega) (by omega)
  have body := (delta0_fourCode c m (m + 1) (m + 2) (m + 3) (by omega) (by omega) (by omega)
    (by omega)).and (d1.and (d2.and (d3.and (d4.and (d5.and (d6.and d7))))))
  have e1 := body.bex (m + 3) (m + 11) (by omega)
  have e2 := e1.bex (m + 11) (m + 10) (by omega)
  have e3 := e2.bex (m + 10) c (by omega)
  have e4 := e3.bex (m + 2) (m + 9) (by omega)
  have e5 := e4.bex (m + 9) (m + 8) (by omega)
  have e6 := e5.bex (m + 8) c (by omega)
  have e7 := e6.bex (m + 1) (m + 7) (by omega)
  have e8 := e7.bex (m + 7) (m + 6) (by omega)
  have e9 := e8.bex (m + 6) c (by omega)
  have e10 := e9.bex m (m + 5) (by omega)
  have e11 := e10.bex (m + 5) (m + 4) (by omega)
  have e12 := e11.bex (m + 4) c (by omega)
  refine (e12.congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    exact (bexFour_iff (v c) _).symm
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase] at hk ⊢
    omega

/-! ### Condition 4 enumerates exactly the definable subsets -/

/-- The transposition of `0` and `i`. -/
def swap0 (i : ℕ) : ℕ → ℕ := fun j => if j = i then 0 else if j = 0 then i else j

theorem swap0_involutive (i : ℕ) : ∀ j, swap0 i (swap0 i j) = j := by
  intro j
  unfold swap0
  by_cases hji : j = i
  · subst hji
    by_cases h0 : j = 0
    · simp [h0]
    · simp [h0]
  · by_cases hj0 : j = 0
    · subst hj0
      simp only [if_neg hji, if_pos rfl]
      by_cases hi0 : i = 0
      · simp [hi0]
      · simp [hi0]
    · simp [hji, hj0]

theorem swap0_injective (i : ℕ) : Function.Injective (swap0 i) :=
  Function.involutive_iff_iter_2_eq_id.mpr (funext (swap0_involutive i)) |>.injective

theorem swap0_eq_zero_iff (i j : ℕ) : swap0 i j = 0 ↔ j = i := by
  unfold swap0
  by_cases hji : j = i
  · simp [hji]
  · rw [if_neg hji]
    by_cases hj0 : j = 0
    · rw [if_pos hj0]
      exact ⟨fun h => hj0.trans h.symm, fun h => absurd h hji⟩
    · rw [if_neg hj0]
      exact ⟨fun h => absurd h hj0, fun h => absurd h hji⟩

theorem swap0_apply_self (i : ℕ) : swap0 i i = 0 := by simp [swap0]

/-- One half of (9.1): a definability input `⟨e, a⟩` names a definable subset of `A`. -/
theorem definableOver_of_defInp {U A T e a X : ZFSet.{u}}
    (hsat : SatCode (L Ordinal.omega0) ωZ A U T)
    (hinp : DefInp (L Ordinal.omega0) ωZ A e a) (hXA : X ⊆ A)
    (hXval : ∀ x ∈ A, (x ∈ X ↔ ∃ ax ∈ U, IsConsSeq x a ax ∧ ZFSet.pair e ax ∈ T)) :
    X ∈ Def A := by
  classical
  have hseqU : ∀ b, IsSeqA ωZ A b → b ∈ U := fun b hb =>
    seq_mem_of_puCl hsat.trans hsat.A_mem hsat.w_mem hsat.pucl hb
  obtain ⟨φ, rfl⟩ := (isCodeW_iff e).mp hinp.1
  obtain ⟨ha, hcov⟩ := defInp_code_iff.mp hinp
  set v : ℕ → ZFSet.{u} := fun j => if j = 0 then ∅ else SeqVal a (j - 1) with hvdef
  have hvA : ∀ j ∈ (Fm.fv φ).erase 0, v j ∈ A := by
    intro j hj
    rw [Finset.mem_erase] at hj
    simp only [hvdef, if_neg hj.1]
    refine seqVal_mem_of_inDom ha (hcov (j - 1) ?_)
    have hj1 : j - 1 + 1 = j := by omega
    rw [hj1]; exact hj.2
  refine mem_Def.mpr ⟨hXA, φ, 0, v, hvA, fun x => ?_⟩
  by_cases hxA : x ∈ A
  · obtain ⟨ax, hax, haxseq, hax0, haxv0, haxs⟩ := exists_consSeq ha hxA
    have haxU : ax ∈ U := hseqU ax haxseq
    have hcov' : ∀ j ∈ Fm.fv φ, InDomZ ax (natZ j) := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · exact hax0
      · obtain ⟨mm, rfl⟩ : ∃ mm, j = mm + 1 := ⟨j - 1, by omega⟩
        exact (haxs mm (hcov mm hj)).1
    have hagree : ∀ j ∈ Fm.fv φ, SeqVal ax j = Function.update v 0 x j := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · rw [haxv0, Function.update_self]
      · obtain ⟨mm, rfl⟩ : ∃ mm, j = mm + 1 := ⟨j - 1, by omega⟩
        rw [(haxs mm (hcov mm hj)).2, Function.update_of_ne (by omega)]
        simp only [hvdef, if_neg (Nat.succ_ne_zero mm), Nat.add_sub_cancel]
    rw [hXval x hxA]
    constructor
    · rintro ⟨ax', hax'U, hax', hT⟩
      rw [isConsSeq_unique hax' hax] at hT
      exact ⟨hxA, (sat_congr hagree).mp
        ((satCode_correct hsat φ ax haxseq hcov').mp hT)⟩
    · rintro ⟨-, hs⟩
      refine ⟨ax, haxU, hax, ?_⟩
      rw [satCode_correct hsat φ ax haxseq hcov']
      exact (sat_congr hagree).mpr hs
  · exact ⟨fun hxX => absurd (hXA hxX) hxA, fun hx => absurd hx.1 hxA⟩

/-- The other half of (9.1): every definable subset of `A` is named by a definability input.
The designated variable is normalised to `v0` by the transposition `swap0 i`. -/
theorem exists_defInp_of_definableOver {U A T X : ZFSet.{u}}
    (hsat : SatCode (L Ordinal.omega0) ωZ A U T) (hX : X ∈ Def A) :
    ∃ e ∈ L Ordinal.omega0.{u}, ∃ a ∈ U, DefInp (L Ordinal.omega0) ωZ A e a ∧ X ⊆ A ∧
      ∀ x ∈ A, (x ∈ X ↔ ∃ ax ∈ U, IsConsSeq x a ax ∧ ZFSet.pair e ax ∈ T) := by
  classical
  have hseqU : ∀ b, IsSeqA ωZ A b → b ∈ U := fun b hb =>
    seq_mem_of_puCl hsat.trans hsat.A_mem hsat.w_mem hsat.pucl hb
  obtain ⟨hXA, φ, i, v, hvA, hXdef⟩ := mem_Def.mp hX
  set f := swap0 i with hf
  have hfinj : Function.Injective f := swap0_injective i
  set ψ := Fm.rename f φ with hψ
  have hfvψ : Fm.fv ψ = (Fm.fv φ).image f := fv_rename f hfinj φ
  set s : Finset ℕ := ((Fm.fv ψ).erase 0).image (fun j => j - 1) with hs
  have hsmem : ∀ mm : ℕ, mm ∈ s ↔ (mm + 1) ∈ Fm.fv ψ := by
    intro mm
    simp only [hs, Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨j, ⟨hj0, hjψ⟩, rfl⟩
      have hj1 : j - 1 + 1 = j := by omega
      rw [hj1]; exact hjψ
    · intro hmm; exact ⟨mm + 1, ⟨Nat.succ_ne_zero mm, hmm⟩, by omega⟩
  have hkey : ∀ j : ℕ, j ∈ Fm.fv ψ → j ≠ 0 → f j ∈ Fm.fv φ ∧ f j ≠ i := by
    intro j hj hj0
    rw [hfvψ, Finset.mem_image] at hj
    obtain ⟨k, hk, rfl⟩ := hj
    rw [hf, swap0_involutive i k]
    refine ⟨hk, fun hki => hj0 ?_⟩
    rw [hki, hf, swap0_apply_self]
  set v'' : ℕ → ZFSet.{u} := fun mm => v (f (mm + 1)) with hv''
  have hv''A : ∀ mm ∈ s, v'' mm ∈ A := by
    intro mm hmm
    obtain ⟨hmem, hne⟩ := hkey (mm + 1) ((hsmem mm).mp hmm) (Nat.succ_ne_zero mm)
    exact hvA _ (Finset.mem_erase.mpr ⟨hne, hmem⟩)
  obtain ⟨a, ha, hadom, haval⟩ := exists_seq_of_val s v'' hv''A
  have hinp : DefInp (L Ordinal.omega0) ωZ A ψ.code a :=
    defInp_code_iff.mpr ⟨ha, fun j hj => hadom j ((hsmem j).mpr hj)⟩
  refine ⟨ψ.code, Fm.code_mem_Lω ψ, a, hseqU a ha, hinp, hXA, fun x hxA => ?_⟩
  obtain ⟨ax, hax, haxseq, hax0, haxv0, haxs⟩ := exists_consSeq ha hxA
  have haxU : ax ∈ U := hseqU ax haxseq
  have hcov' : ∀ j ∈ Fm.fv ψ, InDomZ ax (natZ j) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · exact hax0
    · obtain ⟨mm, rfl⟩ : ∃ mm, j = mm + 1 := ⟨j - 1, by omega⟩
      exact (haxs mm (hadom mm ((hsmem mm).mpr hj))).1
  have hagree : ∀ j ∈ Fm.fv φ, (SeqVal ax ∘ f) j = Function.update v i x j := by
    intro j hj
    by_cases hji : j = i
    · subst hji
      simp only [Function.comp_apply, hf, swap0_apply_self, haxv0, Function.update_self]
    · have hfj0 : f j ≠ 0 := fun hc => hji ((swap0_eq_zero_iff i j).mp hc)
      obtain ⟨mm, hmm⟩ : ∃ mm, f j = mm + 1 := ⟨f j - 1, by omega⟩
      have hmmψ : (mm + 1) ∈ Fm.fv ψ := by
        rw [hfvψ, Finset.mem_image]; exact ⟨j, hj, hmm⟩
      have hmms : mm ∈ s := (hsmem mm).mpr hmmψ
      simp only [Function.comp_apply, hmm]
      rw [(haxs mm (hadom mm hmms)).2, haval mm hmms, Function.update_of_ne hji]
      simp only [hv'', ← hmm, hf, swap0_involutive i j]
  rw [hXdef x]
  constructor
  · rintro ⟨-, hsx⟩
    refine ⟨ax, haxU, hax, ?_⟩
    have hcorr : Sat (· ∈ A) (SeqVal ax ∘ f) φ := (sat_congr hagree).mpr hsx
    rw [satCode_correct hsat ψ ax haxseq hcov', hψ]
    exact (sat_rename hfinj).mpr hcorr
  · rintro ⟨ax', hax'U, hax', hT⟩
    rw [isConsSeq_unique hax' hax] at hT
    have hcorr := (satCode_correct hsat ψ ax haxseq hcov').mp hT
    rw [hψ] at hcorr
    exact ⟨hxA, (sat_congr hagree).mp ((sat_rename hfinj).mp hcorr)⟩

/-- **The content of condition 4**: through a satisfaction code for `A`, the range of the
enumeration `Dx` is exactly `Def A`. -/
theorem mem_ran_defEnum_iff {U A T Dx : ZFSet.{u}}
    (hsat : SatCode (L Ordinal.omega0) ωZ A U T)
    (hD : IsDefEnum (L Ordinal.omega0) ωZ U A T Dx) {Y : ZFSet.{u}} :
    (∃ k, ZFSet.pair k Y ∈ Dx) ↔ Y ∈ Def A := by
  obtain ⟨-, hdom, hval⟩ := hD
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨e, -, a, -, rfl, hinp⟩ := (hdom k).mp ⟨Y, hk⟩
    obtain ⟨hYA, hYval⟩ := hval _ _ _ hk
    exact definableOver_of_defInp hsat hinp hYA hYval
  · intro hY
    obtain ⟨e, he, a, haU, hinp, hYA, hYval⟩ := exists_defInp_of_definableOver hsat hY
    obtain ⟨b, hb⟩ := (hdom (ZFSet.pair e a)).mpr ⟨e, he, a, haU, rfl, hinp⟩
    obtain ⟨hbA, hbval⟩ := hval _ _ _ hb
    have hbY : b = Y := by
      ext x
      by_cases hxA : x ∈ A
      · rw [hbval x hxA, hYval x hxA]
      · exact ⟨fun hxb => absurd (hbA hxb) hxA, fun hxY => absurd (hYA hxY) hxA⟩
    rw [hbY] at hb
    exact ⟨_, hb⟩

/-! ### Lemma 9.2: soundness of a code -/

theorem toZFSet_ne_empty {ξ : Ordinal.{u}} (h : 0 < ξ) : ξ.toZFSet ≠ (∅ : ZFSet.{u}) := by
  intro he
  have h0 : (0 : Ordinal.{u}).toZFSet ∈ ξ.toZFSet := Ordinal.toZFSet_mem_toZFSet_iff.mpr h
  rw [he] at h0
  exact ZFSet.notMem_empty _ h0

/-- **Lemma 9.2**: a code for `η` describes `L η`. -/
theorem lcode_sound {η : Ordinal.{u}} {M c : ZFSet.{u}}
    (hcode : LCode (L Ordinal.omega0.{u}) ωZ.{u} η.toZFSet M c) : M = L η := by
  obtain ⟨U, H, S, D, -, -, ⟨hHf, hHdom, -, hSdom, -, hDdom, hH0⟩, hsat, hdef, hsucc,
    ⟨hlim, hlimη⟩, hMH⟩ := hcode
  have hHval : ∀ a : Ordinal.{u}, a ≤ η → ∃ Ha, ZFSet.pair a.toZFSet Ha ∈ H := by
    intro a hle
    refine (hHdom a.toZFSet).mp ?_
    rw [ZFSet.mem_insert_iff]
    rcases lt_or_eq_of_le hle with hlt | rfl
    · exact Or.inr (Ordinal.toZFSet_mem_toZFSet_iff.mpr hlt)
    · exact Or.inl rfl
  have key : ∀ ξ : Ordinal.{u}, ξ ≤ η → ZFSet.pair ξ.toZFSet (L ξ) ∈ H := by
    intro ξ
    induction ξ using Ordinal.limitRecOn with
    | zero =>
      intro _
      rw [Ordinal.toZFSet_zero, L_zero, ← natZ_zero]
      exact hH0
    | add_one ζ ih =>
      intro hle
      have hζη : ζ < η := lt_of_lt_of_le (Order.lt_add_one_iff.mpr le_rfl) hle
      have hζmem : ζ.toZFSet ∈ η.toZFSet := Ordinal.toZFSet_mem_toZFSet_iff.mpr hζη
      obtain ⟨Sζ, hSζ⟩ := (hSdom ζ.toZFSet).mp hζmem
      obtain ⟨Dζ, hDζ⟩ := (hDdom ζ.toZFSet).mp hζmem
      obtain ⟨Hζ', hHζ'⟩ := hHval (ζ + 1) hle
      have hsc := hsat _ hζmem (L ζ) (ih hζη.le) Sζ hSζ
      have hde := hdef _ hζmem (L ζ) (ih hζη.le) Sζ hSζ Dζ hDζ
      have hran : IsRan Dζ Hζ' := by
        refine hsucc _ hζmem Dζ hDζ Hζ' ?_
        rwa [← Ordinal.toZFSet_add_one]
      have hHeq : Hζ' = L (ζ + 1) := by
        rw [L_succ]
        ext y
        rw [hran y, mem_ran_defEnum_iff hsc hde]
      rwa [hHeq] at hHζ'
    | limit ξ hlimξ ih =>
      intro hle
      have hsuccclosed : ∀ ζ ∈ ξ.toZFSet, insert ζ ζ ∈ ξ.toZFSet := by
        intro ζ hζ
        obtain ⟨a, ha, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hζ
        rw [← Ordinal.toZFSet_add_one]
        exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (hlimξ.add_one_lt ha)
      have hstep : LimClause H ξ.toZFSet := by
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact hlim _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr hlt)
        · rw [heq]; exact hlimη
      obtain ⟨Hξ, hHξ⟩ := hHval ξ hle
      obtain ⟨hsub1, hsub2⟩ :=
        hstep (toZFSet_ne_empty hlimξ.pos) hsuccclosed Hξ hHξ
      have hHeq : Hξ = L ξ := by
        ext x
        constructor
        · intro hx
          obtain ⟨ζ, hζ, Hz, hHz, hxH⟩ := hsub1 x hx
          obtain ⟨a, ha, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hζ
          have hE : Hz = L a := hHf.2 _ _ _ hHz (ih a ha (ha.le.trans hle))
          rw [hE] at hxH
          exact (mem_L_limit hlimξ).mpr ⟨a, ha, hxH⟩
        · intro hx
          obtain ⟨a, ha, hxa⟩ := (mem_L_limit hlimξ).mp hx
          exact hsub2 a.toZFSet (Ordinal.toZFSet_mem_toZFSet_iff.mpr ha) (L a)
            (ih a ha (ha.le.trans hle)) hxa
      rwa [hHeq] at hHξ
  exact hHf.2 _ _ _ hMH (key η le_rfl)

/-- Condition 1 of Definition 9.1: the index of a code is an ordinal in the sense of `ZFSet`. -/
theorem lcode_isOrdinal {h w η M c : ZFSet.{u}} (hcode : LCode h w η M c) : η.IsOrdinal := by
  obtain ⟨-, -, -, -, -, ⟨hη, -⟩, -⟩ := hcode
  exact hη

/-- The index of a code is the image of the external ordinal `η.rank`; the ambient universe
is well founded, so an internal ordinal and an external one are the same thing. -/
theorem lcode_index_eq {h w η M c : ZFSet.{u}} (hcode : LCode h w η M c) :
    η.rank.toZFSet = η :=
  (lcode_isOrdinal hcode).toZFSet_rank_eq

/-- **Lemma 9.2, general form**: the paper states the lemma for an arbitrary `η` satisfying
condition 1 of Definition 9.1, that is, for an arbitrary ordinal in the sense of `ZFSet`; it is
not restricted to indices of the form `ξ.toZFSet` for an external `ξ : Ordinal`.  By
`lcode_index_eq` such an `η` *is* `η.rank.toZFSet`, so `lcode_sound` applies and gives
`M = L η`, the level of the hierarchy indexed by the internal ordinal `η`. -/
theorem lcode_sound_isOrdinal {η M c : ZFSet.{u}}
    (hcode : LCode (L Ordinal.omega0.{u}) ωZ.{u} η M c) : M = L η.rank :=
  lcode_sound (by rwa [lcode_index_eq hcode])

/-- The external form is the special case `η = ξ.toZFSet` of `lcode_sound_isOrdinal`. -/
theorem lcode_sound_of_toZFSet_eq {η M c : ZFSet.{u}} {ζ : Ordinal.{u}} (hζ : ζ.toZFSet = η)
    (hcode : LCode (L Ordinal.omega0.{u}) ωZ.{u} η M c) : M = L ζ := by
  subst hζ
  rw [lcode_sound_isOrdinal hcode, Ordinal.rank_toZFSet]

/-! ### The definable power set through a satisfaction code -/

/-- `Y` is the definable power set of `A`, read off the satisfaction code `T` through the
definability inputs of §9.1.  This is the Σ₁ set function `Y = Def(X)` used in the proof of
Lemma 10.5(2). -/
def IsDefPow (h w U A T Y : ZFSet.{u}) : Prop :=
  ∀ X, X ∈ Y ↔ ∃ e ∈ h, ∃ a ∈ U, DefInp h w A e a ∧ X ⊆ A ∧
    ∀ x ∈ A, (x ∈ X ↔ ∃ ax ∈ U, IsConsSeq x a ax ∧ ZFSet.pair e ax ∈ T)

theorem isDefPow_iff {U A T : ZFSet.{u}} (hsat : SatCode (L Ordinal.omega0) ωZ A U T)
    {Y : ZFSet.{u}} : IsDefPow (L Ordinal.omega0) ωZ U A T Y ↔ Y = Def A := by
  have key : ∀ X : ZFSet.{u},
      (∃ e ∈ L Ordinal.omega0.{u}, ∃ a ∈ U, DefInp (L Ordinal.omega0) ωZ A e a ∧ X ⊆ A ∧
        ∀ x ∈ A, (x ∈ X ↔ ∃ ax ∈ U, IsConsSeq x a ax ∧ ZFSet.pair e ax ∈ T)) ↔ X ∈ Def A := by
    intro X
    exact ⟨fun ⟨_, _, _, _, hinp, hXA, hXval⟩ => definableOver_of_defInp hsat hinp hXA hXval,
      fun hX => exists_defInp_of_definableOver hsat hX⟩
  constructor
  · intro hY
    ext X
    rw [hY X, key]
  · rintro rfl X
    rw [key]

/-- The value clause of `IsDefPow` in the paper's own form (9.1), with `a_x` a term. -/
theorem IsDefPow.val_term {U A T Y X : ZFSet.{u}}
    (hsat : SatCode (L Ordinal.omega0) ωZ A U T)
    (hY : IsDefPow (L Ordinal.omega0) ωZ U A T Y) (hX : X ∈ Y) :
    ∃ e ∈ L Ordinal.omega0.{u}, ∃ a ∈ U, DefInp (L Ordinal.omega0) ωZ A e a ∧ X ⊆ A ∧
      ∀ x ∈ A, ∀ ax, IsConsSeq x a ax → (x ∈ X ↔ ZFSet.pair e ax ∈ T) := by
  obtain ⟨e, he, a, haU, hinp, hXA, hval⟩ := (hY X).mp hX
  exact ⟨e, he, a, haU, hinp, hXA, (defVal_iff_term hsat hinp.2.1).mp hval⟩

theorem isDefPow_iff_bounded (h w U A T Y : ZFSet.{u}) :
    IsDefPow h w U A T Y ↔
      ((∀ X ∈ Y, ∃ e ∈ h, ∃ a ∈ U, DefInp h w A e a ∧ X ⊆ A ∧
          ((∀ x ∈ X, x ∈ A ∧ ∃ ax ∈ U, IsConsSeq x a ax ∧ ZFSet.pair e ax ∈ T) ∧
            (∀ x ∈ A, (∃ ax ∈ U, IsConsSeq x a ax ∧ ZFSet.pair e ax ∈ T) → x ∈ X))) ∧
        (∀ e ∈ h, ∀ a ∈ U, DefInp h w A e a →
          ∃ X ∈ Y, ((∀ x ∈ X, x ∈ A ∧ ∃ ax ∈ U, IsConsSeq x a ax ∧ ZFSet.pair e ax ∈ T) ∧
            (∀ x ∈ A, (∃ ax ∈ U, IsConsSeq x a ax ∧ ZFSet.pair e ax ∈ T) → x ∈ X)))) := by
  classical
  constructor
  · intro hY
    refine ⟨fun X hX => ?_, fun e he a ha hinp => ?_⟩
    · obtain ⟨e, he, a, haU, hinp, hXA, hXval⟩ := (hY X).mp hX
      exact ⟨e, he, a, haU, hinp, hXA,
        fun x hxX => ⟨hXA hxX, (hXval x (hXA hxX)).mp hxX⟩,
        fun x hxA hP => (hXval x hxA).mpr hP⟩
    · refine ⟨ZFSet.sep (fun x => ∃ ax ∈ U, IsConsSeq x a ax ∧ ZFSet.pair e ax ∈ T) A, ?_, ?_, ?_⟩
      · refine (hY _).mpr ⟨e, he, a, ha, hinp, fun x hx => (ZFSet.mem_sep.mp hx).1, fun x _ => ?_⟩
        rw [ZFSet.mem_sep]
        exact ⟨fun hx => hx.2, fun hx => ⟨‹_›, hx⟩⟩
      · intro x hx
        rw [ZFSet.mem_sep] at hx
        exact hx
      · intro x hxA hP
        rw [ZFSet.mem_sep]
        exact ⟨hxA, hP⟩
  · rintro ⟨H1, H2⟩ X
    constructor
    · intro hX
      obtain ⟨e, he, a, haU, hinp, hXA, hx1, hx2⟩ := H1 X hX
      exact ⟨e, he, a, haU, hinp, hXA,
        fun x hxA => ⟨fun hxX => (hx1 x hxX).2, fun hP => hx2 x hxA hP⟩⟩
    · rintro ⟨e, he, a, haU, hinp, hXA, hXval⟩
      obtain ⟨X', hX'Y, hx1, hx2⟩ := H2 e he a haU hinp
      have hXX' : X = X' := by
        ext y
        constructor
        · intro hy; exact hx2 y (hXA hy) ((hXval y (hXA hy)).mp hy)
        · intro hy; exact (hXval y (hx1 y hy).1).mpr (hx1 y hy).2
      rwa [hXX']

set_option linter.unusedVariables false in
theorem delta0_isDefPow (h w U A T Y : ℕ) (hhw : h ≠ w) (hhU : h ≠ U) (hhA : h ≠ A)
    (hhT : h ≠ T) (hhY : h ≠ Y) (hwU : w ≠ U) (hwA : w ≠ A) (hwT : w ≠ T) (hwY : w ≠ Y)
    (hUA : U ≠ A) (hUT : U ≠ T) (hUY : U ≠ Y) (hAT : A ≠ T) (hAY : A ≠ Y) (hTY : T ≠ Y) :
    Delta0Def {h, w, U, A, T, Y}
      (fun _ v => IsDefPow (v h) (v w) (v U) (v A) (v T) (v Y)) := by
  set m := h + w + U + A + T + Y + 1 with hm
  -- X := m, e := m+1, a := m+2, x := m+3, ax := m+4
  have p0 := (delta0_isConsSeq (m + 3) (m + 2) (m + 4) (by omega) (by omega) (by omega)).and
    (delta0_funVal T (m + 1) (m + 4) (by omega) (by omega) (by omega))
  have p1 := p0.bex (m + 4) U (by omega)
  have e1 := ((Delta0Def.mem (m + 3) A).and p1).ball (m + 3) m (by omega)
  have e2 := (p1.imp (Delta0Def.mem (m + 3) m)).ball (m + 3) A (by omega)
  have ext := e1.and e2
  have q0 := (delta0_defInp h w A (m + 1) (m + 2) hhw hhA (by omega) (by omega) hwA
    (by omega) (by omega) (by omega) (by omega) (by omega)).and
    ((delta0_subset m A (by omega)).and ext)
  have q1 := q0.bex (m + 2) U (by omega)
  have q2 := q1.bex (m + 1) h (by omega)
  have c1 := q2.ball m Y (by omega)
  have r1 := ext.bex m Y (by omega)
  have r2 := (delta0_defInp h w A (m + 1) (m + 2) hhw hhA (by omega) (by omega) hwA
    (by omega) (by omega) (by omega) (by omega) (by omega)).imp r1
  have r3 := r2.ball (m + 2) U (by omega)
  have c2 := r3.ball (m + 1) h (by omega)
  refine ((c1.and c2).congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    exact (isDefPow_iff_bounded (v h) (v w) (v U) (v A) (v T) (v Y)).symm
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase] at hk ⊢
    omega

/-! ### The canonical enumeration `D(ξ)` -/

/-- The subset of `A` defined by the input `⟨e, a⟩` through the truth part `T`. -/
noncomputable def defBit (A T e a : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => ∃ ax, IsConsSeq x a ax ∧ ZFSet.pair e ax ∈ T) A

theorem mem_defBit {A T e a x : ZFSet.{u}} :
    x ∈ defBit A T e a ↔ x ∈ A ∧ ∃ ax, IsConsSeq x a ax ∧ ZFSet.pair e ax ∈ T := ZFSet.mem_sep

theorem defBit_subset (A T e a : ZFSet.{u}) : defBit A T e a ⊆ A :=
  fun _ hx => (mem_defBit.mp hx).1

/-- The value clause of Definition 9.1, condition 4, pins the value down to `defBit`. -/
theorem eq_defBit {U A T e a b : ZFSet.{u}} (hsat : SatCode (L Ordinal.omega0) ωZ A U T)
    (ha : IsSeqA ωZ A a) (hbA : b ⊆ A)
    (hb : ∀ x ∈ A, (x ∈ b ↔ ∃ ax ∈ U, IsConsSeq x a ax ∧ ZFSet.pair e ax ∈ T)) :
    b = defBit A T e a := by
  ext x
  by_cases hxA : x ∈ A
  · rw [hb x hxA, mem_defBit]
    constructor
    · rintro ⟨ax, -, hax, hT⟩; exact ⟨hxA, ax, hax, hT⟩
    · rintro ⟨-, ax, hax, hT⟩
      obtain ⟨ax', hax', hseq', -, -, -⟩ := exists_consSeq ha hxA
      refine ⟨ax, ?_, hax, hT⟩
      rw [isConsSeq_unique hax hax']
      exact seq_mem_of_puCl hsat.trans hsat.A_mem hsat.w_mem hsat.pucl hseq'
  · exact ⟨fun hx => absurd (hbA hx) hxA, fun hx => absurd (defBit_subset A T e a hx) hxA⟩

/-- The canonical enumeration of the definable subsets of `A` through `T`. -/
noncomputable def defEnum (A T : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pairSep (fun k b => ∃ e a, k = ZFSet.pair e a ∧ b = defBit A T e a)
    (ZFSet.pairSep (fun e a => DefInp (L Ordinal.omega0) ωZ A e a) (L Ordinal.omega0) (Seqs A))
    (ZFSet.powerset A)

theorem mem_defEnum {A T p : ZFSet.{u}} :
    p ∈ defEnum A T ↔ ∃ e ∈ L Ordinal.omega0.{u}, ∃ a, DefInp (L Ordinal.omega0) ωZ A e a ∧
      p = ZFSet.pair (ZFSet.pair e a) (defBit A T e a) := by
  rw [defEnum, ZFSet.mem_pairSep]
  constructor
  · rintro ⟨k, hk, b, -, rfl, e, a, rfl, rfl⟩
    rw [ZFSet.mem_pairSep] at hk
    obtain ⟨e', he', a', -, hkeq, hinp⟩ := hk
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective hkeq
    exact ⟨_, he', _, hinp, rfl⟩
  · rintro ⟨e, he, a, hinp, rfl⟩
    refine ⟨ZFSet.pair e a, ?_, defBit A T e a, ?_, rfl, e, a, rfl, rfl⟩
    · rw [ZFSet.mem_pairSep]
      exact ⟨e, he, a, mem_Seqs.mpr hinp.2.1, rfl, hinp⟩
    · rw [ZFSet.mem_powerset]; exact defBit_subset A T e a

theorem isDefEnum_defEnum {U A T : ZFSet.{u}} (hsat : SatCode (L Ordinal.omega0) ωZ A U T) :
    IsDefEnum (L Ordinal.omega0) ωZ U A T (defEnum A T) := by
  have hseqU : ∀ b, IsSeqA ωZ A b → b ∈ U := fun b hb =>
    seq_mem_of_puCl hsat.trans hsat.A_mem hsat.w_mem hsat.pucl hb
  have hvals : ∀ e a x, DefInp (L Ordinal.omega0) ωZ A e a → x ∈ A →
      (x ∈ defBit A T e a ↔ ∃ ax ∈ U, IsConsSeq x a ax ∧ ZFSet.pair e ax ∈ T) := by
    intro e a x hinp hxA
    rw [mem_defBit]
    obtain ⟨ax', hax', hseq', -, -, -⟩ := exists_consSeq hinp.2.1 hxA
    constructor
    · rintro ⟨-, ax, hax, hT⟩
      refine ⟨ax, ?_, hax, hT⟩
      rw [isConsSeq_unique hax hax']
      exact hseqU _ hseq'
    · rintro ⟨ax, -, hax, hT⟩
      exact ⟨hxA, ax, hax, hT⟩
  refine ⟨⟨fun p hp => ?_, fun k b b' hb hb' => ?_⟩, fun k => ⟨?_, ?_⟩, fun e a b hb => ?_⟩
  · obtain ⟨e, -, a, -, rfl⟩ := mem_defEnum.mp hp
    exact ⟨_, _, rfl⟩
  · obtain ⟨e, -, a, -, he⟩ := mem_defEnum.mp hb
    obtain ⟨e', -, a', -, he'⟩ := mem_defEnum.mp hb'
    obtain ⟨hk, rfl⟩ := ZFSet.pair_injective he
    obtain ⟨hk', rfl⟩ := ZFSet.pair_injective he'
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective (hk.symm.trans hk')
    rfl
  · rintro ⟨b, hb⟩
    obtain ⟨e, he, a, hinp, heq⟩ := mem_defEnum.mp hb
    obtain ⟨rfl, -⟩ := ZFSet.pair_injective heq
    exact ⟨e, he, a, hseqU a hinp.2.1, rfl, hinp⟩
  · rintro ⟨e, he, a, -, rfl, hinp⟩
    exact ⟨defBit A T e a, mem_defEnum.mpr ⟨e, he, a, hinp, rfl⟩⟩
  · obtain ⟨e', he', a', hinp, heq⟩ := mem_defEnum.mp hb
    obtain ⟨hk, rfl⟩ := ZFSet.pair_injective heq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective hk
    exact ⟨defBit_subset A T e a, fun x hx => hvals e a x hinp hx⟩

theorem isDefEnum_eq_defEnum {U A T Dx : ZFSet.{u}}
    (hsat : SatCode (L Ordinal.omega0) ωZ A U T)
    (hD : IsDefEnum (L Ordinal.omega0) ωZ U A T Dx) : Dx = defEnum A T := by
  obtain ⟨hf, hdom, hval⟩ := hD
  have hseqU : ∀ b, IsSeqA ωZ A b → b ∈ U := fun b hb =>
    seq_mem_of_puCl hsat.trans hsat.A_mem hsat.w_mem hsat.pucl hb
  ext p
  constructor
  · intro hp
    obtain ⟨k, b, rfl⟩ := hf.1 p hp
    obtain ⟨e, he, a, -, rfl, hinp⟩ := (hdom k).mp ⟨b, hp⟩
    obtain ⟨hbA, hbval⟩ := hval e a b hp
    rw [eq_defBit hsat hinp.2.1 hbA hbval]
    exact mem_defEnum.mpr ⟨e, he, a, hinp, rfl⟩
  · intro hp
    obtain ⟨e, he, a, hinp, rfl⟩ := mem_defEnum.mp hp
    obtain ⟨b, hb⟩ := (hdom (ZFSet.pair e a)).mpr ⟨e, he, a, hseqU a hinp.2.1, rfl, hinp⟩
    obtain ⟨hbA, hbval⟩ := hval e a b hb
    rwa [eq_defBit hsat hinp.2.1 hbA hbval] at hb

/-! #### One entry of the enumeration, as a Δ₀ condition -/

/-- `p` is one entry `⟨⟨e, a⟩, b⟩` of the enumeration of Definition 9.1, condition 4. -/
def IsDefEntry (h w U A T p : ZFSet.{u}) : Prop :=
  ∃ e ∈ h, ∃ a ∈ U, DefInp h w A e a ∧ ∃ b, p = ZFSet.pair (ZFSet.pair e a) b ∧ b ⊆ A ∧
    ∀ x ∈ A, (x ∈ b ↔ ∃ ax ∈ U, IsConsSeq x a ax ∧ ZFSet.pair e ax ∈ T)

theorem isDefEntry_iff_bounded (h w U A T p : ZFSet.{u}) :
    IsDefEntry h w U A T p ↔
      ∃ e ∈ h, ∃ a ∈ U, DefInp h w A e a ∧ ∃ q ∈ p, ∃ k ∈ q, ∃ q' ∈ p, ∃ b ∈ q',
        k = ZFSet.pair e a ∧ p = ZFSet.pair k b ∧ b ⊆ A ∧
        ∀ x ∈ A, (x ∈ b ↔ ∃ ax ∈ U, IsConsSeq x a ax ∧ ZFSet.pair e ax ∈ T) := by
  refine exists_congr fun e => and_congr_right fun _ => exists_congr fun a =>
    and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨b, rfl, hbA, hbval⟩
    exact ⟨_, singleton_mem_pair _ _, _, ZFSet.mem_singleton.mpr rfl, _, upair_mem_pair _ _,
      b, mem_upair_right _ _, rfl, rfl, hbA, hbval⟩
  · rintro ⟨q, -, k, -, q', -, b, -, rfl, rfl, hbA, hbval⟩
    exact ⟨b, rfl, hbA, hbval⟩

/-- The value clause of `IsDefEntry` in the paper's own form (9.1), with `a_x` a term. -/
theorem IsDefEntry.val_term {U A T p : ZFSet.{u}}
    (hsat : SatCode (L Ordinal.omega0) ωZ A U T)
    (hp : IsDefEntry (L Ordinal.omega0) ωZ U A T p) :
    ∃ e ∈ L Ordinal.omega0.{u}, ∃ a ∈ U, DefInp (L Ordinal.omega0) ωZ A e a ∧ ∃ b,
      p = ZFSet.pair (ZFSet.pair e a) b ∧ b ⊆ A ∧
        ∀ x ∈ A, ∀ ax, IsConsSeq x a ax → (x ∈ b ↔ ZFSet.pair e ax ∈ T) := by
  obtain ⟨e, he, a, haU, hinp, b, hpe, hbA, hval⟩ := hp
  exact ⟨e, he, a, haU, hinp, b, hpe, hbA, (defVal_iff_term hsat hinp.2.1).mp hval⟩

/-- `defEnum` is exactly the set of entries. -/
theorem mem_defEnum_iff_isDefEntry {U A T : ZFSet.{u}}
    (hsat : SatCode (L Ordinal.omega0) ωZ A U T) {p : ZFSet.{u}} :
    p ∈ defEnum A T ↔ IsDefEntry (L Ordinal.omega0) ωZ U A T p := by
  obtain ⟨-, hdom, hval⟩ := isDefEnum_defEnum hsat
  have hseqU : ∀ b, IsSeqA ωZ A b → b ∈ U := fun b hb =>
    seq_mem_of_puCl hsat.trans hsat.A_mem hsat.w_mem hsat.pucl hb
  constructor
  · intro hp
    obtain ⟨e, he, a, hinp, rfl⟩ := mem_defEnum.mp hp
    obtain ⟨hbA, hbval⟩ := hval e a _ hp
    exact ⟨e, he, a, hseqU a hinp.2.1, hinp, _, rfl, hbA, hbval⟩
  · rintro ⟨e, he, a, -, hinp, b, rfl, hbA, hbval⟩
    rw [eq_defBit hsat hinp.2.1 hbA hbval]
    exact mem_defEnum.mpr ⟨e, he, a, hinp, rfl⟩

set_option linter.unusedVariables false in
theorem delta0_isDefEntry (h w U A T p : ℕ) (hhw : h ≠ w) (hhU : h ≠ U) (hhA : h ≠ A)
    (hhT : h ≠ T) (hhp : h ≠ p) (hwU : w ≠ U) (hwA : w ≠ A) (hwT : w ≠ T) (hwp : w ≠ p)
    (hUA : U ≠ A) (hUT : U ≠ T) (hUp : U ≠ p) (hAT : A ≠ T) (hAp : A ≠ p) (hTp : T ≠ p) :
    Delta0Def {h, w, U, A, T, p}
      (fun _ v => IsDefEntry (v h) (v w) (v U) (v A) (v T) (v p)) := by
  set m := h + w + U + A + T + p + 1 with hm
  -- e := m, a := m+1, q := m+2, k := m+3, q' := m+4, b := m+5, x := m+6, ax := m+7
  have val0 := (delta0_isConsSeq (m + 6) (m + 1) (m + 7) (by omega) (by omega) (by omega)).and
    (delta0_funVal T m (m + 7) (by omega) (by omega) (by omega))
  have val1 := val0.bex (m + 7) U (by omega)
  have val2 := ((Delta0Def.mem (m + 6) (m + 5)).iff val1).ball (m + 6) A (by omega)
  have c0 := (delta0_isKPair (m + 3) m (m + 1) (by omega) (by omega)).and
    ((delta0_isKPair p (m + 3) (m + 5) (by omega) (by omega)).and
      ((delta0_subset (m + 5) A (by omega)).and val2))
  have c1 := c0.bex (m + 5) (m + 4) (by omega)
  have c2 := c1.bex (m + 4) p (by omega)
  have c3 := c2.bex (m + 3) (m + 2) (by omega)
  have c4 := c3.bex (m + 2) p (by omega)
  have c5 := (delta0_defInp h w A m (m + 1) hhw hhA (by omega) (by omega) hwA (by omega)
    (by omega) (by omega) (by omega) (by omega)).and c4
  have c6 := c5.bex (m + 1) U (by omega)
  have c7 := c6.bex m h (by omega)
  refine (c7.congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    exact (isDefEntry_iff_bounded (v h) (v w) (v U) (v A) (v T) (v p)).symm
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_erase] at hk ⊢
    omega

/-! ### An explicit four-tuple code -/

/-- The explicit four-element code of `(U, H, S, D)`. -/
noncomputable def fourTuple (U H S D : ZFSet.{u}) : ZFSet.{u} :=
  ofList [ZFSet.pair (natZ 0) U, ZFSet.pair (natZ 1) H, ZFSet.pair (natZ 2) S,
    ZFSet.pair (natZ 3) D]

theorem mem_fourTuple {U H S D p : ZFSet.{u}} :
    p ∈ fourTuple U H S D ↔ p = ZFSet.pair (natZ 0) U ∨ p = ZFSet.pair (natZ 1) H ∨
      p = ZFSet.pair (natZ 2) S ∨ p = ZFSet.pair (natZ 3) D := by
  rw [fourTuple, mem_ofList]
  simp only [List.mem_cons, List.not_mem_nil, or_false]

theorem fourCode_fourTuple (U H S D : ZFSet.{u}) : FourCode (fourTuple U H S D) U H S D := by
  have hval : ∀ (n : ℕ) (X : ZFSet.{u}) (a b : ZFSet.{u}),
      ZFSet.pair a b = ZFSet.pair (natZ n) X → a = natZ n ∧ b = X :=
    fun _ _ _ _ h => ZFSet.pair_injective h
  refine ⟨⟨fun p hp => ?_, fun a b b' hb hb' => ?_⟩, fun x => ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rcases mem_fourTuple.mp hp with rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
  · rcases mem_fourTuple.mp hb with h | h | h | h <;>
      rcases mem_fourTuple.mp hb' with h' | h' | h' | h' <;>
      obtain ⟨rfl, rfl⟩ := hval _ _ _ _ h <;> obtain ⟨he, rfl⟩ := hval _ _ _ _ h' <;>
      first
        | rfl
        | exact absurd (natZ_injective he) (by decide)
  · intro hx
    obtain ⟨j, hj, rfl⟩ := mem_natZ_iff.mp hx
    interval_cases j
    · exact ⟨U, mem_fourTuple.mpr (Or.inl rfl)⟩
    · exact ⟨H, mem_fourTuple.mpr (Or.inr (Or.inl rfl))⟩
    · exact ⟨S, mem_fourTuple.mpr (Or.inr (Or.inr (Or.inl rfl)))⟩
    · exact ⟨D, mem_fourTuple.mpr (Or.inr (Or.inr (Or.inr rfl)))⟩
  · rintro ⟨b, hb⟩
    rcases mem_fourTuple.mp hb with h | h | h | h <;> obtain ⟨rfl, rfl⟩ := hval _ _ _ _ h
    · exact mem_natZ_iff.mpr ⟨0, by omega, rfl⟩
    · exact mem_natZ_iff.mpr ⟨1, by omega, rfl⟩
    · exact mem_natZ_iff.mpr ⟨2, by omega, rfl⟩
    · exact mem_natZ_iff.mpr ⟨3, by omega, rfl⟩
  · exact mem_fourTuple.mpr (Or.inl rfl)
  · exact mem_fourTuple.mpr (Or.inr (Or.inl rfl))
  · exact mem_fourTuple.mpr (Or.inr (Or.inr (Or.inl rfl)))
  · exact mem_fourTuple.mpr (Or.inr (Or.inr (Or.inr rfl)))

end BM4.ST
