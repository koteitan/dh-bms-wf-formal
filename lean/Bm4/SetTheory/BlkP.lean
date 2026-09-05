/-
  Part III (§12): the *padding* block update of the paper.  Writing `m` for the maximum of
  `dom a` and `{ν i + 1 : i ∈ dom ν}`, the paper puts `dom b = m`, `b j = t i` when `ν i = j`,
  `b j = a j` for the remaining `j ∈ dom a`, and `b j = ∅` for the remaining `j ∈ m`.

  In contrast with `IsBlkUpd` of `Blk.lean`, the domain is padded, so the block variables need
  not already lie in the domain of `a`: `exists_blkUpdP` has no such hypothesis.
-/
import Bm4.SetTheory.Blk

universe u

namespace BM4.ST

open Fm

/-! ### The paper's block update -/

/-- `IsBlkUpdP a ν t b`: the block update of §12, with the domain padded up to the maximum of
`dom a` and `{ν i + 1 : i ∈ dom ν}`.  The last disjunct is the padding: at an index `k` which
is dominated by some value of `ν`, but is neither a value of `ν` nor in the domain of `a`, the
new sequence takes the default value `∅`. -/
def IsBlkUpdP (w a ν t b : ZFSet.{u}) : Prop :=
  IsFunc ν ∧ IsFunc t ∧
    (∀ m x, ZFSet.pair m x ∈ ν → ∃ y, ZFSet.pair m y ∈ t) ∧
    (∀ m y, ZFSet.pair m y ∈ t → ∃ x, ZFSet.pair m x ∈ ν) ∧
    ((∀ p, p ∈ b ↔ (∃ k x, p = ZFSet.pair k x ∧
      ((∃ m, ZFSet.pair m k ∈ ν ∧ ZFSet.pair m x ∈ t) ∨
        (p ∈ a ∧ ∀ m k', ZFSet.pair m k' ∈ ν → k' ≠ k) ∨
        (x = ∅ ∧ (∀ y, ZFSet.pair k y ∉ a) ∧
          (∀ m k', ZFSet.pair m k' ∈ ν → k' ≠ k) ∧
          ∃ m c, ZFSet.pair m c ∈ ν ∧ (k ∈ c ∨ k = c))))) ∧
      (∃ n ∈ w, IsDom ν n) ∧
      (∀ m m' k, ZFSet.pair m k ∈ ν → ZFSet.pair m' k ∈ ν → m = m'))

/-- `ν` is a finite sequence: its domain is an element of `w` (a natural number for `w = ωZ`). -/
theorem IsBlkUpdP.nuSeq {w a ν t b : ZFSet.{u}} (h : IsBlkUpdP w a ν t b) :
    ∃ n ∈ w, IsDom ν n := h.2.2.2.2.2.1

/-- The variable numbers listed by `ν` are pairwise distinct. -/
theorem IsBlkUpdP.nuInj {w a ν t b : ZFSet.{u}} (h : IsBlkUpdP w a ν t b) :
    ∀ m m' k, ZFSet.pair m k ∈ ν → ZFSet.pair m' k ∈ ν → m = m' := h.2.2.2.2.2.2

/-- The padding block update is determined by `a`, `ν` and `t`. -/
theorem isBlkUpdP_unique {w a ν t b b' : ZFSet.{u}} (h : IsBlkUpdP w a ν t b)
    (h' : IsBlkUpdP w a ν t b') : b = b' := by
  ext p
  rw [h.2.2.2.2.1 p, h'.2.2.2.2.1 p]

/-- The three cases of a member of a padding block update, for an explicit pair. -/
theorem blkUpdP_cases {w a ν t b : ZFSet.{u}} (hb : IsBlkUpdP w a ν t b) {k x : ZFSet.{u}}
    (hx : ZFSet.pair k x ∈ b) :
    (∃ m, ZFSet.pair m k ∈ ν ∧ ZFSet.pair m x ∈ t) ∨
      (ZFSet.pair k x ∈ a ∧ ∀ m k', ZFSet.pair m k' ∈ ν → k' ≠ k) ∨
      (x = ∅ ∧ (∀ y, ZFSet.pair k y ∉ a) ∧
        (∀ m k', ZFSet.pair m k' ∈ ν → k' ≠ k) ∧
        ∃ m c, ZFSet.pair m c ∈ ν ∧ (k ∈ c ∨ k = c)) := by
  obtain ⟨k', x', hp, hcase⟩ := (hb.2.2.2.2.1 _).mp hx
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective hp
  exact hcase

/-- A variable outside the block is not a value of the block variable sequence. -/
theorem notNuVal_of_notMem {l : List ℕ} {k : ℕ} (hk : k ∉ l) :
    ∀ m k', ZFSet.pair m k' ∈ seqOfNats.{u} l → k' ≠ natZ.{u} k := by
  intro m k' hmk' hcon
  obtain ⟨i, hi, rfl⟩ := seqOfNats_val hmk'
  exact hk (natZ_injective hcon ▸ hi)

/-! ### The padded length -/

/-- `natBound l` is the least `N` with `i < N` for every `i ∈ l`. -/
def natBound : List ℕ → ℕ
  | [] => 0
  | i :: l => max (i + 1) (natBound l)

theorem lt_natBound_iff {k : ℕ} {l : List ℕ} : k < natBound l ↔ ∃ i ∈ l, k ≤ i := by
  induction l with
  | nil => simp [natBound]
  | cons i l ih =>
    simp only [natBound, List.mem_cons]
    constructor
    · intro h
      by_cases hki : k ≤ i
      · exact ⟨i, Or.inl rfl, hki⟩
      · obtain ⟨j, hj, hkj⟩ := ih.mp (by omega)
        exact ⟨j, Or.inr hj, hkj⟩
    · rintro ⟨j, hj, hkj⟩
      rcases hj with rfl | hj
      · omega
      · have := ih.mpr ⟨j, hj, hkj⟩
        omega

/-! ### Functionality and semantics -/

theorem isFunc_of_isBlkUpdP {w a b : ZFSet.{u}} (hfa : IsFunc a) {l : List ℕ}
    {xs : List ZFSet.{u}} (hb : IsBlkUpdP w a (seqOfNats.{u} l) (seqOfVals xs) b) :
    IsFunc b := by
  refine ⟨fun p hp => ?_, fun c y y' hy hy' => ?_⟩
  · obtain ⟨k, x, rfl, -⟩ := (hb.2.2.2.2.1 p).mp hp
    exact ⟨_, _, rfl⟩
  · rcases blkUpdP_cases hb hy with ⟨m, hm1, hm2⟩ | ⟨ha1, ha2⟩ | ⟨rfl, hn1, hn2, -⟩ <;>
      rcases blkUpdP_cases hb hy' with ⟨m', hm1', hm2'⟩ | ⟨ha1', ha2'⟩ | ⟨rfl, hn1', hn2', -⟩
    · have hmm : m = m' := hb.nuInj _ _ _ hm1 hm1'
      subst hmm
      exact (isFunc_seqOfVals xs).2 _ _ _ hm2 hm2'
    · exact absurd rfl (ha2' m c hm1)
    · exact absurd rfl (hn2' m c hm1)
    · exact absurd rfl (ha2 m' c hm1')
    · exact hfa.2 _ _ _ ha1 ha1'
    · exact absurd ha1 (hn1' y)
    · exact absurd rfl (hn2 m' c hm1')
    · exact absurd ha1' (hn1 y')
    · rfl

/-- The semantics of any padding block update built from lists. -/
theorem seqVal_of_isBlkUpdP {w A a b : ZFSet.{u}} (hemp : ∅ ∈ A) (ha : IsSeqA ωZ A a)
    {l : List ℕ} (hnd : l.Nodup) {xs : List ZFSet.{u}} (hlen : xs.length = l.length)
    (hb : IsBlkUpdP w a (seqOfNats.{u} l) (seqOfVals xs) b) :
    SeqVal b = updList (SeqVal a) l xs := by
  have hfb := isFunc_of_isBlkUpdP ha.1 hb
  funext k
  by_cases hk : k ∈ l
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hk
    have hjx : j < xs.length := lt_of_lt_of_eq hj hlen.symm
    have hν : ZFSet.pair (natZ.{u} j) (natZ.{u} l[j]) ∈ seqOfNats.{u} l :=
      mem_seqOfNats.mpr (List.getElem?_eq_getElem hj)
    have ht : ZFSet.pair (natZ.{u} j) (xs[j]'hjx) ∈ seqOfVals xs := mem_seqOfVals hjx
    have hmem : ZFSet.pair (natZ.{u} l[j]) (xs[j]'hjx) ∈ b :=
      (hb.2.2.2.2.1 _).mpr ⟨_, _, rfl, Or.inl ⟨_, hν, ht⟩⟩
    rw [seqVal_spec hfb hmem, updList_getElem hnd hlen _ hj]
  · have hnot := notNuVal_of_notMem.{u} (l := l) (k := k) hk
    rw [updList_apply_of_notMem l xs _ k hk]
    by_cases hex : ∃ y, ZFSet.pair (natZ.{u} k) y ∈ a
    · obtain ⟨y, hy⟩ := hex
      have hyb : ZFSet.pair (natZ.{u} k) y ∈ b :=
        (hb.2.2.2.2.1 _).mpr ⟨_, _, rfl, Or.inr (Or.inl ⟨hy, hnot⟩)⟩
      rw [seqVal_spec ha.1 hy, seqVal_spec hfb hyb]
    · have hex' : ∀ y, ZFSet.pair (natZ.{u} k) y ∉ a := fun y hy => hex ⟨y, hy⟩
      rw [seqVal_of_notMem hex']
      by_cases hexb : ∃ y, ZFSet.pair (natZ.{u} k) y ∈ b
      · obtain ⟨y, hy⟩ := hexb
        rcases blkUpdP_cases hb hy with ⟨m, hm1, -⟩ | ⟨h1, -⟩ | ⟨rfl, -, -, -⟩
        · exact absurd rfl (hnot m _ hm1)
        · exact absurd h1 (hex' y)
        · exact seqVal_spec hfb hy
      · exact seqVal_of_notMem (fun y hy => hexb ⟨y, hy⟩)

/-! ### Existence -/

/-- A superset of the intended padding block update, used to build it by separation. -/
noncomputable def blkUpdPSet (a ν t : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep
    (fun p => ∃ k x, p = ZFSet.pair k x ∧
      ((∃ m, ZFSet.pair m k ∈ ν ∧ ZFSet.pair m x ∈ t) ∨
        (p ∈ a ∧ ∀ m k', ZFSet.pair m k' ∈ ν → k' ≠ k) ∨
        (x = ∅ ∧ (∀ y, ZFSet.pair k y ∉ a) ∧
          (∀ m k', ZFSet.pair m k' ∈ ν → k' ≠ k) ∧
          ∃ m c, ZFSet.pair m c ∈ ν ∧ (k ∈ c ∨ k = c))))
    (a ∪ ZFSet.pairSep (fun _ _ => True)
      (ZFSet.sUnion (ZFSet.sUnion ν) ∪ ZFSet.sUnion (ZFSet.sUnion (ZFSet.sUnion ν)))
      (ZFSet.sUnion (ZFSet.sUnion t) ∪ ({∅} : ZFSet.{u})))

theorem isBlkUpdP_blkUpdPSet {w a ν t : ZFSet.{u}} (hν : IsFunc ν) (ht : IsFunc t)
    (h3 : ∀ m x, ZFSet.pair m x ∈ ν → ∃ y, ZFSet.pair m y ∈ t)
    (h4 : ∀ m y, ZFSet.pair m y ∈ t → ∃ x, ZFSet.pair m x ∈ ν)
    (h5 : ∃ n ∈ w, IsDom ν n)
    (h6 : ∀ m m' k, ZFSet.pair m k ∈ ν → ZFSet.pair m' k ∈ ν → m = m') :
    IsBlkUpdP w a ν t (blkUpdPSet a ν t) := by
  refine ⟨hν, ht, h3, h4, fun p => ?_, h5, h6⟩
  rw [blkUpdPSet, ZFSet.mem_sep]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨k, x, rfl, hcase⟩ := h
  rcases hcase with ⟨m, hm1, hm2⟩ | ⟨hpa, -⟩ | ⟨rfl, -, -, m, c, hmc, hle⟩
  · refine ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_pairSep.mpr ⟨k, ?_, x, ?_, rfl, trivial⟩))
    · exact ZFSet.mem_union.mpr (Or.inl (ZFSet.mem_sUnion.mpr ⟨_,
        ZFSet.mem_sUnion.mpr ⟨_, hm1, upair_mem_pair m k⟩, mem_upair_right m k⟩))
    · exact ZFSet.mem_union.mpr (Or.inl (ZFSet.mem_sUnion.mpr ⟨_,
        ZFSet.mem_sUnion.mpr ⟨_, hm2, upair_mem_pair m x⟩, mem_upair_right m x⟩))
  · exact ZFSet.mem_union.mpr (Or.inl hpa)
  · refine ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_pairSep.mpr ⟨k, ?_, ∅, ?_, rfl, trivial⟩))
    · have hc : c ∈ ZFSet.sUnion (ZFSet.sUnion ν) :=
        ZFSet.mem_sUnion.mpr ⟨_, ZFSet.mem_sUnion.mpr ⟨_, hmc, upair_mem_pair m c⟩,
          mem_upair_right m c⟩
      rcases hle with hkc | rfl
      · exact ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_sUnion.mpr ⟨c, hc, hkc⟩))
      · exact ZFSet.mem_union.mpr (Or.inl hc)
    · exact ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_singleton.mpr rfl))

/-- Existence and semantics of the padding block update.  Note that, unlike `exists_blkUpd`,
there is **no** hypothesis saying that the block variables lie in the domain of `a`. -/
theorem exists_blkUpdP {A a : ZFSet.{u}} (hemp : ∅ ∈ A) (ha : IsSeqA ωZ A a)
    (l : List ℕ) (hnd : l.Nodup) (xs : List ZFSet.{u}) (hlen : xs.length = l.length)
    (hxs : ∀ x ∈ xs, x ∈ A) :
    ∃ b, IsBlkUpdP ωZ a (seqOfNats.{u} l) (seqOfVals xs) b ∧ IsSeqA ωZ A b ∧
      SeqVal b = updList (SeqVal a) l xs := by
  have h3 : ∀ m x, ZFSet.pair m x ∈ seqOfNats.{u} l → ∃ y, ZFSet.pair m y ∈ seqOfVals xs := by
    intro m x hmx
    obtain ⟨n, i, hni, e⟩ := mem_seqOfNats_iff.mp hmx
    rw [ZFSet.pair_inj] at e
    obtain ⟨rfl, rfl⟩ := e
    have hn : n < l.length := (List.getElem?_eq_some_iff.mp hni).1
    exact ⟨_, mem_seqOfVals (lt_of_lt_of_eq hn hlen.symm)⟩
  have h4 : ∀ m y, ZFSet.pair m y ∈ seqOfVals xs → ∃ x, ZFSet.pair m x ∈ seqOfNats.{u} l := by
    intro m y hmy
    obtain ⟨n, hn, e⟩ := mem_seqOfVals_iff.mp hmy
    rw [ZFSet.pair_inj] at e
    obtain ⟨rfl, rfl⟩ := e
    have hn' : n < l.length := lt_of_lt_of_eq hn hlen
    exact ⟨natZ (l[n]'hn'), mem_seqOfNats.mpr (List.getElem?_eq_getElem hn')⟩
  have h5 : ∃ n ∈ ωZ.{u}, IsDom (seqOfNats.{u} l) n :=
    ⟨natZ l.length, natZ_mem_ωZ _, by
      simpa [seqOfNats, List.length_map] using isDom_seqOfAux.{u} (l.map natZ.{u})⟩
  have h6 : ∀ m m' k : ZFSet.{u}, ZFSet.pair m k ∈ seqOfNats.{u} l →
      ZFSet.pair m' k ∈ seqOfNats.{u} l → m = m' := fun _ _ _ h h' =>
    seqOfNats_index_inj hnd h h'
  have hbu := isBlkUpdP_blkUpdPSet (w := ωZ.{u}) (a := a) (isFunc_seqOfNats.{u} l)
    (isFunc_seqOfVals xs) h3 h4 h5 h6
  obtain ⟨n, hdom₀⟩ := isSeqA_dom ha
  refine ⟨_, hbu, ⟨isFunc_of_isBlkUpdP ha.1 hbu,
    ⟨natZ (max n (natBound l)), natZ_mem_ωZ _, ?_⟩, ?_⟩,
    seqVal_of_isBlkUpdP hemp ha hnd hlen hbu⟩
  · intro cc
    constructor
    · intro hcc
      obtain ⟨k, hk, rfl⟩ := mem_natZ_iff.mp hcc
      by_cases hkl : k ∈ l
      · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hkl
        have hjx : j < xs.length := lt_of_lt_of_eq hj hlen.symm
        exact ⟨xs[j]'hjx, (hbu.2.2.2.2.1 _).mpr ⟨_, _, rfl,
          Or.inl ⟨natZ j, mem_seqOfNats.mpr (List.getElem?_eq_getElem hj), mem_seqOfVals hjx⟩⟩⟩
      · by_cases hka : ∃ y, ZFSet.pair (natZ.{u} k) y ∈ a
        · obtain ⟨y, hy⟩ := hka
          exact ⟨y, (hbu.2.2.2.2.1 _).mpr
            ⟨_, _, rfl, Or.inr (Or.inl ⟨hy, notNuVal_of_notMem.{u} hkl⟩)⟩⟩
        · have hka' : ∀ y, ZFSet.pair (natZ.{u} k) y ∉ a := fun y hy => hka ⟨y, hy⟩
          have hkn : n ≤ k := by
            by_contra hcon
            obtain ⟨y, hy⟩ := (hdom₀ (natZ k)).mp (natZ_mem_natZ_iff.mpr (by omega))
            exact hka ⟨y, hy⟩
          have hkb : k < natBound l := by omega
          obtain ⟨i, hi, hki⟩ := lt_natBound_iff.mp hkb
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hi
          refine ⟨∅, (hbu.2.2.2.2.1 _).mpr ⟨_, _, rfl, Or.inr (Or.inr
            ⟨rfl, hka', notNuVal_of_notMem.{u} hkl, natZ j, natZ (l[j]'hj),
              mem_seqOfNats.mpr (List.getElem?_eq_getElem hj), ?_⟩)⟩⟩
          rcases Nat.lt_or_ge k (l[j]'hj) with hlt | hge
          · exact Or.inl (natZ_mem_natZ_iff.mpr hlt)
          · exact Or.inr (by rw [show k = l[j]'hj by omega])
    · rintro ⟨y, hy⟩
      rcases blkUpdP_cases hbu hy with ⟨m, hm1, -⟩ | ⟨h1, -⟩ | ⟨-, -, -, m, c, hmc, hle⟩
      · obtain ⟨i, hi, rfl⟩ := seqOfNats_val hm1
        have hib : i < natBound l := lt_natBound_iff.mpr ⟨i, hi, le_refl i⟩
        exact natZ_mem_natZ_iff.mpr (by omega)
      · obtain ⟨k, hk, rfl⟩ := mem_natZ_iff.mp ((hdom₀ _).mpr ⟨y, h1⟩)
        exact natZ_mem_natZ_iff.mpr (by omega)
      · obtain ⟨i, hi, rfl⟩ := seqOfNats_val hmc
        have hib : i < natBound l := lt_natBound_iff.mpr ⟨i, hi, le_refl i⟩
        rcases hle with hin | rfl
        · obtain ⟨k, hk, rfl⟩ := mem_natZ_iff.mp hin
          exact natZ_mem_natZ_iff.mpr (by omega)
        · exact natZ_mem_natZ_iff.mpr (by omega)
  · intro cc x hcx
    rcases blkUpdP_cases hbu hcx with ⟨m, -, hm2⟩ | ⟨h1, -⟩ | ⟨rfl, -, -, -⟩
    · obtain ⟨j, hj, e⟩ := mem_seqOfVals_iff.mp hm2
      rw [ZFSet.pair_inj] at e
      rw [e.2]
      exact hxs _ (List.mem_iff_getElem.mpr ⟨j, hj, rfl⟩)
    · exact ha.2.2 _ _ h1
    · exact hemp

/-! ### Δ₀-definability -/

/-- `v kk` is not a value of the function `v nu`. -/
theorem delta0_notNuVal (nu kk : ℕ) :
    Delta0Def {nu, kk} (fun _ v => ∀ m k', ZFSet.pair m k' ∈ v nu → k' ≠ v kk) := by
  set d := nu + kk + 1 with hd
  have n1 := (delta0_isKPair d (d + 2) (d + 4) (by omega) (by omega)).imp
    (Delta0Def.eq (d + 4) kk).not
  have n2 := n1.ball (d + 4) (d + 3) (by omega)
  have n3 := n2.ball (d + 3) d (by omega)
  have n4 := n3.ball (d + 2) (d + 1) (by omega)
  have n5 := n4.ball (d + 1) d (by omega)
  have n6 := n5.ball d nu (by omega)
  refine (n6.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · intro H m k' hmk'
      exact H _ hmk' _ (singleton_mem_pair m k') m (ZFSet.mem_singleton.mpr rfl) _
        (upair_mem_pair m k') k' (mem_upair_right m k') rfl
    · intro H p hp q _ m _ q' _ k' _ hpe
      subst hpe
      exact H m k' hp
  · ext j; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- `v kk` is not in the domain of `v a`. -/
theorem delta0_notInDomA (a kk : ℕ) :
    Delta0Def {a, kk} (fun _ v => ∀ y, ZFSet.pair (v kk) y ∉ v a) := by
  set d := a + kk + 1 with hd
  have n1 := (delta0_isKPair d kk (d + 2) (by omega) (by omega)).not
  have n2 := n1.ball (d + 2) (d + 1) (by omega)
  have n3 := n2.ball (d + 1) d (by omega)
  have n4 := n3.ball d a (by omega)
  refine (n4.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · intro H y hy
      exact H _ hy _ (upair_mem_pair (v kk) y) y (mem_upair_right (v kk) y) rfl
    · intro H p hp q _ y _ hpe
      subst hpe
      exact H y hp
  · ext j; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]; omega

/-- `v kk` is dominated by some value of the function `v nu`. -/
theorem delta0_leNuVal (nu kk : ℕ) :
    Delta0Def {nu, kk} (fun _ v => ∃ m c, ZFSet.pair m c ∈ v nu ∧ (v kk ∈ c ∨ v kk = c)) := by
  set d := nu + kk + 1 with hd
  have e1 := (delta0_isKPair d (d + 2) (d + 4) (by omega) (by omega)).and
    ((Delta0Def.mem kk (d + 4)).or (Delta0Def.eq kk (d + 4)))
  have e2 := e1.bex (d + 4) (d + 3) (by omega)
  have e3 := e2.bex (d + 3) d (by omega)
  have e4 := e3.bex (d + 2) (d + 1) (by omega)
  have e5 := e4.bex (d + 1) d (by omega)
  have e6 := e5.bex d nu (by omega)
  refine (e6.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · rintro ⟨p, hp, q, -, m, -, q', -, c, -, hpe, hle⟩
      subst hpe
      exact ⟨m, c, hp, hle⟩
    · rintro ⟨m, c, hmc, hle⟩
      exact ⟨_, hmc, _, singleton_mem_pair m c, m, ZFSet.mem_singleton.mpr rfl, _,
        upair_mem_pair m c, c, mem_upair_right m c, rfl, hle⟩
  · ext j; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- `⟨v kk, ∅⟩ ∈ v b`. -/
theorem delta0_emptyPairMem (b kk : ℕ) :
    Delta0Def {b, kk} (fun _ v => ZFSet.pair (v kk) ∅ ∈ v b) := by
  set d := b + kk + 1 with hd
  have w1 := (delta0_isEmpty (d + 2)).and (delta0_isKPair d kk (d + 2) (by omega) (by omega))
  have w2 := w1.bex (d + 2) (d + 1) (by omega)
  have w3 := w2.bex (d + 1) d (by omega)
  have w4 := w3.bex d b (by omega)
  refine (w4.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · rintro ⟨p, hp, q, -, e, -, rfl, hpe⟩
      subst hpe
      exact hp
    · intro H
      exact ⟨_, H, _, upair_mem_pair (v kk) ∅, ∅, mem_upair_right (v kk) ∅, rfl, rfl⟩
  · ext j; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- The `ν`-branch: `v kk` is the `ν`-value and `v xx` the `t`-value at a common index. -/
theorem delta0_nuMatch (nu t kk xx : ℕ) (hnk : nu ≠ kk) (htx : t ≠ xx) :
    Delta0Def {nu, t, kk, xx}
      (fun _ v => ∃ m, ZFSet.pair m (v kk) ∈ v nu ∧ ZFSet.pair m (v xx) ∈ v t) := by
  set d := nu + t + kk + xx + 1 with hd
  have f1 := (delta0_funVal nu (d + 2) kk (by omega) hnk (by omega)).and
    (delta0_funVal t (d + 2) xx (by omega) htx (by omega))
  have f2 := f1.bex (d + 2) (d + 1) (by omega)
  have f3 := f2.bex (d + 1) d (by omega)
  have f4 := f3.bex d nu (by omega)
  refine (f4.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · rintro ⟨p, -, q, -, m, -, hm1, hm2⟩
      exact ⟨m, hm1, hm2⟩
    · rintro ⟨m, hm1, hm2⟩
      exact ⟨_, hm1, _, singleton_mem_pair m (v kk), m, ZFSet.mem_singleton.mpr rfl, hm1, hm2⟩
  · ext j; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- Members of the padding block update satisfy the defining condition. -/
theorem delta0_blkMemP (a nu t b : ℕ) (han : a ≠ nu) (hat : a ≠ t) (hab : a ≠ b)
    (hnt : nu ≠ t) (hnb : nu ≠ b) (htb : t ≠ b) :
    Delta0Def {a, nu, t, b} (fun _ v => ∀ p ∈ v b, ∃ k x, p = ZFSet.pair k x ∧
      ((∃ m, ZFSet.pair m k ∈ v nu ∧ ZFSet.pair m x ∈ v t) ∨
        (p ∈ v a ∧ ∀ m k', ZFSet.pair m k' ∈ v nu → k' ≠ k) ∨
        (x = ∅ ∧ (∀ y, ZFSet.pair k y ∉ v a) ∧
          (∀ m k', ZFSet.pair m k' ∈ v nu → k' ≠ k) ∧
          ∃ m c, ZFSet.pair m c ∈ v nu ∧ (k ∈ c ∨ k = c)))) := by
  set c := a + nu + t + b + 1 with hc
  have br1 := delta0_nuMatch nu t (c + 2) (c + 4) (by omega) (by omega)
  have br2 := (Delta0Def.mem c a).and (delta0_notNuVal nu (c + 2))
  have br3 := (delta0_isEmpty (c + 4)).and
    ((delta0_notInDomA a (c + 2)).and
      ((delta0_notNuVal nu (c + 2)).and (delta0_leNuVal nu (c + 2))))
  have g1 := (delta0_isKPair c (c + 2) (c + 4) (by omega) (by omega)).and
    (br1.or (br2.or br3))
  have g2 := g1.bex (c + 4) (c + 3) (by omega)
  have g3 := g2.bex (c + 3) c (by omega)
  have g4 := g3.bex (c + 2) (c + 1) (by omega)
  have g5 := g4.bex (c + 1) c (by omega)
  have h := g5.ball c b (by omega)
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · intro H p hp
      obtain ⟨q, -, k, -, q', -, x, -, hpx, hcase⟩ := H p hp
      exact ⟨k, x, hpx, hcase⟩
    · intro H p hp
      obtain ⟨k, x, rfl, hcase⟩ := H p hp
      exact ⟨_, singleton_mem_pair k x, k, ZFSet.mem_singleton.mpr rfl, _, upair_mem_pair k x,
        x, mem_upair_right k x, rfl, hcase⟩
  · ext j; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- The padding branch of the defining condition of the padding block update. -/
theorem delta0_blkMemPad (a nu b : ℕ) (han : a ≠ nu) (hab : a ≠ b) (hnb : nu ≠ b) :
    Delta0Def {a, nu, b} (fun _ v => ∀ m c, ZFSet.pair m c ∈ v nu → ∀ k, (k ∈ c ∨ k = c) →
      (∀ y, ZFSet.pair k y ∉ v a) → (∀ m' k', ZFSet.pair m' k' ∈ v nu → k' ≠ k) →
      ZFSet.pair k ∅ ∈ v b) := by
  set c := a + nu + b + 1 with hc
  have condA := ((delta0_notInDomA a (c + 5)).and
    (delta0_notNuVal nu (c + 5))).imp (delta0_emptyPairMem b (c + 5))
  have s1 := condA.ball (c + 5) (c + 4) (by omega)
  have condB := ((delta0_notInDomA a (c + 4)).and
    (delta0_notNuVal nu (c + 4))).imp (delta0_emptyPairMem b (c + 4))
  have s2 := (delta0_isKPair c (c + 2) (c + 4) (by omega) (by omega)).imp (s1.and condB)
  have s3 := s2.ball (c + 4) (c + 3) (by omega)
  have s4 := s3.ball (c + 3) c (by omega)
  have s5 := s4.ball (c + 2) (c + 1) (by omega)
  have s6 := s5.ball (c + 1) c (by omega)
  have s7 := s6.ball c nu (by omega)
  refine (s7.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · intro H m cc hmc k hk hnd hnn
      have H2 := H _ hmc _ (singleton_mem_pair m cc) m (ZFSet.mem_singleton.mpr rfl) _
        (upair_mem_pair m cc) cc (mem_upair_right m cc) rfl
      rcases hk with hk | rfl
      · exact H2.1 k hk ⟨hnd, hnn⟩
      · exact H2.2 ⟨hnd, hnn⟩
    · intro H p hp q _ m _ q' _ cc _ hpe
      subst hpe
      exact ⟨fun k _ hk => H m cc hp k (Or.inl ‹k ∈ cc›) hk.1 hk.2,
        fun hk => H m cc hp cc (Or.inr rfl) hk.1 hk.2⟩
  · ext j; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- The values of the function `v nu` are pairwise distinct (Definition 12.1: `ν` lists
*pairwise distinct* variable numbers). -/
theorem delta0_nuInj (nu : ℕ) :
    Delta0Def {nu} (fun _ v => ∀ m m' k, ZFSet.pair m k ∈ v nu → ZFSet.pair m' k ∈ v nu →
      m = m') := by
  set d := nu + 1 with hd
  have b0 := (delta0_funVal nu (d + 7) (d + 4) (by omega) (by omega) (by omega)).imp
    (Delta0Def.eq (d + 2) (d + 7))
  have b1 := b0.ball (d + 7) (d + 6) (by omega)
  have b2 := b1.ball (d + 6) (d + 5) (by omega)
  have b3 := b2.ball (d + 5) nu (by omega)
  have a1 := delta0_isKPair d (d + 2) (d + 4) (by omega) (by omega)
  have b4 := a1.imp b3
  have b5 := b4.ball (d + 4) (d + 3) (by omega)
  have b6 := b5.ball (d + 3) d (by omega)
  have b7 := b6.ball (d + 2) (d + 1) (by omega)
  have b8 := b7.ball (d + 1) d (by omega)
  have h := b8.ball d nu (by omega)
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · intro H m m' k hmk hm'k
      exact H _ hmk _ (singleton_mem_pair m k) m (ZFSet.mem_singleton.mpr rfl) _
        (upair_mem_pair m k) k (mem_upair_right m k) rfl _ hm'k _ (singleton_mem_pair m' k)
        m' (ZFSet.mem_singleton.mpr rfl) hm'k
    · intro H p hp q _ m _ q' _ k _ hpe p2 _ q2 _ m' _ hm'k
      subst hpe
      exact H m m' k hp hm'k
  · ext j; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- Δ₀-definability of the padding block update. -/
theorem delta0_isBlkUpdP (w a nu t b : ℕ) (hwa : w ≠ a) (hwn : w ≠ nu) (hwt : w ≠ t)
    (hwb : w ≠ b) (han : a ≠ nu) (hat : a ≠ t) (hab : a ≠ b)
    (hnt : nu ≠ t) (hnb : nu ≠ b) (htb : t ≠ b) :
    Delta0Def {w, a, nu, t, b} (fun _ v => IsBlkUpdP (v w) (v a) (v nu) (v t) (v b)) := by
  set m := w + a + nu + t + b + 1 with hm
  have h1 := delta0_isFunc nu
  have h2 := delta0_isFunc t
  have h3 := delta0_domSub nu t hnt
  have h4 := delta0_domSub t nu hnt.symm
  have h5 := delta0_blkMemP a nu t b han hat hab hnt hnb htb
  have h6 := delta0_blkMemA a nu b han hab hnb
  have h7 := delta0_blkMemNu nu t b hnt hnb htb
  have h8 := delta0_blkMemPad a nu b han hab hnb
  have h9 := (delta0_isDom nu m (by omega)).bex m w (by omega)
  have h10 := delta0_nuInj nu
  refine (((((h1.and h2).and (h3.and h4)).and (((h5.and h6).and h7).and h8)).and
    (h9.and h10)).congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    unfold IsBlkUpdP
    constructor
    · rintro ⟨⟨⟨⟨hf1, hf2⟩, hc3, hc4⟩, ⟨⟨hmem, hA⟩, hNu⟩, hPad⟩, hSeq, hInj⟩
      refine ⟨hf1, hf2, hc3, hc4, fun p => ⟨hmem p, ?_⟩, hSeq, hInj⟩
      rintro ⟨k, x, rfl, hcase⟩
      rcases hcase with ⟨mm, hmk, hmx⟩ | ⟨hpa, hnot⟩ | ⟨rfl, hnd, hnot, mm, cc, hmc, hle⟩
      · exact hNu mm k hmk x hmx
      · exact hA _ hpa ⟨k, x, rfl, hnot⟩
      · exact hPad mm cc hmc k hle hnd hnot
    · rintro ⟨hf1, hf2, hc3, hc4, hall, hSeq, hInj⟩
      refine ⟨⟨⟨⟨hf1, hf2⟩, hc3, hc4⟩, ⟨⟨fun p hp => (hall p).mp hp, ?_⟩, ?_⟩, ?_⟩, hSeq, hInj⟩
      · intro p hpa hex
        obtain ⟨k, x, hpx, hnot⟩ := hex
        exact (hall p).mpr ⟨k, x, hpx, Or.inr (Or.inl ⟨hpa, hnot⟩)⟩
      · intro mm k hmk x hmx
        exact (hall _).mpr ⟨k, x, rfl, Or.inl ⟨mm, hmk, hmx⟩⟩
      · intro mm cc hmc k hle hnd hnot
        exact (hall _).mpr ⟨k, ∅, rfl, Or.inr (Or.inr ⟨rfl, hnd, hnot, mm, cc, hmc, hle⟩)⟩
  · ext j; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

end BM4.ST
