/-
  Part III (§12–13 preparation): simultaneous updates of an assignment along a block of
  variables (`BlkUpd` of the paper), and the bridge between block quantification in `Fm`
  and the `ExsD` / `AllD` operators.
-/
import Bm4.SetTheory.SatCode
import Bm4.SetTheory.Recur
import Bm4.SetTheory.BFCode

universe u

namespace BM4.ST

open Fm

/-- Universal block quantification (the dual of `ExsD`). -/
def AllD (D : ZFSet.{u} → Prop) : List ℕ → ((ℕ → ZFSet.{u}) → Prop) → (ℕ → ZFSet.{u}) → Prop
  | [], P, v => P v
  | i :: l, P, v => ∀ y, D y → AllD D l P (Function.update v i y)

/-- Block existential quantification in `Fm` is `ExsD`. -/
theorem sat_exs_iff_exsD (D : ZFSet.{u} → Prop) (φ : Fm) :
    ∀ (l : List ℕ) (v : ℕ → ZFSet.{u}), Sat D v (Fm.exs l φ) ↔ ExsD D l (fun w => Sat D w φ) v
  | [], v => Iff.rfl
  | i :: l, v => by
    simp only [Fm.exs_cons, sat_ex, ExsD]
    exact exists_congr fun y => and_congr_right fun _ => sat_exs_iff_exsD D φ l _

/-- Block universal quantification in `Fm` is `AllD`. -/
theorem sat_alls_iff_allD (D : ZFSet.{u} → Prop) (φ : Fm) :
    ∀ (l : List ℕ) (v : ℕ → ZFSet.{u}), Sat D v (Fm.alls l φ) ↔ AllD D l (fun w => Sat D w φ) v
  | [], v => Iff.rfl
  | i :: l, v => by
    simp only [Fm.alls_cons, sat_all, AllD]
    exact forall_congr' fun y => imp_congr_right fun _ => sat_alls_iff_allD D φ l _

theorem allD_congr {D : ZFSet.{u} → Prop} {P Q : (ℕ → ZFSet.{u}) → Prop} (h : ∀ v, P v ↔ Q v) :
    ∀ (l : List ℕ) (v : ℕ → ZFSet.{u}), AllD D l P v ↔ AllD D l Q v
  | [], v => h v
  | i :: l, v => by
    simp only [AllD]
    exact forall_congr' fun y => imp_congr_right fun _ => allD_congr h l _

/-! ### Simultaneous updates along a block -/

/-- `IsBlkUpd a ν t b`: `b` is the assignment `a` updated at the variables listed by the finite
sequence `ν` with the corresponding values of the finite sequence `t`. Both `ν` and `t` are
function-sets with the same domain, a natural number. -/
def IsBlkUpd (a ν t b : ZFSet.{u}) : Prop :=
  IsFunc ν ∧ IsFunc t ∧
    (∀ m x, ZFSet.pair m x ∈ ν → ∃ y, ZFSet.pair m y ∈ t) ∧
    (∀ m y, ZFSet.pair m y ∈ t → ∃ x, ZFSet.pair m x ∈ ν) ∧
    ∀ p, p ∈ b ↔ (∃ k x, p = ZFSet.pair k x ∧
      ((∃ m, ZFSet.pair m k ∈ ν ∧ ZFSet.pair m x ∈ t) ∨
        (p ∈ a ∧ ∀ m k', ZFSet.pair m k' ∈ ν → k' ≠ k)))

/-- Blocks whose variable list has no repetitions give a well-defined update. -/
theorem isBlkUpd_unique {a ν t b b' : ZFSet.{u}} (h : IsBlkUpd a ν t b) (h' : IsBlkUpd a ν t b') :
    b = b' := by
  ext p
  rw [h.2.2.2.2 p, h'.2.2.2.2 p]

/-- The block update, applied to the finite list of variables `l` and values `xs`. -/
theorem blkUpd_seqVal {a ν t b : ZFSet.{u}} (hb : IsBlkUpd a ν t b) {k : ℕ} {x : ZFSet.{u}}
    (hx : ZFSet.pair (natZ k) x ∈ b) :
    (∃ m, ZFSet.pair m (natZ.{u} k) ∈ ν ∧ ZFSet.pair m x ∈ t) ∨
      (ZFSet.pair (natZ k) x ∈ a ∧ ∀ m k', ZFSet.pair m k' ∈ ν → k' ≠ natZ.{u} k) := by
  obtain ⟨k', x', hp, hcase⟩ := (hb.2.2.2.2 _).mp hx
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective hp
  exact hcase

/-! ### Successive updates along a list of variables -/

/-- Successive updates of a valuation along a list of variables. -/
def updList : (ℕ → ZFSet.{u}) → List ℕ → List ZFSet.{u} → (ℕ → ZFSet.{u})
  | v, i :: l, x :: xs => updList (Function.update v i x) l xs
  | v, _, _ => v

@[simp] theorem updList_nil_left (v : ℕ → ZFSet.{u}) (xs : List ZFSet.{u}) :
    updList v [] xs = v := by cases xs <;> rfl

@[simp] theorem updList_nil_right (v : ℕ → ZFSet.{u}) (l : List ℕ) :
    updList v l [] = v := by cases l <;> rfl

@[simp] theorem updList_cons (v : ℕ → ZFSet.{u}) (i : ℕ) (l : List ℕ) (x : ZFSet.{u})
    (xs : List ZFSet.{u}) :
    updList v (i :: l) (x :: xs) = updList (Function.update v i x) l xs := rfl

/-- Variables outside the block keep their value. -/
theorem updList_apply_of_notMem :
    ∀ (l : List ℕ) (xs : List ZFSet.{u}) (v : ℕ → ZFSet.{u}) (k : ℕ), k ∉ l →
      updList v l xs k = v k
  | [], xs, v, k, _ => by simp
  | i :: l, [], v, k, _ => by simp
  | i :: l, x :: xs, v, k, hk => by
    rw [updList_cons, updList_apply_of_notMem l xs _ k (fun h => hk (List.mem_cons_of_mem _ h)),
      Function.update_of_ne (fun h => hk (by simp [h]))]

/-- Variables in the block take the corresponding value (`l` has no repetitions). -/
theorem updList_apply_of_mem :
    ∀ (l : List ℕ), l.Nodup → ∀ (xs : List ZFSet.{u}) (v : ℕ → ZFSet.{u}) (j k : ℕ)
      (x : ZFSet.{u}), l[j]? = some k → xs[j]? = some x → updList v l xs k = x
  | [], _, _, _, _, _, _, hk, _ => by simp at hk
  | _ :: _, _, [], _, _, _, _, _, hx => by simp at hx
  | i :: l, hnd, y :: xs, v, j, k, x, hk, hx => by
    rw [List.nodup_cons] at hnd
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk hx
      subst hk; subst hx
      rw [updList_cons, updList_apply_of_notMem l xs _ i hnd.1, Function.update_self]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hk hx
      rw [updList_cons]
      exact updList_apply_of_mem l hnd.2 xs _ j k x hk hx

theorem updList_getElem {l : List ℕ} (hnd : l.Nodup) {xs : List ZFSet.{u}}
    (hlen : xs.length = l.length) (v : ℕ → ZFSet.{u}) {j : ℕ} (hj : j < l.length) :
    updList v l xs l[j] = xs[j]'(lt_of_lt_of_eq hj hlen.symm) :=
  updList_apply_of_mem l hnd xs v j _ _ (List.getElem?_eq_getElem hj)
    (List.getElem?_eq_getElem (lt_of_lt_of_eq hj hlen.symm))

/-! ### Blocks of witnesses as lists -/

/-- `ExsD` in terms of a list of witnesses. -/
theorem exsD_iff_exists_list {D : ZFSet.{u} → Prop} {P : (ℕ → ZFSet.{u}) → Prop} :
    ∀ (l : List ℕ) (v : ℕ → ZFSet.{u}),
      ExsD D l P v ↔ ∃ xs : List ZFSet.{u}, xs.length = l.length ∧ (∀ x ∈ xs, D x) ∧
        P (updList v l xs)
  | [], v => by
    simp only [ExsD]
    constructor
    · intro h; exact ⟨[], rfl, by simp, by simpa using h⟩
    · rintro ⟨xs, hlen, _, h⟩; simpa using h
  | i :: l, v => by
    simp only [ExsD]
    constructor
    · rintro ⟨y, hy, h⟩
      obtain ⟨xs, hlen, hxs, hP⟩ := (exsD_iff_exists_list l _).mp h
      refine ⟨y :: xs, by simp [hlen], ?_, hP⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hy
      · exact hxs z hz
    · rintro ⟨xs, hlen, hxs, hP⟩
      cases xs with
      | nil => simp at hlen
      | cons y ys =>
        refine ⟨y, hxs y (by simp), (exsD_iff_exists_list l _).mpr ⟨ys, by simpa using hlen, ?_, hP⟩⟩
        intro z hz; exact hxs z (List.mem_cons_of_mem _ hz)

/-- `AllD` in terms of a list of values. -/
theorem allD_iff_forall_list {D : ZFSet.{u} → Prop} {P : (ℕ → ZFSet.{u}) → Prop} :
    ∀ (l : List ℕ) (v : ℕ → ZFSet.{u}),
      AllD D l P v ↔ ∀ xs : List ZFSet.{u}, xs.length = l.length → (∀ x ∈ xs, D x) →
        P (updList v l xs)
  | [], v => by
    simp only [AllD]
    constructor
    · intro h xs hlen _; simpa using h
    · intro h; simpa using h [] rfl (by simp)
  | i :: l, v => by
    simp only [AllD]
    constructor
    · intro H xs hlen hxs
      cases xs with
      | nil => simp at hlen
      | cons y ys =>
        exact (allD_iff_forall_list l _).mp (H y (hxs y (by simp))) ys (by simpa using hlen)
          (fun z hz => hxs z (List.mem_cons_of_mem _ hz))
    · intro H y hy
      refine (allD_iff_forall_list l _).mpr ?_
      intro ys hlen hys
      refine H (y :: ys) (by simp [hlen]) ?_
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hy
      · exact hys z hz

/-! ### The sequence-set of a list of values -/

/-- The sequence-set of a list of values (companion of `seqOfNats`). -/
noncomputable def seqOfVals (xs : List ZFSet.{u}) : ZFSet.{u} := seqOfAux 0 xs

theorem mem_seqOfVals_iff {xs : List ZFSet.{u}} {p : ZFSet.{u}} :
    p ∈ seqOfVals xs ↔ ∃ k, ∃ h : k < xs.length, p = ZFSet.pair (natZ k) xs[k] := by
  rw [seqOfVals, mem_seqOfAux]
  constructor
  · rintro ⟨n, x, hx, rfl⟩
    obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp hx
    exact ⟨n, h, by rw [Nat.zero_add]⟩
  · rintro ⟨k, h, rfl⟩
    exact ⟨k, xs[k], List.getElem?_eq_getElem h, by rw [Nat.zero_add]⟩

theorem mem_seqOfVals {xs : List ZFSet.{u}} {k : ℕ} (h : k < xs.length) :
    ZFSet.pair (natZ.{u} k) xs[k] ∈ seqOfVals xs :=
  mem_seqOfVals_iff.mpr ⟨k, h, rfl⟩

theorem isFunc_seqOfVals (xs : List ZFSet.{u}) : IsFunc (seqOfVals xs) := by
  refine ⟨fun p hp => ?_, fun c y y' hy hy' => ?_⟩
  · obtain ⟨k, _, rfl⟩ := mem_seqOfVals_iff.mp hp
    exact ⟨_, _, rfl⟩
  · obtain ⟨k, hk, h1⟩ := mem_seqOfVals_iff.mp hy
    obtain ⟨k', hk', h2⟩ := mem_seqOfVals_iff.mp hy'
    rw [ZFSet.pair_inj] at h1 h2
    obtain ⟨hc, rfl⟩ := h1
    obtain ⟨hc', rfl⟩ := h2
    have : k = k' := natZ_injective (hc ▸ hc')
    subst this
    rfl

theorem isFunc_seqOfNats (l : List ℕ) : IsFunc (seqOfNats.{u} l) := by
  refine ⟨fun p hp => ?_, fun c y y' hy hy' => ?_⟩
  · obtain ⟨n, i, _, rfl⟩ := mem_seqOfNats_iff.mp hp
    exact ⟨_, _, rfl⟩
  · obtain ⟨n, i, hni, h1⟩ := mem_seqOfNats_iff.mp hy
    obtain ⟨n', i', hni', h2⟩ := mem_seqOfNats_iff.mp hy'
    rw [ZFSet.pair_inj] at h1 h2
    obtain ⟨hc, rfl⟩ := h1
    obtain ⟨hc', rfl⟩ := h2
    have hnn : n = n' := natZ_injective (hc ▸ hc')
    subst hnn
    rw [hni] at hni'
    rw [Option.some.inj hni']

/-! ### Existence and semantics of the block update -/

/-- The two cases of a member of a block update, for an explicit pair. -/
theorem blkUpd_cases {a ν t b : ZFSet.{u}} (hb : IsBlkUpd a ν t b) {k x : ZFSet.{u}}
    (hx : ZFSet.pair k x ∈ b) :
    (∃ m, ZFSet.pair m k ∈ ν ∧ ZFSet.pair m x ∈ t) ∨
      (ZFSet.pair k x ∈ a ∧ ∀ m k', ZFSet.pair m k' ∈ ν → k' ≠ k) := by
  obtain ⟨k', x', hp, hcase⟩ := (hb.2.2.2.2 _).mp hx
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective hp
  exact hcase

/-- A list without repetitions gives an injective sequence of variables. -/
theorem seqOfNats_index_inj {l : List ℕ} (hnd : l.Nodup) {m m' k : ZFSet.{u}}
    (h : ZFSet.pair m k ∈ seqOfNats.{u} l) (h' : ZFSet.pair m' k ∈ seqOfNats.{u} l) : m = m' := by
  obtain ⟨n, i, hni, e1⟩ := mem_seqOfNats_iff.mp h
  obtain ⟨n', i', hni', e2⟩ := mem_seqOfNats_iff.mp h'
  rw [ZFSet.pair_inj] at e1 e2
  obtain ⟨rfl, rfl⟩ := e1
  obtain ⟨rfl, hk'⟩ := e2
  have hii : i = i' := natZ_injective hk'
  subst hii
  obtain ⟨hn, hg⟩ := List.getElem?_eq_some_iff.mp hni
  obtain ⟨hn', hg'⟩ := List.getElem?_eq_some_iff.mp hni'
  have : n = n' := hnd.getElem_inj_iff.mp (by rw [hg, hg'])
  rw [this]

/-- Values of the sequence of variables are the entries of the list. -/
theorem seqOfNats_val {l : List ℕ} {m c : ZFSet.{u}} (h : ZFSet.pair m c ∈ seqOfNats.{u} l) :
    ∃ i ∈ l, c = natZ.{u} i := by
  obtain ⟨n, i, hni, e⟩ := mem_seqOfNats_iff.mp h
  rw [ZFSet.pair_inj] at e
  obtain ⟨hn, hg⟩ := List.getElem?_eq_some_iff.mp hni
  exact ⟨i, List.mem_iff_getElem.mpr ⟨n, hn, hg⟩, e.2⟩

theorem isFunc_of_isBlkUpd {a b : ZFSet.{u}} (hfa : IsFunc a) {l : List ℕ} (hnd : l.Nodup)
    {xs : List ZFSet.{u}} (hb : IsBlkUpd a (seqOfNats.{u} l) (seqOfVals xs) b) : IsFunc b := by
  refine ⟨fun p hp => ?_, fun c y y' hy hy' => ?_⟩
  · obtain ⟨k, x, rfl, _⟩ := (hb.2.2.2.2 p).mp hp
    exact ⟨_, _, rfl⟩
  · rcases blkUpd_cases hb hy with ⟨m, hm1, hm2⟩ | ⟨ha1, ha2⟩ <;>
      rcases blkUpd_cases hb hy' with ⟨m', hm1', hm2'⟩ | ⟨ha1', ha2'⟩
    · have hmm : m = m' := seqOfNats_index_inj hnd hm1 hm1'
      subst hmm
      exact (isFunc_seqOfVals xs).2 _ _ _ hm2 hm2'
    · exact absurd rfl (ha2' m c hm1)
    · exact absurd rfl (ha2 m' c hm1')
    · exact hfa.2 _ _ _ ha1 ha1'

/-- Conversely, any block update by sequences coming from lists has the same semantics. -/
theorem seqVal_of_isBlkUpd {A a b : ZFSet.{u}} (ha : IsSeqA ωZ A a)
    {l : List ℕ} (hnd : l.Nodup) {xs : List ZFSet.{u}} (hlen : xs.length = l.length)
    (hb : IsBlkUpd a (seqOfNats.{u} l) (seqOfVals xs) b) :
    SeqVal b = updList (SeqVal a) l xs := by
  have hfb := isFunc_of_isBlkUpd ha.1 hnd hb
  funext k
  by_cases hk : k ∈ l
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hk
    have hjx : j < xs.length := lt_of_lt_of_eq hj hlen.symm
    have hν : ZFSet.pair (natZ.{u} j) (natZ.{u} l[j]) ∈ seqOfNats.{u} l :=
      mem_seqOfNats.mpr (List.getElem?_eq_getElem hj)
    have ht : ZFSet.pair (natZ.{u} j) (xs[j]'hjx) ∈ seqOfVals xs := mem_seqOfVals hjx
    have hmem : ZFSet.pair (natZ.{u} l[j]) (xs[j]'hjx) ∈ b :=
      (hb.2.2.2.2 _).mpr ⟨_, _, rfl, Or.inl ⟨_, hν, ht⟩⟩
    rw [seqVal_spec hfb hmem, updList_getElem hnd hlen _ hj]
  · have hnot : ∀ m k', ZFSet.pair m k' ∈ seqOfNats.{u} l → k' ≠ natZ.{u} k := by
      intro m k' hmk' hcon
      obtain ⟨i, hi, rfl⟩ := seqOfNats_val hmk'
      exact hk (natZ_injective hcon ▸ hi)
    have hiff : ∀ y, ZFSet.pair (natZ.{u} k) y ∈ b ↔ ZFSet.pair (natZ.{u} k) y ∈ a := by
      intro y
      constructor
      · intro h
        rcases blkUpd_cases hb h with ⟨m, hm1, _⟩ | ⟨h1, _⟩
        · exact absurd rfl (hnot m _ hm1)
        · exact h1
      · intro h
        exact (hb.2.2.2.2 _).mpr ⟨_, _, rfl, Or.inr ⟨h, hnot⟩⟩
    rw [updList_apply_of_notMem l xs _ k hk]
    by_cases hex : ∃ y, ZFSet.pair (natZ.{u} k) y ∈ a
    · obtain ⟨y, hy⟩ := hex
      rw [seqVal_spec ha.1 hy, seqVal_spec hfb ((hiff y).mpr hy)]
    · push Not at hex
      rw [seqVal_of_notMem hex, seqVal_of_notMem (fun y hy => hex y ((hiff y).mp hy))]

/-- A superset of the intended block update, used to build it by separation. -/
noncomputable def blkUpdSet (a ν t : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep
    (fun p => ∃ k x, p = ZFSet.pair k x ∧
      ((∃ m, ZFSet.pair m k ∈ ν ∧ ZFSet.pair m x ∈ t) ∨
        (p ∈ a ∧ ∀ m k', ZFSet.pair m k' ∈ ν → k' ≠ k)))
    (a ∪ ZFSet.pairSep (fun _ _ => True) (ZFSet.sUnion (ZFSet.sUnion ν))
      (ZFSet.sUnion (ZFSet.sUnion t)))

theorem isBlkUpd_blkUpdSet {a ν t : ZFSet.{u}} (hν : IsFunc ν) (ht : IsFunc t)
    (h3 : ∀ m x, ZFSet.pair m x ∈ ν → ∃ y, ZFSet.pair m y ∈ t)
    (h4 : ∀ m y, ZFSet.pair m y ∈ t → ∃ x, ZFSet.pair m x ∈ ν) :
    IsBlkUpd a ν t (blkUpdSet a ν t) := by
  refine ⟨hν, ht, h3, h4, fun p => ?_⟩
  rw [blkUpdSet, ZFSet.mem_sep]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨k, x, rfl, hcase⟩ := h
  rcases hcase with ⟨m, hm1, hm2⟩ | ⟨hpa, -⟩
  · refine ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_pairSep.mpr ⟨k, ?_, x, ?_, rfl, trivial⟩))
    · exact ZFSet.mem_sUnion.mpr ⟨_, ZFSet.mem_sUnion.mpr ⟨_, hm1, upair_mem_pair m k⟩,
        mem_upair_right m k⟩
    · exact ZFSet.mem_sUnion.mpr ⟨_, ZFSet.mem_sUnion.mpr ⟨_, hm2, upair_mem_pair m x⟩,
        mem_upair_right m x⟩
  · exact ZFSet.mem_union.mpr (Or.inl hpa)

/-- Existence and semantics of the block update. The block variables are required to be in the
domain of `a`, so that the update is again a finite sequence (see `exists_blkUpd'`). -/
theorem exists_blkUpd {A a : ZFSet.{u}} (ha : IsSeqA ωZ A a)
    (l : List ℕ) (hnd : l.Nodup) (hdom : ∀ i ∈ l, ∃ y, ZFSet.pair (natZ.{u} i) y ∈ a)
    (xs : List ZFSet.{u}) (hlen : xs.length = l.length) (hxs : ∀ x ∈ xs, x ∈ A) :
    ∃ b, IsBlkUpd a (seqOfNats.{u} l) (seqOfVals xs) b ∧ IsSeqA ωZ A b ∧
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
  have hbu := isBlkUpd_blkUpdSet (a := a) (isFunc_seqOfNats.{u} l) (isFunc_seqOfVals xs) h3 h4
  refine ⟨_, hbu, ⟨isFunc_of_isBlkUpd ha.1 hnd hbu, ?_, ?_⟩, seqVal_of_isBlkUpd ha hnd hlen hbu⟩
  · obtain ⟨n₀, hdom₀⟩ := isSeqA_dom ha
    refine ⟨natZ n₀, natZ_mem_ωZ n₀, fun c => ?_⟩
    rw [hdom₀ c]
    constructor
    · rintro ⟨y, hy⟩
      by_cases hc : ∃ m, ZFSet.pair m c ∈ seqOfNats.{u} l
      · obtain ⟨m, hm⟩ := hc
        obtain ⟨z, hz⟩ := h3 m c hm
        exact ⟨z, (hbu.2.2.2.2 _).mpr ⟨_, _, rfl, Or.inl ⟨m, hm, hz⟩⟩⟩
      · push Not at hc
        refine ⟨y, (hbu.2.2.2.2 _).mpr ⟨_, _, rfl, Or.inr ⟨hy, fun m k' hmk' hkc => ?_⟩⟩⟩
        exact hc m (hkc ▸ hmk')
    · rintro ⟨y, hy⟩
      rcases blkUpd_cases hbu hy with ⟨m, hm1, -⟩ | ⟨h1, -⟩
      · obtain ⟨i, hi, rfl⟩ := seqOfNats_val hm1
        exact hdom i hi
      · exact ⟨y, h1⟩
  · intro c x hcx
    rcases blkUpd_cases hbu hcx with ⟨m, -, hm2⟩ | ⟨h1, -⟩
    · obtain ⟨n, hn, e⟩ := mem_seqOfVals_iff.mp hm2
      rw [ZFSet.pair_inj] at e
      rw [e.2]
      exact hxs _ (List.mem_iff_getElem.mpr ⟨n, hn, rfl⟩)
    · exact ha.2.2 _ _ h1

/-- Any finite sequence can be padded with `∅` (the value of an index outside the domain),
without changing its values, so that its domain covers the first `n` variables. -/
theorem exists_padSeq {A a : ZFSet.{u}} (ha : IsSeqA ωZ A a) (hemp : ∅ ∈ A) (n : ℕ) :
    ∃ a', IsSeqA ωZ A a' ∧ IsPadOf a a' ∧ SeqVal a' = SeqVal a ∧
      ∀ i < n, ∃ y, ZFSet.pair (natZ.{u} i) y ∈ a' := by
  obtain ⟨n₀, hdom₀⟩ := isSeqA_dom ha
  set m := max n₀ n with hm
  have hmnot : ∀ y, ZFSet.pair (natZ.{u} m) y ∉ a := by
    intro y hy
    obtain ⟨k, hk, hkm⟩ := mem_natZ_iff.mp ((hdom₀ (natZ m)).mpr ⟨y, hy⟩)
    have : m = k := natZ_injective hkm
    omega
  obtain ⟨b, hb, hbseq, hbdom, -⟩ := exists_updSeq ha m hemp
  have hpad : IsPadOf a b := by
    constructor
    · intro p hp
      obtain ⟨j, y, rfl⟩ := ha.1.1 p hp
      refine (hb _).mpr (Or.inr (Or.inl ⟨hp, fun y' hcon => ?_⟩))
      rw [ZFSet.pair_inj] at hcon
      exact hmnot y (hcon.1 ▸ hp)
    · intro p hp
      rcases (hb p).mp hp with h1 | ⟨h1, -⟩ | ⟨j, -, -, h1⟩
      · exact Or.inr ⟨_, h1⟩
      · exact Or.inl h1
      · exact Or.inr ⟨_, h1⟩
  refine ⟨b, hbseq, hpad, ?_, ?_⟩
  · funext k
    by_cases hex : ∃ y, ZFSet.pair (natZ.{u} k) y ∈ a
    · obtain ⟨y, hy⟩ := hex
      have hkm : k ≠ m := by rintro rfl; exact hmnot y hy
      have hne : ∀ y', ZFSet.pair (natZ.{u} k) y ≠ ZFSet.pair (natZ.{u} m) y' := by
        intro y' h
        rw [ZFSet.pair_inj] at h
        exact hkm (natZ_injective h.1)
      have hmem : ZFSet.pair (natZ.{u} k) y ∈ b := (hb _).mpr (Or.inr (Or.inl ⟨hy, hne⟩))
      rw [seqVal_spec ha.1 hy, seqVal_spec hbseq.1 hmem]
    · push Not at hex
      rw [seqVal_of_notMem hex]
      by_cases hexb : ∃ z, ZFSet.pair (natZ.{u} k) z ∈ b
      · obtain ⟨z, hz⟩ := hexb
        rw [seqVal_spec hbseq.1 hz]
        rcases (hb _).mp hz with h1 | ⟨h1, -⟩ | ⟨j, -, -, h1⟩
        · rw [ZFSet.pair_inj] at h1; exact h1.2
        · exact absurd h1 (hex z)
        · rw [ZFSet.pair_inj] at h1; exact h1.2
      · push Not at hexb
        exact seqVal_of_notMem hexb
  · intro i hi
    by_cases hia : ∃ y, ZFSet.pair (natZ.{u} i) y ∈ a
    · exact hbdom i (Or.inl hia)
    · by_cases him : i = m
      · exact hbdom i (Or.inr him)
      · push Not at hia
        exact ⟨∅, (hb _).mpr (Or.inr (Or.inr
          ⟨natZ i, mem_natZ_iff.mpr ⟨i, by omega, rfl⟩, hia, rfl⟩))⟩

/-- The block update of an arbitrary finite sequence: after padding `a` to a sequence `a'` with
the same values, the block update exists and is again a finite sequence. -/
theorem exists_blkUpd' {A a : ZFSet.{u}} (hemp : ∅ ∈ A) (ha : IsSeqA ωZ A a)
    (l : List ℕ) (hnd : l.Nodup) (xs : List ZFSet.{u}) (hlen : xs.length = l.length)
    (hxs : ∀ x ∈ xs, x ∈ A) :
    ∃ a' b, IsSeqA ωZ A a' ∧ SeqVal a' = SeqVal a ∧
      IsBlkUpd a' (seqOfNats.{u} l) (seqOfVals xs) b ∧ IsSeqA ωZ A b ∧
      SeqVal b = updList (SeqVal a) l xs := by
  obtain ⟨a', ha', -, hval, hdom⟩ := exists_padSeq ha hemp (l.sum + 1)
  obtain ⟨b, hb, hbseq, hbval⟩ :=
    exists_blkUpd ha' l hnd
      (fun i hi => hdom i (by have := List.le_sum_of_mem hi; omega)) xs hlen hxs
  exact ⟨a', b, ha', hval, hb, hbseq, by rw [hbval, hval]⟩

/-! ### Δ₀-definability of the block update -/

/-- Bounding the second component of a pair in `s`. -/
theorem exists_snd_mem_iff_bounded (s k : ZFSet.{u}) :
    (∃ y, ZFSet.pair k y ∈ s) ↔ ∃ p ∈ s, ∃ q ∈ p, ∃ y ∈ q, ZFSet.pair k y ∈ s := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨_, hy, _, upair_mem_pair k y, y, mem_upair_right k y, hy⟩
  · rintro ⟨p, -, q, -, y, -, hy⟩
    exact ⟨y, hy⟩

/-- Bounding the first component of a pair in `s`. -/
theorem exists_fst_mem_iff_bounded (s k : ZFSet.{u}) (P : ZFSet.{u} → Prop) :
    (∃ m, ZFSet.pair m k ∈ s ∧ P m) ↔ ∃ p ∈ s, ∃ q ∈ p, ∃ m ∈ q, ZFSet.pair m k ∈ s ∧ P m := by
  constructor
  · rintro ⟨m, hm, hP⟩
    exact ⟨_, hm, _, singleton_mem_pair m k, m, ZFSet.mem_singleton.mpr rfl, hm, hP⟩
  · rintro ⟨p, -, q, -, m, -, hm, hP⟩
    exact ⟨m, hm, hP⟩

/-- Bounding the components of a Kuratowski pair by the pair itself. -/
theorem exists_kpair_iff_bounded (p : ZFSet.{u}) (R : ZFSet.{u} → ZFSet.{u} → Prop) :
    (∃ k x, p = ZFSet.pair k x ∧ R k x) ↔
      ∃ q ∈ p, ∃ k ∈ q, ∃ q' ∈ p, ∃ x ∈ q', p = ZFSet.pair k x ∧ R k x := by
  constructor
  · rintro ⟨k, x, rfl, hR⟩
    exact ⟨_, singleton_mem_pair k x, k, ZFSet.mem_singleton.mpr rfl, _, upair_mem_pair k x, x,
      mem_upair_right k x, rfl, hR⟩
  · rintro ⟨q, -, k, -, q', -, x, -, hpx, hR⟩
    exact ⟨k, x, hpx, hR⟩

/-- The domain of `v f` is contained in the domain of `v g`. -/
theorem delta0_domSub (f g : ℕ) (hfg : f ≠ g) :
    Delta0Def {f, g} (fun _ v => ∀ m x, ZFSet.pair m x ∈ v f → ∃ y, ZFSet.pair m y ∈ v g) := by
  set c := f + g + 1 with hc
  have i1 := delta0_funVal g (c + 2) (c + 7) (by omega) (by omega) (by omega)
  have i2 := i1.bex (c + 7) (c + 6) (by omega)
  have i3 := i2.bex (c + 6) (c + 5) (by omega)
  have i4 := i3.bex (c + 5) g (by omega)
  have o1 := (delta0_isKPair c (c + 2) (c + 4) (by omega) (by omega)).imp i4
  have o2 := o1.ball (c + 4) (c + 3) (by omega)
  have o3 := o2.ball (c + 3) c (by omega)
  have o4 := o3.ball (c + 2) (c + 1) (by omega)
  have o5 := o4.ball (c + 1) c (by omega)
  have h := o5.ball c f (by omega)
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · intro H m x hmx
      exact (exists_snd_mem_iff_bounded (v g) m).mpr
        (H _ hmx _ (singleton_mem_pair m x) m (ZFSet.mem_singleton.mpr rfl) _
          (upair_mem_pair m x) x (mem_upair_right m x) rfl)
    · intro H p hp q _ m _ q' _ x _ hpx
      subst hpx
      exact (exists_snd_mem_iff_bounded (v g) m).mp (H m x hp)
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- The `ν`-branch of the defining condition of the block update. -/
theorem delta0_blkMemNu (nu t b : ℕ) (hnt : nu ≠ t) (hnb : nu ≠ b) (htb : t ≠ b) :
    Delta0Def {nu, t, b} (fun _ v => ∀ m k, ZFSet.pair m k ∈ v nu →
      ∀ x, ZFSet.pair m x ∈ v t → ZFSet.pair k x ∈ v b) := by
  set c := nu + t + b + 1 with hc
  have i1 := (delta0_funVal t (c + 2) (c + 7) (by omega) (by omega) (by omega)).imp
    (delta0_funVal b (c + 4) (c + 7) (by omega) (by omega) (by omega))
  have i2 := i1.ball (c + 7) (c + 6) (by omega)
  have i3 := i2.ball (c + 6) (c + 5) (by omega)
  have i4 := i3.ball (c + 5) t (by omega)
  have o1 := (delta0_isKPair c (c + 2) (c + 4) (by omega) (by omega)).imp i4
  have o2 := o1.ball (c + 4) (c + 3) (by omega)
  have o3 := o2.ball (c + 3) c (by omega)
  have o4 := o3.ball (c + 2) (c + 1) (by omega)
  have o5 := o4.ball (c + 1) c (by omega)
  have h := o5.ball c nu (by omega)
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · intro H m k hmk x hmx
      exact H _ hmk _ (singleton_mem_pair m k) m (ZFSet.mem_singleton.mpr rfl) _
        (upair_mem_pair m k) k (mem_upair_right m k) rfl _ hmx _ (upair_mem_pair m x) x
        (mem_upair_right m x) hmx
    · intro H p hp q _ m _ q' _ k _ hpk p2 _ q2 _ x _ hmx
      subst hpk
      exact H m k hp x hmx
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- The `a`-branch of the defining condition of the block update. -/
theorem delta0_blkMemA (a nu b : ℕ) (han : a ≠ nu) (hab : a ≠ b) (hnb : nu ≠ b) :
    Delta0Def {a, nu, b} (fun _ v => ∀ p ∈ v a, (∃ k x, p = ZFSet.pair k x ∧
      ∀ m k', ZFSet.pair m k' ∈ v nu → k' ≠ k) → p ∈ v b) := by
  set c := a + nu + b + 1 with hc
  have n1 := (delta0_isKPair (c + 5) (c + 7) (c + 9) (by omega) (by omega)).imp
    (Delta0Def.eq (c + 9) (c + 2)).not
  have n2 := n1.ball (c + 9) (c + 8) (by omega)
  have n3 := n2.ball (c + 8) (c + 5) (by omega)
  have n4 := n3.ball (c + 7) (c + 6) (by omega)
  have n5 := n4.ball (c + 6) (c + 5) (by omega)
  have n6 := n5.ball (c + 5) nu (by omega)
  have e1 := (delta0_isKPair c (c + 2) (c + 4) (by omega) (by omega)).and n6
  have e2 := e1.bex (c + 4) (c + 3) (by omega)
  have e3 := e2.bex (c + 3) c (by omega)
  have e4 := e3.bex (c + 2) (c + 1) (by omega)
  have e5 := e4.bex (c + 1) c (by omega)
  have h := (e5.imp (Delta0Def.mem c b)).ball c a (by omega)
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · intro H p hp hex
      obtain ⟨k, x, rfl, hnot⟩ := hex
      refine H _ hp ⟨_, singleton_mem_pair k x, k, ZFSet.mem_singleton.mpr rfl, _,
        upair_mem_pair k x, x, mem_upair_right k x, rfl, ?_⟩
      intro p2 hp2 q2 _ m _ q3 _ k' _ hp2e
      subst hp2e
      exact hnot m k' hp2
    · intro H p hp hex
      obtain ⟨q, -, k, -, q', -, x, -, hpx, hnot⟩ := hex
      refine H p hp ⟨k, x, hpx, fun m k' hmk' => ?_⟩
      exact hnot _ hmk' _ (singleton_mem_pair m k') m (ZFSet.mem_singleton.mpr rfl) _
        (upair_mem_pair m k') k' (mem_upair_right m k') rfl
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- Members of the block update satisfy the defining condition. -/
theorem delta0_blkMem (a nu t b : ℕ) (han : a ≠ nu) (hat : a ≠ t) (hab : a ≠ b)
    (hnt : nu ≠ t) (hnb : nu ≠ b) (htb : t ≠ b) :
    Delta0Def {a, nu, t, b} (fun _ v => ∀ p ∈ v b, ∃ k x, p = ZFSet.pair k x ∧
      ((∃ m, ZFSet.pair m k ∈ v nu ∧ ZFSet.pair m x ∈ v t) ∨
        (p ∈ v a ∧ ∀ m k', ZFSet.pair m k' ∈ v nu → k' ≠ k))) := by
  set c := a + nu + t + b + 1 with hc
  have f1 := (delta0_funVal nu (c + 7) (c + 2) (by omega) (by omega) (by omega)).and
    (delta0_funVal t (c + 7) (c + 4) (by omega) (by omega) (by omega))
  have f2 := f1.bex (c + 7) (c + 6) (by omega)
  have f3 := f2.bex (c + 6) (c + 5) (by omega)
  have f4 := f3.bex (c + 5) nu (by omega)
  have n1 := (delta0_isKPair (c + 8) (c + 10) (c + 12) (by omega) (by omega)).imp
    (Delta0Def.eq (c + 12) (c + 2)).not
  have n2 := n1.ball (c + 12) (c + 11) (by omega)
  have n3 := n2.ball (c + 11) (c + 8) (by omega)
  have n4 := n3.ball (c + 10) (c + 9) (by omega)
  have n5 := n4.ball (c + 9) (c + 8) (by omega)
  have n6 := n5.ball (c + 8) nu (by omega)
  have g1 := (delta0_isKPair c (c + 2) (c + 4) (by omega) (by omega)).and
    (f4.or ((Delta0Def.mem c a).and n6))
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
      refine ⟨k, x, hpx, ?_⟩
      rcases hcase with ⟨r, -, s, -, m, -, hm1, hm2⟩ | ⟨hpa, hnot⟩
      · exact Or.inl ⟨m, hm1, hm2⟩
      · refine Or.inr ⟨hpa, fun m k' hmk' => ?_⟩
        exact hnot _ hmk' _ (singleton_mem_pair m k') m (ZFSet.mem_singleton.mpr rfl) _
          (upair_mem_pair m k') k' (mem_upair_right m k') rfl
    · intro H p hp
      obtain ⟨k, x, rfl, hcase⟩ := H p hp
      refine ⟨_, singleton_mem_pair k x, k, ZFSet.mem_singleton.mpr rfl, _, upair_mem_pair k x,
        x, mem_upair_right k x, rfl, ?_⟩
      rcases hcase with ⟨m, hm1, hm2⟩ | ⟨hpa, hnot⟩
      · exact Or.inl ⟨_, hm1, _, singleton_mem_pair m k, m, ZFSet.mem_singleton.mpr rfl, hm1, hm2⟩
      · refine Or.inr ⟨hpa, ?_⟩
        intro p2 hp2 q2 _ m _ q3 _ k' _ hp2e
        subst hp2e
        exact hnot m k' hp2
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- Δ₀-definability of the block update. -/
theorem delta0_isBlkUpd (a nu t b : ℕ) (han : a ≠ nu) (hat : a ≠ t) (hab : a ≠ b)
    (hnt : nu ≠ t) (hnb : nu ≠ b) (htb : t ≠ b) :
    Delta0Def {a, nu, t, b} (fun _ v => IsBlkUpd (v a) (v nu) (v t) (v b)) := by
  have h1 := delta0_isFunc nu
  have h2 := delta0_isFunc t
  have h3 := delta0_domSub nu t hnt
  have h4 := delta0_domSub t nu hnt.symm
  have h5 := delta0_blkMem a nu t b han hat hab hnt hnb htb
  have h6 := delta0_blkMemA a nu b han hab hnb
  have h7 := delta0_blkMemNu nu t b hnt hnb htb
  refine ((((h1.and h2).and (h3.and h4)).and ((h5.and h6).and h7)).congr ?_).of_eq ?_
  · intro D v _ _
    unfold IsBlkUpd
    constructor
    · rintro ⟨⟨⟨hf1, hf2⟩, hc3, hc4⟩, ⟨hi, hiia⟩, hiib⟩
      refine ⟨hf1, hf2, hc3, hc4, ?_⟩
      intro p
      refine ⟨hi p, ?_⟩
      rintro ⟨k, x, rfl, hcase⟩
      rcases hcase with ⟨m, hmk, hmx⟩ | ⟨hpa, hnot⟩
      · exact hiib m k hmk x hmx
      · exact hiia _ hpa ⟨k, x, rfl, hnot⟩
    · rintro ⟨hf1, hf2, hc3, hc4, hall⟩
      refine ⟨⟨⟨hf1, hf2⟩, hc3, hc4⟩, ⟨fun p hp => (hall p).mp hp, ?_⟩, ?_⟩
      · intro p hpa hex
        obtain ⟨k, x, hpx, hnot⟩ := hex
        exact (hall p).mpr ⟨k, x, hpx, Or.inr ⟨hpa, hnot⟩⟩
      · intro m k hmk x hmx
        exact (hall _).mpr ⟨k, x, rfl, Or.inl ⟨m, hmk, hmx⟩⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]; omega

end BM4.ST
