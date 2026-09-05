/-
  Part III, §13: correctness of the alternating-block truth predicates (Theorem 13.6),
  relative to the correctness of the Δ₀ base (`BaseCorrect`).
-/
import Bm4.SetTheory.Truth
import Bm4.SetTheory.BFCode
import Bm4.SetTheory.BFCodeD
import Bm4.SetTheory.Blk

universe u

namespace BM4.ST

open Fm

/-! ### Closure of the domain -/

/-- The domain `W` contains `∅` and is closed under `insert`; equivalently it contains every
hereditarily finite set built from its own elements.  For `W = L θ` with `θ` a limit this is
`empty_mem_L_of_limit` together with `insert_mem_L_of_limit`. -/
def WClosed (W : ZFSet.{u}) : Prop :=
  (∅ : ZFSet.{u}) ∈ W ∧ ∀ x ∈ W, ∀ y ∈ W, insert x y ∈ W

namespace WClosed

variable {W : ZFSet.{u}}

theorem empty_mem (h : WClosed W) : (∅ : ZFSet.{u}) ∈ W := h.1

theorem insert_mem (h : WClosed W) {x y : ZFSet.{u}} (hx : x ∈ W) (hy : y ∈ W) :
    insert x y ∈ W := h.2 x hx y hy

theorem singleton_mem (h : WClosed W) {x : ZFSet.{u}} (hx : x ∈ W) : ({x} : ZFSet.{u}) ∈ W := by
  have he : ({x} : ZFSet.{u}) = insert x ∅ := by ext z; simp
  rw [he]; exact h.insert_mem hx h.empty_mem

theorem upair_mem (h : WClosed W) {x y : ZFSet.{u}} (hx : x ∈ W) (hy : y ∈ W) :
    ({x, y} : ZFSet.{u}) ∈ W := h.insert_mem hx (h.singleton_mem hy)

theorem kpair_mem (h : WClosed W) {x y : ZFSet.{u}} (hx : x ∈ W) (hy : y ∈ W) :
    ZFSet.pair x y ∈ W := by
  have he : ZFSet.pair x y = ({{x}, {x, y}} : ZFSet.{u}) := rfl
  rw [he]
  exact h.upair_mem (h.singleton_mem hx) (h.upair_mem hx hy)

theorem natZ_mem (h : WClosed W) : ∀ n : ℕ, natZ.{u} n ∈ W
  | 0 => h.empty_mem
  | n + 1 => h.insert_mem (h.natZ_mem n) (h.natZ_mem n)

theorem seqOfAux_mem (h : WClosed W) : ∀ (k : ℕ) (l : List ZFSet.{u}), (∀ x ∈ l, x ∈ W) →
    seqOfAux k l ∈ W
  | _, [], _ => h.empty_mem
  | k, x :: l, hl => by
    rw [seqOfAux]
    exact h.insert_mem (h.kpair_mem (h.natZ_mem k) (hl x (by simp)))
      (h.seqOfAux_mem (k + 1) l (fun y hy => hl y (by simp [hy])))

theorem seqOfVals_mem (h : WClosed W) (xs : List ZFSet.{u}) (hxs : ∀ x ∈ xs, x ∈ W) :
    seqOfVals xs ∈ W := h.seqOfAux_mem 0 xs hxs

theorem seqOfNats_mem (h : WClosed W) (l : List ℕ) : seqOfNats.{u} l ∈ W := by
  refine h.seqOfAux_mem 0 (l.map natZ.{u}) ?_
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact h.natZ_mem i

end WClosed

/-- The closure conditions hold for every limit level of the constructible hierarchy, in
particular for `W = L θ` with `θ` admissible; so the extra clauses of `GoodAsn` below are not
vacuous. -/
theorem wClosed_L {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ) : WClosed (L θ) :=
  ⟨empty_mem_L_of_limit hθ, fun _ hx _ hy => insert_mem_L_of_limit hθ hx hy⟩

/-! ### Elementary consequences of transitivity -/

theorem fst_mem_of_kpair_mem {W : ZFSet.{u}} (hWt : W.IsTransitive) {x y : ZFSet.{u}}
    (h : ZFSet.pair x y ∈ W) : x ∈ W :=
  hWt.subset_of_mem (hWt.subset_of_mem h (singleton_mem_pair x y)) (ZFSet.mem_singleton.mpr rfl)

theorem snd_mem_of_kpair_mem {W : ZFSet.{u}} (hWt : W.IsTransitive) {x y : ZFSet.{u}}
    (h : ZFSet.pair x y ∈ W) : y ∈ W :=
  hWt.subset_of_mem (hWt.subset_of_mem h (upair_mem_pair x y)) (mem_upair_right x y)

/-! ### Finite sequences as `seqOfVals` -/

theorem seqVal_mem_of_vals {W s : ZFSet.{u}} (hemp : (∅ : ZFSet.{u}) ∈ W) (hf : IsFunc s)
    (hval : ∀ i x, ZFSet.pair i x ∈ s → x ∈ W) (k : ℕ) : SeqVal s k ∈ W := by
  by_cases hk : ∃ y, ZFSet.pair (natZ.{u} k) y ∈ s
  · obtain ⟨y, hy⟩ := hk
    rw [seqVal_spec hf hy]
    exact hval _ _ hy
  · push Not at hk
    rw [seqVal_of_notMem hk]
    exact hemp

/-- A function-set whose domain is the natural number `n` is the sequence of its own values. -/
theorem seq_eq_seqOfVals {s : ZFSet.{u}} (hf : IsFunc s) {n : ℕ} (hdom : IsDom s (natZ.{u} n)) :
    s = seqOfVals ((List.range n).map (SeqVal s)) := by
  have hlen : ((List.range n).map (SeqVal.{u} s)).length = n := by simp
  ext p
  constructor
  · intro hp
    obtain ⟨c, x, rfl⟩ := hf.1 p hp
    have hc : c ∈ natZ.{u} n := (hdom c).mpr ⟨x, hp⟩
    obtain ⟨k, hk, rfl⟩ := mem_natZ_iff.mp hc
    have hv : SeqVal s k = x := seqVal_spec hf hp
    have hkl : k < ((List.range n).map (SeqVal.{u} s)).length := by rw [hlen]; exact hk
    have hget : ((List.range n).map (SeqVal.{u} s))[k]'hkl = x := by
      rw [List.getElem_map]
      simpa using hv
    rw [← hget]
    exact mem_seqOfVals hkl
  · intro hp
    obtain ⟨k, hk, rfl⟩ := mem_seqOfVals_iff.mp hp
    have hkn : k < n := by rw [hlen] at hk; exact hk
    have hget : ((List.range n).map (SeqVal.{u} s))[k]'hk = SeqVal s k := by
      rw [List.getElem_map]; simp
    rw [hget]
    have hc : natZ.{u} k ∈ natZ.{u} n := natZ_mem_natZ_iff.mpr hkn
    obtain ⟨y, hy⟩ := (hdom _).mp hc
    rw [seqVal_spec hf hy]
    exact hy

/-- A finite sequence over `W` is itself an element of `W`. -/
theorem isSeqA_mem_of_wClosed {W s : ZFSet.{u}} (hW : WClosed W) (hs : IsSeqA ωZ W s) : s ∈ W := by
  obtain ⟨hf, ⟨d, hd, hdom⟩, hval⟩ := hs
  obtain ⟨n, rfl⟩ := mem_ωZ_iff.mp hd
  rw [seq_eq_seqOfVals hf hdom]
  refine hW.seqOfVals_mem _ ?_
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨k, -, rfl⟩ := hx
  exact seqVal_mem_of_vals hW.empty_mem hf hval k


/-! ### Block updates inside `W` -/

/-- A block update never shrinks the domain of the assignment. -/
theorem blkUpd_dom_mono {a ν t b : ZFSet.{u}} (hbu : IsBlkUpd a ν t b) {c : ZFSet.{u}}
    (h : ∃ y, ZFSet.pair c y ∈ a) : ∃ y, ZFSet.pair c y ∈ b := by
  obtain ⟨y, hy⟩ := h
  by_cases hc : ∃ m, ZFSet.pair m c ∈ ν
  · obtain ⟨m, hm⟩ := hc
    obtain ⟨z, hz⟩ := hbu.2.2.1 m c hm
    exact ⟨z, (hbu.2.2.2.2 _).mpr ⟨_, _, rfl, Or.inl ⟨m, hm, hz⟩⟩⟩
  · push Not at hc
    exact ⟨y, (hbu.2.2.2.2 _).mpr ⟨_, _, rfl,
      Or.inr ⟨hy, fun m k' hmk' hkc => hc m (hkc ▸ hmk')⟩⟩⟩

/-- The value part of a block update along `l` has domain `l.length`. -/
theorem isDom_of_blkUpd {a t b : ZFSet.{u}} {l : List ℕ}
    (hbu : IsBlkUpd a (seqOfNats.{u} l) t b) : IsDom t (natZ.{u} l.length) := by
  intro c
  constructor
  · intro hc
    obtain ⟨j, hj, rfl⟩ := mem_natZ_iff.mp hc
    have hν : ZFSet.pair (natZ.{u} j) (natZ.{u} (l[j]'hj)) ∈ seqOfNats.{u} l :=
      mem_seqOfNats.mpr (List.getElem?_eq_getElem hj)
    exact hbu.2.2.1 _ _ hν
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hbu.2.2.2.1 _ _ hy
    obtain ⟨n, i, hni, he⟩ := mem_seqOfNats_iff.mp hx
    obtain ⟨rfl, -⟩ := ZFSet.pair_injective he
    exact natZ_mem_natZ_iff.mpr (List.getElem?_eq_some_iff.mp hni).1

/-- Any block update inside `W` comes from a list of values of `W`. -/
theorem blkUpd_list {W : ZFSet.{u}} (hWt : W.IsTransitive) (hW : WClosed W)
    {a : ZFSet.{u}} (ha : IsSeqA ωZ W a) {l : List ℕ} (hnd : l.Nodup)
    (hdom : ∀ i ∈ l, ∃ y, ZFSet.pair (natZ.{u} i) y ∈ a)
    {t b : ZFSet.{u}} (htW : t ∈ W) (hbu : IsBlkUpd a (seqOfNats.{u} l) t b) :
    ∃ xs : List ZFSet.{u}, xs.length = l.length ∧ (∀ x ∈ xs, x ∈ W) ∧
      IsSeqA ωZ W b ∧ SeqVal b = updList (SeqVal a) l xs := by
  have hft : IsFunc t := hbu.2.1
  have hvalt : ∀ i x, ZFSet.pair i x ∈ t → x ∈ W := fun i x hix =>
    snd_mem_of_kpair_mem hWt (hWt.subset_of_mem htW hix)
  have hdt : IsDom t (natZ.{u} l.length) := isDom_of_blkUpd hbu
  obtain ⟨xs, hlen, hxsW, hteq⟩ : ∃ xs : List ZFSet.{u}, xs.length = l.length ∧
      (∀ x ∈ xs, x ∈ W) ∧ t = seqOfVals xs := by
    refine ⟨(List.range l.length).map (SeqVal.{u} t), by simp, ?_, seq_eq_seqOfVals hft hdt⟩
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨k, -, rfl⟩ := hx
    exact seqVal_mem_of_vals hW.empty_mem hft hvalt k
  rw [hteq] at hbu
  obtain ⟨b₀, hbu₀, hseq₀, hval₀⟩ := exists_blkUpd ha l hnd hdom xs hlen hxsW
  have hbb : b₀ = b := isBlkUpd_unique hbu₀ hbu
  subst hbb
  exact ⟨xs, hlen, hxsW, hseq₀, hval₀⟩

/-- The block update of a sequence of `W` by values of `W` exists inside `W`. -/
theorem exists_blkUpd_W {W : ZFSet.{u}} (hW : WClosed W) {a : ZFSet.{u}} (ha : IsSeqA ωZ W a)
    {l : List ℕ} (hnd : l.Nodup) (hdom : ∀ i ∈ l, ∃ y, ZFSet.pair (natZ.{u} i) y ∈ a)
    {xs : List ZFSet.{u}} (hlen : xs.length = l.length) (hxs : ∀ x ∈ xs, x ∈ W) :
    ∃ b, IsBlkUpd a (seqOfNats.{u} l) (seqOfVals xs) b ∧ IsSeqA ωZ W b ∧ b ∈ W ∧
      SeqVal b = updList (SeqVal a) l xs := by
  obtain ⟨b, hbu, hseq, hval⟩ := exists_blkUpd ha l hnd hdom xs hlen hxs
  exact ⟨b, hbu, hseq, isSeqA_mem_of_wClosed hW hseq, hval⟩

/-! ### Good assignments -/

/-- The block variables of a block formula. -/
def BF.blockVars : BF → List ℕ
  | .delta _ _ => []
  | .exs l ψ => l ++ ψ.blockVars
  | .alls l ψ => l ++ ψ.blockVars

/-- The assignment `a` is a finite sequence over `W` whose domain covers every block variable.
Besides the three clauses of the statement of Theorem 13.6 this records:
the block variable lists have no repetitions (otherwise the block update is not well defined),
the code of `b` lies in `W`, and `W` is closed under `∅` and `insert`. -/
def GoodAsn (W : ZFSet.{u}) (b : BF) (a : ZFSet.{u}) : Prop :=
  IsSeqA ωZ W a ∧ a ∈ W ∧ (∀ i ∈ b.blockVars, ∃ y, ZFSet.pair (natZ.{u} i) y ∈ a) ∧
    b.blockVars.Nodup ∧ BF.code.{u} b ∈ W ∧ WClosed W

/-! ### The code guard of Definitions 13.2 and 13.4 on codes of block formulas -/

/-- No variable repeats anywhere, so in particular none repeats inside a block. -/
theorem BF.nodupBlocks_of_blockVars_nodup : ∀ {b : BF}, b.blockVars.Nodup → b.NodupBlocks := by
  intro b
  induction b with
  | delta sg φ => intro _; trivial
  | exs l ψ ih =>
    intro h
    simp only [BF.blockVars] at h
    exact (BF.nodupBlocks_exs l ψ).mpr
      ⟨(List.nodup_append.mp h).1, ih (List.nodup_append.mp h).2.1⟩
  | alls l ψ ih =>
    intro h
    simp only [BF.blockVars] at h
    exact (BF.nodupBlocks_alls l ψ).mpr
      ⟨(List.nodup_append.mp h).1, ih (List.nodup_append.mp h).2.1⟩

/-- `Form_{Σ̂q}` of Definition 13.4 holds of the code of a `Σ̂q` block formula. -/
theorem isSigCodeWD_code {q : ℕ} {b : BF} (hb : BF.Sig q b) (hnb : b.NodupBlocks) :
    IsSigCodeWD (L Ordinal.omega0) ωZ q (BF.code.{u} b) :=
  (isSigCodeWD_iff q _).mpr ⟨b, hb, hnb, rfl⟩

/-- `Form_{Π̂q}` of Definition 13.4 holds of the code of a `Π̂q` block formula. -/
theorem isPiCodeWD_code {q : ℕ} {b : BF} (hb : BF.Pi q b) (hnb : b.NodupBlocks) :
    IsPiCodeWD (L Ordinal.omega0) ωZ q (BF.code.{u} b) :=
  (isPiCodeWD_iff q _).mpr ⟨b, hb, hnb, rfl⟩

/-- `Form_{Δ₀}` of Definition 13.4 (the `q = 0` level) holds of the code of a signed Δ₀ block
formula. -/
theorem isDeltaBFCodeW_code {sg : Bool} {φ : Fm} (hφ : IsDelta0 φ) :
    IsDeltaBFCodeW (L Ordinal.omega0) ωZ (BF.code.{u} (BF.delta sg φ)) :=
  (isDeltaBFCodeW_iff _).mpr ⟨sg, φ, hφ, rfl⟩


/-! ### The Δ₀ level -/

theorem code_delta_true (φ : Fm) : BF.code.{u} (BF.delta true φ) =
    ZFSet.pair (natZ 0) (ZFSet.pair (natZ 1) (Fm.code.{u} φ)) := rfl

theorem code_delta_false (φ : Fm) : BF.code.{u} (BF.delta false φ) =
    ZFSet.pair (natZ 0) (ZFSet.pair (natZ 0) (Fm.code.{u} φ)) := rfl

theorem toFm_delta_true (φ : Fm) : (BF.delta true φ).toFm = φ := rfl

theorem toFm_delta_false (φ : Fm) : (BF.delta false φ).toFm = Fm.not φ := rfl

theorem trMSig_correct {W : ZFSet.{u}} (hWt : W.IsTransitive) (hbase : BaseCorrect W)
    {sg : Bool} {φ : Fm} (hφ : IsDelta0 φ) {a : ZFSet.{u}}
    (hg : GoodAsn W (BF.delta sg φ) a) :
    TrMSig (· ∈ W) (L Ordinal.omega0) ωZ (BF.code.{u} (BF.delta sg φ)) a ↔
      Sat (· ∈ W) (SeqVal a) (BF.delta sg φ).toFm := by
  obtain ⟨ha, haW, -, -, hcode, hW⟩ := hg
  obtain ⟨hP, hN⟩ := hbase φ hφ a ha haW
  have hdW : Fm.code.{u} φ ∈ W := by
    simp only [BF.code] at hcode
    exact snd_mem_of_kpair_mem hWt (snd_mem_of_kpair_mem hWt hcode)
  have hz : natZ.{u} 0 ∈ W := hW.natZ_mem 0
  have ho : natZ.{u} 1 ∈ W := hW.natZ_mem 1
  refine Iff.trans (and_iff_right (isDeltaBFCodeW_code (sg := sg) hφ)) ?_
  cases sg
  · rw [code_delta_false, toFm_delta_false, sat_not]
    constructor
    · rintro ⟨sg', hsg', d, hd, heq, hcase⟩
      obtain ⟨-, heq2⟩ := ZFSet.pair_injective heq
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective heq2
      rcases hcase with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd (natZ_injective h1) (by decide)
      · exact fun hs => h2 (hN.mpr hs)
    · intro hs
      exact ⟨natZ 0, hz, Fm.code.{u} φ, hdW, rfl, Or.inr ⟨rfl, fun h => hs (hN.mp h)⟩⟩
  · rw [code_delta_true, toFm_delta_true]
    constructor
    · rintro ⟨sg', hsg', d, hd, heq, hcase⟩
      obtain ⟨-, heq2⟩ := ZFSet.pair_injective heq
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective heq2
      rcases hcase with ⟨-, h1⟩ | ⟨h2, -⟩
      · exact hP.mp h1
      · exact absurd (natZ_injective h2) (by decide)
    · intro hs
      exact ⟨natZ 1, ho, Fm.code.{u} φ, hdW, rfl, Or.inl ⟨rfl, hP.mpr hs⟩⟩

theorem trMPi_correct {W : ZFSet.{u}} (hWt : W.IsTransitive) (hbase : BaseCorrect W)
    {sg : Bool} {φ : Fm} (hφ : IsDelta0 φ) {a : ZFSet.{u}}
    (hg : GoodAsn W (BF.delta sg φ) a) :
    TrMPi (· ∈ W) (L Ordinal.omega0) ωZ (BF.code.{u} (BF.delta sg φ)) a ↔
      Sat (· ∈ W) (SeqVal a) (BF.delta sg φ).toFm := by
  obtain ⟨ha, haW, -, -, hcode, hW⟩ := hg
  obtain ⟨hP, hN⟩ := hbase φ hφ a ha haW
  have hdW : Fm.code.{u} φ ∈ W := by
    simp only [BF.code] at hcode
    exact snd_mem_of_kpair_mem hWt (snd_mem_of_kpair_mem hWt hcode)
  have hz : natZ.{u} 0 ∈ W := hW.natZ_mem 0
  have ho : natZ.{u} 1 ∈ W := hW.natZ_mem 1
  refine Iff.trans (and_iff_right (isDeltaBFCodeW_code (sg := sg) hφ)) ?_
  cases sg
  · rw [code_delta_false, toFm_delta_false, sat_not]
    constructor
    · intro H
      obtain ⟨-, h2⟩ := H (natZ 0) hz (Fm.code.{u} φ) hdW rfl
      exact fun hs => h2 rfl (hP.mpr hs)
    · intro hs sg' hsg' d hd heq
      obtain ⟨-, heq2⟩ := ZFSet.pair_injective heq
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective heq2
      exact ⟨fun h1 => absurd (natZ_injective h1) (by decide), fun _ h => hs (hP.mp h)⟩
  · rw [code_delta_true, toFm_delta_true]
    constructor
    · intro H
      obtain ⟨h1, -⟩ := H (natZ 1) ho (Fm.code.{u} φ) hdW rfl
      exact hN.mp (h1 rfl)
    · intro hs sg' hsg' d hd heq
      obtain ⟨-, heq2⟩ := ZFSet.pair_injective heq
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective heq2
      exact ⟨fun _ => hN.mpr hs, fun h0 => absurd (natZ_injective h0) (by decide)⟩


/-! ### The quantifier-block step -/

theorem code_exs (l : List ℕ) (ψ : BF) : BF.code.{u} (BF.exs l ψ) =
    ZFSet.pair (natZ 1) (ZFSet.pair (seqOfNats.{u} l) (BF.code.{u} ψ)) := rfl

theorem code_alls (l : List ℕ) (ψ : BF) : BF.code.{u} (BF.alls l ψ) =
    ZFSet.pair (natZ 2) (ZFSet.pair (seqOfNats.{u} l) (BF.code.{u} ψ)) := rfl

theorem toFm_exs (l : List ℕ) (ψ : BF) : (BF.exs l ψ).toFm = Fm.exs l ψ.toFm := rfl

theorem toFm_alls (l : List ℕ) (ψ : BF) : (BF.alls l ψ).toFm = Fm.alls l ψ.toFm := rfl

theorem trSig_step {W : ZFSet.{u}} (hWt : W.IsTransitive) {l : List ℕ} {ψ : BF}
    {a : ZFSet.{u}} (hg : GoodAsn W (BF.exs l ψ) a)
    {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (hP : ∀ b, GoodAsn W ψ b → (P (BF.code.{u} ψ) b ↔ Sat (· ∈ W) (SeqVal b) ψ.toFm)) :
    (∃ ν, ν ∈ W ∧ ∃ d, d ∈ W ∧ ∃ t, t ∈ W ∧ ∃ b, b ∈ W ∧
        BF.code.{u} (BF.exs l ψ) = ZFSet.pair (natZ 1) (ZFSet.pair ν d) ∧
        IsBlkUpd a ν t b ∧ P d b) ↔
      Sat (· ∈ W) (SeqVal a) (BF.exs l ψ).toFm := by
  obtain ⟨ha, haW, hdom, hnd, hcode, hW⟩ := hg
  simp only [BF.blockVars] at hdom hnd
  have hndl : l.Nodup := (List.nodup_append.mp hnd).1
  have hndψ : ψ.blockVars.Nodup := (List.nodup_append.mp hnd).2.1
  have hdoml : ∀ i ∈ l, ∃ y, ZFSet.pair (natZ.{u} i) y ∈ a :=
    fun i hi => hdom i (List.mem_append_left _ hi)
  have hdomψ : ∀ i ∈ ψ.blockVars, ∃ y, ZFSet.pair (natZ.{u} i) y ∈ a :=
    fun i hi => hdom i (List.mem_append_right _ hi)
  rw [code_exs] at hcode
  have hcodeψ : BF.code.{u} ψ ∈ W :=
    snd_mem_of_kpair_mem hWt (snd_mem_of_kpair_mem hWt hcode)
  rw [toFm_exs, sat_exs_iff_exsD, exsD_iff_exists_list]
  constructor
  · rintro ⟨ν, hνW, d, hdW, t, htW, b, hbW, heq, hbu, hPd⟩
    rw [code_exs] at heq
    obtain ⟨-, heq2⟩ := ZFSet.pair_injective heq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective heq2
    obtain ⟨xs, hlen, hxsW, hseqb, hvalb⟩ := blkUpd_list hWt hW ha hndl hdoml htW hbu
    refine ⟨xs, hlen, hxsW, ?_⟩
    rw [← hvalb]
    exact (hP b ⟨hseqb, hbW, fun i hi => blkUpd_dom_mono hbu (hdomψ i hi), hndψ,
      hcodeψ, hW⟩).mp hPd
  · rintro ⟨xs, hlen, hxsW, hsat⟩
    obtain ⟨b, hbu, hseqb, hbW, hvalb⟩ := exists_blkUpd_W hW ha hndl hdoml hlen hxsW
    refine ⟨seqOfNats.{u} l, hW.seqOfNats_mem l, BF.code.{u} ψ, hcodeψ,
      seqOfVals xs, hW.seqOfVals_mem xs hxsW, b, hbW, code_exs l ψ, hbu, ?_⟩
    refine (hP b ⟨hseqb, hbW, fun i hi => blkUpd_dom_mono hbu (hdomψ i hi), hndψ,
      hcodeψ, hW⟩).mpr ?_
    rw [hvalb]
    exact hsat

theorem trPi_step {W : ZFSet.{u}} (hWt : W.IsTransitive) {l : List ℕ} {ψ : BF}
    {a : ZFSet.{u}} (hg : GoodAsn W (BF.alls l ψ) a)
    {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (hP : ∀ b, GoodAsn W ψ b → (P (BF.code.{u} ψ) b ↔ Sat (· ∈ W) (SeqVal b) ψ.toFm)) :
    (∀ ν, ν ∈ W → ∀ d, d ∈ W → ∀ t, t ∈ W → ∀ b, b ∈ W →
        BF.code.{u} (BF.alls l ψ) = ZFSet.pair (natZ 2) (ZFSet.pair ν d) →
        IsBlkUpd a ν t b → P d b) ↔
      Sat (· ∈ W) (SeqVal a) (BF.alls l ψ).toFm := by
  obtain ⟨ha, haW, hdom, hnd, hcode, hW⟩ := hg
  simp only [BF.blockVars] at hdom hnd
  have hndl : l.Nodup := (List.nodup_append.mp hnd).1
  have hndψ : ψ.blockVars.Nodup := (List.nodup_append.mp hnd).2.1
  have hdoml : ∀ i ∈ l, ∃ y, ZFSet.pair (natZ.{u} i) y ∈ a :=
    fun i hi => hdom i (List.mem_append_left _ hi)
  have hdomψ : ∀ i ∈ ψ.blockVars, ∃ y, ZFSet.pair (natZ.{u} i) y ∈ a :=
    fun i hi => hdom i (List.mem_append_right _ hi)
  rw [code_alls] at hcode
  have hcodeψ : BF.code.{u} ψ ∈ W :=
    snd_mem_of_kpair_mem hWt (snd_mem_of_kpair_mem hWt hcode)
  rw [toFm_alls, sat_alls_iff_allD, allD_iff_forall_list]
  constructor
  · intro H xs hlen hxsW
    obtain ⟨b, hbu, hseqb, hbW, hvalb⟩ := exists_blkUpd_W hW ha hndl hdoml hlen hxsW
    have hPd := H (seqOfNats.{u} l) (hW.seqOfNats_mem l) (BF.code.{u} ψ) hcodeψ
      (seqOfVals xs) (hW.seqOfVals_mem xs hxsW) b hbW (code_alls l ψ) hbu
    rw [← hvalb]
    exact (hP b ⟨hseqb, hbW, fun i hi => blkUpd_dom_mono hbu (hdomψ i hi), hndψ,
      hcodeψ, hW⟩).mp hPd
  · intro H ν hνW d hdW t htW b hbW heq hbu
    rw [code_alls] at heq
    obtain ⟨-, heq2⟩ := ZFSet.pair_injective heq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective heq2
    obtain ⟨xs, hlen, hxsW, hseqb, hvalb⟩ := blkUpd_list hWt hW ha hndl hdoml htW hbu
    refine (hP b ⟨hseqb, hbW, fun i hi => blkUpd_dom_mono hbu (hdomψ i hi), hndψ,
      hcodeψ, hW⟩).mpr ?_
    rw [hvalb]
    exact H xs hlen hxsW


/-! ### Theorem 13.6 -/

/-- The two halves of **Theorem 13.6**, by simultaneous strong induction on the number of
alternating blocks. -/
theorem trSigPiS_correct {W : ZFSet.{u}} (hWt : W.IsTransitive) (hbase : BaseCorrect W) :
    ∀ (q : ℕ) (b : BF),
      (BF.Sig q b → ∀ a, GoodAsn W b a →
        (TrSigS (· ∈ W) (L Ordinal.omega0) ωZ q (BF.code.{u} b) a ↔
          Sat (· ∈ W) (SeqVal a) b.toFm)) ∧
      (BF.Pi q b → ∀ a, GoodAsn W b a →
        (TrPiS (· ∈ W) (L Ordinal.omega0) ωZ q (BF.code.{u} b) a ↔
          Sat (· ∈ W) (SeqVal a) b.toFm)) := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro b
  match q with
  | 0 =>
    constructor
    · intro hs a hg
      cases hs with
      | zero hφ => rw [trSigS_zero]; exact trMSig_correct hWt hbase hφ hg
    · intro hs a hg
      cases hs with
      | zero hφ => rw [trPiS_zero]; exact trMPi_correct hWt hbase hφ hg
  | 1 =>
    constructor
    · intro hs a hg
      cases hs with
      | succ hl hψ =>
        rw [trSigS_one, and_iff_right (isSigCodeWD_code (BF.Sig.succ hl hψ)
          (BF.nodupBlocks_of_blockVars_nodup hg.2.2.2.1))]
        refine trSig_step hWt hg ?_
        intro b' hg'
        cases hψ with
        | zero hφ => exact trMSig_correct hWt hbase hφ hg'
    · intro hs a hg
      cases hs with
      | succ hl hψ =>
        rw [trPiS_one, and_iff_right (isPiCodeWD_code (BF.Pi.succ hl hψ)
          (BF.nodupBlocks_of_blockVars_nodup hg.2.2.2.1))]
        refine trPi_step hWt hg ?_
        intro b' hg'
        cases hψ with
        | zero hφ => exact trMPi_correct hWt hbase hφ hg'
  | n + 2 =>
    constructor
    · intro hs a hg
      cases hs with
      | succ hl hψ =>
        rw [trSigS_add_two, and_iff_right (isSigCodeWD_code (BF.Sig.succ hl hψ)
          (BF.nodupBlocks_of_blockVars_nodup hg.2.2.2.1))]
        refine trSig_step hWt hg ?_
        intro b' hg'
        exact (ih (n + 1) (by omega) _).2 hψ b' hg'
    · intro hs a hg
      cases hs with
      | succ hl hψ =>
        rw [trPiS_add_two, and_iff_right (isPiCodeWD_code (BF.Pi.succ hl hψ)
          (BF.nodupBlocks_of_blockVars_nodup hg.2.2.2.1))]
        refine trPi_step hWt hg ?_
        intro b' hg'
        exact (ih (n + 1) (by omega) _).1 hψ b' hg'

/-- **Theorem 13.6** (Σ side): for a `Σ̂q` block formula `b` and a good assignment `a`, the
truth predicate `TrSigS` applied to the code of `b` expresses satisfaction of `b` in `W`. -/
theorem trSigS_correct {W : ZFSet.{u}} (hWt : W.IsTransitive) (hbase : BaseCorrect W) :
    ∀ (q : ℕ) (b : BF), BF.Sig q b → ∀ a, GoodAsn W b a →
      (TrSigS (· ∈ W) (L Ordinal.omega0) ωZ q (BF.code b) a ↔
        Sat (· ∈ W) (SeqVal a) b.toFm) :=
  fun q b => (trSigPiS_correct hWt hbase q b).1

/-- **Theorem 13.6** (Π side). -/
theorem trPiS_correct {W : ZFSet.{u}} (hWt : W.IsTransitive) (hbase : BaseCorrect W) :
    ∀ (q : ℕ) (b : BF), BF.Pi q b → ∀ a, GoodAsn W b a →
      (TrPiS (· ∈ W) (L Ordinal.omega0) ωZ q (BF.code b) a ↔
        Sat (· ∈ W) (SeqVal a) b.toFm) :=
  fun q b => (trSigPiS_correct hWt hbase q b).2


/-! ### Theorem 13.6 in the external universe

The last sentence of Theorem 13.6, 「同じ同値は外部宇宙 V でも成立する」.  The proof is the same
induction, with the domain `(· ∈ W)` replaced by `V = fun _ => True`; the auxiliary lemmas about
block updates are reused by choosing, for each individual witness, a rank initial segment `V_γ`
that contains it. -/

/-- Any two sets lie in a common transitive `WClosed` set, namely a rank initial segment `V_γ`
with `γ` a limit ordinal above both ranks. -/
theorem exists_wClosed_mem (x y : ZFSet.{u}) :
    ∃ W : ZFSet.{u}, W.IsTransitive ∧ WClosed W ∧ x ∈ W ∧ y ∈ W := by
  set γ : Ordinal.{u} := max (ZFSet.rank x) (ZFSet.rank y) + Ordinal.omega0 with hγ
  have hlim : Order.IsSuccLimit γ := Ordinal.isSuccLimit_add _ Ordinal.isSuccLimit_omega0
  have hbase : max (ZFSet.rank x) (ZFSet.rank y) < γ := lt_add_of_pos_right _ Ordinal.omega0_pos
  refine ⟨ZFSet.vonNeumann γ, ZFSet.isTransitive_vonNeumann γ, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [ZFSet.mem_vonNeumann, ZFSet.rank_empty]
    exact lt_of_le_of_lt (Ordinal.bot_eq_zero ▸ bot_le) hbase
  · intro u hu v hv
    rw [ZFSet.mem_vonNeumann] at hu hv ⊢
    rw [ZFSet.rank_insert]
    exact max_lt (hlim.succ_lt hu) hv
  · rw [ZFSet.mem_vonNeumann]; exact lt_of_le_of_lt (le_max_left _ _) hbase
  · rw [ZFSet.mem_vonNeumann]; exact lt_of_le_of_lt (le_max_right _ _) hbase

/-- A finite sequence of `V` that lies in a transitive `W` is a finite sequence over `W`. -/
theorem isSeqA_of_isSeqV {W a : ZFSet.{u}} (hWt : W.IsTransitive) (ha : IsSeqV ωZ a)
    (haW : a ∈ W) : IsSeqA ωZ W a :=
  ⟨ha.1, ha.2, fun _ _ hix => snd_mem_of_kpair_mem hWt (hWt.subset_of_mem haW hix)⟩

/-- The entries of a list whose coded sequence lies in a transitive `W` lie in `W`. -/
theorem mem_of_seqOfVals_mem {W : ZFSet.{u}} (hWt : W.IsTransitive) {xs : List ZFSet.{u}}
    (h : seqOfVals xs ∈ W) : ∀ x ∈ xs, x ∈ W := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  exact snd_mem_of_kpair_mem hWt (hWt.subset_of_mem h (mem_seqOfVals hk))

/-- `GoodAsn` in the external universe: the clauses `a ∈ W` and `BF.code b ∈ W` and the closure
of `W` are all vacuous in `V`, so only the two clauses of the statement of Theorem 13.6 and the
block-distinctness clause remain. -/
def GoodAsnV (b : BF) (a : ZFSet.{u}) : Prop :=
  IsSeqV ωZ a ∧ (∀ i ∈ b.blockVars, ∃ y, ZFSet.pair (natZ.{u} i) y ∈ a) ∧ b.blockVars.Nodup

theorem trMSig_correct_V (hbase : BaseCorrectV.{u}) {sg : Bool} {φ : Fm} (hφ : IsDelta0 φ)
    {a : ZFSet.{u}} (ha : IsSeqV ωZ a) :
    TrMSig (fun _ => True) (L Ordinal.omega0) ωZ (BF.code.{u} (BF.delta sg φ)) a ↔
      SatV (SeqVal a) (BF.delta sg φ).toFm := by
  obtain ⟨hP, hN⟩ := hbase φ hφ a ha
  refine Iff.trans (and_iff_right (isDeltaBFCodeW_code (sg := sg) hφ)) ?_
  cases sg
  · rw [code_delta_false, toFm_delta_false, SatV, sat_not]
    constructor
    · rintro ⟨sg', -, d, -, heq, hcase⟩
      obtain ⟨-, heq2⟩ := ZFSet.pair_injective heq
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective heq2
      rcases hcase with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd (natZ_injective h1) (by decide)
      · exact fun hs => h2 (hN.mpr hs)
    · intro hs
      exact ⟨natZ 0, trivial, Fm.code.{u} φ, trivial, rfl, Or.inr ⟨rfl, fun h => hs (hN.mp h)⟩⟩
  · rw [code_delta_true, toFm_delta_true]
    constructor
    · rintro ⟨sg', -, d, -, heq, hcase⟩
      obtain ⟨-, heq2⟩ := ZFSet.pair_injective heq
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective heq2
      rcases hcase with ⟨-, h1⟩ | ⟨h2, -⟩
      · exact hP.mp h1
      · exact absurd (natZ_injective h2) (by decide)
    · intro hs
      exact ⟨natZ 1, trivial, Fm.code.{u} φ, trivial, rfl, Or.inl ⟨rfl, hP.mpr hs⟩⟩

theorem trMPi_correct_V (hbase : BaseCorrectV.{u}) {sg : Bool} {φ : Fm} (hφ : IsDelta0 φ)
    {a : ZFSet.{u}} (ha : IsSeqV ωZ a) :
    TrMPi (fun _ => True) (L Ordinal.omega0) ωZ (BF.code.{u} (BF.delta sg φ)) a ↔
      SatV (SeqVal a) (BF.delta sg φ).toFm := by
  obtain ⟨hP, hN⟩ := hbase φ hφ a ha
  refine Iff.trans (and_iff_right (isDeltaBFCodeW_code (sg := sg) hφ)) ?_
  cases sg
  · rw [code_delta_false, toFm_delta_false, SatV, sat_not]
    constructor
    · intro H
      obtain ⟨-, h2⟩ := H (natZ 0) trivial (Fm.code.{u} φ) trivial rfl
      exact fun hs => h2 rfl (hP.mpr hs)
    · intro hs sg' _ d _ heq
      obtain ⟨-, heq2⟩ := ZFSet.pair_injective heq
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective heq2
      exact ⟨fun h1 => absurd (natZ_injective h1) (by decide), fun _ h => hs (hP.mp h)⟩
  · rw [code_delta_true, toFm_delta_true]
    constructor
    · intro H
      obtain ⟨h1, -⟩ := H (natZ 1) trivial (Fm.code.{u} φ) trivial rfl
      exact hN.mp (h1 rfl)
    · intro hs sg' _ d _ heq
      obtain ⟨-, heq2⟩ := ZFSet.pair_injective heq
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective heq2
      exact ⟨fun _ => hN.mpr hs, fun h0 => absurd (natZ_injective h0) (by decide)⟩

theorem trSig_step_V {l : List ℕ} {ψ : BF} {a : ZFSet.{u}} (hg : GoodAsnV (BF.exs l ψ) a)
    {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (hP : ∀ b, GoodAsnV ψ b → (P (BF.code.{u} ψ) b ↔ SatV (SeqVal b) ψ.toFm)) :
    (∃ ν, True ∧ ∃ d, True ∧ ∃ t, True ∧ ∃ b, True ∧
        BF.code.{u} (BF.exs l ψ) = ZFSet.pair (natZ 1) (ZFSet.pair ν d) ∧
        IsBlkUpd a ν t b ∧ P d b) ↔
      SatV (SeqVal a) (BF.exs l ψ).toFm := by
  obtain ⟨ha, hdom, hnd⟩ := hg
  simp only [BF.blockVars] at hdom hnd
  have hndl : l.Nodup := (List.nodup_append.mp hnd).1
  have hndψ : ψ.blockVars.Nodup := (List.nodup_append.mp hnd).2.1
  have hdoml : ∀ i ∈ l, ∃ y, ZFSet.pair (natZ.{u} i) y ∈ a :=
    fun i hi => hdom i (List.mem_append_left _ hi)
  have hdomψ : ∀ i ∈ ψ.blockVars, ∃ y, ZFSet.pair (natZ.{u} i) y ∈ a :=
    fun i hi => hdom i (List.mem_append_right _ hi)
  rw [toFm_exs, SatV, sat_exs_iff_exsD, exsD_iff_exists_list]
  constructor
  · rintro ⟨ν, -, d, -, t, -, b, -, heq, hbu, hPd⟩
    rw [code_exs] at heq
    obtain ⟨-, heq2⟩ := ZFSet.pair_injective heq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective heq2
    obtain ⟨W, hWt, hW, haW, htW⟩ := exists_wClosed_mem a t
    obtain ⟨xs, hlen, -, hseqb, hvalb⟩ :=
      blkUpd_list hWt hW (isSeqA_of_isSeqV hWt ha haW) hndl hdoml htW hbu
    refine ⟨xs, hlen, fun _ _ => trivial, ?_⟩
    rw [← hvalb]
    exact (hP b ⟨isSeqV_of_isSeqA hseqb, fun i hi => blkUpd_dom_mono hbu (hdomψ i hi),
      hndψ⟩).mp hPd
  · rintro ⟨xs, hlen, -, hsat⟩
    obtain ⟨W, hWt, hW, haW, hvW⟩ := exists_wClosed_mem a (seqOfVals xs)
    obtain ⟨b, hbu, hseqb, -, hvalb⟩ := exists_blkUpd_W hW (isSeqA_of_isSeqV hWt ha haW) hndl
      hdoml hlen (mem_of_seqOfVals_mem hWt hvW)
    refine ⟨seqOfNats.{u} l, trivial, BF.code.{u} ψ, trivial, seqOfVals xs, trivial, b, trivial,
      code_exs l ψ, hbu, ?_⟩
    refine (hP b ⟨isSeqV_of_isSeqA hseqb, fun i hi => blkUpd_dom_mono hbu (hdomψ i hi),
      hndψ⟩).mpr ?_
    rw [hvalb]
    exact hsat

theorem trPi_step_V {l : List ℕ} {ψ : BF} {a : ZFSet.{u}} (hg : GoodAsnV (BF.alls l ψ) a)
    {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (hP : ∀ b, GoodAsnV ψ b → (P (BF.code.{u} ψ) b ↔ SatV (SeqVal b) ψ.toFm)) :
    (∀ ν, True → ∀ d, True → ∀ t, True → ∀ b, True →
        BF.code.{u} (BF.alls l ψ) = ZFSet.pair (natZ 2) (ZFSet.pair ν d) →
        IsBlkUpd a ν t b → P d b) ↔
      SatV (SeqVal a) (BF.alls l ψ).toFm := by
  obtain ⟨ha, hdom, hnd⟩ := hg
  simp only [BF.blockVars] at hdom hnd
  have hndl : l.Nodup := (List.nodup_append.mp hnd).1
  have hndψ : ψ.blockVars.Nodup := (List.nodup_append.mp hnd).2.1
  have hdoml : ∀ i ∈ l, ∃ y, ZFSet.pair (natZ.{u} i) y ∈ a :=
    fun i hi => hdom i (List.mem_append_left _ hi)
  have hdomψ : ∀ i ∈ ψ.blockVars, ∃ y, ZFSet.pair (natZ.{u} i) y ∈ a :=
    fun i hi => hdom i (List.mem_append_right _ hi)
  rw [toFm_alls, SatV, sat_alls_iff_allD, allD_iff_forall_list]
  constructor
  · intro H xs hlen _
    obtain ⟨W, hWt, hW, haW, hvW⟩ := exists_wClosed_mem a (seqOfVals xs)
    obtain ⟨b, hbu, hseqb, -, hvalb⟩ := exists_blkUpd_W hW (isSeqA_of_isSeqV hWt ha haW) hndl
      hdoml hlen (mem_of_seqOfVals_mem hWt hvW)
    have hPd := H (seqOfNats.{u} l) trivial (BF.code.{u} ψ) trivial (seqOfVals xs) trivial b
      trivial (code_alls l ψ) hbu
    rw [← hvalb]
    exact (hP b ⟨isSeqV_of_isSeqA hseqb, fun i hi => blkUpd_dom_mono hbu (hdomψ i hi),
      hndψ⟩).mp hPd
  · intro H ν _ d _ t _ b _ heq hbu
    rw [code_alls] at heq
    obtain ⟨-, heq2⟩ := ZFSet.pair_injective heq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective heq2
    obtain ⟨W, hWt, hW, haW, htW⟩ := exists_wClosed_mem a t
    obtain ⟨xs, hlen, -, hseqb, hvalb⟩ :=
      blkUpd_list hWt hW (isSeqA_of_isSeqV hWt ha haW) hndl hdoml htW hbu
    refine (hP b ⟨isSeqV_of_isSeqA hseqb, fun i hi => blkUpd_dom_mono hbu (hdomψ i hi),
      hndψ⟩).mpr ?_
    rw [hvalb]
    exact H xs hlen (fun _ _ => trivial)

/-- The two halves of **Theorem 13.6** in the external universe `V`. -/
theorem trSigPiS_correct_V (hbase : BaseCorrectV.{u}) :
    ∀ (q : ℕ) (b : BF),
      (BF.Sig q b → ∀ a, GoodAsnV b a →
        (TrSigS (fun _ => True) (L Ordinal.omega0) ωZ q (BF.code.{u} b) a ↔
          SatV (SeqVal a) b.toFm)) ∧
      (BF.Pi q b → ∀ a, GoodAsnV b a →
        (TrPiS (fun _ => True) (L Ordinal.omega0) ωZ q (BF.code.{u} b) a ↔
          SatV (SeqVal a) b.toFm)) := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro b
  match q with
  | 0 =>
    constructor
    · intro hs a hg
      cases hs with
      | zero hφ => rw [trSigS_zero]; exact trMSig_correct_V hbase hφ hg.1
    · intro hs a hg
      cases hs with
      | zero hφ => rw [trPiS_zero]; exact trMPi_correct_V hbase hφ hg.1
  | 1 =>
    constructor
    · intro hs a hg
      cases hs with
      | succ hl hψ =>
        rw [trSigS_one, and_iff_right (isSigCodeWD_code (BF.Sig.succ hl hψ)
          (BF.nodupBlocks_of_blockVars_nodup hg.2.2))]
        refine trSig_step_V hg ?_
        intro b' hg'
        cases hψ with
        | zero hφ => exact trMSig_correct_V hbase hφ hg'.1
    · intro hs a hg
      cases hs with
      | succ hl hψ =>
        rw [trPiS_one, and_iff_right (isPiCodeWD_code (BF.Pi.succ hl hψ)
          (BF.nodupBlocks_of_blockVars_nodup hg.2.2))]
        refine trPi_step_V hg ?_
        intro b' hg'
        cases hψ with
        | zero hφ => exact trMPi_correct_V hbase hφ hg'.1
  | n + 2 =>
    constructor
    · intro hs a hg
      cases hs with
      | succ hl hψ =>
        rw [trSigS_add_two, and_iff_right (isSigCodeWD_code (BF.Sig.succ hl hψ)
          (BF.nodupBlocks_of_blockVars_nodup hg.2.2))]
        refine trSig_step_V hg ?_
        intro b' hg'
        exact (ih (n + 1) (by omega) _).2 hψ b' hg'
    · intro hs a hg
      cases hs with
      | succ hl hψ =>
        rw [trPiS_add_two, and_iff_right (isPiCodeWD_code (BF.Pi.succ hl hψ)
          (BF.nodupBlocks_of_blockVars_nodup hg.2.2))]
        refine trPi_step_V hg ?_
        intro b' hg'
        exact (ih (n + 1) (by omega) _).1 hψ b' hg'

/-- **Theorem 13.6** (Σ side) in the external universe `V`. -/
theorem trSigS_correct_V (hbase : BaseCorrectV.{u}) :
    ∀ (q : ℕ) (b : BF), BF.Sig q b → ∀ a : ZFSet.{u}, GoodAsnV b a →
      (TrSigS (fun _ => True) (L Ordinal.omega0) ωZ q (BF.code b) a ↔
        SatV (SeqVal a) b.toFm) :=
  fun q b => (trSigPiS_correct_V hbase q b).1

/-- **Theorem 13.6** (Π side) in the external universe `V`. -/
theorem trPiS_correct_V (hbase : BaseCorrectV.{u}) :
    ∀ (q : ℕ) (b : BF), BF.Pi q b → ∀ a : ZFSet.{u}, GoodAsnV b a →
      (TrPiS (fun _ => True) (L Ordinal.omega0) ωZ q (BF.code b) a ↔
        SatV (SeqVal a) b.toFm) :=
  fun q b => (trSigPiS_correct_V hbase q b).2

end BM4.ST
