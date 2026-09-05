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


/-- A finite sequence of `V` that lies in a transitive `W` is a finite sequence over `W`. -/
theorem isSeqA_of_isSeqV {W a : ZFSet.{u}} (hWt : W.IsTransitive) (ha : IsSeqV ωZ a)
    (haW : a ∈ W) : IsSeqA ωZ W a :=
  ⟨ha.1, ha.2, fun _ _ hix => snd_mem_of_kpair_mem hWt (hWt.subset_of_mem haW hix)⟩

/-! ### The Δ₀ base under the `∅`-padding of `TrMSig` and `TrMPi`

Definition 13.2 judges only *appropriate* assignments: `Tr⁺_{Δ₀}(e, a)` carries `Asn_A(e, a)`,
so an `a` whose domain misses a free variable of `e` is never judged, and Lemma 13.3
(`BaseCorrect`) assumes the same.  `TrMSig` and `TrMPi` therefore evaluate the base at an
`∅`-padding of `a`; padding leaves every value unchanged, so these five lemmas move the
equivalence of Lemma 13.3 from the appropriate assignment to an arbitrary finite sequence. -/

/-- A bound above every free variable of `φ`. -/
theorem exists_fv_bound (φ : Fm) : ∃ n, ∀ k ∈ Fm.fv φ, k < n :=
  ⟨(Fm.fv φ).sup (fun k => k + 1), fun _ hk => Finset.le_sup (f := fun k => k + 1) hk⟩

/-- An `∅`-padding of `a` inside `W` that is an appropriate assignment for `φ`. -/
theorem exists_padAsn {W : ZFSet.{u}} (hW : WClosed W) {a : ZFSet.{u}} (ha : IsSeqA ωZ W a)
    (φ : Fm) :
    ∃ b, b ∈ W ∧ IsSeqA ωZ W b ∧ IsPadOf a b ∧ SeqVal b = SeqVal a ∧
      ∀ k ∈ Fm.fv φ, InDomZ b (natZ k) := by
  obtain ⟨n, hn⟩ := exists_fv_bound φ
  obtain ⟨b, hb, hpad, hval, hdom⟩ := exists_padSeq ha hW.empty_mem n
  exact ⟨b, isSeqA_mem_of_wClosed hW hb, hb, hpad, hval, fun k hk => hdom k (hn k hk)⟩

/-- `Tr⁺_{Δ₀}` at a padding of `a` implies satisfaction: the `Asn_A` conjunct of Definition
13.2 makes that padding an appropriate assignment. -/
theorem sat_of_pad_trD0P {W : ZFSet.{u}} (hWt : W.IsTransitive) (hbase : BaseCorrect W)
    {φ : Fm} (hφ : IsDelta0 φ) {a b : ZFSet.{u}} (ha : IsSeqA ωZ W a) (hbW : b ∈ W)
    (hpad : IsPadOf a b) (h : TrD0P (· ∈ W) (L Ordinal.omega0) ωZ (Fm.code.{u} φ) b) :
    Sat (· ∈ W) (SeqVal a) φ := by
  obtain ⟨-, A, -, U, -, T, -, -, hasn, -, -, -⟩ := id h
  obtain ⟨hbA, hcov⟩ := isAsn_code_iff.mp hasn
  have hbseq : IsSeqA ωZ W b := isSeqA_of_isSeqV hWt (isSeqV_of_isSeqA hbA) hbW
  have hval : SeqVal b = SeqVal a := seqVal_of_isPadOf ha.1 hbA.1 hpad
  rw [← hval]
  exact ((hbase φ hφ b hbseq hbW hcov).1).mp h

/-- Satisfaction implies `Tr⁻_{Δ₀}` at every padding of `a` in `W`. -/
theorem pad_trD0N_of_sat {W : ZFSet.{u}} (hWt : W.IsTransitive) (hbase : BaseCorrect W)
    {φ : Fm} (hφ : IsDelta0 φ) {a b : ZFSet.{u}} (ha : IsSeqA ωZ W a) (hbW : b ∈ W)
    (hpad : IsPadOf a b) (hs : Sat (· ∈ W) (SeqVal a) φ) :
    TrD0N (· ∈ W) (L Ordinal.omega0) ωZ (Fm.code.{u} φ) b := by
  refine ⟨(isDelta0CodeW_iff _).mpr ⟨φ, hφ, rfl⟩, ?_⟩
  rintro A hA U hU T hT ⟨hAt, hasn, hbU, hc⟩
  obtain ⟨hbA, hcov⟩ := isAsn_code_iff.mp hasn
  have hbseq : IsSeqA ωZ W b := isSeqA_of_isSeqV hWt (isSeqV_of_isSeqA hbA) hbW
  have hval : SeqVal b = SeqVal a := seqVal_of_isPadOf ha.1 hbA.1 hpad
  refine ((hbase φ hφ b hbseq hbW hcov).2.mpr ?_).2 A hA U hU T hT ⟨hAt, hasn, hbU, hc⟩
  rw [hval]; exact hs

/-- Satisfaction is witnessed by `Tr⁺_{Δ₀}` at some padding of `a` in `W`. -/
theorem exists_pad_trD0P_of_sat {W : ZFSet.{u}} (hW : WClosed W) (hbase : BaseCorrect W)
    {φ : Fm} (hφ : IsDelta0 φ) {a : ZFSet.{u}} (ha : IsSeqA ωZ W a)
    (hs : Sat (· ∈ W) (SeqVal a) φ) :
    ∃ b, b ∈ W ∧ IsPadOf a b ∧ TrD0P (· ∈ W) (L Ordinal.omega0) ωZ (Fm.code.{u} φ) b := by
  obtain ⟨b, hbW, hbseq, hpad, hval, hcov⟩ := exists_padAsn hW ha φ
  exact ⟨b, hbW, hpad, ((hbase φ hφ b hbseq hbW hcov).1).mpr (by rw [hval]; exact hs)⟩

/-- Failure of satisfaction is witnessed by the failure of `Tr⁻_{Δ₀}` at some padding. -/
theorem exists_pad_not_trD0N_of_not_sat {W : ZFSet.{u}} (hW : WClosed W)
    (hbase : BaseCorrect W) {φ : Fm} (hφ : IsDelta0 φ) {a : ZFSet.{u}} (ha : IsSeqA ωZ W a)
    (hs : ¬ Sat (· ∈ W) (SeqVal a) φ) :
    ∃ b, b ∈ W ∧ IsPadOf a b ∧ ¬ TrD0N (· ∈ W) (L Ordinal.omega0) ωZ (Fm.code.{u} φ) b := by
  obtain ⟨b, hbW, hbseq, hpad, hval, hcov⟩ := exists_padAsn hW ha φ
  refine ⟨b, hbW, hpad, fun h => hs ?_⟩
  rw [← hval]
  exact ((hbase φ hφ b hbseq hbW hcov).2).mp h

/-! ### Block updates inside `W` -/

/-! ### Good assignments -/

/-- The block variables of a block formula. -/
def BF.blockVars : BF → List ℕ
  | .delta _ _ => []
  | .exs l ψ => l ++ ψ.blockVars
  | .alls l ψ => l ++ ψ.blockVars

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
    {sg : Bool} {φ : Fm} (hφ : IsDelta0 φ) {a : ZFSet.{u}} (ha : IsSeqA ωZ W a)
    (haW : a ∈ W) (hcode : BF.code.{u} (BF.delta sg φ) ∈ W) (hW : WClosed W) :
    TrMSig (· ∈ W) (L Ordinal.omega0) ωZ (BF.code.{u} (BF.delta sg φ)) a ↔
      Sat (· ∈ W) (SeqVal a) (BF.delta sg φ).toFm := by
  have hdW : Fm.code.{u} φ ∈ W := by
    simp only [BF.code] at hcode
    exact snd_mem_of_kpair_mem hWt (snd_mem_of_kpair_mem hWt hcode)
  have hz : natZ.{u} 0 ∈ W := hW.natZ_mem 0
  have ho : natZ.{u} 1 ∈ W := hW.natZ_mem 1
  refine Iff.trans (and_iff_right (isDeltaBFCodeW_code (sg := sg) hφ)) ?_
  cases sg
  · rw [code_delta_false, toFm_delta_false, sat_not]
    constructor
    · rintro ⟨sg', -, d, -, heq, b, hbW, hpad, hcase⟩
      obtain ⟨-, heq2⟩ := ZFSet.pair_injective heq
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective heq2
      rcases hcase with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd (natZ_injective h1) (by decide)
      · exact fun hs => h2 (pad_trD0N_of_sat hWt hbase hφ ha hbW hpad hs)
    · intro hs
      obtain ⟨b, hbW, hpad, h2⟩ := exists_pad_not_trD0N_of_not_sat hW hbase hφ ha hs
      exact ⟨natZ 0, hz, Fm.code.{u} φ, hdW, rfl, b, hbW, hpad, Or.inr ⟨rfl, h2⟩⟩
  · rw [code_delta_true, toFm_delta_true]
    constructor
    · rintro ⟨sg', -, d, -, heq, b, hbW, hpad, hcase⟩
      obtain ⟨-, heq2⟩ := ZFSet.pair_injective heq
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective heq2
      rcases hcase with ⟨-, h1⟩ | ⟨h2, -⟩
      · exact sat_of_pad_trD0P hWt hbase hφ ha hbW hpad h1
      · exact absurd (natZ_injective h2) (by decide)
    · intro hs
      obtain ⟨b, hbW, hpad, h1⟩ := exists_pad_trD0P_of_sat hW hbase hφ ha hs
      exact ⟨natZ 1, ho, Fm.code.{u} φ, hdW, rfl, b, hbW, hpad, Or.inl ⟨rfl, h1⟩⟩

theorem trMPi_correct {W : ZFSet.{u}} (hWt : W.IsTransitive) (hbase : BaseCorrect W)
    {sg : Bool} {φ : Fm} (hφ : IsDelta0 φ) {a : ZFSet.{u}} (ha : IsSeqA ωZ W a)
    (haW : a ∈ W) (hcode : BF.code.{u} (BF.delta sg φ) ∈ W) (hW : WClosed W) :
    TrMPi (· ∈ W) (L Ordinal.omega0) ωZ (BF.code.{u} (BF.delta sg φ)) a ↔
      Sat (· ∈ W) (SeqVal a) (BF.delta sg φ).toFm := by
  have hdW : Fm.code.{u} φ ∈ W := by
    simp only [BF.code] at hcode
    exact snd_mem_of_kpair_mem hWt (snd_mem_of_kpair_mem hWt hcode)
  have hz : natZ.{u} 0 ∈ W := hW.natZ_mem 0
  have ho : natZ.{u} 1 ∈ W := hW.natZ_mem 1
  refine Iff.trans (and_iff_right (isDeltaBFCodeW_code (sg := sg) hφ)) ?_
  cases sg
  · rw [code_delta_false, toFm_delta_false, sat_not]
    constructor
    · intro H hs
      obtain ⟨b, hbW, hpad, h1⟩ := exists_pad_trD0P_of_sat hW hbase hφ ha hs
      exact (H (natZ 0) hz (Fm.code.{u} φ) hdW rfl b hbW hpad).2 rfl h1
    · rintro hs sg' - d - heq b hbW hpad
      obtain ⟨-, heq2⟩ := ZFSet.pair_injective heq
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective heq2
      exact ⟨fun h1 => absurd (natZ_injective h1) (by decide),
        fun _ h => hs (sat_of_pad_trD0P hWt hbase hφ ha hbW hpad h)⟩
  · rw [code_delta_true, toFm_delta_true]
    constructor
    · intro H
      by_contra hs
      obtain ⟨b, hbW, hpad, h2⟩ := exists_pad_not_trD0N_of_not_sat hW hbase hφ ha hs
      exact h2 ((H (natZ 1) ho (Fm.code.{u} φ) hdW rfl b hbW hpad).1 rfl)
    · rintro hs sg' - d - heq b hbW hpad
      obtain ⟨-, heq2⟩ := ZFSet.pair_injective heq
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective heq2
      exact ⟨fun _ => pad_trD0N_of_sat hWt hbase hφ ha hbW hpad hs,
        fun h0 => absurd (natZ_injective h0) (by decide)⟩


/-! ### The quantifier-block step -/

theorem code_exs (l : List ℕ) (ψ : BF) : BF.code.{u} (BF.exs l ψ) =
    ZFSet.pair (natZ 1) (ZFSet.pair (seqOfNats.{u} l) (BF.code.{u} ψ)) := rfl

theorem code_alls (l : List ℕ) (ψ : BF) : BF.code.{u} (BF.alls l ψ) =
    ZFSet.pair (natZ 2) (ZFSet.pair (seqOfNats.{u} l) (BF.code.{u} ψ)) := rfl

theorem toFm_exs (l : List ℕ) (ψ : BF) : (BF.exs l ψ).toFm = Fm.exs l ψ.toFm := rfl

theorem toFm_alls (l : List ℕ) (ψ : BF) : (BF.alls l ψ).toFm = Fm.alls l ψ.toFm := rfl

/-! ### Theorem 13.6 -/

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

/-- The entries of a list whose coded sequence lies in a transitive `W` lie in `W`. -/
theorem mem_of_seqOfVals_mem {W : ZFSet.{u}} (hWt : W.IsTransitive) {xs : List ZFSet.{u}}
    (h : seqOfVals xs ∈ W) : ∀ x ∈ xs, x ∈ W := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  exact snd_mem_of_kpair_mem hWt (hWt.subset_of_mem h (mem_seqOfVals hk))

/-! #### The Δ₀ base under the padding, in `V` -/

/-- An `∅`-padding of `a` that is an appropriate assignment for `φ`, built in ZFC. -/
theorem exists_padAsn_V {a : ZFSet.{u}} (ha : IsSeqV ωZ a) (φ : Fm) :
    ∃ b, IsSeqV ωZ b ∧ IsPadOf a b ∧ SeqVal b = SeqVal a ∧
      ∀ k ∈ Fm.fv φ, InDomZ b (natZ k) := by
  obtain ⟨n, hn⟩ := exists_fv_bound φ
  obtain ⟨A, hAt, hAcl, haA, -⟩ := exists_wClosed_mem a a
  obtain ⟨b, hb, hpad, hval, hdom⟩ :=
    exists_padSeq (isSeqA_of_isSeqV hAt ha haA) hAcl.empty_mem n
  exact ⟨b, isSeqV_of_isSeqA hb, hpad, hval, fun k hk => hdom k (hn k hk)⟩

/-- `Tr⁺_{Δ₀}` at a padding of `a` implies satisfaction in `V`. -/
theorem satV_of_pad_trD0P (hbase : BaseCorrectV.{u}) {φ : Fm} (hφ : IsDelta0 φ)
    {a b : ZFSet.{u}} (ha : IsSeqV ωZ a) (hpad : IsPadOf a b)
    (h : TrD0P (fun _ => True) (L Ordinal.omega0) ωZ (Fm.code.{u} φ) b) :
    SatV (SeqVal a) φ := by
  obtain ⟨-, A, -, U, -, T, -, -, hasn, -, -, -⟩ := id h
  obtain ⟨hbA, hcov⟩ := isAsn_code_iff.mp hasn
  have hval : SeqVal b = SeqVal a := seqVal_of_isPadOf ha.1 hbA.1 hpad
  rw [← hval]
  exact ((hbase φ hφ b (isSeqV_of_isSeqA hbA) hcov).1).mp h

/-- Satisfaction in `V` implies `Tr⁻_{Δ₀}` at every padding of `a`. -/
theorem pad_trD0N_of_satV (hbase : BaseCorrectV.{u}) {φ : Fm} (hφ : IsDelta0 φ)
    {a b : ZFSet.{u}} (ha : IsSeqV ωZ a) (hpad : IsPadOf a b) (hs : SatV (SeqVal a) φ) :
    TrD0N (fun _ => True) (L Ordinal.omega0) ωZ (Fm.code.{u} φ) b := by
  refine ⟨(isDelta0CodeW_iff _).mpr ⟨φ, hφ, rfl⟩, ?_⟩
  rintro A - U - T - ⟨hAt, hasn, hbU, hc⟩
  obtain ⟨hbA, hcov⟩ := isAsn_code_iff.mp hasn
  have hval : SeqVal b = SeqVal a := seqVal_of_isPadOf ha.1 hbA.1 hpad
  refine ((hbase φ hφ b (isSeqV_of_isSeqA hbA) hcov).2.mpr ?_).2 A trivial U trivial T trivial
    ⟨hAt, hasn, hbU, hc⟩
  rw [hval]; exact hs

/-- Satisfaction in `V` is witnessed by `Tr⁺_{Δ₀}` at some padding of `a`. -/
theorem exists_pad_trD0P_of_satV (hbase : BaseCorrectV.{u}) {φ : Fm} (hφ : IsDelta0 φ)
    {a : ZFSet.{u}} (ha : IsSeqV ωZ a) (hs : SatV (SeqVal a) φ) :
    ∃ b, IsPadOf a b ∧ TrD0P (fun _ => True) (L Ordinal.omega0) ωZ (Fm.code.{u} φ) b := by
  obtain ⟨b, hbseq, hpad, hval, hcov⟩ := exists_padAsn_V ha φ
  exact ⟨b, hpad, ((hbase φ hφ b hbseq hcov).1).mpr (by rw [hval]; exact hs)⟩

/-- Failure of satisfaction in `V` is witnessed by the failure of `Tr⁻_{Δ₀}` at some padding. -/
theorem exists_pad_not_trD0N_of_not_satV (hbase : BaseCorrectV.{u}) {φ : Fm}
    (hφ : IsDelta0 φ) {a : ZFSet.{u}} (ha : IsSeqV ωZ a) (hs : ¬ SatV (SeqVal a) φ) :
    ∃ b, IsPadOf a b ∧ ¬ TrD0N (fun _ => True) (L Ordinal.omega0) ωZ (Fm.code.{u} φ) b := by
  obtain ⟨b, hbseq, hpad, hval, hcov⟩ := exists_padAsn_V ha φ
  refine ⟨b, hpad, fun h => hs ?_⟩
  rw [← hval]
  exact ((hbase φ hφ b hbseq hcov).2).mp h

theorem trMSig_correct_V (hbase : BaseCorrectV.{u}) {sg : Bool} {φ : Fm} (hφ : IsDelta0 φ)
    {a : ZFSet.{u}} (ha : IsSeqV ωZ a) :
    TrMSig (fun _ => True) (L Ordinal.omega0) ωZ (BF.code.{u} (BF.delta sg φ)) a ↔
      SatV (SeqVal a) (BF.delta sg φ).toFm := by
  refine Iff.trans (and_iff_right (isDeltaBFCodeW_code (sg := sg) hφ)) ?_
  cases sg
  · rw [code_delta_false, toFm_delta_false, SatV, sat_not]
    constructor
    · rintro ⟨sg', -, d, -, heq, b, -, hpad, hcase⟩
      obtain ⟨-, heq2⟩ := ZFSet.pair_injective heq
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective heq2
      rcases hcase with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd (natZ_injective h1) (by decide)
      · exact fun hs => h2 (pad_trD0N_of_satV hbase hφ ha hpad hs)
    · intro hs
      obtain ⟨b, hpad, h2⟩ := exists_pad_not_trD0N_of_not_satV hbase hφ ha hs
      exact ⟨natZ 0, trivial, Fm.code.{u} φ, trivial, rfl, b, trivial, hpad, Or.inr ⟨rfl, h2⟩⟩
  · rw [code_delta_true, toFm_delta_true]
    constructor
    · rintro ⟨sg', -, d, -, heq, b, -, hpad, hcase⟩
      obtain ⟨-, heq2⟩ := ZFSet.pair_injective heq
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective heq2
      rcases hcase with ⟨-, h1⟩ | ⟨h2, -⟩
      · exact satV_of_pad_trD0P hbase hφ ha hpad h1
      · exact absurd (natZ_injective h2) (by decide)
    · intro hs
      obtain ⟨b, hpad, h1⟩ := exists_pad_trD0P_of_satV hbase hφ ha hs
      exact ⟨natZ 1, trivial, Fm.code.{u} φ, trivial, rfl, b, trivial, hpad, Or.inl ⟨rfl, h1⟩⟩

theorem trMPi_correct_V (hbase : BaseCorrectV.{u}) {sg : Bool} {φ : Fm} (hφ : IsDelta0 φ)
    {a : ZFSet.{u}} (ha : IsSeqV ωZ a) :
    TrMPi (fun _ => True) (L Ordinal.omega0) ωZ (BF.code.{u} (BF.delta sg φ)) a ↔
      SatV (SeqVal a) (BF.delta sg φ).toFm := by
  refine Iff.trans (and_iff_right (isDeltaBFCodeW_code (sg := sg) hφ)) ?_
  cases sg
  · rw [code_delta_false, toFm_delta_false, SatV, sat_not]
    constructor
    · intro H hs
      obtain ⟨b, hpad, h1⟩ := exists_pad_trD0P_of_satV hbase hφ ha hs
      exact (H (natZ 0) trivial (Fm.code.{u} φ) trivial rfl b trivial hpad).2 rfl h1
    · rintro hs sg' - d - heq b - hpad
      obtain ⟨-, heq2⟩ := ZFSet.pair_injective heq
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective heq2
      exact ⟨fun h1 => absurd (natZ_injective h1) (by decide),
        fun _ h => hs (satV_of_pad_trD0P hbase hφ ha hpad h)⟩
  · rw [code_delta_true, toFm_delta_true]
    constructor
    · intro H
      by_contra hs
      obtain ⟨b, hpad, h2⟩ := exists_pad_not_trD0N_of_not_satV hbase hφ ha hs
      exact h2 ((H (natZ 1) trivial (Fm.code.{u} φ) trivial rfl b trivial hpad).1 rfl)
    · rintro hs sg' - d - heq b - hpad
      obtain ⟨-, heq2⟩ := ZFSet.pair_injective heq
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective heq2
      exact ⟨fun _ => pad_trD0N_of_satV hbase hφ ha hpad hs,
        fun h0 => absurd (natZ_injective h0) (by decide)⟩

end BM4.ST
