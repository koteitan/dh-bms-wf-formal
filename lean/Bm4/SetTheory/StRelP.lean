/-
  Part III, §14–15 over the *padding* block update (`TrP.lean`) and the *distinctness*-respecting
  code recognizers (`BFCodeD.lean`).

  `StRel.lean` proves Lemma 15.3 by a detour: the direction "elementarity implies `TV_q`" goes
  through the Lévy complexity of the truth predicate (`trSigS_transfer`), because `TVq`
  quantifies over codes that need not be well formed in the sense of Definition 12.1, so the
  correctness theorem 13.6 is unavailable there.

  Here `TVqP` quantifies only over codes recognized by `IsSigCodeWD`, i.e. codes of block
  formulas whose quantifier blocks consist of pairwise distinct variables, and the truth
  predicate is the padding one, for which *every* assignment over the model is good.  Both
  directions of `tvqP_iff_elemHat` then go through the correctness of the truth predicate, in
  `L θ` and in `L ξ` — the paper's own argument.
-/
import Bm4.SetTheory.StRel
import Bm4.SetTheory.TrP
import Bm4.SetTheory.BFCodeD

universe u

namespace BM4.ST

open Fm

/-! ### Per-block distinctness suffices for the padding correctness theorem

`GoodAsnP` of `TrP.lean` asks for `b.blockVars.Nodup`, which forbids a variable occurring in two
*different* blocks.  The recognizer `IsSigCodeWD` only certifies `b.NodupBlocks`, i.e.
distinctness *inside* each block — which is all Definition 12.1 requires and all the block update
ever uses.  So we redo the (short) block step and Theorem 13.6 over the weaker hypothesis. -/

/-- `GoodAsnP` with `b.blockVars.Nodup` weakened to per-block distinctness. -/
def GoodAsnQ (W : ZFSet.{u}) (b : BF) (a : ZFSet.{u}) : Prop :=
  IsSeqA ωZ W a ∧ a ∈ W ∧ b.NodupBlocks ∧ BF.code.{u} b ∈ W ∧ WClosed W

theorem goodAsnQ_of_goodAsnP {W : ZFSet.{u}} {b : BF} {a : ZFSet.{u}} (hg : GoodAsnP W b a) :
    GoodAsnQ W b a :=
  ⟨hg.1, hg.2.1, BF.nodupBlocks_of_blockVars_nodup hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2⟩

/-- At the Δ₀ level there are no block variables at all, so `GoodAsnQ` gives `GoodAsn`. -/
theorem goodAsn_of_goodAsnQ_delta {W : ZFSet.{u}} {sg : Bool} {φ : Fm} {a : ZFSet.{u}}
    (hg : GoodAsnQ W (BF.delta sg φ) a) : GoodAsn W (BF.delta sg φ) a := by
  obtain ⟨ha, haW, -, hcode, hW⟩ := hg
  refine ⟨ha, haW, ?_, ?_, hcode, hW⟩
  · intro i hi
    simp only [BF.blockVars, List.not_mem_nil] at hi
  · simp only [BF.blockVars]
    exact List.nodup_nil

theorem trSigQ_step {W : ZFSet.{u}} (hWt : W.IsTransitive) {l : List ℕ} {ψ : BF}
    {a : ZFSet.{u}} (hg : GoodAsnQ W (BF.exs l ψ) a)
    {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (hP : ∀ b, GoodAsnQ W ψ b → (P (BF.code.{u} ψ) b ↔ Sat (· ∈ W) (SeqVal b) ψ.toFm)) :
    (∃ ν, ν ∈ W ∧ ∃ d, d ∈ W ∧ ∃ t, t ∈ W ∧ ∃ b, b ∈ W ∧
        BF.code.{u} (BF.exs l ψ) = ZFSet.pair (natZ 1) (ZFSet.pair ν d) ∧
        IsBlkUpdP ωZ a ν t b ∧ P d b) ↔
      Sat (· ∈ W) (SeqVal a) (BF.exs l ψ).toFm := by
  obtain ⟨ha, haW, hnd, hcode, hW⟩ := hg
  obtain ⟨hndl, hndψ⟩ := (BF.nodupBlocks_exs l ψ).mp hnd
  rw [code_exs] at hcode
  have hcodeψ : BF.code.{u} ψ ∈ W :=
    snd_mem_of_kpair_mem hWt (snd_mem_of_kpair_mem hWt hcode)
  rw [toFm_exs, sat_exs_iff_exsD, exsD_iff_exists_list]
  constructor
  · rintro ⟨ν, hνW, d, hdW, t, htW, b, hbW, heq, hbu, hPd⟩
    rw [code_exs] at heq
    obtain ⟨-, heq2⟩ := ZFSet.pair_injective heq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective heq2
    obtain ⟨xs, hlen, hxsW, hseqb, hvalb⟩ := blkUpdP_list hWt hW ha hndl htW hbu
    refine ⟨xs, hlen, hxsW, ?_⟩
    rw [← hvalb]
    exact (hP b ⟨hseqb, hbW, hndψ, hcodeψ, hW⟩).mp hPd
  · rintro ⟨xs, hlen, hxsW, hsat⟩
    obtain ⟨b, hbu, hseqb, hbW, hvalb⟩ := exists_blkUpdP_W hW ha hndl hlen hxsW
    refine ⟨seqOfNats.{u} l, hW.seqOfNats_mem l, BF.code.{u} ψ, hcodeψ,
      seqOfVals xs, hW.seqOfVals_mem xs hxsW, b, hbW, code_exs l ψ, hbu, ?_⟩
    refine (hP b ⟨hseqb, hbW, hndψ, hcodeψ, hW⟩).mpr ?_
    rw [hvalb]
    exact hsat

theorem trPiQ_step {W : ZFSet.{u}} (hWt : W.IsTransitive) {l : List ℕ} {ψ : BF}
    {a : ZFSet.{u}} (hg : GoodAsnQ W (BF.alls l ψ) a)
    {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (hP : ∀ b, GoodAsnQ W ψ b → (P (BF.code.{u} ψ) b ↔ Sat (· ∈ W) (SeqVal b) ψ.toFm)) :
    (∀ ν, ν ∈ W → ∀ d, d ∈ W → ∀ t, t ∈ W → ∀ b, b ∈ W →
        BF.code.{u} (BF.alls l ψ) = ZFSet.pair (natZ 2) (ZFSet.pair ν d) →
        IsBlkUpdP ωZ a ν t b → P d b) ↔
      Sat (· ∈ W) (SeqVal a) (BF.alls l ψ).toFm := by
  obtain ⟨ha, haW, hnd, hcode, hW⟩ := hg
  obtain ⟨hndl, hndψ⟩ := (BF.nodupBlocks_alls l ψ).mp hnd
  rw [code_alls] at hcode
  have hcodeψ : BF.code.{u} ψ ∈ W :=
    snd_mem_of_kpair_mem hWt (snd_mem_of_kpair_mem hWt hcode)
  rw [toFm_alls, sat_alls_iff_allD, allD_iff_forall_list]
  constructor
  · intro H xs hlen hxsW
    obtain ⟨b, hbu, hseqb, hbW, hvalb⟩ := exists_blkUpdP_W hW ha hndl hlen hxsW
    have hPd := H (seqOfNats.{u} l) (hW.seqOfNats_mem l) (BF.code.{u} ψ) hcodeψ
      (seqOfVals xs) (hW.seqOfVals_mem xs hxsW) b hbW (code_alls l ψ) hbu
    rw [← hvalb]
    exact (hP b ⟨hseqb, hbW, hndψ, hcodeψ, hW⟩).mp hPd
  · intro H ν hνW d hdW t htW b hbW heq hbu
    rw [code_alls] at heq
    obtain ⟨-, heq2⟩ := ZFSet.pair_injective heq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective heq2
    obtain ⟨xs, hlen, hxsW, hseqb, hvalb⟩ := blkUpdP_list hWt hW ha hndl htW hbu
    refine (hP b ⟨hseqb, hbW, hndψ, hcodeψ, hW⟩).mpr ?_
    rw [hvalb]
    exact H xs hlen hxsW

/-- **Theorem 13.6** over the padding block update, with only per-block distinctness assumed. -/
theorem trSigPiQ_correct {W : ZFSet.{u}} (hWt : W.IsTransitive) (hbase : BaseCorrect W) :
    ∀ (q : ℕ) (b : BF),
      (BF.Sig q b → ∀ a, GoodAsnQ W b a →
        (TrSigP (· ∈ W) (L Ordinal.omega0) ωZ q (BF.code.{u} b) a ↔
          Sat (· ∈ W) (SeqVal a) b.toFm)) ∧
      (BF.Pi q b → ∀ a, GoodAsnQ W b a →
        (TrPiP (· ∈ W) (L Ordinal.omega0) ωZ q (BF.code.{u} b) a ↔
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
      | zero hφ =>
        rw [trSigP_zero]
        exact trMSig_correct hWt hbase hφ (goodAsn_of_goodAsnQ_delta hg)
    · intro hs a hg
      cases hs with
      | zero hφ =>
        rw [trPiP_zero]
        exact trMPi_correct hWt hbase hφ (goodAsn_of_goodAsnQ_delta hg)
  | 1 =>
    constructor
    · intro hs a hg
      cases hs with
      | succ hl hψ =>
        rw [trSigP_one, and_iff_right (isSigCodeWD_code (BF.Sig.succ hl hψ) hg.2.2.1)]
        refine trSigQ_step hWt hg ?_
        intro b' hg'
        cases hψ with
        | zero hφ => exact trMSig_correct hWt hbase hφ (goodAsn_of_goodAsnQ_delta hg')
    · intro hs a hg
      cases hs with
      | succ hl hψ =>
        rw [trPiP_one, and_iff_right (isPiCodeWD_code (BF.Pi.succ hl hψ) hg.2.2.1)]
        refine trPiQ_step hWt hg ?_
        intro b' hg'
        cases hψ with
        | zero hφ => exact trMPi_correct hWt hbase hφ (goodAsn_of_goodAsnQ_delta hg')
  | n + 2 =>
    constructor
    · intro hs a hg
      cases hs with
      | succ hl hψ =>
        rw [trSigP_add_two, and_iff_right (isSigCodeWD_code (BF.Sig.succ hl hψ) hg.2.2.1)]
        refine trSigQ_step hWt hg ?_
        intro b' hg'
        exact (ih (n + 1) (by omega) _).2 hψ b' hg'
    · intro hs a hg
      cases hs with
      | succ hl hψ =>
        rw [trPiP_add_two, and_iff_right (isPiCodeWD_code (BF.Pi.succ hl hψ) hg.2.2.1)]
        refine trPiQ_step hWt hg ?_
        intro b' hg'
        exact (ih (n + 1) (by omega) _).1 hψ b' hg'

/-- **Theorem 13.6** (Σ side) over the padding block update, per-block distinctness only. -/
theorem trSigQ_correct {W : ZFSet.{u}} (hWt : W.IsTransitive) (hbase : BaseCorrect W) :
    ∀ (q : ℕ) (b : BF), BF.Sig q b → ∀ a, GoodAsnQ W b a →
      (TrSigP (· ∈ W) (L Ordinal.omega0) ωZ q (BF.code b) a ↔
        Sat (· ∈ W) (SeqVal a) b.toFm) :=
  fun q b => (trSigPiQ_correct hWt hbase q b).1

/-- **Theorem 13.6** (Π side) over the padding block update, per-block distinctness only. -/
theorem trPiQ_correct {W : ZFSet.{u}} (hWt : W.IsTransitive) (hbase : BaseCorrect W) :
    ∀ (q : ℕ) (b : BF), BF.Pi q b → ∀ a, GoodAsnQ W b a →
      (TrPiP (· ∈ W) (L Ordinal.omega0) ωZ q (BF.code b) a ↔
        Sat (· ∈ W) (SeqVal a) b.toFm) :=
  fun q b => (trSigPiQ_correct hWt hbase q b).2

/-! ### Definition 14.2 over well-formed codes and the padding truth predicate -/

/-- Definition 14.2, one stage.  Only codes recognized by `IsSigCodeWD` — i.e. codes of block
formulas whose quantifier blocks consist of distinct variables — are quantified over.

`TrSigP (· ∈ M) …` is the *semantic* reading of the paper's `Tr^M_{Σ̂ j}(e, a)`, the syntactic
relativization of the fixed Δ₀ formula `Tr_{Σ̂ j}` to `M`.  The two readings agree exactly when
`M` is a transitive nonempty set containing the two parameters `h`, `w` — `GoodDom (· ∈ M)`
together with `ValD (· ∈ M) {h, w}` — so the stage is stated under those hypotheses.  For every
`M` the paper ever applies `TV_q` to, namely the set named by a hierarchy code, they hold.

The conjunct `IsSigCodeWD h w j e` is the paper's `Form_{Σ̂ j}(e)` of (14.1).  Since Definition
13.4 now carries the same guard, `TrSigP D h w j e a` already implies it, so the conjunct is
logically redundant; it is kept because (14.1) states it. -/
def TVBodyP (D : ZFSet.{u} → Prop) (h w : ZFSet.{u}) (j : ℕ) (M : ZFSet.{u}) : Prop :=
  M.IsTransitive → (∃ x, x ∈ M) → h ∈ M → w ∈ M →
    ∀ e ∈ M, ∀ a ∈ M, IsSigCodeWD h w j e → IsSeqA w M a →
      TrSigP D h w j e a → TrSigP (· ∈ M) h w j e a

/-- The conjunction of `TVBodyP` over the stages `1, …, q`. -/
def TVConjP (D : ZFSet.{u} → Prop) (h w : ZFSet.{u}) : ℕ → ZFSet.{u} → Prop
  | 0, _ => True
  | j + 1, M => TVConjP D h w j M ∧ TVBodyP D h w (j + 1) M

/-- `TV_q(M)` (Definition 14.2), padding form: the finite conjunction (14.1) and nothing else. -/
def TVqP (D : ZFSet.{u} → Prop) (h w : ZFSet.{u}) (q : ℕ) (M : ZFSet.{u}) : Prop :=
  TVConjP D h w q M

theorem tvBodyP_of_tvConjP {D : ZFSet.{u} → Prop} {h w M : ZFSet.{u}} :
    ∀ (q j : ℕ), 1 ≤ j → j ≤ q → TVConjP D h w q M → TVBodyP D h w j M := by
  intro q
  induction q with
  | zero => intro j h1 h2 _; omega
  | succ q ih =>
    intro j h1 h2 hc
    rcases Nat.lt_or_ge j (q + 1) with hlt | hge
    · exact ih j h1 (by omega) hc.1
    · have hj : j = q + 1 := by omega
      subst hj
      exact hc.2

/-! ### Complexity -/

theorem piDef_TVqP (q : ℕ) (h w M : ℕ) (hhw : h ≠ w) (hhM : h ≠ M) (hwM : w ≠ M) :
    PiDef (max q 1) {h, w, M} (fun D v => TVqP.{u} D (v h) (v w) q (v M)) := by
  induction q with
  | zero =>
    have hd : Delta0Def.{u} (∅ : Finset ℕ) (fun D v => TVqP.{u} D (v h) (v w) 0 (v M)) :=
      Delta0Def.top.congr (fun _ _ _ _ => by simp [TVqP, TVConjP])
    rw [show max 0 1 = 1 by omega]
    exact (hd.pi 1).mono (Finset.empty_subset _)
  | succ q ih =>
    set m := h + w + M + 1 with hm
    have hX : PiDef (q + 1) {h, w, M} (fun D v => TVqP.{u} D (v h) (v w) q (v M)) :=
      ih.pad (by omega)
    have hP0 : Delta0Def.{u} {h, w, M}
        (fun _ v => (v M).IsTransitive ∧ (∃ x, x ∈ v M) ∧ v h ∈ v M ∧ v w ∈ v M) := by
      refine ((delta0_isTransitive.{u} M).and ((delta0_nonemptyMem.{u} M).and
        ((Delta0Def.mem.{u} h M).and (Delta0Def.mem.{u} w M)))).of_eq ?_
      ext k
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
      tauto
    have hTr : SigmaDef (q + 1) {h, w, m, m + 1}
        (fun D v => TrSigP.{u} D (v h) (v w) (q + 1) (v m) (v (m + 1))) := by
      have hc := (trComplexityP.{u} (q + 1) h w m (m + 1) hhw (by omega) (by omega) (by omega)
        (by omega) (by omega)).1
      rwa [show max (q + 1) 1 = q + 1 by omega] at hc
    obtain ⟨Q, hQ0, hQiff⟩ := hTr.relativize M (by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega)
    have hA : Delta0Def.{u} {h, w, m} (fun _ v => IsSigCodeWD (v h) (v w) (q + 1) (v m)) :=
      delta0_isSigCodeWD (q + 1) h w m hhw (by omega) (by omega)
    have hB : Delta0Def.{u} {w, M, m + 1} (fun _ v => IsSeqA (v w) (v M) (v (m + 1))) :=
      delta0_isSeqA w M (m + 1) hwM (by omega) (by omega)
    have hAnt : Delta0Def.{u} {h, w, M, m, m + 1} (fun _ v =>
        v m ∈ v M ∧ v (m + 1) ∈ v M ∧
          ((v M).IsTransitive ∧ (∃ x, x ∈ v M) ∧ v h ∈ v M ∧ v w ∈ v M)) := by
      refine ((Delta0Def.mem.{u} m M).and ((Delta0Def.mem.{u} (m + 1) M).and hP0)).of_eq ?_
      ext k
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
      tauto
    have hL4 := hTr.imp_pi (hQ0.pi (q + 1))
    have hL3 := (hB.sigma (q + 1)).imp_pi hL4
    have hL2 := (hA.sigma (q + 1)).imp_pi hL3
    have hL1 := (hAnt.sigma (q + 1)).imp_pi hL2
    have hL1' : PiDef (q + 1) {h, w, M, m, m + 1} (fun D v =>
        (v m ∈ v M ∧ v (m + 1) ∈ v M ∧
          ((v M).IsTransitive ∧ (∃ x, x ∈ v M) ∧ v h ∈ v M ∧ v w ∈ v M)) →
        IsSigCodeWD (v h) (v w) (q + 1) (v m) →
        IsSeqA (v w) (v M) (v (m + 1)) →
        TrSigP.{u} D (v h) (v w) (q + 1) (v m) (v (m + 1)) →
        TrSigP.{u} (· ∈ v M) (v h) (v w) (q + 1) (v m) (v (m + 1))) := by
      refine (hL1.congr ?_).of_eq ?_
      · intro D v _ _
        have key : ∀ (_ : v m ∈ v M ∧ v (m + 1) ∈ v M ∧
            ((v M).IsTransitive ∧ (∃ x, x ∈ v M) ∧ v h ∈ v M ∧ v w ∈ v M)),
            (Q D v ↔ TrSigP.{u} (· ∈ v M) (v h) (v w) (q + 1) (v m) (v (m + 1))) := by
          rintro ⟨hem, ham, htr, hne, hhm', hwm'⟩
          refine hQiff D v (goodDom_mem htr hne) ?_
          intro i hi
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl | rfl | rfl
          · exact hhm'
          · exact hwm'
          · exact hem
          · exact ham
        constructor
        · intro H hant h1 h2 h3
          exact (key hant).mp (H hant h1 h2 h3)
        · intro H hant h1 h2 h3
          exact (key hant).mpr (H hant h1 h2 h3)
      · ext k
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
        omega
    have hball := (hL1'.ball (m + 1) M (by omega) (by omega)).ball m M (by omega) (by omega)
    have hbody : PiDef (q + 1) {h, w, M}
        (fun D v => TVBodyP.{u} D (v h) (v w) (q + 1) (v M)) := by
      refine (hball.congr ?_).of_eq ?_
      · intro D v _ _
        simp (disch := omega) only [TVBodyP, Function.update_self, Function.update_of_ne]
        constructor
        · intro H htr hne hhm' hwm' e' he' a' ha'
          exact H e' he' a' ha' ⟨he', ha', htr, hne, hhm', hwm'⟩
        · intro H e' he' a' ha' hant
          exact H hant.2.2.1 hant.2.2.2.1 hant.2.2.2.2.1 hant.2.2.2.2.2 e' he' a' ha'
      · ext k
        simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
        omega
    refine (((hX.and hbody).congr ?_).of_eq ?_).pad (by omega)
    · intro D v _ _
      simp only [TVqP, TVConjP]
    · ext k
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
      tauto

/-! ### The bridge, the paper's way

Both directions go through the correctness of the padding truth predicate (Theorem 13.6),
evaluated once in `L θ` and once in `L ξ`.  Neither direction uses the Lévy complexity of the
truth predicate. -/

/-- **Theorem 14.4** (finite-stage Tarski–Vaught), for *every* `q ≥ 1`: for admissible
`ξ < θ`, `L θ ⊨ TV_q(L ξ)` iff `L ξ ≺*_q L θ`. -/
theorem tvqP_iff_elemHat_general {ξ θ : Ordinal.{u}} (hθ : GoodOrd θ) (hξ : GoodOrd ξ)
    (hlt : ξ < θ) {q : ℕ} (hq : 1 ≤ q) :
    TVqP (· ∈ L θ) (L Ordinal.omega0) ωZ q (L ξ) ↔ ElemHat q (L ξ) (L θ) := by
  have _hq := hq
  have hsub : L ξ ⊆ L θ := L_mono hlt.le
  have hLω : L Ordinal.omega0.{u} ⊆ L ξ := L_mono hξ.omega_lt.le
  have hemp : (∅ : ZFSet.{u}) ∈ L ξ := hξ.wClosed.empty_mem
  constructor
  · -- `TV` gives elementarity: normalise `φ` to a block formula, then use Theorem 13.6 twice.
    intro hconj
    refine elemHat_of_downward hξ.transitive hθ.transitive hsub ?_
    intro j hj1 hj2 φ hφ v hv hsatθ
    obtain ⟨b, hbSig, hbnd, -, hbsat⟩ := (exists_norm.{u} j).1 0 φ hφ
    have hnb : b.NodupBlocks := BF.nodupBlocks_of_blockVars_nodup hbnd
    obtain ⟨a, ha, -, haval⟩ := exists_seq_of_val (fv φ) v hv
    have haξ : a ∈ L ξ := isSeqA_mem_of_wClosed hξ.wClosed ha
    have hcodeξ : BF.code.{u} b ∈ L ξ := hLω (BF.code_mem_Lω b)
    have hGξ : GoodAsnQ (L ξ) b a := ⟨ha, haξ, hnb, hcodeξ, hξ.wClosed⟩
    have hGθ : GoodAsnQ (L θ) b a :=
      ⟨isSeqA_of_subset ha hsub, hsub haξ, hnb, hsub hcodeξ, hθ.wClosed⟩
    have hagree : ∀ x ∈ fv φ, v x = SeqVal a x := fun x hx => (haval x hx).symm
    have hsat1 : Sat (· ∈ L θ) (SeqVal a) φ := (sat_congr hagree).mp hsatθ
    have hsat2 : Sat (· ∈ L θ) (SeqVal a) b.toFm :=
      (hbsat _ ⟨ωZ, hθ.omegaZ_mem⟩ (SeqVal a)).mpr hsat1
    have htrθ : TrSigP (· ∈ L θ) (L Ordinal.omega0) ωZ j (BF.code.{u} b) a :=
      (trSigQ_correct hθ.transitive hθ.base j b hbSig a hGθ).mpr hsat2
    have htrξ : TrSigP (· ∈ L ξ) (L Ordinal.omega0) ωZ j (BF.code.{u} b) a :=
      tvBodyP_of_tvConjP q j hj1 hj2 hconj hξ.transitive ⟨ωZ, hξ.omegaZ_mem⟩
        hξ.Lomega_mem hξ.omegaZ_mem (BF.code.{u} b) hcodeξ a haξ
        ((isSigCodeWD_iff j _).mpr ⟨b, hbSig, hnb, rfl⟩) ha htrθ
    have hsat3 : Sat (· ∈ L ξ) (SeqVal a) b.toFm :=
      (trSigQ_correct hξ.transitive hξ.base j b hbSig a hGξ).mp htrξ
    have hsat4 : Sat (· ∈ L ξ) (SeqVal a) φ :=
      (hbsat _ ⟨ωZ, hξ.omegaZ_mem⟩ (SeqVal a)).mp hsat3
    exact (sat_congr hagree).mpr hsat4
  · -- elementarity gives `TV`: the code is well formed, so Theorem 13.6 applies on both sides
    -- and elementarity moves satisfaction of `b.toFm` from `L θ` to `L ξ`.
    intro hel
    have key : ∀ p, p ≤ q → TVConjP (· ∈ L θ) (L Ordinal.omega0) ωZ p (L ξ) := by
      intro p
      induction p with
      | zero => intro _; trivial
      | succ p ih =>
        intro hp
        refine ⟨ih (by omega), ?_⟩
        intro _ _ _ _ e he a ha hcode hseq htr
        obtain ⟨b, hbSig, hnb, rfl⟩ := (isSigCodeWD_iff (p + 1) e).mp hcode
        have hGξ : GoodAsnQ (L ξ) b a := ⟨hseq, ha, hnb, he, hξ.wClosed⟩
        have hGθ : GoodAsnQ (L θ) b a :=
          ⟨isSeqA_of_subset hseq hsub, hsub ha, hnb, hsub he, hθ.wClosed⟩
        have hsatθ : Sat (· ∈ L θ) (SeqVal a) b.toFm :=
          (trSigQ_correct hθ.transitive hθ.base (p + 1) b hbSig a hGθ).mp htr
        have hval : ValIn (L ξ) (fv b.toFm) (SeqVal a) :=
          fun x _ => seqVal_mem_of_vals hemp hseq.1 hseq.2.2 x
        have hE : SatIn (L ξ) (SeqVal a) b.toFm ↔ SatIn (L θ) (SeqVal a) b.toFm :=
          hel.sigma (j := p + 1) (by omega) (hbSig.isSigma hnb) hval
        exact (trSigQ_correct hξ.transitive hξ.base (p + 1) b hbSig a hGξ).mpr (hE.mpr hsatθ)
    exact key q le_rfl

/-- **Theorem 14.4** at `q = k + 2`, the instance Definition 15.2 uses. -/
theorem tvqP_iff_elemHat {ξ θ : Ordinal.{u}} (hθ : GoodOrd θ) (hξ : GoodOrd ξ) (hlt : ξ < θ)
    (k : ℕ) :
    TVqP (· ∈ L θ) (L Ordinal.omega0) ωZ (k + 2) (L ξ) ↔ ElemHat (k + 2) (L ξ) (L θ) :=
  tvqP_iff_elemHat_general hθ hξ hlt (by omega)

end BM4.ST
