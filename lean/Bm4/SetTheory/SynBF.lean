/-
  Part III, §12: two more operations of Lemma 12.2 whose graphs are Δ₀, this time on the codes of
  *block* formulas (`BF.code` of `Bm4/SetTheory/BFCode.lean`):

  * prefixing an alternation block, the last item of Lemma 12.2 (1);
  * dualization of Σ̂q and Π̂q, Lemma 12.2 (2) — the operation Theorem 14.4 actually calls on.

  On block codes both operations are shallow: the code of `∃x̄ ψ` is literally `⟨1, ⟨x̄, ψ⟩⟩`, so
  prefixing a block is a single tagged-pair equation, and dualization only swaps the tags `1 ↔ 2`
  all the way down and flips the sign bit of the Δ₀ matrix.  Accordingly `IsDualSigW`/`IsDualPiW`
  are defined by external recursion on `q`, exactly like the recognizers `IsSigCodeWD` /
  `IsPiCodeWD` of `Bm4/SetTheory/BFCodeD.lean`, and their Δ₀-definability and correctness are
  proved by induction on `q` along the same lines.

  The semantic half of Lemma 12.2 (2) — that the dual is equivalent to the negation in *every*
  domain, with no hypothesis at all — is `BF.sat_dual` of `Bm4/SetTheory/BF.lean`, and the
  preservation of the class is `BF.Sig.dual` / `BF.Pi.dual`.
-/
import Bm4.SetTheory.BFCodeD

universe u

namespace BM4.ST

open Fm

/-! ### Prefixing an alternation block (Lemma 12.2 (1)) -/

/-- `d` is the code obtained from the block code `e` by prefixing the block `ν` with the
quantifier tagged `t` (`1` for `∃`, `2` for `∀`). -/
def IsPrefixBlkW (t : ℕ) (ν e d : ZFSet.{u}) : Prop := d = ZFSet.pair (natZ t) (ZFSet.pair ν e)

theorem delta0_isPrefixBlkW (t : ℕ) (n e d : ℕ) (hdn : d ≠ n) (hde : d ≠ e) :
    Delta0Def.{u} {n, e, d} (fun _ v => IsPrefixBlkW t (v n) (v e) (v d)) :=
  ((delta0_tagPair t d n e hdn hde).congr (fun _ _ _ _ => Iff.rfl)).mono
    (by intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk ⊢
        tauto)

theorem isPrefixBlkW_exs (l : List ℕ) (ψ : BF) :
    IsPrefixBlkW 1 (seqOfNats.{u} l) (BF.code ψ) (BF.code (BF.exs l ψ)) := rfl

theorem isPrefixBlkW_alls (l : List ℕ) (ψ : BF) :
    IsPrefixBlkW 2 (seqOfNats.{u} l) (BF.code ψ) (BF.code (BF.alls l ψ)) := rfl

/-- The graph of block prefixing is single-valued and hits exactly the intended code. -/
theorem isPrefixBlkW_iff_exs (l : List ℕ) (ψ : BF) (d : ZFSet.{u}) :
    IsPrefixBlkW 1 (seqOfNats.{u} l) (BF.code ψ) d ↔ d = BF.code (BF.exs l ψ) := Iff.rfl

theorem isPrefixBlkW_iff_alls (l : List ℕ) (ψ : BF) (d : ZFSet.{u}) :
    IsPrefixBlkW 2 (seqOfNats.{u} l) (BF.code ψ) d ↔ d = BF.code (BF.alls l ψ) := Iff.rfl

/-! ### Dualization of the Δ₀ matrix -/

/-- `d` is the code of the dual of the Δ₀ block code `e`: the same matrix with the sign bit
flipped.  All the quantifiers are bounded by `e` and `d`, so the predicate is Δ₀. -/
def IsDualDeltaW (h w e d : ZFSet.{u}) : Prop :=
  ∃ q ∈ e, ∃ t ∈ q, ∃ s ∈ t, ∃ sg ∈ s, ∃ s₁ ∈ t, ∃ c ∈ s₁,
  ∃ q' ∈ d, ∃ t' ∈ q', ∃ s' ∈ t', ∃ sg' ∈ s',
    IsDelta0CodeW h w c ∧
    e = ZFSet.pair (natZ 0) (ZFSet.pair sg c) ∧
    d = ZFSet.pair (natZ 0) (ZFSet.pair sg' c) ∧
    ((sg = natZ 0 ∧ sg' = natZ 1) ∨ (sg = natZ 1 ∧ sg' = natZ 0))

theorem delta0_isDualDeltaW (h w e d : ℕ) (hhw : h ≠ w) (hhe : h ≠ e) (hhd : h ≠ d)
    (hwe : w ≠ e) (hwd : w ≠ d) (hed : e ≠ d) :
    Delta0Def.{u} {h, w, e, d} (fun _ v => IsDualDeltaW (v h) (v w) (v e) (v d)) := by
  set m := h + w + e + d + 1 with hm
  -- q := m, t := m+1, s := m+2, sg := m+3, s₁ := m+4, c := m+5,
  -- q' := m+6, t' := m+7, s' := m+8, sg' := m+9
  have h0 := (delta0_isDelta0CodeW h w (m + 5) hhw (by omega) (by omega)).and
    ((delta0_tagPair 0 e (m + 3) (m + 5) (by omega) (by omega)).and
      ((delta0_tagPair 0 d (m + 9) (m + 5) (by omega) (by omega)).and
        (((delta0_isNatZ 0 (m + 3)).and (delta0_isNatZ 1 (m + 9))).or
         ((delta0_isNatZ 1 (m + 3)).and (delta0_isNatZ 0 (m + 9))))))
  have h1 := h0.bex (m + 9) (m + 8) (by omega)
  have h2 := h1.bex (m + 8) (m + 7) (by omega)
  have h3 := h2.bex (m + 7) (m + 6) (by omega)
  have h4 := h3.bex (m + 6) d (by omega)
  have h5 := h4.bex (m + 5) (m + 4) (by omega)
  have h6 := h5.bex (m + 4) (m + 1) (by omega)
  have h7 := h6.bex (m + 3) (m + 2) (by omega)
  have h8 := h7.bex (m + 2) (m + 1) (by omega)
  have h9 := h8.bex (m + 1) m (by omega)
  have hA := h9.bex m e (by omega)
  refine (hA.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    rfl
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

theorem isDualDeltaW_iff (e d : ZFSet.{u}) :
    IsDualDeltaW (L Ordinal.omega0) ωZ e d ↔
      ∃ (sg : Bool) (φ : Fm), IsDelta0 φ ∧ e = BF.code.{u} (BF.delta sg φ) ∧
        d = BF.code.{u} (BF.delta sg φ).dual := by
  constructor
  · rintro ⟨q, -, t, -, s, -, sg, -, s₁, -, c, -, q', -, t', -, s', -, sg', -,
      hc, he, hd, hsign⟩
    obtain ⟨φ, hφ, rfl⟩ := (isDelta0CodeW_iff c).mp hc
    rcases hsign with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨false, φ, hφ, by rw [he]; rfl, by rw [hd]; rfl⟩
    · exact ⟨true, φ, hφ, by rw [he]; rfl, by rw [hd]; rfl⟩
  · rintro ⟨sg, φ, hφ, rfl, rfl⟩
    refine ⟨_, upair_mem_pair _ _, _, mem_upair_right _ _, _, upair_mem_pair _ _,
      _, mem_upair_left _ _, _, upair_mem_pair _ _, _, mem_upair_right _ _,
      _, upair_mem_pair _ _, _, mem_upair_right _ _, _, upair_mem_pair _ _,
      _, mem_upair_left _ _, (isDelta0CodeW_iff _).mpr ⟨φ, hφ, rfl⟩, rfl, ?_, ?_⟩
    · cases sg <;> rfl
    · cases sg <;> simp

/-! ### Dualization of Σ̂q / Π̂q block codes (Lemma 12.2 (2)) -/

/-- Δ₀-definability of `∃ ν b b', e = ⟨natZ t₁, ⟨ν, b⟩⟩ ∧ d = ⟨natZ t₂, ⟨ν, b'⟩⟩ ∧ Q w ν ∧
P h w b b'` — the two-code companion of `delta0_pairShape`. -/
theorem delta0_pairShape₂ (t₁ t₂ : ℕ) (h w e d : ℕ) (hhw : h ≠ w) (hhe : h ≠ e) (hhd : h ≠ d)
    (hwe : w ≠ e) (hwd : w ≠ d) (hed : e ≠ d)
    {Q : ZFSet.{u} → ZFSet.{u} → Prop} {P : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop}
    (hQ : ∀ a : ℕ, h ≠ a → w ≠ a → e ≠ a → d ≠ a →
      Delta0Def.{u} {w, a} (fun _ v => Q (v w) (v a)))
    (hP : ∀ b b' : ℕ, h ≠ b → w ≠ b → e ≠ b → d ≠ b → h ≠ b' → w ≠ b' → e ≠ b' → d ≠ b' →
      b ≠ b' → Delta0Def.{u} {h, w, b, b'} (fun _ v => P (v h) (v w) (v b) (v b'))) :
    Delta0Def.{u} {h, w, e, d} (fun _ v =>
      ∃ ν b b', v e = ZFSet.pair (natZ t₁) (ZFSet.pair ν b) ∧
        v d = ZFSet.pair (natZ t₂) (ZFSet.pair ν b') ∧ Q (v w) ν ∧ P (v h) (v w) b b') := by
  set m := h + w + e + d + 1 with hm
  -- qa := m+1, X := m+2, r := m+3, ν := m+4, r' := m+5, b := m+6,
  -- qa' := m+7, X' := m+8, r'' := m+9, b' := m+10
  have b0 := (delta0_tagPair t₁ e (m + 4) (m + 6) (by omega) (by omega)).and
    ((delta0_tagPair t₂ d (m + 4) (m + 10) (by omega) (by omega)).and
      ((hQ (m + 4) (by omega) (by omega) (by omega) (by omega)).and
        (hP (m + 6) (m + 10) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega))))
  have b1 := b0.bex (m + 10) (m + 9) (by omega)
  have b2 := b1.bex (m + 9) (m + 8) (by omega)
  have b3 := b2.bex (m + 8) (m + 7) (by omega)
  have b4 := b3.bex (m + 7) d (by omega)
  have b5 := b4.bex (m + 6) (m + 5) (by omega)
  have b6 := b5.bex (m + 5) (m + 2) (by omega)
  have b7 := b6.bex (m + 4) (m + 3) (by omega)
  have b8 := b7.bex (m + 3) (m + 2) (by omega)
  have b9 := b8.bex (m + 2) (m + 1) (by omega)
  have bA := b9.bex (m + 1) e (by omega)
  refine (bA.congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · rintro ⟨qa, -, X, -, r, -, ν, -, r', -, b, -, qa', -, X', -, r'', -, b', -,
        H1, H2, hq, hp⟩
      exact ⟨ν, b, b', H1, H2, hq, hp⟩
    · rintro ⟨ν, b, b', H1, H2, hq, hp⟩
      exact ⟨_, by rw [H1]; exact upair_mem_pair _ _, _, mem_upair_right _ _,
        _, upair_mem_pair _ _, ν, mem_upair_left _ _,
        _, upair_mem_pair _ _, b, mem_upair_right _ _,
        _, by rw [H2]; exact upair_mem_pair _ _, _, mem_upair_right _ _,
        _, upair_mem_pair _ _, b', mem_upair_right _ _, H1, H2, hq, hp⟩
  · intro k hk; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union] at hk ⊢; omega

mutual
/-- `d` codes the dual of the Σ̂q block code `e`. -/
def IsDualSigW (h w : ZFSet.{u}) : ℕ → ZFSet.{u} → ZFSet.{u} → Prop
  | 0, e, d => IsDualDeltaW h w e d
  | q + 1, e, d => ∃ ν b b', e = ZFSet.pair (natZ 1) (ZFSet.pair ν b) ∧
      d = ZFSet.pair (natZ 2) (ZFSet.pair ν b') ∧ IsNeSeqWD w ν ∧ IsDualPiW h w q b b'
/-- `d` codes the dual of the Π̂q block code `e`. -/
def IsDualPiW (h w : ZFSet.{u}) : ℕ → ZFSet.{u} → ZFSet.{u} → Prop
  | 0, e, d => IsDualDeltaW h w e d
  | q + 1, e, d => ∃ ν b b', e = ZFSet.pair (natZ 2) (ZFSet.pair ν b) ∧
      d = ZFSet.pair (natZ 1) (ZFSet.pair ν b') ∧ IsNeSeqWD w ν ∧ IsDualSigW h w q b b'
end

theorem isDualSigW_succ (h w : ZFSet.{u}) (q : ℕ) (e d : ZFSet.{u}) :
    IsDualSigW h w (q + 1) e d ↔ ∃ ν b b', e = ZFSet.pair (natZ 1) (ZFSet.pair ν b) ∧
      d = ZFSet.pair (natZ 2) (ZFSet.pair ν b') ∧ IsNeSeqWD w ν ∧
      IsDualPiW h w q b b' := Iff.rfl

theorem isDualPiW_succ (h w : ZFSet.{u}) (q : ℕ) (e d : ZFSet.{u}) :
    IsDualPiW h w (q + 1) e d ↔ ∃ ν b b', e = ZFSet.pair (natZ 2) (ZFSet.pair ν b) ∧
      d = ZFSet.pair (natZ 1) (ZFSet.pair ν b') ∧ IsNeSeqWD w ν ∧
      IsDualSigW h w q b b' := Iff.rfl

/-- Lemma 12.2 (2): the graph of dualization is Δ₀. -/
theorem delta0_isDualSigPiW : ∀ (q : ℕ) (h w e d : ℕ), h ≠ w → h ≠ e → h ≠ d → w ≠ e → w ≠ d →
    e ≠ d →
    Delta0Def.{u} {h, w, e, d} (fun _ v => IsDualSigW (v h) (v w) q (v e) (v d)) ∧
    Delta0Def.{u} {h, w, e, d} (fun _ v => IsDualPiW (v h) (v w) q (v e) (v d)) := by
  intro q
  induction q with
  | zero =>
    intro h w e d hhw hhe hhd hwe hwd hed
    exact ⟨(delta0_isDualDeltaW h w e d hhw hhe hhd hwe hwd hed).congr (fun _ _ _ _ => Iff.rfl),
      (delta0_isDualDeltaW h w e d hhw hhe hhd hwe hwd hed).congr (fun _ _ _ _ => Iff.rfl)⟩
  | succ q ih =>
    intro h w e d hhw hhe hhd hwe hwd hed
    constructor
    · refine (delta0_pairShape₂ (Q := fun W ν => IsNeSeqWD W ν)
        (P := fun H W b b' => IsDualPiW H W q b b') 1 2 h w e d hhw hhe hhd hwe hwd hed
        (fun a _ hwa _ _ => delta0_isNeSeqWD w a hwa)
        (fun b b' hhb hwb _ _ hhb' hwb' _ _ hbb' =>
          (ih h w b b' hhw hhb hhb' hwb hwb' hbb').2)).congr (fun _ _ _ _ => Iff.rfl)
    · refine (delta0_pairShape₂ (Q := fun W ν => IsNeSeqWD W ν)
        (P := fun H W b b' => IsDualSigW H W q b b') 2 1 h w e d hhw hhe hhd hwe hwd hed
        (fun a _ hwa _ _ => delta0_isNeSeqWD w a hwa)
        (fun b b' hhb hwb _ _ hhb' hwb' _ _ hbb' =>
          (ih h w b b' hhw hhb hhb' hwb hwb' hbb').1)).congr (fun _ _ _ _ => Iff.rfl)

theorem delta0_isDualSigW (q : ℕ) (h w e d : ℕ) (hhw : h ≠ w) (hhe : h ≠ e) (hhd : h ≠ d)
    (hwe : w ≠ e) (hwd : w ≠ d) (hed : e ≠ d) :
    Delta0Def.{u} {h, w, e, d} (fun _ v => IsDualSigW (v h) (v w) q (v e) (v d)) :=
  (delta0_isDualSigPiW q h w e d hhw hhe hhd hwe hwd hed).1

theorem delta0_isDualPiW (q : ℕ) (h w e d : ℕ) (hhw : h ≠ w) (hhe : h ≠ e) (hhd : h ≠ d)
    (hwe : w ≠ e) (hwd : w ≠ d) (hed : e ≠ d) :
    Delta0Def.{u} {h, w, e, d} (fun _ v => IsDualPiW (v h) (v w) q (v e) (v d)) :=
  (delta0_isDualSigPiW q h w e d hhw hhe hhd hwe hwd hed).2

/-! ### Correctness of the dualization graph -/

theorem isDualSigPiW_iff : ∀ (q : ℕ) (e d : ZFSet.{u}),
    (IsDualSigW (L Ordinal.omega0) ωZ q e d ↔
      ∃ b : BF, BF.Sig q b ∧ b.NodupBlocks ∧ e = BF.code.{u} b ∧ d = BF.code.{u} b.dual) ∧
    (IsDualPiW (L Ordinal.omega0) ωZ q e d ↔
      ∃ b : BF, BF.Pi q b ∧ b.NodupBlocks ∧ e = BF.code.{u} b ∧ d = BF.code.{u} b.dual) := by
  intro q
  induction q with
  | zero =>
    intro e d
    constructor
    · refine (isDualDeltaW_iff e d).trans ?_
      constructor
      · rintro ⟨sg, φ, hφ, rfl, rfl⟩
        exact ⟨BF.delta sg φ, BF.Sig.zero hφ, trivial, rfl, rfl⟩
      · rintro ⟨b, hb, -, rfl, rfl⟩
        cases hb with
        | @zero sg φ hφ => exact ⟨sg, φ, hφ, rfl, rfl⟩
    · refine (isDualDeltaW_iff e d).trans ?_
      constructor
      · rintro ⟨sg, φ, hφ, rfl, rfl⟩
        exact ⟨BF.delta sg φ, BF.Pi.zero hφ, trivial, rfl, rfl⟩
      · rintro ⟨b, hb, -, rfl, rfl⟩
        cases hb with
        | @zero sg φ hφ => exact ⟨sg, φ, hφ, rfl, rfl⟩
  | succ q ih =>
    intro e d
    constructor
    · rw [isDualSigW_succ]
      constructor
      · rintro ⟨ν, b, b', He, Hd, hν, hb⟩
        obtain ⟨l, hl, hnd, rfl⟩ := (isNeSeqWD_iff ν).mp hν
        obtain ⟨c, hc, hnc, rfl, rfl⟩ := (ih b b').2.mp hb
        exact ⟨BF.exs l c, BF.Sig.succ hl hc, ⟨hnd, hnc⟩, He, Hd⟩
      · rintro ⟨b, hb, hnb, rfl, rfl⟩
        cases hb with
        | @succ q' l hl ψ hψ =>
          obtain ⟨hndl, hndψ⟩ : l.Nodup ∧ ψ.NodupBlocks := hnb
          exact ⟨seqOfNats.{u} l, BF.code.{u} ψ, BF.code.{u} ψ.dual, rfl, rfl,
            (isNeSeqWD_iff _).mpr ⟨l, hl, hndl, rfl⟩, (ih _ _).2.mpr ⟨ψ, hψ, hndψ, rfl, rfl⟩⟩
    · rw [isDualPiW_succ]
      constructor
      · rintro ⟨ν, b, b', He, Hd, hν, hb⟩
        obtain ⟨l, hl, hnd, rfl⟩ := (isNeSeqWD_iff ν).mp hν
        obtain ⟨c, hc, hnc, rfl, rfl⟩ := (ih b b').1.mp hb
        exact ⟨BF.alls l c, BF.Pi.succ hl hc, ⟨hnd, hnc⟩, He, Hd⟩
      · rintro ⟨b, hb, hnb, rfl, rfl⟩
        cases hb with
        | @succ q' l hl ψ hψ =>
          obtain ⟨hndl, hndψ⟩ : l.Nodup ∧ ψ.NodupBlocks := hnb
          exact ⟨seqOfNats.{u} l, BF.code.{u} ψ, BF.code.{u} ψ.dual, rfl, rfl,
            (isNeSeqWD_iff _).mpr ⟨l, hl, hndl, rfl⟩, (ih _ _).1.mpr ⟨ψ, hψ, hndψ, rfl, rfl⟩⟩

theorem isDualSigW_iff (q : ℕ) (e d : ZFSet.{u}) :
    IsDualSigW (L Ordinal.omega0) ωZ q e d ↔
      ∃ b : BF, BF.Sig q b ∧ b.NodupBlocks ∧ e = BF.code.{u} b ∧ d = BF.code.{u} b.dual :=
  (isDualSigPiW_iff q e d).1

theorem isDualPiW_iff (q : ℕ) (e d : ZFSet.{u}) :
    IsDualPiW (L Ordinal.omega0) ωZ q e d ↔
      ∃ b : BF, BF.Pi q b ∧ b.NodupBlocks ∧ e = BF.code.{u} b ∧ d = BF.code.{u} b.dual :=
  (isDualSigPiW_iff q e d).2

/-- Lemma 12.2 (2), the semantic half, restated from `BF.sat_dual`: the dual of a Σ̂q block
formula is a Π̂q block formula equivalent to its negation, in **every** domain. -/
theorem dual_sig_correct {q : ℕ} {b : BF} (h : BF.Sig q b) :
    BF.Pi q b.dual ∧ ∀ (D : ZFSet.{u} → Prop) (v : ℕ → ZFSet.{u}),
      Sat D v b.dual.toFm ↔ ¬ Sat D v b.toFm :=
  ⟨h.dual, BF.sat_dual b⟩

theorem dual_pi_correct {q : ℕ} {b : BF} (h : BF.Pi q b) :
    BF.Sig q b.dual ∧ ∀ (D : ZFSet.{u} → Prop) (v : ℕ → ZFSet.{u}),
      Sat D v b.dual.toFm ↔ ¬ Sat D v b.toFm :=
  ⟨h.dual, BF.sat_dual b⟩

end BM4.ST
