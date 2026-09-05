/-
  Part III, §12: the graph of padding is Δ₀ (Lemma 12.2 (3)).

  Lemma 12.2 (3) says that moving a Σ̂j formula to an equivalent Σ̂q formula for `j ≤ q` — by
  adding vacuous blocks at the innermost position — has a Δ₀ graph on codes.  The operation
  itself, on block formulas, is `BF.padSigN` / `BF.padPiN` of `Bm4/SetTheory/BFPad.lean`; this
  file gives the code-level recognizer `IsPadSigW` / `IsPadPiW` and proves it Δ₀ and correct.

  Two points.  The vacuous variable is `fresh (fv φ)` of the Δ₀ matrix; that is not merely
  *some* unused variable but the *least* one from which nothing is free any more, and `IsFreshW`
  expresses exactly that with all quantifiers bounded (by `ω`, a set, and by `z` itself), so the
  graph really is single-valued and Δ₀ — `isFreshW_iff` identifies it with `Fm.fresh`.  Second,
  since the matrix never changes along the padding, every added block quantifies the *same*
  variable; `BF.vacSig` / `BF.vacPi` name that shape and `IsVacSigW` / `IsVacPiW` recognise it.
-/
import Bm4.SetTheory.SynBF
import Bm4.SetTheory.BFPad
import Bm4.SetTheory.CodeFV

universe u

namespace BM4.ST

open Fm

/-! ### The fresh variable of a code -/

/-- `z` is the least element of `w` from which on nothing is free in `e` — i.e. the paper's
choice of "a variable not occurring in the formula", made canonical.  Both quantifiers are
bounded (`y ∈ w`, `z' ∈ z`), so the predicate is Δ₀. -/
def IsFreshW (h w z e : ZFSet.{u}) : Prop :=
  (∀ y ∈ w, (z ∈ y ∨ z = y) → NotFreeW h w y e) ∧
  ∀ z' ∈ z, ¬ (∀ y ∈ w, (z' ∈ y ∨ z' = y) → NotFreeW h w y e)

theorem delta0_isFreshW (h w z e : ℕ) (hhw : h ≠ w) (hhz : h ≠ z) (hhe : h ≠ e)
    (hwz : w ≠ z) (hwe : w ≠ e) (hze : z ≠ e) :
    Delta0Def.{u} {h, w, z, e} (fun _ v => IsFreshW (v h) (v w) (v z) (v e)) := by
  set m := h + w + z + e + 1 with hm
  -- y := m, z' := m+1, y' := m+2
  have p1 := (((Delta0Def.mem.{u} z m).or (Delta0Def.eq.{u} z m)).imp
    (delta0_notFreeW h w m e hhw (by omega) hhe (by omega) hwe (by omega))).ball m w (by omega)
  have p2 := ((((Delta0Def.mem.{u} (m + 1) (m + 2)).or (Delta0Def.eq.{u} (m + 1) (m + 2))).imp
    (delta0_notFreeW h w (m + 2) e hhw (by omega) hhe (by omega) hwe
      (by omega))).ball (m + 2) w (by omega)).not.ball (m + 1) z (by omega)
  refine ((p1.and p2).congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    rfl
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

theorem fresh_spec (F : Finset ℕ) :
    (∀ n : ℕ, Fm.fresh F ≤ n → n ∉ F) ∧ ∀ j < Fm.fresh F, ∃ n : ℕ, j ≤ n ∧ n ∈ F := by
  unfold Fm.fresh
  split_ifs with hF
  · refine ⟨fun n hn hmem => ?_, fun j hj => ⟨F.max' hF, by omega, F.max'_mem hF⟩⟩
    have := F.le_max' n hmem
    omega
  · exact ⟨fun n _ hmem => hF ⟨n, hmem⟩, fun j hj => absurd hj (by omega)⟩

/-- `IsFreshW` picks out exactly `Fm.fresh (fv φ)`. -/
theorem isFreshW_iff (k : ℕ) (φ : Fm) :
    IsFreshW (L Ordinal.omega0) ωZ (natZ.{u} k) φ.code ↔ k = Fm.fresh (Fm.fv φ) := by
  have hnf : ∀ n : ℕ, NotFreeW (L Ordinal.omega0) ωZ (natZ.{u} n) φ.code ↔ n ∉ Fm.fv φ := by
    intro n
    rw [notFreeW_iff]
    constructor
    · rintro ⟨ψ, hψ, hfv⟩; obtain rfl := Fm.code_injective hψ; exact hfv
    · intro hfv; exact ⟨φ, rfl, hfv⟩
  have hstep : ∀ j : ℕ,
      ((∀ y ∈ ωZ.{u}, (natZ j ∈ y ∨ natZ j = y) → NotFreeW (L Ordinal.omega0) ωZ y φ.code) ↔
        ∀ n : ℕ, j ≤ n → n ∉ Fm.fv φ) := by
    intro j
    constructor
    · intro H n hn
      refine (hnf n).mp (H (natZ n) (natZ_mem_ωZ n) ?_)
      rcases Nat.lt_or_ge j n with hlt | hge
      · exact Or.inl (natZ_mem_natZ_iff.mpr hlt)
      · exact Or.inr (by rw [show j = n by omega])
    · intro H y hy hcmp
      obtain ⟨n, rfl⟩ := mem_ωZ_iff.mp hy
      refine (hnf n).mpr (H n ?_)
      rcases hcmp with hc | hc
      · exact le_of_lt (natZ_mem_natZ_iff.mp hc)
      · exact le_of_eq (natZ_injective hc)
  obtain ⟨hf1, hf2⟩ := fresh_spec (Fm.fv φ)
  constructor
  · rintro ⟨H1, H2⟩
    rw [hstep k] at H1
    have H2' : ∀ j < k, ¬ (∀ n : ℕ, j ≤ n → n ∉ Fm.fv φ) := by
      intro j hj
      have := H2 (natZ j) (mem_natZ_iff.mpr ⟨j, hj, rfl⟩)
      rwa [hstep j] at this
    by_contra hne
    rcases Nat.lt_or_ge k (Fm.fresh (Fm.fv φ)) with hlt | hge
    · obtain ⟨n, hkn, hmem⟩ := hf2 k hlt
      exact H1 n hkn hmem
    · have hlt' : Fm.fresh (Fm.fv φ) < k := by omega
      exact H2' _ hlt' hf1
  · rintro rfl
    refine ⟨(hstep _).mpr hf1, ?_⟩
    intro z' hz'
    obtain ⟨j, hj, rfl⟩ := mem_natZ_iff.mp hz'
    rw [hstep j]
    intro H
    obtain ⟨n, hjn, hmem⟩ := hf2 j hj
    exact H n hjn hmem

/-! ### A one-element block -/

/-- `ν` is the code of the one-element block `[z]`. -/
def IsSingletonSeqW (ν z : ZFSet.{u}) : Prop :=
  ∃ p ∈ ν, ν = {p} ∧ ∃ t ∈ p, ∃ n0 ∈ t, n0 = natZ 0 ∧ p = ZFSet.pair n0 z

theorem delta0_isSingletonSeqW (a b : ℕ) (hab : a ≠ b) :
    Delta0Def.{u} {a, b} (fun _ v => IsSingletonSeqW (v a) (v b)) := by
  set m := a + b + 1 with hm
  -- p := m, t := m+1, n0 := m+2
  have h0 := (delta0_isNatZ 0 (m + 2)).and (delta0_isKPair m (m + 2) b (by omega) (by omega))
  have h1 := h0.bex (m + 2) (m + 1) (by omega)
  have h2 := h1.bex (m + 1) m (by omega)
  have h3 := (delta0_isSingleton a m (by omega)).and h2
  have h := h3.bex m a (by omega)
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    rfl
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

theorem seqOfNats_singleton (k : ℕ) :
    seqOfNats.{u} [k] = ({ZFSet.pair (natZ 0) (natZ k)} : ZFSet.{u}) := by
  ext x
  simp [seqOfNats, seqOfAux]

theorem isSingletonSeqW_iff (ν : ZFSet.{u}) (k : ℕ) :
    IsSingletonSeqW ν (natZ k) ↔ ν = seqOfNats.{u} [k] := by
  rw [seqOfNats_singleton]
  constructor
  · rintro ⟨p, -, hν, t, -, n0, -, rfl, rfl⟩; exact hν
  · rintro rfl
    exact ⟨_, ZFSet.mem_singleton.mpr rfl, rfl, _, singleton_mem_pair _ _,
      _, ZFSet.mem_singleton.mpr rfl, rfl, rfl⟩

/-! ### Vacuous blocks on a fixed variable -/

mutual
/-- `d` is `e` wrapped in `n` alternating vacuous blocks on `z`, outermost `∃`. -/
def IsVacSigW : ℕ → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop
  | 0, _, e, d => d = e
  | n + 1, z, e, d => ∃ q ∈ d, ∃ t ∈ q, ∃ s ∈ t, ∃ ν ∈ s, ∃ s' ∈ t, ∃ d' ∈ s',
      d = ZFSet.pair (natZ 1) (ZFSet.pair ν d') ∧ IsSingletonSeqW ν z ∧ IsVacPiW n z e d'
/-- The `∀`-outermost counterpart. -/
def IsVacPiW : ℕ → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop
  | 0, _, e, d => d = e
  | n + 1, z, e, d => ∃ q ∈ d, ∃ t ∈ q, ∃ s ∈ t, ∃ ν ∈ s, ∃ s' ∈ t, ∃ d' ∈ s',
      d = ZFSet.pair (natZ 2) (ZFSet.pair ν d') ∧ IsSingletonSeqW ν z ∧ IsVacSigW n z e d'
end

theorem isVacSigW_succ (n : ℕ) (z e d : ZFSet.{u}) :
    IsVacSigW (n + 1) z e d ↔ ∃ q ∈ d, ∃ t ∈ q, ∃ s ∈ t, ∃ ν ∈ s, ∃ s' ∈ t, ∃ d' ∈ s',
      d = ZFSet.pair (natZ 1) (ZFSet.pair ν d') ∧ IsSingletonSeqW ν z ∧
      IsVacPiW n z e d' := Iff.rfl

theorem isVacPiW_succ (n : ℕ) (z e d : ZFSet.{u}) :
    IsVacPiW (n + 1) z e d ↔ ∃ q ∈ d, ∃ t ∈ q, ∃ s ∈ t, ∃ ν ∈ s, ∃ s' ∈ t, ∃ d' ∈ s',
      d = ZFSet.pair (natZ 2) (ZFSet.pair ν d') ∧ IsSingletonSeqW ν z ∧
      IsVacSigW n z e d' := Iff.rfl

theorem delta0_isVacSigPiW : ∀ (n : ℕ) (a b c : ℕ), a ≠ b → a ≠ c → b ≠ c →
    Delta0Def.{u} {a, b, c} (fun _ v => IsVacSigW n (v a) (v b) (v c)) ∧
    Delta0Def.{u} {a, b, c} (fun _ v => IsVacPiW n (v a) (v b) (v c)) := by
  intro n
  induction n with
  | zero =>
    intro a b c hab hac hbc
    exact ⟨((Delta0Def.eq.{u} c b).congr (fun _ _ _ _ => Iff.rfl)).mono
        (by intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk ⊢; tauto),
      ((Delta0Def.eq.{u} c b).congr (fun _ _ _ _ => Iff.rfl)).mono
        (by intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk ⊢; tauto)⟩
  | succ n ih =>
    intro a b c hab hac hbc
    set m := a + b + c + 1 with hm
    -- q := m, t := m+1, s := m+2, ν := m+3, s' := m+4, d' := m+5
    have mk : ∀ (tg : ℕ),
        Delta0Def.{u} {a, b, m + 3, m + 5} (fun _ v => IsVacSigW n (v a) (v b) (v (m + 5))) →
        Delta0Def.{u} {a, b, c}
          (fun _ v => ∃ q ∈ v c, ∃ t ∈ q, ∃ s ∈ t, ∃ ν ∈ s, ∃ s' ∈ t, ∃ d' ∈ s',
            v c = ZFSet.pair (natZ tg) (ZFSet.pair ν d') ∧ IsSingletonSeqW ν (v a) ∧
            IsVacSigW n (v a) (v b) d') := by
      intro tg hrec
      have h0 := (delta0_tagPair tg c (m + 3) (m + 5) (by omega) (by omega)).and
        ((delta0_isSingletonSeqW (m + 3) a (by omega)).and hrec)
      have h1 := h0.bex (m + 5) (m + 4) (by omega)
      have h2 := h1.bex (m + 4) (m + 1) (by omega)
      have h3 := h2.bex (m + 3) (m + 2) (by omega)
      have h4 := h3.bex (m + 2) (m + 1) (by omega)
      have h5 := h4.bex (m + 1) m (by omega)
      have h := h5.bex m c (by omega)
      refine (h.congr ?_).mono ?_
      · intro D v _ _
        simp (disch := omega) only [Function.update_self, Function.update_of_ne]
      · intro k hk; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
          Finset.mem_union] at hk ⊢; omega
    have mkPi : ∀ (tg : ℕ),
        Delta0Def.{u} {a, b, m + 3, m + 5} (fun _ v => IsVacPiW n (v a) (v b) (v (m + 5))) →
        Delta0Def.{u} {a, b, c}
          (fun _ v => ∃ q ∈ v c, ∃ t ∈ q, ∃ s ∈ t, ∃ ν ∈ s, ∃ s' ∈ t, ∃ d' ∈ s',
            v c = ZFSet.pair (natZ tg) (ZFSet.pair ν d') ∧ IsSingletonSeqW ν (v a) ∧
            IsVacPiW n (v a) (v b) d') := by
      intro tg hrec
      have h0 := (delta0_tagPair tg c (m + 3) (m + 5) (by omega) (by omega)).and
        ((delta0_isSingletonSeqW (m + 3) a (by omega)).and hrec)
      have h1 := h0.bex (m + 5) (m + 4) (by omega)
      have h2 := h1.bex (m + 4) (m + 1) (by omega)
      have h3 := h2.bex (m + 3) (m + 2) (by omega)
      have h4 := h3.bex (m + 2) (m + 1) (by omega)
      have h5 := h4.bex (m + 1) m (by omega)
      have h := h5.bex m c (by omega)
      refine (h.congr ?_).mono ?_
      · intro D v _ _
        simp (disch := omega) only [Function.update_self, Function.update_of_ne]
      · intro k hk; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
          Finset.mem_union] at hk ⊢; omega
    have hrecS : Delta0Def.{u} {a, b, m + 3, m + 5}
        (fun _ v => IsVacSigW n (v a) (v b) (v (m + 5))) :=
      ((ih a b (m + 5) hab (by omega) (by omega)).1).mono
        (by intro k hk
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk ⊢
            omega)
    have hrecP : Delta0Def.{u} {a, b, m + 3, m + 5}
        (fun _ v => IsVacPiW n (v a) (v b) (v (m + 5))) :=
      ((ih a b (m + 5) hab (by omega) (by omega)).2).mono
        (by intro k hk
            simp only [Finset.mem_insert, Finset.mem_singleton] at hk ⊢
            omega)
    exact ⟨(mkPi 1 hrecP).congr (fun _ _ _ _ => Iff.rfl),
      (mk 2 hrecS).congr (fun _ _ _ _ => Iff.rfl)⟩

theorem isVacSigPiW_iff : ∀ (n k : ℕ) (b : BF) (d : ZFSet.{u}),
    (IsVacSigW n (natZ k) (BF.code.{u} b) d ↔ d = BF.code.{u} (BF.vacSig k n b)) ∧
    (IsVacPiW n (natZ k) (BF.code.{u} b) d ↔ d = BF.code.{u} (BF.vacPi k n b)) := by
  intro n
  induction n with
  | zero => intro k b d; exact ⟨Iff.rfl, Iff.rfl⟩
  | succ n ih =>
    intro k b d
    constructor
    · rw [isVacSigW_succ, BF.vacSig_succ]
      constructor
      · rintro ⟨q, -, t, -, s, -, ν, -, s', -, d', -, hd, hν, hrec⟩
        rw [(isSingletonSeqW_iff ν k).mp hν] at hd
        rw [(ih k b d').2.mp hrec] at hd
        exact hd
      · rintro rfl
        exact ⟨_, upair_mem_pair _ _, _, mem_upair_right _ _, _, upair_mem_pair _ _,
          _, mem_upair_left _ _, _, upair_mem_pair _ _, _, mem_upair_right _ _, rfl,
          (isSingletonSeqW_iff _ k).mpr rfl, (ih k b _).2.mpr rfl⟩
    · rw [isVacPiW_succ, BF.vacPi_succ]
      constructor
      · rintro ⟨q, -, t, -, s, -, ν, -, s', -, d', -, hd, hν, hrec⟩
        rw [(isSingletonSeqW_iff ν k).mp hν] at hd
        rw [(ih k b d').1.mp hrec] at hd
        exact hd
      · rintro rfl
        exact ⟨_, upair_mem_pair _ _, _, mem_upair_right _ _, _, upair_mem_pair _ _,
          _, mem_upair_left _ _, _, upair_mem_pair _ _, _, mem_upair_right _ _, rfl,
          (isSingletonSeqW_iff _ k).mpr rfl, (ih k b _).1.mpr rfl⟩

/-! ### The padding graph -/

mutual
/-- `d` is the code of the Σ̂q block formula coded by `e`, padded by `n` levels. -/
def IsPadSigW (h w : ZFSet.{u}) : ℕ → ℕ → ZFSet.{u} → ZFSet.{u} → Prop
  | 0, n, e, d => ∃ z ∈ w, ∃ q ∈ e, ∃ t ∈ q, ∃ s ∈ t, ∃ sg ∈ s, ∃ s₁ ∈ t, ∃ c ∈ s₁,
      e = ZFSet.pair (natZ 0) (ZFSet.pair sg c) ∧ (sg = natZ 0 ∨ sg = natZ 1) ∧
      IsDelta0CodeW h w c ∧ IsFreshW h w z c ∧ IsVacSigW n z e d
  | q + 1, n, e, d => ∃ ν b b', e = ZFSet.pair (natZ 1) (ZFSet.pair ν b) ∧
      d = ZFSet.pair (natZ 1) (ZFSet.pair ν b') ∧ IsNeSeqWD w ν ∧ IsPadPiW h w q n b b'
/-- The Π̂ counterpart. -/
def IsPadPiW (h w : ZFSet.{u}) : ℕ → ℕ → ZFSet.{u} → ZFSet.{u} → Prop
  | 0, n, e, d => ∃ z ∈ w, ∃ q ∈ e, ∃ t ∈ q, ∃ s ∈ t, ∃ sg ∈ s, ∃ s₁ ∈ t, ∃ c ∈ s₁,
      e = ZFSet.pair (natZ 0) (ZFSet.pair sg c) ∧ (sg = natZ 0 ∨ sg = natZ 1) ∧
      IsDelta0CodeW h w c ∧ IsFreshW h w z c ∧ IsVacPiW n z e d
  | q + 1, n, e, d => ∃ ν b b', e = ZFSet.pair (natZ 2) (ZFSet.pair ν b) ∧
      d = ZFSet.pair (natZ 2) (ZFSet.pair ν b') ∧ IsNeSeqWD w ν ∧ IsPadSigW h w q n b b'
end

theorem isPadSigW_succ (h w : ZFSet.{u}) (q n : ℕ) (e d : ZFSet.{u}) :
    IsPadSigW h w (q + 1) n e d ↔ ∃ ν b b', e = ZFSet.pair (natZ 1) (ZFSet.pair ν b) ∧
      d = ZFSet.pair (natZ 1) (ZFSet.pair ν b') ∧ IsNeSeqWD w ν ∧
      IsPadPiW h w q n b b' := Iff.rfl

theorem isPadPiW_succ (h w : ZFSet.{u}) (q n : ℕ) (e d : ZFSet.{u}) :
    IsPadPiW h w (q + 1) n e d ↔ ∃ ν b b', e = ZFSet.pair (natZ 2) (ZFSet.pair ν b) ∧
      d = ZFSet.pair (natZ 2) (ZFSet.pair ν b') ∧ IsNeSeqWD w ν ∧
      IsPadSigW h w q n b b' := Iff.rfl

theorem delta0_isPadBase {V : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop}
    (hV : ∀ a b c : ℕ, a ≠ b → a ≠ c → b ≠ c →
      Delta0Def.{u} {a, b, c} (fun _ v => V (v a) (v b) (v c)))
    (h w e d : ℕ) (hhw : h ≠ w) (hhe : h ≠ e) (hhd : h ≠ d)
    (hwe : w ≠ e) (hwd : w ≠ d) (hed : e ≠ d) :
    Delta0Def.{u} {h, w, e, d} (fun _ v =>
      ∃ z ∈ v w, ∃ q ∈ v e, ∃ t ∈ q, ∃ s ∈ t, ∃ sg ∈ s, ∃ s₁ ∈ t, ∃ c ∈ s₁,
        v e = ZFSet.pair (natZ 0) (ZFSet.pair sg c) ∧ (sg = natZ 0 ∨ sg = natZ 1) ∧
        IsDelta0CodeW (v h) (v w) c ∧ IsFreshW (v h) (v w) z c ∧ V z (v e) (v d)) := by
  set m := h + w + e + d + 1 with hm
  -- z := m, q := m+1, t := m+2, s := m+3, sg := m+4, s₁ := m+5, c := m+6
  have hvac := hV m e d (by omega) (by omega) hed
  have h0 := (delta0_tagPair 0 e (m + 4) (m + 6) (by omega) (by omega)).and
    (((delta0_isNatZ 0 (m + 4)).or (delta0_isNatZ 1 (m + 4))).and
      ((delta0_isDelta0CodeW h w (m + 6) hhw (by omega) (by omega)).and
        ((delta0_isFreshW h w m (m + 6) hhw (by omega) (by omega) (by omega) (by omega)
          (by omega)).and hvac)))
  have h1 := h0.bex (m + 6) (m + 5) (by omega)
  have h2 := h1.bex (m + 5) (m + 2) (by omega)
  have h3 := h2.bex (m + 4) (m + 3) (by omega)
  have h4 := h3.bex (m + 3) (m + 2) (by omega)
  have h5 := h4.bex (m + 2) (m + 1) (by omega)
  have h6 := h5.bex (m + 1) e (by omega)
  have hh := h6.bex m w (by omega)
  refine (hh.congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
  · intro k hk; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union] at hk ⊢; omega

/-- Lemma 12.2 (3): the graph of padding is Δ₀. -/
theorem delta0_isPadSigPiW : ∀ (q n : ℕ) (h w e d : ℕ), h ≠ w → h ≠ e → h ≠ d → w ≠ e → w ≠ d →
    e ≠ d →
    Delta0Def.{u} {h, w, e, d} (fun _ v => IsPadSigW (v h) (v w) q n (v e) (v d)) ∧
    Delta0Def.{u} {h, w, e, d} (fun _ v => IsPadPiW (v h) (v w) q n (v e) (v d)) := by
  intro q
  induction q with
  | zero =>
    intro n h w e d hhw hhe hhd hwe hwd hed
    exact ⟨(delta0_isPadBase (V := fun z x y => IsVacSigW n z x y)
        (fun a b c h1 h2 h3 => (delta0_isVacSigPiW n a b c h1 h2 h3).1)
        h w e d hhw hhe hhd hwe hwd hed).congr (fun _ _ _ _ => Iff.rfl),
      (delta0_isPadBase (V := fun z x y => IsVacPiW n z x y)
        (fun a b c h1 h2 h3 => (delta0_isVacSigPiW n a b c h1 h2 h3).2)
        h w e d hhw hhe hhd hwe hwd hed).congr (fun _ _ _ _ => Iff.rfl)⟩
  | succ q ih =>
    intro n h w e d hhw hhe hhd hwe hwd hed
    constructor
    · refine (delta0_pairShape₂ (Q := fun W ν => IsNeSeqWD W ν)
        (P := fun H W b b' => IsPadPiW H W q n b b') 1 1 h w e d hhw hhe hhd hwe hwd hed
        (fun a _ hwa _ _ => delta0_isNeSeqWD w a hwa)
        (fun b b' hhb hwb _ _ hhb' hwb' _ _ hbb' =>
          (ih n h w b b' hhw hhb hhb' hwb hwb' hbb').2)).congr (fun _ _ _ _ => Iff.rfl)
    · refine (delta0_pairShape₂ (Q := fun W ν => IsNeSeqWD W ν)
        (P := fun H W b b' => IsPadSigW H W q n b b') 2 2 h w e d hhw hhe hhd hwe hwd hed
        (fun a _ hwa _ _ => delta0_isNeSeqWD w a hwa)
        (fun b b' hhb hwb _ _ hhb' hwb' _ _ hbb' =>
          (ih n h w b b' hhw hhb hhb' hwb hwb' hbb').1)).congr (fun _ _ _ _ => Iff.rfl)

/-! ### Correctness -/

theorem isPadSigPiW_iff : ∀ (q n : ℕ) (e d : ZFSet.{u}),
    (IsPadSigW (L Ordinal.omega0) ωZ q n e d ↔
      ∃ b : BF, BF.Sig q b ∧ b.NodupBlocks ∧ e = BF.code.{u} b ∧
        d = BF.code.{u} (BF.padSigN b n)) ∧
    (IsPadPiW (L Ordinal.omega0) ωZ q n e d ↔
      ∃ b : BF, BF.Pi q b ∧ b.NodupBlocks ∧ e = BF.code.{u} b ∧
        d = BF.code.{u} (BF.padPiN b n)) := by
  intro q
  induction q with
  | zero =>
    intro n e d
    have baseSig : IsPadSigW (L Ordinal.omega0) ωZ 0 n e d ↔
        ∃ (sg : Bool) (φ : Fm), IsDelta0 φ ∧ e = BF.code.{u} (BF.delta sg φ) ∧
          d = BF.code.{u} (BF.vacSig (Fm.fresh (Fm.fv φ)) n (BF.delta sg φ)) := by
      constructor
      · rintro ⟨z, hz, q, -, t, -, s, -, sgv, -, s₁, -, c, -, he, hsg, hc, hfr, hvac⟩
        obtain ⟨φ, hφ, rfl⟩ := (isDelta0CodeW_iff c).mp hc
        obtain ⟨kz, rfl⟩ := mem_ωZ_iff.mp hz
        obtain rfl := (isFreshW_iff kz φ).mp hfr
        rw [he] at hvac
        rcases hsg with rfl | rfl
        · exact ⟨false, φ, hφ, he, (isVacSigPiW_iff n _ (BF.delta false φ) d).1.mp hvac⟩
        · exact ⟨true, φ, hφ, he, (isVacSigPiW_iff n _ (BF.delta true φ) d).1.mp hvac⟩
      · rintro ⟨sg, φ, hφ, rfl, rfl⟩
        refine ⟨natZ (Fm.fresh (Fm.fv φ)), natZ_mem_ωZ _,
          _, upair_mem_pair _ _, _, mem_upair_right _ _, _, upair_mem_pair _ _,
          _, mem_upair_left _ _, _, upair_mem_pair _ _, _, mem_upair_right _ _, rfl, ?_,
          (isDelta0CodeW_iff _).mpr ⟨φ, hφ, rfl⟩, (isFreshW_iff _ φ).mpr rfl,
          (isVacSigPiW_iff n _ (BF.delta sg φ) _).1.mpr rfl⟩
        cases sg <;> simp
    have basePi : IsPadPiW (L Ordinal.omega0) ωZ 0 n e d ↔
        ∃ (sg : Bool) (φ : Fm), IsDelta0 φ ∧ e = BF.code.{u} (BF.delta sg φ) ∧
          d = BF.code.{u} (BF.vacPi (Fm.fresh (Fm.fv φ)) n (BF.delta sg φ)) := by
      constructor
      · rintro ⟨z, hz, q, -, t, -, s, -, sgv, -, s₁, -, c, -, he, hsg, hc, hfr, hvac⟩
        obtain ⟨φ, hφ, rfl⟩ := (isDelta0CodeW_iff c).mp hc
        obtain ⟨kz, rfl⟩ := mem_ωZ_iff.mp hz
        obtain rfl := (isFreshW_iff kz φ).mp hfr
        rw [he] at hvac
        rcases hsg with rfl | rfl
        · exact ⟨false, φ, hφ, he, (isVacSigPiW_iff n _ (BF.delta false φ) d).2.mp hvac⟩
        · exact ⟨true, φ, hφ, he, (isVacSigPiW_iff n _ (BF.delta true φ) d).2.mp hvac⟩
      · rintro ⟨sg, φ, hφ, rfl, rfl⟩
        refine ⟨natZ (Fm.fresh (Fm.fv φ)), natZ_mem_ωZ _,
          _, upair_mem_pair _ _, _, mem_upair_right _ _, _, upair_mem_pair _ _,
          _, mem_upair_left _ _, _, upair_mem_pair _ _, _, mem_upair_right _ _, rfl, ?_,
          (isDelta0CodeW_iff _).mpr ⟨φ, hφ, rfl⟩, (isFreshW_iff _ φ).mpr rfl,
          (isVacSigPiW_iff n _ (BF.delta sg φ) _).2.mpr rfl⟩
        cases sg <;> simp
    constructor
    · rw [baseSig]
      constructor
      · rintro ⟨sg, φ, hφ, rfl, hd⟩
        exact ⟨BF.delta sg φ, BF.Sig.zero hφ, trivial, rfl,
          by rw [BF.padSigN_delta]; exact hd⟩
      · rintro ⟨b, hb, -, rfl, hd⟩
        cases hb with
        | @zero sg φ hφ =>
          rw [BF.padSigN_delta] at hd
          exact ⟨sg, φ, hφ, rfl, hd⟩
    · rw [basePi]
      constructor
      · rintro ⟨sg, φ, hφ, rfl, hd⟩
        exact ⟨BF.delta sg φ, BF.Pi.zero hφ, trivial, rfl,
          by rw [BF.padPiN_delta]; exact hd⟩
      · rintro ⟨b, hb, -, rfl, hd⟩
        cases hb with
        | @zero sg φ hφ =>
          rw [BF.padPiN_delta] at hd
          exact ⟨sg, φ, hφ, rfl, hd⟩
  | succ q ih =>
    intro n e d
    constructor
    · rw [isPadSigW_succ]
      constructor
      · rintro ⟨ν, b, b', He, Hd, hν, hb⟩
        obtain ⟨l, hl, hnd, rfl⟩ := (isNeSeqWD_iff ν).mp hν
        obtain ⟨c, hc, hnc, rfl, rfl⟩ := (ih n b b').2.mp hb
        refine ⟨BF.exs l c, BF.Sig.succ hl hc, ⟨hnd, hnc⟩, He, ?_⟩
        rw [BF.padSigN_exs]
        exact Hd
      · rintro ⟨b, hb, hnb, rfl, hd⟩
        cases hb with
        | @succ q' l hl ψ hψ =>
          obtain ⟨hndl, hndψ⟩ : l.Nodup ∧ ψ.NodupBlocks := hnb
          rw [BF.padSigN_exs] at hd
          exact ⟨seqOfNats.{u} l, BF.code.{u} ψ, BF.code.{u} (BF.padPiN ψ n), rfl, hd,
            (isNeSeqWD_iff _).mpr ⟨l, hl, hndl, rfl⟩,
            (ih n _ _).2.mpr ⟨ψ, hψ, hndψ, rfl, rfl⟩⟩
    · rw [isPadPiW_succ]
      constructor
      · rintro ⟨ν, b, b', He, Hd, hν, hb⟩
        obtain ⟨l, hl, hnd, rfl⟩ := (isNeSeqWD_iff ν).mp hν
        obtain ⟨c, hc, hnc, rfl, rfl⟩ := (ih n b b').1.mp hb
        refine ⟨BF.alls l c, BF.Pi.succ hl hc, ⟨hnd, hnc⟩, He, ?_⟩
        rw [BF.padPiN_alls]
        exact Hd
      · rintro ⟨b, hb, hnb, rfl, hd⟩
        cases hb with
        | @succ q' l hl ψ hψ =>
          obtain ⟨hndl, hndψ⟩ : l.Nodup ∧ ψ.NodupBlocks := hnb
          rw [BF.padPiN_alls] at hd
          exact ⟨seqOfNats.{u} l, BF.code.{u} ψ, BF.code.{u} (BF.padSigN ψ n), rfl, hd,
            (isNeSeqWD_iff _).mpr ⟨l, hl, hndl, rfl⟩,
            (ih n _ _).1.mpr ⟨ψ, hψ, hndψ, rfl, rfl⟩⟩

theorem isPadSigW_iff (q n : ℕ) (e d : ZFSet.{u}) :
    IsPadSigW (L Ordinal.omega0) ωZ q n e d ↔
      ∃ b : BF, BF.Sig q b ∧ b.NodupBlocks ∧ e = BF.code.{u} b ∧
        d = BF.code.{u} (BF.padSigN b n) :=
  (isPadSigPiW_iff q n e d).1

theorem isPadPiW_iff (q n : ℕ) (e d : ZFSet.{u}) :
    IsPadPiW (L Ordinal.omega0) ωZ q n e d ↔
      ∃ b : BF, BF.Pi q b ∧ b.NodupBlocks ∧ e = BF.code.{u} b ∧
        d = BF.code.{u} (BF.padPiN b n) :=
  (isPadSigPiW_iff q n e d).2

end BM4.ST
