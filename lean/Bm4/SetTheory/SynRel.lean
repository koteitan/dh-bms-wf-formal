/-
  Part III, §12: the graph of relativization is Δ₀ (Lemma 12.2 (1)).

  `Fm.relTo m` of `Bm4/SetTheory/Rel.lean` is the paper's `φ ↦ φ^M`: every unbounded quantifier
  is restricted to `m`, bounded ones are left alone.  Lemma 12.2 (1) asserts that the relation

      G(m, e, d)  ⟺  `e` codes a formula `φ` and `d` codes `φ^M`

  is Δ₀.  As for substitution (`Bm4/SetTheory/SynSubst.lean`), this is obtained as an instance of
  the schema (8.3) — `GraphW` / `delta0_graphW` of `Bm4/SetTheory/CodeFV.lean` — by supplying the
  three local rules and checking that they are Δ₀.

  Two points are specific to relativization.  First, the `all` rule has to *decide* whether the
  quantifier it is looking at is bounded, i.e. whether the child is of the shape `i ∈ j → ψ` with
  `j ≠ i`; that is a test on the child's **code**, so the trace values are again pairs
  `⟨input code, output code⟩`.  `IsBallBodyW` is that test, and `isBallBodyW_iff` identifies it
  with the syntactic `Fm.isBallBody`.  Second, in the unbounded case the rule has to *build* the
  code of `∀i ∈ m, …`, one node deeper than the code it receives; `delta0_ballCodeShape` is the
  corresponding Δ₀ lemma.
-/
import Bm4.SetTheory.SynSubst
import Bm4.SetTheory.Rel

universe u

namespace BM4.ST

open Fm

/-! ### Two shapes of codes -/

/-- `v e = ⟨3, ⟨⟨2, ⟨i, j⟩⟩, c⟩⟩`: the code of `i ∈ j → …`. -/
theorem delta0_ballBodyShape (e i j c : ℕ) (hei : e ≠ i) (hej : e ≠ j) (hec : e ≠ c) :
    Delta0Def.{u} {e, i, j, c} (fun _ v => v e =
      ZFSet.pair (natZ 3) (ZFSet.pair (ZFSet.pair (natZ 2) (ZFSet.pair (v i) (v j))) (v c))) := by
  set m := e + i + j + c + 1 with hm
  -- q := m, t := m+1, s := m+2, g := m+3
  have h0 := (delta0_tagPair 3 e (m + 3) c (by omega) (by omega)).and
    (delta0_tagPair 2 (m + 3) i j (by omega) (by omega))
  have h1 := h0.bex (m + 3) (m + 2) (by omega)
  have h2 := h1.bex (m + 2) (m + 1) (by omega)
  have h3 := h2.bex (m + 1) m (by omega)
  have h := h3.bex m e (by omega)
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · rintro ⟨q, -, t, -, s, -, g, -, H, rfl⟩; exact H
    · intro H
      exact ⟨_, by rw [H]; exact upair_mem_pair _ _, _, mem_upair_right _ _,
        _, singleton_mem_pair _ _, _, ZFSet.mem_singleton.mpr rfl, H, rfl⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- `v b = ⟨4, ⟨i, ⟨3, ⟨⟨2, ⟨i, p⟩⟩, d⟩⟩⟩⟩`: the code of `∀i ∈ p, …`. -/
theorem delta0_ballCodeShape (b i p d : ℕ) (hbi : b ≠ i) (hbp : b ≠ p) (hbd : b ≠ d) :
    Delta0Def.{u} {b, i, p, d} (fun _ v => v b =
      ZFSet.pair (natZ 4) (ZFSet.pair (v i)
        (ZFSet.pair (natZ 3) (ZFSet.pair (ZFSet.pair (natZ 2) (ZFSet.pair (v i) (v p)))
          (v d))))) := by
  set m := b + i + p + d + 1 with hm
  -- q := m, t := m+1, s := m+2, c := m+3
  have h0 := (delta0_tagPair 4 b i (m + 3) (by omega) (by omega)).and
    (delta0_ballBodyShape (m + 3) i p d (by omega) (by omega) (by omega))
  have h1 := h0.bex (m + 3) (m + 2) (by omega)
  have h2 := h1.bex (m + 2) (m + 1) (by omega)
  have h3 := h2.bex (m + 1) m (by omega)
  have h := h3.bex m b (by omega)
  refine (h.congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · rintro ⟨q, -, t, -, s, -, c, -, H, rfl⟩; exact H
    · intro H
      exact ⟨_, by rw [H]; exact upair_mem_pair _ _, _, mem_upair_right _ _,
        _, mem_upair_right _ _, _, mem_upair_right _ _, H, rfl⟩
  · intro k hk; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union] at hk ⊢; omega

/-! ### Deciding boundedness on codes -/

/-- `e` is the code of the body `i ∈ j → ψ` of a bounded quantifier `∀i ∈ j` (`j ≠ i`).  This is
the paper's distinction between bounded and unbounded quantifiers, read off the code. -/
def IsBallBodyW (w i e : ZFSet.{u}) : Prop :=
  ∃ j ∈ w, ∃ q ∈ e, ∃ t ∈ q, ∃ s ∈ t, ∃ c ∈ s, j ≠ i ∧
    e = ZFSet.pair (natZ 3) (ZFSet.pair (ZFSet.pair (natZ 2) (ZFSet.pair i j)) c)

theorem delta0_isBallBodyW (a b c : ℕ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Delta0Def.{u} {a, b, c} (fun _ v => IsBallBodyW (v a) (v b) (v c)) := by
  set m := a + b + c + 1 with hm
  -- j := m, q := m+1, t := m+2, s := m+3, c' := m+4
  have h0 := (Delta0Def.eq.{u} m b).not.and
    (delta0_ballBodyShape c b m (m + 4) (by omega) (by omega) (by omega))
  have h1 := h0.bex (m + 4) (m + 3) (by omega)
  have h2 := h1.bex (m + 3) (m + 2) (by omega)
  have h3 := h2.bex (m + 2) (m + 1) (by omega)
  have h4 := h3.bex (m + 1) c (by omega)
  have h := h4.bex m a (by omega)
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    rfl
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

theorem codeShape_mem {ψ : Fm} {a b : ZFSet.{u}}
    (h : ψ.code = ZFSet.pair (natZ 2) (ZFSet.pair a b)) :
    ∃ i j : ℕ, ψ = Fm.mem i j ∧ a = natZ i ∧ b = natZ j := by
  cases ψ with
  | falsum => rw [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | eq i j => rw [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | mem i j =>
    rw [Fm.code, ZFSet.pair_inj, ZFSet.pair_inj] at h
    exact ⟨i, j, rfl, h.2.1.symm, h.2.2.symm⟩
  | imp _ _ => rw [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | all _ _ => rw [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))

/-- The Δ₀ test on codes is the syntactic test of `Bm4/SetTheory/Rel.lean`. -/
theorem isBallBodyW_iff (i : ℕ) (φ : Fm) :
    IsBallBodyW ωZ.{u} (natZ i) φ.code ↔ Fm.isBallBody i φ = true := by
  constructor
  · rintro ⟨j, hj, q, -, t, -, s, -, c, -, hji, hshape⟩
    obtain ⟨j₀, rfl⟩ := mem_ωZ_iff.mp hj
    obtain ⟨φ₁, φ₂, rfl, hc₁, rfl⟩ := nfCodeShape_imp hshape
    obtain ⟨i', j', rfl, hi', hj'⟩ := codeShape_mem hc₁.symm
    obtain rfl := natZ_injective hi'
    obtain rfl := natZ_injective hj'
    exact (Fm.isBallBody_iff i _).mpr ⟨_, φ₂, fun hh => hji (by rw [hh]), rfl⟩
  · intro h
    obtain ⟨j, ψ, hj, rfl⟩ := (Fm.isBallBody_iff i φ).mp h
    refine ⟨natZ j, natZ_mem_ωZ j, _, upair_mem_pair _ _, _, mem_upair_right _ _,
      _, mem_upair_right _ _, _, mem_upair_right _ _,
      fun hh => hj (natZ_injective hh), rfl⟩

/-! ### The local rules -/

/-- Local rule at an atomic node: relativization leaves atoms alone. -/
def RelAtomR (w _p e v : ZFSet.{u}) : Prop := IsAtomicCodeW w e ∧ v = ZFSet.pair e e

/-- Local rule at an `imp` node: componentwise, exactly as for substitution. -/
abbrev RelImpR : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop := SbImpR

/-- Local rule at an `all` node: a bounded quantifier is copied, an unbounded one is restricted
to the parameter `p`. -/
def RelAllR (w p i v₁ v : ZFSet.{u}) : Prop :=
  ∃ q₁ ∈ v₁, ∃ e₁ ∈ q₁, ∃ d₁ ∈ q₁, ∃ r ∈ v, ∃ a ∈ r, ∃ b ∈ r,
    v₁ = ZFSet.pair e₁ d₁ ∧ v = ZFSet.pair a b ∧
    a = ZFSet.pair (natZ 4) (ZFSet.pair i e₁) ∧
    ((IsBallBodyW w i e₁ ∧ b = ZFSet.pair (natZ 4) (ZFSet.pair i d₁)) ∨
     (¬ IsBallBodyW w i e₁ ∧ b = ZFSet.pair (natZ 4) (ZFSet.pair i
        (ZFSet.pair (natZ 3)
          (ZFSet.pair (ZFSet.pair (natZ 2) (ZFSet.pair i p)) d₁)))))

theorem delta0_relAtomR (a b c d : ℕ) (hac : a ≠ c) (hcd : c ≠ d) :
    Delta0Def.{u} {a, b, c, d} (fun _ v => RelAtomR (v a) (v b) (v c) (v d)) :=
  (((delta0_isAtomicCodeW a c hac).and
      (delta0_isKPair d c c (Ne.symm hcd) (Ne.symm hcd))).congr
    (fun _ _ _ _ => Iff.rfl)).mono
    (by intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at hk ⊢
        tauto)

theorem delta0_relAllR (a b c d e : ℕ) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    Delta0Def.{u} {a, b, c, d, e} (fun _ v => RelAllR (v a) (v b) (v c) (v d) (v e)) := by
  set m := a + b + c + d + e + 1 with hm
  -- q₁ := m, e₁ := m+1, d₁ := m+2, r := m+3, A := m+4, B := m+5
  have h0 := (delta0_isKPair d (m + 1) (m + 2) (by omega) (by omega)).and
    ((delta0_isKPair e (m + 4) (m + 5) (by omega) (by omega)).and
      ((delta0_tagPair 4 (m + 4) c (m + 1) (by omega) (by omega)).and
        (((delta0_isBallBodyW a c (m + 1) (by omega) (by omega) (by omega)).and
            (delta0_tagPair 4 (m + 5) c (m + 2) (by omega) (by omega))).or
         ((delta0_isBallBodyW a c (m + 1) (by omega) (by omega) (by omega)).not.and
            (delta0_ballCodeShape (m + 5) c b (m + 2) (by omega) (by omega) (by omega))))))
  have h1 := h0.bex (m + 5) (m + 3) (by omega)
  have h2 := h1.bex (m + 4) (m + 3) (by omega)
  have h3 := h2.bex (m + 3) e (by omega)
  have h4 := h3.bex (m + 2) m (by omega)
  have h5 := h4.bex (m + 1) m (by omega)
  have h := h5.bex m d (by omega)
  refine (h.congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    rfl
  · intro k hk; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union] at hk ⊢; omega

/-! ### The graph of relativization -/

/-- The graph of relativization: `d` is the code of `φ^M` for the formula `φ` coded by `e`, the
parameter `p` naming the variable `m`. -/
def RelToW (h w p e d : ZFSet.{u}) : Prop :=
  ∃ s ∈ h, ∃ t ∈ h, DerSeqW w s ∧ TraceW w RelAtomR RelImpR RelAllR p s t ∧
    ∃ P ∈ s, ∃ Q ∈ P, ∃ k ∈ Q, P = ZFSet.pair k e ∧
      ∃ P' ∈ t, ∃ Q' ∈ P', ∃ z ∈ Q', P' = ZFSet.pair k z ∧ z = ZFSet.pair e d

theorem relToW_iff_graphW (h w p e d : ZFSet.{u}) :
    RelToW h w p e d ↔ GraphW h w RelAtomR RelImpR RelAllR p e (ZFSet.pair e d) := by
  constructor
  · rintro ⟨s, hs, t, ht, hd, htr, P, hP, Q, -, k, -, rfl, P', hP', Q', -, z, -, rfl, rfl⟩
    exact ⟨s, hs, t, ht, hd, htr, k, hP, hP'⟩
  · rintro ⟨s, hs, t, ht, hd, htr, k, hke, hkd⟩
    exact ⟨s, hs, t, ht, hd, htr, _, hke, _, upair_mem_pair _ _, k, mem_upair_left _ _, rfl,
      _, hkd, _, upair_mem_pair _ _, _, mem_upair_right _ _, rfl, rfl⟩

/-- Lemma 12.2 (1) for relativization: the graph is Δ₀. -/
theorem delta0_relToW (h w p e d : ℕ)
    (hhw : h ≠ w) (hhp : h ≠ p) (hhe : h ≠ e) (hhd : h ≠ d)
    (hwp : w ≠ p) (hwe : w ≠ e) (hwd : w ≠ d) (hpe : p ≠ e) (hpd : p ≠ d) (hed : e ≠ d) :
    Delta0Def.{u} {h, w, p, e, d} (fun _ v => RelToW (v h) (v w) (v p) (v e) (v d)) := by
  set m := h + w + p + e + d + 1 with hm
  -- s := m, t := m+1, P := m+2, Q := m+3, k := m+4, P' := m+5, Q' := m+6, z := m+7
  have i0 := (delta0_isKPair (m + 5) (m + 4) (m + 7) (by omega) (by omega)).and
    (delta0_isKPair (m + 7) e d (by omega) (by omega))
  have i1 := i0.bex (m + 7) (m + 6) (by omega)
  have i2 := i1.bex (m + 6) (m + 5) (by omega)
  have i3 := i2.bex (m + 5) (m + 1) (by omega)
  have b0 := (delta0_isKPair (m + 2) (m + 4) e (by omega) (by omega)).and i3
  have b1 := b0.bex (m + 4) (m + 3) (by omega)
  have b2 := b1.bex (m + 3) (m + 2) (by omega)
  have b3 := b2.bex (m + 2) m (by omega)
  have dd := (delta0_derSeqW w m (by omega)).and
    ((delta0_traceW (A := RelAtomR) (I := RelImpR) (U := RelAllR) w p m (m + 1)
      (fun a b c d _ h2 _ _ _ h6 => delta0_relAtomR a b c d h2 h6)
      (fun a b c d e _ h2 h3 h4 _ _ _ h8 h9 h10 => delta0_sbImpR a b c d e h2 h3 h4 h8 h9 h10)
      (fun a b c d e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
        delta0_relAllR a b c d e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).and b3)
  have hh1 := dd.bex (m + 1) h (by omega)
  have hh := hh1.bex m h (by omega)
  refine (hh.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    rfl
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-! ### The rules do hold at the codes -/

theorem relTo_all_of_isBallBody (m i : ℕ) (φ : Fm) (h : Fm.isBallBody i φ = true) :
    Fm.relTo m (Fm.all i φ) = Fm.all i (Fm.relTo m φ) := by
  show (if Fm.isBallBody i φ then _ else _) = _
  rw [if_pos h]

theorem relTo_atomic {φ : Fm} (m : ℕ) (h : IsAtomicCodeW ωZ.{u} φ.code) :
    Fm.relTo m φ = φ := by
  rcases isAtomicCodeW_shape h with hc | ⟨i, j, hc⟩ | ⟨i, j, hc⟩ <;>
    obtain rfl := Fm.code_injective hc <;> rfl

/-- An atomic code together with the (identical) code of its relativization. -/
theorem isAtomicCodeW_rel (m : ℕ) {e : ZFSet.{u}} (h : IsAtomicCodeW ωZ e) :
    ∃ φ : Fm, e = φ.code ∧ Fm.relTo m φ = φ := by
  rcases isAtomicCodeW_shape h with hc | ⟨i, j, hc⟩ | ⟨i, j, hc⟩
  · exact ⟨Fm.falsum, hc, rfl⟩
  · exact ⟨Fm.eq i j, hc, rfl⟩
  · exact ⟨Fm.mem i j, hc, rfl⟩

theorem relAtomR_of_atomic (m : ℕ) {φ : Fm} (h : IsAtomicCodeW ωZ.{u} φ.code) :
    RelAtomR ωZ.{u} (natZ m) φ.code (ZFSet.pair φ.code (Fm.relTo m φ).code) :=
  ⟨h, by rw [relTo_atomic m h]⟩

/-- The `imp` rule holds of any pairs, whichever operation the components come from. -/
theorem sbImpR_pairs (w p a₁ b₁ a₂ b₂ : ZFSet.{u}) :
    SbImpR w p (ZFSet.pair a₁ b₁) (ZFSet.pair a₂ b₂)
      (ZFSet.pair (ZFSet.pair (natZ 3) (ZFSet.pair a₁ a₂))
        (ZFSet.pair (natZ 3) (ZFSet.pair b₁ b₂))) :=
  ⟨_, upair_mem_pair _ _, _, mem_upair_left _ _, _, mem_upair_right _ _,
   _, upair_mem_pair _ _, _, mem_upair_left _ _, _, mem_upair_right _ _,
   _, upair_mem_pair _ _, _, mem_upair_left _ _, _, mem_upair_right _ _,
   rfl, rfl, rfl, rfl, rfl⟩

theorem relImpR_intro (m : ℕ) (φ ψ : Fm) :
    RelImpR ωZ.{u} (natZ m)
      (ZFSet.pair φ.code (Fm.relTo m φ).code)
      (ZFSet.pair ψ.code (Fm.relTo m ψ).code)
      (ZFSet.pair (Fm.imp φ ψ).code (Fm.relTo m (Fm.imp φ ψ)).code) :=
  sbImpR_pairs _ _ _ _ _ _

theorem relAllR_intro (m i : ℕ) (φ : Fm) :
    RelAllR ωZ.{u} (natZ m) (natZ i)
      (ZFSet.pair φ.code (Fm.relTo m φ).code)
      (ZFSet.pair (Fm.all i φ).code (Fm.relTo m (Fm.all i φ)).code) := by
  refine ⟨_, upair_mem_pair _ _, _, mem_upair_left _ _, _, mem_upair_right _ _,
    _, upair_mem_pair _ _, _, mem_upair_left _ _, _, mem_upair_right _ _, rfl, rfl, rfl, ?_⟩
  by_cases hb : Fm.isBallBody i φ = true
  · refine Or.inl ⟨(isBallBodyW_iff i φ).mpr hb, ?_⟩
    rw [relTo_all_of_isBallBody m i φ hb]
    rfl
  · refine Or.inr ⟨fun hh => hb ((isBallBodyW_iff i φ).mp hh), ?_⟩
    rw [Fm.relTo_all_of_not m i φ (by simpa using hb)]
    rfl

/-! ### Soundness -/

theorem traceW_rel_entry {m : ℕ} {s t : ZFSet.{u}}
    (ht : TraceW ωZ RelAtomR RelImpR RelAllR (natZ m) s t) :
    ∀ n e v, ZFSet.pair (natZ n) e ∈ s → ZFSet.pair (natZ n) v ∈ t →
      ∃ φ : Fm, e = φ.code ∧ v = ZFSet.pair φ.code (Fm.relTo m φ).code := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro e v he hv
  obtain ⟨v', hv', H⟩ := ht.2 _ _ he
  obtain rfl : v' = v := ht.1.2 _ _ _ hv' hv
  rcases H with ⟨hat, rfl⟩ | ⟨k₁, hk₁, k₂, hk₂, e₁, e₂, v₁, v₂, h₁, h₂, g₁, g₂, rfl, HI⟩ |
    ⟨k₁, hk₁, e₁, v₁, i, hi, h₁, g₁, rfl, HU⟩
  · obtain ⟨φ, rfl, hr⟩ := isAtomicCodeW_rel m hat
    exact ⟨φ, rfl, by rw [hr]⟩
  · obtain ⟨n₁, hn₁, rfl⟩ := mem_natZ_iff.mp hk₁
    obtain ⟨n₂, hn₂, rfl⟩ := mem_natZ_iff.mp hk₂
    obtain ⟨φ₁, rfl, rfl⟩ := ih n₁ hn₁ e₁ v₁ h₁ g₁
    obtain ⟨φ₂, rfl, rfl⟩ := ih n₂ hn₂ e₂ v₂ h₂ g₂
    obtain ⟨q₁, -, a₁, -, b₁, -, q₂, -, a₂, -, b₂, -, r, -, A, -, B, -,
      hv₁, hv₂, rfl, hA', hB'⟩ := HI
    rw [ZFSet.pair_inj] at hv₁ hv₂
    obtain ⟨rfl, rfl⟩ := hv₁
    obtain ⟨rfl, rfl⟩ := hv₂
    exact ⟨Fm.imp φ₁ φ₂, rfl, by rw [hA', hB']; rfl⟩
  · obtain ⟨n₁, hn₁, rfl⟩ := mem_natZ_iff.mp hk₁
    obtain ⟨φ₁, rfl, rfl⟩ := ih n₁ hn₁ e₁ v₁ h₁ g₁
    obtain ⟨i₀, rfl⟩ := mem_ωZ_iff.mp hi
    obtain ⟨q₁, -, a₁, -, b₁, -, r, -, A, -, B, -, hv₁, rfl, hA', hB'⟩ := HU
    rw [ZFSet.pair_inj] at hv₁
    obtain ⟨rfl, rfl⟩ := hv₁
    refine ⟨Fm.all i₀ φ₁, rfl, ?_⟩
    rcases hB' with ⟨hbb, rfl⟩ | ⟨hbb, rfl⟩
    · rw [hA', relTo_all_of_isBallBody m i₀ φ₁ ((isBallBodyW_iff i₀ φ₁).mp hbb)]; rfl
    · rw [hA', Fm.relTo_all_of_not m i₀ φ₁
        (by simpa using fun hh => hbb ((isBallBodyW_iff i₀ φ₁).mpr hh))]
      rfl

/-! ### Completeness -/

open Classical in
/-- The value the rules attach to a code: the pair of the code and the code of its
relativization. -/
noncomputable def relValZ (m : ℕ) (e : ZFSet.{u}) : ZFSet.{u} :=
  if h : ∃ φ : Fm, e = φ.code then ZFSet.pair e (Fm.relTo m h.choose).code
  else ZFSet.pair e e

theorem relValZ_code (m : ℕ) (φ : Fm) :
    relValZ.{u} m φ.code = ZFSet.pair φ.code (Fm.relTo m φ).code := by
  have h : ∃ ψ : Fm, (φ.code : ZFSet.{u}) = ψ.code := ⟨φ, rfl⟩
  rw [relValZ, dif_pos h]
  have : h.choose = φ := (Fm.code_injective h.choose_spec).symm
  rw [this]

theorem relValZ_mem_Lω (m : ℕ) {e : ZFSet.{u}} (he : ∃ φ : Fm, e = φ.code) :
    relValZ.{u} m e ∈ L Ordinal.omega0 := by
  obtain ⟨φ, rfl⟩ := he
  rw [relValZ_code]
  exact kpair_mem_Lω φ.code_mem_Lω (Fm.relTo m φ).code_mem_Lω

theorem traceW_rel_seqOf_der (m : ℕ) (φ : Fm) :
    TraceW ωZ.{u} RelAtomR RelImpR RelAllR (natZ m)
      (seqOfAux 0 (Fm.der.{u} φ)) (seqOfAux 0 ((Fm.der.{u} φ).map (relValZ m))) := by
  refine ⟨isFunc_seqOfAux _, ?_⟩
  intro k e hke
  obtain ⟨n, z, hz, hp⟩ := mem_seqOfAux.mp hke
  rw [ZFSet.pair_inj] at hp
  obtain ⟨hk, he⟩ := hp
  subst hk
  subst he
  have key : ∀ (j : ℕ) (y' : ZFSet.{u}), (Fm.der.{u} φ)[j]? = some y' →
      ZFSet.pair (natZ j) (relValZ m y') ∈ seqOfAux 0 ((Fm.der.{u} φ).map (relValZ m)) := by
    intro j y' hy'
    exact mem_seqOfAux.mpr ⟨j, relValZ m y', by simp [hy'], by simp⟩
  have keys : ∀ (j : ℕ) (y' : ZFSet.{u}), (Fm.der.{u} φ)[j]? = some y' →
      ZFSet.pair (natZ j) y' ∈ seqOfAux 0 (Fm.der.{u} φ) := by
    intro j y' hy'
    exact mem_seqOfAux.mpr ⟨j, y', hy', by simp⟩
  refine ⟨relValZ m e, by simpa using key n e hz, ?_⟩
  have hzmem : e ∈ Fm.der.{u} φ := by
    obtain ⟨hn, hh⟩ := List.getElem?_eq_some_iff.mp hz
    exact hh ▸ List.getElem_mem hn
  obtain ⟨ψ₀, rfl⟩ := Fm.mem_der.{u} φ e hzmem
  obtain ⟨y', hy', H⟩ := Fm.der_good.{u} φ n ψ₀.code hz
  rw [hz] at hy'
  obtain rfl := Option.some.inj hy'
  rcases H with H | ⟨n₁, hn₁, n₂, hn₂, y₁, y₂, hy₁, hy₂, H⟩ | ⟨n₁, hn₁, y₁, i, hy₁, H⟩
  · rw [relValZ_code]
    exact Or.inl (relAtomR_of_atomic m H)
  · obtain ⟨ψ₁, ψ₂, rfl, rfl, rfl⟩ := nfCodeShape_imp H
    refine Or.inr (Or.inl ⟨natZ n₁, by simpa [natZ_mem_natZ_iff] using hn₁, natZ n₂,
      by simpa [natZ_mem_natZ_iff] using hn₂, ψ₁.code, ψ₂.code, relValZ m ψ₁.code,
      relValZ m ψ₂.code, keys _ _ hy₁, keys _ _ hy₂, key _ _ hy₁, key _ _ hy₂, rfl, ?_⟩)
    rw [relValZ_code, relValZ_code, relValZ_code]
    exact relImpR_intro m ψ₁ ψ₂
  · obtain ⟨ψ₁, rfl, rfl⟩ := nfCodeShape_all H
    refine Or.inr (Or.inr ⟨natZ n₁, by simpa [natZ_mem_natZ_iff] using hn₁, ψ₁.code,
      relValZ m ψ₁.code, natZ i, natZ_mem_ωZ i, keys _ _ hy₁, key _ _ hy₁, rfl, ?_⟩)
    rw [relValZ_code, relValZ_code]
    exact relAllR_intro m i ψ₁

/-! ### Lemma 12.2 (1) for relativization -/

/-- Correctness of the instance: `RelToW` relates exactly the code of a formula and the code of
its relativization.  With `delta0_relToW` this is Lemma 12.2 (1) for relativization. -/
theorem relToW_iff (m : ℕ) (e d : ZFSet.{u}) :
    RelToW (L Ordinal.omega0) ωZ (natZ m) e d ↔
      ∃ φ : Fm, e = φ.code ∧ d = (Fm.relTo m φ).code := by
  rw [relToW_iff_graphW]
  constructor
  · rintro ⟨s, -, t, -, hs, ht, k, hke, hkd⟩
    obtain ⟨dm, hdm, hdom⟩ := hs.2.1
    have hkd' : k ∈ dm := (hdom k).mpr ⟨e, hke⟩
    obtain ⟨M, rfl⟩ := mem_ωZ_iff.mp hdm
    obtain ⟨q, -, rfl⟩ := mem_natZ_iff.mp hkd'
    obtain ⟨φ, rfl, hval⟩ := traceW_rel_entry ht q e _ hke hkd
    rw [ZFSet.pair_inj] at hval
    exact ⟨φ, rfl, hval.2⟩
  · rintro ⟨φ, rfl, rfl⟩
    refine ⟨seqOfAux 0 (Fm.der.{u} φ), ?_,
      seqOfAux 0 ((Fm.der.{u} φ).map (relValZ m)), ?_,
      derSeqW_seqOf_der φ, traceW_rel_seqOf_der m φ,
      natZ ((Fm.der.{u} φ).length - 1), ?_, ?_⟩
    · apply seqOfAux_mem_Lω
      intro w hw
      obtain ⟨ψ, rfl⟩ := Fm.mem_der.{u} φ w hw
      exact ψ.code_mem_Lω
    · apply seqOfAux_mem_Lω
      intro w hw
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw
      exact relValZ_mem_Lω m (Fm.mem_der.{u} φ z hz)
    · exact mem_seqOfAux.mpr ⟨(Fm.der.{u} φ).length - 1, φ.code, Fm.der_last.{u} φ, by simp⟩
    · refine mem_seqOfAux.mpr ⟨(Fm.der.{u} φ).length - 1,
        ZFSet.pair φ.code (Fm.relTo m φ).code, ?_, by simp⟩
      rw [List.getElem?_map, Fm.der_last.{u} φ]
      exact congrArg some (relValZ_code m φ)

end BM4.ST
