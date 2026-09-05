/-
  Part III, §12: the graph of variable renaming is Δ₀ (Lemma 12.2 (1)).

  `Fm.rename f` of `Bm4/SetTheory/Fm.lean` applies `f` uniformly to every variable, free and
  bound.  Lemma 12.2 (1) asserts that on codes the relation

      G(ν, e, d)  ⟺  `e` codes `φ` and `d` codes `φ` renamed along the finite map coded by `ν`

  is Δ₀.  As before this is an instance of the schema (8.3) — `GraphW` / `delta0_graphW` of
  `Bm4/SetTheory/CodeFV.lean`.  The renaming map is a *parameter*: `ν` is a set of Kuratowski
  pairs and `⟨i, i'⟩ ∈ ν` is the Δ₀ predicate `delta0_funVal` of `Bm4/SetTheory/HF.lean`.

  Unlike substitution and relativization, renaming needs no information about the children beyond
  their outputs, so here the trace value is simply the output code and `RenW` is `GraphW` itself.

  The correctness statement `renW_iff` takes `ν` to agree with an actual map `f` (`hν`) and to
  cover the variables of `φ` (`hcov`) — exactly the finiteness-friendly reading of the paper: `ν`
  need only be defined on the finitely many variables that occur.
-/
import Bm4.SetTheory.SynSubst

universe u

namespace BM4.ST

open Fm

/-! ### The local rules -/

/-- Local rule at an atomic node: both variable slots are moved along `p`. -/
def RenAtomR (w p e v : ZFSet.{u}) : Prop :=
  (e = ZFSet.pair (natZ 0) (natZ 0) ∧ v = e) ∨
  ∃ i ∈ w, ∃ j ∈ w, ∃ i' ∈ w, ∃ j' ∈ w,
    ZFSet.pair i i' ∈ p ∧ ZFSet.pair j j' ∈ p ∧
    ((e = ZFSet.pair (natZ 1) (ZFSet.pair i j) ∧
        v = ZFSet.pair (natZ 1) (ZFSet.pair i' j')) ∨
     (e = ZFSet.pair (natZ 2) (ZFSet.pair i j) ∧
        v = ZFSet.pair (natZ 2) (ZFSet.pair i' j')))

/-- Local rule at an `imp` node. -/
def RenImpR (_w _p v₁ v₂ v : ZFSet.{u}) : Prop := v = ZFSet.pair (natZ 3) (ZFSet.pair v₁ v₂)

/-- Local rule at an `all` node: the bound variable too is moved along `p`. -/
def RenAllR (w p i v₁ v : ZFSet.{u}) : Prop :=
  ∃ i' ∈ w, ZFSet.pair i i' ∈ p ∧ v = ZFSet.pair (natZ 4) (ZFSet.pair i' v₁)

theorem delta0_renAtomR (a b c d : ℕ) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Delta0Def.{u} {a, b, c, d} (fun _ v => RenAtomR (v a) (v b) (v c) (v d)) := by
  set m := a + b + c + d + 1 with hm
  -- i := m, j := m+1, i' := m+2, j' := m+3
  have h0 := (delta0_funVal b m (m + 2) (by omega) (by omega) (by omega)).and
    ((delta0_funVal b (m + 1) (m + 3) (by omega) (by omega) (by omega)).and
      (((delta0_tagPair 1 c m (m + 1) (by omega) (by omega)).and
          (delta0_tagPair 1 d (m + 2) (m + 3) (by omega) (by omega))).or
       ((delta0_tagPair 2 c m (m + 1) (by omega) (by omega)).and
          (delta0_tagPair 2 d (m + 2) (m + 3) (by omega) (by omega)))))
  have h1 := h0.bex (m + 3) a (by omega)
  have h2 := h1.bex (m + 2) a (by omega)
  have h3 := h2.bex (m + 1) a (by omega)
  have h4 := h3.bex m a (by omega)
  have h := ((delta0_tagPair0 c).and (Delta0Def.eq.{u} d c)).or h4
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    rfl
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

theorem delta0_renImpR (a b c d e : ℕ) (hec : e ≠ c) (hed : e ≠ d) :
    Delta0Def.{u} {a, b, c, d, e} (fun _ v => RenImpR (v a) (v b) (v c) (v d) (v e)) :=
  (((delta0_tagPair 3 e c d hec hed).congr (fun _ _ _ _ => Iff.rfl))).mono
    (by intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk ⊢
        tauto)

theorem delta0_renAllR (a b c d e : ℕ) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    Delta0Def.{u} {a, b, c, d, e} (fun _ v => RenAllR (v a) (v b) (v c) (v d) (v e)) := by
  set m := a + b + c + d + e + 1 with hm
  have h0 := (delta0_funVal b c m (by omega) (by omega) (by omega)).and
    (delta0_tagPair 4 e m d (by omega) (by omega))
  have h := h0.bex m a (by omega)
  refine (h.congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    rfl
  · intro k hk; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union] at hk ⊢; omega

/-! ### The graph of renaming -/

/-- The graph of renaming, read straight off the schema (8.3). -/
def RenW (h w p e d : ZFSet.{u}) : Prop := GraphW h w RenAtomR RenImpR RenAllR p e d

/-- Lemma 12.2 (1) for variable renaming: the graph is Δ₀. -/
theorem delta0_renW (h w p e d : ℕ)
    (hhw : h ≠ w) (hhp : h ≠ p) (hhe : h ≠ e) (hhd : h ≠ d)
    (hwp : w ≠ p) (hwe : w ≠ e) (hwd : w ≠ d) (hpe : p ≠ e) (hpd : p ≠ d) (hed : e ≠ d) :
    Delta0Def.{u} {h, w, p, e, d} (fun _ v => RenW (v h) (v w) (v p) (v e) (v d)) :=
  delta0_graphW h w p e d
    (fun a b c d hab hac had hbc hbd hcd => delta0_renAtomR a b c d hab hac had hbc hbd hcd)
    (fun a b c d e _ _ _ _ _ _ _ _ h9 h10 => delta0_renImpR a b c d e h9.symm h10.symm)
    (fun a b c d e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
      delta0_renAllR a b c d e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    hhw hhp hhe hhd hwp hwe hwd hpe hpd hed

/-! ### Subformulas keep the variables -/

theorem mem_der_vars (φ : Fm) :
    ∀ x ∈ Fm.der.{u} φ, ∃ ψ : Fm, x = ψ.code ∧ Fm.vars ψ ⊆ Fm.vars φ := by
  induction φ with
  | falsum => intro x hx; simp only [Fm.der, List.mem_singleton] at hx; exact ⟨_, hx, subset_rfl⟩
  | eq i j => intro x hx; simp only [Fm.der, List.mem_singleton] at hx; exact ⟨_, hx, subset_rfl⟩
  | mem i j => intro x hx; simp only [Fm.der, List.mem_singleton] at hx; exact ⟨_, hx, subset_rfl⟩
  | imp φ ψ ih₁ ih₂ =>
    intro x hx
    simp only [Fm.der, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx | rfl
    · obtain ⟨χ, rfl, hv⟩ := ih₁ x hx
      exact ⟨χ, rfl, hv.trans (by simp only [Fm.vars]; exact Finset.subset_union_left)⟩
    · obtain ⟨χ, rfl, hv⟩ := ih₂ x hx
      exact ⟨χ, rfl, hv.trans (by simp only [Fm.vars]; exact Finset.subset_union_right)⟩
    · exact ⟨_, rfl, subset_rfl⟩
  | all i φ ih =>
    intro x hx
    simp only [Fm.der, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · obtain ⟨χ, rfl, hv⟩ := ih x hx
      exact ⟨χ, rfl, hv.trans (by simp only [Fm.vars]; exact Finset.subset_insert _ _)⟩
    · exact ⟨_, rfl, subset_rfl⟩

/-! ### Correctness -/

variable {ν : ZFSet.{u}} {f : ℕ → ℕ}

theorem traceW_ren_entry (hν : ∀ i j : ℕ, ZFSet.pair (natZ.{u} i) (natZ j) ∈ ν → j = f i)
    {s t : ZFSet.{u}} (ht : TraceW ωZ RenAtomR RenImpR RenAllR ν s t) :
    ∀ n e v, ZFSet.pair (natZ n) e ∈ s → ZFSet.pair (natZ n) v ∈ t →
      ∃ φ : Fm, e = φ.code ∧ v = (Fm.rename f φ).code := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro e v he hv
  obtain ⟨v', hv', H⟩ := ht.2 _ _ he
  obtain rfl : v' = v := ht.1.2 _ _ _ hv' hv
  rcases H with hA | ⟨k₁, hk₁, k₂, hk₂, e₁, e₂, v₁, v₂, h₁, h₂, g₁, g₂, rfl, HI⟩ |
    ⟨k₁, hk₁, e₁, v₁, i, hi, h₁, g₁, rfl, HU⟩
  · rcases hA with ⟨hb, rfl⟩ | ⟨i, hi, j, hj, i', hi', j', hj', hmi, hmj, Hshape⟩
    · exact ⟨Fm.falsum, hb, by rw [hb]; rfl⟩
    · obtain ⟨i₀, rfl⟩ := mem_ωZ_iff.mp hi
      obtain ⟨j₀, rfl⟩ := mem_ωZ_iff.mp hj
      obtain ⟨i₁, rfl⟩ := mem_ωZ_iff.mp hi'
      obtain ⟨j₁, rfl⟩ := mem_ωZ_iff.mp hj'
      obtain rfl := hν i₀ i₁ hmi
      obtain rfl := hν j₀ j₁ hmj
      rcases Hshape with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨Fm.eq i₀ j₀, rfl, rfl⟩
      · exact ⟨Fm.mem i₀ j₀, rfl, rfl⟩
  · obtain ⟨n₁, hn₁, rfl⟩ := mem_natZ_iff.mp hk₁
    obtain ⟨n₂, hn₂, rfl⟩ := mem_natZ_iff.mp hk₂
    obtain ⟨φ₁, rfl, rfl⟩ := ih n₁ hn₁ e₁ v₁ h₁ g₁
    obtain ⟨φ₂, rfl, rfl⟩ := ih n₂ hn₂ e₂ v₂ h₂ g₂
    exact ⟨Fm.imp φ₁ φ₂, rfl, HI⟩
  · obtain ⟨n₁, hn₁, rfl⟩ := mem_natZ_iff.mp hk₁
    obtain ⟨φ₁, rfl, rfl⟩ := ih n₁ hn₁ e₁ v₁ h₁ g₁
    obtain ⟨i₀, rfl⟩ := mem_ωZ_iff.mp hi
    obtain ⟨i', hi', hmi, rfl⟩ := HU
    obtain ⟨i₁, rfl⟩ := mem_ωZ_iff.mp hi'
    obtain rfl := hν i₀ i₁ hmi
    exact ⟨Fm.all i₀ φ₁, rfl, rfl⟩

open Classical in
/-- The value the rules attach to a code: the code of the renamed formula. -/
noncomputable def renValZ (f : ℕ → ℕ) (e : ZFSet.{u}) : ZFSet.{u} :=
  if h : ∃ φ : Fm, e = φ.code then (Fm.rename f h.choose).code else e

theorem renValZ_code (f : ℕ → ℕ) (φ : Fm) :
    renValZ.{u} f φ.code = (Fm.rename f φ).code := by
  have h : ∃ ψ : Fm, (φ.code : ZFSet.{u}) = ψ.code := ⟨φ, rfl⟩
  rw [renValZ, dif_pos h]
  have : h.choose = φ := (Fm.code_injective h.choose_spec).symm
  rw [this]

theorem renValZ_mem_Lω (f : ℕ → ℕ) {e : ZFSet.{u}} (he : ∃ φ : Fm, e = φ.code) :
    renValZ.{u} f e ∈ L Ordinal.omega0 := by
  obtain ⟨φ, rfl⟩ := he
  rw [renValZ_code]
  exact (Fm.rename f φ).code_mem_Lω

theorem traceW_ren_seqOf_der (φ : Fm)
    (hcov : ∀ i ∈ Fm.vars φ, ZFSet.pair (natZ.{u} i) (natZ (f i)) ∈ ν) :
    TraceW ωZ.{u} RenAtomR RenImpR RenAllR ν
      (seqOfAux 0 (Fm.der.{u} φ)) (seqOfAux 0 ((Fm.der.{u} φ).map (renValZ f))) := by
  refine ⟨isFunc_seqOfAux _, ?_⟩
  intro k e hke
  obtain ⟨n, z, hz, hp⟩ := mem_seqOfAux.mp hke
  rw [ZFSet.pair_inj] at hp
  obtain ⟨hk, he⟩ := hp
  subst hk
  subst he
  have key : ∀ (j : ℕ) (y' : ZFSet.{u}), (Fm.der.{u} φ)[j]? = some y' →
      ZFSet.pair (natZ j) (renValZ f y') ∈ seqOfAux 0 ((Fm.der.{u} φ).map (renValZ f)) := by
    intro j y' hy'
    exact mem_seqOfAux.mpr ⟨j, renValZ f y', by simp [hy'], by simp⟩
  have keys : ∀ (j : ℕ) (y' : ZFSet.{u}), (Fm.der.{u} φ)[j]? = some y' →
      ZFSet.pair (natZ j) y' ∈ seqOfAux 0 (Fm.der.{u} φ) := by
    intro j y' hy'
    exact mem_seqOfAux.mpr ⟨j, y', hy', by simp⟩
  refine ⟨renValZ f e, by simpa using key n e hz, ?_⟩
  have hzmem : e ∈ Fm.der.{u} φ := by
    obtain ⟨hn, hh⟩ := List.getElem?_eq_some_iff.mp hz
    exact hh ▸ List.getElem_mem hn
  obtain ⟨ψ₀, rfl, hvars⟩ := mem_der_vars φ e hzmem
  obtain ⟨y', hy', H⟩ := Fm.der_good.{u} φ n ψ₀.code hz
  rw [hz] at hy'
  obtain rfl := Option.some.inj hy'
  rcases H with H | ⟨n₁, hn₁, n₂, hn₂, y₁, y₂, hy₁, hy₂, H⟩ | ⟨n₁, hn₁, y₁, i, hy₁, H⟩
  · rw [renValZ_code]
    refine Or.inl ?_
    rcases isAtomicCodeW_shape H with hc | ⟨i, j, hc⟩ | ⟨i, j, hc⟩ <;>
      obtain rfl := Fm.code_injective hc
    · exact Or.inl ⟨rfl, rfl⟩
    · refine Or.inr ⟨natZ i, natZ_mem_ωZ i, natZ j, natZ_mem_ωZ j, natZ (f i), natZ_mem_ωZ _,
        natZ (f j), natZ_mem_ωZ _, hcov i (hvars (by simp [Fm.vars])),
        hcov j (hvars (by simp [Fm.vars])), Or.inl ⟨rfl, rfl⟩⟩
    · refine Or.inr ⟨natZ i, natZ_mem_ωZ i, natZ j, natZ_mem_ωZ j, natZ (f i), natZ_mem_ωZ _,
        natZ (f j), natZ_mem_ωZ _, hcov i (hvars (by simp [Fm.vars])),
        hcov j (hvars (by simp [Fm.vars])), Or.inr ⟨rfl, rfl⟩⟩
  · obtain ⟨ψ₁, ψ₂, rfl, rfl, rfl⟩ := nfCodeShape_imp H
    refine Or.inr (Or.inl ⟨natZ n₁, by simpa [natZ_mem_natZ_iff] using hn₁, natZ n₂,
      by simpa [natZ_mem_natZ_iff] using hn₂, ψ₁.code, ψ₂.code, renValZ f ψ₁.code,
      renValZ f ψ₂.code, keys _ _ hy₁, keys _ _ hy₂, key _ _ hy₁, key _ _ hy₂, rfl, ?_⟩)
    show renValZ f (Fm.imp ψ₁ ψ₂).code = _
    rw [renValZ_code, renValZ_code, renValZ_code]
    rfl
  · obtain ⟨ψ₁, rfl, rfl⟩ := nfCodeShape_all H
    refine Or.inr (Or.inr ⟨natZ n₁, by simpa [natZ_mem_natZ_iff] using hn₁, ψ₁.code,
      renValZ f ψ₁.code, natZ i, natZ_mem_ωZ i, keys _ _ hy₁, key _ _ hy₁, rfl, ?_⟩)
    refine ⟨natZ (f i), natZ_mem_ωZ _, hcov i (hvars (by simp [Fm.vars])), ?_⟩
    show renValZ f (Fm.all i ψ₁).code = _
    rw [renValZ_code, renValZ_code]
    rfl

/-- Correctness of the instance: with `ν` agreeing with `f` and covering the variables of `φ`,
the graph relates exactly `φ.code` and `(rename f φ).code`.  With `delta0_renW` this is Lemma
12.2 (1) for variable renaming. -/
theorem renW_iff (hν : ∀ i j : ℕ, ZFSet.pair (natZ.{u} i) (natZ j) ∈ ν → j = f i)
    (φ : Fm) (hcov : ∀ i ∈ Fm.vars φ, ZFSet.pair (natZ.{u} i) (natZ (f i)) ∈ ν)
    (d : ZFSet.{u}) :
    RenW (L Ordinal.omega0) ωZ ν φ.code d ↔ d = (Fm.rename f φ).code := by
  constructor
  · rintro ⟨s, -, t, -, hs, ht, k, hke, hkd⟩
    obtain ⟨dm, hdm, hdom⟩ := hs.2.1
    have hkd' : k ∈ dm := (hdom k).mpr ⟨_, hke⟩
    obtain ⟨M, rfl⟩ := mem_ωZ_iff.mp hdm
    obtain ⟨q, -, rfl⟩ := mem_natZ_iff.mp hkd'
    obtain ⟨χ, hc, hval⟩ := traceW_ren_entry hν ht q _ d hke hkd
    obtain rfl := Fm.code_injective hc
    exact hval
  · rintro rfl
    refine ⟨seqOfAux 0 (Fm.der.{u} φ), ?_,
      seqOfAux 0 ((Fm.der.{u} φ).map (renValZ f)), ?_,
      derSeqW_seqOf_der φ, traceW_ren_seqOf_der φ hcov,
      natZ ((Fm.der.{u} φ).length - 1), ?_, ?_⟩
    · apply seqOfAux_mem_Lω
      intro w hw
      obtain ⟨ψ, rfl⟩ := Fm.mem_der.{u} φ w hw
      exact ψ.code_mem_Lω
    · apply seqOfAux_mem_Lω
      intro w hw
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw
      exact renValZ_mem_Lω f (Fm.mem_der.{u} φ z hz)
    · exact mem_seqOfAux.mpr ⟨(Fm.der.{u} φ).length - 1, φ.code, Fm.der_last.{u} φ, by simp⟩
    · refine mem_seqOfAux.mpr ⟨(Fm.der.{u} φ).length - 1, (Fm.rename f φ).code, ?_, by simp⟩
      rw [List.getElem?_map, Fm.der_last.{u} φ]
      exact congrArg some (renValZ_code f φ)

end BM4.ST
