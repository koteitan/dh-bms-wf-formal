/-
  Part V: initial labels, termination and well-foundedness (Lemma 20.1, Theorem 21.1,
  Theorem 1.2, Proposition 22.1), relative to a `LabelSystem`.
-/
import Bm4.Label

open Classical

universe u

namespace BM4

variable (S : LabelSystem.{u}) {r : ℕ}

/-! ### Lemma 20.1: the standard initial array has a stable label -/

theorem E_len (r : ℕ) : (E r).len = 2 := rfl

/-- Lemma 20.1. -/
theorem stable_E : ∃ f, Stable S (E r) f := by
  obtain ⟨Λ, Θ, hΛΘ⟩ := S.init
  refine ⟨fun i => if i = 0 then Λ else Θ, ?_, ?_⟩
  · intro i j hij hj
    have hj' : j < 2 := hj
    have hi0 : i = 0 := by omega
    have hj1 : j = 1 := by omega
    subst hi0; subst hj1
    simpa using S.rel_lt (hΛΘ 0)
  · intro k _ i j hj h
    have hij := anc_lt h
    have hj' : j < 2 := hj
    have hi0 : i = 0 := by omega
    have hj1 : j = 1 := by omega
    subst hi0; subst hj1
    simpa using hΛΘ k

/-- Every nonempty array of BM4 carries a stable label (Lemma 20.1 + Proposition 19.1). -/
theorem reachable_stable {A : Arr r} (hA : Reachable r A) (h0 : 0 < A.len) :
    ∃ f, Stable S A f := by
  induction hA with
  | init => exact stable_E S
  | @step A N hA ih =>
    by_cases hlen : A.len = 0
    · rw [expand_of_len_zero hlen] at h0
      omega
    · obtain ⟨f, hf⟩ := ih (Nat.pos_of_ne_zero hlen)
      obtain ⟨g, hg, _⟩ := descent S hf (Nat.pos_of_ne_zero hlen) N h0
      exact ⟨g, hg⟩

/-! ### Theorem 21.1 / Theorem 1.2: termination -/

theorem seq_succ_shift (A : Arr r) (n : ℕ → ℕ) (t : ℕ) :
    seq A n (t + 1) = seq (expand A (n 0)) (fun t => n (t + 1)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show expand (seq A n (t + 1)) (n (t + 1)) = expand (seq (expand A (n 0)) (fun t => n (t + 1)) t) (n (t + 1))
    rw [ih]

/-- ω-recursion (with Choice) behind Theorem 21.1: given a stable label `f₀` of `A` and the
assumption that no term of the expansion sequence `(A_t)_{t<ω}` is empty, Proposition 19.1
(`descent`) provides at each step *at least one* stable label of strictly smaller height;
`Classical.choose` picks one and `Nat.rec` iterates the choice through all of `ω`. -/
private noncomputable def chain {A : Arr r} {n : ℕ → ℕ}
    (hpos : ∀ t, 0 < (seq A n t).len) {f₀ : ℕ → S.Lab} (hf₀ : Stable S A f₀) :
    ∀ t, {g : ℕ → S.Lab // Stable S (seq A n t) g} :=
  Nat.rec ⟨f₀, hf₀⟩ fun t g =>
    ⟨_, (descent S g.2 (hpos t) (n t) (hpos (t + 1))).choose_spec.1⟩

/-- The heights along `chain` strictly decrease: `ht(f₀) > ht(f₁) > ht(f₂) > ⋯` (21.3). -/
private theorem chain_lt {A : Arr r} {n : ℕ → ℕ} (hpos : ∀ t, 0 < (seq A n t).len)
    {f₀ : ℕ → S.Lab} (hf₀ : Stable S A f₀) (t : ℕ) :
    ht S (seq A n (t + 1)) (chain S hpos hf₀ (t + 1)).1
      < ht S (seq A n t) (chain S hpos hf₀ t).1 :=
  (descent S (chain S hpos hf₀ t).2 (hpos t) (n t) (hpos (t + 1))).choose_spec.2

include S in
/-- **Theorem 21.1 / Theorem 1.2 (termination)**, relative to a label system: every expansion
sequence starting from an array of BM4 reaches the empty array.

The paper's proof: suppose no term is empty.  All terms are reachable and nonempty, so Lemma 20.1
plus Proposition 19.1 (`reachable_stable`) give a stable label `f₀` of `A₀ = A`, and Proposition
19.1 (`descent`) gives, at each step, a stable label of strictly smaller height.  Choice and
ω-recursion (`chain`) turn this into a sequence of stable labels with
`ht(f₀) > ht(f₁) > ht(f₂) > ⋯`.  The set of heights is a nonempty set of labels, hence has a
`<`-minimal element `ht(f_{t₀})` (`WellFounded.has_min`, the paper's Replacement + least
element), but `ht(f_{t₀+1})` lies in the same set and is smaller — contradiction. -/
theorem terminates (A : Arr r) (hA : Reachable r A) (n : ℕ → ℕ) :
    ∃ T, (seq A n T).len = 0 := by
  by_contra hcon
  push Not at hcon
  -- (1) the infinite nonempty expansion sequence
  have hpos : ∀ t, 0 < (seq A n t).len := fun t => Nat.pos_of_ne_zero (hcon t)
  -- (2) Lemma 20.1 + Proposition 19.1: a stable label `f₀` of `A₀ = A`
  obtain ⟨f₀, hf₀⟩ := reachable_stable S hA (hpos 0)
  -- (3) Choice + ω-recursion: the strictly decreasing chain of heights (21.3)
  have hdesc := chain_lt S hpos hf₀
  -- (4) the set of heights has a `<`-minimal element
  obtain ⟨β, ⟨t₀, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := S.Lab)).has_min
      (Set.range fun t => ht S (seq A n t) (chain S hpos hf₀ t).1)
      ⟨_, Set.mem_range_self 0⟩
  exact hmin _ (Set.mem_range_self (t₀ + 1)) (hdesc t₀)

/-- Once empty, the sequence stays empty. -/
theorem seq_len_zero_of_le {A : Arr r} {n : ℕ → ℕ} {T : ℕ} (hT : (seq A n T).len = 0) {t : ℕ}
    (ht : T ≤ t) : (seq A n t).len = 0 := by
  induction ht with
  | refl => exact hT
  | step _ ih => simp only [seq]; rw [expand_of_len_zero ih]; exact ih

/-! ### Proposition 22.1: well-foundedness of the one-step relation -/

include S in
/-- **Proposition 22.1**: the one-step expansion relation on BM4 is well-founded.

The paper's proof: if `R` were not well-founded there would be a nonempty `X ⊆ BM4` without an
`R`-minimal element, and ω-recursion along `X` would produce an infinite descending `R`-sequence
`(B_t)_{t<ω}`.  Unfolding `R` gives `B_{t+1} = B_t[n_t]` with every `B_t` reachable and nonempty,
so `B_t = seq B₀ n t` and Theorem 1.2 makes some `B_T` empty — contradiction. -/
theorem R_wf (r : ℕ) : WellFounded (R r) := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  refine ⟨fun B => ?_⟩
  obtain ⟨B, hB⟩ := B
  -- (2) unfold `R`; Choice turns the step-wise existentials into a function `n : ℕ → ℕ`
  have hstep : ∀ t, ∃ N, B (t + 1) = expand (B t) N := fun t => (hB t).2.2
  choose n hn using hstep
  -- (3) the descending chain is the expansion sequence of `B 0`
  have hBseq : ∀ t, B t = seq (B 0) n t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [hn t, ih]; rfl
  obtain ⟨T, hT⟩ := terminates S (B 0) (hB 0).1 n
  have hlen : 0 < (B T).len := (hB T).2.1
  rw [hBseq T, hT] at hlen
  exact absurd hlen (lt_irrefl 0)

include S in
/-- Its strict transitive closure is well-founded as well (the paper's separate argument for `R⁺`
proves the same fact). -/
theorem transGen_R_wf (r : ℕ) : WellFounded (Relation.TransGen (R r)) :=
  (R_wf S r).transGen

end BM4
