/-
  Part III, §12: substitution (Lemma 12.2 (1)).

  Lemma 12.2 (1) lists *substitution* among the safe syntactic operations, next to variable
  renaming and the avoidance of bound-variable capture.  Since the language is `{∈}` and the only
  terms are variables, the substitution meant there is the substitution of a variable for a
  variable, `φ[x := y]`.  It is not the renaming `Fm.rename` of `Bm4/SetTheory/Fm.lean`: that one
  applies an injective map uniformly to *all* variables, free and bound, whereas substitution
  replaces the free occurrences of one variable and may identify two variables.

  Because capture avoidance is listed by the paper as a *separate* operation, the substitution
  here is the naive one: `∀x φ` blocks the substitution of `x`, and the correctness statement
  `sat_subst` carries the capture hypothesis `y ∉ bv φ` rather than renaming anything.

  As required by the lemma, the equivalence
      `Sat D v (φ[x := y])  ↔  Sat D (v[x ↦ v y]) φ`
  is proved for an *arbitrary* domain predicate `D`: no nonemptiness, no transitivity.
-/
import Bm4.SetTheory.Fm

universe u

namespace BM4.ST
namespace Fm

/-! ### Bound variables -/

/-- The variables bound by a quantifier of `φ`. -/
def bv : Fm → Finset ℕ
  | falsum => ∅
  | eq _ _ => ∅
  | mem _ _ => ∅
  | imp φ ψ => bv φ ∪ bv ψ
  | all i φ => insert i (bv φ)

theorem bv_subset_vars : ∀ φ : Fm, bv φ ⊆ vars φ
  | falsum => by simp [bv, vars]
  | eq i j => by simp [bv, vars]
  | mem i j => by simp [bv, vars]
  | imp φ ψ => by
    simp only [bv, vars]
    exact Finset.union_subset_union (bv_subset_vars φ) (bv_subset_vars ψ)
  | all i φ => by
    simp only [bv, vars]
    exact Finset.insert_subset_insert _ (bv_subset_vars φ)

@[simp] theorem bv_not (φ : Fm) : bv (not φ) = bv φ := by simp [not, bv]
@[simp] theorem bv_ex (i : ℕ) (φ : Fm) : bv (ex i φ) = insert i (bv φ) := by simp [ex, not, bv]
@[simp] theorem bv_ball (i j : ℕ) (φ : Fm) : bv (ball i j φ) = insert i (bv φ) := by
  simp [ball, bv]

theorem bv_exs (l : List ℕ) (φ : Fm) : bv (exs l φ) = l.toFinset ∪ bv φ := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih, Finset.insert_union]

theorem bv_alls (l : List ℕ) (φ : Fm) : bv (alls l φ) = l.toFinset ∪ bv φ := by
  induction l with
  | nil => simp
  | cons i l ih => simp [bv, ih, Finset.insert_union]

/-! ### Substitution of a variable for a variable -/

/-- The substitution acting on a single variable index. -/
def sb (x y i : ℕ) : ℕ := if i = x then y else i

@[simp] theorem sb_self (x y : ℕ) : sb x y x = y := by simp [sb]
theorem sb_of_ne {x y i : ℕ} (h : i ≠ x) : sb x y i = i := by simp [sb, h]

/-- `φ[x := y]`: replace the free occurrences of `x` by `y`. -/
def subst (x y : ℕ) : Fm → Fm
  | falsum => falsum
  | eq i j => eq (sb x y i) (sb x y j)
  | mem i j => mem (sb x y i) (sb x y j)
  | imp φ ψ => imp (subst x y φ) (subst x y ψ)
  | all i φ => if i = x then all i φ else all i (subst x y φ)

@[simp] theorem subst_falsum (x y : ℕ) : subst x y falsum = falsum := rfl
@[simp] theorem subst_imp (x y : ℕ) (φ ψ : Fm) :
    subst x y (imp φ ψ) = imp (subst x y φ) (subst x y ψ) := rfl

theorem subst_all_of_eq (x y : ℕ) (φ : Fm) : subst x y (all x φ) = all x φ := by simp [subst]
theorem subst_all_of_ne {x y i : ℕ} (h : i ≠ x) (φ : Fm) :
    subst x y (all i φ) = all i (subst x y φ) := by simp [subst, h]

@[simp] theorem subst_not (x y : ℕ) (φ : Fm) : subst x y (not φ) = not (subst x y φ) := rfl

theorem subst_ball_of_eq (x y j : ℕ) (φ : Fm) : subst x y (ball x j φ) = ball x j φ := by
  rw [ball, subst_all_of_eq]

theorem subst_ball_of_ne {x y i : ℕ} (h : i ≠ x) (j : ℕ) (φ : Fm) :
    subst x y (ball i j φ) = ball i (sb x y j) (subst x y φ) := by
  rw [ball, subst_all_of_ne h, ball]
  simp only [subst, sb_of_ne h]

theorem subst_ex_of_eq (x y : ℕ) (φ : Fm) : subst x y (ex x φ) = ex x φ := by
  simp [ex, not, subst]
theorem subst_ex_of_ne {x y i : ℕ} (h : i ≠ x) (φ : Fm) :
    subst x y (ex i φ) = ex i (subst x y φ) := by simp [ex, not, subst, h]

theorem subst_exs_of_mem {x y : ℕ} {l : List ℕ} (hx : x ∈ l) (φ : Fm) :
    subst x y (exs l φ) = exs l φ := by
  induction l with
  | nil => cases hx
  | cons i l ih =>
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact subst_ex_of_eq _ _ _
    · by_cases h : i = x
      · subst h; exact subst_ex_of_eq _ _ _
      · rw [exs_cons, subst_ex_of_ne h, ih hx']

theorem subst_exs_of_notMem {x y : ℕ} {l : List ℕ} (hx : x ∉ l) (φ : Fm) :
    subst x y (exs l φ) = exs l (subst x y φ) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    have hi : i ≠ x := fun h => hx (by simp [h])
    rw [exs_cons, subst_ex_of_ne hi, ih (fun h => hx (by simp [h])), exs_cons]

theorem subst_alls_of_mem {x y : ℕ} {l : List ℕ} (hx : x ∈ l) (φ : Fm) :
    subst x y (alls l φ) = alls l φ := by
  induction l with
  | nil => cases hx
  | cons i l ih =>
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact subst_all_of_eq _ _ _
    · by_cases h : i = x
      · subst h; exact subst_all_of_eq _ _ _
      · rw [alls_cons, subst_all_of_ne h, ih hx']

theorem subst_alls_of_notMem {x y : ℕ} {l : List ℕ} (hx : x ∉ l) (φ : Fm) :
    subst x y (alls l φ) = alls l (subst x y φ) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    have hi : i ≠ x := fun h => hx (by simp [h])
    rw [alls_cons, subst_all_of_ne hi, ih (fun h => hx (by simp [h])), alls_cons]

/-! ### Free variables -/

theorem fv_subst_subset : ∀ φ : Fm, fv (subst x y φ) ⊆ insert y ((fv φ).erase x)
  | falsum => by simp [subst, fv]
  | eq i j => by
    intro k hk
    simp only [subst, fv, Finset.mem_insert, Finset.mem_singleton] at hk
    simp only [Finset.mem_insert, Finset.mem_erase, fv, Finset.mem_singleton]
    rcases hk with rfl | rfl <;> [skip; skip] <;>
      · unfold sb; split_ifs with h
        · exact Or.inl rfl
        · exact Or.inr ⟨h, by simp⟩
  | mem i j => by
    intro k hk
    simp only [subst, fv, Finset.mem_insert, Finset.mem_singleton] at hk
    simp only [Finset.mem_insert, Finset.mem_erase, fv, Finset.mem_singleton]
    rcases hk with rfl | rfl <;> [skip; skip] <;>
      · unfold sb; split_ifs with h
        · exact Or.inl rfl
        · exact Or.inr ⟨h, by simp⟩
  | imp φ ψ => by
    intro k hk
    simp only [subst, fv, Finset.mem_union] at hk
    rcases hk with hk | hk
    · have := fv_subst_subset φ hk
      simp only [Finset.mem_insert, Finset.mem_erase] at this ⊢
      simp only [fv, Finset.mem_union]; tauto
    · have := fv_subst_subset ψ hk
      simp only [Finset.mem_insert, Finset.mem_erase] at this ⊢
      simp only [fv, Finset.mem_union]; tauto
  | all i φ => by
    intro k hk
    by_cases h : i = x
    · subst h
      rw [subst_all_of_eq] at hk
      simp only [fv, Finset.mem_erase] at hk
      simp only [Finset.mem_insert, Finset.mem_erase, fv]
      exact Or.inr ⟨hk.1, hk.1, hk.2⟩
    · rw [subst_all_of_ne h] at hk
      simp only [fv, Finset.mem_erase] at hk
      have := fv_subst_subset φ hk.2
      simp only [Finset.mem_insert, Finset.mem_erase] at this ⊢
      simp only [fv, Finset.mem_erase]
      rcases this with rfl | ⟨h1, h2⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨h1, hk.1, h2⟩

/-! ### Correctness (Lemma 12.2 (1), over an arbitrary domain) -/

/-- Substituting in a variable slot is reading it off the updated valuation. -/
theorem sat_sb (x y : ℕ) (v : ℕ → ZFSet.{u}) (i : ℕ) :
    v (sb x y i) = Function.update v x (v y) i := by
  unfold sb; split_ifs with h
  · subst h; simp
  · rw [Function.update_of_ne h]

/-- The substitution `φ[x := y]` says of `v` what `φ` says of `v` with `x` reset to `v y`.
No hypothesis on the domain `D`: this is the paper's "the equivalence holds in every nonempty
first-order structure", here even without nonemptiness. -/
theorem sat_subst {D : ZFSet.{u} → Prop} {x y : ℕ} :
    ∀ {φ : Fm}, y ∉ bv φ → ∀ {v : ℕ → ZFSet.{u}},
      (Sat D v (subst x y φ) ↔ Sat D (Function.update v x (v y)) φ)
  | falsum, _, _ => Iff.rfl
  | eq i j, _, v => by simp only [subst, sat_eq, sat_sb]
  | mem i j, _, v => by simp only [subst, sat_mem, sat_sb]
  | imp φ ψ, h, v => by
    simp only [bv, Finset.mem_union, not_or] at h
    simp only [subst_imp, sat_imp, sat_subst h.1, sat_subst h.2]
  | all i φ, h, v => by
    simp only [bv, Finset.mem_insert, not_or] at h
    obtain ⟨hyi, hbv⟩ := h
    by_cases hix : i = x
    · subst hix
      rw [subst_all_of_eq]
      simp only [sat_all]
      apply forall_congr'; intro z; apply imp_congr_right; intro _
      rw [Function.update_idem]
    · rw [subst_all_of_ne hix]
      simp only [sat_all]
      apply forall_congr'; intro z; apply imp_congr_right; intro _
      rw [sat_subst hbv, Function.update_of_ne hyi,
        Function.update_comm (fun h => hix h.symm) _ _ v]

/-! ### Preservation of the syntactic classes -/

theorem IsDelta0.subst {x y : ℕ} : ∀ {φ : Fm}, y ∉ bv φ → IsDelta0 φ →
    IsDelta0 (Fm.subst x y φ) := by
  intro φ hy h
  induction h with
  | falsum => exact IsDelta0.falsum
  | eq i j => exact IsDelta0.eq _ _
  | mem i j => exact IsDelta0.mem _ _
  | @imp φ ψ _ _ ih₁ ih₂ =>
    simp only [bv, Finset.mem_union, not_or] at hy
    exact (ih₁ hy.1).imp (ih₂ hy.2)
  | @ball i j hij φ hφ ih =>
    simp only [bv_ball, Finset.mem_insert, not_or] at hy
    obtain ⟨hyi, hbv⟩ := hy
    by_cases hix : i = x
    · subst hix
      rw [subst_ball_of_eq]
      exact IsDelta0.ball hij hφ
    · rw [subst_ball_of_ne hix]
      refine IsDelta0.ball ?_ (ih hbv)
      unfold sb
      split_ifs with hjx
      · exact fun h => hyi h.symm
      · exact hij

mutual
theorem IsSigma.subst {x y : ℕ} : ∀ {q : ℕ} {φ : Fm}, IsSigma q φ → y ∉ bv φ →
    IsSigma q (Fm.subst x y φ)
  | _, _, .zero h, hy => .zero (IsDelta0.subst hy h)
  | _, _, .succ l hl hnd h, hy => by
    rw [bv_exs, Finset.mem_union, not_or, List.mem_toFinset] at hy
    by_cases hx : x ∈ l
    · rw [subst_exs_of_mem hx]; exact IsSigma.succ l hl hnd h
    · rw [subst_exs_of_notMem hx]
      exact IsSigma.succ l hl hnd (IsPi.subst h hy.2)
theorem IsPi.subst {x y : ℕ} : ∀ {q : ℕ} {φ : Fm}, IsPi q φ → y ∉ bv φ →
    IsPi q (Fm.subst x y φ)
  | _, _, .zero h, hy => .zero (IsDelta0.subst hy h)
  | _, _, .succ l hl hnd h, hy => by
    rw [bv_alls, Finset.mem_union, not_or, List.mem_toFinset] at hy
    by_cases hx : x ∈ l
    · rw [subst_alls_of_mem hx]; exact IsPi.succ l hl hnd h
    · rw [subst_alls_of_notMem hx]
      exact IsPi.succ l hl hnd (IsSigma.subst h hy.2)
end

end Fm
end BM4.ST
