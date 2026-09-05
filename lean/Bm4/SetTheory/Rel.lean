/-
  Part III: relativization of a formula to a set variable `m` (all quantifiers bounded by `m`),
  its semantics, and Δ₀-definability of relativized predicates.
-/
import Bm4.SetTheory.Defin

universe u

namespace BM4.ST

namespace Fm

/-- Relativize all quantifiers to the variable `m`. -/
def relTo (m : ℕ) : Fm → Fm
  | falsum => falsum
  | eq i j => eq i j
  | mem i j => mem i j
  | imp φ ψ => imp (relTo m φ) (relTo m ψ)
  | all i φ => ball i m (relTo m φ)

theorem relTo_delta0 (m : ℕ) : ∀ φ : Fm, m ∉ vars φ → IsDelta0 (relTo m φ)
  | falsum, _ => IsDelta0.falsum
  | eq i j, _ => IsDelta0.eq i j
  | mem i j, _ => IsDelta0.mem i j
  | imp φ ψ, h => by
    simp only [vars, Finset.mem_union, not_or] at h
    exact (relTo_delta0 m φ h.1).imp (relTo_delta0 m ψ h.2)
  | all i φ, h => by
    simp only [vars, Finset.mem_insert, not_or] at h
    exact IsDelta0.ball (fun hi => h.1 hi.symm) (relTo_delta0 m φ h.2)

theorem fv_relTo_subset (m : ℕ) : ∀ φ : Fm, fv (relTo m φ) ⊆ insert m (fv φ)
  | falsum => by simp [relTo, fv]
  | eq i j => by simp [relTo, fv]
  | mem i j => by simp [relTo, fv]
  | imp φ ψ => by
    simp only [relTo, fv]
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_insert.mp (fv_relTo_subset m φ hx) with rfl | hx
      · simp
      · simp [hx]
    · rcases Finset.mem_insert.mp (fv_relTo_subset m ψ hx) with rfl | hx
      · simp
      · simp [hx]
  | all i φ => by
    simp only [relTo, fv_ball, fv]
    intro x hx
    rw [Finset.mem_erase] at hx
    rcases Finset.mem_union.mp hx.2 with hx' | hx'
    · rcases Finset.mem_insert.mp hx' with rfl | hx'
      · exact absurd rfl hx.1
      · rw [Finset.mem_singleton] at hx'; subst hx'; simp
    · rcases Finset.mem_insert.mp (fv_relTo_subset m φ hx') with rfl | hx''
      · simp
      · simp [Finset.mem_erase, hx.1, hx'']

/-- Semantics of relativization: over a domain containing `v m`'s elements, `relTo m φ` holds iff
`φ` holds with quantifiers ranging over `v m`. -/
theorem sat_relTo {D : ZFSet.{u} → Prop} (m : ℕ) : ∀ (φ : Fm) (v : ℕ → ZFSet.{u}), m ∉ vars φ →
    (∀ x ∈ v m, D x) → (Sat D v (relTo m φ) ↔ Sat (· ∈ v m) v φ)
  | falsum, _, _, _ => Iff.rfl
  | eq i j, _, _, _ => Iff.rfl
  | mem i j, _, _, _ => Iff.rfl
  | imp φ ψ, v, hm, hD => by
    simp only [vars, Finset.mem_union, not_or] at hm
    simp only [relTo, sat_imp]
    rw [sat_relTo m φ v hm.1 hD, sat_relTo m ψ v hm.2 hD]
  | all i φ, v, hm, hD => by
    simp only [vars, Finset.mem_insert, not_or] at hm
    have him : i ≠ m := fun h => hm.1 h.symm
    simp only [relTo, sat_all]
    rw [sat_ball_of_ne him]
    constructor
    · intro H x hx
      have := H x (hD x hx) hx
      rw [sat_relTo m φ _ hm.2 (by rw [Function.update_of_ne him.symm]; exact hD)] at this
      rwa [Function.update_of_ne him.symm] at this
    · intro H x _ hx
      rw [sat_relTo m φ _ hm.2 (by rw [Function.update_of_ne him.symm]; exact hD)]
      rw [Function.update_of_ne him.symm]
      exact H x hx

/-- Renaming the bound variables of `φ` away from `m` (and from a finite set `avoid`), keeping
the free variables. -/
def avoidMap (φ : Fm) (K : ℕ) : ℕ → ℕ := fun i => if i ∈ fv φ then i else i + K

theorem avoidMap_injective (φ : Fm) {K : ℕ} (hK : ∀ i ∈ fv φ, i < K) :
    Function.Injective (avoidMap φ K) := by
  intro i j hij
  unfold avoidMap at hij
  split_ifs at hij with hi hj hj
  · exact hij
  · have := hK i hi; omega
  · have := hK j hj; omega
  · omega

theorem fv_rename_avoidMap (φ : Fm) {K : ℕ} (hK : ∀ i ∈ fv φ, i < K) :
    fv (rename (avoidMap φ K) φ) = fv φ := by
  rw [fv_rename _ (avoidMap_injective φ hK)]
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩; simpa [avoidMap, hi]
  · intro hx; exact ⟨x, hx, by simp [avoidMap, hx]⟩

theorem sat_rename_avoidMap (φ : Fm) {K : ℕ} (hK : ∀ i ∈ fv φ, i < K) (D : ZFSet.{u} → Prop)
    (v : ℕ → ZFSet.{u}) : Sat D v (rename (avoidMap φ K) φ) ↔ Sat D v φ := by
  rw [sat_rename (avoidMap_injective φ hK)]
  apply sat_congr
  intro x hx
  simp [avoidMap, hx]

theorem notMem_vars_rename_avoidMap (φ : Fm) {K m : ℕ} (hK : ∀ i ∈ fv φ, i < K) (hmK : m < K)
    (hm : m ∉ fv φ) : m ∉ vars (rename (avoidMap φ K) φ) := by
  rw [vars_rename]
  intro h
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
  unfold avoidMap at hi
  split_ifs at hi with hif
  · subst hi; exact hm hif
  · omega

/-- Any formula has an equivalent one (same free variables, same Σ̂/Π̂ class) not using `m` as a
bound variable, provided `m` is not free. -/
theorem exists_avoid (φ : Fm) (m : ℕ) (hm : m ∉ fv φ) :
    ∃ φ' : Fm, m ∉ vars φ' ∧ fv φ' = fv φ ∧
      (∀ (D : ZFSet.{u} → Prop) (v : ℕ → ZFSet.{u}), Sat D v φ' ↔ Sat D v φ) ∧
      (∀ q, IsSigma q φ → IsSigma q φ') ∧ (∀ q, IsPi q φ → IsPi q φ') := by
  let K := bound φ + m + 1
  have hK : ∀ i ∈ fv φ, i < K := fun i hi => by have := fv_lt_bound hi; omega
  refine ⟨rename (avoidMap φ K) φ, notMem_vars_rename_avoidMap φ hK (by omega) hm,
    fv_rename_avoidMap φ hK, sat_rename_avoidMap φ hK, fun q h => h.rename (avoidMap_injective φ hK),
    fun q h => h.rename (avoidMap_injective φ hK)⟩

end Fm

open Fm

/-- Relativized satisfaction is Δ₀-definable (in the set variable `m` and the free variables). -/
theorem delta0Def_relTo (φ : Fm) (m : ℕ) (hm : m ∉ vars φ) :
    Delta0Def (insert m (fv φ)) (fun _ v => Sat (· ∈ v m) v φ) := by
  refine ⟨relTo m φ, relTo_delta0 m φ hm, fv_relTo_subset m φ, ?_⟩
  intro D v hD hv
  have hvm : D (v m) := hv m (by simp)
  exact sat_relTo m φ v hm (fun x hx => hD.2 _ hvm x hx)

/-- Relativized satisfaction of any formula (bound variables renamed away from `m`). -/
theorem delta0Def_relTo' (φ : Fm) (m : ℕ) (hm : m ∉ fv φ) :
    Delta0Def (insert m (fv φ)) (fun _ v => Sat (· ∈ v m) v φ) := by
  obtain ⟨φ', hm', hfv, hequiv, _, _⟩ := exists_avoid φ m hm
  have := delta0Def_relTo φ' m hm'
  rw [hfv] at this
  exact this.congr (fun D v _ _ => hequiv _ v)

/-! ### Relativizing a definable predicate to a set variable -/

/-- The relativization of a Σ̂q-definable predicate to the set named by the variable `m` is
Δ₀-definable. -/
theorem SigmaDef.relativize {q : ℕ} {s : Finset ℕ} {P : Pred.{u}} (hP : SigmaDef q s P) (m : ℕ)
    (hm : m ∉ s) :
    ∃ Q : Pred.{u}, Delta0Def (insert m s) Q ∧
      ∀ (D : ZFSet.{u} → Prop) (v : ℕ → ZFSet.{u}), GoodDom (· ∈ v m) → ValD (· ∈ v m) s v →
        (Q D v ↔ P (· ∈ v m) v) := by
  obtain ⟨φ, hφ, hfv, hsat⟩ := hP
  have hmφ : m ∉ fv φ := fun h => hm (hfv h)
  refine ⟨fun _ v => Sat (· ∈ v m) v φ, (delta0Def_relTo' φ m hmφ).mono ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert] at hx ⊢
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr (hfv hx)
  · intro D v hD hv
    exact hsat _ v hD hv

/-- The relativization of a Π̂q-definable predicate. -/
theorem PiDef.relativize {q : ℕ} {s : Finset ℕ} {P : Pred.{u}} (hP : PiDef q s P) (m : ℕ)
    (hm : m ∉ s) :
    ∃ Q : Pred.{u}, Delta0Def (insert m s) Q ∧
      ∀ (D : ZFSet.{u} → Prop) (v : ℕ → ZFSet.{u}), GoodDom (· ∈ v m) → ValD (· ∈ v m) s v →
        (Q D v ↔ P (· ∈ v m) v) := by
  obtain ⟨φ, hφ, hfv, hsat⟩ := hP
  have hmφ : m ∉ fv φ := fun h => hm (hfv h)
  refine ⟨fun _ v => Sat (· ∈ v m) v φ, (delta0Def_relTo' φ m hmφ).mono ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert] at hx ⊢
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr (hfv hx)
  · intro D v hD hv
    exact hsat _ v hD hv

end BM4.ST
