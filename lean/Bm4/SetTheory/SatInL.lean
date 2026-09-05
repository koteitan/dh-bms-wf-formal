/-
  Part III: satisfaction codes exist inside an admissible `L θ` (Lemma 10.5(1), semantic form).
-/
import Bm4.SetTheory.SatCode
import Bm4.SetTheory.Recursion

universe u

namespace BM4.ST

open Fm

variable {θ : Ordinal.{u}}

/-! ### Working tools: Δ₀-separation and Σ1-replacement inside `L θ` -/

/-- Δ₀-separation inside `L θ`, in a convenient form: the separating predicate is given
by a Δ₀ matrix `Q` with the separated variable at index `0`. -/
theorem sepL (hθ : IsAdmissible θ) {s : Finset ℕ} {Q : Pred.{u}} (hQ : Delta0Def s Q)
    {v : ℕ → ZFSet.{u}} (hv : ∀ k ∈ s, k ≠ 0 → v k ∈ L θ) {a : ZFSet.{u}} (ha : a ∈ L θ)
    (P : ZFSet.{u} → Prop)
    (hP : ∀ x, Q (fun _ => True) (Function.update v 0 x) ↔ P x) :
    ZFSet.sep P a ∈ L θ := by
  have h := sep_mem_L_of_limit hθ.isSuccLimit hQ 0
    (v := v) (fun k hk => hv k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk)) ha
  have he : ZFSet.sep (fun x => Q (fun _ => True) (Function.update v 0 x)) a = ZFSet.sep P a := by
    ext x; rw [ZFSet.mem_sep, ZFSet.mem_sep, hP]
  rwa [he] at h

/-- Σ1-collection specialised: variable `0` ranges over `v 1`, variable `2` is the witness. -/
theorem collect2 (hθ : IsAdmissible θ) {s : Finset ℕ} {Q : Pred.{u}}
    (hQ : Delta0Def s Q) {v : ℕ → ZFSet.{u}}
    (hv : ∀ k ∈ s, k ≠ 2 → k ≠ 0 → v k ∈ L θ) (hX : v 1 ∈ L θ)
    (h : ∀ x ∈ v 1, ∃ y ∈ L θ, Q (· ∈ L θ) (Function.update (Function.update v 0 x) 2 y)) :
    ∃ b ∈ L θ, ∀ x ∈ v 1, ∃ y ∈ b, Q (· ∈ L θ) (Function.update (Function.update v 0 x) 2 y) :=
  sigma1_collection hθ hQ [2] 0 1 (by decide) (by simp) (by simp)
    (fun k hk hk2 hk0 => hv k hk (by simpa using hk2) hk0) hX h

/-- Σ1-replacement: the image of `v 1` under a Δ₀-definable operation `G` is bounded in `L θ`. -/
theorem image_bound (hθ : IsAdmissible θ) {s : Finset ℕ} {Q : Pred.{u}}
    (hQ : Delta0Def s Q) {v : ℕ → ZFSet.{u}}
    (hv : ∀ k ∈ s, k ≠ 2 → k ≠ 0 → v k ∈ L θ) (hX : v 1 ∈ L θ)
    (G : ZFSet.{u} → ZFSet.{u}) (hG : ∀ x ∈ v 1, G x ∈ L θ)
    (hRG : ∀ x ∈ v 1, ∀ z : ZFSet.{u},
      Q (· ∈ L θ) (Function.update (Function.update v 0 x) 2 z) ↔ z = G x) :
    ∃ b ∈ L θ, ∀ x ∈ v 1, G x ∈ b := by
  obtain ⟨b, hb, H⟩ := collect2 hθ hQ hv hX (fun x hx => ⟨G x, hG x hx, (hRG x hx _).mpr rfl⟩)
  refine ⟨b, hb, fun x hx => ?_⟩
  obtain ⟨y, hy, hQy⟩ := H x hx
  rwa [(hRG x hx y).mp hQy] at hy

/-! ### Updates of functions -/

/-- The update of `a` at `i` by `x`, as a set. -/
noncomputable def updZ (a i x : ZFSet.{u}) : ZFSet.{u} :=
  insert (ZFSet.pair i x) (ZFSet.sep (fun p => ∀ y, p ≠ ZFSet.pair i y) a)

theorem isUpdate_updZ (a i x : ZFSet.{u}) : IsUpdate a i x (updZ a i x) := by
  intro p
  unfold updZ
  rw [ZFSet.mem_insert_iff, ZFSet.mem_sep]
  tauto

theorem isUpdate_eq {a i x b : ZFSet.{u}} (h : IsUpdate a i x b) : b = updZ a i x := by
  ext p; rw [h p, isUpdate_updZ a i x p]

/-- `∀ y, p ≠ pair i y` is Δ₀. -/
theorem delta0_notPairAt (p i : ℕ) (hpi : p ≠ i) :
    Delta0Def {p, i} (fun _ v => ∀ z, v p ≠ ZFSet.pair (v i) z) := by
  set m := p + i + 1 with hm
  have h1 := (delta0_isKPair p i (m + 1) (by omega) (by omega)).not
  have h2 := h1.ball (m + 1) m (by omega)
  have h := h2.ball m p (by omega)
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    rw [forall_ne_pair_iff_bounded]
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]; omega

theorem sep_notPairAt_mem_L (hθ : IsAdmissible θ) {a i : ZFSet.{u}} (ha : a ∈ L θ)
    (hi : i ∈ L θ) : ZFSet.sep (fun p => ∀ y, p ≠ ZFSet.pair i y) a ∈ L θ := by
  refine sepL hθ (delta0_notPairAt 0 1 (by omega))
    (v := fun k => if k = 1 then i else ∅) ?_ ha _ ?_
  · intro k hk hk0
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact absurd rfl hk0
    · simpa using hi
  · intro x
    simp

theorem updZ_mem_L (hθ : IsAdmissible θ) {a i x : ZFSet.{u}} (ha : a ∈ L θ) (hi : i ∈ L θ)
    (hx : x ∈ L θ) : updZ a i x ∈ L θ :=
  insert_mem_L_of_limit hθ.isSuccLimit
    (kpair_mem_L_of_limit hθ.isSuccLimit hi hx) (sep_notPairAt_mem_L hθ ha hi)

/-! ### One-step updates and the sets `A^n` -/

/-- The set of updates of `f` at `i` by elements of `A`. -/
noncomputable def updIm (A i f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun g => ∃ x ∈ A, IsUpdate f i x g)
    (ZFSet.powerset (f ∪ ZFSet.pairSep (fun _ _ => True) ({i} : ZFSet.{u}) A))

theorem mem_updIm {A i f g : ZFSet.{u}} : g ∈ updIm A i f ↔ ∃ x ∈ A, IsUpdate f i x g := by
  unfold updIm
  rw [ZFSet.mem_sep, ZFSet.mem_powerset]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨x, hx, hu⟩ := h
  intro p hp
  rw [ZFSet.mem_union]
  rcases (hu p).mp hp with ⟨hpf, _⟩ | rfl
  · exact Or.inl hpf
  · refine Or.inr ?_
    rw [ZFSet.mem_pairSep]
    exact ⟨i, ZFSet.mem_singleton.mpr rfl, x, hx, rfl, trivial⟩

theorem updIm_mem_L (hθ : IsAdmissible θ) {A i f : ZFSet.{u}} (hA : A ∈ L θ) (hi : i ∈ L θ)
    (hf : f ∈ L θ) : updIm A i f ∈ L θ := by
  obtain ⟨b, hb, hbmem⟩ :=
    image_bound hθ (delta0_isUpdate 3 4 0 2 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega))
      (v := fun k => if k = 1 then A else if k = 3 then f else if k = 4 then i else ∅)
      (by
        intro k hk hk2 hk0
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl | rfl
        · simpa using hf
        · simpa using hi
        · exact absurd rfl hk0
        · exact absurd rfl hk2)
      (by simpa using hA) (fun x => updZ f i x)
      (by
        intro x hx
        exact updZ_mem_L hθ hf hi ((L_transitive θ).subset_of_mem hA (by simpa using hx)))
      (by
        intro x _ z
        simp only [Function.update_apply]
        norm_num
        exact ⟨fun h => isUpdate_eq h, fun h => h ▸ isUpdate_updZ f i x⟩)
  have heq : updIm A i f = ZFSet.sep (fun g => ∃ x ∈ A, IsUpdate f i x g) b := by
    ext g
    rw [mem_updIm, ZFSet.mem_sep]
    refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
    obtain ⟨x, hx, hu⟩ := h
    rw [isUpdate_eq hu]
    exact hbmem x (by simpa using hx)
  rw [heq]
  refine sepL hθ
    ((delta0_isUpdate 3 4 5 0 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)).bex 5 1 (by omega))
    (v := fun k => if k = 1 then A else if k = 3 then f else if k = 4 then i else ∅)
    (by
      intro k hk hk0
      simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton] at hk
      rcases hk with rfl | ⟨_, rfl | rfl | rfl | rfl⟩
      · simpa using hA
      · simpa using hf
      · simpa using hi
      · omega
      · exact absurd rfl hk0)
    hb _
    (by intro g; simp only [Function.update_apply]; norm_num)

/-- The set of sequences over `A` with domain `natZ n`. -/
noncomputable def PowSeq (A : ZFSet.{u}) (n : ℕ) : ZFSet.{u} :=
  ZFSet.sep (fun a => IsDom a (natZ n)) (Seqs A)

theorem mem_PowSeq {A a : ZFSet.{u}} {n : ℕ} :
    a ∈ PowSeq A n ↔ IsSeqA ωZ A a ∧ IsDom a (natZ n) := by
  unfold PowSeq
  rw [ZFSet.mem_sep, mem_Seqs]

theorem powSeq_zero (A : ZFSet.{u}) : PowSeq A 0 = ({∅} : ZFSet.{u}) := by
  have hdom : IsDom (∅ : ZFSet.{u}) (natZ 0) := by
    intro j
    constructor
    · intro hj; exact absurd hj (ZFSet.notMem_empty j)
    · rintro ⟨b, hb⟩; exact absurd hb (ZFSet.notMem_empty _)
  ext a
  rw [mem_PowSeq, ZFSet.mem_singleton]
  constructor
  · rintro ⟨hs, hd⟩
    ext p
    simp only [ZFSet.notMem_empty, iff_false]
    intro hp
    obtain ⟨i, x, rfl⟩ := hs.1.1 p hp
    exact absurd ((hd i).mpr ⟨x, hp⟩) (ZFSet.notMem_empty i)
  · rintro rfl
    exact ⟨⟨⟨fun p hp => absurd hp (ZFSet.notMem_empty p),
      fun _ _ _ hb _ => absurd hb (ZFSet.notMem_empty _)⟩,
      ⟨natZ 0, natZ_mem_ωZ 0, hdom⟩, fun _ _ hx => absurd hx (ZFSet.notMem_empty _)⟩, hdom⟩

/-- Every sequence of length `n+1` is a one-step update of a sequence of length `n`. -/
theorem powSeq_succ_decomp {A a : ZFSet.{u}} {n : ℕ} (h : a ∈ PowSeq A (n + 1)) :
    ∃ f ∈ PowSeq A n, ∃ x ∈ A, IsUpdate f (natZ n) x a := by
  rw [mem_PowSeq] at h
  obtain ⟨hs, hd⟩ := h
  obtain ⟨x, hx⟩ : ∃ x, ZFSet.pair (natZ.{u} n) x ∈ a :=
    (hd (natZ n)).mp (natZ_mem_natZ_iff.mpr (by omega))
  set f := ZFSet.sep (fun p => ∀ y, p ≠ ZFSet.pair (natZ.{u} n) y) a with hfdef
  have hmemf : ∀ p, p ∈ f ↔ (p ∈ a ∧ ∀ y, p ≠ ZFSet.pair (natZ.{u} n) y) := fun p => ZFSet.mem_sep
  have hfa : ∀ p, p ∈ f → p ∈ a := fun p hp => ((hmemf p).mp hp).1
  have hdomf : IsDom f (natZ.{u} n) := by
    intro j
    constructor
    · intro hj
      obtain ⟨m, hm, rfl⟩ := mem_natZ_iff.mp hj
      obtain ⟨y, hy⟩ := (hd (natZ m)).mp (natZ_mem_natZ_iff.mpr (by omega))
      refine ⟨y, (hmemf _).mpr ⟨hy, fun z hz => ?_⟩⟩
      rw [ZFSet.pair_inj] at hz
      exact absurd (natZ_injective hz.1) (by omega)
    · rintro ⟨y, hy⟩
      have h1 := hfa _ hy
      have h2 := ((hmemf _).mp hy).2
      have hj1 : j ∈ natZ.{u} (n + 1) := (hd j).mpr ⟨y, h1⟩
      obtain ⟨m, hm, rfl⟩ := mem_natZ_iff.mp hj1
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hmn | rfl
      · exact mem_natZ_iff.mpr ⟨m, hmn, rfl⟩
      · exact absurd rfl (h2 y)
  refine ⟨f, mem_PowSeq.mpr ⟨⟨⟨fun p hp => hs.1.1 p (hfa _ hp),
      fun i b b' hb hb' => hs.1.2 i b b' (hfa _ hb) (hfa _ hb')⟩,
      ⟨natZ n, natZ_mem_ωZ n, hdomf⟩, fun i y hy => hs.2.2 i y (hfa _ hy)⟩, hdomf⟩,
    x, hs.2.2 _ _ hx, ?_⟩
  intro p
  constructor
  · intro hp
    by_cases hcase : ∃ y, p = ZFSet.pair (natZ.{u} n) y
    · obtain ⟨y, rfl⟩ := hcase
      exact Or.inr (by rw [hs.1.2 _ _ _ hp hx])
    · refine Or.inl ⟨(hmemf p).mpr ⟨hp, fun y hy => hcase ⟨y, hy⟩⟩, fun y hy => hcase ⟨y, hy⟩⟩
  · rintro (⟨hpf, _⟩ | rfl)
    · exact hfa _ hpf
    · exact hx

theorem powSeq_succ_mem_L (hθ : IsAdmissible θ) {A : ZFSet.{u}} (hA : A ∈ L θ) (n : ℕ)
    (hn : PowSeq A n ∈ L θ) : PowSeq A (n + 1) ∈ L θ := by
  have hlim := hθ.isSuccLimit
  have hT := L_transitive θ
  have hnat : ∀ m : ℕ, natZ.{u} m ∈ L θ := fun m => natZ_mem_L hθ.omega_lt m
  have hω : ωZ.{u} ∈ L θ := hθ.omega_mem
  have hupd : Delta0Def {0, 4, 6, 5} (fun _ v => IsUpdate (v 0) (v 4) (v 6) (v 5)) :=
    delta0_isUpdate 0 4 6 5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hQ : Delta0Def ({0, 2, 3, 4} : Finset ℕ) (fun _ v =>
      (∀ g ∈ v 2, ∃ x ∈ v 3, IsUpdate (v 0) (v 4) x g) ∧
      (∀ x ∈ v 3, ∃ g ∈ v 2, IsUpdate (v 0) (v 4) x g)) :=
    (((hupd.bex 6 3 (by omega)).ball 5 2 (by omega)).and
      ((hupd.bex 5 2 (by omega)).ball 6 3 (by omega))).mono (by decide)
  obtain ⟨b, hb, hbmem⟩ := image_bound hθ hQ
    (v := fun k => if k = 1 then PowSeq A n else if k = 3 then A else if k = 4 then natZ n else ∅)
    (by
      intro k hk hk2 hk0
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · exact absurd rfl hk0
      · exact absurd rfl hk2
      · simpa using hA
      · simpa using hnat n)
    (by simpa using hn) (fun f => updIm A (natZ n) f)
    (by
      intro f hf
      simp only at hf
      exact updIm_mem_L hθ hA (hnat n) (hT.subset_of_mem hn (by simpa using hf)))
    (by
      intro f hf z
      simp only [Function.update_apply]
      norm_num
      constructor
      · rintro ⟨H1, H2⟩
        ext g
        rw [mem_updIm]
        refine ⟨fun hg => H1 g hg, ?_⟩
        rintro ⟨x, hx, hu⟩
        obtain ⟨g', hg', hu'⟩ := H2 x hx
        rw [isUpdate_eq hu, ← isUpdate_eq hu']
        exact hg'
      · rintro rfl
        exact ⟨fun g hg => mem_updIm.mp hg,
          fun x hx => ⟨updZ f (natZ n) x, mem_updIm.mpr ⟨x, hx, isUpdate_updZ _ _ _⟩,
            isUpdate_updZ _ _ _⟩⟩)
  have hsub : PowSeq A (n + 1) = ZFSet.sep (fun a => IsSeqA ωZ A a ∧ IsDom a (natZ (n + 1)))
      (ZFSet.sUnion b) := by
    ext a
    rw [ZFSet.mem_sep, mem_PowSeq]
    refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
    obtain ⟨f, hf, x, hx, hu⟩ := powSeq_succ_decomp (mem_PowSeq.mpr h)
    exact ZFSet.mem_sUnion.mpr ⟨updIm A (natZ n) f, hbmem f (by simpa using hf),
      mem_updIm.mpr ⟨x, hx, hu⟩⟩
  rw [hsub]
  refine sepL hθ
    (((delta0_isSeqA 3 1 0 (by omega) (by omega) (by omega)).and
      (delta0_isDom 0 4 (by omega))).mono (show _ ⊆ ({0, 1, 3, 4} : Finset ℕ) by decide))
    (v := fun k => if k = 1 then A else if k = 3 then ωZ else if k = 4 then natZ (n + 1) else ∅)
    (by
      intro k hk hk0
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · exact absurd rfl hk0
      · simpa using hA
      · simpa using hω
      · simpa using hnat (n + 1))
    (sUnion_mem_L_of_limit hlim hb) _
    (by intro a; simp only [Function.update_apply]; norm_num)

theorem powSeq_mem_L (hθ : IsAdmissible θ) {A : ZFSet.{u}} (hA : A ∈ L θ) :
    ∀ n : ℕ, PowSeq A n ∈ L θ
  | 0 => by
    rw [powSeq_zero]
    exact singleton_mem_L_of_limit hθ.isSuccLimit (empty_mem_L_of_limit hθ.isSuccLimit)
  | n + 1 => powSeq_succ_mem_L hθ hA n (powSeq_mem_L hθ hA n)

/-! ### The set of all finite sequences over `A` lies in `L θ` -/

theorem isDom_unique {a d d' : ZFSet.{u}} (h : IsDom a d) (h' : IsDom a d') : d = d' := by
  ext j; rw [h j, h' j]

/-- Extending a sequence of length `m` by one value gives a sequence of length `m+1`. -/
theorem updZ_mem_powSeq_succ {A a x : ZFSet.{u}} {m : ℕ} (ha : a ∈ PowSeq A m) (hx : x ∈ A) :
    updZ a (natZ m) x ∈ PowSeq A (m + 1) := by
  obtain ⟨hs, hd⟩ := mem_PowSeq.mp ha
  set b := updZ a (natZ.{u} m) x with hbdef
  have hb : ∀ p, p ∈ b ↔ (p ∈ a ∧ ∀ y, p ≠ ZFSet.pair (natZ.{u} m) y) ∨
      p = ZFSet.pair (natZ.{u} m) x := isUpdate_updZ a (natZ m) x
  have hval : ∀ i y, ZFSet.pair i y ∈ b → y ∈ A := by
    intro i y hy
    rcases (hb _).mp hy with ⟨hya, _⟩ | he
    · exact hs.2.2 _ _ hya
    · rw [ZFSet.pair_inj] at he; rw [he.2]; exact hx
  have hdomb : IsDom b (natZ.{u} (m + 1)) := by
    intro j
    constructor
    · intro hj
      obtain ⟨l, hl, rfl⟩ := mem_natZ_iff.mp hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hlm | rfl
      · obtain ⟨y, hy⟩ := (hd (natZ l)).mp (natZ_mem_natZ_iff.mpr hlm)
        exact ⟨y, (hb _).mpr (Or.inl ⟨hy, fun z hz => by
          rw [ZFSet.pair_inj] at hz
          exact absurd (natZ_injective hz.1) (by omega)⟩)⟩
      · exact ⟨x, (hb _).mpr (Or.inr rfl)⟩
    · rintro ⟨y, hy⟩
      rcases (hb _).mp hy with ⟨hya, _⟩ | he
      · have := (hd j).mpr ⟨y, hya⟩
        obtain ⟨l, hl, rfl⟩ := mem_natZ_iff.mp this
        exact mem_natZ_iff.mpr ⟨l, by omega, rfl⟩
      · rw [ZFSet.pair_inj] at he
        rw [he.1]
        exact natZ_mem_natZ_iff.mpr (by omega)
  refine mem_PowSeq.mpr ⟨⟨⟨fun p hp => ?_, ?_⟩, ⟨natZ (m + 1), natZ_mem_ωZ _, hdomb⟩, hval⟩, hdomb⟩
  · rcases (hb _).mp hp with ⟨hpa, _⟩ | rfl
    · exact hs.1.1 p hpa
    · exact ⟨_, _, rfl⟩
  · intro i y y' hy hy'
    rcases (hb _).mp hy with ⟨hya, hne⟩ | he
    · rcases (hb _).mp hy' with ⟨hya', _⟩ | he'
      · exact hs.1.2 _ _ _ hya hya'
      · rw [ZFSet.pair_inj] at he'
        exact absurd (show ZFSet.pair i y = ZFSet.pair (natZ.{u} m) y by rw [he'.1]) (hne y)
    · rcases (hb _).mp hy' with ⟨_, hne'⟩ | he'
      · rw [ZFSet.pair_inj] at he
        exact absurd (show ZFSet.pair i y' = ZFSet.pair (natZ.{u} m) y' by rw [he.1]) (hne' y')
      · rw [ZFSet.pair_inj] at he he'
        rw [he.2, he'.2]

/-- Sequences over `A` of length at most `nn`. -/
noncomputable def SeqsLe (A nn : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun a => ∃ d, IsDom a d ∧ (d = nn ∨ d ∈ nn)) (Seqs A)

theorem mem_SeqsLe {A nn a : ZFSet.{u}} :
    a ∈ SeqsLe A nn ↔ IsSeqA ωZ A a ∧ ∃ d, IsDom a d ∧ (d = nn ∨ d ∈ nn) := by
  unfold SeqsLe; rw [ZFSet.mem_sep, mem_Seqs]

theorem mem_seqsLe_natZ {A a : ZFSet.{u}} {k : ℕ} :
    a ∈ SeqsLe A (natZ k) ↔ ∃ m ≤ k, a ∈ PowSeq A m := by
  rw [mem_SeqsLe]
  constructor
  · rintro ⟨hs, d, hd, hcase⟩
    obtain ⟨d₀, hd₀, hdom₀⟩ := hs.2.1
    obtain ⟨m, rfl⟩ := mem_ωZ_iff.mp hd₀
    rw [isDom_unique hd hdom₀] at hcase
    rcases hcase with he | he
    · exact ⟨m, le_of_eq (natZ_injective he), mem_PowSeq.mpr ⟨hs, hdom₀⟩⟩
    · exact ⟨m, le_of_lt (natZ_mem_natZ_iff.mp he), mem_PowSeq.mpr ⟨hs, hdom₀⟩⟩
  · rintro ⟨m, hm, ha⟩
    obtain ⟨hs, hd⟩ := mem_PowSeq.mp ha
    refine ⟨hs, natZ m, hd, ?_⟩
    rcases Nat.eq_or_lt_of_le hm with rfl | hlt
    · exact Or.inl rfl
    · exact Or.inr (natZ_mem_natZ_iff.mpr hlt)

theorem seqsLe_mem_L (hθ : IsAdmissible θ) {A : ZFSet.{u}} (hA : A ∈ L θ) :
    ∀ k : ℕ, SeqsLe A (natZ k) ∈ L θ
  | 0 => by
    have he : SeqsLe A (natZ.{u} 0) = PowSeq A 0 := by
      ext a; rw [mem_seqsLe_natZ]
      exact ⟨fun ⟨m, hm, ha⟩ => by rwa [Nat.le_zero.mp hm] at ha, fun ha => ⟨0, le_rfl, ha⟩⟩
    rw [he]; exact powSeq_mem_L hθ hA 0
  | k + 1 => by
    have he : SeqsLe A (natZ.{u} (k + 1)) = SeqsLe A (natZ k) ∪ PowSeq A (k + 1) := by
      ext a
      rw [mem_seqsLe_natZ, ZFSet.mem_union, mem_seqsLe_natZ]
      constructor
      · rintro ⟨m, hm, ha⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hm) with hlt | rfl
        · exact Or.inl ⟨m, by omega, ha⟩
        · exact Or.inr ha
      · rintro (⟨m, hm, ha⟩ | ha)
        · exact ⟨m, by omega, ha⟩
        · exact ⟨k + 1, le_rfl, ha⟩
    rw [he]
    exact union_mem_L_of_limit hθ.isSuccLimit (seqsLe_mem_L hθ hA k) (powSeq_mem_L hθ hA (k + 1))

/-- Completeness of a set closed under one-step extensions. -/
theorem cum_complete {A z : ZFSet.{u}} {k : ℕ} (h2 : (∅ : ZFSet.{u}) ∈ z)
    (h3 : ∀ a ∈ z, ∀ d ∈ ωZ.{u}, IsDom a d → d ∈ natZ k → ∀ x ∈ A, ∃ b ∈ z, IsUpdate a d x b) :
    ∀ m ≤ k, ∀ a ∈ PowSeq A m, a ∈ z := by
  intro m
  induction m with
  | zero =>
    intro _ a ha
    rw [powSeq_zero, ZFSet.mem_singleton] at ha
    exact ha ▸ h2
  | succ m ih =>
    intro hmk a ha
    obtain ⟨f, hf, x, hx, hu⟩ := powSeq_succ_decomp ha
    obtain ⟨b, hbz, hub⟩ := h3 f (ih (by omega) f hf) (natZ m) (natZ_mem_ωZ m)
      (mem_PowSeq.mp hf).2 (natZ_mem_natZ_iff.mpr (by omega)) x hx
    rw [isUpdate_eq hu, ← isUpdate_eq hub]
    exact hbz

theorem seqs_mem_L (hθ : IsAdmissible θ) {A : ZFSet.{u}} (hA : A ∈ L θ) : Seqs A ∈ L θ := by
  have hlim := hθ.isSuccLimit
  have hω : ωZ.{u} ∈ L θ := hθ.omega_mem
  have hQ : Delta0Def ({0, 1, 2, 3, 5} : Finset ℕ) (fun _ v =>
      (∀ a ∈ v 2, IsSeqA (v 1) (v 3) a ∧ ∃ d ∈ v 1, IsDom a d ∧ (d = v 0 ∨ d ∈ v 0)) ∧
      (v 5 ∈ v 2) ∧
      (∀ a ∈ v 2, ∀ d ∈ v 1, (IsDom a d ∧ d ∈ v 0) →
        ∀ x ∈ v 3, ∃ b ∈ v 2, IsUpdate a d x b)) := by
    have c1 := ((delta0_isSeqA 1 3 6 (by omega) (by omega) (by omega)).and
      (((delta0_isDom 6 7 (by omega)).and ((Delta0Def.eq 7 0).or (Delta0Def.mem 7 0))).bex 7 1
        (by omega))).ball 6 2 (by omega)
    have c2 := Delta0Def.mem 5 2
    have c3 := ((((delta0_isDom 6 7 (by omega)).and (Delta0Def.mem 7 0)).imp
      (((delta0_isUpdate 6 7 8 9 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)).bex 9 2 (by omega)).ball 8 3 (by omega))).ball 7 1 (by omega)).ball 6 2
        (by omega)
    exact ((c1.and (c2.and c3)).congr
      (by
        intro D v _ _
        simp (disch := omega) only [Function.update_self, Function.update_of_ne])).mono (by decide)
  obtain ⟨b, hb, hbmem⟩ := image_bound hθ hQ
    (v := Function.update (Function.update (fun _ => (∅ : ZFSet.{u})) 1 ωZ) 3 A)
    (by
      intro k hk hk2 hk0
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl hk0
      · simpa (disch := omega) only [Function.update_self, Function.update_of_ne] using hω
      · exact absurd rfl hk2
      · simpa (disch := omega) only [Function.update_self, Function.update_of_ne] using hA
      · simpa (disch := omega) only [Function.update_self, Function.update_of_ne] using
          empty_mem_L_of_limit hlim)
    (by simpa (disch := omega) only [Function.update_self, Function.update_of_ne] using hω)
    (fun nn => SeqsLe A nn)
    (by
      intro nn hnn
      simp (disch := omega) only [Function.update_self, Function.update_of_ne] at hnn
      obtain ⟨k, rfl⟩ := mem_ωZ_iff.mp hnn
      exact seqsLe_mem_L hθ hA k)
    (by
      intro nn hnn z
      simp (disch := omega) only [Function.update_self, Function.update_of_ne] at hnn
      obtain ⟨k, rfl⟩ := mem_ωZ_iff.mp hnn
      simp (disch := omega) only [Function.update_self, Function.update_of_ne]
      constructor
      · rintro ⟨H1, H2, H3⟩
        ext a
        rw [mem_seqsLe_natZ]
        constructor
        · intro ha
          obtain ⟨hs, d, _, hd, hcase⟩ := H1 a ha
          exact (mem_seqsLe_natZ (k := k)).mp (mem_SeqsLe.mpr ⟨hs, d, hd, hcase⟩)
        · rintro ⟨m, hm, ha⟩
          exact cum_complete H2 (fun a' ha' d hd hdom hdk x hx => H3 a' ha' d hd ⟨hdom, hdk⟩ x hx)
            m hm a ha
      · rintro rfl
        refine ⟨?_, ?_, ?_⟩
        · intro a ha
          obtain ⟨m, hm, ha'⟩ := mem_seqsLe_natZ.mp ha
          obtain ⟨hs, hd⟩ := mem_PowSeq.mp ha'
          refine ⟨hs, natZ m, natZ_mem_ωZ m, hd, ?_⟩
          rcases Nat.eq_or_lt_of_le hm with rfl | hlt
          · exact Or.inl rfl
          · exact Or.inr (natZ_mem_natZ_iff.mpr hlt)
        · exact mem_seqsLe_natZ.mpr ⟨0, Nat.zero_le k,
            by rw [powSeq_zero]; exact ZFSet.mem_singleton.mpr rfl⟩
        · rintro a ha d hd ⟨hdom, hdk⟩ x hx
          obtain ⟨m, hm, ha'⟩ := mem_seqsLe_natZ.mp ha
          have hdm : d = natZ m := isDom_unique hdom (mem_PowSeq.mp ha').2
          subst hdm
          refine ⟨updZ a (natZ m) x, mem_seqsLe_natZ.mpr ⟨m + 1, ?_,
            updZ_mem_powSeq_succ ha' hx⟩, isUpdate_updZ _ _ _⟩
          exact Nat.succ_le_of_lt (natZ_mem_natZ_iff.mp hdk))
  simp (disch := omega) only [Function.update_self, Function.update_of_ne] at hbmem
  have he : Seqs A = ZFSet.sep (IsSeqA ωZ A) (ZFSet.sUnion b) := by
    ext a
    rw [mem_Seqs, ZFSet.mem_sep]
    refine ⟨fun ha => ⟨?_, ha⟩, fun h => h.2⟩
    obtain ⟨d, hd, hdom⟩ := ha.2.1
    obtain ⟨m, rfl⟩ := mem_ωZ_iff.mp hd
    exact ZFSet.mem_sUnion.mpr ⟨SeqsLe A (natZ m), hbmem _ (natZ_mem_ωZ m),
      mem_SeqsLe.mpr ⟨ha, natZ m, hdom, Or.inl rfl⟩⟩
  rw [he]
  refine sepL hθ (delta0_isSeqA 3 1 0 (by omega) (by omega) (by omega))
    (v := Function.update (Function.update (fun _ => (∅ : ZFSet.{u})) 1 A) 3 ωZ)
    (by
      intro k hk hk0
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl
      · simpa (disch := omega) only [Function.update_self, Function.update_of_ne] using hω
      · simpa (disch := omega) only [Function.update_self, Function.update_of_ne] using hA
      · exact absurd rfl hk0)
    (sUnion_mem_L_of_limit hlim hb) _
    (by intro a; simp (disch := omega) only [Function.update_self, Function.update_of_ne])

/-! ### Cartesian products inside `L θ` -/

/-- The set of Kuratowski pairs from `X` and `Y`. -/
noncomputable def kprodZ (X Y : ZFSet.{u}) : ZFSet.{u} := ZFSet.pairSep (fun _ _ => True) X Y

theorem mem_kprodZ {X Y z : ZFSet.{u}} :
    z ∈ kprodZ X Y ↔ ∃ x ∈ X, ∃ y ∈ Y, z = ZFSet.pair x y := by
  unfold kprodZ
  rw [ZFSet.mem_pairSep]
  exact ⟨fun ⟨x, hx, y, hy, he, _⟩ => ⟨x, hx, y, hy, he⟩,
    fun ⟨x, hx, y, hy, he⟩ => ⟨x, hx, y, hy, he, trivial⟩⟩

private theorem hv3 {θ : Ordinal.{u}} {Y x : ZFSet.{u}} (hY : Y ∈ L θ) (hx : x ∈ L θ) :
    ∀ k ∈ ({0, 1, 3} : Finset ℕ), k ≠ 0 →
      Function.update (Function.update (fun _ => (∅ : ZFSet.{u})) 1 Y) 3 x k ∈ L θ := by
  intro k hk hk0
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl
  · exact absurd rfl hk0
  · simpa (disch := omega) only [Function.update_self, Function.update_of_ne] using hY
  · simpa (disch := omega) only [Function.update_self, Function.update_of_ne] using hx

theorem kprod_singleton_mem_L (hθ : IsAdmissible θ) {x Y : ZFSet.{u}} (hx : x ∈ L θ)
    (hY : Y ∈ L θ) : kprodZ ({x} : ZFSet.{u}) Y ∈ L θ := by
  have hemp : (∅ : ZFSet.{u}) ∈ L θ := empty_mem_L_of_limit hθ.isSuccLimit
  obtain ⟨b, hb, hbmem⟩ := image_bound hθ
    ((delta0_isKPair 2 3 0 (by omega) (by omega)).mono
      (show _ ⊆ ({0, 2, 3} : Finset ℕ) by decide))
    (v := Function.update (Function.update (fun _ => (∅ : ZFSet.{u})) 1 Y) 3 x)
    (by
      intro k hk hk2 hk0
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl
      · exact absurd rfl hk0
      · exact absurd rfl hk2
      · simpa (disch := omega) only [Function.update_self, Function.update_of_ne] using hx)
    (by simpa (disch := omega) only [Function.update_self, Function.update_of_ne] using hY)
    (fun y => ZFSet.pair x y)
    (by
      intro y hy
      simp (disch := omega) only [Function.update_self, Function.update_of_ne] at hy
      exact kpair_mem_L_of_limit hθ.isSuccLimit hx ((L_transitive θ).subset_of_mem hY hy))
    (by
      intro y _ z
      simp (disch := omega) only [Function.update_self, Function.update_of_ne])
  simp (disch := omega) only [Function.update_self, Function.update_of_ne] at hbmem
  have he : kprodZ ({x} : ZFSet.{u}) Y = ZFSet.sep (fun z => ∃ y ∈ Y, z = ZFSet.pair x y) b := by
    ext z
    rw [mem_kprodZ, ZFSet.mem_sep]
    constructor
    · rintro ⟨x', hx', y, hy, rfl⟩
      rw [ZFSet.mem_singleton] at hx'
      subst hx'
      exact ⟨hbmem y hy, y, hy, rfl⟩
    · rintro ⟨_, y, hy, rfl⟩
      exact ⟨x, ZFSet.mem_singleton.mpr rfl, y, hy, rfl⟩
  rw [he]
  exact sepL hθ
    (((delta0_isKPair 0 3 4 (by omega) (by omega)).bex 4 1 (by omega)).mono
      (show _ ⊆ ({0, 1, 3} : Finset ℕ) by decide))
    (hv3 hY hx) hb _
    (by intro z; simp (disch := omega) only [Function.update_self, Function.update_of_ne])

theorem kprod_mem_L (hθ : IsAdmissible θ) {X Y : ZFSet.{u}} (hX : X ∈ L θ) (hY : Y ∈ L θ) :
    kprodZ X Y ∈ L θ := by
  have hemp : (∅ : ZFSet.{u}) ∈ L θ := empty_mem_L_of_limit hθ.isSuccLimit
  have hT := L_transitive θ
  have hQ : Delta0Def ({0, 2, 3} : Finset ℕ) (fun _ v =>
      (∀ z ∈ v 2, ∃ y ∈ v 3, z = ZFSet.pair (v 0) y) ∧
      (∀ y ∈ v 3, ∃ z ∈ v 2, z = ZFSet.pair (v 0) y)) :=
    (((delta0_isKPair 4 0 5 (by omega) (by omega)).bex 5 3 (by omega)).ball 4 2 (by omega)).and
      (((delta0_isKPair 4 0 5 (by omega) (by omega)).bex 4 2 (by omega)).ball 5 3
        (by omega)) |>.congr
      (by
        intro D v _ _
        simp (disch := omega) only [Function.update_self, Function.update_of_ne])
      |>.mono (by decide)
  obtain ⟨b, hb, hbmem⟩ := image_bound hθ hQ
    (v := Function.update (Function.update (fun _ => (∅ : ZFSet.{u})) 1 X) 3 Y)
    (by
      intro k hk hk2 hk0
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl
      · exact absurd rfl hk0
      · exact absurd rfl hk2
      · simpa (disch := omega) only [Function.update_self, Function.update_of_ne] using hY)
    (by simpa (disch := omega) only [Function.update_self, Function.update_of_ne] using hX)
    (fun x => kprodZ ({x} : ZFSet.{u}) Y)
    (by
      intro x hx
      simp (disch := omega) only [Function.update_self, Function.update_of_ne] at hx
      exact kprod_singleton_mem_L hθ (hT.subset_of_mem hX hx) hY)
    (by
      intro x _ z
      simp (disch := omega) only [Function.update_self, Function.update_of_ne]
      constructor
      · rintro ⟨H1, H2⟩
        ext w
        rw [mem_kprodZ]
        constructor
        · intro hw
          obtain ⟨y, hy, he⟩ := H1 w hw
          exact ⟨x, ZFSet.mem_singleton.mpr rfl, y, hy, he⟩
        · rintro ⟨x', hx', y, hy, rfl⟩
          rw [ZFSet.mem_singleton] at hx'
          subst hx'
          obtain ⟨w, hw, he⟩ := H2 y hy
          rwa [← he]
      · rintro rfl
        constructor
        · intro w hw
          obtain ⟨x', hx', y, hy, he⟩ := mem_kprodZ.mp hw
          rw [ZFSet.mem_singleton] at hx'
          exact ⟨y, hy, by rw [he, hx']⟩
        · intro y hy
          exact ⟨ZFSet.pair x y,
            mem_kprodZ.mpr ⟨x, ZFSet.mem_singleton.mpr rfl, y, hy, rfl⟩, rfl⟩)
  simp (disch := omega) only [Function.update_self, Function.update_of_ne] at hbmem
  have he : kprodZ X Y = ZFSet.sep (fun z => ∃ x ∈ X, ∃ y ∈ Y, z = ZFSet.pair x y)
      (ZFSet.sUnion b) := by
    ext z
    rw [mem_kprodZ, ZFSet.mem_sep]
    refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    exact ZFSet.mem_sUnion.mpr ⟨kprodZ ({x} : ZFSet.{u}) Y, hbmem x hx,
      mem_kprodZ.mpr ⟨x, ZFSet.mem_singleton.mpr rfl, y, hy, rfl⟩⟩
  rw [he]
  exact sepL hθ
    ((((delta0_isKPair 0 4 5 (by omega) (by omega)).bex 5 3 (by omega)).bex 4 1
      (by omega)).mono (show _ ⊆ ({0, 1, 3} : Finset ℕ) by decide))
    (hv3 hX hY) (sUnion_mem_L_of_limit hθ.isSuccLimit hb) _
    (by intro z; simp (disch := omega) only [Function.update_self, Function.update_of_ne])

/-! ### Assignments covering the free variables of a formula -/

/-- A bound on the free variables of `φ`: every free variable of `φ` is `< fvSup φ`. -/
def fvSup (φ : Fm) : ℕ := (Fm.fv φ).sup (fun k => k + 1)

theorem lt_fvSup {φ : Fm} {k : ℕ} (hk : k ∈ Fm.fv φ) : k < fvSup φ :=
  Finset.le_sup (f := fun k => k + 1) hk

/-- The finite sequences over `A` whose domain contains `n`. -/
noncomputable def SeqsFrom (A n : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun a => ∃ d ∈ ωZ, IsDom a d ∧ n ⊆ d) (Seqs A)

/-- `SeqsFrom A (natZ (fvSup φ))` is exactly the set of appropriate assignments for `φ`. -/
theorem mem_SeqsFrom {A a : ZFSet.{u}} {φ : Fm} :
    a ∈ SeqsFrom A (natZ (fvSup φ)) ↔
      IsSeqA ωZ A a ∧ ∀ k ∈ Fm.fv φ, InDomZ a (natZ k) := by
  unfold SeqsFrom
  rw [ZFSet.mem_sep, mem_Seqs]
  constructor
  · rintro ⟨ha, d, -, hdom, hsub⟩
    refine ⟨ha, fun k hk => ?_⟩
    have h1 : natZ.{u} k ∈ natZ.{u} (fvSup φ) := mem_natZ_iff.mpr ⟨k, lt_fvSup hk, rfl⟩
    exact (hdom (natZ k)).mp (hsub h1)
  · rintro ⟨ha, hcov⟩
    obtain ⟨n, hdom⟩ := isSeqA_dom ha
    refine ⟨ha, natZ n, natZ_mem_ωZ n, hdom, ?_⟩
    have hle : fvSup φ ≤ n := Finset.sup_le fun k hk => by
      obtain ⟨y, hy⟩ := hcov k hk
      obtain ⟨k', hk', hkk⟩ := mem_natZ_iff.mp ((hdom (natZ k)).mpr ⟨y, hy⟩)
      have : k = k' := natZ_injective hkk
      omega
    intro z hz
    obtain ⟨k, hk, rfl⟩ := mem_natZ_iff.mp hz
    exact mem_natZ_iff.mpr ⟨k, by omega, rfl⟩

/-! ### Truth sets of a formula together with its subformulas -/

/-- The truth pairs of the single formula `φ`, over the appropriate assignments. -/
noncomputable def TAtom (A : ZFSet.{u}) (φ : Fm) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ a, z = ZFSet.pair (Fm.code.{u} φ) a ∧ SatIn A (SeqVal a) φ)
    (kprodZ ({Fm.code.{u} φ} : ZFSet.{u}) (SeqsFrom A (natZ (fvSup φ))))

theorem mem_TAtom {A : ZFSet.{u}} {φ : Fm} {z : ZFSet.{u}} :
    z ∈ TAtom A φ ↔ ∃ a, IsSeqA ωZ A a ∧ (∀ k ∈ Fm.fv φ, InDomZ a (natZ k)) ∧
      z = ZFSet.pair (Fm.code.{u} φ) a ∧ SatIn A (SeqVal a) φ := by
  unfold TAtom
  rw [ZFSet.mem_sep, mem_kprodZ]
  constructor
  · rintro ⟨⟨c, hc, a, ha, rfl⟩, a', he, hs⟩
    rw [ZFSet.mem_singleton] at hc
    subst hc
    rw [ZFSet.pair_inj] at he
    obtain ⟨-, rfl⟩ := he
    obtain ⟨ha1, ha2⟩ := mem_SeqsFrom.mp ha
    exact ⟨a, ha1, ha2, rfl, hs⟩
  · rintro ⟨a, ha, hcov, rfl, hs⟩
    exact ⟨⟨_, ZFSet.mem_singleton.mpr rfl, a, mem_SeqsFrom.mpr ⟨ha, hcov⟩, rfl⟩, a, rfl, hs⟩

/-- The truth pairs of `φ` and all its subformulas. -/
noncomputable def TSet (A : ZFSet.{u}) : Fm → ZFSet.{u}
  | .falsum => TAtom A .falsum
  | .eq i j => TAtom A (.eq i j)
  | .mem i j => TAtom A (.mem i j)
  | .imp φ ψ => TAtom A (.imp φ ψ) ∪ (TSet A φ ∪ TSet A ψ)
  | .all i φ => TAtom A (.all i φ) ∪ TSet A φ

theorem TAtom_subset_TSet {A : ZFSet.{u}} (φ : Fm) : TAtom A φ ⊆ TSet A φ := by
  cases φ with
  | falsum => exact fun z hz => hz
  | eq i j => exact fun z hz => hz
  | mem i j => exact fun z hz => hz
  | imp φ ψ => exact fun z hz => ZFSet.mem_union.mpr (Or.inl hz)
  | all i φ => exact fun z hz => ZFSet.mem_union.mpr (Or.inl hz)

theorem TSet_sound {A : ZFSet.{u}} : ∀ (φ : Fm) (z : ZFSet.{u}), z ∈ TSet A φ →
    ∃ (ψ : Fm) (a : ZFSet.{u}), IsSeqA ωZ A a ∧ (∀ k ∈ Fm.fv ψ, InDomZ a (natZ k)) ∧
      z = ZFSet.pair (Fm.code.{u} ψ) a ∧ SatIn A (SeqVal a) ψ := by
  intro φ
  induction φ with
  | falsum =>
    intro z hz; obtain ⟨a, ha, hc, he, hs⟩ := mem_TAtom.mp hz; exact ⟨_, a, ha, hc, he, hs⟩
  | eq i j =>
    intro z hz; obtain ⟨a, ha, hc, he, hs⟩ := mem_TAtom.mp hz; exact ⟨_, a, ha, hc, he, hs⟩
  | mem i j =>
    intro z hz; obtain ⟨a, ha, hc, he, hs⟩ := mem_TAtom.mp hz; exact ⟨_, a, ha, hc, he, hs⟩
  | imp φ ψ ihφ ihψ =>
    intro z hz
    have hz' : z ∈ TAtom A (Fm.imp φ ψ) ∪ (TSet A φ ∪ TSet A ψ) := hz
    rw [ZFSet.mem_union, ZFSet.mem_union] at hz'
    rcases hz' with hz' | hz' | hz'
    · obtain ⟨a, ha, hc, he, hs⟩ := mem_TAtom.mp hz'; exact ⟨_, a, ha, hc, he, hs⟩
    · exact ihφ z hz'
    · exact ihψ z hz'
  | all i φ ih =>
    intro z hz
    have hz' : z ∈ TAtom A (Fm.all i φ) ∪ TSet A φ := hz
    rw [ZFSet.mem_union] at hz'
    rcases hz' with hz' | hz'
    · obtain ⟨a, ha, hc, he, hs⟩ := mem_TAtom.mp hz'; exact ⟨_, a, ha, hc, he, hs⟩
    · exact ih z hz'

theorem pair_code_mem_TSet {A a : ZFSet.{u}} {φ : Fm} :
    ZFSet.pair (Fm.code.{u} φ) a ∈ TSet A φ ↔ IsSeqA ωZ A a ∧
      (∀ k ∈ Fm.fv φ, InDomZ a (natZ k)) ∧ SatIn A (SeqVal a) φ := by
  constructor
  · intro h
    obtain ⟨ψ, a', ha', hc', he, hs⟩ := TSet_sound φ _ h
    rw [ZFSet.pair_inj] at he
    obtain ⟨h1, rfl⟩ := he
    have hpsi : φ = ψ := Fm.code_injective h1
    subst hpsi
    exact ⟨ha', hc', hs⟩
  · rintro ⟨ha, hcov, hs⟩
    exact TAtom_subset_TSet φ (mem_TAtom.mpr ⟨a, ha, hcov, rfl, hs⟩)

/-! ### Δ₀ matrices and valuations for the truth-set clauses -/

private noncomputable def val10 (x1 x3 x4 x5 x6 x7 x8 x9 x10 : ZFSet.{u}) : ℕ → ZFSet.{u} :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
      (fun _ => (∅ : ZFSet.{u})) 1 x1) 3 x3) 4 x4) 5 x5) 6 x6) 7 x7) 8 x8) 9 x9) 10 x10

private theorem hv10 {θ : Ordinal.{u}} {x1 x3 x4 x5 x6 x7 x8 x9 x10 : ZFSet.{u}}
    (h1 : x1 ∈ L θ) (h3 : x3 ∈ L θ) (h4 : x4 ∈ L θ) (h5 : x5 ∈ L θ) (h6 : x6 ∈ L θ)
    (h7 : x7 ∈ L θ) (h8 : x8 ∈ L θ) (h9 : x9 ∈ L θ) (h10 : x10 ∈ L θ)
    (he : (∅ : ZFSet.{u}) ∈ L θ) :
    ∀ k : ℕ, val10 x1 x3 x4 x5 x6 x7 x8 x9 x10 k ∈ L θ := by
  intro k
  simp only [val10, Function.update_apply]
  split_ifs <;> assumption

theorem seqsFrom_mem_L (hθ : IsAdmissible θ) {A n : ZFSet.{u}} (hA : A ∈ L θ) (hn : n ∈ L θ) :
    SeqsFrom A n ∈ L θ := by
  have he : (∅ : ZFSet.{u}) ∈ L θ := empty_mem_L_of_limit hθ.isSuccLimit
  have hQ : Delta0Def ({0, 1, 3} : Finset ℕ) (fun _ v =>
      ∃ d ∈ v 1, IsDom (v 0) d ∧ v 3 ⊆ d) := by
    have body := ((delta0_isDom 0 11 (by omega)).and (delta0_subset 3 11 (by omega))).bex 11 1
      (by omega)
    exact (body.congr (by
      intro D v _ _
      simp (disch := omega) only [Function.update_self, Function.update_of_ne])).mono (by decide)
  exact sepL hθ hQ (v := val10 ωZ n ∅ ∅ ∅ ∅ ∅ ∅ ∅)
    (fun k _ _ => hv10 hθ.omega_mem hn he he he he he he he he k) (seqs_mem_L hθ hA) _
    (by intro z; simp (disch := omega) only [val10, Function.update_self, Function.update_of_ne])

theorem TSet_mem_L (hθ : IsAdmissible θ) {A : ZFSet.{u}} (hA : A ∈ L θ) :
    ∀ φ : Fm, TSet A φ ∈ L θ := by
  have hlim := hθ.isSuccLimit
  have he : (∅ : ZFSet.{u}) ∈ L θ := empty_mem_L_of_limit hlim
  have hcode : ∀ ψ : Fm, Fm.code.{u} ψ ∈ L θ := fun ψ => L_mono hθ.omega_lt.le (Fm.code_mem_Lω ψ)
  have hnat : ∀ n : ℕ, natZ.{u} n ∈ L θ := fun n => natZ_mem_L hθ.omega_lt n
  have hSF : ∀ ψ : Fm, SeqsFrom A (natZ (fvSup ψ)) ∈ L θ :=
    fun ψ => seqsFrom_mem_L hθ hA (hnat _)
  have hbd : ∀ ψ : Fm,
      kprodZ ({Fm.code.{u} ψ} : ZFSet.{u}) (SeqsFrom A (natZ (fvSup ψ))) ∈ L θ :=
    fun ψ => kprod_mem_L hθ (singleton_mem_L_of_limit hlim (hcode ψ)) (hSF ψ)
  intro φ
  induction φ with
  | falsum =>
    have h0 : TSet A Fm.falsum = ∅ := by
      show TAtom A Fm.falsum = ∅
      ext z
      simp only [ZFSet.notMem_empty, iff_false]
      intro hz
      obtain ⟨a, -, -, -, hs⟩ := mem_TAtom.mp hz
      exact sat_falsum.mp hs
    rw [h0]; exact he
  | eq i j =>
    have hQ : Delta0Def ({0, 1, 3, 4, 5, 6} : Finset ℕ) (fun _ v =>
        ∃ a ∈ v 1, v 0 = ZFSet.pair (v 3) a ∧
          ∃ x ∈ v 4, ValAt a (v 5) x ∧ ∃ y ∈ v 4, ValAt a (v 6) y ∧ x = y) := by
      have e2 := ((delta0_valAt 11 6 13 (by omega) (by omega) (by omega)).and
        (Delta0Def.eq 12 13)).bex 13 4 (by omega)
      have e1 := ((delta0_valAt 11 5 12 (by omega) (by omega) (by omega)).and e2).bex 12 4
        (by omega)
      have body := ((delta0_isKPair 0 3 11 (by omega) (by omega)).and e1).bex 11 1 (by omega)
      exact (body.congr (by
        intro D v _ _
        simp (disch := omega) only [Function.update_self, Function.update_of_ne])).mono (by decide)
    have hE : TSet A (Fm.eq i j) = ZFSet.sep
        (fun z => ∃ a ∈ SeqsFrom A (natZ (fvSup (Fm.eq i j))),
          z = ZFSet.pair (Fm.code.{u} (Fm.eq i j)) a ∧
          ∃ x ∈ A, ValAt a (natZ i) x ∧ ∃ y ∈ A, ValAt a (natZ j) y ∧ x = y)
        (kprodZ ({Fm.code.{u} (Fm.eq i j)} : ZFSet.{u})
          (SeqsFrom A (natZ (fvSup (Fm.eq i j))))) := by
      show TAtom A (Fm.eq i j) = _
      ext z
      rw [mem_TAtom, ZFSet.mem_sep, mem_kprodZ]
      constructor
      · rintro ⟨a, ha, hcov, rfl, hs⟩
        exact ⟨⟨_, ZFSet.mem_singleton.mpr rfl, a, mem_SeqsFrom.mpr ⟨ha, hcov⟩, rfl⟩,
          a, mem_SeqsFrom.mpr ⟨ha, hcov⟩, rfl,
          _, seqVal_mem_of_inDom ha (hcov i (by simp [Fm.fv])),
          (valAt_iff ha.1 (hcov i (by simp [Fm.fv]))).mpr rfl,
          _, seqVal_mem_of_inDom ha (hcov j (by simp [Fm.fv])),
          (valAt_iff ha.1 (hcov j (by simp [Fm.fv]))).mpr rfl, hs⟩
      · rintro ⟨-, a, haS, rfl, x, hx, hxv, y, hy, hyv, hxy⟩
        obtain ⟨ha, hcov⟩ := mem_SeqsFrom.mp haS
        refine ⟨a, ha, hcov, rfl, ?_⟩
        rw [valAt_iff ha.1 (hcov i (by simp [Fm.fv]))] at hxv
        rw [valAt_iff ha.1 (hcov j (by simp [Fm.fv]))] at hyv
        show SeqVal a i = SeqVal a j
        rw [← hxv, ← hyv]; exact hxy
    rw [hE]
    exact sepL hθ hQ
      (v := val10 (SeqsFrom A (natZ (fvSup (Fm.eq i j)))) (Fm.code.{u} (Fm.eq i j)) A
        (natZ i) (natZ j) ∅ ∅ ∅ ∅)
      (fun k _ _ => hv10 (hSF _) (hcode _) hA (hnat i) (hnat j) he he he he he k) (hbd _) _
      (by intro z; simp (disch := omega) only [val10, Function.update_self, Function.update_of_ne])
  | mem i j =>
    have hQ : Delta0Def ({0, 1, 3, 4, 5, 6} : Finset ℕ) (fun _ v =>
        ∃ a ∈ v 1, v 0 = ZFSet.pair (v 3) a ∧
          ∃ x ∈ v 4, ValAt a (v 5) x ∧ ∃ y ∈ v 4, ValAt a (v 6) y ∧ x ∈ y) := by
      have e2 := ((delta0_valAt 11 6 13 (by omega) (by omega) (by omega)).and
        (Delta0Def.mem 12 13)).bex 13 4 (by omega)
      have e1 := ((delta0_valAt 11 5 12 (by omega) (by omega) (by omega)).and e2).bex 12 4
        (by omega)
      have body := ((delta0_isKPair 0 3 11 (by omega) (by omega)).and e1).bex 11 1 (by omega)
      exact (body.congr (by
        intro D v _ _
        simp (disch := omega) only [Function.update_self, Function.update_of_ne])).mono (by decide)
    have hE : TSet A (Fm.mem i j) = ZFSet.sep
        (fun z => ∃ a ∈ SeqsFrom A (natZ (fvSup (Fm.mem i j))),
          z = ZFSet.pair (Fm.code.{u} (Fm.mem i j)) a ∧
          ∃ x ∈ A, ValAt a (natZ i) x ∧ ∃ y ∈ A, ValAt a (natZ j) y ∧ x ∈ y)
        (kprodZ ({Fm.code.{u} (Fm.mem i j)} : ZFSet.{u})
          (SeqsFrom A (natZ (fvSup (Fm.mem i j))))) := by
      show TAtom A (Fm.mem i j) = _
      ext z
      rw [mem_TAtom, ZFSet.mem_sep, mem_kprodZ]
      constructor
      · rintro ⟨a, ha, hcov, rfl, hs⟩
        exact ⟨⟨_, ZFSet.mem_singleton.mpr rfl, a, mem_SeqsFrom.mpr ⟨ha, hcov⟩, rfl⟩,
          a, mem_SeqsFrom.mpr ⟨ha, hcov⟩, rfl,
          _, seqVal_mem_of_inDom ha (hcov i (by simp [Fm.fv])),
          (valAt_iff ha.1 (hcov i (by simp [Fm.fv]))).mpr rfl,
          _, seqVal_mem_of_inDom ha (hcov j (by simp [Fm.fv])),
          (valAt_iff ha.1 (hcov j (by simp [Fm.fv]))).mpr rfl, hs⟩
      · rintro ⟨-, a, haS, rfl, x, hx, hxv, y, hy, hyv, hxy⟩
        obtain ⟨ha, hcov⟩ := mem_SeqsFrom.mp haS
        refine ⟨a, ha, hcov, rfl, ?_⟩
        rw [valAt_iff ha.1 (hcov i (by simp [Fm.fv]))] at hxv
        rw [valAt_iff ha.1 (hcov j (by simp [Fm.fv]))] at hyv
        show SeqVal a i ∈ SeqVal a j
        rw [← hxv, ← hyv]; exact hxy
    rw [hE]
    exact sepL hθ hQ
      (v := val10 (SeqsFrom A (natZ (fvSup (Fm.mem i j)))) (Fm.code.{u} (Fm.mem i j)) A
        (natZ i) (natZ j) ∅ ∅ ∅ ∅)
      (fun k _ _ => hv10 (hSF _) (hcode _) hA (hnat i) (hnat j) he he he he he k) (hbd _) _
      (by intro z; simp (disch := omega) only [val10, Function.update_self, Function.update_of_ne])
  | imp φ ψ ihφ ihψ =>
    have hQ : Delta0Def ({0, 1, 3, 7, 8, 9, 10} : Finset ℕ) (fun _ v =>
        ∃ a ∈ v 1, v 0 = ZFSet.pair (v 3) a ∧
          (ZFSet.pair (v 7) a ∈ v 8 → ZFSet.pair (v 9) a ∈ v 10)) := by
      have body := ((delta0_isKPair 0 3 11 (by omega) (by omega)).and
        ((delta0_funVal 8 7 11 (by omega) (by omega) (by omega)).imp
          (delta0_funVal 10 9 11 (by omega) (by omega) (by omega)))).bex 11 1 (by omega)
      exact (body.congr (by
        intro D v _ _
        simp (disch := omega) only [Function.update_self, Function.update_of_ne])).mono (by decide)
    have hE : TAtom A (Fm.imp φ ψ) = ZFSet.sep
        (fun z => ∃ a ∈ SeqsFrom A (natZ (fvSup (Fm.imp φ ψ))),
          z = ZFSet.pair (Fm.code.{u} (Fm.imp φ ψ)) a ∧
          (ZFSet.pair (Fm.code.{u} φ) a ∈ TSet A φ → ZFSet.pair (Fm.code.{u} ψ) a ∈ TSet A ψ))
        (kprodZ ({Fm.code.{u} (Fm.imp φ ψ)} : ZFSet.{u})
          (SeqsFrom A (natZ (fvSup (Fm.imp φ ψ))))) := by
      ext z
      rw [mem_TAtom, ZFSet.mem_sep, mem_kprodZ]
      constructor
      · rintro ⟨a, ha, hcov, rfl, hs⟩
        have hcφ : ∀ k ∈ Fm.fv φ, InDomZ a (natZ k) := fun k hk =>
          hcov k (by simp only [Fm.fv, Finset.mem_union]; exact Or.inl hk)
        have hcψ : ∀ k ∈ Fm.fv ψ, InDomZ a (natZ k) := fun k hk =>
          hcov k (by simp only [Fm.fv, Finset.mem_union]; exact Or.inr hk)
        refine ⟨⟨_, ZFSet.mem_singleton.mpr rfl, a, mem_SeqsFrom.mpr ⟨ha, hcov⟩, rfl⟩,
          a, mem_SeqsFrom.mpr ⟨ha, hcov⟩, rfl, fun hφ => ?_⟩
        exact pair_code_mem_TSet.mpr
          ⟨ha, hcψ, sat_imp.mp hs (pair_code_mem_TSet.mp hφ).2.2⟩
      · rintro ⟨-, a, haS, rfl, H⟩
        obtain ⟨ha, hcov⟩ := mem_SeqsFrom.mp haS
        have hcφ : ∀ k ∈ Fm.fv φ, InDomZ a (natZ k) := fun k hk =>
          hcov k (by simp only [Fm.fv, Finset.mem_union]; exact Or.inl hk)
        refine ⟨a, ha, hcov, rfl, sat_imp.mpr fun hφ => ?_⟩
        exact (pair_code_mem_TSet.mp (H (pair_code_mem_TSet.mpr ⟨ha, hcφ, hφ⟩))).2.2
    have hAt : TAtom A (Fm.imp φ ψ) ∈ L θ := by
      rw [hE]
      exact sepL hθ hQ
        (v := val10 (SeqsFrom A (natZ (fvSup (Fm.imp φ ψ)))) (Fm.code.{u} (Fm.imp φ ψ)) ∅ ∅ ∅
          (Fm.code.{u} φ) (TSet A φ) (Fm.code.{u} ψ) (TSet A ψ))
        (fun k _ _ => hv10 (hSF _) (hcode _) he he he (hcode φ) ihφ (hcode ψ) ihψ he k) (hbd _) _
        (by intro z
            simp (disch := omega) only [val10, Function.update_self, Function.update_of_ne])
    show TAtom A (Fm.imp φ ψ) ∪ (TSet A φ ∪ TSet A ψ) ∈ L θ
    exact union_mem_L_of_limit hlim hAt (union_mem_L_of_limit hlim ihφ ihψ)
  | all i φ ih =>
    have hQ : Delta0Def ({0, 1, 3, 4, 5, 6, 7, 8} : Finset ℕ) (fun _ v =>
        ∃ a ∈ v 1, v 0 = ZFSet.pair (v 3) a ∧
          ∀ x ∈ v 4, ∀ b ∈ v 6, IsUpdSeq a (v 5) x b → ZFSet.pair (v 7) b ∈ v 8) := by
      have inner := ((delta0_isUpdSeq 11 5 12 14 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)).imp
        (delta0_funVal 8 7 14 (by omega) (by omega) (by omega))).ball 14 6 (by omega)
      have inner2 := inner.ball 12 4 (by omega)
      have body := ((delta0_isKPair 0 3 11 (by omega) (by omega)).and inner2).bex 11 1 (by omega)
      exact (body.congr (by
        intro D v _ _
        simp (disch := omega) only [Function.update_self, Function.update_of_ne])).mono (by decide)
    have hE : TAtom A (Fm.all i φ) = ZFSet.sep
        (fun z => ∃ a ∈ SeqsFrom A (natZ (fvSup (Fm.all i φ))),
          z = ZFSet.pair (Fm.code.{u} (Fm.all i φ)) a ∧
          ∀ x ∈ A, ∀ b ∈ SeqsFrom A (natZ (fvSup φ)), IsUpdSeq a (natZ i) x b →
            ZFSet.pair (Fm.code.{u} φ) b ∈ TSet A φ)
        (kprodZ ({Fm.code.{u} (Fm.all i φ)} : ZFSet.{u})
          (SeqsFrom A (natZ (fvSup (Fm.all i φ))))) := by
      ext z
      rw [mem_TAtom, ZFSet.mem_sep, mem_kprodZ]
      have key : ∀ (a : ZFSet.{u}), IsSeqA ωZ A a →
          (∀ k ∈ Fm.fv (Fm.all i φ), InDomZ a (natZ k)) → ∀ x ∈ A, ∀ b, IsUpdSeq a (natZ i) x b →
          b ∈ SeqsFrom A (natZ (fvSup φ)) ∧
            (SatIn A (SeqVal b) φ ↔ SatIn A (Function.update (SeqVal a) i x) φ) := by
        intro a ha hcov x hx b hb
        simp only [Fm.fv] at hcov
        obtain ⟨b', hb', hbseq, hbdom, hbval⟩ := exists_updSeq ha i hx
        have hbcov : ∀ k ∈ Fm.fv φ, InDomZ b' (natZ k) := by
          intro k hk
          by_cases hki : k = i
          · exact hbdom k (Or.inr hki)
          · exact hbdom k (Or.inl (hcov k (Finset.mem_erase.mpr ⟨hki, hk⟩)))
        have hagree : ∀ k ∈ Fm.fv φ, SeqVal b' k = Function.update (SeqVal a) i x k := by
          intro k hk
          by_cases hki : k = i
          · exact hbval k (Or.inr hki)
          · exact hbval k (Or.inl (hcov k (Finset.mem_erase.mpr ⟨hki, hk⟩)))
        rw [isUpdSeq_unique hb hb']
        exact ⟨mem_SeqsFrom.mpr ⟨hbseq, hbcov⟩, sat_congr hagree⟩
      constructor
      · rintro ⟨a, ha, hcov, rfl, hs⟩
        refine ⟨⟨_, ZFSet.mem_singleton.mpr rfl, a, mem_SeqsFrom.mpr ⟨ha, hcov⟩, rfl⟩,
          a, mem_SeqsFrom.mpr ⟨ha, hcov⟩, rfl, fun x hx b hbS hub => ?_⟩
        obtain ⟨hbS', hiff⟩ := key a ha hcov x hx b hub
        obtain ⟨hbseq, hbcov⟩ := mem_SeqsFrom.mp hbS'
        exact pair_code_mem_TSet.mpr ⟨hbseq, hbcov, hiff.mpr (sat_all.mp hs x hx)⟩
      · rintro ⟨-, a, haS, rfl, H⟩
        obtain ⟨ha, hcov⟩ := mem_SeqsFrom.mp haS
        refine ⟨a, ha, hcov, rfl, sat_all.mpr fun x hx => ?_⟩
        obtain ⟨b', hb', -, -, -⟩ := exists_updSeq ha i hx
        obtain ⟨hbS', hiff⟩ := key a ha hcov x hx b' hb'
        exact hiff.mp (pair_code_mem_TSet.mp (H x hx b' hbS' hb')).2.2
    have hAt : TAtom A (Fm.all i φ) ∈ L θ := by
      rw [hE]
      exact sepL hθ hQ
        (v := val10 (SeqsFrom A (natZ (fvSup (Fm.all i φ)))) (Fm.code.{u} (Fm.all i φ)) A
          (natZ i) (SeqsFrom A (natZ (fvSup φ))) (Fm.code.{u} φ) (TSet A φ) ∅ ∅)
        (fun k _ _ => hv10 (hSF _) (hcode _) hA (hnat i) (hSF _) (hcode φ) ih he he he k)
        (hbd _) _
        (by intro z
            simp (disch := omega) only [val10, Function.update_self, Function.update_of_ne])
    show TAtom A (Fm.all i φ) ∪ TSet A φ ∈ L θ
    exact union_mem_L_of_limit hlim hAt ih

/-! ### Shapes of codes -/

theorem code_eq_falsum {χ : Fm} (h : Fm.code.{u} χ = ZFSet.pair (natZ 0) (natZ 0)) :
    χ = Fm.falsum := by
  cases χ with
  | falsum => rfl
  | eq i j => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | mem i j => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | imp φ ψ => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | all i φ => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))

theorem code_eq_eq {χ : Fm} {i j : ZFSet.{u}}
    (h : Fm.code.{u} χ = ZFSet.pair (natZ 1) (ZFSet.pair i j)) :
    ∃ m n : ℕ, χ = Fm.eq m n ∧ i = natZ m ∧ j = natZ n := by
  cases χ with
  | falsum => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | eq m n =>
    simp only [Fm.code, ZFSet.pair_inj] at h
    exact ⟨m, n, rfl, h.2.1.symm, h.2.2.symm⟩
  | mem m n => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | imp φ ψ => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | all m φ => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))

theorem code_eq_mem {χ : Fm} {i j : ZFSet.{u}}
    (h : Fm.code.{u} χ = ZFSet.pair (natZ 2) (ZFSet.pair i j)) :
    ∃ m n : ℕ, χ = Fm.mem m n ∧ i = natZ m ∧ j = natZ n := by
  cases χ with
  | falsum => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | eq m n => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | mem m n =>
    simp only [Fm.code, ZFSet.pair_inj] at h
    exact ⟨m, n, rfl, h.2.1.symm, h.2.2.symm⟩
  | imp φ ψ => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | all m φ => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))

theorem code_eq_imp {χ : Fm} {e₁ e₂ : ZFSet.{u}}
    (h : Fm.code.{u} χ = ZFSet.pair (natZ 3) (ZFSet.pair e₁ e₂)) :
    ∃ χ₁ χ₂ : Fm, χ = Fm.imp χ₁ χ₂ ∧ e₁ = Fm.code.{u} χ₁ ∧ e₂ = Fm.code.{u} χ₂ := by
  cases χ with
  | falsum => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | eq m n => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | mem m n => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | imp φ ψ =>
    simp only [Fm.code, ZFSet.pair_inj] at h
    exact ⟨φ, ψ, rfl, h.2.1.symm, h.2.2.symm⟩
  | all m φ => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))

theorem code_eq_all {χ : Fm} {i e' : ZFSet.{u}}
    (h : Fm.code.{u} χ = ZFSet.pair (natZ 4) (ZFSet.pair i e')) :
    ∃ (m : ℕ) (χ' : Fm), χ = Fm.all m χ' ∧ i = natZ m ∧ e' = Fm.code.{u} χ' := by
  cases χ with
  | falsum => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | eq m n => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | mem m n => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | imp φ ψ => simp only [Fm.code, ZFSet.pair_inj] at h; exact absurd h.1 (natZ_ne (by decide))
  | all m φ =>
    simp only [Fm.code, ZFSet.pair_inj] at h
    exact ⟨m, φ, rfl, h.2.1.symm, h.2.2.symm⟩

/-! ### The set of subformula codes -/

/-- The codes of `φ` and of all its subformulas. -/
noncomputable def Cs : Fm → ZFSet.{u}
  | .falsum => {Fm.code.{u} .falsum}
  | .eq i j => {Fm.code.{u} (.eq i j)}
  | .mem i j => {Fm.code.{u} (.mem i j)}
  | .imp φ ψ => insert (Fm.code.{u} (.imp φ ψ)) (Cs φ ∪ Cs ψ)
  | .all i φ => insert (Fm.code.{u} (.all i φ)) (Cs φ)

theorem code_mem_Cs (φ : Fm) : Fm.code.{u} φ ∈ Cs.{u} φ := by
  cases φ with
  | falsum => exact ZFSet.mem_singleton.mpr rfl
  | eq i j => exact ZFSet.mem_singleton.mpr rfl
  | mem i j => exact ZFSet.mem_singleton.mpr rfl
  | imp φ ψ => exact ZFSet.mem_insert_iff.mpr (Or.inl rfl)
  | all i φ => exact ZFSet.mem_insert_iff.mpr (Or.inl rfl)

theorem Cs_mem_L (hθ : IsAdmissible θ) : ∀ φ : Fm, Cs.{u} φ ∈ L θ := by
  have hlim := hθ.isSuccLimit
  have hcode : ∀ ψ : Fm, Fm.code.{u} ψ ∈ L θ := fun ψ => L_mono hθ.omega_lt.le (Fm.code_mem_Lω ψ)
  intro φ
  induction φ with
  | falsum => exact singleton_mem_L_of_limit hlim (hcode _)
  | eq i j => exact singleton_mem_L_of_limit hlim (hcode _)
  | mem i j => exact singleton_mem_L_of_limit hlim (hcode _)
  | imp φ ψ ihφ ihψ =>
    exact insert_mem_L_of_limit hlim (hcode _) (union_mem_L_of_limit hlim ihφ ihψ)
  | all i φ ih => exact insert_mem_L_of_limit hlim (hcode _) ih

/-- Every element of `Cs φ` is the code of a subformula, whose own data is contained in
that of `φ`. -/
theorem Cs_sub {A : ZFSet.{u}} : ∀ (φ : Fm), ∀ e ∈ Cs.{u} φ, ∃ χ : Fm, e = Fm.code.{u} χ ∧
    Cs.{u} χ ⊆ Cs.{u} φ ∧ TSet A χ ⊆ TSet A φ := by
  intro φ
  induction φ with
  | falsum =>
    intro e he
    have he' : e ∈ ({Fm.code.{u} (Fm.falsum)} : ZFSet.{u}) := he
    rw [ZFSet.mem_singleton] at he'
    exact ⟨Fm.falsum, he', subset_rfl, subset_rfl⟩
  | eq i j =>
    intro e he
    have he' : e ∈ ({Fm.code.{u} (Fm.eq i j)} : ZFSet.{u}) := he
    rw [ZFSet.mem_singleton] at he'
    exact ⟨Fm.eq i j, he', subset_rfl, subset_rfl⟩
  | mem i j =>
    intro e he
    have he' : e ∈ ({Fm.code.{u} (Fm.mem i j)} : ZFSet.{u}) := he
    rw [ZFSet.mem_singleton] at he'
    exact ⟨Fm.mem i j, he', subset_rfl, subset_rfl⟩
  | imp φ ψ ihφ ihψ =>
    have hCφ : Cs.{u} φ ⊆ Cs.{u} (Fm.imp φ ψ) := fun x hx =>
      ZFSet.mem_insert_iff.mpr (Or.inr (ZFSet.mem_union.mpr (Or.inl hx)))
    have hCψ : Cs.{u} ψ ⊆ Cs.{u} (Fm.imp φ ψ) := fun x hx =>
      ZFSet.mem_insert_iff.mpr (Or.inr (ZFSet.mem_union.mpr (Or.inr hx)))
    have hTφ : TSet A φ ⊆ TSet A (Fm.imp φ ψ) := fun x hx =>
      ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_union.mpr (Or.inl hx)))
    have hTψ : TSet A ψ ⊆ TSet A (Fm.imp φ ψ) := fun x hx =>
      ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_union.mpr (Or.inr hx)))
    intro e he
    have he' : e ∈ insert (Fm.code.{u} (Fm.imp φ ψ)) (Cs.{u} φ ∪ Cs.{u} ψ) := he
    rw [ZFSet.mem_insert_iff, ZFSet.mem_union] at he'
    rcases he' with rfl | he' | he'
    · exact ⟨Fm.imp φ ψ, rfl, subset_rfl, subset_rfl⟩
    · obtain ⟨χ, hχ, hC, hT⟩ := ihφ e he'
      exact ⟨χ, hχ, hC.trans hCφ, hT.trans hTφ⟩
    · obtain ⟨χ, hχ, hC, hT⟩ := ihψ e he'
      exact ⟨χ, hχ, hC.trans hCψ, hT.trans hTψ⟩
  | all i φ ih =>
    have hCφ : Cs.{u} φ ⊆ Cs.{u} (Fm.all i φ) := fun x hx =>
      ZFSet.mem_insert_iff.mpr (Or.inr hx)
    have hTφ : TSet A φ ⊆ TSet A (Fm.all i φ) := fun x hx => ZFSet.mem_union.mpr (Or.inr hx)
    intro e he
    have he' : e ∈ insert (Fm.code.{u} (Fm.all i φ)) (Cs.{u} φ) := he
    rw [ZFSet.mem_insert_iff] at he'
    rcases he' with rfl | he'
    · exact ⟨Fm.all i φ, rfl, subset_rfl, subset_rfl⟩
    · obtain ⟨χ, hχ, hC, hT⟩ := ih e he'
      exact ⟨χ, hχ, hC.trans hCφ, hT.trans hTφ⟩

theorem pair_code_mem_TSet_sub {A a : ZFSet.{u}} {φ χ : Fm} (h : TSet A χ ⊆ TSet A φ) :
    ZFSet.pair (Fm.code.{u} χ) a ∈ TSet A φ ↔ IsSeqA ωZ A a ∧
      (∀ k ∈ Fm.fv χ, InDomZ a (natZ k)) ∧ SatIn A (SeqVal a) χ := by
  constructor
  · intro hz
    obtain ⟨ψ, a', ha', hc', hee, hs⟩ := TSet_sound φ _ hz
    rw [ZFSet.pair_inj] at hee
    obtain ⟨h1, rfl⟩ := hee
    have hx : χ = ψ := Fm.code_injective h1
    subst hx
    exact ⟨ha', hc', hs⟩
  · rintro ⟨ha, hcov, hs⟩
    exact h (pair_code_mem_TSet.mpr ⟨ha, hcov, hs⟩)

/-! ### Partial satisfaction structures -/

/-- `C` is closed under the codes of immediate subformulas (`C₀` bounds all codes). -/
def SubCl (W C₀ C : ZFSet.{u}) : Prop :=
  ∀ e ∈ C,
    (∀ e₁ ∈ C₀, ∀ e₂ ∈ C₀, e = ZFSet.pair (natZ 3) (ZFSet.pair e₁ e₂) → e₁ ∈ C ∧ e₂ ∈ C) ∧
    (∀ i ∈ W, ∀ e' ∈ C₀, e = ZFSet.pair (natZ 4) (ZFSet.pair i e') → e' ∈ C)

/-- `t` satisfies the Tarski clauses over the structure `(A, ∈)` for the codes in `C`. -/
def TClause (A S W C₀ C t : ZFSet.{u}) : Prop :=
  ∀ e ∈ C, ∀ a ∈ S,
    (e = ZFSet.pair (natZ 0) (natZ 0) → ZFSet.pair e a ∉ t) ∧
    (∀ i ∈ W, ∀ j ∈ W, e = ZFSet.pair (natZ 1) (ZFSet.pair i j) → InDomZ a i → InDomZ a j →
      (ZFSet.pair e a ∈ t ↔ ∃ x ∈ A, ValAt a i x ∧ ∃ y ∈ A, ValAt a j y ∧ x = y)) ∧
    (∀ i ∈ W, ∀ j ∈ W, e = ZFSet.pair (natZ 2) (ZFSet.pair i j) → InDomZ a i → InDomZ a j →
      (ZFSet.pair e a ∈ t ↔ ∃ x ∈ A, ValAt a i x ∧ ∃ y ∈ A, ValAt a j y ∧ x ∈ y)) ∧
    (∀ e₁ ∈ C₀, ∀ e₂ ∈ C₀, e = ZFSet.pair (natZ 3) (ZFSet.pair e₁ e₂) →
      IsAsn C₀ W A e₁ a → IsAsn C₀ W A e₂ a →
      (ZFSet.pair e a ∈ t ↔ (ZFSet.pair e₁ a ∈ t → ZFSet.pair e₂ a ∈ t))) ∧
    (∀ i ∈ W, ∀ e' ∈ C₀, e = ZFSet.pair (natZ 4) (ZFSet.pair i e') →
      (∀ k ∈ W, k ≠ i → ¬ NotFreeW C₀ W k e' → InDomZ a k) →
      (ZFSet.pair e a ∈ t ↔ ∀ x ∈ A, ∀ b ∈ S, IsUpdSeq a i x b → ZFSet.pair e' b ∈ t))

/-- A partial satisfaction structure computes truth correctly, on appropriate pairs. -/
theorem tClause_correct {A C t : ZFSet.{u}}
    (hsub : SubCl ωZ (L Ordinal.omega0) C)
    (hcl : TClause A (Seqs A) ωZ (L Ordinal.omega0) C t) :
    ∀ (φ : Fm), Fm.code.{u} φ ∈ C → ∀ a, IsSeqA ωZ A a →
      (∀ k ∈ Fm.fv φ, InDomZ a (natZ k)) →
      (ZFSet.pair (Fm.code.{u} φ) a ∈ t ↔ SatIn A (SeqVal a) φ) := by
  intro φ
  induction φ with
  | falsum =>
    intro hc a ha _
    simp only [SatIn, sat_falsum, iff_false]
    exact (hcl _ hc a (mem_Seqs.mpr ha)).1 rfl
  | eq i j =>
    intro hc a ha hcov
    have hi := hcov i (by simp [Fm.fv])
    have hj := hcov j (by simp [Fm.fv])
    rw [(hcl _ hc a (mem_Seqs.mpr ha)).2.1 (natZ i) (natZ_mem_ωZ i) (natZ j) (natZ_mem_ωZ j) rfl
      hi hj]
    constructor
    · rintro ⟨x, -, hx, y, -, hy, hxy⟩
      rw [valAt_iff ha.1 hi] at hx
      rw [valAt_iff ha.1 hj] at hy
      show SeqVal a i = SeqVal a j
      rw [← hx, ← hy]; exact hxy
    · intro h
      exact ⟨_, seqVal_mem_of_inDom ha hi, (valAt_iff ha.1 hi).mpr rfl,
        _, seqVal_mem_of_inDom ha hj, (valAt_iff ha.1 hj).mpr rfl, h⟩
  | mem i j =>
    intro hc a ha hcov
    have hi := hcov i (by simp [Fm.fv])
    have hj := hcov j (by simp [Fm.fv])
    rw [(hcl _ hc a (mem_Seqs.mpr ha)).2.2.1 (natZ i) (natZ_mem_ωZ i) (natZ j) (natZ_mem_ωZ j) rfl
      hi hj]
    constructor
    · rintro ⟨x, -, hx, y, -, hy, hxy⟩
      rw [valAt_iff ha.1 hi] at hx
      rw [valAt_iff ha.1 hj] at hy
      show SeqVal a i ∈ SeqVal a j
      rw [← hx, ← hy]; exact hxy
    · intro h
      exact ⟨_, seqVal_mem_of_inDom ha hi, (valAt_iff ha.1 hi).mpr rfl,
        _, seqVal_mem_of_inDom ha hj, (valAt_iff ha.1 hj).mpr rfl, h⟩
  | imp φ ψ ihφ ihψ =>
    intro hc a ha hcov
    have hcφ : ∀ k ∈ Fm.fv φ, InDomZ a (natZ k) := fun k hk =>
      hcov k (by simp only [Fm.fv, Finset.mem_union]; exact Or.inl hk)
    have hcψ : ∀ k ∈ Fm.fv ψ, InDomZ a (natZ k) := fun k hk =>
      hcov k (by simp only [Fm.fv, Finset.mem_union]; exact Or.inr hk)
    have hclos := (hsub _ hc).1 (Fm.code.{u} φ) (Fm.code_mem_Lω φ) (Fm.code.{u} ψ)
      (Fm.code_mem_Lω ψ) rfl
    rw [(hcl _ hc a (mem_Seqs.mpr ha)).2.2.2.1 (Fm.code.{u} φ) (Fm.code_mem_Lω φ)
      (Fm.code.{u} ψ) (Fm.code_mem_Lω ψ) rfl (isAsn_code_iff.mpr ⟨ha, hcφ⟩)
      (isAsn_code_iff.mpr ⟨ha, hcψ⟩), ihφ hclos.1 a ha hcφ, ihψ hclos.2 a ha hcψ]
    exact Iff.rfl
  | all i φ ih =>
    intro hc a ha hcov
    simp only [Fm.fv] at hcov
    have hclos := (hsub _ hc).2 (natZ i) (natZ_mem_ωZ i) (Fm.code.{u} φ) (Fm.code_mem_Lω φ) rfl
    have key : ∀ x ∈ A, ∀ b, IsUpdSeq a (natZ i) x b → IsSeqA ωZ A b ∧
        (∀ k ∈ Fm.fv φ, InDomZ b (natZ k)) ∧
        (SatIn A (SeqVal b) φ ↔ SatIn A (Function.update (SeqVal a) i x) φ) := by
      intro x hx b hb
      obtain ⟨b', hb', hbseq, hbdom, hbval⟩ := exists_updSeq ha i hx
      have hbcov : ∀ k ∈ Fm.fv φ, InDomZ b' (natZ k) := by
        intro k hk
        by_cases hki : k = i
        · exact hbdom k (Or.inr hki)
        · exact hbdom k (Or.inl (hcov k (Finset.mem_erase.mpr ⟨hki, hk⟩)))
      have hagree : ∀ k ∈ Fm.fv φ, SeqVal b' k = Function.update (SeqVal a) i x k := by
        intro k hk
        by_cases hki : k = i
        · exact hbval k (Or.inr hki)
        · exact hbval k (Or.inl (hcov k (Finset.mem_erase.mpr ⟨hki, hk⟩)))
      rw [isUpdSeq_unique hb hb']
      exact ⟨hbseq, hbcov, sat_congr hagree⟩
    rw [(hcl _ hc a (mem_Seqs.mpr ha)).2.2.2.2 (natZ i) (natZ_mem_ωZ i) (Fm.code.{u} φ)
      (Fm.code_mem_Lω φ) rfl (allGuard_code_iff.mpr hcov)]
    constructor
    · intro Hall
      refine sat_all.mpr fun x hx => ?_
      obtain ⟨b, hb, -, -, -⟩ := exists_updSeq ha i hx
      obtain ⟨hbseq, hbcov, hiff⟩ := key x hx b hb
      have h2 := Hall x hx b (mem_Seqs.mpr hbseq) hb
      rw [ih hclos b hbseq hbcov] at h2
      exact hiff.mp h2
    · intro Hs x hx b hbS hub
      obtain ⟨hbseq, hbcov, hiff⟩ := key x hx b hub
      rw [ih hclos b hbseq hbcov]
      exact hiff.mpr (sat_all.mp Hs x hx)

theorem subCl_Cs (φ : Fm) : SubCl ωZ.{u} (L Ordinal.omega0) (Cs.{u} φ) := by
  intro e he
  obtain ⟨χ, rfl, hC, -⟩ := Cs_sub (A := (∅ : ZFSet.{u})) φ e he
  constructor
  · intro e₁ _ e₂ _ hshape
    obtain ⟨χ₁, χ₂, rfl, rfl, rfl⟩ := code_eq_imp hshape
    exact ⟨hC (show Fm.code.{u} χ₁ ∈ Cs.{u} (Fm.imp χ₁ χ₂) from
        ZFSet.mem_insert_iff.mpr (Or.inr (ZFSet.mem_union.mpr (Or.inl (code_mem_Cs χ₁))))),
      hC (show Fm.code.{u} χ₂ ∈ Cs.{u} (Fm.imp χ₁ χ₂) from
        ZFSet.mem_insert_iff.mpr (Or.inr (ZFSet.mem_union.mpr (Or.inr (code_mem_Cs χ₂)))))⟩
  · intro i _ e' _ hshape
    obtain ⟨m, χ', rfl, rfl, rfl⟩ := code_eq_all hshape
    exact hC (show Fm.code.{u} χ' ∈ Cs.{u} (Fm.all m χ') from
      ZFSet.mem_insert_iff.mpr (Or.inr (code_mem_Cs χ')))

theorem tClause_Cs {A : ZFSet.{u}} (φ : Fm) :
    TClause A (Seqs A) ωZ (L Ordinal.omega0) (Cs.{u} φ) (TSet A φ) := by
  intro e he a haS
  obtain ⟨χ, rfl, -, hT⟩ := Cs_sub (A := A) φ e he
  have ha : IsSeqA ωZ A a := mem_Seqs.mp haS
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hshape
    have hx : χ = Fm.falsum := code_eq_falsum hshape
    subst hx
    intro hmem
    exact sat_falsum.mp ((pair_code_mem_TSet_sub hT).mp hmem).2.2
  · intro i _ j _ hshape hdi hdj
    obtain ⟨m, n, rfl, rfl, rfl⟩ := code_eq_eq hshape
    have hcov : ∀ k ∈ Fm.fv (Fm.eq m n), InDomZ a (natZ k) := by
      intro k hk
      simp only [Fm.fv, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hdi
      · exact hdj
    rw [pair_code_mem_TSet_sub hT]
    constructor
    · rintro ⟨-, -, hs⟩
      exact ⟨_, seqVal_mem_of_inDom ha hdi, (valAt_iff ha.1 hdi).mpr rfl,
        _, seqVal_mem_of_inDom ha hdj, (valAt_iff ha.1 hdj).mpr rfl, hs⟩
    · rintro ⟨x, -, hx, y, -, hy, hxy⟩
      rw [valAt_iff ha.1 hdi] at hx
      rw [valAt_iff ha.1 hdj] at hy
      exact ⟨ha, hcov, show SeqVal a m = SeqVal a n by rw [← hx, ← hy]; exact hxy⟩
  · intro i _ j _ hshape hdi hdj
    obtain ⟨m, n, rfl, rfl, rfl⟩ := code_eq_mem hshape
    have hcov : ∀ k ∈ Fm.fv (Fm.mem m n), InDomZ a (natZ k) := by
      intro k hk
      simp only [Fm.fv, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hdi
      · exact hdj
    rw [pair_code_mem_TSet_sub hT]
    constructor
    · rintro ⟨-, -, hs⟩
      exact ⟨_, seqVal_mem_of_inDom ha hdi, (valAt_iff ha.1 hdi).mpr rfl,
        _, seqVal_mem_of_inDom ha hdj, (valAt_iff ha.1 hdj).mpr rfl, hs⟩
    · rintro ⟨x, -, hx, y, -, hy, hxy⟩
      rw [valAt_iff ha.1 hdi] at hx
      rw [valAt_iff ha.1 hdj] at hy
      exact ⟨ha, hcov, show SeqVal a m ∈ SeqVal a n by rw [← hx, ← hy]; exact hxy⟩
  · intro e₁ _ e₂ _ hshape hA1 hA2
    obtain ⟨χ₁, χ₂, rfl, rfl, rfl⟩ := code_eq_imp hshape
    obtain ⟨-, hc1⟩ := isAsn_code_iff.mp hA1
    obtain ⟨-, hc2⟩ := isAsn_code_iff.mp hA2
    have hcov : ∀ k ∈ Fm.fv (Fm.imp χ₁ χ₂), InDomZ a (natZ k) := by
      intro k hk
      simp only [Fm.fv, Finset.mem_union] at hk
      rcases hk with hk | hk
      · exact hc1 k hk
      · exact hc2 k hk
    have hT1 : TSet A χ₁ ⊆ TSet A φ := fun x hx =>
      hT (show x ∈ TSet A (Fm.imp χ₁ χ₂) from
        ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_union.mpr (Or.inl hx))))
    have hT2 : TSet A χ₂ ⊆ TSet A φ := fun x hx =>
      hT (show x ∈ TSet A (Fm.imp χ₁ χ₂) from
        ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_union.mpr (Or.inr hx))))
    rw [pair_code_mem_TSet_sub hT, pair_code_mem_TSet_sub hT1, pair_code_mem_TSet_sub hT2]
    constructor
    · rintro ⟨-, -, hs⟩ ⟨-, -, h1⟩
      exact ⟨ha, hc2, sat_imp.mp hs h1⟩
    · intro H
      exact ⟨ha, hcov, sat_imp.mpr fun h1 => (H ⟨ha, hc1, h1⟩).2.2⟩
  · intro i _ e' _ hshape hg
    obtain ⟨m, χ', rfl, rfl, rfl⟩ := code_eq_all hshape
    have hcov := allGuard_code_iff.mp hg
    have hT1 : TSet A χ' ⊆ TSet A φ := fun x hx =>
      hT (show x ∈ TSet A (Fm.all m χ') from ZFSet.mem_union.mpr (Or.inr hx))
    have key : ∀ x ∈ A, ∀ b, IsUpdSeq a (natZ m) x b → IsSeqA ωZ A b ∧
        (∀ k ∈ Fm.fv χ', InDomZ b (natZ k)) ∧
        (SatIn A (SeqVal b) χ' ↔ SatIn A (Function.update (SeqVal a) m x) χ') := by
      intro x hx b hb
      obtain ⟨b', hb', hbseq, hbdom, hbval⟩ := exists_updSeq ha m hx
      have hbcov : ∀ k ∈ Fm.fv χ', InDomZ b' (natZ k) := by
        intro k hk
        by_cases hki : k = m
        · exact hbdom k (Or.inr hki)
        · exact hbdom k (Or.inl (hcov k (Finset.mem_erase.mpr ⟨hki, hk⟩)))
      have hagree : ∀ k ∈ Fm.fv χ', SeqVal b' k = Function.update (SeqVal a) m x k := by
        intro k hk
        by_cases hki : k = m
        · exact hbval k (Or.inr hki)
        · exact hbval k (Or.inl (hcov k (Finset.mem_erase.mpr ⟨hki, hk⟩)))
      rw [isUpdSeq_unique hb hb']
      exact ⟨hbseq, hbcov, sat_congr hagree⟩
    rw [pair_code_mem_TSet_sub hT]
    constructor
    · rintro ⟨-, -, hs⟩ x hx b _ hub
      obtain ⟨hbseq, hbcov, hiff⟩ := key x hx b hub
      exact (pair_code_mem_TSet_sub hT1).mpr ⟨hbseq, hbcov, hiff.mpr (sat_all.mp hs x hx)⟩
    · intro H
      refine ⟨ha, by simpa only [Fm.fv] using hcov, sat_all.mpr fun x hx => ?_⟩
      obtain ⟨b', hb', -, -, -⟩ := exists_updSeq ha m hx
      obtain ⟨hbseq, hbcov, hiff⟩ := key x hx b' hb'
      exact hiff.mp ((pair_code_mem_TSet_sub hT1).mp
        (H x hx b' (mem_Seqs.mpr hbseq) hb')).2.2

/-! ### Δ₀-definability of the partial satisfaction structures -/

theorem delta0_subCl : Delta0Def ({1, 2, 6} : Finset ℕ)
    (fun _ v => SubCl.{u} (v 6) (v 1) (v 2)) := by
  have p1 := (((delta0_tagPair 3 12 13 14 (by omega) (by omega)).imp
      ((Delta0Def.mem 13 2).and (Delta0Def.mem 14 2))).ball 14 1 (by omega)).ball 13 1 (by omega)
  have p2 := (((delta0_tagPair 4 12 13 14 (by omega) (by omega)).imp
      (Delta0Def.mem 14 2)).ball 14 1 (by omega)).ball 13 6 (by omega)
  have h := (p1.and p2).ball 12 2 (by omega)
  exact (h.congr (by
    intro D v _ _
    unfold SubCl
    simp (disch := omega) only [Function.update_self, Function.update_of_ne])).mono (by decide)

theorem delta0_tClause : Delta0Def ({1, 2, 3, 4, 5, 6} : Finset ℕ)
    (fun _ v => TClause.{u} (v 4) (v 5) (v 6) (v 1) (v 2) (v 3)) := by
  have hfv := delta0_funVal 3 12 13 (by omega) (by omega) (by omega)
  have c1 := (delta0_tagPair0 12).imp hfv.not
  have eqbody := ((delta0_valAt 13 14 16 (by omega) (by omega) (by omega)).and
      (((delta0_valAt 13 15 17 (by omega) (by omega) (by omega)).and
        (Delta0Def.eq 16 17)).bex 17 4 (by omega))).bex 16 4 (by omega)
  have membody := ((delta0_valAt 13 14 16 (by omega) (by omega) (by omega)).and
      (((delta0_valAt 13 15 17 (by omega) (by omega) (by omega)).and
        (Delta0Def.mem 16 17)).bex 17 4 (by omega))).bex 16 4 (by omega)
  have hdi := delta0_inDomZ 13 14 (by omega)
  have hdj := delta0_inDomZ 13 15 (by omega)
  have c2 := (((delta0_tagPair 1 12 14 15 (by omega) (by omega)).imp
      (hdi.imp (hdj.imp (hfv.iff eqbody)))).ball 15 6 (by omega)).ball 14 6 (by omega)
  have c3 := (((delta0_tagPair 2 12 14 15 (by omega) (by omega)).imp
      (hdi.imp (hdj.imp (hfv.iff membody)))).ball 15 6 (by omega)).ball 14 6 (by omega)
  have c4 := (((delta0_tagPair 3 12 14 15 (by omega) (by omega)).imp
      ((delta0_isAsn 1 6 4 14 13 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)).imp
        ((delta0_isAsn 1 6 4 15 13 (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega)).imp
        (hfv.iff ((delta0_funVal 3 14 13 (by omega) (by omega) (by omega)).imp
          (delta0_funVal 3 15 13 (by omega) (by omega) (by omega))))))).ball 15 1
        (by omega)).ball 14 1 (by omega)
  have allbody := (((delta0_isUpdSeq 13 14 16 18 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)).imp
      (delta0_funVal 3 15 18 (by omega) (by omega) (by omega))).ball 18 5 (by omega)).ball 16 4
      (by omega)
  have allguard := (((Delta0Def.eq 19 14).not.imp
      ((delta0_notFreeW 1 6 19 15 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)).not.imp (delta0_inDomZ 13 19 (by omega)))).ball 19 6 (by omega))
  have c5 := (((delta0_tagPair 4 12 14 15 (by omega) (by omega)).imp
      (allguard.imp (hfv.iff allbody))).ball 15 1 (by omega)).ball 14 6 (by omega)
  have h := ((c1.and (c2.and (c3.and (c4.and c5)))).ball 13 5 (by omega)).ball 12 2 (by omega)
  exact (h.congr (by
    intro D v _ _
    unfold TClause
    simp (disch := omega) only [Function.update_self, Function.update_of_ne])).mono (by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
        Finset.mem_union] at hk ⊢
      omega)

/-- Σ1-collection with two witness variables (`2` and `3`). -/
theorem collect3 (hθ : IsAdmissible θ) {s : Finset ℕ} {Q : Pred.{u}}
    (hQ : Delta0Def s Q) {v : ℕ → ZFSet.{u}}
    (hv : ∀ k ∈ s, k ≠ 2 → k ≠ 3 → k ≠ 0 → v k ∈ L θ) (hX : v 1 ∈ L θ)
    (h : ∀ x ∈ v 1, ∃ c ∈ L θ, ∃ t ∈ L θ,
      Q (· ∈ L θ) (Function.update (Function.update (Function.update v 0 x) 2 c) 3 t)) :
    ∃ b ∈ L θ, ∀ x ∈ v 1, ∃ c ∈ b, ∃ t ∈ b,
      Q (· ∈ L θ) (Function.update (Function.update (Function.update v 0 x) 2 c) 3 t) :=
  sigma1_collection hθ hQ [2, 3] 0 1 (by decide) (by simp) (by simp)
    (fun k hk hl h0 => hv k hk (by simp only [List.mem_cons] at hl; tauto)
      (by simp only [List.mem_cons] at hl; tauto) h0) hX h

private noncomputable def valT (x1 x4 x5 x6 x7 : ZFSet.{u}) : ℕ → ZFSet.{u} :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (fun _ => (∅ : ZFSet.{u})) 1 x1) 4 x4) 5 x5) 6 x6) 7 x7

private theorem hvT {θ : Ordinal.{u}} {x1 x4 x5 x6 x7 : ZFSet.{u}}
    (h1 : x1 ∈ L θ) (h4 : x4 ∈ L θ) (h5 : x5 ∈ L θ) (h6 : x6 ∈ L θ) (h7 : x7 ∈ L θ)
    (he : (∅ : ZFSet.{u}) ∈ L θ) : ∀ k : ℕ, valT x1 x4 x5 x6 x7 k ∈ L θ := by
  intro k
  simp only [valT, Function.update_apply]
  split_ifs <;> assumption

/-! ### The full truth set lies in `L θ` -/

theorem truthSet_mem_L (hθ : IsAdmissible θ) {A : ZFSet.{u}} (hA : A ∈ L θ) :
    TruthSet A ∈ L θ := by
  have hlim := hθ.isSuccLimit
  have he : (∅ : ZFSet.{u}) ∈ L θ := empty_mem_L_of_limit hlim
  have hS : Seqs A ∈ L θ := seqs_mem_L hθ hA
  have hLω : L Ordinal.omega0.{u} ∈ L θ := L_mem_L hθ.omega_lt
  have hω : ωZ.{u} ∈ L θ := hθ.omega_mem
  have hM : Delta0Def ({0, 1, 2, 3, 4, 5, 6} : Finset ℕ) (fun _ v =>
      SubCl.{u} (v 6) (v 1) (v 2) ∧ (TClause.{u} (v 4) (v 5) (v 6) (v 1) (v 2) (v 3) ∧
        (IsCodeW (v 1) (v 6) (v 0) → v 0 ∈ v 2))) :=
    (delta0_subCl.and (delta0_tClause.and
      ((delta0_isCodeW 1 6 0 (by omega) (by omega) (by omega)).imp
        (Delta0Def.mem 0 2)))).mono (by decide)
  obtain ⟨b, hb, hbmem⟩ := collect3 hθ hM
    (v := valT (L Ordinal.omega0.{u}) A (Seqs A) ωZ ∅)
    (fun k _ _ _ _ => hvT hLω hA hS hω he he k)
    (by simpa (disch := omega) only [valT, Function.update_self, Function.update_of_ne] using hLω)
    (by
      intro e hee
      simp (disch := omega) only [valT, Function.update_self, Function.update_of_ne] at hee ⊢
      by_cases hcode : IsCodeW (L Ordinal.omega0.{u}) ωZ e
      · obtain ⟨φ, rfl⟩ := (isCodeW_iff _).mp hcode
        exact ⟨Cs.{u} φ, Cs_mem_L hθ φ, TSet A φ, TSet_mem_L hθ hA φ,
          subCl_Cs φ, tClause_Cs φ, fun _ => code_mem_Cs φ⟩
      · refine ⟨∅, he, ∅, he, ?_, ?_, fun hc => absurd hc hcode⟩
        · intro x hx; exact absurd hx (ZFSet.notMem_empty x)
        · intro x hx; exact absurd hx (ZFSet.notMem_empty x))
  simp (disch := omega) only [valT, Function.update_self, Function.update_of_ne] at hbmem
  have hΨ : Delta0Def ({0, 1, 4, 5, 6, 7} : Finset ℕ) (fun _ v =>
      ∃ c ∈ v 7, ∃ t ∈ v 7, SubCl.{u} (v 6) (v 1) c ∧ (TClause.{u} (v 4) (v 5) (v 6) (v 1) c t ∧
        (∃ e ∈ v 1, ∃ a ∈ v 5, v 0 = ZFSet.pair e a ∧
          (IsCodeW (v 1) (v 6) e ∧ (IsAsn (v 1) (v 6) (v 4) e a ∧ (e ∈ c ∧ v 0 ∈ t)))))) := by
    have rest := (((delta0_isKPair 0 30 31 (by omega) (by omega)).and
      ((delta0_isCodeW 1 6 30 (by omega) (by omega) (by omega)).and
        ((delta0_isAsn 1 6 4 30 31 (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega)).and
        ((Delta0Def.mem 30 2).and (Delta0Def.mem 0 3))))).bex 31 5 (by omega)).bex 30 1
          (by omega)
    have h := ((delta0_subCl.and (delta0_tClause.and rest)).bex 3 7 (by omega)).bex 2 7 (by omega)
    exact (h.congr (by
      intro D v _ _
      simp (disch := omega) only [Function.update_self, Function.update_of_ne])).mono (by decide)
  have heq : TruthSet A = ZFSet.sep
      (fun z => ∃ c ∈ b, ∃ t ∈ b, SubCl.{u} ωZ (L Ordinal.omega0) c ∧
        (TClause.{u} A (Seqs A) ωZ (L Ordinal.omega0) c t ∧
          (∃ e ∈ L Ordinal.omega0.{u}, ∃ a ∈ Seqs A, z = ZFSet.pair e a ∧
            (IsCodeW (L Ordinal.omega0.{u}) ωZ e ∧
              (IsAsn (L Ordinal.omega0.{u}) ωZ A e a ∧ (e ∈ c ∧ z ∈ t))))))
      (kprodZ (L Ordinal.omega0.{u}) (Seqs A)) := by
    ext z
    rw [mem_TruthSet, ZFSet.mem_sep, mem_kprodZ]
    constructor
    · rintro ⟨φ, a, rfl, ha, hcov, hs⟩
      have hcode : IsCodeW (L Ordinal.omega0.{u}) ωZ (Fm.code.{u} φ) :=
        (isCodeW_iff _).mpr ⟨φ, rfl⟩
      obtain ⟨c, hc, t, ht, hsub, hcl, hin⟩ := hbmem (Fm.code.{u} φ) (Fm.code_mem_Lω φ)
      refine ⟨⟨_, Fm.code_mem_Lω φ, a, mem_Seqs.mpr ha, rfl⟩,
        c, hc, t, ht, hsub, hcl, _, Fm.code_mem_Lω φ, a, mem_Seqs.mpr ha, rfl, hcode,
        isAsn_code_iff.mpr ⟨ha, hcov⟩, hin hcode, ?_⟩
      exact (tClause_correct hsub hcl φ (hin hcode) a ha hcov).mpr hs
    · rintro ⟨-, c, hc, t, ht, hsub, hcl, e, hee, a, haS, rfl, hcode, hasn, hec, hzt⟩
      obtain ⟨φ, rfl⟩ := (isCodeW_iff _).mp hcode
      obtain ⟨ha, hcov⟩ := isAsn_code_iff.mp hasn
      exact ⟨φ, a, rfl, ha, hcov,
        (tClause_correct hsub hcl φ hec a ha hcov).mp hzt⟩
  rw [heq]
  exact sepL hθ hΨ (v := valT (L Ordinal.omega0.{u}) A (Seqs A) ωZ b)
    (fun k _ _ => hvT hLω hA hS hω hb he k) (kprod_mem_L hθ hLω hS) _
    (by intro z; simp (disch := omega) only [valT, Function.update_self, Function.update_of_ne])

/-! ### The satisfaction code for the truth set -/

theorem satCode_truthSet {A U : ZFSet.{u}} (hUtrans : U.IsTransitive)
    (hAU : A ∈ U) (hTU : TruthSet A ∈ U) (hωU : ωZ ∈ U)
    (hpucl : ∀ x ∈ U, ∀ y ∈ U, ({x, y} : ZFSet.{u}) ∈ U ∧ ZFSet.sUnion x ∈ U) :
    SatCode (L Ordinal.omega0) ωZ A U (TruthSet A) :=
  satCode_truthSet_of hUtrans hAU hTU hωU hpucl

/-! ### Admissible ordinals are closed under `ζ ↦ ζ + ω` -/

theorem natZ_zero : natZ.{u} 0 = ∅ := rfl

theorem natZ_succ (n : ℕ) : natZ.{u} (n + 1) = insert (natZ.{u} n) (natZ.{u} n) := rfl

/-- Iterated singletons over `c`. -/
noncomputable def nestZ (c : ZFSet.{u}) : ℕ → ZFSet.{u}
  | 0 => c
  | n + 1 => ({nestZ c n} : ZFSet.{u})

theorem rank_nestZ (c : ZFSet.{u}) : ∀ n : ℕ, (nestZ c n).rank = c.rank + (n : Ordinal.{u})
  | 0 => by show c.rank = _; simp
  | n + 1 => by
    show (({nestZ c n} : ZFSet.{u})).rank = c.rank + ((n + 1 : ℕ) : Ordinal.{u})
    rw [ZFSet.rank_singleton, rank_nestZ c n, Order.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
      add_assoc]

theorem nestZ_mem_L {θ : Ordinal.{u}} (hlim : Order.IsSuccLimit θ) {c : ZFSet.{u}} (hc : c ∈ L θ) :
    ∀ n : ℕ, nestZ c n ∈ L θ
  | 0 => hc
  | n + 1 => singleton_mem_L_of_limit hlim (nestZ_mem_L hlim hc n)

/-- The finite function `natZ m ↦ nestZ c m` for `m ≤ n`. -/
noncomputable def chainF (c : ZFSet.{u}) : ℕ → ZFSet.{u}
  | 0 => ({ZFSet.pair (natZ 0) (nestZ c 0)} : ZFSet.{u})
  | n + 1 => insert (ZFSet.pair (natZ (n + 1)) (nestZ c (n + 1))) (chainF c n)

/-- Its range. -/
noncomputable def chainR (c : ZFSet.{u}) : ℕ → ZFSet.{u}
  | 0 => ({nestZ c 0} : ZFSet.{u})
  | n + 1 => insert (nestZ c (n + 1)) (chainR c n)

theorem mem_chainF {c p : ZFSet.{u}} : ∀ {n : ℕ},
    p ∈ chainF c n ↔ ∃ m ≤ n, p = ZFSet.pair (natZ m) (nestZ c m)
  | 0 => by
    show p ∈ ({ZFSet.pair (natZ.{u} 0) (nestZ c 0)} : ZFSet.{u}) ↔ _
    rw [ZFSet.mem_singleton]
    exact ⟨fun h => ⟨0, le_rfl, h⟩, fun ⟨m, hm, h⟩ => by rwa [Nat.le_zero.mp hm] at h⟩
  | n + 1 => by
    show p ∈ insert (ZFSet.pair (natZ.{u} (n + 1)) (nestZ c (n + 1))) (chainF c n) ↔ _
    rw [ZFSet.mem_insert_iff, mem_chainF]
    constructor
    · rintro (rfl | ⟨m, hm, rfl⟩)
      · exact ⟨n + 1, le_rfl, rfl⟩
      · exact ⟨m, by omega, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      rcases Nat.eq_or_lt_of_le hm with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr ⟨m, by omega, rfl⟩

theorem mem_chainR {c x : ZFSet.{u}} : ∀ {n : ℕ},
    x ∈ chainR c n ↔ ∃ m ≤ n, x = nestZ c m
  | 0 => by
    show x ∈ ({nestZ c 0} : ZFSet.{u}) ↔ _
    rw [ZFSet.mem_singleton]
    exact ⟨fun h => ⟨0, le_rfl, h⟩, fun ⟨m, hm, h⟩ => by rwa [Nat.le_zero.mp hm] at h⟩
  | n + 1 => by
    show x ∈ insert (nestZ c (n + 1)) (chainR c n) ↔ _
    rw [ZFSet.mem_insert_iff, mem_chainR]
    constructor
    · rintro (rfl | ⟨m, hm, rfl⟩)
      · exact ⟨n + 1, le_rfl, rfl⟩
      · exact ⟨m, by omega, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      rcases Nat.eq_or_lt_of_le hm with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr ⟨m, by omega, rfl⟩

theorem chainF_mem_L {θ : Ordinal.{u}} (hlim : Order.IsSuccLimit θ) {c : ZFSet.{u}} (hc : c ∈ L θ)
    (hnat : ∀ n : ℕ, natZ.{u} n ∈ L θ) : ∀ n : ℕ, chainF c n ∈ L θ
  | 0 => singleton_mem_L_of_limit hlim
      (kpair_mem_L_of_limit hlim (hnat 0) (nestZ_mem_L hlim hc 0))
  | n + 1 => insert_mem_L_of_limit hlim
      (kpair_mem_L_of_limit hlim (hnat (n + 1)) (nestZ_mem_L hlim hc (n + 1)))
      (chainF_mem_L hlim hc hnat n)

theorem chainR_mem_L {θ : Ordinal.{u}} (hlim : Order.IsSuccLimit θ) {c : ZFSet.{u}} (hc : c ∈ L θ) :
    ∀ n : ℕ, chainR c n ∈ L θ
  | 0 => singleton_mem_L_of_limit hlim (nestZ_mem_L hlim hc 0)
  | n + 1 => insert_mem_L_of_limit hlim (nestZ_mem_L hlim hc (n + 1)) (chainR_mem_L hlim hc n)

theorem isFunc_chainF (c : ZFSet.{u}) (n : ℕ) : IsFunc (chainF c n) := by
  constructor
  · intro p hp
    obtain ⟨m, -, rfl⟩ := mem_chainF.mp hp
    exact ⟨_, _, rfl⟩
  · intro a b b' hb hb'
    obtain ⟨m, -, hm⟩ := mem_chainF.mp hb
    obtain ⟨m', -, hm'⟩ := mem_chainF.mp hb'
    rw [ZFSet.pair_inj] at hm hm'
    have : m = m' := natZ_injective (hm.1.symm.trans hm'.1)
    rw [hm.2, hm'.2, this]

theorem isRan_chainF (c : ZFSet.{u}) (n : ℕ) : IsRan (chainF c n) (chainR c n) := by
  intro x
  rw [mem_chainR]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨natZ m, mem_chainF.mpr ⟨m, hm, rfl⟩⟩
  · rintro ⟨a, ha⟩
    obtain ⟨m, hm, hp⟩ := mem_chainF.mp ha
    rw [ZFSet.pair_inj] at hp
    exact ⟨m, hm, hp.2⟩

theorem isDom_chainF (c : ZFSet.{u}) (n : ℕ) : IsDom (chainF c n) (natZ (n + 1)) := by
  intro a
  constructor
  · intro ha
    obtain ⟨m, hm, rfl⟩ := mem_natZ_iff.mp ha
    exact ⟨nestZ c m, mem_chainF.mpr ⟨m, by omega, rfl⟩⟩
  · rintro ⟨b, hb⟩
    obtain ⟨m, hm, hp⟩ := mem_chainF.mp hb
    rw [ZFSet.pair_inj] at hp
    rw [hp.1]
    exact natZ_mem_natZ_iff.mpr (by omega)

theorem add_omega0_lt (hθ : IsAdmissible θ) {ζ : Ordinal.{u}} (hζ : ζ < θ) :
    ζ + Ordinal.omega0 < θ := by
  have hlim := hθ.isSuccLimit
  have he : (∅ : ZFSet.{u}) ∈ L θ := empty_mem_L_of_limit hlim
  have hω : ωZ.{u} ∈ L θ := hθ.omega_mem
  have hnat : ∀ n : ℕ, natZ.{u} n ∈ L θ := fun n => natZ_mem_L hθ.omega_lt n
  set c : ZFSet.{u} := ζ.toZFSet with hcdef
  have hcL : c ∈ L θ := (toZFSet_mem_L_iff θ ζ).mpr hζ
  have hcrank : c.rank = ζ := Ordinal.rank_toZFSet ζ
  have hQ : Delta0Def ({0, 1, 2, 3, 4, 5} : Finset ℕ) (fun _ v =>
      IsFunc (v 2) ∧ (IsRan (v 2) (v 3) ∧ (ZFSet.pair (v 5) (v 4) ∈ v 2 ∧
        ∃ d ∈ v 1, IsDom (v 2) d ∧ (v 0 ∈ d ∧
          ∀ m ∈ d, ∀ s ∈ d, ∀ w ∈ v 3, ∀ w' ∈ v 3,
            ((s = insert m m ∧ ZFSet.pair m w ∈ v 2) ∧ ZFSet.pair s w' ∈ v 2) →
              w' = ({w} : ZFSet.{u}))))) := by
    have step := ((((((delta0_isSucc 8 7 (by omega)).and
        (delta0_funVal 2 7 9 (by omega) (by omega) (by omega))).and
        (delta0_funVal 2 8 10 (by omega) (by omega) (by omega))).imp
        (delta0_isSingleton 10 9 (by omega))).ball 10 3 (by omega)).ball 9 3
        (by omega)).ball 8 6 (by omega)
    have step2 := step.ball 7 6 (by omega)
    have dpart := ((delta0_isDom 2 6 (by omega)).and
      ((Delta0Def.mem 0 6).and step2)).bex 6 1 (by omega)
    have h := (delta0_isFunc 2).and ((delta0_isRan 2 3 (by omega)).and
      ((delta0_funVal 2 5 4 (by omega) (by omega) (by omega)).and dpart))
    exact (h.congr (by
      intro D v _ _
      simp (disch := omega) only [Function.update_self, Function.update_of_ne])).mono (by decide)
  obtain ⟨b, hb, hbmem⟩ := collect3 hθ hQ (v := valT ωZ.{u} c ∅ ∅ ∅)
    (fun k _ _ _ _ => hvT hω hcL he he he he k)
    (by simpa (disch := omega) only [valT, Function.update_self, Function.update_of_ne] using hω)
    (by
      intro nn hnn
      simp (disch := omega) only [valT, Function.update_self, Function.update_of_ne] at hnn ⊢
      obtain ⟨k, rfl⟩ := mem_ωZ_iff.mp hnn
      refine ⟨chainF c k, chainF_mem_L hlim hcL hnat k, chainR c k, chainR_mem_L hlim hcL k,
        isFunc_chainF c k, isRan_chainF c k, mem_chainF.mpr ⟨0, Nat.zero_le k, rfl⟩,
        natZ (k + 1), natZ_mem_ωZ (k + 1), isDom_chainF c k,
        natZ_mem_natZ_iff.mpr (by omega), ?_⟩
      rintro m hm s hs w hw w' hw' ⟨⟨hsucc, hmw⟩, hsw⟩
      obtain ⟨pm, -, rfl⟩ := mem_natZ_iff.mp hm
      obtain ⟨qs, -, rfl⟩ := mem_natZ_iff.mp hs
      obtain ⟨mw, -, rfl⟩ := mem_chainR.mp hw
      obtain ⟨mw2, -, rfl⟩ := mem_chainR.mp hw'
      have hq : qs = pm + 1 := natZ_injective hsucc
      obtain ⟨m1, -, h1⟩ := mem_chainF.mp hmw
      rw [ZFSet.pair_inj] at h1
      have hpm1 : pm = m1 := natZ_injective h1.1
      obtain ⟨m2, -, h2⟩ := mem_chainF.mp hsw
      rw [ZFSet.pair_inj] at h2
      have hqs2 : qs = m2 := natZ_injective h2.1
      rw [h2.2, h1.2, ← hqs2, ← hpm1, hq]
      rfl)
  simp (disch := omega) only [valT, Function.update_self, Function.update_of_ne] at hbmem
  set V : ZFSet.{u} := ZFSet.sUnion (ZFSet.sUnion (ZFSet.sUnion b)) with hVdef
  have hVL : V ∈ L θ := sUnion_mem_L_of_limit hlim (sUnion_mem_L_of_limit hlim
    (sUnion_mem_L_of_limit hlim hb))
  have hnest : ∀ k : ℕ, nestZ c k ∈ V := by
    intro k
    obtain ⟨Y, hY, R, hR, hf, hr, hbase, d, hd, hdom, hkd, hstep⟩ :=
      hbmem (natZ k) (natZ_mem_ωZ k)
    obtain ⟨l, rfl⟩ := mem_ωZ_iff.mp hd
    have hkl : k < l := natZ_mem_natZ_iff.mp hkd
    have key : ∀ m, m < l → ZFSet.pair (natZ m) (nestZ c m) ∈ Y := by
      intro m
      induction m with
      | zero => intro _; exact hbase
      | succ m ih =>
        intro hml
        have hm : m < l := by omega
        have h1 := ih hm
        obtain ⟨w', hw'⟩ := (hdom (natZ (m + 1))).mp (natZ_mem_natZ_iff.mpr hml)
        have hwR : nestZ c m ∈ R := (hr _).mpr ⟨natZ m, h1⟩
        have hw'R : w' ∈ R := (hr _).mpr ⟨natZ (m + 1), hw'⟩
        have hEq := hstep (natZ m) (natZ_mem_natZ_iff.mpr hm) (natZ (m + 1))
          (natZ_mem_natZ_iff.mpr hml) (nestZ c m) hwR w' hw'R ⟨⟨rfl, h1⟩, hw'⟩
        show ZFSet.pair (natZ (m + 1)) ({nestZ c m} : ZFSet.{u}) ∈ Y
        rw [← hEq]
        exact hw'
    refine ZFSet.mem_sUnion.mpr ⟨({natZ k, nestZ c k} : ZFSet.{u}), ?_, mem_upair_right _ _⟩
    refine ZFSet.mem_sUnion.mpr ⟨ZFSet.pair (natZ k) (nestZ c k), ?_, upair_mem_pair _ _⟩
    exact ZFSet.mem_sUnion.mpr ⟨Y, hY, key k hkl⟩
  have hlt : ∀ k : ℕ, ζ + (k : Ordinal.{u}) < V.rank := by
    intro k
    have h := ZFSet.rank_lt_of_mem (hnest k)
    rwa [rank_nestZ, hcrank] at h
  by_contra hcon
  have hcon' : θ ≤ ζ + Ordinal.omega0 := not_lt.mp hcon
  have hVlt : V.rank < ζ + Ordinal.omega0 := lt_of_lt_of_le (rank_lt_of_mem_L hVL) hcon'
  have hζle : ζ ≤ V.rank := le_of_lt (by simpa using hlt 0)
  have hsub : V.rank - ζ < Ordinal.omega0 := Ordinal.sub_lt_of_lt_add hVlt Ordinal.omega0_pos
  obtain ⟨m, hm⟩ := Ordinal.lt_omega0.mp hsub
  have hVr : V.rank = ζ + (m : Ordinal.{u}) := by
    rw [← hm, Ordinal.add_sub_cancel_of_le hζle]
  rw [hVr] at hlt
  exact absurd (hlt m) (lt_irrefl _)

theorem exists_limit_between (hθ : IsAdmissible θ) {ζ : Ordinal.{u}} (hζ : ζ < θ) :
    ∃ ξ : Ordinal.{u}, Order.IsSuccLimit ξ ∧ ζ ≤ ξ ∧ ξ < θ :=
  ⟨ζ + Ordinal.omega0, Ordinal.isSuccLimit_add _ Ordinal.isSuccLimit_omega0,
    le_self_add, add_omega0_lt hθ hζ⟩


/-! ### Lemma 10.4(2): the transitive closure `TC(X)` -/

/-- One step of the recursion of Lemma 10.4(2): `y = x ∪ ⋃ x`. -/
def IsTCStep (x y : ZFSet.{u}) : Prop := y = x ∪ ZFSet.sUnion x

theorem isTCStep_iff_bounded (x y : ZFSet.{u}) :
    IsTCStep x y ↔ (∀ z ∈ y, z ∈ x ∨ ∃ u ∈ x, z ∈ u) ∧ (∀ z ∈ x, z ∈ y) ∧
      (∀ u ∈ x, ∀ z ∈ u, z ∈ y) := by
  unfold IsTCStep
  constructor
  · rintro rfl
    refine ⟨fun z hz => ?_, fun z hz => ZFSet.mem_union.mpr (Or.inl hz),
      fun u hu z hz => ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_sUnion.mpr ⟨u, hu, hz⟩))⟩
    rcases ZFSet.mem_union.mp hz with h | h
    · exact Or.inl h
    · exact Or.inr (ZFSet.mem_sUnion.mp h)
  · rintro ⟨h1, h2, h3⟩
    ext z
    rw [ZFSet.mem_union]
    constructor
    · intro hz
      rcases h1 z hz with h | ⟨u, hu, hzu⟩
      · exact Or.inl h
      · exact Or.inr (ZFSet.mem_sUnion.mpr ⟨u, hu, hzu⟩)
    · rintro (h | h)
      · exact h2 z h
      · obtain ⟨u, hu, hzu⟩ := ZFSet.mem_sUnion.mp h
        exact h3 u hu z hzu

theorem delta0_isTCStep (x y : ℕ) :
    Delta0Def {x, y} (fun _ v => IsTCStep (v x) (v y)) := by
  set m := x + y + 1 with hm
  -- `z := m`, `u := m + 1`
  have a1 := (((Delta0Def.mem m x).or
    ((Delta0Def.mem m (m + 1)).bex (m + 1) x (by omega))).ball m y (by omega))
  have a2 := (Delta0Def.mem m y).ball m x (by omega)
  have a3 := ((Delta0Def.mem m y).ball m (m + 1) (by omega)).ball (m + 1) x (by omega)
  refine ((a1.and (a2.and a3)).congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    exact (isTCStep_iff_bounded (v x) (v y)).symm
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union] at hk ⊢
    omega

/-- The stages `R₀ = X`, `R_{n+1} = R_n ∪ ⋃ R_n` of Lemma 10.4(2). -/
noncomputable def tcSeq (X : ZFSet.{u}) : ℕ → ZFSet.{u}
  | 0 => X
  | n + 1 => tcSeq X n ∪ ZFSet.sUnion (tcSeq X n)

theorem tcSeq_zero (X : ZFSet.{u}) : tcSeq X 0 = X := rfl

theorem tcSeq_succ (X : ZFSet.{u}) (n : ℕ) :
    tcSeq X (n + 1) = tcSeq X n ∪ ZFSet.sUnion (tcSeq X n) := rfl

theorem tcSeq_mem_L {θ : Ordinal.{u}} (hlim : Order.IsSuccLimit θ) {X : ZFSet.{u}}
    (hX : X ∈ L θ) : ∀ n : ℕ, tcSeq X n ∈ L θ
  | 0 => hX
  | n + 1 => union_mem_L_of_limit hlim (tcSeq_mem_L hlim hX n)
      (sUnion_mem_L_of_limit hlim (tcSeq_mem_L hlim hX n))

theorem tcSeq_subset_succ (X : ZFSet.{u}) (n : ℕ) : ∀ z ∈ tcSeq X n, z ∈ tcSeq X (n + 1) :=
  fun _ hz => ZFSet.mem_union.mpr (Or.inl hz)

theorem tcSeq_mono (X : ZFSet.{u}) {m n : ℕ} (h : m ≤ n) : ∀ z ∈ tcSeq X m, z ∈ tcSeq X n := by
  induction n with
  | zero => intro z hz; rwa [Nat.le_zero.mp h] at hz
  | succ n ih =>
    intro z hz
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with hlt | rfl
    · exact tcSeq_subset_succ X n z (ih (by omega) z hz)
    · exact hz

/-- The finite function `natZ m ↦ tcSeq X m` for `m ≤ n`. -/
noncomputable def tcF (X : ZFSet.{u}) : ℕ → ZFSet.{u}
  | 0 => ({ZFSet.pair (natZ 0) (tcSeq X 0)} : ZFSet.{u})
  | n + 1 => insert (ZFSet.pair (natZ (n + 1)) (tcSeq X (n + 1))) (tcF X n)

/-- Its range. -/
noncomputable def tcR (X : ZFSet.{u}) : ℕ → ZFSet.{u}
  | 0 => ({tcSeq X 0} : ZFSet.{u})
  | n + 1 => insert (tcSeq X (n + 1)) (tcR X n)

theorem mem_tcF {X p : ZFSet.{u}} : ∀ {n : ℕ},
    p ∈ tcF X n ↔ ∃ m ≤ n, p = ZFSet.pair (natZ m) (tcSeq X m)
  | 0 => by
    show p ∈ ({ZFSet.pair (natZ.{u} 0) (tcSeq X 0)} : ZFSet.{u}) ↔ _
    rw [ZFSet.mem_singleton]
    exact ⟨fun h => ⟨0, le_rfl, h⟩, fun ⟨m, hm, h⟩ => by rwa [Nat.le_zero.mp hm] at h⟩
  | n + 1 => by
    show p ∈ insert (ZFSet.pair (natZ.{u} (n + 1)) (tcSeq X (n + 1))) (tcF X n) ↔ _
    rw [ZFSet.mem_insert_iff, mem_tcF]
    constructor
    · rintro (rfl | ⟨m, hm, rfl⟩)
      · exact ⟨n + 1, le_rfl, rfl⟩
      · exact ⟨m, by omega, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      rcases Nat.eq_or_lt_of_le hm with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr ⟨m, by omega, rfl⟩

theorem mem_tcR {X z : ZFSet.{u}} : ∀ {n : ℕ}, z ∈ tcR X n ↔ ∃ m ≤ n, z = tcSeq X m
  | 0 => by
    show z ∈ ({tcSeq X 0} : ZFSet.{u}) ↔ _
    rw [ZFSet.mem_singleton]
    exact ⟨fun h => ⟨0, le_rfl, h⟩, fun ⟨m, hm, h⟩ => by rwa [Nat.le_zero.mp hm] at h⟩
  | n + 1 => by
    show z ∈ insert (tcSeq X (n + 1)) (tcR X n) ↔ _
    rw [ZFSet.mem_insert_iff, mem_tcR]
    constructor
    · rintro (rfl | ⟨m, hm, rfl⟩)
      · exact ⟨n + 1, le_rfl, rfl⟩
      · exact ⟨m, by omega, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      rcases Nat.eq_or_lt_of_le hm with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr ⟨m, by omega, rfl⟩

theorem tcF_mem_L {θ : Ordinal.{u}} (hlim : Order.IsSuccLimit θ) {X : ZFSet.{u}} (hX : X ∈ L θ)
    (hnat : ∀ n : ℕ, natZ.{u} n ∈ L θ) : ∀ n : ℕ, tcF X n ∈ L θ
  | 0 => singleton_mem_L_of_limit hlim
      (kpair_mem_L_of_limit hlim (hnat 0) (tcSeq_mem_L hlim hX 0))
  | n + 1 => insert_mem_L_of_limit hlim
      (kpair_mem_L_of_limit hlim (hnat (n + 1)) (tcSeq_mem_L hlim hX (n + 1)))
      (tcF_mem_L hlim hX hnat n)

theorem tcR_mem_L {θ : Ordinal.{u}} (hlim : Order.IsSuccLimit θ) {X : ZFSet.{u}} (hX : X ∈ L θ) :
    ∀ n : ℕ, tcR X n ∈ L θ
  | 0 => singleton_mem_L_of_limit hlim (tcSeq_mem_L hlim hX 0)
  | n + 1 => insert_mem_L_of_limit hlim (tcSeq_mem_L hlim hX (n + 1)) (tcR_mem_L hlim hX n)

theorem isFunc_tcF (X : ZFSet.{u}) (n : ℕ) : IsFunc (tcF X n) := by
  constructor
  · intro p hp
    obtain ⟨m, -, rfl⟩ := mem_tcF.mp hp
    exact ⟨_, _, rfl⟩
  · intro a b b' hb hb'
    obtain ⟨m, -, hm⟩ := mem_tcF.mp hb
    obtain ⟨m', -, hm'⟩ := mem_tcF.mp hb'
    rw [ZFSet.pair_inj] at hm hm'
    have : m = m' := natZ_injective (hm.1.symm.trans hm'.1)
    rw [hm.2, hm'.2, this]

theorem isRan_tcF (X : ZFSet.{u}) (n : ℕ) : IsRan (tcF X n) (tcR X n) := by
  intro z
  rw [mem_tcR]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨natZ m, mem_tcF.mpr ⟨m, hm, rfl⟩⟩
  · rintro ⟨a, ha⟩
    obtain ⟨m, hm, hp⟩ := mem_tcF.mp ha
    rw [ZFSet.pair_inj] at hp
    exact ⟨m, hm, hp.2⟩

theorem isDom_tcF (X : ZFSet.{u}) (n : ℕ) : IsDom (tcF X n) (natZ (n + 1)) := by
  intro a
  constructor
  · intro ha
    obtain ⟨m, hm, rfl⟩ := mem_natZ_iff.mp ha
    exact ⟨tcSeq X m, mem_tcF.mpr ⟨m, by omega, rfl⟩⟩
  · rintro ⟨b, hb⟩
    obtain ⟨m, hm, hp⟩ := mem_tcF.mp hb
    rw [ZFSet.pair_inj] at hp
    rw [hp.1]
    exact natZ_mem_natZ_iff.mpr (by omega)

/-- **Lemma 10.4(2)**: every set `X` is contained in a least transitive set `TC(X)`.
(Semantic form: inside `L θ` for an admissible `θ`.) -/
theorem exists_tc {θ : Ordinal.{u}} (hθ : IsAdmissible θ) {X : ZFSet.{u}} (hX : X ∈ L θ) :
    ∃ T ∈ L θ, X ⊆ T ∧ T.IsTransitive ∧
      ∀ Y : ZFSet.{u}, X ⊆ Y → Y.IsTransitive → T ⊆ Y := by
  have hlim := hθ.isSuccLimit
  have he : (∅ : ZFSet.{u}) ∈ L θ := empty_mem_L_of_limit hlim
  have hω : ωZ.{u} ∈ L θ := hθ.omega_mem
  have hnat : ∀ n : ℕ, natZ.{u} n ∈ L θ := fun n => natZ_mem_L hθ.omega_lt n
  -- the Δ₀ description of "`Y` is a chain of stages of length `d`, with range `R`"
  have hQ : Delta0Def ({0, 1, 2, 3, 4, 5} : Finset ℕ) (fun _ v =>
      IsFunc (v 2) ∧ (IsRan (v 2) (v 3) ∧ (ZFSet.pair (v 5) (v 4) ∈ v 2 ∧
        ∃ d ∈ v 1, IsDom (v 2) d ∧ (v 0 ∈ d ∧
          ∀ m ∈ d, ∀ s ∈ d, ∀ w ∈ v 3, ∀ w' ∈ v 3,
            ((s = insert m m ∧ ZFSet.pair m w ∈ v 2) ∧ ZFSet.pair s w' ∈ v 2) →
              IsTCStep w w')))) := by
    have step := ((((((delta0_isSucc 8 7 (by omega)).and
        (delta0_funVal 2 7 9 (by omega) (by omega) (by omega))).and
        (delta0_funVal 2 8 10 (by omega) (by omega) (by omega))).imp
        (delta0_isTCStep 9 10)).ball 10 3 (by omega)).ball 9 3
        (by omega)).ball 8 6 (by omega)
    have step2 := step.ball 7 6 (by omega)
    have dpart := ((delta0_isDom 2 6 (by omega)).and
      ((Delta0Def.mem 0 6).and step2)).bex 6 1 (by omega)
    have h := (delta0_isFunc 2).and ((delta0_isRan 2 3 (by omega)).and
      ((delta0_funVal 2 5 4 (by omega) (by omega) (by omega)).and dpart))
    exact (h.congr (by
      intro D v _ _
      simp (disch := omega) only [Function.update_self, Function.update_of_ne])).mono (by decide)
  obtain ⟨b, hb, hbmem⟩ := collect3 hθ hQ (v := valT ωZ.{u} X ∅ ∅ ∅)
    (fun k _ _ _ _ => hvT hω hX he he he he k)
    (by simpa (disch := omega) only [valT, Function.update_self, Function.update_of_ne] using hω)
    (by
      intro nn hnn
      simp (disch := omega) only [valT, Function.update_self, Function.update_of_ne] at hnn ⊢
      obtain ⟨k, rfl⟩ := mem_ωZ_iff.mp hnn
      refine ⟨tcF X k, tcF_mem_L hlim hX hnat k, tcR X k, tcR_mem_L hlim hX k,
        isFunc_tcF X k, isRan_tcF X k, mem_tcF.mpr ⟨0, Nat.zero_le k, rfl⟩,
        natZ (k + 1), natZ_mem_ωZ (k + 1), isDom_tcF X k,
        natZ_mem_natZ_iff.mpr (by omega), ?_⟩
      rintro m hm s hs w hw w' hw' ⟨⟨hsucc, hmw⟩, hsw⟩
      obtain ⟨pm, -, rfl⟩ := mem_natZ_iff.mp hm
      obtain ⟨qs, -, rfl⟩ := mem_natZ_iff.mp hs
      obtain ⟨mw, -, rfl⟩ := mem_tcR.mp hw
      obtain ⟨mw2, -, rfl⟩ := mem_tcR.mp hw'
      have hq : qs = pm + 1 := natZ_injective hsucc
      obtain ⟨m1, -, h1⟩ := mem_tcF.mp hmw
      rw [ZFSet.pair_inj] at h1
      have hpm1 : pm = m1 := natZ_injective h1.1
      obtain ⟨m2, -, h2⟩ := mem_tcF.mp hsw
      rw [ZFSet.pair_inj] at h2
      have hqs2 : qs = m2 := natZ_injective h2.1
      rw [h2.2, h1.2, ← hqs2, ← hpm1, hq]
      rfl)
  simp (disch := omega) only [valT, Function.update_self, Function.update_of_ne] at hbmem
  -- every chain in `b` computes the stages
  have hchainval : ∀ Y R : ZFSet.{u}, ∀ l : ℕ, IsFunc Y → IsRan Y R →
      ZFSet.pair (natZ.{u} 0) X ∈ Y → IsDom Y (natZ.{u} l) →
      (∀ m ∈ natZ.{u} l, ∀ s ∈ natZ.{u} l, ∀ w ∈ R, ∀ w' ∈ R,
        ((s = insert m m ∧ ZFSet.pair m w ∈ Y) ∧ ZFSet.pair s w' ∈ Y) → IsTCStep w w') →
      ∀ m, m < l → ZFSet.pair (natZ.{u} m) (tcSeq X m) ∈ Y := by
    intro Y R l hf hr hbase hdom hstep m
    induction m with
    | zero => intro _; exact hbase
    | succ m ih =>
      intro hml
      have hm : m < l := by omega
      have h1 := ih hm
      obtain ⟨w', hw'⟩ := (hdom (natZ (m + 1))).mp (natZ_mem_natZ_iff.mpr hml)
      have hwR : tcSeq X m ∈ R := (hr _).mpr ⟨natZ m, h1⟩
      have hw'R : w' ∈ R := (hr _).mpr ⟨natZ (m + 1), hw'⟩
      have hEq := hstep (natZ m) (natZ_mem_natZ_iff.mpr hm) (natZ (m + 1))
        (natZ_mem_natZ_iff.mpr hml) (tcSeq X m) hwR w' hw'R ⟨⟨rfl, h1⟩, hw'⟩
      rw [tcSeq_succ, ← hEq]
      exact hw'
  -- the Δ₀ condition picking out the elements of the stages
  have hC : Delta0Def ({0, 1, 2, 3, 4} : Finset ℕ) (fun _ v =>
      ∃ Y ∈ v 1, ∃ R ∈ v 1, IsFunc Y ∧ (IsRan Y R ∧ (ZFSet.pair (v 4) (v 3) ∈ Y ∧
        ∃ d ∈ v 2, IsDom Y d ∧
          ((∀ m ∈ d, ∀ s ∈ d, ∀ w ∈ R, ∀ w' ∈ R,
            ((s = insert m m ∧ ZFSet.pair m w ∈ Y) ∧ ZFSet.pair s w' ∈ Y) → IsTCStep w w') ∧
            ∃ w ∈ R, v 0 ∈ w)))) := by
    have step := ((((((delta0_isSucc 9 8 (by omega)).and
        (delta0_funVal 5 8 10 (by omega) (by omega) (by omega))).and
        (delta0_funVal 5 9 11 (by omega) (by omega) (by omega))).imp
        (delta0_isTCStep 10 11)).ball 11 6 (by omega)).ball 10 6
        (by omega)).ball 9 7 (by omega)
    have step2 := step.ball 8 7 (by omega)
    have last := (Delta0Def.mem 0 12).bex 12 6 (by omega)
    have dpart := ((delta0_isDom 5 7 (by omega)).and (step2.and last)).bex 7 2 (by omega)
    have body := (delta0_isFunc 5).and ((delta0_isRan 5 6 (by omega)).and
      ((delta0_funVal 5 4 3 (by omega) (by omega) (by omega)).and dpart))
    have h := (body.bex 6 1 (by omega)).bex 5 1 (by omega)
    exact (h.congr (by
      intro D v _ _
      simp (disch := omega) only [Function.update_self, Function.update_of_ne])).mono (by decide)
  set V : ZFSet.{u} := ZFSet.sUnion (ZFSet.sUnion (ZFSet.sUnion b)) with hVdef
  have hVL : V ∈ L θ := sUnion_mem_L_of_limit hlim (sUnion_mem_L_of_limit hlim
    (sUnion_mem_L_of_limit hlim hb))
  have hstageV : ∀ k : ℕ, tcSeq X k ∈ V := by
    intro k
    obtain ⟨Y, hY, R, hR, hf, hr, hbase, d, hd, hdom, hkd, hstep⟩ :=
      hbmem (natZ k) (natZ_mem_ωZ k)
    obtain ⟨l, rfl⟩ := mem_ωZ_iff.mp hd
    have hkl : k < l := natZ_mem_natZ_iff.mp hkd
    have key := hchainval Y R l hf hr hbase hdom hstep k hkl
    refine ZFSet.mem_sUnion.mpr ⟨({natZ k, tcSeq X k} : ZFSet.{u}), ?_, mem_upair_right _ _⟩
    refine ZFSet.mem_sUnion.mpr ⟨ZFSet.pair (natZ k) (tcSeq X k), ?_, upair_mem_pair _ _⟩
    exact ZFSet.mem_sUnion.mpr ⟨Y, hY, key⟩
  -- the transitive closure itself
  set P : ZFSet.{u} → Prop := fun z => ∃ k : ℕ, z ∈ tcSeq X k with hPdef
  have hchar : ∀ z : ZFSet.{u},
      (∃ Y ∈ b, ∃ R ∈ b, IsFunc Y ∧ (IsRan Y R ∧ (ZFSet.pair (∅ : ZFSet.{u}) X ∈ Y ∧
        ∃ d ∈ ωZ.{u}, IsDom Y d ∧
          ((∀ m ∈ d, ∀ s ∈ d, ∀ w ∈ R, ∀ w' ∈ R,
            ((s = insert m m ∧ ZFSet.pair m w ∈ Y) ∧ ZFSet.pair s w' ∈ Y) → IsTCStep w w') ∧
            ∃ w ∈ R, z ∈ w)))) ↔ P z := by
    intro z
    constructor
    · rintro ⟨Y, hY, R, hR, hf, hr, hbase, d, hd, hdom, hstep, w, hw, hzw⟩
      obtain ⟨l, rfl⟩ := mem_ωZ_iff.mp hd
      obtain ⟨a, ha⟩ := (hr w).mp hw
      have had : a ∈ natZ.{u} l := (hdom a).mpr ⟨w, ha⟩
      obtain ⟨m, hml, rfl⟩ := mem_natZ_iff.mp had
      have := hchainval Y R l hf hr hbase hdom hstep m hml
      rw [hf.2 _ w (tcSeq X m) ha this] at hzw
      exact ⟨m, hzw⟩
    · rintro ⟨k, hzk⟩
      obtain ⟨Y, hY, R, hR, hf, hr, hbase, d, hd, hdom, hkd, hstep⟩ :=
        hbmem (natZ k) (natZ_mem_ωZ k)
      obtain ⟨l, rfl⟩ := mem_ωZ_iff.mp hd
      have hkl : k < l := natZ_mem_natZ_iff.mp hkd
      have key := hchainval Y R l hf hr hbase hdom hstep k hkl
      exact ⟨Y, hY, R, hR, hf, hr, hbase, natZ l, natZ_mem_ωZ l, hdom, hstep,
        tcSeq X k, (hr _).mpr ⟨natZ k, key⟩, hzk⟩
  have hVUL : ZFSet.sUnion V ∈ L θ := sUnion_mem_L_of_limit hlim hVL
  have hTL : ZFSet.sep P (ZFSet.sUnion V) ∈ L θ := by
    refine sepL hθ hC (v := Function.update (Function.update (Function.update
      (Function.update (fun _ => (∅ : ZFSet.{u})) 1 b) 2 ωZ.{u}) 3 X) 4 ∅) ?_ hVUL P ?_
    · intro k hk hk0
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      have : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · simpa (disch := omega) only [Function.update_self, Function.update_of_ne] using hb
      · simpa (disch := omega) only [Function.update_self, Function.update_of_ne] using hω
      · simpa (disch := omega) only [Function.update_self, Function.update_of_ne] using hX
      · simpa (disch := omega) only [Function.update_self, Function.update_of_ne] using he
    · intro z
      simp (disch := omega) only [Function.update_self, Function.update_of_ne]
      exact hchar z
  refine ⟨ZFSet.sep P (ZFSet.sUnion V), hTL, ?_, ?_, ?_⟩
  · intro z hz
    exact ZFSet.mem_sep.mpr ⟨ZFSet.mem_sUnion.mpr ⟨tcSeq X 0, hstageV 0, hz⟩, 0, hz⟩
  · intro w hw z hzw
    obtain ⟨-, k, hwk⟩ := ZFSet.mem_sep.mp hw
    have hzk : z ∈ tcSeq X (k + 1) :=
      ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_sUnion.mpr ⟨w, hwk, hzw⟩))
    exact ZFSet.mem_sep.mpr
      ⟨ZFSet.mem_sUnion.mpr ⟨tcSeq X (k + 1), hstageV (k + 1), hzk⟩, k + 1, hzk⟩
  · intro Y hXY hYtr z hz
    obtain ⟨-, k, hzk⟩ := ZFSet.mem_sep.mp hz
    have hsub : ∀ n : ℕ, ∀ x ∈ tcSeq X n, x ∈ Y := by
      intro n
      induction n with
      | zero => intro x hx; exact hXY hx
      | succ n ih =>
        intro x hx
        rcases ZFSet.mem_union.mp hx with h | h
        · exact ih x h
        · obtain ⟨u, hu, hxu⟩ := ZFSet.mem_sUnion.mp h
          exact hYtr.subset_of_mem (ih u hu) hxu
    exact hsub k z hzk

/-! ### Lemma 10.4(3): a transitive, pair- and union-closed superset -/

/-- **Lemma 10.4(3)**: for every set `X` there is a set `U` with `X ⊆ U`, `U` transitive and
`PUCl(U)`.  (Semantic form: inside `L θ` for an admissible `θ`.) -/
theorem exists_puCl_superset {θ : Ordinal.{u}} (hθ : IsAdmissible θ) {X : ZFSet.{u}}
    (hX : X ∈ L θ) : ∃ U ∈ L θ, X ⊆ U ∧ U.IsTransitive ∧ PUCl U := by
  have hlim := hθ.isSuccLimit
  obtain ⟨ζ, hζ, hXζ⟩ := (mem_L_limit hlim).mp hX
  obtain ⟨ξ, hξlim, hξge, hξlt⟩ := exists_limit_between hθ hζ
  refine ⟨L ξ, L_mem_L hξlt, fun z hz => (L_transitive ξ).subset_of_mem (L_mono hξge hXζ) hz,
    L_transitive ξ, fun x hx y hy => ?_⟩
  exact ⟨pair_mem_L_of_limit hξlim hx hy, sUnion_mem_L_of_limit hξlim hx⟩

/-! ### Lemma 10.5(1): satisfaction codes exist inside an admissible `L θ` -/

theorem satCode_exists_in_L {θ : Ordinal.{u}} (hθ : IsAdmissible θ) {A : ZFSet.{u}}
    (hA : A ∈ L θ) :
    ∃ U ∈ L θ, ∃ T ∈ L θ, SatCode (L Ordinal.omega0) ωZ A U T := by
  have hlim := hθ.isSuccLimit
  have hT : TruthSet A ∈ L θ := truthSet_mem_L hθ hA
  have hω : ωZ.{u} ∈ L θ := hθ.omega_mem
  -- Lemma 10.4(3) applied to `{A, ω, T}`, exactly as in the paper's proof of Lemma 10.5(1)
  have hXL : (insert A (insert ωZ.{u} (insert (TruthSet A) (∅ : ZFSet.{u})))) ∈ L θ :=
    insert_mem_L_of_limit hlim hA
      (insert_mem_L_of_limit hlim hω
        (insert_mem_L_of_limit hlim hT (empty_mem_L_of_limit hlim)))
  obtain ⟨U, hUL, hXU, hUtrans, hUpucl⟩ := exists_puCl_superset hθ hXL
  have hAU : A ∈ U := hXU (by simp)
  have hωU : ωZ.{u} ∈ U := hXU (by simp)
  have hTU : TruthSet A ∈ U := hXU (by simp)
  exact ⟨U, hUL, TruthSet A, hT, satCode_truthSet hUtrans hAU hTU hωU hUpucl⟩

end BM4.ST
