[← Back](../README.md)

# Phase B 作業メモ（完了、2026-09-04）

**Phase B は完了しました。** 論文全体が sorry なしで形式化されています。

```
BM4.ST.terminates_unconditional : ∀ {r} (A : Arr r), Reachable r A → ∀ n, ∃ T, (seq A n T).len = 0
BM4.ST.R_wf_unconditional : ∀ r, WellFounded (R r)
```

依存公理は propext, Classical.choice, Quot.sound のみ。ファイル構成は `lean/README.md` を参照。

以下は作業中の記録（履歴として残す）。

# Phase B 作業メモ（2026-09-04 時点）

設計は `lean-formalization-study.md` §9 を参照。ファイルは `lean/Bm4/SetTheory/`。

## 済（sorry 無し、ビルド済み）
- `Fm.lean`: 名前付き変数の論理式、`Sat D v φ`、Δ0、絶対性、Σ̂q/Π̂q、双対、padding、連言併合、`rename`。
- `L.lean`: `DefinableOver`, `Def`, `L`, 推移性・単調性・`L_mem_L`・`toZFSet_mem_L_iff`・`rank_L_le`。
- `Elem.lean`: `ElemHat q M N`（定義 14.1）、`elemHat_of_downward`（定理 14.4 の意味論版）。
- `Defin.lean`: `Delta0Def/SigmaDef/PiDef s P` と閉包補題。
- `Adm.lean`: `ωZ`, `Delta0Collection`, `IsAdmissible`, `pair/kpair/sUnion_mem_L_of_limit`, `sep_mem_L_of_limit`。
- `BF.lean`: ブロック論理式 `BF`（符号付き Δ0 行列）、`dual`（対合）、`Sig/Pi`、`subs`, `closure`, `Closed`, `ElemF`, `elemF_of_downward`（有限族 Tarski–Vaught）。

## 済（続き、2026-09-04 再起動後）
- `HF.lean`: 自然数 `natZ`、`ωZ`、L_θ の閉包（insert, ∪, 有限集合 `ofList`）、Δ0 定義可能な基本述語（対、関数、定義域、値域、更新 など）。
- `Rel.lean`: 相対化 `relTo m φ`、意味論、`delta0Def_relTo'`。
- `Recur.lean`: Σ1-収集 `sigma1_collection`（証人の組を有限集合にまとめて Δ0-収集に帰着）。
- `Recursion.lean`: 順序数に沿った Σ1-再帰 `sigma1_recursion`（補題 10.3 の意味論版）、部分近似 `PA` とその一意性。
- `Code.lean`: 論理式のコード `Fm.code`、導出列 `DerSeqW`、`IsCodeW` の Δ0 定義可能性と正しさ `isCodeW_iff`。

- `SatCode.lean`: 充足コード（定義 8.3）、補題 8.2、更新列の存在、正しさ（8.6）、真理部分の一意性、V での存在（911 行）。
- `Omega1.lean`: L_γ (γ < ω₁) の可算性（補題 16.1）、ω₁ の許容性。
- `Skolem.lean`: 補題 16.2 後半。可算な Λ で L_Λ ≺ L_{ω₁}（`exists_elemFull_pair`）。
- `Elem.lean` 追加分: 完全初等性 `ElemFull` と Tarski–Vaught 判定 `elemFull_of_witness`。

- `BFCode.lean`: ブロック論理式のコード、Δ0/Σ̂q/Π̂q コード認識述語、射影（793 行）。
- `LCode.lean`: 定義 9.1（L 階層の内部記述）、補題 9.2（`lcode_sound : LCode → M = L η`）（672 行）。
- `Blk.lean`: ブロック更新 `IsBlkUpd` の Δ0 定義可能性、`updList` との対応、`exsD_iff_exists_list` など。
  注意: `exists_blkUpd` はブロック変数が a の定義域にあることを要求する（`IsBlkUpd` は穴埋めをしないため）。
  一般形は `exists_blkUpd'`（定義域を伸ばした a' を使う）。
- `Truth.lean`: Tr⁺/Tr⁻（Σ1/Π1）、符号付き Δ0 行列の Σ/Π 側真理、交代ブロック真理述語 `TrSigS`/`TrPiS`、
  **補題 13.5**（`trComplexity`: TrSigS q ∈ Σ̂q, TrPiS q ∈ Π̂q）、正しさのインターフェース `BaseCorrect W`。
- `Rel.lean` 追加分: `SigmaDef.relativize` / `PiDef.relativize`（Σ̂q 述語の M への相対化は Δ0）。
- `Stable.lean`: `AdmOrd`（許容順序数）、`RelAdm k α β := α < β ∧ ElemHat (k+2) (L α) (L β)`、補題 15.1。

- `TV.lean`: TV_q, St_k, Rel_k の定義と複雑度（§14-15）。
  注意: `RelK` の定義には「M が良い領域で引数を含む」条件が入っている（相対化が Δ0 になるため）。
- `TrCorrect.lean`: 定理 13.6（真理述語の正しさ）。`GoodAsn` に 3 条件が要る:
  ブロック変数が重複しないこと（数学的に必要）、コードが W の元、W が insert で閉じること。
- `SatInL.lean`: **補題 10.5(1)**（充足コードが許容 L_θ に存在、1667 行）。sigma1_recursion は使わず、
  外側の帰納（ℕ と Fm）＋ Σ1 収集で構成。`add_omega0_lt` に θ の許容性が本質的に要る。
- `BaseOK.lean`: `baseCorrect_L`（許容 θ で `BaseCorrect (L θ)`）。定理 13.6 が無条件になった。
- `AdmTrans.lean`: 初等性に沿った許容性の下降、`exists_admissible_elemFull_pair`（補題 16.2 完全形）。
- `Good.lean`: `GoodOrd θ`（許容 ∧ BaseCorrect ∧ LCode 存在）のインターフェース。
- `Stable.lean`: `AdmOrd`, `RelAdm`, 補題 15.1, `exists_relAdm_all`（初期対）。
- `BFConv.lean`: Fm の Σ̂q 論理式 → ブロック論理式。

## 進行中（作業者）
- `LCodeEx.lean`: 補題 10.5(2)（LCode の L_θ 内存在）と `goodOrd_of_isAdmissible`。
- `StRel.lean`: 補題 15.3, 15.5（St_k, Rel_k の正しさ）。
- `AdmP.lean`: 定義 11.1, 補題 11.2（内部の許容性述語 `AdmP`、Σ̂1）。

## 進行中だったもの（旧）
- `HF.lean`（作業者に委任中、再起動で消える可能性あり）: 自然数 `natZ`、`ωZ` の元、L_θ（極限）の insert/∪/有限集合の閉包、Δ0 定義可能な基本述語（部分集合、空、単集合、非順序対、Kuratowski 対、後続、推移的、順序数、⋃、∪、insert、`IsFunc`、`FunVal`、`IsDom`、`IsRan`、`IsUpdate`）。仕様の要点: 各述語を `Delta0Def {vars} (fun _ v => ...)` の形で、隠れた非有界量化を `∀ p ∈ f, ∀ q ∈ p, ∀ a ∈ q, ...` の有界形に直してから `Delta0Def.ball/bex` と `congr` で示す。

## 次にやること（順番）
1. 定理 17.1（有限反映）。作業者 3 つの結果が揃ってから。手順:
   - 与えられた有限データ（X, y_0..y_{s-1}, パターン）から論理式 Φ を組み立てる。
     Φ = ∃u_0..∃u_{s-1} [⋀ AdmP(u_i) ∧ ⋀_{x∈X}(x < u_0) ∧ ⋀_{i<j}(u_i < u_j)
          ∧ ⋀ RelK_k(x,u_i) ∧ ⋀ RelK_k(u_i,u_j) ∧ ⋀_{m<n} StK_m(u_i)]
   - 複雑度: n = 0 なら全連言子が Σ̂1 なので Φ は Σ̂1（padding で Σ̂2）。
     n > 0 なら Σ̂1 を Π̂2 に上げ（`Fm.IsSigma.exists_pi_two`）、Π̂_{n+1} に padding して
     `IsPi.and_exists` でまとめ、∃ ブロックを付けて Σ̂_{n+2}。
   - Φ のブロック変数は互いに異なるように取る（`TrCorrect` の `GoodAsn` が要求）。
   - L_β で Φ が真（証人は y_i 自身）→ `RelAdm n α β = ElemHat (n+2)` で L_α に反映
     → 証人 y'_i を取り出し、`admP_iff`, `stK_iff`, `relK_iff` で外部の関係に戻す。
2. `LabelSystem` のインスタンス構成。`Stable.lean` の `AdmOrd`/`RelAdm`、初期対は `exists_relAdm_all`、
   反映は 1。ラベルは許容順序数（`GoodOrd` は `goodOrd_of_isAdmissible` で自動）。
3. `Bm4/Main.lean` の `terminates` / `R_wf` に 2 のインスタンスを代入して無条件化する。
