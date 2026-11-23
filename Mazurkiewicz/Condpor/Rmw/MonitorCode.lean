import Mazurkiewicz.Condpor.Rmw.Monitors

/-!
# Monitors: the code of a monitor state

`sigDecode_sigCode`: the decoding inverts the coding, for every monitor state
(including `[]`, whose code is `0`). Consequences: `sigCode` and `freeVal` are
injective; a free value is even and never `1`; only `[]` has the code `0`.

The proof goes through the layers of the coding: `listDecode` inverts
`listCode` with enough fuel (`listDecode_listCode`, fuel at least the number
of digits, which the code bounds), `WComp.unflat` inverts `WComp.flat`
followed by a rest (`WComp.unflat_flat`), and `unflatAll` the flattened list
(`unflatAll_flatMap`).
-/

namespace Condpor

/-! ### Numbers and lists -/

/-- The number of steps `listDecode` takes on `listCode L`, apart from the
final one. -/
def listSize : List ℕ → ℕ
  | [] => 0
  | n :: l => n + 1 + listSize l

theorem listCode_pos (L : List ℕ) : 0 < listCode L := by
  cases L with
  | nil => simp [listCode]
  | cons n l =>
    simp only [listCode]
    have := Nat.one_le_two_pow (n := n)
    have : 0 < listCode l := listCode_pos l
    positivity

theorem listSize_lt_listCode (L : List ℕ) : listSize L < listCode L := by
  induction L with
  | nil => simp [listSize, listCode]
  | cons n l ih =>
    simp only [listSize, listCode]
    have h1 : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
    have h2 : listCode l * 2 * (n + 1) ≤ listCode l * 2 * 2 ^ n := Nat.mul_le_mul_left _ h1
    have h3 : 1 ≤ listCode l := listCode_pos l
    nlinarith

theorem listDecode_one (fuel acc : ℕ) : listDecode fuel 1 acc = [] := by
  cases fuel <;> simp [listDecode]

/-- One number: `k` digits `1`, a digit `0`, then the code `X` of the rest. -/
theorem listDecode_block (X : ℕ) (hX : 0 < X) :
    ∀ (k acc fuel : ℕ), k + 1 ≤ fuel →
      listDecode fuel (X * 2 * 2 ^ k + (2 ^ k - 1)) acc =
        (acc + k) :: listDecode (fuel - (k + 1)) X 0 := by
  intro k
  induction k with
  | zero =>
    intro acc fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hm : ¬ X * 2 * 2 ^ 0 + (2 ^ 0 - 1) ≤ 1 := by simp; omega
    have he : (X * 2 * 2 ^ 0 + (2 ^ 0 - 1)) % 2 = 0 := by simp
    simp only [listDecode, hm, he, ↓reduceIte]
    simp
  | succ k ih =>
    intro acc fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have heq : X * 2 * 2 ^ (k + 1) + (2 ^ (k + 1) - 1) =
        2 * (X * 2 * 2 ^ k + (2 ^ k - 1)) + 1 := by
      rw [pow_succ]
      have : 2 ^ k * 2 - 1 = 2 * (2 ^ k - 1) + 1 := by omega
      rw [this]
      have h2 : X * 2 * (2 ^ k * 2) = 2 * (X * 2 * 2 ^ k) := by
        rw [Nat.mul_comm (2 ^ k) 2, ← Nat.mul_assoc, Nat.mul_comm _ 2, Nat.mul_assoc]
      omega
    rw [heq]
    have hm : ¬ 2 * (X * 2 * 2 ^ k + (2 ^ k - 1)) + 1 ≤ 1 := by
      have : 0 < X * 2 * 2 ^ k := by positivity
      omega
    have ho : (2 * (X * 2 * 2 ^ k + (2 ^ k - 1)) + 1) % 2 = 1 := by omega
    have hd : (2 * (X * 2 * 2 ^ k + (2 ^ k - 1)) + 1) / 2 = X * 2 * 2 ^ k + (2 ^ k - 1) := by
      omega
    rw [listDecode]
    simp only [hm, ho, ↓reduceIte]
    rw [hd, ih (acc + 1) f (by omega), show acc + 1 + k = acc + (k + 1) by omega,
      show f + 1 - (k + 1 + 1) = f - (k + 1) by omega]

/-- `listDecode` inverts `listCode`, with at least `listSize L` steps. -/
theorem listDecode_listCode (L : List ℕ) :
    ∀ fuel, listSize L ≤ fuel → listDecode fuel (listCode L) 0 = L := by
  induction L with
  | nil => intro fuel _; exact listDecode_one fuel 0
  | cons n l ih =>
    intro fuel hf
    simp only [listSize] at hf
    simp only [listCode]
    rw [listDecode_block _ (listCode_pos l) n 0 fuel (by omega), ih _ (by omega)]
    simp

/-- With the fuel of `sigDecode`. -/
theorem listDecode_listCode_self (L : List ℕ) :
    listDecode (listCode L + 1) (listCode L) 0 = L :=
  listDecode_listCode L _ (by have := listSize_lt_listCode L; omega)

/-! ### Components -/

theorem unflatPairs_flat (W : List (Tid × ℕ)) (rest : List ℕ) :
    unflatPairs W.length (W.flatMap (fun w => [w.1, w.2]) ++ rest) = (W, rest) := by
  induction W with
  | nil => simp [unflatPairs]
  | cons w W ih =>
    simp only [List.length_cons, List.flatMap_cons, List.cons_append, List.nil_append] at ih ⊢
    rw [unflatPairs, ih]

/-- `WComp.unflat` inverts `WComp.flat`, followed by any rest. -/
theorem WComp.unflat_flat (k : WComp) (rest : List ℕ) :
    WComp.unflat (k.flat ++ rest) = (k, rest) := by
  obtain ⟨c, a, T, S, W⟩ := k
  simp only [WComp.flat, List.cons_append, List.nil_append, List.append_assoc]
  rw [WComp.unflat]
  simp only [List.drop_left', List.take_left']
  rw [unflatPairs_flat]

/-- `unflatAll` inverts the flattening of a list of components. -/
theorem unflatAll_flatMap (σ : List WComp) (rest : List ℕ) :
    unflatAll σ.length (σ.flatMap WComp.flat ++ rest) = σ := by
  induction σ with
  | nil => simp [unflatAll]
  | cons k σ ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc]
    rw [unflatAll, WComp.unflat_flat, ih]

/-! ### Monitor states -/

/-- The decoding inverts the coding, for every monitor state. -/
theorem sigDecode_sigCode (σ : Sig) : sigDecode (sigCode σ) = σ := by
  by_cases h : σ = []
  · subst h
    simp [sigCode, sigDecode, listDecode]
  · unfold sigDecode sigCode
    simp only [h, ↓reduceIte]
    rw [listDecode_listCode_self]
    simpa using unflatAll_flatMap σ []

theorem sigCode_injective : Function.Injective sigCode := by
  intro σ τ h
  rw [← sigDecode_sigCode σ, h, sigDecode_sigCode]

/-- Only the state without components has the code `0`. -/
theorem sigCode_eq_zero_iff (σ : Sig) : sigCode σ = 0 ↔ σ = [] := by
  constructor
  · intro h
    by_contra hne
    unfold sigCode at h
    simp only [hne, ↓reduceIte] at h
    exact (listCode_pos _).ne' h
  · rintro rfl
    simp [sigCode]

theorem freeVal_mod_two (σ : Sig) : freeVal σ % 2 = 0 := by
  simp [freeVal]

theorem freeVal_ne_one (σ : Sig) : freeVal σ ≠ 1 := by
  intro h
  have h2 := freeVal_mod_two σ
  rw [h] at h2
  exact absurd h2 (by decide)

theorem freeVal_div_two (σ : Sig) : freeVal σ / 2 = sigCode σ := by
  simp [freeVal]

/-- The state a reader of a free value decodes is the state of the writer. -/
theorem sigDecode_freeVal (σ : Sig) : sigDecode (freeVal σ / 2) = σ := by
  rw [freeVal_div_two, sigDecode_sigCode]

theorem freeVal_injective : Function.Injective freeVal := by
  intro σ τ h
  rw [← sigDecode_freeVal σ, h, sigDecode_freeVal]

/-- The initial value `0` of a location is the free value of `[]`. -/
theorem freeVal_nil : freeVal [] = 0 := by
  simp [freeVal, sigCode]

end Condpor
