import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_915_aux

def ixf (k : ℕ) (hk : 0 < k) (n : ℕ) : Fin k := ⟨n % k, Nat.mod_lt _ hk⟩

def dif {k : ℕ} (f : (Fin k → ZMod 2) → ZMod 2) (v x : Fin k → ZMod 2) : ZMod 2 := f (x + v) - f x

def Dep {k : ℕ} (A : Finset (Fin k)) (f : (Fin k → ZMod 2) → ZMod 2) : Prop :=
  ∀ w w' : Fin k → ZMod 2, (∀ a ∈ A, w a = w' a) → f w = f w'

def win (k : ℕ) (hk : 0 < k) (b : ℕ) (j : Fin k) : Finset (Fin k) :=
  Finset.univ.image (fun u : Fin b => ixf k hk (j.val + u.val))

def uv {k : ℕ} (a : Fin k) : Fin k → ZMod 2 := fun j => if j = a then (1 : ZMod 2) else 0

theorem alg_sum {k : ℕ} (g : Fin k → (Fin k → ZMod 2) → ZMod 2) (l : List (Fin k → ZMod 2)) (x : Fin k → ZMod 2) :
    l.foldl dif (fun w => ∑ j : Fin k, g j w) x = ∑ j : Fin k, l.foldl dif (g j) x := by
  induction l generalizing g with
  | nil => rfl
  | cons v l ih =>
    have e : dif (fun w => ∑ j : Fin k, g j w) v = fun w => ∑ j : Fin k, dif (g j) v w := by
      funext w
      simp only [dif, Finset.sum_sub_distrib]
    show l.foldl dif (dif (fun w => ∑ j : Fin k, g j w) v) x = ∑ j : Fin k, l.foldl dif (dif (g j) v) x
    rw [e]
    exact ih (fun j => dif (g j) v)

theorem dep_dif {k : ℕ} (A : Finset (Fin k)) (f : (Fin k → ZMod 2) → ZMod 2) (hf : Dep A f)
    (v : Fin k → ZMod 2) : Dep A (dif f v) := by
  intro w w' h
  unfold dif
  rw [hf w w' h, hf (w + v) (w' + v) (fun a ha => by simp only [Pi.add_apply, h a ha])]

theorem alg_loc {k : ℕ} (A : Finset (Fin k)) (f : (Fin k → ZMod 2) → ZMod 2) (hf : Dep A f)
    (l l' : List (Fin k → ZMod 2)) (hl : List.Forall₂ (fun v v' => ∀ a ∈ A, v a = v' a) l l') :
    l.foldl dif f = l'.foldl dif f := by
  induction hl generalizing f with
  | nil => rfl
  | @cons v v' l l' hv _ ih =>
    have e : dif f v = dif f v' := by
      funext x
      unfold dif
      rw [hf (x + v) (x + v') (fun a ha => by simp only [Pi.add_apply, hv a ha])]
    show l.foldl dif (dif f v) = l'.foldl dif (dif f v')
    rw [e]
    exact ih (dif f v') (dep_dif A f hf v')

theorem foldl_zero {k : ℕ} (l : List (Fin k → ZMod 2)) :
    l.foldl dif (fun _ => (0 : ZMod 2)) = fun _ => 0 := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    have e : dif (fun _ => (0 : ZMod 2)) v = fun _ => 0 := by
      funext x
      simp [dif]
    show l.foldl dif (dif (fun _ => (0 : ZMod 2)) v) = _
    rw [e]
    exact ih

theorem alg_zero {k : ℕ} (A : Finset (Fin k)) (f : (Fin k → ZMod 2) → ZMod 2) (hf : Dep A f)
    (l : List (Fin k → ZMod 2)) (hz : ∃ v ∈ l, ∀ a ∈ A, v a = 0) :
    l.foldl dif f = fun _ => 0 := by
  induction l generalizing f with
  | nil => simp at hz
  | cons v0 l ih =>
    show l.foldl dif (dif f v0) = _
    obtain ⟨v, hv, hva⟩ := hz
    rcases List.mem_cons.mp hv with rfl | hv'
    · have e : dif f v = fun _ => 0 := by
        funext x
        unfold dif
        rw [hf (x + v) x (fun a ha => by simp only [Pi.add_apply, hva a ha, add_zero]), sub_self]
      rw [e]
      exact foldl_zero l
    · exact ih (dif f v0) (dep_dif A f hf v0) ⟨v, hv', hva⟩

lemma ge_key (k : ℕ) (hk : 0 < k) (s x y j u1 u2 : ℕ) (h1 : ixf k hk (s + x) = ixf k hk (j + u1))
    (h2 : ixf k hk (s + y) = ixf k hk (j + u2)) (hx : x + u2 < k) (hy : y + u1 < k) :
    x + u2 = y + u1 := by
  have e1 : s + x ≡ j + u1 [MOD k] := congrArg Fin.val h1
  have e2 : s + y ≡ j + u2 [MOD k] := congrArg Fin.val h2
  have e3 : s + (x + u2) ≡ s + (y + u1) [MOD k] := by
    have a := e1.add_right u2
    have c := e2.add_right u1
    rw [show j + u2 + u1 = j + u1 + u2 by ring] at c
    rw [← add_assoc, ← add_assoc]
    exact a.trans c.symm
  have e4 := Nat.ModEq.add_left_cancel' s e3
  unfold Nat.ModEq at e4
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at e4

lemma ge_ne (k : ℕ) (hk : 0 < k) (s x y : ℕ) (h : ixf k hk (s + x) = ixf k hk (s + y))
    (hx : x < k) (hy : y < k) : x = y := by
  have e : s + x ≡ s + y [MOD k] := congrArg Fin.val h
  have e4 := Nat.ModEq.add_left_cancel' s e
  unfold Nat.ModEq at e4
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at e4

lemma ge_fit (b p t k i : ℕ) (hb : 0 < b) (hi : i < t)
    (hsz : b + t*p + (t+1)*(b-1) ≤ k) : 2*b-1 + i*(p+b-1) + p + (b-1) ≤ k := by
  have h1 : (i+1)*(p+b-1) ≤ t*(p+b-1) := Nat.mul_le_mul_right _ hi
  have h2 : t*(p+b-1) = t*p + t*(b-1) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  have h3 : (t+1)*(b-1) = t*(b-1) + (b-1) := Nat.succ_mul _ _
  have h4 : (i+1)*(p+b-1) = i*(p+b-1) + (p+b-1) := Nat.succ_mul _ _
  omega

lemma ge_gap (b p i i' : ℕ) (hb : 0 < b) (h : i < i') :
    i*(p+b-1) + p + (b-1) ≤ i'*(p+b-1) := by
  have h1 : (i+1)*(p+b-1) ≤ i'*(p+b-1) := Nat.mul_le_mul_right _ h
  have h4 : (i+1)*(p+b-1) = i*(p+b-1) + (p+b-1) := Nat.succ_mul _ _
  omega

lemma ge_div (D p : ℕ) (hp : 0 < p) : ∃ n, D ≤ p*n ∧ p*n < D + p := by
  refine ⟨(D+p-1)/p, ?_⟩
  have h1 := Nat.div_add_mod (D+p-1) p
  have h2 := Nat.mod_lt (D+p-1) hp
  omega

theorem geo (k b p t : ℕ) (hk : 0 < k) (hb : 0 < b) (hp : 0 < p) (ht : 2 ≤ t)
    (hsz : b + t*p + (t+1)*(b-1) ≤ k) (s : Fin k) (off : Fin t → Fin b) :
    ∃ far : Fin t → Fin k, Function.Injective far ∧
      (∀ i (u : Fin b), far i ≠ ixf k hk (s.val + u.val)) ∧
      (∀ i, ∃ n : ℕ, far i = ixf k hk ((ixf k hk (s.val + (off i).val)).val + p*n)) ∧
      ∀ (j : Fin k) (i : Fin t), far i ∈ win k hk b j → ∀ i' : Fin t, i' ≠ i →
        ixf k hk (s.val + (off i').val) ∉ win k hk b j ∧ far i' ∉ win k hk b j := by
  have hfit : ∀ i : Fin t, 2*b-1 + i.val*(p+b-1) + p + (b-1) ≤ k :=
    fun i => ge_fit b p t k i.val hb i.isLt hsz
  have hgap : ∀ i i' : Fin t, i.val < i'.val → i.val*(p+b-1) + p + (b-1) ≤ i'.val*(p+b-1) :=
    fun i i' h => ge_gap b p i.val i'.val hb h
  have hP : ∀ i, (ixf k hk (s.val + (off i).val)).val ≤ s.val + (off i).val :=
    fun i => Nat.mod_le _ _
  have hoff : ∀ i, (off i).val < b := fun i => (off i).isLt
  have hex : ∀ i : Fin t, ∃ n, s.val + (2*b-1 + i.val*(p+b-1)) ≤ (ixf k hk (s.val + (off i).val)).val + p*n ∧
      (ixf k hk (s.val + (off i).val)).val + p*n < s.val + (2*b-1 + i.val*(p+b-1)) + p := by
    intro i
    obtain ⟨n, h1, h2⟩ := ge_div (s.val + (2*b-1 + i.val*(p+b-1)) - (ixf k hk (s.val + (off i).val)).val) p hp
    have := hP i
    have := hoff i
    exact ⟨n, by omega, by omega⟩
  choose n hn using hex
  have hf : ∀ i, ixf k hk ((ixf k hk (s.val + (off i).val)).val + p * n i) =
      ixf k hk (s.val + ((ixf k hk (s.val + (off i).val)).val + p * n i - s.val)) := by
    intro i
    have := hn i
    congr 1
    omega
  refine ⟨fun i => ixf k hk ((ixf k hk (s.val + (off i).val)).val + p * n i), ?_, ?_,
    fun i => ⟨n i, rfl⟩, ?_⟩
  · intro i i' h
    simp only at h
    rw [hf i, hf i'] at h
    have a := hn i
    have a' := hn i'
    have fi := hfit i
    have fi' := hfit i'
    have e := ge_ne k hk s.val _ _ h (by omega) (by omega)
    apply Fin.ext
    rcases Nat.lt_trichotomy i.val i'.val with c | c | c
    · have := hgap i i' c
      omega
    · exact c
    · have := hgap i' i c
      omega
  · intro i u h
    simp only at h
    rw [hf i] at h
    have a := hn i
    have fi := hfit i
    have e := ge_ne k hk s.val _ _ h (by omega) (by omega)
    have := u.isLt
    omega
  · intro j i hi i' hne
    simp only at hi ⊢
    rw [hf i] at hi
    unfold win at hi ⊢
    rw [Finset.mem_image] at hi
    obtain ⟨u1, -, hu1⟩ := hi
    have a := hn i
    have fi := hfit i
    have a' := hn i'
    have fi' := hfit i'
    have hu1' := u1.isLt
    have ho := hoff i'
    constructor
    · rw [Finset.mem_image]
      rintro ⟨u2, -, hu2⟩
      have hu2' := u2.isLt
      have e := ge_key k hk s.val _ _ j.val u1.val u2.val hu1.symm hu2.symm (by omega) (by omega)
      omega
    · rw [Finset.mem_image]
      rintro ⟨u2, -, hu2⟩
      rw [hf i'] at hu2
      have hu2' := u2.isLt
      have e := ge_key k hk s.val _ _ j.val u1.val u2.val hu1.symm hu2.symm (by omega) (by omega)
      rcases Nat.lt_trichotomy i.val i'.val with c | c | c
      · have := hgap i i' c
        omega
      · exact hne (Fin.ext c.symm)
      · have := hgap i' i c
        omega

theorem dep_win (k b : ℕ) (hk : 0 < k) (j : Fin k) (tb : (Fin b → ZMod 2) → ZMod 2) :
    Dep (win k hk b j) (fun w => tb (fun u => w (ixf k hk (j.val + u.val)))) := by
  intro w w' h
  have e : (fun u : Fin b => w (ixf k hk (j.val + u.val))) = (fun u => w' (ixf k hk (j.val + u.val))) := by
    funext u
    exact h _ (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩)
  simp only [e]

theorem forall2_ofFn {k t : ℕ} (A : Finset (Fin k)) (f g : Fin t → Fin k → ZMod 2)
    (h : ∀ i, ∀ a ∈ A, f i a = g i a) :
    List.Forall₂ (fun v v' => ∀ a ∈ A, v a = v' a) (List.ofFn f) (List.ofFn g) := by
  rw [List.ofFn_eq_map, List.ofFn_eq_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro i _
  exact h i

theorem uv_ne {k : ℕ} (a c : Fin k) (h : c ≠ a) : uv a c = 0 := by
  simp [uv, h]

theorem main (k b p t : ℕ) (hk : 0 < k) (hb : 0 < b) (hp : 0 < p) (ht : 2 ≤ t)
    (hsz : b + t*p + (t+1)*(b-1) ≤ k) (s : Fin k) (off : Fin t → Fin b) :
    ∃ far : Fin t → Fin k, Function.Injective far ∧
      (∀ i (u : Fin b), far i ≠ ixf k hk (s.val + u.val)) ∧
      (∀ i, ∃ n : ℕ, far i = ixf k hk ((ixf k hk (s.val + (off i).val)).val + p*n)) ∧
      ∀ (table : Fin k → (Fin b → ZMod 2) → ZMod 2) (x : Fin k → ZMod 2),
        (List.ofFn (fun i => uv (ixf k hk (s.val + (off i).val)) + uv (far i))).foldl dif
            (fun w => ∑ j : Fin k, table j (fun u => w (ixf k hk (j.val + u.val)))) x =
          (List.ofFn (fun i => uv (ixf k hk (s.val + (off i).val)))).foldl dif
            (fun w => ∑ j : Fin k, table j (fun u => w (ixf k hk (j.val + u.val)))) x := by
  obtain ⟨far, h1, h2, h3, h4⟩ := geo k b p t hk hb hp ht hsz s off
  refine ⟨far, h1, h2, h3, fun table x => ?_⟩
  rw [alg_sum, alg_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hd := dep_win k b hk j (table j)
  by_cases hj : ∃ i, far i ∈ win k hk b j
  · obtain ⟨i, hi⟩ := hj
    have hex : ∃ i' : Fin t, i' ≠ i := by
      by_cases h0 : i.val = 0
      · exact ⟨⟨1, by omega⟩, fun h => by have := congrArg Fin.val h; simp at this; omega⟩
      · exact ⟨⟨0, by omega⟩, fun h => by have := congrArg Fin.val h; simp at this; omega⟩
    obtain ⟨i', hi'⟩ := hex
    obtain ⟨hp', hf'⟩ := h4 j i hi i' hi'
    have z1 := alg_zero (win k hk b j) _ hd
      (List.ofFn (fun i => uv (ixf k hk (s.val + (off i).val)) + uv (far i)))
      ⟨_, List.mem_ofFn.mpr ⟨i', rfl⟩, fun a ha => by
        simp only [Pi.add_apply]
        rw [uv_ne (ixf k hk (s.val + (off i').val)) a (fun h => hp' (h ▸ ha)), uv_ne (far i') a (fun h => hf' (h ▸ ha)), add_zero]⟩
    have z2 := alg_zero (win k hk b j) _ hd
      (List.ofFn (fun i => uv (ixf k hk (s.val + (off i).val))))
      ⟨_, List.mem_ofFn.mpr ⟨i', rfl⟩, fun a ha => uv_ne (ixf k hk (s.val + (off i').val)) a (fun h => hp' (h ▸ ha))⟩
    rw [z1, z2]
  · simp only [not_exists] at hj
    rw [alg_loc (win k hk b j) _ hd _ _ (forall2_ofFn (win k hk b j) _ _ (fun i a ha => by
      simp only [Pi.add_apply]
      rw [uv_ne (far i) a (fun h => hj i (h ▸ ha)), add_zero]))]

end PEqualNP.Outside.L_lib_915_aux

theorem PEqualNP.Outside.L_lib_915 : (∀ (k b p t : ℕ) (hk : 0 < k), 0 < b → 0 < p → 2 ≤ t →
  b + t*p + (t+1)*(b-1) ≤ k →
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let unit := fun (a j : Fin k) => if j = a then (1 : F) else 0
  let diff := fun (f : W → F) (v x : W) => f (x+v) - f x
  let cube := fun (f : W → F) (v : Fin t → W) => (List.ofFn v).foldl diff f
  ∀ (s : Fin k) (off : Fin t → Fin b),
    let pos := fun i => ix (s.val + (off i).val)
    ∃ (far : Fin t → Fin k), Function.Injective far ∧
      (∀ i (u : Fin b), far i ≠ ix (s.val+u.val)) ∧
      (∀ i, ∃ n : ℕ, far i = ix ((pos i).val + p*n)) ∧
      ∀ (table : Fin k → (Fin b → F) → F) (x : W),
        let f := fun w : W => ∑ j : Fin k, table j (fun u => w (ix (j.val+u.val)))
        cube f (fun i => unit (pos i) + unit (far i)) x =
          cube f (fun i => unit (pos i)) x) := by
  intro k b p t hk hb hp ht hsz
  dsimp only
  intro s off
  exact PEqualNP.Outside.L_lib_915_aux.main k b p t hk hb hp ht hsz s off
