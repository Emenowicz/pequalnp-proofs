import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25750_aux

def sgn (t : ZMod 2) : ℤ := if t = 0 then 1 else -1

theorem sgn_zero : sgn 0 = 1 := by simp [sgn]

theorem sgn_add : ∀ x y : ZMod 2, sgn (x + y) = sgn x * sgn y := by decide

theorem sgn_one : sgn 1 = -1 := by decide

theorem zmod2_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

theorem add_self_zmod2 : ∀ x : ZMod 2, x + x = 0 := by decide

theorem zmod2_sum3 : ∀ a b c : ZMod 2, a + b + c = 0 → c = b + a := by decide

theorem zmod2_per : ∀ p q : ZMod 2, (q + p) + q = p := by decide

theorem zmod2_triple : ∀ p : ZMod 2, p + p + p = 0 → p = 0 := by decide

theorem eq_of_add_eq_zero {k : ℕ} (x y : ZMod k → ZMod 2) : y + x = 0 ↔ y = x := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    have h2 := add_self_zmod2 (x i)
    simp only [Pi.add_apply, Pi.zero_apply] at hi
    calc y i = y i + (x i + x i) := by rw [h2, add_zero]
      _ = (y i + x i) + x i := by ring
      _ = x i := by rw [hi, zero_add]
  · rintro rfl
    funext i
    exact add_self_zmod2 (y i)

variable {k : ℕ}

def mixd (d : ℕ) (x : ZMod k → ZMod 2) : ZMod k → ZMod 2 :=
  fun i => x (i - (d : ZMod k)) + x i + x (i + (d : ZMod k))

def nlf (y : ZMod k → ZMod 2) : ZMod k → ZMod 2 :=
  fun j => y j + (1 + y (j + 1)) * y (j + 2)

theorem mix_add (d : ℕ) (x y : ZMod k → ZMod 2) : mixd d (x + y) = mixd d x + mixd d y := by
  funext i
  simp only [mixd, Pi.add_apply]
  ring

theorem mix_zero (d : ℕ) : mixd d (0 : ZMod k → ZMod 2) = 0 := by
  funext i
  simp [mixd]

theorem ker_rec (d : ℕ) (x : ZMod k → ZMod 2) (hx : mixd d x = 0) (i : ZMod k) :
    x (i + (d : ZMod k) + (d : ZMod k)) = x (i + (d : ZMod k)) + x i := by
  have h := congrFun hx (i + (d : ZMod k))
  simp only [mixd, Pi.zero_apply, add_sub_cancel_right] at h
  exact zmod2_sum3 _ _ _ h

theorem ker_per3 (d : ℕ) (x : ZMod k → ZMod 2) (hx : mixd d x = 0) (i : ZMod k) :
    x (i + (d : ZMod k) + (d : ZMod k) + (d : ZMod k)) = x i := by
  rw [ker_rec d x hx (i + (d : ZMod k)), ker_rec d x hx i]
  exact zmod2_per _ _

theorem ker_per3_iter (d : ℕ) (x : ZMod k → ZMod 2) (hx : mixd d x = 0) (t : ℕ) (i : ZMod k) :
    x (i + ((3 * t : ℕ) : ZMod k) * (d : ZMod k)) = x i := by
  induction t with
  | zero => simp
  | succ t ih =>
    have e : i + ((3 * (t + 1) : ℕ) : ZMod k) * (d : ZMod k)
        = (i + ((3 * t : ℕ) : ZMod k) * (d : ZMod k)) + (d : ZMod k) + (d : ZMod k) + (d : ZMod k) := by
      push_cast
      ring
    rw [e, ker_per3 d x hx, ih]

theorem ker_trivial (d g L d' : ℕ) (hk : k = g * L) (hd : d = g * d') (h3 : ¬ 3 ∣ L)
    (x : ZMod k → ZMod 2) (hx : mixd d x = 0) : x = 0 := by
  obtain ⟨t, c, ht⟩ : ∃ t c : ℕ, 3 * t = c * L + 1 := by
    have hmod : L % 3 = 1 ∨ L % 3 = 2 := by omega
    rcases hmod with h | h
    · exact ⟨(2 * L + 1) / 3, 2, by omega⟩
    · exact ⟨(L + 1) / 3, 1, by omega⟩
  have key : ((3 * t : ℕ) : ZMod k) * (d : ZMod k) = (d : ZMod k) := by
    have e1 : 3 * t * d = k * (c * d') + d := by
      rw [ht, hk, hd]
      ring
    have e2 : ((3 * t : ℕ) : ZMod k) * (d : ZMod k) = ((3 * t * d : ℕ) : ZMod k) := by push_cast; ring
    rw [e2, e1]
    push_cast
    rw [ZMod.natCast_self, zero_mul, zero_add]
  have hper : ∀ i : ZMod k, x (i + (d : ZMod k)) = x i := by
    intro i
    have h := ker_per3_iter d x hx t i
    rwa [key] at h
  funext i
  have h := congrFun hx i
  simp only [mixd, Pi.zero_apply] at h
  have h1 : x (i - (d : ZMod k)) = x i := by
    have h2 := hper (i - (d : ZMod k))
    rw [sub_add_cancel] at h2
    exact h2.symm
  rw [h1, hper i] at h
  exact zmod2_triple _ h

variable [NeZero k]

theorem card_V : Fintype.card (ZMod k → ZMod 2) = 2 ^ k := by
  simp [ZMod.card]

theorem orth (c : ZMod k → ZMod 2) :
    ∑ w : ZMod k → ZMod 2, sgn (c ⬝ᵥ w) = if c = 0 then (2 : ℤ) ^ k else 0 := by
  split_ifs with hc
  · subst hc
    simp [sgn_zero]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hc
    have hci : c i = 1 := by
      rcases zmod2_cases (c i) with h | h
      · exact absurd h hi
      · exact h
    have hshift : ∑ w : ZMod k → ZMod 2, sgn (c ⬝ᵥ (w + Pi.single i 1))
        = ∑ w : ZMod k → ZMod 2, sgn (c ⬝ᵥ w) := by
      rw [← Equiv.sum_comp (Equiv.addRight (Pi.single i (1 : ZMod 2))) (fun w => sgn (c ⬝ᵥ w))]
      simp only [Equiv.coe_addRight]
    have hterm : ∀ w : ZMod k → ZMod 2, sgn (c ⬝ᵥ (w + Pi.single i 1)) = - sgn (c ⬝ᵥ w) := by
      intro w
      rw [dotProduct_add, dotProduct_single, hci, mul_one, sgn_add, sgn_one]
      ring
    rw [Finset.sum_congr rfl (fun w _ => hterm w), Finset.sum_neg_distrib] at hshift
    omega

theorem sgn_sum {ι : Type} (s : Finset ι) (f : ι → ZMod 2) :
    sgn (∑ i ∈ s, f i) = ∏ i ∈ s, sgn (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sgn_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sgn_add, ih]

theorem prod_apply (m : ℕ) : ∀ (A : ℕ → Matrix (ZMod 2) (ZMod 2) ℤ) (l h : ZMod 2),
    ((List.range m).map A).prod l h
      = ∑ q : Fin (m + 1) → ZMod 2, (if q 0 = l then 1 else 0) * (if q (Fin.last m) = h then 1 else 0)
          * ∏ j : Fin m, A j (q j.castSucc) (q j.succ) := by
  induction m with
  | zero =>
    intro A l h
    rw [← (Equiv.funUnique (Fin 1) (ZMod 2)).symm.sum_comp]
    simp [Matrix.one_apply, eq_comm]
  | succ m ih =>
    intro A l h
    rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map, Matrix.mul_apply]
    have hmap : (A ∘ Nat.succ) = (fun j => A (j + 1)) := rfl
    rw [hmap]
    have hL : ∑ x : ZMod 2, A 0 l x * ((List.map (fun j => A (j + 1)) (List.range m)).prod x h)
        = ∑ q' : Fin (m + 1) → ZMod 2, A 0 l (q' 0) *
            ((if q' (Fin.last m) = h then 1 else 0) * ∏ j : Fin m, A (j + 1) (q' j.castSucc) (q' j.succ)) := by
      simp only [ih (fun j => A (j + 1)), Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun q' _ => ?_)
      rw [Finset.sum_eq_single (q' 0)]
      · simp
      · intro x _ hx
        simp [Ne.symm hx]
      · intro hx
        exact absurd (Finset.mem_univ _) hx
    have hR : ∑ q : Fin (m + 1 + 1) → ZMod 2, (if q 0 = l then 1 else 0) * (if q (Fin.last (m + 1)) = h then 1 else 0)
          * ∏ j : Fin (m + 1), A j (q j.castSucc) (q j.succ)
        = ∑ q' : Fin (m + 1) → ZMod 2, A 0 l (q' 0) *
            ((if q' (Fin.last m) = h then 1 else 0) * ∏ j : Fin m, A (j + 1) (q' j.castSucc) (q' j.succ)) := by
      rw [← (Fin.consEquiv (fun _ => ZMod 2)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun q' _ => ?_)
      rw [Finset.sum_eq_single l]
      · simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, ite_true, one_mul, Fin.prod_univ_succ,
          Fin.castSucc_zero, Fin.val_zero, Fin.val_succ, ← Fin.succ_last,
          Fin.cons_succ, ← Fin.succ_castSucc]
        ring
      · intro y _ hy
        simp [Fin.consEquiv, hy]
      · intro hx
        exact absurd (Finset.mem_univ _) hx
    rw [hL, hR]

theorem snoc_succ (n : ℕ) (s : Fin (n + 1) → ZMod 2) (j : Fin (n + 1)) :
    (Fin.snoc s (s 0) : Fin (n + 1 + 1) → ZMod 2) j.succ = s (j + 1) := by
  by_cases hj : j = Fin.last n
  · subst hj
    rw [Fin.succ_last, Fin.snoc_last, Fin.last_add_one]
  · have hlt : j < Fin.last n := Fin.lt_last_iff_ne_last.mpr hj
    have he : j.succ = (j + 1).castSucc := by
      apply Fin.ext
      rw [Fin.val_succ, Fin.val_castSucc, Fin.val_add_one_of_lt hlt]
    rw [he, Fin.snoc_castSucc]

theorem trace_cyclic (n : ℕ) (A : ℕ → Matrix (ZMod 2) (ZMod 2) ℤ) :
    Matrix.trace (((List.range (n + 1)).map A).prod)
      = ∑ s : Fin (n + 1) → ZMod 2, ∏ j : Fin (n + 1), A j (s j) (s (j + 1)) := by
  simp only [Matrix.trace, Matrix.diag_apply, prod_apply]
  rw [Finset.sum_comm]
  rw [← (Fin.snocEquiv (fun _ => ZMod 2)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Finset.sum_eq_single (s 0)]
  · rw [Finset.sum_eq_single (s 0)]
    · have h0 : (Fin.snoc s (s 0) : Fin (n + 1 + 1) → ZMod 2) 0 = s 0 := by simp
      simp only [Fin.snocEquiv, Equiv.coe_fn_mk, h0, Fin.snoc_last, ite_true, one_mul]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [Fin.snoc_castSucc, snoc_succ]
    · intro l _ hl
      have h0 : (Fin.snoc s (s 0) : Fin (n + 1 + 1) → ZMod 2) 0 = s 0 := by simp
      simp [Fin.snocEquiv, h0, Ne.symm hl]
    · intro hx
      exact absurd (Finset.mem_univ _) hx
  · intro y _ hy
    refine Finset.sum_eq_zero (fun l _ => ?_)
    have h0 : (Fin.snoc s y : Fin (n + 1 + 1) → ZMod 2) 0 = s 0 := by simp
    by_cases h1 : s 0 = l
    · have h2 : ¬ y = l := fun h => hy (h.trans h1.symm)
      simp [Fin.snocEquiv, h0, h1, h2]
    · simp [Fin.snocEquiv, h0, h1]
  · intro hx
    exact absurd (Finset.mem_univ _) hx

def phi (b s : ZMod k → ZMod 2) : ZMod 2 :=
  ∑ i : ZMod k, ((b i + b (i - 2)) * s i + b (i - 1) * s i * s (i + 1))

theorem nl_dot (b y : ZMod k → ZMod 2) : b ⬝ᵥ nlf y = phi b y := by
  have e2 : ∑ j : ZMod k, b j * y (j + 2) = ∑ i : ZMod k, b (i - 2) * y i := by
    rw [← Equiv.sum_comp (Equiv.addRight (2 : ZMod k)) (fun i => b (i - 2) * y i)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp
  have e3 : ∑ j : ZMod k, b j * (y (j + 1) * y (j + 2)) = ∑ i : ZMod k, b (i - 1) * y i * y (i + 1) := by
    rw [← Equiv.sum_comp (Equiv.addRight (1 : ZMod k)) (fun i => b (i - 1) * y i * y (i + 1))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    rw [add_assoc, one_add_one_eq_two]
    ring
  have e1 : b ⬝ᵥ nlf y = ∑ j : ZMod k, b j * y j + ∑ j : ZMod k, b j * y (j + 2)
      + ∑ j : ZMod k, b j * (y (j + 1) * y (j + 2)) := by
    simp only [dotProduct, nlf]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [e1, e2, e3, phi, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

theorem mix_symm (d : ℕ) (x u : ZMod k → ZMod 2) : mixd d x ⬝ᵥ u = x ⬝ᵥ mixd d u := by
  have e1 : ∑ i : ZMod k, x (i - (d : ZMod k)) * u i = ∑ j : ZMod k, x j * u (j + (d : ZMod k)) := by
    rw [← Equiv.sum_comp (Equiv.addRight (d : ZMod k)) (fun i => x (i - (d : ZMod k)) * u i)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp
  have e2 : ∑ i : ZMod k, x (i + (d : ZMod k)) * u i = ∑ j : ZMod k, x j * u (j - (d : ZMod k)) := by
    rw [← Equiv.sum_comp (Equiv.subRight (d : ZMod k)) (fun i => x (i + (d : ZMod k)) * u i)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp
  have eL : mixd d x ⬝ᵥ u = ∑ i : ZMod k, x (i - (d : ZMod k)) * u i + ∑ i : ZMod k, x i * u i
      + ∑ i : ZMod k, x (i + (d : ZMod k)) * u i := by
    simp only [dotProduct, mixd]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have eR : x ⬝ᵥ mixd d u = ∑ j : ZMod k, x j * u (j + (d : ZMod k)) + ∑ i : ZMod k, x i * u i
      + ∑ j : ZMod k, x j * u (j - (d : ZMod k)) := by
    simp only [dotProduct, mixd]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [eL, eR, e1, e2]

theorem trace_transfer (n : ℕ) (u b : ZMod (n + 1) → ZMod 2) :
    Matrix.trace (List.prod (α := Matrix (ZMod 2) (ZMod 2) ℤ) ((List.range (n + 1)).map (fun (j : ℕ) =>
      (fun (l h : ZMod 2) => sgn ((u (j : ZMod (n + 1)) + b (j : ZMod (n + 1)) + b ((j : ZMod (n + 1)) - 2)) * l
        + b ((j : ZMod (n + 1)) - 1) * l * h) : Matrix (ZMod 2) (ZMod 2) ℤ))))
      = ∑ s : ZMod (n + 1) → ZMod 2, sgn (u ⬝ᵥ s + phi b s) := by
  refine (trace_cyclic n _).trans ?_
  show ∑ s : ZMod (n + 1) → ZMod 2, ∏ j : ZMod (n + 1),
      sgn ((u ((ZMod.val j : ℕ) : ZMod (n + 1)) + b ((ZMod.val j : ℕ) : ZMod (n + 1))
          + b (((ZMod.val j : ℕ) : ZMod (n + 1)) - 2)) * s j
        + b (((ZMod.val j : ℕ) : ZMod (n + 1)) - 1) * s j * s (j + 1)) = _
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp only [ZMod.natCast_zmod_val]
  rw [← sgn_sum]
  congr 1
  simp only [dotProduct, phi]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

theorem inner_id (d : ℕ) (a b x : ZMod k → ZMod 2) :
    ∑ u : ZMod k → ZMod 2, sgn (x ⬝ᵥ (mixd d u + a)) * ∑ s : ZMod k → ZMod 2, sgn (u ⬝ᵥ s + phi b s)
      = (2 : ℤ) ^ k * (sgn (a ⬝ᵥ x) * sgn (phi b (mixd d x))) := by
  have e : ∀ u s : ZMod k → ZMod 2, sgn (x ⬝ᵥ (mixd d u + a)) * sgn (u ⬝ᵥ s + phi b s)
      = sgn (a ⬝ᵥ x) * sgn (phi b s) * sgn ((mixd d x + s) ⬝ᵥ u) := by
    intro u s
    rw [dotProduct_add, sgn_add, sgn_add, add_dotProduct, sgn_add, ← mix_symm d x u,
      dotProduct_comm x a, dotProduct_comm u s]
    ring
  simp only [Finset.mul_sum, e]
  rw [Finset.sum_comm]
  have h2 : ∀ s : ZMod k → ZMod 2,
      ∑ u : ZMod k → ZMod 2, sgn (a ⬝ᵥ x) * sgn (phi b s) * sgn ((mixd d x + s) ⬝ᵥ u)
      = if s = mixd d x then sgn (a ⬝ᵥ x) * sgn (phi b s) * (2 : ℤ) ^ k else 0 := by
    intro s
    rw [← Finset.mul_sum, orth]
    by_cases hs : s = mixd d x
    · subst hs
      have h0 : mixd d x + mixd d x = 0 := (eq_of_add_eq_zero (mixd d x) (mixd d x)).mpr rfl
      simp [h0]
    · have h0 : ¬ (mixd d x + s = 0) := fun h => hs ((eq_of_add_eq_zero s (mixd d x)).mp h).symm
      simp [h0, hs]
  rw [Finset.sum_congr rfl (fun s _ => h2 s), Finset.sum_ite_eq' Finset.univ (mixd d x)]
  simp only [Finset.mem_univ, ite_true]
  ring

theorem part1 (d : ℕ) (a b : ZMod k → ZMod 2) :
    ∑ x : ZMod k → ZMod 2, sgn (a ⬝ᵥ x + b ⬝ᵥ nlf (mixd d x))
      = ∑ u ∈ Finset.univ.filter (fun u : ZMod k → ZMod 2 => mixd d u = a),
          ∑ s : ZMod k → ZMod 2, sgn (u ⬝ᵥ s + phi b s) := by
  have hN : (2 : ℤ) ^ k ≠ 0 := by positivity
  apply mul_left_cancel₀ hN
  have horth : ∀ u : ZMod k → ZMod 2, ∑ x : ZMod k → ZMod 2, sgn (x ⬝ᵥ (mixd d u + a))
      = if mixd d u = a then (2 : ℤ) ^ k else 0 := by
    intro u
    have hc : (∑ x : ZMod k → ZMod 2, sgn (x ⬝ᵥ (mixd d u + a)))
        = ∑ w : ZMod k → ZMod 2, sgn ((mixd d u + a) ⬝ᵥ w) :=
      Finset.sum_congr rfl (fun w _ => by rw [dotProduct_comm])
    rw [hc, orth]
    by_cases hu : mixd d u = a
    · subst hu
      have h0 : mixd d u + mixd d u = 0 := (eq_of_add_eq_zero (mixd d u) (mixd d u)).mpr rfl
      simp [h0]
    · have h0 : ¬ (mixd d u + a = 0) := fun h => hu ((eq_of_add_eq_zero a (mixd d u)).mp h)
      simp [h0, hu]
  calc (2 : ℤ) ^ k * ∑ x : ZMod k → ZMod 2, sgn (a ⬝ᵥ x + b ⬝ᵥ nlf (mixd d x))
      = ∑ x : ZMod k → ZMod 2, (2 : ℤ) ^ k * (sgn (a ⬝ᵥ x) * sgn (phi b (mixd d x))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [sgn_add, nl_dot]
    _ = ∑ x : ZMod k → ZMod 2, ∑ u : ZMod k → ZMod 2, sgn (x ⬝ᵥ (mixd d u + a))
          * ∑ s : ZMod k → ZMod 2, sgn (u ⬝ᵥ s + phi b s) :=
        Finset.sum_congr rfl (fun x _ => (inner_id d a b x).symm)
    _ = ∑ u : ZMod k → ZMod 2, ∑ x : ZMod k → ZMod 2, sgn (x ⬝ᵥ (mixd d u + a))
          * ∑ s : ZMod k → ZMod 2, sgn (u ⬝ᵥ s + phi b s) := Finset.sum_comm
    _ = ∑ u : ZMod k → ZMod 2, (if mixd d u = a then (2 : ℤ) ^ k else 0)
          * ∑ s : ZMod k → ZMod 2, sgn (u ⬝ᵥ s + phi b s) :=
        Finset.sum_congr rfl (fun u _ => by rw [← Finset.sum_mul, horth])
    _ = (2 : ℤ) ^ k * ∑ u ∈ Finset.univ.filter (fun u : ZMod k → ZMod 2 => mixd d u = a),
          ∑ s : ZMod k → ZMod 2, sgn (u ⬝ᵥ s + phi b s) := by
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun u _ => ?_)
        split_ifs <;> ring

theorem arith (k d : ℕ) [NeZero k] : ∃ (L d' e : ℕ), 0 < Nat.gcd k d ∧ k = Nat.gcd k d * L ∧ d = Nat.gcd k d * d'
    ∧ L = k / Nat.gcd k d ∧ 0 < L ∧ ((Nat.gcd k d : ℕ) : ZMod k) = (e : ZMod k) * (d : ZMod k)
    ∧ (d' * e) % L = 1 % L := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hg : 0 < Nat.gcd k d := Nat.gcd_pos_of_pos_left d hk
  obtain ⟨L, hL⟩ := Nat.gcd_dvd_left k d
  obtain ⟨d', hd'⟩ := Nat.gcd_dvd_right k d
  have hLpos : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · rw [h, Nat.mul_zero] at hL
      omega
    · exact h
  have hb := congrArg (Int.cast : ℤ → ZMod k) (Nat.gcd_eq_gcd_ab k d)
  push_cast at hb
  rw [ZMod.natCast_self, zero_mul, zero_add] at hb
  have he : ((((Nat.gcdB k d : ℤ) : ZMod k).val : ℕ) : ZMod k) = ((Nat.gcdB k d : ℤ) : ZMod k) :=
    ZMod.natCast_zmod_val _
  refine ⟨L, d', ((Nat.gcdB k d : ℤ) : ZMod k).val, hg, hL, hd', ?_, hLpos, ?_, ?_⟩
  · exact (Nat.div_eq_of_eq_mul_right hg hL).symm
  · rw [he, hb, mul_comm]
  · have h1 : ((Nat.gcd k d : ℕ) : ZMod k)
        = (((((Nat.gcdB k d : ℤ) : ZMod k).val) * d : ℕ) : ZMod k) := by
      push_cast
      rw [he, hb, mul_comm]
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).mp h1
    have h3 : Nat.gcd k d * 1 ≡ Nat.gcd k d * (d' * ((Nat.gcdB k d : ℤ) : ZMod k).val) [MOD Nat.gcd k d * L] := by
      have e1 : Nat.gcd k d * (d' * ((Nat.gcdB k d : ℤ) : ZMod k).val)
          = ((Nat.gcdB k d : ℤ) : ZMod k).val * (Nat.gcd k d * d') := by ring
      rw [e1, ← hd', ← hL, Nat.mul_one]
      exact h2
    have h4 := Nat.ModEq.mul_left_cancel' (Nat.pos_iff_ne_zero.mp hg) h3
    exact h4.symm

theorem ker_zero_of_base (d g e : ℕ) (hgpos : 0 < g)
    (hg : (g : ZMod k) = (e : ZMod k) * (d : ZMod k))
    (z : ZMod k → ZMod 2) (hz : mixd d z = 0)
    (h0 : ∀ r : ℕ, r < g → z (r : ZMod k) = 0 ∧ z ((r : ZMod k) + (d : ZMod k)) = 0) : z = 0 := by
  have step : ∀ r : ℕ, r < g → ∀ t : ℕ, z ((r : ZMod k) + (t : ZMod k) * (d : ZMod k)) = 0
      ∧ z ((r : ZMod k) + ((t + 1 : ℕ) : ZMod k) * (d : ZMod k)) = 0 := by
    intro r hr t
    induction t with
    | zero => simpa using h0 r hr
    | succ t ih =>
      refine ⟨ih.2, ?_⟩
      have e2 : (r : ZMod k) + ((t + 1 + 1 : ℕ) : ZMod k) * (d : ZMod k)
          = ((r : ZMod k) + (t : ZMod k) * (d : ZMod k)) + (d : ZMod k) + (d : ZMod k) := by
        push_cast
        ring
      have e3 : (r : ZMod k) + (t : ZMod k) * (d : ZMod k) + (d : ZMod k)
          = (r : ZMod k) + ((t + 1 : ℕ) : ZMod k) * (d : ZMod k) := by
        push_cast
        ring
      rw [e2, ker_rec d z hz, e3, ih.1, ih.2, add_zero]
  funext i
  have hi : i = ((i.val % g : ℕ) : ZMod k) + ((e * (i.val / g) : ℕ) : ZMod k) * (d : ZMod k) := by
    have h1 : (i.val : ZMod k) = i := ZMod.natCast_zmod_val i
    have h2 : i.val = i.val % g + g * (i.val / g) := (Nat.mod_add_div i.val g).symm
    calc i = ((i.val : ℕ) : ZMod k) := h1.symm
      _ = ((i.val % g + g * (i.val / g) : ℕ) : ZMod k) := by rw [← h2]
      _ = ((i.val % g : ℕ) : ZMod k) + ((e * (i.val / g) : ℕ) : ZMod k) * (d : ZMod k) := by
        push_cast
        rw [hg]
        ring
  rw [hi]
  exact (step _ (Nat.mod_lt _ hgpos) _).1

theorem ker_card_le (d g e : ℕ) (hgpos : 0 < g)
    (hg : (g : ZMod k) = (e : ZMod k) * (d : ZMod k)) :
    (Finset.univ.filter (fun u : ZMod k → ZMod 2 => mixd d u = 0)).card ≤ 4 ^ g := by
  have hcard : Fintype.card (Fin g → ZMod 2 × ZMod 2) = 4 ^ g := by
    simp
  rw [← hcard, ← Finset.card_univ]
  refine Finset.card_le_card_of_injOn
    (fun (x : ZMod k → ZMod 2) (r : Fin g) => (x ((r.val : ℕ) : ZMod k), x (((r.val : ℕ) : ZMod k) + (d : ZMod k))))
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_
  intro x hx x' hx' hxx
  have hx0 : mixd d x = 0 := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
  have hx0' : mixd d x' = 0 := (Finset.mem_filter.mp (Finset.mem_coe.mp hx')).2
  have hz : mixd d (x + x') = 0 := by rw [mix_add, hx0, hx0', add_zero]
  have hzero : x + x' = 0 := by
    apply ker_zero_of_base d g e hgpos hg (x + x') hz
    intro r hr
    have h := congrFun hxx ⟨r, hr⟩
    simp only [Prod.mk.injEq] at h
    constructor
    · rw [Pi.add_apply, h.1]
      exact add_self_zmod2 _
    · rw [Pi.add_apply, h.2]
      exact add_self_zmod2 _
  exact (eq_of_add_eq_zero x' x).mp hzero

def fsel (t : ℕ) (p : ZMod 2 × ZMod 2) : ZMod 2 :=
  if t = 0 then p.1 else if t = 1 then p.2 else p.1 + p.2

def psi (g L e : ℕ) (P : ℕ → ZMod 2 × ZMod 2) : ZMod k → ZMod 2 :=
  fun i => fsel (((i.val / g) % L * e) % 3) (P (i.val % g))

theorem modL3 (X e L : ℕ) (h3 : 3 ∣ L) : (X % L * e) % 3 = (X * e) % 3 := by
  rw [Nat.mul_mod, Nat.mod_mod_of_dvd _ h3, ← Nat.mul_mod]

theorem shift_nat (g L d' e n : ℕ) (hg : 0 < g) (h3 : 3 ∣ L) (he : (d' * e) % L = 1) :
    ((n + g * d') % (g * L)) % g = n % g ∧
      ((((n + g * d') % (g * L)) / g) % L * e) % 3 = (((n / g) % L * e) % 3 + 1) % 3 := by
  constructor
  · rw [Nat.mod_mul_right_mod, Nat.add_mul_mod_self_left]
  · rw [Nat.mod_mul_right_div_self, Nat.add_mul_div_left _ _ hg, Nat.mod_mod, modL3 _ _ _ h3,
      modL3 _ _ _ h3]
    have hq : (d' * e) % 3 = 1 := by
      have h := Nat.mod_mod_of_dvd (d' * e) h3
      rw [he] at h
      omega
    have e1 : (n / g + d') * e = n / g * e + d' * e := by ring
    rw [e1]
    omega

theorem fsel_sum : ∀ (t : ℕ), t < 3 → ∀ u v : ZMod 2,
    fsel t (u, v) + fsel ((t + 1) % 3) (u, v) + fsel (((t + 1) % 3 + 1) % 3) (u, v) = 0 := by
  intro t ht
  interval_cases t <;> simp only [fsel] <;> decide

theorem val_add_d (d : ℕ) (i : ZMod k) : (i + (d : ZMod k)).val = (i.val + d) % k := by
  rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod]

theorem psi_shift (d g L d' e : ℕ) (hk : k = g * L) (hd : d = g * d') (hg : 0 < g) (h3 : 3 ∣ L)
    (he : (d' * e) % L = 1) (P : ℕ → ZMod 2 × ZMod 2) (i : ZMod k) :
    (psi g L e P : ZMod k → ZMod 2) (i + (d : ZMod k))
      = fsel ((((i.val / g) % L * e) % 3 + 1) % 3) (P (i.val % g)) := by
  have h := shift_nat g L d' e i.val hg h3 he
  rw [← hk, ← hd] at h
  simp only [psi]
  rw [val_add_d, h.1, h.2]

theorem psi_triple (d g L d' e : ℕ) (hk : k = g * L) (hd : d = g * d') (hg : 0 < g) (h3 : 3 ∣ L)
    (he : (d' * e) % L = 1) (P : ℕ → ZMod 2 × ZMod 2) (j : ZMod k) :
    (psi g L e P : ZMod k → ZMod 2) j + psi g L e P (j + (d : ZMod k))
      + psi g L e P (j + (d : ZMod k) + (d : ZMod k)) = 0 := by
  have h := shift_nat g L d' e j.val hg h3 he
  rw [← hk, ← hd] at h
  rw [psi_shift d g L d' e hk hd hg h3 he P (j + (d : ZMod k)), psi_shift d g L d' e hk hd hg h3 he P j,
    val_add_d, h.1, h.2]
  have hlt : ((j.val / g) % L * e) % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hs := fsel_sum _ hlt (P (j.val % g)).1 (P (j.val % g)).2
  simpa [psi] using hs

theorem psi_mem (d g L d' e : ℕ) (hk : k = g * L) (hd : d = g * d') (hg : 0 < g) (h3 : 3 ∣ L)
    (he : (d' * e) % L = 1) (P : ℕ → ZMod 2 × ZMod 2) :
    mixd d (psi g L e P : ZMod k → ZMod 2) = 0 := by
  funext i
  simp only [mixd, Pi.zero_apply]
  have h := psi_triple d g L d' e hk hd hg h3 he P (i - (d : ZMod k))
  rw [sub_add_cancel] at h
  exact h

theorem psi_base (d g L d' e : ℕ) (hk : k = g * L) (hd : d = g * d') (hg : 0 < g) (h3 : 3 ∣ L)
    (he : (d' * e) % L = 1) (hL : 0 < L) (P : ℕ → ZMod 2 × ZMod 2) (r : ℕ) (hr : r < g) :
    (psi g L e P : ZMod k → ZMod 2) (r : ZMod k) = (P r).1 ∧
      (psi g L e P : ZMod k → ZMod 2) ((r : ZMod k) + (d : ZMod k)) = (P r).2 := by
  have hrk : r < k := by
    rw [hk]
    calc r < g := hr
      _ = g * 1 := (Nat.mul_one g).symm
      _ ≤ g * L := Nat.mul_le_mul_left g hL
  have hval : (r : ZMod k).val = r := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hrk]
  have hdiv : r / g = 0 := Nat.div_eq_of_lt hr
  have hmod : r % g = r := Nat.mod_eq_of_lt hr
  constructor
  · simp [psi, hval, hdiv, hmod, fsel]
  · rw [psi_shift d g L d' e hk hd hg h3 he P (r : ZMod k), hval, hdiv, hmod]
    simp [fsel]

theorem ker_card_ge (d g L d' e : ℕ) (hk : k = g * L) (hd : d = g * d') (hg : 0 < g) (h3 : 3 ∣ L)
    (he : (d' * e) % L = 1) (hL : 0 < L) :
    4 ^ g ≤ (Finset.univ.filter (fun u : ZMod k → ZMod 2 => mixd d u = 0)).card := by
  have hcard : Fintype.card (Fin g → ZMod 2 × ZMod 2) = 4 ^ g := by
    simp
  rw [← hcard, ← Finset.card_univ]
  refine Finset.card_le_card_of_injOn
    (fun (p : Fin g → ZMod 2 × ZMod 2) =>
      (psi g L e (fun n => if h : n < g then p ⟨n, h⟩ else 0) : ZMod k → ZMod 2)) ?_ ?_
  · intro p _
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      psi_mem d g L d' e hk hd hg h3 he _⟩)
  · intro p _ p' _ hpp
    funext r
    have hb := psi_base d g L d' e hk hd hg h3 he hL (fun n => if h : n < g then p ⟨n, h⟩ else 0) r.val r.isLt
    have hb' := psi_base d g L d' e hk hd hg h3 he hL (fun n => if h : n < g then p' ⟨n, h⟩ else 0) r.val r.isLt
    have h1 := congrFun hpp ((r.val : ℕ) : ZMod k)
    have h2 := congrFun hpp (((r.val : ℕ) : ZMod k) + (d : ZMod k))
    simp only [] at h1 h2
    rw [hb.1, hb'.1] at h1
    rw [hb.2, hb'.2] at h2
    simp only [r.isLt, dite_true] at h1 h2
    exact Prod.ext h1 h2

theorem part2 (d : ℕ) (a : ZMod k → ZMod 2) :
    (Finset.univ.filter (fun u : ZMod k → ZMod 2 => mixd d u = a)).card
      = if (∃ y : ZMod k → ZMod 2, mixd d y = a) then
          (if 3 ∣ (k / Nat.gcd k d) then 4 ^ Nat.gcd k d else 1) else 0 := by
  obtain ⟨L, d', e, hg, hk, hd, hLdef, hLpos, hbez, hinv⟩ := arith k d
  by_cases hex : ∃ y : ZMod k → ZMod 2, mixd d y = a
  · obtain ⟨y0, hy0⟩ := hex
    have hlift : (Finset.univ.filter (fun u : ZMod k → ZMod 2 => mixd d u = a)).card
        = (Finset.univ.filter (fun u : ZMod k → ZMod 2 => mixd d u = 0)).card := by
      symm
      refine Finset.card_equiv (Equiv.addRight y0) ?_
      intro u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_addRight]
      constructor
      · intro h
        rw [mix_add, h, hy0, zero_add]
      · intro h
        rw [mix_add, hy0] at h
        exact add_right_cancel (h.trans (zero_add a).symm)
    rw [hlift]
    simp only [eq_true (⟨y0, hy0⟩ : ∃ y : ZMod k → ZMod 2, mixd d y = a), ite_true]
    rw [← hLdef]
    by_cases h3 : 3 ∣ L
    · simp only [eq_true h3, ite_true]
      have hL3 : 3 ≤ L := Nat.le_of_dvd hLpos h3
      have he1 : (d' * e) % L = 1 := by
        rw [hinv]
        exact Nat.mod_eq_of_lt (by omega)
      exact le_antisymm (ker_card_le d _ e hg hbez) (ker_card_ge d _ L d' e hk hd hg h3 he1 hLpos)
    · simp only [eq_false h3, ite_false]
      have hK : (Finset.univ.filter (fun u : ZMod k → ZMod 2 => mixd d u = 0)) = {0} := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hu
          exact ker_trivial d _ L d' hk hd h3 u hu
        · rintro rfl
          exact mix_zero d
      rw [hK, Finset.card_singleton]
  · simp only [eq_false hex, ite_false]
    exact Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr (fun u _ h => hex ⟨u, h⟩))

end PEqualNP.Outside.L_meta_25750_aux

theorem PEqualNP.Outside.L_meta_25750 : (∀ (k : ℕ) [NeZero k] (d : ℕ),
  let I := ZMod k
  let B := ZMod 2
  let V := I → B
  let sign := fun (t : B) => if t = 0 then (1 : ℤ) else -1
  let mix := fun (x : V) (i : I) => x (i-(d : I)) + x i + x (i+(d : I))
  let nl := fun (y : V) (j : I) => y j + (1+y (j+1))*y (j+2)
  let lifts := fun (a : V) => Finset.univ.filter (fun u : V => mix u = a)
  let transfer := fun (u b : V) (j : ℕ) =>
    let i := (j : I)
    (fun (left right : B) =>
      sign ((u i+b i+b (i-2))*left + b (i-1)*left*right) : Matrix B B ℤ)
  let g := Nat.gcd k d
  ∀ (a b : V),
    (∑ x : V, sign (dotProduct a x + dotProduct b (nl (mix x)))) =
      ∑ u ∈ lifts a, Matrix.trace (List.prod (α := Matrix B B ℤ) ((List.range k).map (transfer u b))) ∧
    (lifts a).card = (if (∃ y : V, mix y = a) then
      (if 3 ∣ (k/g) then 4^g else 1) else 0)) := by
  intro k _ d
  dsimp only
  intro a b
  constructor
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := NeZero.pos k; omega⟩
    exact (PEqualNP.Outside.L_meta_25750_aux.part1 d a b).trans
      (Finset.sum_congr rfl (fun u _ => (PEqualNP.Outside.L_meta_25750_aux.trace_transfer n u b).symm))
  · exact PEqualNP.Outside.L_meta_25750_aux.part2 d a
