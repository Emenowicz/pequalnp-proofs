import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_lib_836

namespace PEqualNP.Outside.L_clb_112_aux

def Lq (d q : ℕ) : ℕ := q * (2 * (d+2) + (2^(d+2) - 1))

def Bq (d q : ℕ) : ℕ := Lq d q + (d+2)

def pk (d : ℕ) (tag : Bool) (u : Fin d → Bool) : Fin (d+2) → Bool :=
  (Fin.cases tag (Fin.cases false u) : Fin (d+2) → Bool)

def zz (d : ℕ) (v : Fin d → Bool) (k : ℕ) : Bool :=
  if h : k < d+2 then pk d true v ⟨k, h⟩
  else if h' : k - (d+2) < d+2 then pk d false v ⟨k - (d+2), h'⟩ else false

abbrev Sw (d : ℕ) (j0 : ℕ) (pat : Fin (d+2+1) → Bool) : Prop :=
  ∃ v : Fin d → Bool, ∀ j : Fin (d+2+1), pat j = zz d v (j0 + j.val)

def cat (d : ℕ) (e s : Fin (d+2) → Bool) (k : ℕ) : Bool :=
  if h : k < d+2 then e ⟨k, h⟩ else if h' : k - (d+2) < d+2 then s ⟨k - (d+2), h'⟩ else false

def lc (n : ℕ) (hn : 0 < n) (k : ℕ) : Fin n := ⟨k % n, Nat.mod_lt _ hn⟩

def nx (t : ℕ) (ht : 0 < t) (h : Fin t) : Fin t := ⟨(h.val + 1) % t, Nat.mod_lt _ ht⟩

theorem pos_lt {t B a o : ℕ} (ha : a < t) (ho : o < B) : a * B + o < t * B := by
  have h1 : (a + 1) * B ≤ t * B := Nat.mul_le_mul_right B ha
  rw [Nat.add_mul, one_mul] at h1
  omega

theorem Lq_lt (d q : ℕ) : Lq d q < Bq d q := by
  unfold Bq
  omega

def bse (d q t : ℕ) (bs : Fin (Lq d q) × (Fin (d+2+1) → Bool) → Bool)
    (s : Fin (t * Bq d q) × (Fin (d+2+1) → Bool)) : Bool :=
  if h : s.1.val % Bq d q < Lq d q then bs (⟨s.1.val % Bq d q, h⟩, s.2)
  else decide (Sw d (s.1.val % Bq d q - Lq d q) s.2)

def prt (d q t : ℕ)
    (pt : Fin q × (Fin d → Bool) × (Fin d → Bool) → Fin (Lq d q) × (Fin (d+2+1) → Bool))
    (e : Fin t × Fin q × (Fin d → Bool) × (Fin d → Bool)) : Fin (t * Bq d q) × (Fin (d+2+1) → Bool) :=
  (⟨e.1.val * Bq d q + (pt e.2).1.val, pos_lt e.1.isLt (lt_trans (pt e.2).1.isLt (Lq_lt d q))⟩, (pt e.2).2)

open Classical in
noncomputable def dh (d q t : ℕ) (digits : Finset (Fin t × Fin q × (Fin d → Bool) × (Fin d → Bool))) (h : Fin t) :
    Finset (Fin q × (Fin d → Bool) × (Fin d → Bool)) :=
  Finset.univ.filter (fun e : Fin q × (Fin d → Bool) × (Fin d → Bool) => (h, e) ∈ digits)

def st (d q : ℕ) (y : Fin (Bq d q) → Bool) : Fin (d+2) → Bool :=
  fun j => y ⟨j.val, by unfold Bq; omega⟩

def en (d q : ℕ) (y : Fin (Bq d q) → Bool) : Fin (d+2) → Bool :=
  fun j => y ⟨Lq d q + j.val, by unfold Bq; omega⟩

def wn (d q : ℕ) (y : Fin (Bq d q) → Bool) (i : Fin (Lq d q)) : Fin (d+2+1) → Bool :=
  fun j => y ⟨i.val + j.val, by have := i.isLt; have := j.isLt; unfold Bq; omega⟩

abbrev Seg (d q t : ℕ) (bs : Fin (Lq d q) × (Fin (d+2+1) → Bool) → Bool)
    (pt : Fin q × (Fin d → Bool) × (Fin d → Bool) → Fin (Lq d q) × (Fin (d+2+1) → Bool))
    (digits : Finset (Fin t × Fin q × (Fin d → Bool) × (Fin d → Bool))) (h : Fin t)
    (y : Fin (Bq d q) → Bool) : Prop :=
  ∀ i : Fin (Lq d q), bs (i, wn d q y i) = true ∨ (i, wn d q y i) ∈ (dh d q t digits h).image pt

theorem fo_cat_lo (d : ℕ) (e s : Fin (d+2) → Bool) (k m : ℕ) (hk : k = m) (h : m < d+2) :
    cat d e s k = e ⟨m, h⟩ := by
  subst hk
  unfold cat
  rw [dif_pos h]

theorem fo_cat_hi (d : ℕ) (e s : Fin (d+2) → Bool) (k m : ℕ) (hk : k = d+2+m) (h : m < d+2) :
    cat d e s k = s ⟨m, h⟩ := by
  subst hk
  unfold cat
  rw [dif_neg (by omega), dif_pos (by omega)]
  congr 2
  omega

theorem fo_zz_lo (d : ℕ) (v : Fin d → Bool) (k m : ℕ) (hk : k = m) (h : m < d+2) :
    zz d v k = pk d true v ⟨m, h⟩ := by
  subst hk
  unfold zz
  rw [dif_pos h]

theorem fo_zz_hi (d : ℕ) (v : Fin d → Bool) (k m : ℕ) (hk : k = d+2+m) (h : m < d+2) :
    zz d v k = pk d false v ⟨m, h⟩ := by
  subst hk
  unfold zz
  rw [dif_neg (by omega), dif_pos (by omega)]
  congr 2
  omega

theorem fo_get (d j0 : ℕ) (e s : Fin (d+2) → Bool) (H : Sw d j0 (fun j => cat d e s (j0 + j.val))) :
    ∃ w : Fin d → Bool, ∀ j : ℕ, j < d+2+1 → cat d e s (j0 + j) = zz d w (j0 + j) := by
  obtain ⟨w, hw⟩ := H
  exact ⟨w, fun j hj => hw ⟨j, hj⟩⟩

theorem fo_ext (d : ℕ) (f g : Fin (d+2) → Bool) (h0 : f ⟨0, by omega⟩ = g ⟨0, by omega⟩)
    (h1 : f ⟨1, by omega⟩ = g ⟨1, by omega⟩)
    (h2 : ∀ i : ℕ, ∀ hi : i < d, f ⟨i+2, by omega⟩ = g ⟨i+2, by omega⟩) : f = g := by
  funext ⟨k, hk⟩
  match k, hk with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | i+2, hk => exact h2 i (by omega)

theorem force (d : ℕ) (e s : Fin (d+2) → Bool) :
    (∀ j0 : ℕ, j0 < d+2 → Sw d j0 (fun j => cat d e s (j0 + j.val))) ↔
      ∃ v : Fin d → Bool, e = pk d true v ∧ s = pk d false v := by
  constructor
  · intro H
    obtain ⟨w0, hw0⟩ := fo_get d 0 e s (H 0 (by omega))
    obtain ⟨w1, hw1⟩ := fo_get d 1 e s (H 1 (by omega))
    have e0 : e ⟨0, by omega⟩ = true := by
      have := hw0 0 (by omega)
      rw [fo_cat_lo d e s _ 0 (by omega) (by omega), fo_zz_lo d w0 _ 0 (by omega) (by omega)] at this
      exact this
    have e1 : e ⟨1, by omega⟩ = false := by
      have := hw0 1 (by omega)
      rw [fo_cat_lo d e s _ 1 (by omega) (by omega), fo_zz_lo d w0 _ 1 (by omega) (by omega)] at this
      exact this
    have s0 : s ⟨0, by omega⟩ = false := by
      have := hw0 (d+2) (by omega)
      rw [fo_cat_hi d e s _ 0 (by omega) (by omega), fo_zz_hi d w0 _ 0 (by omega) (by omega)] at this
      exact this
    have s1 : s ⟨1, by omega⟩ = false := by
      have := hw1 (d+2) (by omega)
      rw [fo_cat_hi d e s _ 1 (by omega) (by omega), fo_zz_hi d w1 _ 1 (by omega) (by omega)] at this
      exact this
    have pl : ∀ i : ℕ, ∀ hi : i < d, e ⟨i+2, by omega⟩ = s ⟨i+2, by omega⟩ := by
      intro i hi
      obtain ⟨w, hw⟩ := fo_get d (i+2) e s (H (i+2) (by omega))
      have ha := hw 0 (by omega)
      have hb := hw (d+2) (by omega)
      rw [fo_cat_lo d e s _ (i+2) (by omega) (by omega), fo_zz_lo d w _ (i+2) (by omega) (by omega)] at ha
      rw [fo_cat_hi d e s _ (i+2) (by omega) (by omega), fo_zz_hi d w _ (i+2) (by omega) (by omega)] at hb
      exact ha.trans hb.symm
    refine ⟨fun i => e ⟨i.val+2, by omega⟩, ?_, ?_⟩
    · exact fo_ext d _ _ e0 e1 (fun i hi => rfl)
    · exact fo_ext d _ _ s0 s1 (fun i hi => (pl i hi).symm)
  · rintro ⟨v, rfl, rfl⟩ j0 _
    exact ⟨v, fun j => rfl⟩

def cn_pl {d : ℕ} (w : Fin (d+2) → Bool) : Fin d → Bool := fun i => w i.succ.succ

theorem cn_pl_pk (d : ℕ) (tag : Bool) (u : Fin d → Bool) : cn_pl (pk d tag u) = u := by
  funext i
  simp [cn_pl, pk]

theorem cn_inj {d : ℕ} {tag : Bool} {u u' : Fin d → Bool} (h : pk d tag u = pk d tag u') : u = u' := by
  have := congrArg cn_pl h
  rwa [cn_pl_pk, cn_pl_pk] at this

theorem cnt {α : Type} [Fintype α] {t d : ℕ} (nxf : Fin t → Fin t) (hnx : Function.Bijective nxf)
    (P : Fin t → α → Prop) [∀ h y, Decidable (P h y)] (s e : α → (Fin (d+2) → Bool)) :
    (Finset.univ.filter (fun Y : Fin t → α =>
      ∀ h, P h (Y h) ∧ ∃ v : Fin d → Bool, e (Y h) = pk d true v ∧ s (Y (nxf h)) = pk d false v)).card =
    ∑ p : Fin t → (Fin d → Bool), ∏ h : Fin t,
      (Finset.univ.filter (fun y : α => s y = pk d false (p h) ∧ e y = pk d true (p (nxf h)) ∧ P h y)).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun Y h => cn_pl (s (Y h))) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [← Fintype.card_piFinset]
  congr 1
  ext Y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hG, rfl⟩
    have key : ∀ h, s (Y h) = pk d false (cn_pl (s (Y h))) := by
      intro h
      obtain ⟨h', rfl⟩ := hnx.2 h
      obtain ⟨v, -, hv⟩ := (hG h').2
      rw [hv, cn_pl_pk]
    intro h
    obtain ⟨hP, v, he, hs⟩ := hG h
    refine ⟨key h, ?_, hP⟩
    rw [he, cn_inj (hs.symm.trans (key (nxf h)))]
  · intro hA
    refine ⟨fun h => ⟨(hA h).2.2, p (nxf h), (hA h).2.1, (hA (nxf h)).1⟩, ?_⟩
    funext h
    rw [(hA h).1, cn_pl_pk]

theorem ly_pos_inj {B a a' o o' : ℕ} (h : a * B + o = a' * B + o') (ho : o < B) (ho' : o' < B) :
    a = a' ∧ o = o' := by
  rcases lt_trichotomy a a' with hl | hl | hl
  · have : (a + 1) * B ≤ a' * B := Nat.mul_le_mul_right B hl
    rw [Nat.add_mul, one_mul] at this
    omega
  · subst hl; omega
  · have : (a' + 1) * B ≤ a * B := Nat.mul_le_mul_right B hl
    rw [Nat.add_mul, one_mul] at this
    omega

theorem ly_mod {B a o : ℕ} (ho : o < B) : (a * B + o) % B = o := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ho]

theorem ly_wrap {t B a r : ℕ} (ha : a ≤ t) (ht : 0 < t) (hr : r < B) :
    (a * B + r) % (t * B) = (a % t) * B + r := by
  rcases Nat.lt_or_ge a t with h | h
  · rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (pos_lt h hr)]
  · have : a = t := by omega
    subst this
    rw [Nat.mod_self, zero_mul, zero_add, Nat.add_comm, Nat.add_mod_right]
    apply Nat.mod_eq_of_lt
    have : 1 * B ≤ a * B := Nat.mul_le_mul_right B ht
    omega

theorem ly_reindex {t B : ℕ} (P : Fin (t * B) → Prop) :
    (∀ i, P i) ↔ ∀ h : Fin t, ∀ o : Fin B, P ⟨h.val * B + o.val, pos_lt h.isLt o.isLt⟩ := by
  refine ⟨fun H h o => H _, fun H i => ?_⟩
  have hB0 : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h | h
    · subst h; exact absurd i.isLt (by simp)
    · exact h
  have hd : i.val / B < t := Nat.div_lt_of_lt_mul (lt_of_lt_of_eq i.isLt (Nat.mul_comm t B))
  have := H ⟨i.val / B, hd⟩ ⟨i.val % B, Nat.mod_lt _ hB0⟩
  have he : (⟨i.val / B * B + i.val % B, pos_lt hd (Nat.mod_lt _ hB0)⟩ : Fin (t * B)) = i :=
    Fin.ext (Nat.div_add_mod' i.val B)
  rw [he] at this
  exact this

theorem ly_split {d q : ℕ} (Q : Fin (Bq d q) → Prop) :
    (∀ o, Q o) ↔ (∀ o : Fin (Lq d q), Q ⟨o.val, lt_trans o.isLt (Lq_lt d q)⟩) ∧
      (∀ j0 : ℕ, (hj : j0 < d + 2) → Q ⟨Lq d q + j0, by unfold Bq; omega⟩) := by
  refine ⟨fun H => ⟨fun o => H _, fun j0 _ => H _⟩, fun H o => ?_⟩
  rcases Nat.lt_or_ge o.val (Lq d q) with h | h
  · exact H.1 ⟨o.val, h⟩
  · have hj : o.val - Lq d q < d + 2 := by have := o.isLt; unfold Bq at this; omega
    have := H.2 _ hj
    have he : (⟨Lq d q + (o.val - Lq d q), by unfold Bq; omega⟩ : Fin (Bq d q)) = o := Fin.ext (by simp; omega)
    rw [he] at this
    exact this

def ly_un (d q t : ℕ) (x : Fin (t * Bq d q) → Bool) : Fin t → Fin (Bq d q) → Bool :=
  fun h o => x ⟨h.val * Bq d q + o.val, pos_lt h.isLt o.isLt⟩

theorem ly_Bpos (d q : ℕ) : 0 < Bq d q := by
  unfold Bq; omega

theorem ly_dlt {d q t : ℕ} (k : Fin (t * Bq d q)) : k.val / Bq d q < t :=
  Nat.div_lt_of_lt_mul (lt_of_lt_of_eq k.isLt (Nat.mul_comm t (Bq d q)))

def ly_fo (d q t : ℕ) (hB : 0 < t * Bq d q) (Y : Fin t → Fin (Bq d q) → Bool) : Fin (t * Bq d q) → Bool :=
  fun k => Y ⟨k.val / Bq d q, ly_dlt k⟩ ⟨k.val % Bq d q, Nat.mod_lt _ (ly_Bpos d q)⟩

theorem ly_un_fo (d q t : ℕ) (hB : 0 < t * Bq d q) (Y : Fin t → Fin (Bq d q) → Bool) :
    ly_un d q t (ly_fo d q t hB Y) = Y := by
  funext h o
  simp only [ly_un, ly_fo]
  have := ly_pos_inj (B := Bq d q) (a := h.val) (o := o.val)
    (Nat.div_add_mod' (h.val * Bq d q + o.val) (Bq d q)).symm
    o.isLt (Nat.mod_lt _ (ly_Bpos d q))
  congr 1
  · exact Fin.ext this.1.symm
  · exact Fin.ext this.2.symm

theorem ly_fo_un (d q t : ℕ) (hB : 0 < t * Bq d q) (x : Fin (t * Bq d q) → Bool) :
    ly_fo d q t hB (ly_un d q t x) = x := by
  funext k
  simp only [ly_un, ly_fo]
  congr 1
  exact Fin.ext (Nat.div_add_mod' k.val (Bq d q))

theorem ly_A (d q t : ℕ) (hB : 0 < t * Bq d q)
    (bs : Fin (Lq d q) × (Fin (d+2+1) → Bool) → Bool)
    (pt : Fin q × (Fin d → Bool) × (Fin d → Bool) → Fin (Lq d q) × (Fin (d+2+1) → Bool))
    (digits : Finset (Fin t × Fin q × (Fin d → Bool) × (Fin d → Bool)))
    (x : Fin (t * Bq d q) → Bool) (h : Fin t) (o : Fin (Lq d q)) :
    (bse d q t bs (⟨h.val * Bq d q + o.val, pos_lt h.isLt (lt_trans o.isLt (Lq_lt d q))⟩,
        fun j => x (lc (t * Bq d q) hB (h.val * Bq d q + o.val + j.val))) = true ∨
      (⟨h.val * Bq d q + o.val, pos_lt h.isLt (lt_trans o.isLt (Lq_lt d q))⟩,
        fun j => x (lc (t * Bq d q) hB (h.val * Bq d q + o.val + j.val))) ∈ digits.image (prt d q t pt)) ↔
    (bs (o, wn d q (ly_un d q t x h) o) = true ∨
      (o, wn d q (ly_un d q t x h) o) ∈ (dh d q t digits h).image pt) := by
  have hoB : o.val < Bq d q := lt_trans o.isLt (Lq_lt d q)
  have hW : (fun j : Fin (d+2+1) => x (lc (t * Bq d q) hB (h.val * Bq d q + o.val + j.val))) =
      wn d q (ly_un d q t x h) o := by
    funext j
    simp only [wn, ly_un]
    congr 1
    apply Fin.ext
    have hj : o.val + j.val < Bq d q := by have := o.isLt; have := j.isLt; unfold Bq; omega
    simp only [lc]
    rw [Nat.add_assoc]
    exact Nat.mod_eq_of_lt (pos_lt h.isLt hj)
  rw [hW]
  have hbse : ∀ P, bse d q t bs (⟨h.val * Bq d q + o.val, pos_lt h.isLt hoB⟩, P) = bs (o, P) := by
    intro P
    simp [bse, ly_mod hoB]
  rw [hbse]
  apply or_congr Iff.rfl
  simp only [Finset.mem_image, dh, Finset.mem_filter, Finset.mem_univ, true_and, prt]
  constructor
  · rintro ⟨⟨h', e⟩, he, hpe⟩
    simp only [Prod.mk.injEq, Fin.ext_iff] at hpe
    obtain ⟨h1, h2⟩ := hpe
    have := ly_pos_inj h1 (lt_trans (pt e).1.isLt (Lq_lt d q)) hoB
    have hh : h' = h := Fin.ext this.1
    subst hh
    exact ⟨e, he, Prod.ext (Fin.ext this.2) h2⟩
  · rintro ⟨e, he, hpe⟩
    refine ⟨(h, e), he, ?_⟩
    simp [hpe]

theorem ly_B (d q t : ℕ) (ht : 0 < t) (hB : 0 < t * Bq d q)
    (bs : Fin (Lq d q) × (Fin (d+2+1) → Bool) → Bool)
    (pt : Fin q × (Fin d → Bool) × (Fin d → Bool) → Fin (Lq d q) × (Fin (d+2+1) → Bool))
    (digits : Finset (Fin t × Fin q × (Fin d → Bool) × (Fin d → Bool)))
    (x : Fin (t * Bq d q) → Bool) (h : Fin t) (j0 : ℕ) (hj0 : j0 < d + 2) (hoB : Lq d q + j0 < Bq d q) :
    (bse d q t bs (⟨h.val * Bq d q + (Lq d q + j0), pos_lt h.isLt hoB⟩,
        fun j => x (lc (t * Bq d q) hB (h.val * Bq d q + (Lq d q + j0) + j.val))) = true ∨
      (⟨h.val * Bq d q + (Lq d q + j0), pos_lt h.isLt hoB⟩,
        fun j => x (lc (t * Bq d q) hB (h.val * Bq d q + (Lq d q + j0) + j.val))) ∈ digits.image (prt d q t pt)) ↔
    Sw d j0 (fun j => cat d (en d q (ly_un d q t x h)) (st d q (ly_un d q t x (nx t ht h))) (j0 + j.val)) := by
  have hW : (fun j : Fin (d+2+1) => x (lc (t * Bq d q) hB (h.val * Bq d q + (Lq d q + j0) + j.val))) =
      fun j => cat d (en d q (ly_un d q t x h)) (st d q (ly_un d q t x (nx t ht h))) (j0 + j.val) := by
    funext j
    have hjl := j.isLt
    unfold cat
    split_ifs with h1 h2
    · simp only [en, ly_un]
      congr 1
      apply Fin.ext
      have hj : Lq d q + (j0 + j.val) < Bq d q := by unfold Bq; omega
      simp only [lc]
      rw [show h.val * Bq d q + (Lq d q + j0) + j.val = h.val * Bq d q + (Lq d q + (j0 + j.val)) by omega]
      exact Nat.mod_eq_of_lt (pos_lt h.isLt hj)
    · simp only [st, ly_un, nx]
      congr 1
      apply Fin.ext
      have hj : j0 + j.val - (d + 2) < Bq d q := by unfold Bq; omega
      simp only [lc]
      rw [show h.val * Bq d q + (Lq d q + j0) + j.val = (h.val + 1) * Bq d q + (j0 + j.val - (d + 2)) by
        rw [Nat.add_mul, one_mul]; unfold Bq; omega]
      exact ly_wrap h.isLt ht hj
    · omega
  rw [hW]
  have hbse : ∀ P, bse d q t bs (⟨h.val * Bq d q + (Lq d q + j0), pos_lt h.isLt hoB⟩, P) = decide (Sw d j0 P) := by
    intro P
    simp [bse, ly_mod hoB]
  rw [hbse]
  have hni : ∀ P, (⟨h.val * Bq d q + (Lq d q + j0), pos_lt h.isLt hoB⟩, P) ∉ digits.image (prt d q t pt) := by
    intro P
    simp only [Finset.mem_image, prt, not_exists, not_and]
    intro e _ hpe
    simp only [Prod.mk.injEq, Fin.ext_iff] at hpe
    have := ly_pos_inj hpe.1 (lt_trans (pt e.2).1.isLt (Lq_lt d q)) hoB
    have := (pt e.2).1.isLt
    omega
  simp only [decide_eq_true_eq]
  exact ⟨fun H => H.elim id (fun H' => absurd H' (hni _)), Or.inl⟩

theorem ly_key (d q t : ℕ)
    (hforce : ∀ (e s : Fin (d+2) → Bool), (∀ j0 : ℕ, j0 < d+2 → Sw d j0 (fun j => cat d e s (j0 + j.val))) ↔ ∃ v : Fin d → Bool, e = pk d true v ∧ s = pk d false v)
    (ht : 0 < t) (hB : 0 < t * Bq d q)
    (bs : Fin (Lq d q) × (Fin (d+2+1) → Bool) → Bool)
    (pt : Fin q × (Fin d → Bool) × (Fin d → Bool) → Fin (Lq d q) × (Fin (d+2+1) → Bool))
    (digits : Finset (Fin t × Fin q × (Fin d → Bool) × (Fin d → Bool)))
    (x : Fin (t * Bq d q) → Bool) :
    (∀ i : Fin (t * Bq d q),
        bse d q t bs (i, fun j => x (lc (t * Bq d q) hB (i.val + j.val))) = true ∨
        (i, fun j => x (lc (t * Bq d q) hB (i.val + j.val))) ∈ digits.image (prt d q t pt)) ↔
    ∀ h : Fin t, Seg d q t bs pt digits h (ly_un d q t x h) ∧
        ∃ v : Fin d → Bool, en d q (ly_un d q t x h) = pk d true v ∧
          st d q (ly_un d q t x (nx t ht h)) = pk d false v := by
  refine (ly_reindex _).trans (forall_congr' fun h => (ly_split _).trans (and_congr ?_ ?_))
  · exact forall_congr' fun o => ly_A d q t hB bs pt digits x h o
  · rw [← hforce]
    exact forall_congr' fun j0 => forall_congr' fun hj =>
      ly_B d q t ht hB bs pt digits x h j0 hj (by unfold Bq; omega)

theorem ly_main (d q t : ℕ)
    (hforce : ∀ (e s : Fin (d+2) → Bool), (∀ j0 : ℕ, j0 < d+2 → Sw d j0 (fun j => cat d e s (j0 + j.val))) ↔ ∃ v : Fin d → Bool, e = pk d true v ∧ s = pk d false v)
    (ht : 0 < t) (hB : 0 < t * Bq d q)
    (bs : Fin (Lq d q) × (Fin (d+2+1) → Bool) → Bool)
    (pt : Fin q × (Fin d → Bool) × (Fin d → Bool) → Fin (Lq d q) × (Fin (d+2+1) → Bool))
    (digits : Finset (Fin t × Fin q × (Fin d → Bool) × (Fin d → Bool))) :
    (Finset.univ.filter (fun x : Fin (t * Bq d q) → Bool => ∀ i : Fin (t * Bq d q),
        bse d q t bs (i, fun j => x (lc (t * Bq d q) hB (i.val + j.val))) = true ∨
        (i, fun j => x (lc (t * Bq d q) hB (i.val + j.val))) ∈ digits.image (prt d q t pt))).card =
    (Finset.univ.filter (fun Y : Fin t → Fin (Bq d q) → Bool => ∀ h : Fin t,
        Seg d q t bs pt digits h (Y h) ∧
        ∃ v : Fin d → Bool, en d q (Y h) = pk d true v ∧ st d q (Y (nx t ht h)) = pk d false v)).card := by
  apply Finset.card_nbij' (ly_un d q t) (ly_fo d q t hB)
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    exact (ly_key d q t hforce ht hB bs pt digits x).1 hx
  · intro Y hY
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hY ⊢
    have := (ly_key d q t hforce ht hB bs pt digits (ly_fo d q t hB Y)).2
    rw [ly_un_fo] at this
    exact this hY
  · intro x _
    exact ly_fo_un d q t hB x
  · intro Y _
    exact ly_un_fo d q t hB Y

theorem lay (d q t : ℕ)
    (hforce : ∀ (e s : Fin (d+2) → Bool), (∀ j0 : ℕ, j0 < d+2 → Sw d j0 (fun j => cat d e s (j0 + j.val))) ↔ ∃ v : Fin d → Bool, e = pk d true v ∧ s = pk d false v)
    (ht : 0 < t) (hB : 0 < t * Bq d q)
    (bs : Fin (Lq d q) × (Fin (d+2+1) → Bool) → Bool)
    (pt : Fin q × (Fin d → Bool) × (Fin d → Bool) → Fin (Lq d q) × (Fin (d+2+1) → Bool))
    (digits : Finset (Fin t × Fin q × (Fin d → Bool) × (Fin d → Bool))) :
    (Finset.univ.filter (fun x : Fin (t * Bq d q) → Bool => ∀ i : Fin (t * Bq d q),
        bse d q t bs (i, fun j => x (lc (t * Bq d q) hB (i.val + j.val))) = true ∨
        (i, fun j => x (lc (t * Bq d q) hB (i.val + j.val))) ∈ digits.image (prt d q t pt))).card =
    (Finset.univ.filter (fun Y : Fin t → Fin (Bq d q) → Bool => ∀ h : Fin t,
        Seg d q t bs pt digits h (Y h) ∧
        ∃ v : Fin d → Bool, en d q (Y h) = pk d true v ∧ st d q (Y (nx t ht h)) = pk d false v)).card :=
  ly_main d q t hforce ht hB bs pt digits

theorem arith (d q t : ℕ) (hq : 0 < q) :
    t * (q * (2 * (d+2) + (2^(d+2) - 1)) + (d+2)) * 2^(d+2+1) ≤ 80 * t * q * (2^d)^2 := by
  have hm : 1 ≤ 2^d := Nat.one_le_two_pow
  have hw : d + 2 ≤ 2 * 2^d := by
    induction d with
    | zero => norm_num
    | succ k ih =>
      have h1 : 1 ≤ 2^k := Nat.one_le_two_pow
      rw [pow_succ]
      omega
  have e1 : 2^(d+2) = 4 * 2^d := by rw [pow_add]; ring
  have e2 : 2^(d+2+1) = 8 * 2^d := by rw [pow_add, pow_add]; ring
  rw [e1, e2]
  have key : q * (2 * (d+2) + (4 * 2^d - 1)) + (d+2) ≤ 10 * q * 2^d := by
    have hX : q * (2 * (d+2) + (4 * 2^d - 1)) ≤ 8 * (q * 2^d) := by
      calc q * (2 * (d+2) + (4 * 2^d - 1)) ≤ q * (8 * 2^d) := Nat.mul_le_mul_left q (by omega)
        _ = 8 * (q * 2^d) := by ring
    have hqa : 2^d ≤ q * 2^d := Nat.le_mul_of_pos_left (2^d) hq
    have e3 : 10 * q * 2^d = 10 * (q * 2^d) := by ring
    omega
  calc t * (q * (2 * (d+2) + (4 * 2^d - 1)) + (d+2)) * (8 * 2^d)
      ≤ t * (10 * q * 2^d) * (8 * 2^d) := by
        apply Nat.mul_le_mul_right; exact Nat.mul_le_mul_left t key
    _ = 80 * t * q * (2^d)^2 := by ring

theorem prt_pos_inj {B a a' o o' : ℕ} (h : a * B + o = a' * B + o') (ho : o < B) (ho' : o' < B) :
    a = a' ∧ o = o' := by
  have hB : 0 < B := by omega
  have h1 : (a * B + o) / B = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt ho, zero_add]
  have h2 : (a' * B + o') / B = a' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt ho', zero_add]
  have ha : a = a' := by rw [← h1, ← h2, h]
  subst ha
  exact ⟨rfl, by omega⟩

theorem prt_inj (d q t : ℕ)
    (pt : Fin q × (Fin d → Bool) × (Fin d → Bool) → Fin (Lq d q) × (Fin (d+2+1) → Bool))
    (hinj : Function.Injective pt) : Function.Injective (prt d q t pt) := by
  intro e e' h
  have h1 := congrArg (fun s => s.1.val) h
  have h2 := congrArg (fun s => s.2) h
  simp only [prt] at h1 h2
  obtain ⟨ha, ho⟩ := prt_pos_inj h1 (lt_trans (pt e.2).1.isLt (Lq_lt d q))
    (lt_trans (pt e'.2).1.isLt (Lq_lt d q))
  have hp : pt e.2 = pt e'.2 := Prod.ext (Fin.ext ho) h2
  exact Prod.ext (Fin.ext ha) (hinj hp)

theorem prt_mod (d q t : ℕ)
    (pt : Fin q × (Fin d → Bool) × (Fin d → Bool) → Fin (Lq d q) × (Fin (d+2+1) → Bool))
    (e : Fin t × Fin q × (Fin d → Bool) × (Fin d → Bool)) :
    (prt d q t pt e).1.val % Bq d q = (pt e.2).1.val ∧ (prt d q t pt e).1.val / Bq d q = e.1.val := by
  have ho : (pt e.2).1.val < Bq d q := lt_trans (pt e.2).1.isLt (Lq_lt d q)
  have hB : 0 < Bq d q := by omega
  simp only [prt]
  constructor
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ho]
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt ho, zero_add]

theorem prt_base (d q t : ℕ) (bs : Fin (Lq d q) × (Fin (d+2+1) → Bool) → Bool)
    (pt : Fin q × (Fin d → Bool) × (Fin d → Bool) → Fin (Lq d q) × (Fin (d+2+1) → Bool))
    (hbase : ∀ e, bs (pt e) = false) (e : Fin t × Fin q × (Fin d → Bool) × (Fin d → Bool)) :
    bse d q t bs (prt d q t pt e) = false := by
  have hm := (prt_mod d q t pt e).1
  have hlt : (prt d q t pt e).1.val % Bq d q < Lq d q := by rw [hm]; exact (pt e.2).1.isLt
  unfold bse
  rw [dite_cond_eq_true (eq_true hlt)]
  have : ((⟨(prt d q t pt e).1.val % Bq d q, hlt⟩ : Fin (Lq d q)), (prt d q t pt e).2) = pt e.2 := by
    apply Prod.ext
    · exact Fin.ext hm
    · rfl
  rw [this]
  exact hbase e.2

theorem nx_bij (t : ℕ) (ht : 0 < t) : Function.Bijective (nx t ht) := by
  apply (Finite.injective_iff_bijective).mp
  intro a b h
  have h1 := congrArg Fin.val h
  simp only [nx] at h1
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  rcases Nat.lt_or_ge (a.val + 1) t with h2 | h2 <;> rcases Nat.lt_or_ge (b.val + 1) t with h3 | h3
  · rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3] at h1; omega
  · have e3 : b.val + 1 = t := by omega
    rw [Nat.mod_eq_of_lt h2, e3, Nat.mod_self] at h1; omega
  · have e2 : a.val + 1 = t := by omega
    rw [Nat.mod_eq_of_lt h3, e2, Nat.mod_self] at h1; omega
  · omega

theorem layer (d q t : ℕ) (hq : 0 < q) (bs : Fin (Lq d q) × (Fin (d+2+1) → Bool) → Bool)
    (pt : Fin q × (Fin d → Bool) × (Fin d → Bool) → Fin (Lq d q) × (Fin (d+2+1) → Bool))
    (hcount : ∀ (digits : Finset (Fin q × (Fin d → Bool) × (Fin d → Bool))) (a b : Bool) (u v : Fin d → Bool),
      (Finset.univ.filter (fun x : Fin (Bq d q) → Bool =>
        (∀ j : Fin (d+2), x (lc (Bq d q) (lt_of_le_of_lt (Nat.zero_le _) (Lq_lt d q)) j.val) = pk d a u j ∧
          x (lc (Bq d q) (lt_of_le_of_lt (Nat.zero_le _) (Lq_lt d q)) (Lq d q + j.val)) = pk d b v j) ∧
        ∀ i : Fin (Lq d q),
          bs (i, fun off => x (lc (Bq d q) (lt_of_le_of_lt (Nat.zero_le _) (Lq_lt d q)) (i.val + off.val))) = true ∨
          (i, fun off => x (lc (Bq d q) (lt_of_le_of_lt (Nat.zero_le _) (Lq_lt d q)) (i.val + off.val))) ∈ digits.image pt)).card =
        if a = b then (if u = v then (if a then 2^q else 1) else 0)
        else if a then 0 else (Finset.univ : Finset (Fin q)).sum (fun bit => if (bit,u,v) ∈ digits then 2^bit.val else 0))
    (digits : Finset (Fin t × Fin q × (Fin d → Bool) × (Fin d → Bool))) (h : Fin t) (u v : Fin d → Bool) :
    (Finset.univ.filter (fun y : Fin (Bq d q) → Bool =>
      st d q y = pk d false u ∧ en d q y = pk d true v ∧ Seg d q t bs pt digits h y)).card =
    (Finset.univ : Finset (Fin q)).sum (fun bit => if (h,bit,u,v) ∈ digits then 2^bit.val else 0) := by
  classical
  have hc := hcount (dh d q t digits h) false true u v
  simp only [Bool.false_eq_true, ↓reduceIte] at hc
  have hB : 0 < Bq d q := lt_of_le_of_lt (Nat.zero_le _) (Lq_lt d q)
  have hloc : ∀ k (hk : k < Bq d q), lc (Bq d q) hB k = ⟨k, hk⟩ := fun k hk => Fin.ext (Nat.mod_eq_of_lt hk)
  have hsum : ((Finset.univ : Finset (Fin q)).sum (fun bit => if (bit,u,v) ∈ dh d q t digits h then 2^bit.val else 0)) =
      (Finset.univ : Finset (Fin q)).sum (fun bit => if (h,bit,u,v) ∈ digits then 2^bit.val else 0) := by
    apply Finset.sum_congr rfl
    intro bit _
    simp [dh]
  rw [← hsum, ← hc]
  congr 1
  apply Finset.filter_congr
  intro y _
  have hw : ∀ i : Fin (Lq d q), (fun off : Fin (d+2+1) => y (lc (Bq d q) hB (i.val + off.val))) = wn d q y i := by
    intro i
    funext off
    simp only [wn]
    rw [hloc]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun j => ⟨?_, ?_⟩, fun i => ?_⟩
    · rw [hloc j.val (by have := j.isLt; unfold Bq; omega)]
      exact congrFun h1 j
    · rw [hloc (Lq d q + j.val) (by have := j.isLt; unfold Bq; omega)]
      exact congrFun h2 j
    · rw [hw i]
      exact h3 i
  · rintro ⟨h1, h3⟩
    refine ⟨funext fun j => ?_, funext fun j => ?_, fun i => ?_⟩
    · have := (h1 j).1
      rw [hloc j.val (by have := j.isLt; unfold Bq; omega)] at this
      exact this
    · have := (h1 j).2
      rw [hloc (Lq d q + j.val) (by have := j.isLt; unfold Bq; omega)] at this
      exact this
    · have := h3 i
      rw [hw i] at this
      exact this

end PEqualNP.Outside.L_clb_112_aux

theorem PEqualNP.Outside.L_clb_112 : (∀ (d q t : Nat) (hq : 0 < q) (ht : 0 < t),
  let w := d+2
  let m := 2^d
  let block := q*(2*w+(2^w-1))+w
  let n := t*block
  let D := Fin d → Bool
  let E := Fin t × Fin q × D × D
  let S := Fin n × (Fin (w+1) → Bool)
  let next := fun (h : Fin t) => (⟨(h.val+1) % t, Nat.mod_lt _ ht⟩ : Fin t)
  let loc := fun k : Nat => (⟨k % n, Nat.mod_lt _ (Nat.mul_pos ht (Nat.lt_of_lt_of_le (Nat.succ_pos (d+1)) (Nat.le_add_left _ _)))⟩ : Fin n)
  n * 2^(w+1) ≤ 80 * t * q * m^2 ∧
    ∃ (base : S → Bool) (port : E → S),
      Function.Injective port ∧ (∀ e, base (port e) = false) ∧
      (∀ e, (port e).1.val / block = e.1.val) ∧
      ∀ digits : Finset E,
        let weight := fun (layer : Fin t) (u v : D) =>
          (Finset.univ : Finset (Fin q)).sum (fun bit =>
            if (layer,bit,u,v) ∈ digits then 2^bit.val else 0)
        (Finset.univ.filter (fun x : Fin n → Bool => ∀ i : Fin n,
          let s : S := (i,fun j => x (loc (i.val+j.val)))
          base s = true ∨ s ∈ digits.image port)).card =
          (Finset.univ : Finset (Fin t → D)).sum (fun p =>
            (Finset.univ : Finset (Fin t)).prod (fun layerId => weight layerId (p layerId) (p (next layerId))))) := by
  intro d q t hq ht
  dsimp only
  have h836 := PEqualNP.Outside.L_lib_836 d q
  dsimp only at h836
  obtain ⟨bs, pt, hinj, hbase, _, hcount⟩ := h836
  have hB : 0 < t * PEqualNP.Outside.L_clb_112_aux.Bq d q :=
    Nat.mul_pos ht (lt_of_le_of_lt (Nat.zero_le _) (PEqualNP.Outside.L_clb_112_aux.Lq_lt d q))
  refine ⟨PEqualNP.Outside.L_clb_112_aux.arith d q t hq,
    PEqualNP.Outside.L_clb_112_aux.bse d q t bs, PEqualNP.Outside.L_clb_112_aux.prt d q t pt,
    PEqualNP.Outside.L_clb_112_aux.prt_inj d q t pt hinj,
    PEqualNP.Outside.L_clb_112_aux.prt_base d q t bs pt hbase,
    fun e => (PEqualNP.Outside.L_clb_112_aux.prt_mod d q t pt e).2, fun digits => ?_⟩
  have hl := PEqualNP.Outside.L_clb_112_aux.lay d q t (PEqualNP.Outside.L_clb_112_aux.force d) ht hB bs pt digits
  have hc := PEqualNP.Outside.L_clb_112_aux.cnt (PEqualNP.Outside.L_clb_112_aux.nx t ht)
    (PEqualNP.Outside.L_clb_112_aux.nx_bij t ht)
    (PEqualNP.Outside.L_clb_112_aux.Seg d q t bs pt digits)
    (PEqualNP.Outside.L_clb_112_aux.st d q) (PEqualNP.Outside.L_clb_112_aux.en d q)
  refine (hl.trans hc).trans ?_
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.prod_congr rfl
  intro h _
  exact PEqualNP.Outside.L_clb_112_aux.layer d q t hq bs pt (fun dg a b u v => hcount dg a b u v) digits h _ _
