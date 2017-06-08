import data.list.permutations library_dev.data.list.sort

open list

@[reducible] def pre_pdmap (K : Type) (V : K → Type) := list (Σ (k : K), V k)

namespace pre_pdmap
variables {K : Type} {V : K → Type}

def get [decidable_eq K] [∀ k, inhabited (V k)] (k₀ : K) : pre_pdmap K V → V k₀
| []           := default _
| (⟨k,v⟩::kvs) := if H : k = k₀ then eq.rec_on H v else get kvs

def has_key [decidable_eq K] (k₀ : K) : pre_pdmap K V → Prop
| []           := false
| (⟨k,v⟩::kvs) := if k₀ = k then true else has_key kvs

instance decidable_has_key [decidable_eq K]  (k₀ : K) : Π (kvs : pre_pdmap K V), decidable (has_key k₀ kvs)
| [] := is_false (λ f, f)
| (⟨k, v⟩::kvs) :=
begin
dunfold has_key,
apply (@decidable.by_cases (k₀ = k)),
{ intro H_eq, simp [H_eq], exact decidable.true },
{ intro H_neq, simp [H_neq], apply decidable_has_key }
end

def rm_key [decidable_eq K] (k₀ : K) : pre_pdmap K V → pre_pdmap K V
| []             := []
| (⟨k,v⟩::kvs) := if k₀ = k then kvs else ⟨k,v⟩ :: rm_key kvs

def insert [decidable_eq K] (k₀ : K) (v₀ : V k₀) (pdm : pre_pdmap K V) : pre_pdmap K V :=
if has_key k₀ pdm then ⟨k₀, v₀⟩ :: rm_key k₀ pdm else ⟨k₀, v₀⟩ :: pdm

def keys : pre_pdmap K V → list K
| [] := []
| (⟨k,v⟩::kvs) := k::keys kvs

def erase_dup_keys [decidable_eq K] : pre_pdmap K V → pre_pdmap K V
| []        :=  []
| (⟨k,v⟩ :: kvs) := if has_key k kvs then erase_dup_keys kvs else ⟨k,v⟩ :: erase_dup_keys kvs

end pre_pdmap

def pdmap (K : Type) (V : K → Type) : Type := {xs : pre_pdmap K V // nodup (pre_pdmap.keys xs)}

namespace pdmap
variables {K : Type} {V : K → Type}

-- TODO(dhs): nodup nil
def mk : pdmap K V := ⟨[], sorry⟩

def get [decidable_eq K] [∀ k, inhabited (V k)] (k₀ : K) : pdmap K V → V k₀
| ⟨kvs, H⟩ := pre_pdmap.get k₀ kvs

def has_key [decidable_eq K] (k₀ : K) : pdmap K V → Prop
| ⟨kvs, H⟩ := pre_pdmap.has_key k₀ kvs

instance decidable_has_key [decidable_eq K]  (k₀ : K) : Π (kvs : pdmap K V), decidable (has_key k₀ kvs)
| ⟨kvs, H⟩ := begin dunfold has_key, apply_instance end

-- TODO(dhs): removing does not introduce a duplicate
def rm_key [decidable_eq K] (k₀ : K) : pdmap K V → pdmap K V
| ⟨kvs, H⟩ := ⟨pre_pdmap.rm_key k₀ kvs, sorry⟩

-- TODO(dhs): removing does not introduce a duplicate, and means not in, and consing when not in does not introduce a duplicate
def insert [decidable_eq K] (k₀ : K) (v₀ : V k₀) : pdmap K V → pdmap K V
| ⟨kvs, H⟩ := ⟨pre_pdmap.insert k₀ v₀ kvs, sorry⟩

def keys : pdmap K V → list K
| ⟨kvs, H⟩ := pre_pdmap.keys kvs

definition eqv (l₁ l₂ : pdmap K V) :=
perm l₁.1 l₂.1

local infix ~ := eqv

definition eqv.refl (l : pdmap K V) : l ~ l :=
perm.refl l.1

definition eqv.symm (l₁ l₂ : pdmap K V) : l₁ ~ l₂ → l₂ ~ l₁ :=
perm.symm

definition eqv.trans (l₁ l₂ l₃ : pdmap K V) : l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃ :=
perm.trans

instance pdmap.eqv_setoid : setoid (pdmap K V) :=
setoid.mk eqv (mk_equivalence eqv eqv.refl eqv.symm eqv.trans)

end pdmap

def dmap (K : Type) (V : K → Type) : Type := quot (@pdmap.eqv K V)

namespace dmap
variables {K : Type} {V : K → Type}

def mk : dmap K V := quotient.mk pdmap.mk

def has_key [decidable_eq K] (k₀ : K) (dm : dmap K V) : Prop :=
quot.lift_on dm (λ pdm, pdmap.has_key k₀ pdm) (λ l₁ l₂ (e : pdmap.eqv l₁ l₂), sorry)

instance decidable_has_key [decidable_eq K] (k₀ : K) (dm : dmap K V) : decidable (has_key k₀ dm) :=
quot.rec_on dm (λ pdm, pdmap.decidable_has_key k₀ pdm) (λ l₁ l₂ (e : pdmap.eqv l₁ l₂), sorry)

def get [decidable_eq K] [∀ k, inhabited (V k)] (k₀ : K) (dm : dmap K V) : V k₀ :=
quot.lift_on dm (λ pdm, pdmap.get k₀ pdm) (λ l₁ l₂ (H_eqv : pdmap.eqv l₁ l₂), sorry)

def insert [decidable_eq K] (k₀ : K) (v₀ : V k₀) (dm : dmap K V) : dmap K V :=
quot.lift_on dm (λ pdm, quotient.mk $ pdmap.insert k₀ v₀ pdm) (λ l₁ l₂ (H_eqv : pdmap.eqv l₁ l₂), sorry)

def keys [has_lt K] [decidable_rel (@has_lt.lt K _)] (dm : dmap K V) : list K :=
quot.lift_on dm (λ pdm, insertion_sort has_lt.lt (pdmap.keys pdm)) (λ l₁ l₂ (H_eqv : pdmap.eqv l₁ l₂), sorry)

lemma has_key_mem_keys [decidable_eq K] [has_lt K] [decidable_rel (@has_lt.lt K _)] {k : K} {dm : dmap K V} :
  has_key k dm → k ∈ keys dm := sorry

lemma has_key_insert [decidable_eq K] {k₁ k₂ : K} {v₂ : V k₂} {dm : dmap K V} :
  has_key k₁ dm → has_key k₁ (insert k₂ v₂ dm) := sorry

lemma has_key_insert_same [decidable_eq K] (k : K) {v : V k} (dm : dmap K V) :
  has_key k (insert k v dm) := sorry

lemma get_insert_same [decidable_eq K] [∀ k, inhabited (V k)] (k : K) (v : V k) (dm : dmap K V) :
  get k (insert k v dm) = v := sorry

lemma get_insert_diff [decidable_eq K] [∀ k, inhabited (V k)] {k₁ k₂ : K} (v₂ : V k₂) (dm : dmap K V) :
  k₁ ≠ k₂ → get k₁ (insert k₂ v₂ dm) = get k₁ dm := sorry

lemma insert_get_same [decidable_eq K] [∀ k, inhabited (V k)] (k : K) (dm : dmap K V) :
  insert k (get k dm) dm = dm := sorry

lemma insert_insert_flip [decidable_eq K] [∀ k, inhabited (V k)] {k₁ k₂ : K} (v₁ : V k₁) (v₂ : V k₂) (dm : dmap K V) :
  k₁ ≠ k₂ → insert k₁ v₁ (insert k₂ v₂ dm) = insert k₂ v₂ (insert k₁ v₁ dm) := sorry

lemma insert_insert_same [decidable_eq K] (k : K) (v₁ v₂ : V k) (dm : dmap K V) :
  insert k v₁ (insert k v₂ dm) = insert k v₁ dm := sorry

lemma nodup_insert [decidable_eq K] [has_lt K] [decidable_rel (@has_lt.lt K _)] {k : K} {v : V k} {ks : list K} {dm : dmap K V} :
  nodup (dmap.keys dm ++ (k :: ks)) → nodup (dmap.keys (dmap.insert k v dm) ++ ks) := sorry

lemma not_mem_of_insert [decidable_eq K] [has_lt K] [decidable_rel (@has_lt.lt K _)] {k₀ k : K} {v : V k} {ks : list K} {dm : dmap K V} :
  k₀ ∉ (dmap.keys dm ++ (k :: ks)) → k₀ ∉ (dmap.keys (dmap.insert k v dm) ++ ks) := sorry

lemma not_mem_of_insert_symm [decidable_eq K] [has_lt K] [decidable_rel (@has_lt.lt K _)] {k₀ k : K} {v : V k} {ks : list K} {dm : dmap K V} :
  k₀ ∉ (dmap.keys (dmap.insert k v dm) ++ ks) → k₀ ∉ (dmap.keys dm ++ (k :: ks)) := sorry

end dmap
